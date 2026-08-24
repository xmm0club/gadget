open Ast

exception Error of loc * string

let err loc fmt = Printf.ksprintf (fun s -> raise (Error (loc, s))) fmt

(* ------------------------------------------------------------------ types

   inference needs mutable variables and levels, but everything downstream of this module
   wants a ground Ast.ty, so the two representations are kept apart and every inference
   type is zonked into an Ast.ty at the very end *)

type ity =
  | Iint
  | Ibool
  | Ifloat
  | Iunit
  | Ipair of ity * ity
  | Iarrow of ity * ity
  | Ivar of tv ref

and tv =
  | Unbound of int * int
  | Link of ity

let tv_counter = ref 0

let fresh lvl =
  incr tv_counter;
  Ivar (ref (Unbound (!tv_counter, lvl)))

let rec repr t =
  match t with
  | Ivar ({ contents = Link t' } as r) ->
    let t'' = repr t' in
    r := Link t'';
    t''
  | t -> t

let tv_name id =
  let i = (id - 1) mod 26 and n = (id - 1) / 26 in
  let c = Char.chr (Char.code 'a' + i) in
  if n = 0 then Printf.sprintf "'%c" c else Printf.sprintf "'%c%d" c n

let rec show t =
  match repr t with
  | Iint -> "Int"
  | Ibool -> "Bool"
  | Ifloat -> "Float"
  | Iunit -> "Unit"
  | Ipair (a, b) -> "(" ^ show a ^ ", " ^ show_tuple b ^ ")"
  | Iarrow (a, b) -> show_atom a ^ " -> " ^ show b
  | Ivar { contents = Unbound (id, _) } -> tv_name id
  | Ivar { contents = Link _ } -> assert false

and show_tuple t =
  match repr t with Ipair (a, b) -> show a ^ ", " ^ show_tuple b | t -> show t

and show_atom t = match repr t with Iarrow _ -> "(" ^ show t ^ ")" | t -> show t

let rec of_ast = function
  | Tint -> Iint
  | Tbool -> Ibool
  | Tfloat -> Ifloat
  | Tunit -> Iunit
  | Tpair (a, b) -> Ipair (of_ast a, of_ast b)
  | Tarrow (a, b) -> Iarrow (of_ast a, of_ast b)

(* a variable that nothing ever constrained cannot be given a runtime representation, so
   it is defaulted to Unit; the link is written back so every use agrees *)
let rec zonk t =
  match repr t with
  | Iint -> Tint
  | Ibool -> Tbool
  | Ifloat -> Tfloat
  | Iunit -> Tunit
  | Ipair (a, b) -> Tpair (zonk a, zonk b)
  | Iarrow (a, b) -> Tarrow (zonk a, zonk b)
  | Ivar r ->
    r := Link Iunit;
    Tunit

exception Clash

let rec occurs id lvl t =
  match repr t with
  | Ivar r -> (
    match !r with
    | Unbound (id', lvl') ->
      if id' = id
      then true
      else begin
        if lvl' > lvl then r := Unbound (id', lvl);
        false
      end
    | Link _ -> false)
  | Ipair (a, b) | Iarrow (a, b) ->
    let x = occurs id lvl a in
    let y = occurs id lvl b in
    x || y
  | _ -> false

let rec unify a b =
  let a = repr a and b = repr b in
  match a, b with
  | Ivar r1, Ivar r2 when r1 == r2 -> ()
  | Iint, Iint | Ibool, Ibool | Ifloat, Ifloat | Iunit, Iunit -> ()
  | Ipair (a1, a2), Ipair (b1, b2) | Iarrow (a1, a2), Iarrow (b1, b2) ->
    unify a1 b1;
    unify a2 b2
  | Ivar ({ contents = Unbound (id, lvl) } as r), t
  | t, Ivar ({ contents = Unbound (id, lvl) } as r) ->
    if occurs id lvl t then raise Clash;
    r := Link t
  | _ -> raise Clash

let rec free_vars lvl acc t =
  match repr t with
  | Ivar { contents = Unbound (id, l) } ->
    if l > lvl && not (List.mem id acc) then id :: acc else acc
  | Ipair (a, b) | Iarrow (a, b) -> free_vars lvl (free_vars lvl acc a) b
  | _ -> acc

let generalize lvl t = free_vars lvl [] t

(* ------------------------------------------------------- environments and groups

   a binding that generalises is not elaborated in place; it is recorded as a group,
   every occurrence of it registers the types it was instantiated at, and after the whole
   program is inferred the group is re elaborated once per distinct instantiation *)

type entry =
  | Emono of string * ity
  | Epoly of pgroup * int

and env = (string * entry) list

and gsrc =
  | Gval of Ast.expr
  | Grec of Ast.letrec list

and guse =
  { uargs : ity list
  ; umember : int
  ; uref : Tast.vref
  }

and pgroup =
  { gmembers : (string * ity) list
  ; gqs : int list
  ; gsrc : gsrc
  ; genv : env
  ; glevel : int
  ; gloc : Ast.loc
  ; mutable guses : guse list
  ; mutable uhandled : int
  ; mutable gdone : (Ast.ty list * string list) list
  ; mutable gslot : Tast.group option
  }

let groups : pgroup list ref = ref []
let patches : (unit -> unit) list ref = ref []
let deferred : (unit -> unit) list ref = ref []
let uid = ref 0
let instances = ref 0

let next_uid () =
  incr uid;
  !uid

let spec_name base = Printf.sprintf "%s#%d" base (next_uid ())
let tmp_name () = Printf.sprintf "$p%d" (next_uid ())
let later f = patches := f :: !patches
let defer f = deferred := f :: !deferred

(* inferring the right hand side of a binding is only how its type scheme is discovered;
   if it turns out to generalise the elaboration is thrown away and redone once per
   instantiation, so the work it queued has to be rolled back too - otherwise a deferred
   check would zonk, and therefore default, a variable that is still quantified *)
let snapshot () = !deferred, !patches, !groups
let restore (d, p, g) =
  deferred := d;
  patches := p;
  groups := g

let node loc desc ty =
  let n = { Tast.desc; ty = Tunit; loc } in
  later (fun () -> n.Tast.ty <- zonk ty);
  n

let ret loc desc ty = node loc desc ty, ty

let instantiate_group lvl g =
  let tbl = Hashtbl.create 8 in
  List.iter (fun id -> Hashtbl.replace tbl id (fresh lvl)) g.gqs;
  let rec go t =
    match repr t with
    | Ivar { contents = Unbound (id, _) } as v -> (
      match Hashtbl.find_opt tbl id with Some x -> x | None -> v)
    | Ipair (a, b) -> Ipair (go a, go b)
    | Iarrow (a, b) -> Iarrow (go a, go b)
    | t -> t
  in
  List.map (fun (_, t) -> go t) g.gmembers

(* the value restriction: only a syntactic value generalises, which also means an unused
   polymorphic binding can be dropped without changing what the program does *)
let rec is_value (e : Ast.expr) =
  match e.desc with
  | Int _ | Bool _ | Float _ | Unit | Var _ | Fun _ -> true
  | Pair (a, b) -> is_value a && is_value b
  | Ann (a, _) -> is_value a
  | _ -> false

let union a b = List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) b a

(* --------------------------------------------------------------- inference *)

let rec infer lvl env (e : Ast.expr) : Tast.t * ity =
  let loc = e.loc in
  match e.desc with
  | Ast.Int n -> ret loc (Tast.Int n) Iint
  | Ast.Bool b -> ret loc (Tast.Bool b) Ibool
  | Ast.Float f -> ret loc (Tast.Float f) Ifloat
  | Ast.Unit -> ret loc Tast.Unit Iunit
  | Ast.Var x -> (
    match List.assoc_opt x env with
    | None -> err loc "unbound variable %s" x
    | Some (Emono (nm, t)) -> ret loc (Tast.Var { Tast.vname = nm }) t
    | Some (Epoly (g, i)) ->
      let args = instantiate_group lvl g in
      let vr = { Tast.vname = "" } in
      g.guses <- g.guses @ [ { uargs = args; umember = i; uref = vr } ];
      ret loc (Tast.Var vr) (List.nth args i))
  | Ast.Ann (e', t) ->
    let want = of_ast t in
    check lvl env e' want, want
  | Ast.Bin (op, a, b) -> infer_bin lvl env loc op a b
  | Ast.Un (op, a) -> infer_un lvl env loc op a
  | Ast.If (c, a, b) ->
    let tc = check lvl env c Ibool in
    let ta, aty = infer lvl env a in
    let tb = check_at lvl env b aty "the two branches of if must have the same type" in
    ret loc (Tast.If (tc, ta, tb)) aty
  | Ast.Let (p, ann, rhs, body) -> infer_let lvl env loc p ann rhs body
  | Ast.Let_rec (lrs, rest) -> infer_letrec lvl env loc lrs rest
  | Ast.Fun (x, ann, b) ->
    let pt = match ann with Some t -> of_ast t | None -> fresh lvl in
    let tb, rt = infer lvl ((x, Emono (x, pt)) :: env) b in
    let lam = { Tast.param = x; param_ty = Tunit; body = tb } in
    later (fun () -> lam.Tast.param_ty <- zonk pt);
    ret loc (Tast.Fun lam) (Iarrow (pt, rt))
  | Ast.App (f, a) ->
    let tf, fty = infer lvl env f in
    let pa = fresh lvl and pr = fresh lvl in
    (try unify fty (Iarrow (pa, pr)) with
     | Clash ->
       err f.Ast.loc "expected a function, found %s, so it cannot be applied" (show fty));
    let ta = check lvl env a pa in
    ret loc (Tast.App (tf, ta)) pr
  | Ast.Pair (a, b) ->
    let ta, aty = infer lvl env a in
    let tb, bty = infer lvl env b in
    ret loc (Tast.Pair (ta, tb)) (Ipair (aty, bty))

and check lvl env e want =
  let t, got = infer lvl env e in
  (try unify want got with
   | Clash -> err e.Ast.loc "expected %s, found %s" (show want) (show got));
  t

and check_at lvl env e want ctx =
  let t, got = infer lvl env e in
  (try unify want got with
   | Clash -> err e.Ast.loc "%s: expected %s, found %s" ctx (show want) (show got));
  t

and infer_let lvl env loc p ann rhs body =
  match p with
  | Ast.Pvar x when is_value rhs ->
    (* infer at a deeper level so that anything the body does not constrain shows up as
       quantifiable when we come back out *)
    let snap = snapshot () in
    let trhs, rty = infer (lvl + 1) env rhs in
    (match ann with
     | None -> ()
     | Some t -> (
       try unify (of_ast t) rty with
       | Clash -> err rhs.Ast.loc "expected %s, found %s" (show_ty t) (show rty)));
    let qs = generalize lvl rty in
    if qs = []
    then begin
      let tb, bty = infer lvl ((x, Emono (x, rty)) :: env) body in
      ret loc (Tast.Let { Tast.binds = [ Tast.Bval (x, trhs) ]; gbody = tb }) bty
    end
    else begin
      restore snap;
      let g =
        { gmembers = [ x, rty ]
        ; gqs = qs
        ; gsrc = Gval rhs
        ; genv = env
        ; glevel = lvl
        ; gloc = loc
        ; guses = []
        ; uhandled = 0
        ; gdone = []
        ; gslot = None
        }
      in
      groups := g :: !groups;
      let tb, bty = infer lvl ((x, Epoly (g, 0)) :: env) body in
      let slot = { Tast.binds = []; gbody = tb } in
      g.gslot <- Some slot;
      ret loc (Tast.Let slot) bty
    end
  | _ ->
    let trhs, rty = infer lvl env rhs in
    (match ann with
     | None -> ()
     | Some t -> (
       try unify (of_ast t) rty with
       | Clash -> err rhs.Ast.loc "expected %s, found %s" (show_ty t) (show rty)));
    let binds, env' = bind_pat lvl loc env p rty trhs in
    let tb, bty = infer lvl env' body in
    ret loc (Tast.Let { Tast.binds; gbody = tb }) bty

(* a tuple pattern turns into a chain of ordinary bindings reading fst and snd out of a
   temporary, so patterns never reach the compiler *)
and bind_pat lvl loc env p ty rhs =
  let binds = ref [] in
  let env = ref env in
  let bind name t v =
    binds := !binds @ [ Tast.Bval (name, v) ];
    env := (name, Emono (name, t)) :: !env
  in
  let rec go p ty (src : Tast.t) =
    match p with
    | Ast.Pvar x -> bind x ty src
    | Ast.Ppair (a, b) ->
      let ta = fresh lvl and tb = fresh lvl in
      (try unify ty (Ipair (ta, tb)) with
       | Clash -> err loc "expected a tuple, found %s" (show ty));
      let nm = tmp_name () in
      bind nm ty src;
      let read () = node loc (Tast.Var { Tast.vname = nm }) ty in
      go a ta (node loc (Tast.Un (Ast.Fst, read ())) ta);
      go b tb (node loc (Tast.Un (Ast.Snd, read ())) tb)
  in
  go p ty rhs;
  !binds, !env

and infer_letrec lvl env loc lrs rest =
  let inner = lvl + 1 in
  let dup =
    List.find_opt
      (fun lr -> List.length (List.filter (fun o -> o.Ast.name = lr.Ast.name) lrs) > 1)
      lrs
  in
  (match dup with
   | Some lr -> err lr.Ast.rloc "%s is bound twice in the same recursive group" lr.Ast.name
   | None -> ());
  let snap = snapshot () in
  let sigs =
    List.map
      (fun lr ->
        let pt =
          match lr.Ast.param_ty with Some t -> of_ast t | None -> fresh inner
        in
        pt, fresh inner)
      lrs
  in
  let mems = List.map2 (fun lr (pt, rt) -> lr.Ast.name, Iarrow (pt, rt)) lrs sigs in
  (* every member of the group is in scope in every body, and recursive uses are
     monomorphic, which is what keeps the number of specialisations finite *)
  let genv =
    List.fold_left
      (fun acc (nm, t) -> (nm, Emono (nm, t)) :: acc)
      env mems
  in
  let bodies =
    List.map2
      (fun lr (pt, rt) ->
        let benv = (lr.Ast.param, Emono (lr.Ast.param, pt)) :: genv in
        check_at inner benv lr.Ast.body rt "the body of a recursive binding")
      lrs sigs
  in
  let qs = List.fold_left (fun acc (_, t) -> union (generalize lvl t) acc) [] mems in
  if qs = []
  then begin
    let fnodes =
      List.map2
        (fun (lr, tb) (pt, rt) ->
          let f =
            { Tast.fname = lr.Ast.name
            ; fparam = lr.Ast.param
            ; fparam_ty = Tunit
            ; fret_ty = Tunit
            ; fbody = tb
            }
          in
          later (fun () ->
              f.Tast.fparam_ty <- zonk pt;
              f.Tast.fret_ty <- zonk rt);
          f)
        (List.combine lrs bodies) sigs
    in
    let env' =
      List.fold_left (fun acc (nm, t) -> (nm, Emono (nm, t)) :: acc) env mems
    in
    let tr, rty = infer lvl env' rest in
    ret loc (Tast.Let { Tast.binds = [ Tast.Brec fnodes ]; gbody = tr }) rty
  end
  else begin
    restore snap;
    let g =
      { gmembers = mems
      ; gqs = qs
      ; gsrc = Grec lrs
      ; genv = env
      ; glevel = lvl
      ; gloc = loc
      ; guses = []
      ; uhandled = 0
      ; gdone = []
      ; gslot = None
      }
    in
    groups := g :: !groups;
    let env' =
      List.fold_left
        (fun acc (i, lr) -> (lr.Ast.name, Epoly (g, i)) :: acc)
        env
        (List.mapi (fun i lr -> i, lr) lrs)
    in
    let tr, rty = infer lvl env' rest in
    let slot = { Tast.binds = []; gbody = tr } in
    g.gslot <- Some slot;
    ret loc (Tast.Let slot) rty
  end

and infer_bin lvl env loc op a b =
  match op with
  | Ast.Add | Ast.Sub | Ast.Mul | Ast.Div | Ast.Mod ->
    let ta = check lvl env a Iint in
    let tb = check lvl env b Iint in
    ret loc (Tast.Bin (op, ta, tb)) Iint
  | Ast.Fadd | Ast.Fsub | Ast.Fmul | Ast.Fdiv ->
    let ta = check lvl env a Ifloat in
    let tb = check lvl env b Ifloat in
    ret loc (Tast.Bin (op, ta, tb)) Ifloat
  | Ast.And | Ast.Or ->
    let ta = check lvl env a Ibool in
    let tb = check lvl env b Ibool in
    ret loc (Tast.Bin (op, ta, tb)) Ibool
  | Ast.Lt | Ast.Le | Ast.Gt | Ast.Ge ->
    let ta, aty = infer lvl env a in
    let tb = check_at lvl env b aty "both sides of a comparison" in
    (* which of ilt and flt to emit is only known once the operand type settles, so the
       check runs after inference rather than here *)
    defer (fun () ->
        match repr aty with
        | Ivar _ -> ( try unify aty Iint with Clash -> ())
        | Iint | Ifloat -> ()
        | t -> err loc "%s expects Int or Float, found %s" (show_binop op) (show t));
    ret loc (Tast.Bin (op, ta, tb)) Ibool
  | Ast.Eq | Ast.Ne ->
    let ta, aty = infer lvl env a in
    let tb = check_at lvl env b aty "both sides of a comparison" in
    defer (fun () ->
        let t = zonk aty in
        if not (comparable t)
        then
          err loc "%s cannot compare values of type %s, which contains a function"
            (show_binop op) (show_ty t));
    ret loc (Tast.Bin (op, ta, tb)) Ibool

and infer_un lvl env loc op a =
  match op with
  | Ast.Neg ->
    let t = check lvl env a Iint in
    ret loc (Tast.Un (op, t)) Iint
  | Ast.Fneg ->
    let t = check lvl env a Ifloat in
    ret loc (Tast.Un (op, t)) Ifloat
  | Ast.Not ->
    let t = check lvl env a Ibool in
    ret loc (Tast.Un (op, t)) Ibool
  | Ast.To_float ->
    let t = check lvl env a Iint in
    ret loc (Tast.Un (op, t)) Ifloat
  | Ast.To_int ->
    let t = check lvl env a Ifloat in
    ret loc (Tast.Un (op, t)) Iint
  | Ast.Fst | Ast.Snd ->
    let t, ty = infer lvl env a in
    let x = fresh lvl and y = fresh lvl in
    (try unify ty (Ipair (x, y)) with
     | Clash ->
       err a.Ast.loc "%s expects a tuple, found %s" (show_unop op) (show ty));
    ret loc (Tast.Un (op, t)) (if op = Ast.Fst then x else y)

(* ---------------------------------------------------------- monomorphisation *)

and instance g key =
  incr instances;
  if !instances > 500
  then
    err g.gloc
      "too many specialisations of one binding; polymorphic recursion is not supported";
  let names = List.map (fun (nm, _) -> spec_name nm) g.gmembers in
  g.gdone <- (key, names) :: g.gdone;
  let slot =
    match g.gslot with
    | Some s -> s
    | None -> err g.gloc "internal: a generalised binding has no place to expand into"
  in
  (match g.gsrc, key, names with
   | Gval rhs, [ k ], [ nm ] ->
     let t = check g.glevel g.genv rhs (of_ast k) in
     slot.Tast.binds <- slot.Tast.binds @ [ Tast.Bval (nm, t) ]
   | Grec lrs, _, _ ->
     let trip = List.map2 (fun (lr, nm) k -> lr, nm, k) (List.combine lrs names) key in
     let env =
       List.fold_left
         (fun acc (lr, nm, k) -> (lr.Ast.name, Emono (nm, of_ast k)) :: acc)
         g.genv trip
     in
     let fnodes =
       List.map
         (fun (lr, nm, k) ->
           match of_ast k with
           | Iarrow (pt, rt) ->
             let benv = (lr.Ast.param, Emono (lr.Ast.param, pt)) :: env in
             let tb = check g.glevel benv lr.Ast.body rt in
             { Tast.fname = nm
             ; fparam = lr.Ast.param
             ; fparam_ty = zonk pt
             ; fret_ty = zonk rt
             ; fbody = tb
             }
           | _ -> err lr.Ast.rloc "internal: a recursive binding is not a function")
         trip
     in
     slot.Tast.binds <- slot.Tast.binds @ [ Tast.Brec fnodes ]
   | _ -> err g.gloc "internal: malformed specialisation");
  names

(* run the deferred operand checks and expand every generalised binding, repeating until
   neither produces anything new; expanding one binding can uncover uses of another *)
let settle () =
  let rec loop n =
    if n > 1000 then err no_loc "type checking did not converge";
    let ds = List.rev !deferred in
    deferred := [];
    List.iter (fun f -> f ()) ds;
    let progress = ref (ds <> []) in
    List.iter
      (fun g ->
        while g.uhandled < List.length g.guses do
          let u = List.nth g.guses g.uhandled in
          g.uhandled <- g.uhandled + 1;
          progress := true;
          let key = List.map zonk u.uargs in
          let names =
            match
              List.find_opt
                (fun (k, _) ->
                  List.length k = List.length key && List.for_all2 equal_ty k key)
                g.gdone
            with
            | Some (_, ns) -> ns
            | None -> instance g key
          in
          u.uref.Tast.vname <- List.nth names u.umember
        done)
      !groups;
    if !progress || !deferred <> [] then loop (n + 1)
  in
  loop 0

let program (e : Ast.expr) : Tast.t =
  groups := [];
  patches := [];
  deferred := [];
  tv_counter := 0;
  uid := 0;
  instances := 0;
  let t, _ = infer 0 [] e in
  settle ();
  List.iter (fun f -> f ()) (List.rev !patches);
  patches := [];
  groups := [];
  t
