#!/bin/sh
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 1
objs=_build/default/lib/.gadget.objs/byte
[ -d "$objs" ] || { echo "build the library first: dune build"; exit 1; }
tmp=$(mktemp -d)
out=$(ocamlc -color never -c -I "$objs" -o "$tmp/ill_typed.cmo" \
        test/ill_typed/ill_typed.ml 2>&1)
status=$?
rm -rf "$tmp"
if [ $status -eq 0 ]; then
  echo "FAIL: ill typed bytecode compiled"
  exit 1
fi
printf '%s\n' "$out"
printf '%s\n' "$out" | grep -q "not compatible with type" || {
  echo "FAIL: rejected for the wrong reason"
  exit 1
}
echo
echo "ok: ill typed bytecode is a compile time error"
