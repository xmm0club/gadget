#!/bin/sh
# checks the claims that the readme makes about representation:
#   1. the eval loop contains no allocation point in the emitted machine code
#   2. dispatch is a jump table, not a chain of compares
#   3. operand words are 8 bytes each and the loop allocates nothing at runtime
set -u
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root" || exit 1

obj=_build/default/lib/.gadget.objs/native/gadget__Vm.o
[ -f "$obj" ] || { echo "build first: dune build"; exit 1; }

asm=$(mktemp)
objdump -d "$obj" | sed -n '/<camlGadget__Vm__loop_/,/^0000/p' > "$asm"
allocs=$(grep -cE 'sub +\$0x[0-9a-f]+,%r15' "$asm")
tables=$(grep -cE 'jmp +\*' "$asm")
insns=$(wc -l < "$asm")
rm -f "$asm"

echo "eval loop, from objdump of gadget__Vm.o"
printf "  %-24s %d\n" "machine instructions" "$insns"
printf "  %-24s %d\n" "allocation points" "$allocs"
printf "  %-24s %d\n" "indirect dispatch jumps" "$tables"
[ "$allocs" -eq 0 ] || { echo "FAIL: the eval loop allocates"; exit 1; }
[ "$tables" -ge 1 ] || { echo "FAIL: dispatch is not a jump table"; exit 1; }
echo

for t in typecheck_tests vm_tests layout_tests; do
  ( cd test && "$root/_build/default/test/$t.exe" ) || exit 1
done
