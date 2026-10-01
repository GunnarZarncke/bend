#!/bin/sh
# hypervisor: assembles the trap shim of hv_state.c (the __asm__ block:
# hv_enter, hv_exit, the saves, the vectors) on its own, links it at
# 0x40100000 with __persist_start at 0x90000000, and writes its words
# and symbols to shim_words.bend, which PROOF.bend runs on Isa.bend.
#
#   sh demos/hypervisor/gen_shim.sh
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${TMPDIR:-/tmp}/bend-shim.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT
{ echo 'typedef unsigned long long u64;'
  sed -n '/^#define HV_SYS(X)/,/^);/p' "$here/hv_state.c"; } > "$out/shim.c"
clang --target=aarch64-none-elf -c "$out/shim.c" -o "$out/shim.o"
flags="-Ttext=0x40100000 --defsym=__persist_start=0x90000000 --defsym=bare_fault=0x40200000 -e 0"
ld.lld $flags "$out/shim.o" -o "$out/shim.elf"
ld.lld $flags --oformat=binary "$out/shim.o" -o "$out/shim.bin"
sym() { nm "$out/shim.elf" | awk -v s="$1" '$3 == s { print $1 }'; }
{
  echo "# hypervisor: the trap shim of hv_state.c as words, linked at"
  echo "# 0x40100000; written by gen_shim.sh, do not edit"
  echo ""
  echo "import Base"
  echo ""
  for s in hv_enter hv_exit hv_exit_sync hv_exit_irq hv_decide hv_vectors; do
    printf 'def %s() -> U32:\n  %d\n\n' "$s" "$((0x$(sym $s)))"
  done
  printf 'def size() -> U32:\n  %d\n\n' "$(wc -c < "$out/shim.bin" | tr -d ' ')"
  echo "def words() -> List<&2, U32>:"
  od -An -tu4 -v "$out/shim.bin" | tr -s ' \n' ' ' | sed 's/^ //; s/ $//; s/ /, /g' \
    | fold -s -w 76 | sed 's/ *$//; s/^/    /; 1s/^    /  [/; $s/,*$/]/'
  echo
} > "$here/shim_words.bend"
