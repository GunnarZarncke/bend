#!/bin/sh
# hypervisor: assembles the test guests and prints their words, the
# tables hv_guest_a..d in hv.c. Each guest runs at EL1 with no MMU; its
# hypercalls are hvc #1 (print x0 as a character), hvc #0 (yield) and
# hvc #2 (quit). D writes a block it does not own and is stopped.
#
#   sh demos/hypervisor/gen_guests.sh
set -e
out=${TMPDIR:-/tmp}/bend-guests.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT
guest() {
  printf '%s\n' "$2" > "$out/$1.S"
  clang --target=aarch64-none-elf -c "$out/$1.S" -o "$out/$1.o"
  ld.lld --oformat=binary --image-base=0 -Ttext=0 -e 0 "$out/$1.o" -o "$out/$1.bin"
  printf '%s: ' "$1"
  od -An -tx4 -v "$out/$1.bin" | tr -s ' \n' ' '
  printf '\n'
}
guest a '  mov x19, #3
1: mov x0, #65
  hvc #1
  hvc #0
  subs x19, x19, #1
  b.ne 1b
  hvc #2
  b .'
guest b '  mov x19, #3
1: mov x0, #66
  hvc #1
  hvc #0
  subs x19, x19, #1
  b.ne 1b
  hvc #2
  b .'
guest c '  mov x0, #67
  hvc #1
  mov x19, #0x4000000
1: subs x19, x19, #1
  b.ne 1b
  mov x0, #67
  hvc #1
  hvc #2
  b .'
guest d '  mov x0, #68
  hvc #1
  mov x0, #0x40000000
  str x0, [x0]
  mov x0, #68
  hvc #1
  hvc #2
  b .'
