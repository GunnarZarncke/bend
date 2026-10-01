#!/bin/sh
# hypervisor: assembles the test guests and prints their words, the
# tables hv_guest_a..d (set 0, run.sh's) and hv_guest_e0..e3 (set 1,
# diff.sh's) in hv.c, and set 1's lists in model.bend. Each guest runs at
# EL1 with no MMU; its hypercalls are hvc #1 (print x0 as a character),
# hvc #0 (yield) and hvc #2 (quit). D writes a block it does not own and
# is stopped. Set 1 exercises every form Isa.bend models: E0 arithmetic,
# flags and branches, and an unknown call; E1 loads, stores and pairs in
# every addressing mode, then a read of a block it does not own; E2 the
# EL1 system registers and a trapped WFI; E3 a branch out of its blocks.
# E0 ends in a write outside the guest region's GiB (a level-1 fault),
# E1 in a read inside it (level 2).
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
guest e0 '  mov x1, #5
  mov x2, #0
1: add x2, x2, #3
  subs x1, x1, #1
  b.ne 1b
  mov x0, x2
  add x0, x0, #50
  hvc #1
  mov x3, #0xffff0000
  add w4, w3, #1
  subs w5, w4, w4
  b.eq 2f
  hvc #9
2: hvc #7
  subs x6, x0, #1
  b.mi 3f
  hvc #9
3: mov x0, #69
  hvc #1
  movz x8, #0xff00
  movk x8, #0x1234, lsl #16
  movk x8, #0xabcd, lsl #32
  movk x8, #0x0007, lsl #48
  lsr x9, x8, #40
  lsl x10, x9, #33
  and x11, x10, x8
  lsr x12, x8, #7
  lsl x13, x12, #3
  and x14, x13, x10
  lsr w15, w8, #5
  lsl w16, w15, #9
  and w17, w16, w8
  orr x18, x14, x17
  hvc #0
  mov x7, #0x40000000
  str x7, [x7, #8]
  b .'
guest e1 '  mov x20, sp
  mov x1, #0x1234
  mov x2, #0x5678
  stp x1, x2, [sp, #-16]!
  str x1, [sp, #-8]!
  ldr x3, [sp], #8
  ldp x4, x5, [sp], #16
  sub x21, x20, #64
  str x5, [x21]
  str x4, [x21, #8]
  ldr x6, [x21, #8]
  ldp x7, x8, [x21]
  str x1, [x21, #16]!
  ldr x9, [x21], #-16
  stp x3, x9, [x21, #32]
  add x0, x6, #0
  sub x0, x0, #1, lsl #12
  sub x0, x0, #0x1e7
  hvc #1
  mov x10, #0xa8000000
  ldr x11, [x10]
  hvc #2
  b .'
guest e2 '  mov x1, #0x1111
  msr tpidr_el1, x1
  mov x2, #0x2222
  msr tpidr_el0, x2
  msr tpidrro_el0, x2
  msr contextidr_el1, x1
  mov x3, #0x3000
  msr vbar_el1, x3
  msr far_el1, x2
  msr esr_el1, x1
  msr mair_el1, x2
  mrs x4, tpidr_el1
  mrs x5, tpidr_el0
  add x6, x4, x5
  mov x0, #83
  hvc #1
  wfi
  mov x0, #87
  hvc #1
  hvc #2
  b .'
guest e3 '  mov x0, #73
  hvc #1
  b . + 0x4000000
  hvc #2'
