#!/bin/sh
# hypervisor: builds a Bend program (no `!`) for the bare host: a
# freestanding ARM64 ELF for EL2 on QEMU virt with -m 2048. The compiler
# emits the C; clang and lld build it with boot.c as its host
# (-DBEND_HOST), bare.c as its libc (-include) and the linker script
# below: the image at 0x40080000, the runtime's arena (1 GiB, its corpus
# lays 409 MiB) at 0x48000000, the persist region (16 MiB, kept across
# restarts) at 0x90000000, the term stack (32 MiB) at the top of RAM, so
# a deep recursion runs off it and faults. Only the image loads.
#
#   sh demos/hypervisor/build.sh x.bend x.elf   (BEND="bun bend2/main.ts" for the tree)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bend=${BEND:-bend}
tmp=${TMPDIR:-/tmp}/bend-bare.$$
mkdir -p "$tmp"
trap 'rm -rf "$tmp"' EXIT
$bend "$1" -o "$tmp/main.c"
grep -q '^#define BANGS *0$' "$tmp/main.c" \
  || { echo "build.sh: a ! program cannot build for the bare host: it runs one core" >&2; exit 1; }
cat > "$tmp/link.ld" <<'EOF'
ENTRY(_start)
SECTIONS {
  . = 0x40080000;
  .text : { KEEP(*(.text.boot)) *(.text*) }
  .rodata : { *(.rodata*) }
  .init_array : {
    __init_array_start = .;
    KEEP(*(.init_array*))
    __init_array_end = .;
  }
  .data : { *(.data*) }
  .bss (NOLOAD) : { . = ALIGN(16); __bss_start = .; *(.bss*) *(COMMON) . = ALIGN(16); __bss_end = .; }
  .stack (NOLOAD) : { . = ALIGN(16); . += 1M; __stack_top = .; }
  . = 0x48000000;
  .arena (NOLOAD) : { __arena_start = .; . += 1024M; __arena_end = .; }
  . = 0x90000000;
  .persist (NOLOAD) : { __persist_start = .; . += 16M; __persist_end = .; }
  . = 0xBE000000;
  .tstack (NOLOAD) : { __stack_lo = .; . += 32M; __stack_hi = .; }
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
EOF
clang --target=aarch64-none-elf -ffreestanding -nostdlib -fno-builtin \
  -fno-math-errno -mno-outline-atomics -std=c11 -O3 -I"$here" \
  -include "$here/bare.c" -DBEND_HOST='"boot.c"' -fuse-ld=lld -Wl,-T,"$tmp/link.ld" -Wl,--gc-sections \
  "$tmp/main.c" -o "$2"
