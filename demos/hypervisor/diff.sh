#!/bin/sh
# hypervisor: the differential test of Isa.bend. It builds diff.bend with
# build.sh and boots it on QEMU, runs model.bend on the host, and compares
# the two logs line for line: every action of the kernel and, at every
# exit, the 55 registers the trap shim saved. Guest set 1 (hv.c) takes
# every instruction form the model has, a trapped WFI, a stage-2 write
# fault at level 1, a read fault at level 2 and an instruction fault.
# Prints PASS, or the diff.
#
#   sh demos/hypervisor/diff.sh          (BEND="bun bend2/main.ts" to use the tree)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bend=${BEND:-bend}
out=${TMPDIR:-/tmp}/bend-diff.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT
BEND="$bend" sh "$here/build.sh" "$here/diff.bend" "$out/diff.elf"
perl -e 'alarm 120; exec @ARGV' qemu-system-aarch64 \
  -machine virt,virtualization=on,gic-version=3 -cpu cortex-a72 -m 2048 \
  -nographic -semihosting -kernel "$out/diff.elf" > "$out/qemu.raw" 2>&1 \
  || { echo "FAIL: qemu exited $?"; cat "$out/qemu.raw"; exit 1; }
tr -d '\r' < "$out/qemu.raw" | sed -n '/^diff: start$/,$p' > "$out/qemu.txt"
$bend "$here/model.bend" > "$out/model.txt"
diff "$out/qemu.txt" "$out/model.txt" > "$out/diff.txt" \
  || { echo "FAIL: the model and QEMU differ"; cat "$out/diff.txt"; exit 1; }
for want in "^halt\$" "^0: data abort" "^1: data abort" "^2: wfi" "^3: inst abort"; do
  grep -q "$want" "$out/qemu.txt" || { echo "FAIL: no line $want"; exit 1; }
done
echo "$(grep -c '^file' "$out/qemu.txt") exits, $(grep -c '^act' "$out/qemu.txt") actions agree"
echo PASS
