#!/bin/sh
# hypervisor: builds bare.bend with build.sh, boots it on QEMU (virt,
# GICv3, 2 GiB) and checks the run: A and B print three letters, C two,
# D one before its abort stops it; the timer preempts C at least once;
# at least one handoff; a clean halt. Prints PASS or the failing check.
#
#   sh demos/hypervisor/run.sh          (BEND="bun bend2/main.ts" to use the tree)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bend=${BEND:-bend}
out=${TMPDIR:-/tmp}/bend-hv.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT
BEND="$bend" sh "$here/build.sh" "$here/bare.bend" "$out/hv.elf"
perl -e 'alarm 120; exec @ARGV' qemu-system-aarch64 \
  -machine virt,virtualization=on,gic-version=3 -cpu cortex-a72 -m 2048 \
  -nographic -semihosting -kernel "$out/hv.elf" > "$out/hv.out" 2>&1 \
  || { echo "FAIL: qemu exited $?"; cat "$out/hv.out"; exit 1; }
cat "$out/hv.out"
count() { grep -c "^$1\$" "$out/hv.out" || true; }
check() { [ "$1" = "$2" ] || { echo "FAIL: $3: got $1, want $2"; exit 1; }; }
check "$(count A)" 3 "A prints"
check "$(count B)" 3 "B prints"
check "$(count C)" 2 "C prints"
check "$(count D)" 1 "D prints"
check "$(grep -c '^3: data abort' "$out/hv.out")" 1 "D's abort"
for g in 0 1 2 3; do
  check "$(count "\\[guest $g stopped\\]")" 1 "guest $g stops once"
done
[ "$(grep -c '^2: timer' "$out/hv.out")" -ge 1 ] || { echo "FAIL: no timer exit"; exit 1; }
[ "$(grep -c 'instance ends: handoff' "$out/hv.out")" -ge 1 ] || { echo "FAIL: no handoff"; exit 1; }
check "$(count 'halt: no guest runs')" 1 "the halt"
echo PASS
