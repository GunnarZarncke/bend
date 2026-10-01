#!/bin/sh
# hypervisor: the demo's gate. The repo's gates run tests/ on the cluster
# under a 30 s cap; this demo needs QEMU and two kernel runs of some
# minutes, so it has its own gate, run on one machine. It checks, in turn:
#
#   sim      main.bend prints the #| lines it ends in
#   words    shim_words.bend is gen_shim.sh's output for hv_state.c now,
#            and hv.c's and model.bend's guest words are gen_guests.sh's
#   laws     bend PROOF.bend --verdict: ALL PROOFS CHECK
#   shim     bend SHIM_PROOF.bend --verdict: ALL PROOFS CHECK. It runs
#            Segments.bend, which gen_seg.sh writes, so a Segments.bend
#            stale against Isa.bend or Shim.bend fails here: its segment
#            laws are claims about the very runs that changed
#   run      run.sh: PASS
#   diff     diff.sh: PASS
#
# Prints one line per check with its time, then PASS, or FAIL and the
# failing check's output.
#
#   sh demos/hypervisor/gate.sh          (BEND="bun bend2/main.ts" to use the tree)
here=$(cd "$(dirname "$0")" && pwd)
bend=${BEND:-bend}
out=${TMPDIR:-/tmp}/bend-hv-gate.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT
fails=0

check() {
  name=$1
  shift
  t0=$(date +%s)
  if "$@" > "$out/$name.log" 2>&1; then
    printf '%-6s ok    %3ss\n' "$name" "$(( $(date +%s) - t0 ))"
  else
    printf '%-6s FAIL  %3ss\n' "$name" "$(( $(date +%s) - t0 ))"
    sed 's/^/  | /' "$out/$name.log" | tail -40
    fails=$((fails + 1))
  fi
}

sim() {
  grep '^#|' "$here/main.bend" | cut -c3- > "$out/sim.want"
  $bend "$here/main.bend" > "$out/sim.got" || return 1
  diff "$out/sim.want" "$out/sim.got"
}

# a guest's words as hex, one per line: from gen_guests.sh's line, from a
# C table, from a Bend list of decimals
gen_words() {
  grep "^$1: " "$out/guests" | cut -d: -f2 | tr -s ' ' '\n' | grep .
}
c_words() {
  sed -n "/hv_guest_$1\[\] = {/,/};/p" "$here/hv.c" | grep -o '0x[0-9a-f]*' | sed 's/^0x//'
}
bend_words() {
  sed -n '/^def guest_code/,/^def base/p' "$here/model.bend" | grep '\[' | sed -n "$1p" \
    | grep -o '[0-9][0-9]*' | while read -r n; do printf '%08x\n' "$n"; done
}

words() {
  cp "$here/shim_words.bend" "$out/shim_words.bend"
  sh "$here/gen_shim.sh" || return 1
  cmp -s "$here/shim_words.bend" "$out/shim_words.bend" \
    || { cp "$out/shim_words.bend" "$here/shim_words.bend"; echo "shim_words.bend is stale: run gen_shim.sh"; return 1; }
  sh "$here/gen_guests.sh" 2>/dev/null | grep '^[a-e][0-9]*: ' > "$out/guests" || return 1
  for g in a b c d e0 e1 e2 e3; do
    gen_words "$g" > "$out/g.gen"
    c_words "$g" > "$out/g.c"
    cmp -s "$out/g.gen" "$out/g.c" || { echo "hv.c's guest $g is stale"; return 1; }
  done
  i=1
  for g in e0 e1 e2 e3; do
    gen_words "$g" > "$out/g.gen"
    bend_words "$i" > "$out/g.bend"
    cmp -s "$out/g.gen" "$out/g.bend" || { echo "model.bend's guest $g is stale"; return 1; }
    i=$((i + 1))
  done
}

verdict() {
  $bend "$here/$1" $2 > "$out/v" 2>&1
  cat "$out/v"
  grep -q '^ALL PROOFS CHECK$' "$out/v"
}

passes() {
  BEND="$bend" sh "$here/$1" > "$out/p" 2>&1
  cat "$out/p"
  tail -1 "$out/p" | grep -q '^PASS$'
}

check sim sim
check words words
check laws verdict PROOF.bend --verdict
check shim verdict SHIM_PROOF.bend --verdict
check run passes run.sh
check diff passes diff.sh

[ "$fails" -eq 0 ] || { echo "FAIL: $fails of 6 checks"; exit 1; }
echo PASS
