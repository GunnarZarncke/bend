#!/bin/sh
# hypervisor: writes Segments.bend, the shim's symbolic paths -- entering
# a guest, the two ways out of it, and the five arms of the exit decoding
# -- each cut into segments the BendTT kernel can check. The kernel
# spends its fuel on a run of more than about seventeen steps, most of it
# on the pc: by then the pc is a chain of adds that every fetch reduces
# again. A segment that starts from a state written out has no chain, so
# short segments are cheap, and Chain.bend adds them back up.
#
# The states are symbolic, so they come from bend2 itself: a deliberately
# false claim about the state after k steps makes the checker print its
# normal form, which is Bend source but for the text of Shim.rom() and of
# the cells the path starts with, which this puts back as the calls they
# came from. Whatever it writes the checker checks, so an error here is a
# proof that fails, never a proof that passes wrongly.
#
#   sh demos/hypervisor/gen_seg.sh [--cut <n>] [--guests <n>] [--kernel]
#
# --kernel checks each segment with the kernel as it is made and halves
# it until it fits, which the tail of an exit path and of the decode
# need; without it the cut is taken as given. SPEC.md, section 14, has
# the cuts it found. The gate does not run this: it runs the proof, which
# fails if Segments.bend is stale. BEND=... picks another checker.
#
# It is shell because a state runs to some seventeen thousand characters
# and a Bend program cannot rebuild a string that long (SPEC.md, section
# 14), and because gates/repo.ts allows a demo .sh and not a .ts. The
# work is one awk call per state, so the shape of a state is parsed in
# awk and everything else is printf.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
out=${TMPDIR:-/tmp}/bend-seg.$$
mkdir -p "$out"
trap 'rm -rf "$out"' EXIT

cut=8
guests=4
kernel=
while [ $# -gt 0 ]; do
  case $1 in
    --cut)    cut=$2; shift 2 ;;
    --guests) guests=$2; shift 2 ;;
    --kernel) kernel=1; shift ;;
    *) echo "gen_seg: unknown option $1" >&2; exit 1 ;;
  esac
done

bend=${BEND:-bun $root/bend2/main.ts}
probe=$here/t_seg.bend
check=$here/t_segck.bend
target=$here/Segments.bend

die() {
  echo "gen_seg: $1" >&2
  [ -z "$2" ] || head -c 1500 "$2" >&2
  exit 1
}

# Shapes
# ------
# the parameters every def of a path takes, the arguments a call passes,
# and the match that puts the records the run reads apart into their
# words. A state that names only variables it never forces needs no match
# for them, so the decode's shape is the shorter one.

pats() {   # the W64 patterns of a record's fields, under one prefix
  pre=$1
  shift
  sep=
  for n in "$@"; do
    printf '%sHv.W64{+%s%sh, +%s%sl}' "$sep" "$pre" "$n" "$pre" "$n"
    sep=", "
  done
}

xs=$(i=0; while [ $i -le 30 ]; do printf 'x%s ' $i; i=$((i + 1)); done)
rs=$(i=0; while [ $i -le 16 ]; do printf 'r%s ' $i; i=$((i + 1)); done)
host=$(i=2; while [ $i -le 30 ]; do printf 'x%s ' $i; i=$((i + 1)); done)

hpat=$(pats h $host)
fpat=$(pats f $xs sp1 sp0 elr spsr $rs esr far hpfar)

switch_p="+h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>,\
 +mem: List<&2, I.Cell>, +f: Shim.Saved, +s2: Hv.Tree<Bool>"
switch_a="h, nzcv, daif, sys, mem, f, s2"
switch_m="  match h f:
    case Shim.Host{$hpat} Shim.Saved{$fpat}:"

rest_p="+h: Shim.Host, +nzcv: U32, +daif: U32, +sys: List<&2, I.Sr>,\
 +mem: List<&2, I.Cell>, +s2: Hv.Tree<Bool>, +lh: U32, +ll: U32"
rest_a="h, nzcv, daif, sys, mem, s2, lh, ll"

decode_p="+esr: Hv.W64, +fh: U32, +fl: U32, +ph: U32, +pl: U32, +ar: Hv.W64, $rest_p"
decode_a="esr, fh, fl, ph, pl, ar, $rest_a"
decode_m="  match h:
    case Shim.Host{$hpat}:"

step_p="+esr: Hv.W64, +fault: Hv.W64, +hpfar: Hv.W64, +eh: U32, +el: U32, $rest_p"
step_a="esr, fault, hpfar, eh, el, $rest_a"
step_m=$decode_m

use_shape() {
  case $1 in
    switch) sh_p=$switch_p; sh_a=$switch_a; sh_m=$switch_m ;;
    decode) sh_p=$decode_p; sh_a=$decode_a; sh_m=$decode_m ;;
    step)   sh_p=$step_p;   sh_a=$step_a;   sh_m=$step_m ;;
  esac
}

head_text="import Base
import ./main.bend as Hv
import ./Isa.bend as I
import ./Shim.bend as Shim
import ./Chain.bend as C
"

banner="# The shim's paths, run on Isa.bend in segments, so that the BendTT
# kernel can check them: a whole path in one def is past its fuel.
# Written by gen_seg.sh, do not edit. SPEC.md, section 14.
"

# a state with nothing in it: the marker the false claim compares against
mcpu="I.Cpu{Nil{}, Hv.W64{0, 0}, 0, 0, 0, 0, Nil{}}"
mrom="I.Rom{Hv.W64{0, 0}, 0, Nil{}}"
mark="I.State{$mcpu, Nil{}, $mrom, s2}"

# Paths
# -----
# the runs the shim's laws speak of. A path whose run reads no memory of
# the guest's area holds for every guest, so it is built once: p_once.
# p_proj holds @O@ where the run goes.

exit_tail="Shim.cells(Shim.Host.saved(h), I.W.sub(Shim.stack(), I.W.of(96)),\
 Shim.cell2(Shim.persist(), I.W.sub(Shim.stack(), I.W.of(96)), mem))"

decode_far="Shim.fault_at(Hv.W64{fh, fl}, Hv.W64{ph, pl})"

npaths=8

set_path() {   # $1 the path's number, $2 the guest
  g=$2
  p_once=
  p_tail=
  p_type="Maybe<&2, Shim.Decided>"
  p_proj="Shim.decided(@O@)"
  p_shape=decode
  case $1 in
    0) p_name=en; p_total=68; p_shape=switch
       p_start="Shim.enter_state($g, h, nzcv, daif, sys, mem, f, s2)"
       p_tail="Shim.cells(Shim.Saved.list(f), Shim.area($g), mem)"
       p_proj="Shim.entered(@O@)"
       p_want="Shim.entered.want($g, h, f)"
       p_type="Maybe<&2, Shim.Entered>" ;;
    1|2)
       if [ "$1" = 1 ]; then p_name=xs; vec=1024; kind=0
       else p_name=xi; vec=1152; kind=1
       fi
       p_total=80; p_shape=switch
       p_start="Shim.exit_state($g, $vec, h, nzcv, sys, mem, f, s2)"
       p_tail=$exit_tail
       p_proj="Shim.exited($g, @O@)"
       p_want="Shim.exited.want($kind, h, f)"
       p_type="Maybe<&2, Shim.Exited>" ;;
    3) p_name=dh; p_total=9;  cls=22; kind=1; far="I.W.of(0)" ;;
    4) p_name=dd; p_total=17; cls=36; kind=2; far=$decode_far ;;
    5) p_name=di; p_total=19; cls=32; kind=3; far=$decode_far ;;
    6) p_name=do; p_total=14; cls=24; kind=5; far="I.W.of(0)" ;;
    7) p_name=ow; p_total=18; p_shape=step
       p_start="Shim.decide_mid(Hv.W64{0, 1}, esr, fault, hpfar,\
 Shim.area($g), h, nzcv, daif, sys,\
 I.Cell{Shim.at(Shim.area($g), 264), Hv.W64{eh, el}} <> mem, s2,\
 Hv.W64{lh, ll})"
       p_proj="Shim.stepped($g, @O@)"
       p_want="Shim.stepped.want(Hv.W64{eh, el}, Hv.W64{lh, ll})"
       p_type="Maybe<&2, Shim.Stepped>" ;;
  esac
  case $1 in
    3|4|5|6)
       p_once=1
       p_start="Shim.decide_mid(Hv.W64{0, $cls}, esr, Hv.W64{fh, fl},\
 Hv.W64{ph, pl}, ar, h, nzcv, daif, sys, mem, s2, Hv.W64{lh, ll})"
       p_want="Shim.decided.want($kind, $far, Hv.W64{lh, ll})" ;;
  esac
  if [ -n "$p_once" ]; then tag="${p_name}_"; else tag="${p_name}${g}_"; fi
  use_shape $p_shape
}

proj() {   # the path's view of one Out expression
  awk -v o="$1" -v p="$p_proj" 'BEGIN {
    i = index(p, "@O@")
    printf "%s%s%s", substr(p, 1, i - 1), o, substr(p, i + 3)
  }'
}

# bend2
# -----

run_bend() {   # the checker on one file, output and errors together
  $bend "$1" ${2+"$2"} 2>&1 || true
}

# the normal form of a state expression, as Bend source, into $out/term.
# $out/defs holds the defs it may name.
dump() {
  { printf '%s' "$head_text"; cat "$out/defs"
    printf '\ndef probe(%s) -> {%s == %s : I.State}:\n%s\n      {==}\n' \
      "$sh_p" "$1" "$mark" "$sh_m"
  } > "$probe"
  run_bend "$probe" > "$out/said"
  sed -n -e 's/^- expected : //p' -e 's/^- observed : //p' "$out/said" > "$out/two"
  [ "$(grep -c . "$out/two")" = 2 ] \
    || die "bend2 printed no pair of terms" "$out/said"
  awk 'length($0) > length(l) { l = $0 } END { printf "%s", l }' \
    "$out/two" > "$out/term"
  grep -q '\^' "$out/term" \
    && die "the term names a shadowed variable: $(head -c 300 "$out/term")"
  grep -q '^I\.State{' "$out/term" \
    || die "bend2 printed no state" "$out/said"
}

# the four arguments of a printed I.State{..}, into $out/f1 .. $out/f4
fields() {
  awk -v d="$out" '{
    b = index($0, "{")
    s = substr($0, b + 1, length($0) - b - 1)
    depth = 0
    at = 1
    n = 0
    for (i = 1; i <= length(s); i += 1) {
      c = substr(s, i, 1)
      if (c == "{" || c == "[" || c == "(") { depth += 1 }
      else if (c == "}" || c == "]" || c == ")") { depth -= 1 }
      else if (c == "," && depth == 0) {
        n += 1
        f = substr(s, at, i - at)
        gsub(/^ +| +$/, "", f)
        printf "%s", f > (d "/f" n)
        at = i + 1
      }
    }
    n += 1
    f = substr(s, at)
    gsub(/^ +| +$/, "", f)
    printf "%s", f > (d "/f" n)
  }' "$1"
}

# Folding
# -------
# A state as bend2 prints it holds the whole text of the rom and of the
# cells the path starts with: a thousand words that every segment would
# repeat. Both are asked for once, and put back as the calls they are.

fold_open() {   # the two texts, for the path now in p_tail
  printf '%s' "" > "$out/defs"
  dump "I.State{$mcpu, Nil{}, Shim.rom(), s2}"
  fields "$out/term"
  cp "$out/f3" "$out/rom"
  printf '%s' "" > "$out/cells"
  [ -z "$p_tail" ] || {
    dump "I.State{$mcpu, $p_tail, $mrom, s2}"
    fields "$out/term"
    cp "$out/f2" "$out/cells"
  }
}

fold() {   # $out/term into $out/body, the rom and the cells named again
  fields "$out/term"
  cmp -s "$out/f3" "$out/rom" \
    || die "the state's text is not Shim.rom(): $(head -c 200 "$out/f3")"
  { printf 'I.State{'; cat "$out/f1"; printf ', '
    if [ -s "$out/cells" ]; then
      awk -v rep="$p_tail" 'NR == FNR { sf = $0; next } {
        n = length($0)
        m = length(sf)
        if (substr($0, n - m + 1) == sf) { printf "%s%s", substr($0, 1, n - m), rep }
        else { printf "%s", $0 }
      }' "$out/cells" "$out/f2"
    else
      cat "$out/f2"
    fi
    printf ', Shim.rom(), '; cat "$out/f4"; printf '}'
  } > "$out/body"
}

# Emitting
# --------

mid_def() {   # $1 the name, $2 the file holding the body
  printf 'def %s(%s) -> I.State:\n%s\n      ' "$1" "$sh_p" "$sh_m"
  cat "$2"
  printf '\n\n'
}

seg_law() {   # $1 the name, $2 the state before, $3 the def after, $4 steps
  printf 'def %s(%s) -> {I.steps(%sn, I.Run{%s}) == I.Run{%s(%s)} : I.Out}:\n%s\n      {==}\n\n' \
    "$1" "$sh_p" "$4" "$2" "$3" "$sh_a" "$sh_m"
}

kernel_ok() {   # whether the kernel checks the file it is handed
  cp "$1" "$check"
  run_bend "$check" --verdict | grep -q '^ALL PROOFS CHECK$'
}

# Building
# --------
# one path of one guest: each state is asked of bend2 from the one before
# it, so the words are always the checker's own normal form. $out/mids
# holds every mid def, $out/laws the laws that join them, $out/refs one
# line per state, and cuts the steps of each segment.

build() {
  fold_open
  printf '%s' "" > "$out/mids"
  printf '%s' "" > "$out/laws"
  printf '%s\n' "$p_start" > "$out/refs"
  cuts=
  ncuts=0
  at=0
  prev=$p_start
  printf '%s' "" > "$out/prev"
  while [ "$at" -lt "$p_total" ]; do
    n=$((p_total - at))
    [ "$n" -le "$cut" ] || n=$cut
    while :; do
      name="${tag}$((ncuts + 1))"
      cp "$out/mids" "$out/defs"
      dump "I.Out.s(I.steps(${n}n, I.Run{$prev}))"
      fold
      { cat "$out/prev"; mid_def "$name" "$out/body"
        seg_law "${tag}s${ncuts}" "$prev" "$name" "$n"
      } > "$out/one"
      if [ -z "$kernel" ]; then break; fi
      { printf '%s\n' "$head_text"; cat "$out/one"; } > "$out/try"
      if kernel_ok "$out/try"; then break; fi
      n=$((n / 2))
      [ "$n" -gt 0 ] || die "$name: even one step is past the kernel's fuel"
      echo "    $((n * 2)) steps did not fit; trying $n"
    done
    mid_def "$name" "$out/body" > "$out/prev"
    cat "$out/prev" >> "$out/mids"
    seg_law "${tag}s${ncuts}" "$prev" "$name" "$n" >> "$out/laws"
    prev="$name($sh_a)"
    printf '%s\n' "$prev" >> "$out/refs"
    cuts="$cuts $n"
    ncuts=$((ncuts + 1))
    at=$((at + n))
    echo "  $name: $at/$p_total steps, $(wc -c < "$out/body" | tr -d ' ') chars"
  done
  echo "  cuts $(echo $cuts | tr ' ' ',')"
}

nth() {   # the $1st word of $2, counting from zero
  echo "$2" | awk -v k="$1" '{ printf "%s", $(k + 1) }'
}

ref() {   # the $1st state of the path, counting from zero
  sed -n "$(($1 + 1))p" "$out/refs"
}

# Chaining
# --------
# the segments joined back into the whole run, and the run into the law:
# a run of m + n steps is a run of m and then a run of n (Chain.bend).

chain() {
  last=$(ref "$ncuts")
  k=$((ncuts - 1))
  while [ "$k" -ge 0 ]; do
    nk=$(nth "$k" "$cuts")
    tk=$(echo "$cuts" | awk -v k="$k" '{ s = 0; for (i = k + 1; i <= NF; i += 1) s += $i; printf "%s", s }')
    tn=$((tk - nk))
    rk=$(ref "$k")
    rn=$(ref "$((k + 1))")
    a="I.steps(${tk}n, I.Run{$rk})"
    ab="I.steps(${tn}n, I.steps(${nk}n, I.Run{$rk}))"
    mid="I.steps(${tn}n, I.Run{$rn})"
    if [ "$k" = "$((ncuts - 1))" ]; then rest="{==}"; else rest="${tag}r$((k + 1))($sh_a)"; fi
    cat <<EOF
def ${tag}r${k}($sh_p) -> {$a == I.Run{$last} : I.Out}:
  Equal.trans(I.Out, $a, $ab, I.Run{$last},
    C.steps_add(${nk}n, ${tn}n, I.Run{$rk}),
    Equal.trans(I.Out, $ab, $mid, I.Run{$last},
      Equal.cong(I.Out, I.Out, o => I.steps(${tn}n, o),
        I.steps(${nk}n, I.Run{$rk}), I.Run{$rn},
        ${tag}s${k}($sh_a)),
      $rest))

EOF
    k=$((k - 1))
  done
  total=$(echo "$cuts" | awk '{ s = 0; for (i = 1; i <= NF; i += 1) s += $i; printf "%s", s }')
  fin=$(proj "I.Run{$last}")
  lhs=$(proj "I.steps(${total}n, I.Run{$p_start})")
  cat <<EOF
def ${tag}fin($sh_p) -> {$fin == $p_want : $p_type}:
$sh_m
      {==}

def ${tag}law($sh_p) -> {$lhs == $p_want : $p_type}:
  Equal.trans($p_type, $lhs, $fin, $p_want,
    Equal.cong(I.Out, $p_type, o => $(proj o),
      I.steps(${total}n, I.Run{$p_start}), I.Run{$last}, ${tag}r0($sh_a)),
    ${tag}fin($sh_a))

EOF
}

# Main
# ----

echo "gen_seg: asking bend2 for the states"
printf '%s' "" > "$out/all"
g=0
while [ "$g" -lt "$guests" ]; do
  i=0
  while [ "$i" -lt "$npaths" ]; do
    set_path "$i" "$g"
    if [ -n "$p_once" ] && [ "$g" -gt 0 ]; then i=$((i + 1)); continue; fi
    echo "$tag: $p_total steps"
    build
    { cat "$out/mids" "$out/laws"; chain; } >> "$out/all"
    i=$((i + 1))
  done
  g=$((g + 1))
done

{ printf '%s\n%s\n' "$banner" "$head_text"; cat "$out/all"; } > "$target"
rm -f "$probe" "$check"
echo "gen_seg: wrote ${target#"$root/"}, $(wc -c < "$target" | tr -d ' ') bytes"
