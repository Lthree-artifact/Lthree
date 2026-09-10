#!/usr/bin/env bash
# validate_all.sh --inputs DIR[,DIR...] --outdir RESULTS [--jobs N] [validate.sh options...]
#   Runs validate.sh on every *.lean under the input directories (N cases in flight)
#   and writes RESULTS/summary.tsv (case, verdict, prove status, refute status, tier, seconds).
#   --cases "a b c"   whitelist of case names
set -o pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
INPUTS=""; RESULTS=""; JOBS=1; CASES=""; PASS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --inputs) INPUTS="$2"; shift 2 ;;
    --outdir) RESULTS="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --cases) CASES="$2"; shift 2 ;;
    -h|--help) sed -n '2,6p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 2 ;;
    *) PASS+=("$1"); shift ;;
  esac
done
[[ -n "$INPUTS" && -n "$RESULTS" ]] || { sed -n '2,6p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 2; }
mkdir -p "$RESULTS"; RESULTS="$(cd "$RESULTS" && pwd)"
IFS=',' read -r -a DIRS <<< "$INPUTS"
LIST=()
while IFS= read -r f; do
  c="$(basename "$f" .lean)"
  if [[ -n "$CASES" && " $CASES " != *" $c "* ]]; then continue; fi
  LIST+=("$f")
done < <(find "${DIRS[@]}" -name '*.lean' | sort)
echo "[validate_all] ${#LIST[@]} inputs, $JOBS in flight, results in $RESULTS"
[[ ${#LIST[@]} -gt 0 ]] || exit 1
for f in "${LIST[@]}"; do
  while [[ "$(jobs -rp | wc -l)" -ge "$JOBS" ]]; do wait -n; done
  c="$(basename "$f" .lean)"
  ( bash "$HERE/validate.sh" "$f" --outdir "$RESULTS/$c" "${PASS[@]}" > "$RESULTS/$c.log" 2>&1 ) &
done
wait
printf 'case\tverdict\tprove\trefute\ttier\tseconds\n' > "$RESULTS/summary.tsv"
for f in "${LIST[@]}"; do
  c="$(basename "$f" .lean)"
  if [[ -f "$RESULTS/$c/result.tsv" ]]; then cat "$RESULTS/$c/result.tsv"; else printf '%s\terror\t-\t-\t-\t0\n' "$c"; fi
done >> "$RESULTS/summary.tsv"
echo "[validate_all] summary: $RESULTS/summary.tsv"
awk -F'\t' 'NR>1{c[$2]++} END{for(k in c) printf "  %-14s %d\n", k, c[k]}' "$RESULTS/summary.tsv"
