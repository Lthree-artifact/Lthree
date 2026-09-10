#!/usr/bin/env bash
# validate.sh INPUT.lean [options]
#   Runs a refinement-proof arm and a counterexample arm on one transformation.
#   --outdir DIR          output directory (default: ./validate_out/<case>)
#   --mode race|both|prove|refute
#                         race: first kernel-accepted verdict wins, the other arm is stopped (default)
#                         both: let both arms finish
#   --proposer llm|enum   counterexample proposer (default llm; enum is deterministic and uses no LLM)
#   --cex-tier auto|strict|kernel|native
#                         auto: strict for single-block pairs; native search + kernel re-check for CFG pairs
#   --attempts N          counterexample rounds (default 5)
#   --witness FILE        try this counterexample JSON first (see cex_search.py for the schema)
#   --budget SEC          LLM budget for the proof arm (default 7200)
#   --witness-budget SEC  LLM budget per counterexample proposal (default 900)
#   --gate-timeout SEC    per `lake env lean` call (default 900)
#   --max-rss-mb MB       memory ceiling per gate (default 24000)
#   --model M --effort E  LLM model / reasoning effort (default gpt-5.5 / xhigh)
# Environment: REPO (Lean project with `lake env lean`), CODEX_CMD (default codex)
set -o pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EMITTER="$HERE/emit_scaffold.py"
CHECK="$HERE/check.py"
SEARCH="$HERE/cex_search.py"
REPO="${REPO:-}"
CODEX_CMD="${CODEX_CMD:-codex}"
MODEL="${MODEL:-gpt-5.5}"; EFFORT="${EFFORT:-xhigh}"
BUDGET=7200; WITNESS_BUDGET=900; GATE_TIMEOUT=900; MAX_RSS_MB=24000
MODE=race; PROPOSER=llm; CEX_TIER=auto; ATTEMPTS=5; OUTDIR=""; WITNESS=""
AUTO_COMPACT="${AUTO_COMPACT:-180000}"

usage() { sed -n '2,20p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 2; }
[[ $# -ge 1 ]] || usage
INPUT="$1"; shift
while [[ $# -gt 0 ]]; do
  case "$1" in
    --outdir) OUTDIR="$2"; shift 2 ;;
    --mode) MODE="$2"; shift 2 ;;
    --proposer) PROPOSER="$2"; shift 2 ;;
    --cex-tier) CEX_TIER="$2"; shift 2 ;;
    --attempts) ATTEMPTS="$2"; shift 2 ;;
    --witness) WITNESS="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"; shift 2 ;;
    --budget) BUDGET="$2"; shift 2 ;;
    --witness-budget) WITNESS_BUDGET="$2"; shift 2 ;;
    --gate-timeout) GATE_TIMEOUT="$2"; shift 2 ;;
    --max-rss-mb) MAX_RSS_MB="$2"; shift 2 ;;
    --model) MODEL="$2"; shift 2 ;;
    --effort) EFFORT="$2"; shift 2 ;;
    -h|--help) usage ;;
    *) echo "unknown option: $1"; usage ;;
  esac
done
[[ -f "$INPUT" ]] || { echo "input not found: $INPUT"; exit 1; }
if [[ -z "$REPO" || ( ! -f "$REPO/lakefile.toml" && ! -f "$REPO/lakefile.lean" ) ]]; then echo "set REPO to the Lean project directory"; exit 1; fi
REPO="$(cd "$REPO" && pwd)"
command -v lake >/dev/null || { echo "lake not on PATH"; exit 1; }
case "$MODE" in race|both|prove|refute) ;; *) usage ;; esac
if [[ "$MODE" != "refute" || "$PROPOSER" == "llm" ]]; then
  command -v "$CODEX_CMD" >/dev/null || { echo "LLM command '$CODEX_CMD' not on PATH (set CODEX_CMD, or use --mode refute --proposer enum)"; exit 1; }
fi

CASE="$(basename "$INPUT" .lean)"
OUT="${OUTDIR:-$PWD/validate_out/$CASE}"
mkdir -p "$OUT/prove" "$OUT/refute"
OUT="$(cd "$OUT" && pwd)"
TASK="$OUT/$CASE.lean"
python3 - "$INPUT" "$TASK" <<'PY'
import sys
t = open(sys.argv[1], encoding='utf-8').read()
out = []; i = 0; d = 0; n = len(t)
while i < n:
    if t.startswith('/-', i): d += 1; i += 2; continue
    if d and t.startswith('-/', i): d -= 1; i += 2; continue
    if d: i += 1; continue
    if t.startswith('--', i):
        j = t.find('\n', i); i = n if j < 0 else j; continue
    out.append(t[i]); i += 1
lines = [l.rstrip() for l in ''.join(out).split('\n')]
res = []; blank = 0
for l in lines:
    if l == '':
        blank += 1
        if blank > 1: continue
    else:
        blank = 0
    res.append(l)
open(sys.argv[2], 'w', encoding='utf-8').write('\n'.join(res).strip('\n') + '\n')
PY
FACTS="$OUT/facts.json"
python3 "$SEARCH" facts "$TASK" > "$FACTS" 2>"$OUT/facts.err" || { echo "cannot parse input: $(cat "$OUT/facts.err")"; exit 1; }
MULTI="$(python3 -c "import json,sys;print(int(json.load(open(sys.argv[1]))['multiblock']))" "$FACTS")"
SYMB="$(python3 -c "import json,sys;print(int(json.load(open(sys.argv[1]))['num_widths']>0))" "$FACTS")"
if [[ "$CEX_TIER" == "auto" ]]; then
  if [[ "$MULTI" == 1 ]]; then SEARCH_TIER=native; REGATE_TIER=kernel; else SEARCH_TIER=strict; REGATE_TIER=""; fi
else
  SEARCH_TIER="$CEX_TIER"; REGATE_TIER=""
fi
START=$(date +%s)
echo "[validate] case=$CASE multiblock=$MULTI symbolic=$SYMB mode=$MODE proposer=$PROPOSER tier=$SEARCH_TIER${REGATE_TIER:+ (re-check $REGATE_TIER)}"

count_tokens() { python3 "$CHECK" count "$1" "$2"; }

run_gate() {  # run_gate FILE LOG -> GATE_RC GATE_OOM GATE_PEAK_MB
  local f="$1" log="$2" base; base="$(basename "$f")"
  local rssf="$log.rss" oomf="$log.oom"
  : > "$rssf"; rm -f "$oomf"
  ( cd "$REPO" && timeout -k 10 "$GATE_TIMEOUT" lake env lean "$f" ) >"$log" 2>&1 &
  local gp=$!
  (
    local peak=0 pids sum
    while kill -0 "$gp" 2>/dev/null; do
      pids="$(pgrep -f "$base" 2>/dev/null | paste -sd, -)"
      if [[ -n "$pids" ]]; then
        sum=$(ps -o rss= -p "$pids" 2>/dev/null | awk '{t+=$1} END{print t+0}')
        if [[ "${sum:-0}" -gt "$peak" ]]; then peak="$sum"; echo "$peak" > "$rssf"; fi
        if [[ $(( ${sum:-0} / 1024 )) -gt "$MAX_RSS_MB" ]]; then
          echo "$sum" > "$oomf"; pkill -f "$base" 2>/dev/null; break
        fi
      fi
      sleep 3
    done
  ) &
  local wp=$!
  wait "$gp"; GATE_RC=$?
  kill "$wp" 2>/dev/null; wait "$wp" 2>/dev/null
  GATE_PEAK_MB=$(( $(cat "$rssf" 2>/dev/null || echo 0) / 1024 ))
  if [[ -f "$oomf" ]]; then GATE_RC=137; GATE_OOM=1; else GATE_OOM=0; fi
  rm -f "$rssf" "$oomf"
}

run_llm() {  # run_llm CWD ADDDIR BUDGET LOG PROMPT
  local cwd="$1" add="$2" budget="$3" log="$4" prompt="$5"
  local compact=()
  [[ -n "$AUTO_COMPACT" && "$AUTO_COMPACT" != 0 ]] && compact=(-c "model_auto_compact_token_limit=$AUTO_COMPACT")
  ( cd "$cwd" && timeout "$budget" "$CODEX_CMD" exec -m "$MODEL" --sandbox workspace-write --skip-git-repo-check \
      -c model_reasoning_effort="$EFFORT" "${compact[@]}" --add-dir "$add" "$prompt" ) </dev/null >"$log" 2>&1
}

PROVE_HDR='You are an expert Lean 4 theorem prover working fully autonomously.

Edit THIS file in place until it compiles cleanly:
  %s

It is a complete proof scaffold EXCEPT for one or more helper lemmas whose
bodies are `sorry`.
Replace ONLY those `sorry` bodies with correct proofs; iterate until Lean
accepts the file.
You have the lean-lsp MCP (lean_goal, lean_diagnostic_messages, lean_multi_attempt,
lean_hover_info, lean_local_search, lean_hammer_premise); you may add helper lemmas
above the holed lemmas and raise set_option maxHeartbeats/maxRecDepth.
%s
HARD RULES (integrity):
- DERIVE the proofs from the goal states. Do NOT search the filesystem for any
  existing or previous proof/answer, for a dataset manifest, README, provenance,
  or any directory whose name reveals the verdict. Read only THIS file and the
  framework source (SSA/LeanMLIR) you need.
- Change ONLY the holed lemma bodies; do NOT touch other declarations, *_correct,
  the *_src/_tgt defs, the width binders, or the imports.
- Finish with NO sorry/admit, no native_decide, only standard axioms.'
SYM_NOTE='
The programs are parameterised by a bit width `w : Nat` and the goal is
universally quantified over it. The proof must hold for EVERY `w`: do not
specialise `w`, and do not add any hypothesis about it.
'

prove_arm() {
  local t0; t0=$(date +%s)
  prove_body
  echo $(( $(date +%s) - t0 )) > "$OUT/prove/seconds"; touch "$OUT/prove/done"
}

prove_body() {
  local P="$OUT/prove" line rc shape mainfile expected companions
  line=$(python3 "$EMITTER" "$TASK" --outdir "$P" --case "$CASE" 2>"$P/emit.err"); rc=$?
  printf '%s\n' "$line" > "$P/manifest"
  if [[ $rc -ne 0 || "$line" == *DECLINED* || -z "$line" ]]; then
    echo "declined" > "$P/status"; echo "$(cut -f3- <<<"$line")" > "$P/detail"; return
  fi
  IFS=$'\t' read -r _ shape mainfile expected companions <<< "$line"
  echo "$shape" > "$P/shape"
  cp "$mainfile" "$P/$CASE.emitted.lean"
  local stmt; stmt="$(python3 "$CHECK" statement "$mainfile" "${CASE}_correct")"
  run_gate "$mainfile" "$P/gate.log"
  if [[ $GATE_RC -ne 0 ]]; then
    echo "failed_gate" > "$P/status"; echo "scaffold did not compile (rc=$GATE_RC)" > "$P/detail"; return
  fi
  local nmain; nmain=$(count_tokens "$mainfile" '\bsorry\b')
  if [[ "$nmain" -ne "$expected" ]]; then
    echo "failed_gate" > "$P/status"; echo "sorry count $nmain != expected $expected" > "$P/detail"; return
  fi
  if [[ -f "$P/${CASE}_audit.json" ]]; then
    echo "vacuous" > "$P/status"; echo "signature-only certificate; not a semantic proof" > "$P/detail"; return
  fi
  if [[ "$expected" -eq 0 ]]; then
    local thm; thm="$(python3 "$CHECK" qualified "$mainfile" "${CASE}_correct")"
    if python3 "$CHECK" trust "$P/$CASE.emitted.lean" "$mainfile" --thm "$thm" --tier strict --repo "$REPO" > "$P/trust.log" 2>&1; then
      cp "$mainfile" "$OUT/${CASE}_proof.lean"; echo "proved" > "$P/status"; echo "closed by the emitter" > "$P/detail"; touch "$P/accept"
    else
      echo "axiom-policy-failed" > "$P/status"; tail -n 3 "$P/trust.log" | tr '\n' ' ' > "$P/detail"
    fi
    return
  fi
  local note=""; [[ "$SYMB" == 1 ]] && note="$SYM_NOTE"
  local prompt; prompt=$(printf "$PROVE_HDR" "$mainfile" "$note")
  run_llm "$REPO" "$P" "$BUDGET" "$P/prover.log" "$prompt"
  local bad; bad=$(count_tokens "$mainfile" '\b(sorry|admit)\b')
  if [[ "$bad" -ne 0 ]]; then
    echo "unresolved" > "$P/status"; echo "$bad open sorry/admit after the LLM budget" > "$P/detail"; return
  fi
  if [[ -n "$stmt" ]] && ! grep -qxF "$stmt" "$mainfile"; then
    echo "statement-changed" > "$P/status"; echo "the theorem statement line was edited" > "$P/detail"; return
  fi
  run_gate "$mainfile" "$P/kernel.log"
  if [[ $GATE_RC -ne 0 ]]; then
    echo "unresolved" > "$P/status"; echo "final file does not compile (rc=$GATE_RC)" > "$P/detail"; return
  fi
  local thm; thm="$(python3 "$CHECK" qualified "$mainfile" "${CASE}_correct")"
  if python3 "$CHECK" trust "$P/$CASE.emitted.lean" "$mainfile" --thm "$thm" --tier strict --allow-compiled --skip-nonhole --repo "$REPO" > "$P/trust.log" 2>&1; then
    cp "$mainfile" "$OUT/${CASE}_proof.lean"; echo "proved" > "$P/status"
    grep '^axioms:' "$P/trust.log" > "$P/detail" || echo "kernel-accepted" > "$P/detail"
    touch "$P/accept"
  else
    echo "axiom-policy-failed" > "$P/status"; tail -n 3 "$P/trust.log" | tr '\n' ' ' > "$P/detail"
  fi
}

gate_cert() {  # gate_cert WITNESS TIER ROUNDDIR -> sets CERT OUTCOME DETAIL
  local wit="$1" tier="$2" rd="$3" line
  mkdir -p "$rd"
  line=$(python3 "$EMITTER" "$TASK" --outdir "$rd" --case "$CASE" --cex-witness "$wit" --cex-tier "$tier" 2>"$rd/emit.err")
  printf '%s\n' "$line" > "$rd/manifest"
  if [[ "$line" == *DECLINED* || -z "$line" ]]; then
    CERT=""; OUTCOME="emit-declined"; DETAIL="$(cut -f3- <<<"$line")"; return
  fi
  CERT="$(cut -f3 <<<"$line")"
  local exp; exp="$(cut -f4 <<<"$line")"
  if [[ "$exp" != "0" ]]; then OUTCOME="emit-holed"; DETAIL="certificate has $exp open holes"; return; fi
  cp "$CERT" "$rd/emitted.snapshot.lean"
  run_gate "$CERT" "$rd/gate.log"
  echo "$GATE_PEAK_MB" > "$rd/peak_rss_mb"
  if [[ $GATE_RC -ne 0 ]]; then
    IFS=$'\t' read -r OUTCOME DETAIL < <(python3 "$SEARCH" classify "$CERT" "$rd/gate.log" "$GATE_RC" $([[ $GATE_OOM == 1 ]] && echo --oom))
    return
  fi
  local ttier=strict; [[ "$tier" == native ]] && ttier=native
  if python3 "$CHECK" trust "$rd/emitted.snapshot.lean" "$CERT" --thm "${CASE}_correct_counterexample" --tier "$ttier" --repo "$REPO" > "$rd/trust.log" 2>&1; then
    OUTCOME="cex-certified"; DETAIL="$(grep '^axioms:' "$rd/trust.log" | head -1)"
  else
    OUTCOME="trust-failed"; DETAIL="$(tail -n 2 "$rd/trust.log" | tr '\n' ' ')"
  fi
}

refute_arm() {
  local R="$OUT/refute" hist="$OUT/refute/history.json" r=0 keys="$OUT/refute/keys.txt"
  local t0; t0=$(date +%s)
  echo "[]" > "$hist"; : > "$keys"; : > "$R/attempts.tsv"
  printf 'round\tproposer\twitness\toutcome\tdetail\n' > "$R/attempts.tsv"
  local mode=enum; [[ "$PROPOSER" == llm ]] && mode=llm
  while [[ $r -lt $ATTEMPTS ]]; do
    r=$((r+1))
    local rd="$R/r$r" wit="$R/r$r/witness.json" outcome detail brief
    mkdir -p "$rd"
    local rmode="$mode"
    if [[ $r -eq 1 && -n "$WITNESS" ]]; then
      rmode=given
      python3 - "$WITNESS" "$wit" <<'PY'
import json, sys
w = json.load(open(sys.argv[1])); w.pop('input_sha256', None)
json.dump(w, open(sys.argv[2], 'w'), indent=1)
PY
    else
      python3 "$SEARCH" next "$TASK" --history "$hist" --mode "$mode" --out "$wit" --prompt-out "$rd/prompt.txt" \
          --case "$CASE" --value-rounds "$ATTEMPTS" > "$rd/next.out" 2>&1
      local nrc=$?
      if [[ $nrc -eq 3 ]]; then echo "search space exhausted" > "$R/detail"; break; fi
      if [[ $nrc -ne 0 ]]; then echo "proposer error: $(cat "$rd/next.out")" > "$R/detail"; break; fi
    fi
    if [[ "$rmode" == llm ]]; then
      run_llm "$rd" "$rd" "$WITNESS_BUDGET" "$rd/proposer.log" "$(cat "$rd/prompt.txt")"
      [[ -s "$wit" ]] || python3 "$SEARCH" extract "$rd/proposer.log" "$wit" 2>/dev/null
    fi
    if [[ ! -s "$wit" ]]; then
      outcome="propose-failed"; detail="no witness written"; brief="-"
    elif ! detail="$(python3 "$SEARCH" check "$wit" "$TASK" 2>&1)"; then
      outcome="schema-invalid"; brief="$(python3 "$SEARCH" brief "$wit" 2>/dev/null || echo '-')"
    else
      brief="$(python3 "$SEARCH" brief "$wit")"
      local key; key="$(python3 "$SEARCH" key "$wit")"
      if grep -Fqx -- "$key" "$keys"; then
        outcome="duplicate"; detail="already tried"
      else
        echo "$key" >> "$keys"
        gate_cert "$wit" "$SEARCH_TIER" "$rd/$SEARCH_TIER"
        outcome="$OUTCOME"; detail="$DETAIL"
        local accepted_cert="$CERT" accepted_tier="$SEARCH_TIER"
        if [[ "$outcome" == "cex-certified" && -n "$REGATE_TIER" ]]; then
          gate_cert "$wit" "$REGATE_TIER" "$rd/$REGATE_TIER"
          if [[ "$OUTCOME" == "cex-certified" ]]; then
            accepted_cert="$CERT"; accepted_tier="$REGATE_TIER"; detail="$DETAIL"
          else
            detail="$SEARCH_TIER-tier certificate; $REGATE_TIER re-check: $OUTCOME"
          fi
        fi
        if [[ "$outcome" == "cex-certified" ]]; then
          cp "$accepted_cert" "$OUT/${CASE}_counterexample.lean"; cp "$wit" "$OUT/${CASE}_counterexample.json"
          echo "$accepted_tier" > "$R/tier"
        fi
      fi
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$r" "$rmode" "$brief" "$outcome" "$detail" >> "$R/attempts.tsv"
    echo "  [refute] round $r: $brief -> $outcome${detail:+ ($detail)}"
    python3 - "$hist" "$wit" "$outcome" <<'PY'
import json, sys, os
h = json.load(open(sys.argv[1]))
w = json.load(open(sys.argv[2])) if os.path.exists(sys.argv[2]) and os.path.getsize(sys.argv[2]) else None
h.append({'witness': w, 'outcome': sys.argv[3]})
json.dump(h, open(sys.argv[1], 'w'))
PY
    if [[ "$outcome" == "cex-certified" ]]; then
      echo "refuted" > "$R/status"; echo "$detail" > "$R/detail"; touch "$R/accept"; break
    fi
    if [[ "$outcome" == "emit-declined" && "$SYMB" == 0 ]]; then
      echo "declined" > "$R/status"; echo "$detail" > "$R/detail"; break
    fi
  done
  [[ -f "$R/status" ]] || { echo "unresolved" > "$R/status"; [[ -f "$R/detail" ]] || echo "no certified counterexample in $r round(s)" > "$R/detail"; }
  echo $(( $(date +%s) - t0 )) > "$R/seconds"; touch "$R/done"
}

kill_arm() {  # kill_arm PGID DIR
  local pgid="$1" dir="$2"
  [[ -n "$pgid" ]] && kill -TERM -- "-$pgid" 2>/dev/null
  pkill -TERM -f -- "$dir" 2>/dev/null
  ( sleep 2; [[ -n "$pgid" ]] && kill -KILL -- "-$pgid" 2>/dev/null; pkill -KILL -f -- "$dir" 2>/dev/null ) >/dev/null 2>&1 &
}

VERDICT=""
case "$MODE" in
  prove)  prove_arm ;;
  refute) refute_arm ;;
  *)
    set -m
    ( prove_arm ) & PP=$!
    ( refute_arm ) & PC=$!
    set +m
    while :; do
      pa=0; ca=0
      [[ -f "$OUT/prove/accept" ]] && pa=1
      [[ -f "$OUT/refute/accept" ]] && ca=1
      if [[ "$MODE" == race ]]; then
        if [[ $pa -eq 1 && $ca -eq 1 ]]; then kill_arm "$PP" "$OUT/prove"; kill_arm "$PC" "$OUT/refute"; break; fi
        if [[ $pa -eq 1 ]]; then [[ -f "$OUT/refute/done" ]] || kill_arm "$PC" "$OUT/refute"; break; fi
        if [[ $ca -eq 1 ]]; then [[ -f "$OUT/prove/done" ]] || kill_arm "$PP" "$OUT/prove"; break; fi
      fi
      [[ -f "$OUT/prove/done" && -f "$OUT/refute/done" ]] && break
      sleep 1
    done
    sleep 3
    wait 2>/dev/null
    ;;
esac

PS="$(cat "$OUT/prove/status" 2>/dev/null || echo not-run)"
RS="$(cat "$OUT/refute/status" 2>/dev/null || echo not-run)"
[[ "$MODE" == race && ! -f "$OUT/prove/done" && "$PS" == not-run ]] && PS=stopped
[[ "$MODE" == race && ! -f "$OUT/refute/done" && "$RS" == not-run ]] && RS=stopped
if [[ "$PS" == proved && "$RS" == refuted ]]; then VERDICT=contradiction
elif [[ "$PS" == proved ]]; then VERDICT=proved
elif [[ "$RS" == refuted ]]; then VERDICT=refuted
else VERDICT=unresolved; fi
TIER="$(cat "$OUT/refute/tier" 2>/dev/null || echo -)"
ELAPSED=$(( $(date +%s) - START ))
python3 - "$OUT/result.json" "$CASE" "$VERDICT" "$PS" "$RS" "$TIER" "$ELAPSED" "$OUT" <<'PY'
import json, sys, os
o, case, verdict, ps, rs, tier, secs, out = sys.argv[1:]
def rd(p):
    try: return open(p).read().strip()
    except OSError: return ''
json.dump({'case': case, 'verdict': verdict,
           'prove': {'status': ps, 'detail': rd(os.path.join(out, 'prove', 'detail')), 'shape': rd(os.path.join(out, 'prove', 'shape'))},
           'refute': {'status': rs, 'detail': rd(os.path.join(out, 'refute', 'detail')), 'tier': tier},
           'seconds': int(secs)}, open(o, 'w'), indent=1)
PY
printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$CASE" "$VERDICT" "$PS" "$RS" "$TIER" "$ELAPSED" > "$OUT/result.tsv"
echo "[validate] $CASE -> $VERDICT (prove=$PS refute=$RS tier=$TIER ${ELAPSED}s)"
echo "[validate] outputs: $OUT"
case "$VERDICT" in proved|refuted) exit 0 ;; contradiction) exit 4 ;; *) exit 1 ;; esac
