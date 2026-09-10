#!/usr/bin/env python3
import argparse
import hashlib
import itertools
import json
import os
import re
import sys

MAX_FUEL = 1024
MAX_WIDTH = 64
POISON = 'P'

DEF_FW = re.compile(r'def\s+([A-Za-z_]\w*)\s*:=\s*\[llvm\(\)\|\s*\{(.*?)\}\s*\]', re.S)
DEF_SY = re.compile(r'def\s+([A-Za-z_]\w*)\s*((?:\([^)]*\)\s*)+):=\s*\[llvm\(([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)\)\|\s*\{(.*?)\}\s*\]', re.S)
HEADER = re.compile(r'llvm\.func\s+@(\S+)\(([^)]*)\)\s*->\s*(\S+)\s*\{')
ARG = re.compile(r'%(\w+)\s*:\s*([^,\s]+)')
BLOCK = re.compile(r'\^\w+\([^)]*\):')
CONST = re.compile(r'llvm\.mlir\.constant\s*\(?\s*(-?\d+)')


def strip_lean_comments(t):
    out = []
    i = 0
    d = 0
    n = len(t)
    while i < n:
        if t.startswith('/-', i):
            d += 1
            i += 2
            continue
        if d and t.startswith('-/', i):
            d -= 1
            i += 2
            continue
        if d:
            i += 1
            continue
        if t.startswith('--', i):
            j = t.find('\n', i)
            i = n if j < 0 else j
            continue
        out.append(t[i])
        i += 1
    return ''.join(out)


def parse(text):
    t = strip_lean_comments(text)
    defs = []
    for m in DEF_SY.finditer(t):
        syms = [s.strip() for s in m.group(3).split(',')]
        defs.append((m.start(), m.group(1), syms, m.group(4)))
    for m in DEF_FW.finditer(t):
        defs.append((m.start(), m.group(1), [], m.group(2)))
    defs.sort()
    if len(defs) < 2:
        raise ValueError('expected two [llvm(..)| definitions (src then tgt)')
    (_, sname, ssyms, sbody), (_, tname, tsyms, tbody) = defs[0], defs[1]
    h = HEADER.search(sbody)
    if not h:
        raise ValueError('no llvm.func header in the source definition')
    args = ARG.findall(h.group(2))
    return {
        'src_name': sname, 'tgt_name': tname,
        'width_symbols': ssyms, 'src_body': sbody, 'tgt_body': tbody,
        'args': args, 'ret_type': h.group(3),
    }


def width_of_type(ty, syms):
    ty = ty.strip()
    if ty == '_' and syms:
        return syms[0]
    if ty.startswith('i') and ty[1:].isdigit():
        return int(ty[1:])
    return ty


def min_faithful_width(bodies):
    w = 1
    for b in bodies:
        for c in CONST.findall(b):
            c = int(c)
            if c >= 0:
                w = max(w, max(1, c.bit_length()))
            else:
                w = max(w, (-c - 1).bit_length() + 1)
    return w


def facts(text):
    p = parse(text)
    syms = p['width_symbols']
    names = ['%' + a for a, _ in p['args']]
    types = [t for _, t in p['args']]
    widths = [width_of_type(t, syms) for t in types]
    src_blocks = len(BLOCK.findall(p['src_body']))
    tgt_blocks = len(BLOCK.findall(p['tgt_body']))
    entry_end = p['src_body'].find('):')
    after_entry = p['src_body'][entry_end + 2:] if entry_end >= 0 else p['src_body']
    used = [n for n in names if re.search(re.escape(n) + r'\b', after_entry)]
    consts = sorted({int(c) for b in (p['src_body'], p['tgt_body']) for c in CONST.findall(b)})
    return {
        'dialect': 'symbolic' if syms else 'fixed',
        'width_symbols': syms,
        'num_widths': len(syms),
        'surface_arg_names': names,
        'surface_arg_types': types,
        'surface_arg_widths': [str(w) for w in widths],
        'num_args': len(names),
        'return_type': p['ret_type'],
        'src_blocks': src_blocks,
        'tgt_blocks': tgt_blocks,
        'multiblock': (src_blocks > 1 or tgt_blocks > 1),
        'used_arg_names': used,
        'constants': consts,
        'width_min_faithful': min_faithful_width((p['src_body'], p['tgt_body'])),
    }


def facts_lines(f):
    keys = ['dialect', 'num_args', 'surface_arg_names', 'surface_arg_types', 'surface_arg_widths',
            'return_type', 'src_blocks', 'tgt_blocks', 'width_symbols', 'num_widths',
            'used_arg_names', 'constants', 'width_min_faithful']
    out = []
    for k in keys:
        v = f[k]
        if isinstance(v, list):
            v = ','.join(str(x) for x in v)
        out.append('%s=%s' % (k, v))
    return '\n'.join(out)


def sha256_file(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def corners(w):
    lim = 1 << w
    seq = [0, 1, POISON, lim - 1, 1 << (w - 1), (1 << (w - 1)) - 1, 2, 3]
    out = []
    for v in seq:
        if v == POISON or (0 <= v < lim):
            if v not in out:
                out.append(v)
    return out


def arg_width(f, i, width):
    w = f['surface_arg_widths'][i]
    if w.isdigit():
        return int(w)
    return width if width else 4


def value_tuple(f, width, vidx):
    n = f['num_args']
    if n == 0:
        return []
    per = [corners(arg_width(f, i, width)) for i in range(n)]
    if not f['used_arg_names']:
        return [0] * n
    k = min(len(c) for c in per)
    order = sorted(itertools.product(range(k), repeat=n), key=lambda t: (max(t), sum(t), t))
    tup = order[vidx % len(order)]
    return [per[i][tup[i]] for i in range(n)]


def value_space(f, width):
    n = f['num_args']
    if n == 0 or not f['used_arg_names']:
        return 1
    k = min(len(corners(arg_width(f, i, width))) for i in range(n))
    return k ** n


def width_ladder(f, allow_truncating):
    if f['num_widths'] == 0:
        return [None]
    wmf = f['width_min_faithful']
    cand = [wmf, wmf + 1, max(wmf, 8), max(wmf, 16), 32, 64]
    if allow_truncating:
        cand = [4, 2, 1] + cand
    out = []
    for w in cand:
        if 1 <= w <= MAX_WIDTH and w not in out:
            out.append(w)
    return sorted(out) if allow_truncating else out


def make_witness(f, case, isha, values, width, fuel):
    args = []
    for i, v in enumerate(values):
        name = f['surface_arg_names'][i]
        if v == POISON:
            args.append({'name': name, 'kind': 'poison'})
        else:
            args.append({'name': name, 'kind': 'value', 'nat': int(v)})
    w = {'schema': 1, 'case': case, 'input_sha256': isha, 'args': args}
    if f['num_widths'] == 1:
        w['width'] = width
    elif f['num_widths'] > 1:
        w['widths'] = [width + i for i in range(f['num_widths'])]
    if f['multiblock']:
        w['state'] = 'default'
        w['fuel'] = fuel
    return w


def dedup_key(w):
    k = {'args': [{'kind': a.get('kind', 'value'), 'nat': a.get('nat')} for a in w.get('args', [])]}
    for key in ('width', 'widths', 'fuel', 'state'):
        if key in w:
            k[key] = w[key]
    return json.dumps(k, sort_keys=True, separators=(',', ':'))


def check_witness(w, f, width_required):
    if w.get('schema') != 1:
        return 'schema != 1'
    args = w.get('args')
    if not isinstance(args, list) or len(args) != f['num_args']:
        return 'args must be a list of exactly %d entries' % f['num_args']
    width = None
    if f['num_widths'] == 1:
        width = w.get('width')
        if width is None and width_required:
            return '"width" is required for the symbolic dialect'
        if width is not None and (isinstance(width, bool) or not isinstance(width, int) or not 1 <= width <= MAX_WIDTH):
            return '"width" must be an integer in [1, %d]' % MAX_WIDTH
    elif f['num_widths'] > 1:
        ws = w.get('widths')
        if not isinstance(ws, (list, dict)) or len(ws) != f['num_widths']:
            return '"widths" must list one width per symbol (%d)' % f['num_widths']
    else:
        if 'width' in w or 'widths' in w:
            return 'fixed-width dialect: omit "width"'
    for i, a in enumerate(args):
        if not isinstance(a, dict):
            return 'args[%d] is not an object' % i
        kind = a.get('kind', 'value')
        if kind not in ('value', 'poison'):
            return 'args[%d].kind must be value or poison' % i
        if kind == 'value':
            v = a.get('nat')
            if isinstance(v, bool) or not isinstance(v, int) or v < 0:
                return 'args[%d].nat must be a non-negative integer' % i
            aw = f['surface_arg_widths'][i]
            lim = None
            if aw.isdigit():
                lim = 1 << int(aw)
            elif f['num_widths'] == 1 and width:
                lim = 1 << width
            if lim is not None and v >= lim:
                return 'args[%d].nat = %d exceeds the width' % (i, v)
    if f['multiblock']:
        st = w.get('state')
        if st != 'default' and st != {'kind': 'default'}:
            return '"state" must be "default"'
        fuel = w.get('fuel')
        if isinstance(fuel, bool) or not isinstance(fuel, int) or not 1 <= fuel <= MAX_FUEL:
            return '"fuel" must be an integer in [1, %d]' % MAX_FUEL
    return ''


ANGLES_LINE = [
    'the corner values first: 0, 1, all-ones (the w-bit -1), and the sign boundary INT_MIN = 2^(w-1). Most real miscompilations break exactly there.',
    'make an operation TRAP or POISON: a zero divisor for udiv/sdiv/urem/srem, a shift amount >= the bit width, an exact/disjoint flag whose side condition is violated, INT_MIN / -1 for a signed division.',
    'attack the NO-WRAP flags: pick inputs where an nsw/nuw add/sub/mul/shl overflows in ONE of the two programs but not the other, so one side is poison and the other is a value.',
    'attack the CONTROL/COMPARISON structure: pick inputs that send an icmp or a select down a different branch in src than in tgt, or that make src well-defined while tgt is immediate UB.',
    'something structurally different from every valuation listed above.',
]

ANGLES_LOOP = [
    'the corner values first: 0, 1, all-ones (the w-bit -1), and the sign boundary INT_MIN = 2^(w-1), and a fuel comfortably above the loop\'s block-jump count. Most real miscompilations break exactly at those inputs.',
    'the TRIP COUNT and the exit test: pick inputs that make the loop exit after a different number of iterations in src than in tgt, or that make an induction variable wrap. Remember the exit value the two programs return must then differ.',
    'the NO-WRAP / disjointness flags carried in or out of the loop: pick inputs where an nsw/nuw add/sub/mul/shl overflows, or where an `or disjoint` has overlapping bits, so one side is poison and the other is a value.',
    'UB and poison on the TARGET side: a zero divisor, a shift amount >= the bit width, INT_MIN / -1 for a signed division, or a poison operand that the target propagates to the result while the source does not.',
    'something structurally different from every triple listed above.',
]

ANGLES_LOOP_SYM = [
    'THE WIDTH FIRST: pick the smallest width at which every integer literal in the two programs is representable without truncation, and inputs at the corners (0, 1, all-ones, INT_MIN = 2^(w-1)). A width below that changes the constants and therefore the program.',
    'the TRIP COUNT and the exit test: pick a width and inputs that make the loop exit after a different number of iterations in src than in tgt, or that make an induction variable wrap. Remember the exit value the two programs return must then differ. A trip-count literal truncates at small widths, so the width is part of this choice.',
    'the NO-WRAP / disjointness flags carried in or out of the loop: pick a width and inputs where an nsw/nuw add/sub/mul/shl overflows, or where an `or disjoint` has overlapping bits, so one side is poison and the other is a value. Overflow is EASIER at small widths.',
    'UB and poison on the TARGET side: a zero divisor, INT_MIN / -1 for a signed division, or a poison operand that the target propagates to the result while the source does not.',
    'a LARGE width (32 or 64) with a constant that only becomes distinguishable there: two literals that alias modulo 2^w at small widths but differ at the full width.',
]


def prompt_text(f, prog, case, isha, wit_path, rnd, fuel, width, refuted, ladder):
    fl = facts_lines(f)
    if not f['multiblock']:
        angle = ANGLES_LINE[(rnd - 1) % len(ANGLES_LINE)]
        prev = ''
        if refuted:
            prev = ('ALREADY TRIED AND KERNEL-REFUTED - at each of these valuations the\n'
                    'refinement HOLDS, so none of them is a counterexample.  Do NOT propose any of\n'
                    'them again, and do not propose a trivial re-spelling of one:\n' + refuted + '\n')
        return f'''You are refuting an LLVM peephole rewrite.  Below are two programs in the
LeanMLIR llvm dialect, a source and a target.  Someone claims src is refined by
tgt (src ⊑ tgt).  Your job is to find ONE concrete input valuation at which that
claim is FALSE, and to write that valuation as JSON.  You write no Lean, no
proof, no tactic - just the numbers.

The claim src ⊑ tgt fails at an input when ANY of these happens there:
  (a) both are defined but produce DIFFERENT values;
  (b) src produces a value and tgt produces poison;
  (c) src is well-defined and tgt triggers immediate UB (a zero divisor, for
      instance) - UB in the target is not allowed to appear out of nowhere;
  (d) tgt keeps a poison-generating flag (nsw/nuw/exact/disjoint) whose side
      condition src never needed.
Poison flows: a poison operand poisons the result; select/icmp propagate it.

THE TWO PROGRAMS
------------------------------------------------------------
{prog}
------------------------------------------------------------

CASE FACTS (fill exactly this arity and schema)
{fl}

SEARCH ANGLE FOR THIS ROUND - try {angle}

{prev}
BEFORE YOU WRITE ANYTHING: evaluate BOTH programs by hand at the valuation you
picked, instruction by instruction, and convince yourself the claim really
breaks there.  If it does not, pick another valuation and evaluate again.  Put
that hand-evaluation in the self_check field - it is recorded and read by a
human, so make it concrete (actual intermediate values, not a restatement).

WRITE PURE JSON - no prose, no markdown fence - to EXACTLY this path:
  {wit_path}

{{
  "schema": 1,
  "case": "{case}",
  "input_sha256": "{isha}",
  "width":  <concrete Nat - ONLY when num_widths=1; omit for the fixed dialect>,
  "widths": <use INSTEAD of "width" when num_widths>1: one concrete Nat per
             symbol in width_symbols, IN THAT ORDER, e.g. [2, 3]>,
  "args": [ one entry per surface arg, LEFT TO RIGHT, matching
            surface_arg_names exactly:
      {{"name": "%argname", "kind": "value", "nat": <0 .. 2^(that arg's width)-1>}}
      or {{"name": "%argname", "kind": "poison"}} ],
  "self_check": {{
    "src_eval": "<what src computes at this valuation, step by step>",
    "tgt_eval": "<what tgt computes at this valuation, step by step>",
    "why_it_fails": "<which of (a)-(d) above applies, in one line>"
  }}
}}

RULES
- Widths: prefer the SMALLEST width where the claim breaks - 1 to 4 is ideal.
  The certificate is checked by kernel evaluation, and small widths check fast.
  With several width symbols, respect any side condition the definitions are
  guarded by (a binder like (_h : w1 < w2) forces w1 < w2; a violating tuple
  cannot be instantiated at all).
- args are in SURFACE order, left to right, exactly as listed in the facts.
- Values are UNSIGNED naturals in [0, 2^w).  Write -1 as 2^w - 1, and INT_MIN as
  2^(w-1).
- Do not read anything else on the filesystem: everything you need is above.
  Derive the answer from the two programs.
- Your self_check is NOT trusted and is NOT part of the certificate.  A kernel
  evaluates both programs at your valuation and decides for itself, so a
  confident but wrong valuation is simply rejected - reason carefully instead.
- Write ONLY the JSON file at the path above.
'''
    sym = f['num_widths'] >= 1
    angles = ANGLES_LOOP_SYM if sym else ANGLES_LOOP
    angle = angles[(rnd - 1) % len(angles)]
    prev = ''
    if refuted:
        if sym:
            prev = ('ALREADY TRIED - the kernel did NOT accept any of these quadruples.  The\n'
                    'tag after each one says why: refinement-holds means the kernel evaluated both\n'
                    'programs there and the claim really holds AT THAT WIDTH AND VALUATION, so that\n'
                    'quadruple is dead - but a DIFFERENT WIDTH may still work; fuel-starved means a\n'
                    'side had not TERMINATED at that fuel, so the width/values may be fine and only\n'
                    'the fuel was too small - raise it.  Do not repeat a quadruple, and do not\n'
                    're-spell one:\n' + refuted + '\n')
        else:
            prev = ('ALREADY TRIED - the kernel did NOT accept any of these triples.  The tag\n'
                    'after each one says why: refinement-holds means the kernel evaluated both\n'
                    'programs there and the claim really holds, so that valuation is dead;\n'
                    'fuel-starved means a side had not TERMINATED at that fuel, so the valuation may\n'
                    'still be fine but the fuel was too small - raise it.  Do not repeat a triple,\n'
                    'and do not re-spell one:\n' + refuted + '\n')
    width_block = ''
    width_key = ''
    width_rule = ''
    quant = 'THREE'
    name = 'triple'
    if sym:
        quant = 'FOUR'
        name = 'quadruple'
        wmf = f['width_min_faithful']
        width_block = f'''
THE WIDTH IS THE FIRST THING TO CHOOSE, and it is not a formality:
  * every `llvm.mlir.constant N : _` is N TRUNCATED TO w BITS.  A trip-count
    literal that truncates changes how many times the loop runs, and two
    literals that differ at 32 bits can be equal at 2 bits.
  * so a width that is too small can make a broken transformation look correct
    (the two sides coincide after truncation) - and it can also make a correct
    one look broken, which is not what you want either.
  * the smallest width at which NO literal in these two programs truncates is
    {wmf}.  Widths >= {wmf} are "faithful": the program really is the one written
    above.  Prefer a faithful width.  Going smaller is allowed but only if you
    can say why the difference you are exploiting is real there.
  * overflow of nsw/nuw arithmetic is EASIER at small widths, so if the bug is
    an overflow flag, a small (but still faithful) width is the cheap attack.
  * this run's width ladder for this case is: {ladder}
    and the harness suggests {width} for this round.  Override it if your own
    reading of the constants says otherwise.
'''
        width_key = f'  "width": <positive integer, at most {MAX_WIDTH} - the bit width you refute at>,\n'
        width_rule = f'- "width" is REQUIRED and must be an integer in [1, {MAX_WIDTH}].\n'
    head = ('You are refuting an LLVM loop transformation stated at an ARBITRARY BIT WIDTH.\n'
            'Below are two programs in the LeanMLIR llvm dialect, a source and a target, each\n'
            'a multi-basic-block CFG (the block arguments ARE the phi nodes).  Both are\n'
            'parameterised by a width variable: `def X_src (w : Nat) := [llvm(w)| ... ]`,\n'
            'and every data-typed operand, block argument, function argument, return type and\n'
            'constant is written `_`, meaning "at width w".  Someone claims\n\n'
            '    for EVERY width w,  X_src w  is refined by  X_tgt w.\n') if sym else (
            'You are refuting an LLVM loop transformation.  Below are two programs in the\n'
            'LeanMLIR llvm dialect, a source and a target, each a multi-basic-block CFG (the\n'
            'block arguments ARE the phi nodes).  Someone claims src is refined by tgt\n'
            '(src ⊑ tgt).')
    return f'''{head}
Your job is to find ONE concrete WITNESS {name.upper()} at which that claim is FALSE,
and to write it as JSON.  You write no Lean, no proof, no tactic - just numbers.

The claim quantifies over {quant} things, so your witness names all of them:
{'  * the BIT WIDTH w,' + chr(10) if sym else ''}  * the input valuation V (one entry per surface argument),
  * the initial memory state s,
  * the FUEL, which is a budget of BLOCK JUMPS for the interpreter.
{width_block}
FUEL IS PART OF THE PROBLEM, not a formality:
  * a side that has not terminated within the fuel denotes "no result", and the
    certificate contains two guards that make it FAIL unless BOTH sides have
    terminated at your fuel.  So the fuel must be at least the number of block
    jumps the LONGER side performs (count them: each `llvm.br` / taken
    `llvm.cond_br` edge is one jump, and the loop repeats).
  * do not pad it to a huge number either: the kernel really executes the loop,
    so an unnecessarily large fuel makes the check slow.  Pick the smallest
    fuel at which both sides finish, plus a small margin.

The claim fails at a {name} when ANY of these happens there:
  (a) both programs terminate and return DIFFERENT values;
  (b) src returns a value and tgt returns poison;
  (c) src is well-defined and tgt triggers immediate UB (a zero divisor, for
      instance) - UB in the target may not appear out of nowhere;
  (d) tgt keeps a poison-generating flag (nsw/nuw/exact/disjoint) whose side
      condition src never needed.
Poison flows: a poison operand poisons the result; icmp/select propagate it.

THE TWO PROGRAMS
------------------------------------------------------------
{prog}
------------------------------------------------------------

CASE FACTS (fill exactly this arity and schema)
{fl}

SEARCH ANGLE FOR THIS ROUND - try {angle}
A fuel of {fuel} is the harness's own suggestion for this round; override it if
your own jump count says otherwise.

{prev}
BEFORE YOU WRITE ANYTHING: execute BOTH programs by hand at your {name}, block
by block, counting the block jumps as you go, and convince yourself (i) both
finish within your fuel and (ii) the claim really breaks there.  If not, pick
another {name} and redo it.  Put that hand-execution in self_check - it is
recorded and read by a human, so make it concrete (actual intermediate values
and the jump count, not a restatement).

WRITE PURE JSON - no prose, no markdown fence - to EXACTLY this path:
  {wit_path}

{{
  "schema": 1,
  "case": "{case}",
  "input_sha256": "{isha}",
{width_key}  "args": [ one entry per surface argument, LEFT TO RIGHT, matching
            surface_arg_names exactly:
      {{"name": "%argname", "kind": "value", "nat": <0 .. 2^(that arg's width)-1>}}
      or {{"name": "%argname", "kind": "poison"}} ],
  "state": "default",
  "fuel": <positive integer, at most {MAX_FUEL}>,
  "self_check": {{
    "src_eval": "<src block by block at this valuation, with the jump count>",
    "tgt_eval": "<tgt block by block at this valuation, with the jump count>",
    "why_it_fails": "<which of (a)-(d) applies, in one line>"
  }}
}}

RULES
- args are in SURFACE order, left to right, exactly as the facts list them.
- Values are UNSIGNED naturals in [0, 2^w).  Write -1 as 2^w - 1 and INT_MIN as
  2^(w-1).  A "nat" >= 2^w is REJECTED by the harness.
{width_rule}- "state" must be exactly "default": the certificate can only name the canonical
  initial memory state, so any other value is REJECTED rather than quietly
  ignored.
- Do not read anything else on the filesystem: everything you need is above.
  Derive the answer from the two programs.
- Your self_check is NOT trusted and is NOT part of the certificate.  A kernel
  evaluates both programs at your {name} and decides for itself, so a confident
  but wrong {name} is simply rejected - reason carefully instead.
- Write ONLY the JSON file at the path above.
'''


RESOURCE_MARKS = ('maximum recursion depth', 'deep recursion', '(deterministic) timeout',
                  'maxHeartbeats', 'maxRecDepth', 'out of memory', 'bad_alloc',
                  'Cannot allocate', 'failed to reduce', 'stack overflow')
DECL = re.compile(r'\s*(?:private\s+)?(?:theorem|lemma|def|abbrev|instance|example)\s+(\S+)')


def classify(cert, log, rc, oom):
    text = open(log, encoding='utf-8', errors='ignore').read() if os.path.exists(log) else ''
    if oom:
        return 'gate-oom', 'RSS watchdog killed the gate'
    if rc in (124, 137):
        return 'gate-timeout', 'wall-clock timeout'
    for m in RESOURCE_MARKS:
        if m in text:
            return 'gate-resource', m
    owners = {}
    src = open(cert, encoding='utf-8', errors='ignore').read().split('\n') if os.path.exists(cert) else []
    cur = ''
    for i, line in enumerate(src, 1):
        m = DECL.match(line)
        if m:
            cur = m.group(1)
        owners[i] = cur
    errs = []
    pat = re.compile(r'^(?:' + re.escape(cert) + r'|[^\s:]+):(\d+):\d+: error(?:\([^)]*\))?:(.*)$', re.M)
    for m in pat.finditer(text):
        ln = int(m.group(1))
        start = m.end()
        nxt = pat.search(text, start)
        msg = m.group(2) + text[start:nxt.start() if nxt else len(text)]
        errs.append((ln, owners.get(ln, ''), msg))
    if not errs:
        first = text.strip().split('\n')[0] if text.strip() else 'rc=%d, empty log' % rc
        return 'gate-error', first[:160]

    def decided_false(msg):
        return (('proved that the proposition' in msg or 'evaluated that the proposition' in msg)
                and 'is false' in msg)

    evaluator = 'the compiled evaluator' if 'native_decide' in text else 'the kernel'
    for ln, nm, msg in errs:
        if not decided_false(msg):
            continue
        if nm.endswith('_src_terminates_at_cexFuel'):
            return 'fuel-starved-src', 'src had not terminated at the witnessed fuel (line %d)' % ln
        if nm.endswith('_tgt_terminates_at_cexFuel'):
            return 'fuel-starved-tgt', 'tgt had not terminated at the witnessed fuel (line %d)' % ln
    for ln, nm, msg in errs:
        if nm.endswith('_audit_relation_is_memory'):
            return 'relation-audit-failed', 'the pinned memory relation did not resolve (line %d)' % ln
    for ln, nm, msg in errs:
        if (nm.endswith('_pointwise_cex') or nm.endswith('_refute_of_sepBool')
                or nm.endswith('_correct_counterexample_witness')) and decided_false(msg):
            return 'refinement-holds', '%s evaluated both programs and decided src is refined by tgt here (line %d)' % (evaluator, ln)
    detail = errs[0][2].split('\n')[0].strip()
    return 'gate-error', ('%s @ %s' % (detail, errs[0][1]))[:160]


def brief(w):
    vals = ';'.join('poison' if a.get('kind') == 'poison' else str(a.get('nat')) for a in w.get('args', []))
    parts = []
    if 'width' in w:
        parts.append('w=%s' % w['width'])
    if 'widths' in w:
        parts.append('widths=%s' % w['widths'])
    if 'fuel' in w:
        parts.append('fuel=%s' % w['fuel'])
    if 'state' in w:
        parts.append('state=%s' % w['state'])
    parts.append('args=%s' % vals)
    return ' '.join(parts)


def load_history(path):
    if not os.path.exists(path):
        return []
    return json.load(open(path))


def next_candidate(f, history, allow_truncating, value_rounds, fuel_start):
    ladder = width_ladder(f, allow_truncating)
    wi = 0
    vi = 0
    fuel = fuel_start
    lo = 0
    hi = 0
    starved = 0
    for h in history:
        out = h.get('outcome', '')
        w = h.get('witness') or {}
        used_fuel = w.get('fuel', fuel)
        has_poison = any(a.get('kind') == 'poison' for a in w.get('args', []))
        if out.startswith('fuel-starved'):
            starved += 1
            if used_fuel >= MAX_FUEL or (has_poison and starved >= 2):
                vi += 1
                fuel = fuel_start
                lo = hi = 0
                starved = 0
            else:
                lo = max(lo, used_fuel)
                fuel = min(MAX_FUEL, max(used_fuel * 2, fuel_start))
                if hi and fuel >= hi:
                    fuel = (lo + hi) // 2 if hi - lo > 1 else hi
        elif out in ('gate-oom', 'gate-timeout', 'gate-resource'):
            hi = used_fuel if (hi == 0 or used_fuel < hi) else hi
            if hi - lo <= 1:
                wi += 1
                vi = 0
                lo = hi = 0
                fuel = fuel_start
            else:
                fuel = (lo + hi) // 2
        elif out in ('refinement-holds', 'duplicate', 'schema-invalid', 'propose-failed', 'gate-error', 'trust-failed'):
            vi += 1
            starved = 0
        elif out in ('emit-declined', 'emit-holed', 'relation-audit-failed'):
            wi += 1
            vi = 0
        width = ladder[wi] if wi < len(ladder) else None
        if vi >= min(value_rounds, value_space(f, width or 4)):
            wi += 1
            vi = 0
            lo = hi = 0
            fuel = fuel_start
    if wi >= len(ladder):
        return None
    width = ladder[wi]
    return {'width': width, 'value_index': vi, 'fuel': fuel, 'ladder': ladder}


def main():
    ap = argparse.ArgumentParser(prog='cex_search.py')
    sub = ap.add_subparsers(dest='cmd', required=True)
    p = sub.add_parser('facts')
    p.add_argument('input')
    p = sub.add_parser('next')
    p.add_argument('input')
    p.add_argument('--history', required=True)
    p.add_argument('--mode', choices=['enum', 'llm'], default='enum')
    p.add_argument('--out', required=True)
    p.add_argument('--prompt-out', default=None)
    p.add_argument('--program', default=None)
    p.add_argument('--case', default=None)
    p.add_argument('--fuel-start', type=int, default=2)
    p.add_argument('--value-rounds', type=int, default=3)
    p.add_argument('--allow-truncating-width', action='store_true')
    p = sub.add_parser('check')
    p.add_argument('witness')
    p.add_argument('input')
    p = sub.add_parser('key')
    p.add_argument('witness')
    p = sub.add_parser('brief')
    p.add_argument('witness')
    p = sub.add_parser('classify')
    p.add_argument('cert')
    p.add_argument('log')
    p.add_argument('rc', type=int)
    p.add_argument('--oom', action='store_true')
    p = sub.add_parser('extract')
    p.add_argument('log')
    p.add_argument('out')
    a = ap.parse_args()

    if a.cmd == 'facts':
        print(json.dumps(facts(open(a.input, encoding='utf-8').read()), indent=1))
        return 0
    if a.cmd == 'check':
        f = facts(open(a.input, encoding='utf-8').read())
        try:
            w = json.load(open(a.witness))
        except Exception as e:
            print('invalid JSON: %s' % e)
            return 1
        err = check_witness(w, f, width_required=True)
        if err:
            print(err)
            return 1
        return 0
    if a.cmd == 'key':
        print(dedup_key(json.load(open(a.witness))))
        return 0
    if a.cmd == 'brief':
        print(brief(json.load(open(a.witness))))
        return 0
    if a.cmd == 'classify':
        o, d = classify(a.cert, a.log, a.rc, a.oom)
        print('%s\t%s' % (o, re.sub(r'\s+', ' ', d)[:160]))
        return 0
    if a.cmd == 'extract':
        log = open(a.log, encoding='utf-8', errors='ignore').read()
        best = None
        for m in re.finditer(r'\{', log):
            depth = 0
            for i in range(m.start(), len(log)):
                if log[i] == '{':
                    depth += 1
                elif log[i] == '}':
                    depth -= 1
                    if depth == 0:
                        try:
                            o = json.loads(log[m.start():i + 1])
                            if isinstance(o, dict) and 'args' in o:
                                best = o
                        except Exception:
                            pass
                        break
        if best is None:
            return 1
        json.dump(best, open(a.out, 'w'))
        return 0

    text = open(a.input, encoding='utf-8').read()
    f = facts(text)
    isha = sha256_file(a.input)
    case = a.case or os.path.splitext(os.path.basename(a.input))[0]
    history = load_history(a.history)
    nxt = next_candidate(f, history, a.allow_truncating_width, a.value_rounds, a.fuel_start)
    if nxt is None:
        print('exhausted')
        return 3
    if a.mode == 'enum':
        values = value_tuple(f, nxt['width'] or 4, nxt['value_index'])
        w = make_witness(f, case, isha, values, nxt['width'], nxt['fuel'])
        json.dump(w, open(a.out, 'w'), indent=1)
        print(brief(w))
        return 0
    prog = strip_lean_comments(open(a.program or a.input, encoding='utf-8').read()).strip()
    refuted = '\n'.join('%s   [%s]' % (brief(h['witness']), h.get('outcome', ''))
                        for h in history if h.get('witness'))
    txt = prompt_text(f, prog, case, isha, a.out, len(history) + 1, nxt['fuel'], nxt['width'], refuted,
                      ' '.join(str(x) for x in nxt['ladder'] if x))
    open(a.prompt_out or (a.out + '.prompt'), 'w', encoding='utf-8').write(txt)
    print('fuel=%s width=%s' % (nxt['fuel'], nxt['width']))
    return 0


if __name__ == '__main__':
    sys.exit(main())
