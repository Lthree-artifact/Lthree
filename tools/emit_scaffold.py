#!/usr/bin/env python3
import hashlib
import json
import os
import re
import sys
import types

VERSION = 'emit_scaffold 1.0'

class Unsupported(Exception):
    def __init__(self, *args):
        super().__init__(*args)
        try:
            self.fence_line = sys._getframe(1).f_lineno
        except Exception:
            self.fence_line = None


def parse_overflow_set(rest, op):
    parts = set()
    for g in re.findall(r'overflow<([^>]*)>', rest):
        found_any = False
        for p in g.split(','):
            p = p.strip()
            if not p:
                continue
            if p not in ('nsw', 'nuw'):
                raise Unsupported(f"llvm.{op} overflow flag {p!r}")
            parts.add(p)
            found_any = True
        if not found_any:
            raise Unsupported(f"llvm.{op} empty overflow<>")
    return frozenset(parts)


_DIV_OR_GUARDS = {}


def _div_or_guard(hn, ubp):
    depth = 0
    parts, cur, i = [], '', 0
    while i < len(ubp):
        c = ubp[i]
        if c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        if depth == 0 and ubp.startswith('\u2228', i):
            parts.append(cur.strip()); cur = ''; i += 1; continue
        cur += c; i += 1
    parts.append(cur.strip())
    if len(parts) == 2:
        _DIV_OR_GUARDS[hn] = parts[1]


def _div_or_rw(p):
    return [f"{p}try rw [if_neg (fun h => {hn} (Or.inr h))]"
            for hn in sorted(_DIV_OR_GUARDS)]


BINOP_MODIFIER_KIND = {
    'add': 'overflow', 'sub': 'overflow', 'mul': 'overflow', 'shl': 'overflow',
    'lshr': 'exact', 'ashr': 'exact', 'sdiv': 'exact', 'udiv': 'exact',
    'or': 'disjoint',
    'and': None, 'xor': None, 'srem': None, 'urem': None,
}


MODIFIER_FLAGS = {
    'overflow': ('nsw', 'nuw', 'both'),
    'exact': ('exact',),
    'disjoint': ('disjoint',),
    None: (),
}


_PREFIX_MOD_RE = re.compile(r'^\s*(exact|disjoint|nneg)\b\s*')


_SSA_TOK_RE = re.compile(r'%[\w.$-]+')
_OVERFLOW_GRP_RE = re.compile(r'overflow\s*<[^>]*>')


def parse_binop_modifier(op, rest):
    if op not in BINOP_MODIFIER_KIND:
        raise Unsupported(f"llvm.{op} is not an int binop (no modifier table row)")
    legal = BINOP_MODIFIER_KIND[op]
    legal_txt = legal if legal else 'no'

    body = rest
    prefix = None
    pm = _PREFIX_MOD_RE.match(body)
    if pm:
        prefix = pm.group(1)
        body = body[pm.end():]


    resid = _SSA_TOK_RE.sub('', body)
    ovf_groups = _OVERFLOW_GRP_RE.findall(resid)
    resid_bare = _OVERFLOW_GRP_RE.sub('', resid)
    stray = re.search(r'\b(exact|disjoint|nneg)\b', resid_bare)
    if stray:
        raise Unsupported(f"llvm.{op} misplaced/duplicate {stray.group(1)!r} modifier")
    if 'overflow' in resid_bare:
        raise Unsupported(f"llvm.{op} malformed overflow modifier {rest.strip()!r}")

    if ovf_groups:
        if prefix is not None:
            raise Unsupported(f"llvm.{op} incompatible modifiers "
                              f"({prefix!r} + overflow<>)")
        if len(ovf_groups) > 1:
            raise Unsupported(f"llvm.{op} duplicate overflow<> modifier")
        if legal != 'overflow':
            raise Unsupported(f"llvm.{op} overflow<> modifier "
                              f"(llvm.{op} takes {legal_txt} modifier)")

        ovf_at = _OVERFLOW_GRP_RE.search(body)
        first_ssa = _SSA_TOK_RE.search(body)
        if first_ssa is not None and ovf_at.start() < first_ssa.start():
            raise Unsupported(f"llvm.{op} overflow<> modifier before the operands")
        parts = parse_overflow_set(body, op)
        if parts == {'nsw', 'nuw'}:
            return 'both', body
        if parts == {'nsw'}:
            return 'nsw', body
        if parts == {'nuw'}:
            return 'nuw', body
        raise Unsupported(f"llvm.{op} empty overflow<>")

    if prefix is not None:
        if prefix != legal:
            raise Unsupported(f"llvm.{op} {prefix!r} modifier "
                              f"(llvm.{op} takes {legal_txt} modifier)")
        return prefix, body

    return 'none', body


def assert_no_modifier(op, rest):
    resid = _OVERFLOW_GRP_RE.sub(' overflow ', _SSA_TOK_RE.sub('', rest))
    m = re.search(r'\b(exact|disjoint|nneg|overflow)\b', resid)
    if m:
        raise Unsupported(f"llvm.{op} {m.group(1)!r} modifier "
                          f"(llvm.{op} takes no modifier)")


_F9_EXTENDED = ("F9 with extended features (w1/multi-assume/shift/cast) "
              "unsupported")
INTERACTIONS = [

    (frozenset({'f9route', 'ret_outside_pred'}), 'UNKNOWN',
     'f9-ret-outside-pred', 'F9: return uses args outside the predicate'),
    (frozenset({'f9route', 'sdis'}), 'UNKNOWN',
     'f9-disjoint', 'F9 with disjoint/i1 args'),
    (frozenset({'f9route', 'i1args'}), 'UNKNOWN',
     'f9-i1args', 'F9 with disjoint/i1 args'),
    (frozenset({'f9route', 'fw', 'shl_flagged'}), 'UNKNOWN',
     'f9-fw-flagged-shl', 'F9 with an nsw/nuw-flagged shl'),
    (frozenset({'f9route', 'sym', 'newfeat'}), 'UNKNOWN',
     'f9-sym-extended', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'extra_binders'}), 'UNKNOWN',
     'f9-fw-extras', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'multi_assume'}), 'UNKNOWN',
     'f9-fw-multi', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'leaf_amt'}), 'UNKNOWN',
     'f9-fw-leafamt', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'exf_amt'}), 'UNKNOWN',
     'f9-fw-exfamt', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'anydiv'}), 'UNKNOWN',
     'f9-fw-div', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'i1sym'}), 'UNKNOWN',
     'f9-fw-i1sym', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'symmode'}), 'UNKNOWN',
     'f9-fw-symmode', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'op_trunc'}), 'UNKNOWN',
     'f9-fw-trunc', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'op_ispow2'}), 'UNKNOWN',
     'f9-fw-ispow2', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'op_ctpop'}), 'UNKNOWN',
     'f9-fw-ctpop', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'op_cttz'}), 'UNKNOWN',
     'f9-fw-cttz', _F9_EXTENDED),
    (frozenset({'f9route', 'fw', 'op_ctlz'}), 'UNKNOWN',
     'f9-fw-ctlz', _F9_EXTENDED),
    (frozenset({'f9route'}), 'ALLOW', 'F9', None),

    (frozenset({'fwchain', 'symmode'}), 'UNKNOWN', 'fwchain-mix-symmode',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'i1sym'}), 'UNKNOWN', 'fwchain-mix-i1sym',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'i1sel'}), 'UNKNOWN', 'fwchain-mix-i1sel',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'sdis'}), 'UNKNOWN', 'fwchain-mix-sdis',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'i1args'}), 'UNKNOWN', 'fwchain-mix-i1args',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'has_exact'}), 'UNKNOWN', 'fwchain-mix-exact',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'multi_assume'}), 'UNKNOWN', 'fwchain-mix-multi',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'use_seqflag'}), 'UNKNOWN', 'fwchain-mix-seqflag',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'predflag_mode'}), 'UNKNOWN', 'fwchain-mix-predflag',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'exf_amt'}), 'UNKNOWN', 'fwchain-mix-exfamt',
     'fw flag chain (flagged shl / div+flag) mixed with'),
    (frozenset({'fwchain', 'pred_div'}), 'UNKNOWN', 'fwchain-pred-div',
     'fw flag chain with a pred-side division'),
    (frozenset({'fwchain', 'tgt_div'}), 'UNKNOWN', 'fwchain-tgt-div',
     'fw flag chain with an uncovered tgt-side division'),
    (frozenset({'fwchain'}), 'ALLOW', 'fwchain', None),
    (frozenset(), 'ALLOW', 'standard', None),
]
_RANK = {'DENY': 3, 'UNKNOWN': 2, 'ALLOW': 1}


def interactions_decide(features):
    true_atoms = {k for k, v in features.items() if v}
    best = None
    for key, cls, rid, legacy in INTERACTIONS:
        if key <= true_atoms:
            if best is None or _RANK[cls] > _RANK[best[0]]:
                best = (cls, rid, legacy)
    return best or ('UNKNOWN', 'no-matching-interaction', None)


def _shadow_log(case, features, decision):
    try:
        path = os.environ.get('EMIT_SHADOW')
        with open(path, 'a', encoding='utf-8') as f:
            json.dump({'case': case,
                       'atoms': sorted(k for k, v in features.items() if v),
                       'decision': decision[:2],
                       'legacy': decision[2]}, f)
            f.write('\n')
    except Exception:
        pass


_EXTRA_TOKEN_RE = re.compile(
    r'[A-Za-z_]\w*|\d+|≤|≥|≠|<=|>=|[<>=+\-*^/%()]|\s+')


def check_extra_binder_shared(g, allowed_widths):
    allowed = set(allowed_widths) | {'Nat'}
    bm = re.fullmatch(r'\(\s*([^:\s]+)\s*:\s*(.*?)\s*\)', g, re.S)
    if not bm:
        raise Unsupported(f"cannot read extra binder {g!r}")
    name, btype = bm.group(1), bm.group(2)
    pos = 0
    for m in _EXTRA_TOKEN_RE.finditer(btype):
        if m.start() != pos:
            raise Unsupported(
                f"extra binder type token {btype[pos:]!r} not whitelisted")
        tok = m.group(0)
        pos = m.end()
        if re.fullmatch(r'[A-Za-z_]\w*', tok) and tok not in allowed:
            raise Unsupported(
                f"extra binder references non-whitelisted name {tok!r}")
    if pos != len(btype):
        raise Unsupported(
            f"extra binder type token {btype[pos:]!r} not whitelisted")
    return name


def _build_shape_a2():

    FAMILY = 'A2'
    SHAPE = 'A2'


    A2_WVSET = []


    BIN_NOWRAP = {"add", "sub", "mul", "shl"}
    BIN_PLAIN  = {"and", "or", "xor", "lshr", "ashr"}


    BIN_UB     = {"udiv", "sdiv", "urem", "srem"}
    SHIFTS     = {"shl", "lshr", "ashr"}
    ICMP_PRED  = {"eq","ne","slt","sle","sgt","sge","ult","ule","ugt","uge"}


    DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*((?:\([^)]*\)\s*)+):=\s*'
        r'\[llvm\(([A-Za-z_][\w\s,]*?)\)\|\s*\{(.*?)\}\s*\]', re.S)


    FW_DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*:=\s*'
        r'\[llvm\(\)\|\s*\{(.*?)\}\s*\]', re.S)

    BLOCK_HDR_RE = re.compile(r'\^\w+\([^)]*\):')


    EXTRA_TOKEN_RE = re.compile(r'[A-Za-z_]\w*|\d+|≤|≥|≠|<=|>=|[<>=+\-*^/%()]|\s+')

    def parse_type(t, wv='w'):
        t = t.strip()
        if wv is None:


            m = re.fullmatch(r'i(\d+)', t)
            if m and int(m.group(1)) > 0: return m.group(1)
            raise Unsupported(f"type {t!r} (fixed-width dialect requires literal iK)")
        if t == '_':      return wv
        if t == 'i1':     return '1'
        m = re.fullmatch(r'i(\d+)', t)
        if m:             return m.group(1)
        if t == wv:       return wv
        if t in A2_WVSET: return t
        raise Unsupported(f"type {t!r}")

    def parse_func(block, wv):
        m = re.search(r'llvm\.func\s+@(\S+)\(([^)]*)\)\s*->\s*(\S+)\s*\{', block)
        if not m: raise Unsupported("no llvm.func header")
        name, arglist, ret = m.group(1), m.group(2), m.group(3)
        args = []
        for a in arglist.split(','):
            a = a.strip()
            if not a: continue
            am = re.fullmatch(r'%(\S+)\s*:\s*(\S+)', a)
            if not am: raise Unsupported(f"arg {a!r}")
            args.append((am.group(1), parse_type(am.group(2), wv)))

        blocks = BLOCK_HDR_RE.findall(block)
        if len(blocks) != 1:
            raise Unsupported(f"expected single block, found {len(blocks)}: {blocks}")
        body = block[BLOCK_HDR_RE.search(block).end():]
        ops = []
        retvar = None
        for line in body.splitlines():
            line = line.strip().rstrip('}').strip()
            if not line: continue

            rm = re.match(r'llvm\.return\s+%(\S+?)(\s*:\s*(\S+))?$', line)
            if rm: retvar = rm.group(1); continue

            om = re.match(r'%(\S+)\s*=\s*llvm\.([a-zA-Z][A-Za-z0-9._]*)\s*(.*)', line)
            if not om:
                if line.startswith('llvm.assume'):

                    raise Unsupported("llvm.assume (assume family) -> route to Shape-B recipe path")
                if line.startswith('llvm.') or line.startswith('%'):
                    raise Unsupported(f"op line {line!r}")
                continue
            res, op, rest = om.group(1), om.group(2), om.group(3)
            ops.append((res, op, rest))
        if retvar is None: raise Unsupported("no return")
        return name, args, ret, ops, retvar

    def build_defs(ops, wv):
        d = {}
        for res, op, rest in ops:
            if op == 'mlir.constant':


                bm = re.search(r'\(\s*(true|false)\s*\)\s*:\s*(\S+)', rest)
                if bm:
                    d[res] = ('const', 1 if bm.group(1) == 'true' else 0, parse_type(bm.group(2), wv))
                    continue
                if wv is None:


                    fcm = re.search(r'\(\s*(-?\d+)\s*:\s*(\S+?)\s*\)\s*:\s*(\S+)', rest)
                    if not fcm:
                        raise Unsupported(f"constant {rest!r} (fixed-width requires (N : iK) : iK)")
                    inner = parse_type(fcm.group(2), None)
                    outer = parse_type(fcm.group(3), None)
                    if inner != outer:
                        raise Unsupported(f"constant width mismatch {rest!r}")
                    d[res] = ('const', int(fcm.group(1)), outer)
                    continue

                wm = re.search(r'\(\s*'+re.escape(wv)+r'\s*:\s*\S+?\s*\)\s*:\s*(\S+)', rest)
                if wm and not wv.isdigit():
                    d[res] = ('wconst', parse_type(wm.group(1), wv))
                    continue
                cm = re.search(r'\(\s*(-?\d+)\s*:\s*(\S+?)\s*\)\s*:\s*(\S+)', rest)
                if not cm:


                    cm2 = re.match(r'\(?\s*(-?\d+)\s*:', rest.strip())
                    if not cm2: raise Unsupported(f"constant {rest!r}")
                    d[res] = ('const', int(cm2.group(1)), wv)
                else:
                    d[res] = ('const', int(cm.group(1)), parse_type(cm.group(3), wv))
            elif op in BIN_UB:


                mflag, _mbody = parse_binop_modifier(op, rest)
                exact = False
                if mflag == 'exact':
                    if wv is not None or op not in ('udiv', 'sdiv'):
                        raise Unsupported(f"llvm.{op} exact flag")
                    exact = True
                operands = re.findall(r'%(\S+?)[,\s]', rest + ' ')
                if len(operands) < 2:
                    raise Unsupported(f"llvm.{op} operands {rest!r}")
                d[res] = ('binub', op, operands[:2], exact)
            elif op in BIN_NOWRAP or op in BIN_PLAIN:


                mflag, _mbody = parse_binop_modifier(op, rest)
                exact_sh = False
                if mflag == 'exact':
                    if wv is not None or op not in ('lshr', 'ashr'):
                        raise Unsupported(f"llvm.{op} exact flag")
                    exact_sh = True
                disjoint = mflag == 'disjoint'
                operands = re.findall(r'%(\S+?)[,\s]', rest + ' ')
                if mflag == 'both':         flags = 'both'
                elif mflag == 'nsw':        flags = 'nsw'
                elif mflag == 'nuw':        flags = 'nuw'
                else:                       flags = 'none'
                if disjoint: flags = 'disjoint'
                if exact_sh:
                    if flags != 'none':
                        raise Unsupported(f"llvm.{op} exact+overflow flags")
                    flags = 'exact'
                d[res] = ('bin', op, operands[:2], flags)
            elif op == 'icmp':
                assert_no_modifier(op, rest)
                pm = re.match(r'"(\w+)"\s+%(\S+?),\s*%(\S+)', rest)
                if not pm: raise Unsupported(f"icmp {rest!r}")
                pred = pm.group(1)
                if pred not in ICMP_PRED: raise Unsupported(f"icmp pred {pred}")
                d[res] = ('icmp', pred, [pm.group(2), pm.group(3).split()[0].rstrip(':').strip()])
            elif op == 'select':
                assert_no_modifier(op, rest)
                operands = re.findall(r'%([A-Za-z0-9_]+)', rest)
                d[res] = ('select', operands[:3])
            elif op == 'ctpop':
                assert_no_modifier(op, rest)
                operands = re.findall(r'%([A-Za-z0-9_]+)', rest)
                d[res] = ('un', 'ctpop', operands[:1])
            elif op in ('cttz', 'ctlz'):

                fm = re.match(r'%([A-Za-z0-9_]+)\s*,\s*(true|false)', rest)
                if not fm: raise Unsupported(f"llvm.{op} operands {rest!r}")
                d[res] = ('ctz', op, fm.group(1), fm.group(2))
            elif op in ('zext', 'sext', 'trunc'):


                nneg = False
                r2 = rest.strip()
                if wv is None and op == 'trunc':
                    tm = re.match(r'%(\S+?)\s+overflow<([^>]*)>\s*:\s*(\S+)\s+to\s+(\S+)\s*$', r2)
                    if tm:

                        parts = parse_overflow_set(r2, 'trunc')
                        if not parts:
                            raise Unsupported("llvm.trunc empty overflow<>")
                        dst = parse_type(tm.group(4), None)
                        parse_type(tm.group(3), None)
                        d[res] = ('castf', 'trunc', tm.group(1), dst,
                                  'true' if 'nsw' in parts else 'false',
                                  'true' if 'nuw' in parts else 'false')
                        continue
                if wv is None and op == 'zext':
                    nm = re.match(r'nneg\s+(.*)$', r2, re.S)
                    if nm:
                        nneg = True
                        r2 = nm.group(1)
                if re.search(r'\bnneg\b|\bnonNeg\b|overflow', r2):
                    raise Unsupported(f"llvm.{op} with flag")
                cm = re.match(r'%(\S+?)\s*:\s*(\S+)\s+to\s+(\S+)\s*$', r2)
                if not cm: raise Unsupported(f"cast form {rest!r}")
                dst = parse_type(cm.group(3), wv)
                parse_type(cm.group(2), wv)
                if nneg:
                    d[res] = ('cast', op, cm.group(1), dst, True)
                else:
                    d[res] = ('cast', op, cm.group(1), dst)
            elif op == 'freeze':
                assert_no_modifier(op, rest)
                operands = re.findall(r'%([A-Za-z0-9_]+)', rest)
                d[res] = ('freeze', operands[:1])
            else:
                raise Unsupported(f"opcode llvm.{op}")


        for res, kind in d.items():
            if kind[0] == 'bin' and kind[1] in SHIFTS:
                amt = kind[2][1] if len(kind[2]) > 1 else None
                if amt in d and d[amt][0] == 'wconst':
                    raise Unsupported("width-constant as shift amount (normal-form instability)")
        return d

    FLAG = {'none': '', 'nsw': ' (LLVM.NoWrapFlags.mk true false)',
            'nuw': ' (LLVM.NoWrapFlags.mk false true)', 'both': ' (LLVM.NoWrapFlags.mk true true)',
            'disjoint': ' (LLVM.DisjointFlag.mk true)',
            'exact': ' (LLVM.ExactFlag.mk true)'}

    def emit_expr(v, defs, argref, wv):
        if v in argref:
            return argref[v]
        if v not in defs:
            raise Unsupported(f"unknown value %{v}")
        kind = defs[v]
        if kind[0] == 'const':
            cw = kind[2] if len(kind) > 2 else wv


            lit = f"({kind[1]})" if kind[1] < 0 else f"{kind[1]}"
            return f"(LLVM.const? {cw} {lit})"
        if kind[0] == 'wconst':

            return f"(LLVM.const? {kind[1]} ({wv} : Int))"
        if kind[0] == 'bin':
            _, op, ops, flags = kind
            a = emit_expr(ops[0], defs, argref, wv); b = emit_expr(ops[1], defs, argref, wv)
            return f"(LLVM.{op} {a} {b}{FLAG[flags]})"
        if kind[0] == 'icmp':
            _, pred, ops = kind
            a = emit_expr(ops[0], defs, argref, wv); b = emit_expr(ops[1], defs, argref, wv)
            return f"(LLVM.icmp LLVM.IntPred.{pred} {a} {b})"
        if kind[0] == 'select':
            c, a, b = [emit_expr(x, defs, argref, wv) for x in kind[1]]
            return f"(LLVM.select {c} {a} {b})"
        if kind[0] == 'cast':
            op, operand, dst = kind[1], kind[2], kind[3]
            if len(kind) == 5 and kind[4]:


                return f"(LLVM.{op} {dst} {emit_expr(operand, defs, argref, wv)} (LLVM.NonNegFlag.mk true))"
            return f"(LLVM.{op} {dst} {emit_expr(operand, defs, argref, wv)})"
        if kind[0] == 'castf':
            _, op, operand, dst, nsw, nuw = kind


            return f"(LLVM.{op} {dst} {emit_expr(operand, defs, argref, wv)} (LLVM.NoWrapFlags.mk {nsw} {nuw}))"
        if kind[0] == 'ctz':
            _, op, a, flag = kind
            return f"(LLVM.{op} {emit_expr(a, defs, argref, wv)} {{is_zero_poison := {flag}}})"
        if kind[0] == 'un':
            return f"(LLVM.{kind[1]} {emit_expr(kind[2][0], defs, argref, wv)})"
        if kind[0] == 'freeze':
            return f"(LLVM.freeze {emit_expr(kind[1][0], defs, argref, wv)})"
        raise Unsupported(str(kind))

    def tree_has_ub(v, defs, seen=None):
        if seen is None: seen = set()
        if v in seen or v not in defs: return False
        seen.add(v)
        kind = defs[v]
        if kind[0] == 'binub': return True
        if kind[0] == 'bin':    return any(tree_has_ub(o, defs, seen) for o in kind[2])
        if kind[0] == 'icmp':   return any(tree_has_ub(o, defs, seen) for o in kind[2])
        if kind[0] == 'select': return any(tree_has_ub(o, defs, seen) for o in kind[1])
        if kind[0] == 'cast':   return tree_has_ub(kind[2], defs, seen)
        if kind[0] == 'castf':  return tree_has_ub(kind[2], defs, seen)
        if kind[0] == 'ctz':    return tree_has_ub(kind[2], defs, seen)
        if kind[0] == 'un':     return tree_has_ub(kind[2][0], defs, seen)
        if kind[0] == 'freeze': return tree_has_ub(kind[1][0], defs, seen)
        return False

    def emit_expr_ub(v, defs, argref, wv):
        if v in argref:
            return f"(some {argref[v]})"
        if v not in defs:
            raise Unsupported(f"unknown value %{v}")
        kind = defs[v]
        if kind[0] == 'const':
            cw = kind[2] if len(kind) > 2 else wv
            lit = f"({kind[1]})" if kind[1] < 0 else f"{kind[1]}"
            return f"(some (LLVM.const? {cw} {lit}))"
        if kind[0] == 'wconst':
            return f"(some (LLVM.const? {kind[1]} ({wv} : Int)))"
        if kind[0] == 'bin':
            _, op, ops, flags = kind
            a = emit_expr_ub(ops[0], defs, argref, wv); b = emit_expr_ub(ops[1], defs, argref, wv)
            return f"(InstCombine.lift2 (fun x y => LLVM.{op} x y{FLAG[flags]}) {a} {b})"
        if kind[0] == 'binub':
            _, op, ops, exact = kind
            a = emit_expr_ub(ops[0], defs, argref, wv); b = emit_expr_ub(ops[1], defs, argref, wv)
            fl = " (LLVM.ExactFlag.mk true)" if exact else ""
            return f"(InstCombine.lift2UB (fun x y => LLVM.{op} x y{fl}) {a} {b})"
        if kind[0] == 'icmp':
            _, pred, ops = kind
            a = emit_expr_ub(ops[0], defs, argref, wv); b = emit_expr_ub(ops[1], defs, argref, wv)
            return f"(InstCombine.lift2 (fun x y => LLVM.icmp LLVM.IntPred.{pred} x y) {a} {b})"
        if kind[0] == 'select':
            c, a, b = [emit_expr_ub(x, defs, argref, wv) for x in kind[1]]
            return f"(InstCombine.lift3 (fun c x y => LLVM.select c x y) {c} {a} {b})"
        if kind[0] == 'cast':
            op, operand, dst = kind[1], kind[2], kind[3]
            if len(kind) == 5 and kind[4]:
                return f"(InstCombine.lift1 (fun x => LLVM.{op} {dst} x (LLVM.NonNegFlag.mk true)) {emit_expr_ub(operand, defs, argref, wv)})"
            return f"(InstCombine.lift1 (fun x => LLVM.{op} {dst} x) {emit_expr_ub(operand, defs, argref, wv)})"
        if kind[0] == 'castf':
            _, op, operand, dst, nsw, nuw = kind
            return f"(InstCombine.lift1 (fun x => LLVM.{op} {dst} x (LLVM.NoWrapFlags.mk {nsw} {nuw})) {emit_expr_ub(operand, defs, argref, wv)})"
        if kind[0] == 'ctz':
            _, op, a, flag = kind
            return f"(InstCombine.lift1 (fun x => LLVM.{op} x {{is_zero_poison := {flag}}}) {emit_expr_ub(a, defs, argref, wv)})"
        if kind[0] == 'un':
            return f"(InstCombine.lift1 (fun x => LLVM.{kind[1]} x) {emit_expr_ub(kind[2][0], defs, argref, wv)})"
        if kind[0] == 'freeze':
            return f"(InstCombine.lift1 (fun x => LLVM.freeze x) {emit_expr_ub(kind[1][0], defs, argref, wv)})"
        raise Unsupported(str(kind))

    def ty(width):
        return f"InstCombine.LLVM.Ty.bitvec {width}"


    def check_extra_binder(g, wv):
        return check_extra_binder_shared(g, (wv,))

    def extract_defs(text):
        ms = list(DEF_RE.finditer(text))
        if len(ms) != 2:
            raise Unsupported(f"expected exactly 2 llvm defs, found {len(ms)}")
        (m_src, m_tgt) = ms
        src_name, src_binders, wv_s, src_body = m_src.groups()
        tgt_name, tgt_binders, wv_t, tgt_body = m_tgt.groups()
        if 'src' not in src_name:
            raise Unsupported(f"first def {src_name!r} has no 'src' in name")
        if re.sub('src', 'tgt', src_name) != tgt_name:
            raise Unsupported(f"def names do not pair: {src_name!r} vs {tgt_name!r}")


        wlist = lambda s: [w.strip() for w in s.split(',') if w.strip()]
        wvlist_s, wvlist_t = wlist(wv_s), wlist(wv_t)
        if wvlist_s != wvlist_t:
            raise Unsupported(f"width symbols differ: {wvlist_s} vs {wvlist_t}")
        for w in wvlist_s:
            if not re.fullmatch(r'[A-Za-z_]\w*', w):
                raise Unsupported(f"width symbol {w!r} is not an identifier")
        if len(wvlist_s) != len(set(wvlist_s)):
            raise Unsupported(f"duplicate width symbol in {wvlist_s}")
        norm = lambda s: re.sub(r'\s+', ' ', s.strip())
        if norm(src_binders) != norm(tgt_binders):
            raise Unsupported("src/tgt binder lists differ")
        groups = re.findall(r'\([^)]*\)', src_binders)


        g0 = re.fullmatch(r'\(\s*([A-Za-z_][\w\s]*?)\s*:\s*Nat\s*\)',
                          groups[0].strip())
        if not g0:
            raise Unsupported(f"first binder {groups[0]!r} is not (W.. : Nat)")
        binder_widths = g0.group(1).split()
        if binder_widths != wvlist_s:
            raise Unsupported(f"binder widths {binder_widths} != "
                              f"llvm({wvlist_s})")
        extras = [g.strip() for g in groups[1:]]


        extra_names = [check_extra_binder_shared(g, wvlist_s) for g in extras]
        return (src_name, tgt_name, wvlist_s, extra_names, " ".join(extras),
                src_body, tgt_body, m_src.group(0), m_tgt.group(0))

    def emit_text(text, base):
        (src_name, tgt_name, wvlist, extra_names, extra_binders,
         src_body, tgt_body, src_full, tgt_full) = extract_defs(text)


        A2_WVSET[:] = wvlist
        primary = wvlist[0]
        wbind = " ".join(wvlist)
        wapp = " ".join(wvlist)
        name = base
        sname, sargs, sret, sops, sretv = parse_func(src_body, primary)
        tname, targs, tret, tops, tretv = parse_func(tgt_body, primary)
        if [a[1] for a in sargs] != [a[1] for a in targs]:
            raise Unsupported("src/tgt arg types differ")
        if sret != tret: raise Unsupported("src/tgt return types differ")
        n = len(sargs)
        argnames = [a[0] for a in sargs]
        argw = {a[0]: a[1] for a in sargs}

        if any(w in argnames for w in wvlist):
            raise Unsupported("a width var collides with an SSA arg name")
        for en in extra_names:
            if en in argnames or en in wvlist or en == 'V':
                raise Unsupported(f"extra binder name {en!r} collides")

        idx = {a[0]: n-1-p for p, a in enumerate(sargs)}
        retw = parse_type(sret, primary)

        L = []
        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax")
        L.append("")
        L.append("open scoped InstCombine")
        L.append("open BitVec")
        L.append("")
        L.append(f"-- ===== GIVEN (input): the two programs =====")
        L.append(src_full.strip())
        L.append("")
        L.append(tgt_full.strip())
        L.append("")
        L.append("-- ===== AUTO-EMITTED SCAFFOLD (0 LLM) =====")


        ctxlist = ", ".join(ty(argw[a]) for a in reversed(argnames))
        L.append(f"abbrev {name}_ctx ({wbind} : Nat) : Ctxt InstCombine.LLVM.Ty :=")
        L.append(f"  Ctxt.ofList [{ctxlist}]")

        for a in argnames:
            L.append(f"def {name}_{a} ({wbind} : Nat) (V : InstCombine.InputValuation ({name}_ctx {wapp})) : LLVM.IntW {argw[a]} :=")
            L.append(f"  V (Ctxt.Var.mk (Γ := {name}_ctx {wapp}) (t := {ty(argw[a])}) {idx[a]} (by simp [{name}_ctx]))")

        argref_V = {a: f"({name}_{a} {wapp} V)" for a in argnames}
        sdefs = build_defs(sops, primary); tdefs = build_defs(tops, primary)


        ub_mode = tree_has_ub(sretv, sdefs) or tree_has_ub(tretv, tdefs)
        emit_e = emit_expr_ub if ub_mode else emit_expr
        semty = f"LLVM.IntWUB {retw}" if ub_mode else f"LLVM.IntW {retw}"
        src_sem = emit_e(sretv, sdefs, argref_V, primary)
        tgt_sem = emit_e(tretv, tdefs, argref_V, primary)
        L.append(f"def {name}_src_sem ({wbind} : Nat) (V : InstCombine.InputValuation ({name}_ctx {wapp})) : {semty} :=")
        L.append(f"  {src_sem}")
        L.append(f"def {name}_tgt_sem ({wbind} : Nat) (V : InstCombine.InputValuation ({name}_ctx {wapp})) : {semty} :=")
        L.append(f"  {tgt_sem}")


        L.append(f"def {name}_ret (x : {semty}) :")
        L.append(f"    HVector TyDenote.toType [{ty(retw)}] :=")
        if ub_mode:
            L.append(f"  (x : TyDenote.toType ({ty(retw)})) ::ₕ HVector.nil")
        else:
            L.append(f"  (some x : TyDenote.toType ({ty(retw)})) ::ₕ HVector.nil")


        argref_var = {a: a for a in argnames}
        src_val = emit_e(sretv, sdefs, argref_var, primary)
        tgt_val = emit_e(tretv, tdefs, argref_var, primary)
        binders = " ".join(f"({a} : LLVM.IntW {argw[a]})" for a in argnames)
        esig = (" " + extra_binders) if extra_binders else ""
        eapp = (" " + " ".join(extra_names)) if extra_names else ""
        L.append("")
        L.append(f"-- ===== THE ONLY HOLE: the value-level refinement lemma (LLM writes this) =====")
        L.append(f"theorem {name}_value ({wbind} : Nat){esig} {binders} :")
        L.append(f"    {src_val}")
        L.append(f"      ⊑ {tgt_val} := by")
        L.append(f"  sorry")

        L.append("")
        L.append(f"-- ===== AUTO-EMITTED glue (0 LLM) =====")
        L.append(f"theorem {name}_correct ({wbind} : Nat){esig} : {src_name} {wapp}{eapp} ⊑ {tgt_name} {wapp}{eapp} := by")
        L.append(f"  unfold {src_name} {tgt_name}")
        L.append(f"  intro V")
        L.append(f"  change")
        L.append(f"    (some ({name}_ret ({name}_src_sem {wapp} V)) ⊑ some ({name}_ret ({name}_tgt_sem {wapp} V)))")
        L.append(f"  apply ImmediateUBOr.IsRefinedBy.bothValues")
        L.append(f"  unfold {name}_ret")
        L.append(f"  constructor")
        callargs = " ".join(f"({name}_{a} {wapp} V)" for a in argnames)
        if ub_mode:


            L.append(f"  · exact (by")
            L.append(f"      simpa [{name}_src_sem, {name}_tgt_sem] using")
            L.append(f"        {name}_value {wapp}{eapp} {callargs})")
        else:
            L.append(f"  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by")
            L.append(f"      simpa [{name}_src_sem, {name}_tgt_sem] using")
            L.append(f"        {name}_value {wapp}{eapp} {callargs}")
        L.append(f"  · exact True.intro")
        return "\n".join(L) + "\n"


    def extract_defs_fw(text):
        ms = list(FW_DEF_RE.finditer(text))
        if len(ms) != 2:
            raise Unsupported(f"expected exactly 2 binder-less [llvm()| defs, found {len(ms)}")
        (m_src, m_tgt) = ms
        src_name, src_body = m_src.groups()
        tgt_name, tgt_body = m_tgt.groups()
        if 'src' not in src_name:
            raise Unsupported(f"first def {src_name!r} has no 'src' in name")
        if re.sub('src', 'tgt', src_name) != tgt_name:
            raise Unsupported(f"def names do not pair: {src_name!r} vs {tgt_name!r}")
        return (src_name, tgt_name, src_body, tgt_body, m_src.group(0), m_tgt.group(0))

    def sanitize_arg_fw(a):
        s = a if re.fullmatch(r'[A-Za-z_]\w*', a) else 'v' + a
        if not re.fullmatch(r'[A-Za-z_]\w*', s):
            raise Unsupported(f"arg name {a!r} not sanitizable to a Lean identifier")
        return s

    def emit_text_fw(text, base):
        (src_name, tgt_name, src_body, tgt_body, src_full, tgt_full) = extract_defs_fw(text)
        name = base
        sname, sargs, sret, sops, sretv = parse_func(src_body, None)
        tname, targs, tret, tops, tretv = parse_func(tgt_body, None)
        if [a[1] for a in sargs] != [a[1] for a in targs]:
            raise Unsupported("src/tgt arg types differ")
        if sret != tret: raise Unsupported("src/tgt return types differ")
        n = len(sargs)
        argnames = [a[0] for a in sargs]
        argw = {a[0]: a[1] for a in sargs}
        san = {a: sanitize_arg_fw(a) for a in argnames}
        if len(set(san.values())) != n or 'V' in san.values():
            raise Unsupported("sanitized arg names collide")

        idx = {a[0]: n-1-p for p, a in enumerate(sargs)}
        retw = parse_type(sret, None)

        L = []
        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax")
        L.append("")
        L.append("open scoped InstCombine")
        L.append("open BitVec")
        L.append("")
        L.append(f"-- ===== GIVEN (input): the two programs =====")
        L.append(src_full.strip())
        L.append("")
        L.append(tgt_full.strip())
        L.append("")
        L.append("-- ===== AUTO-EMITTED SCAFFOLD (0 LLM) =====")
        ctxlist = ", ".join(ty(argw[a]) for a in reversed(argnames))
        L.append(f"abbrev {name}_ctx : Ctxt InstCombine.LLVM.Ty :=")
        L.append(f"  Ctxt.ofList [{ctxlist}]")
        for a in argnames:
            L.append(f"def {name}_{san[a]} (V : InstCombine.InputValuation {name}_ctx) : LLVM.IntW {argw[a]} :=")
            L.append(f"  V (Ctxt.Var.mk (Γ := {name}_ctx) (t := {ty(argw[a])}) {idx[a]} (by simp [{name}_ctx]))")
        argref_V = {a: f"({name}_{san[a]} V)" for a in argnames}
        sdefs = build_defs(sops, None); tdefs = build_defs(tops, None)
        ub_mode = tree_has_ub(sretv, sdefs) or tree_has_ub(tretv, tdefs)
        emit_e = emit_expr_ub if ub_mode else emit_expr
        semty = f"LLVM.IntWUB {retw}" if ub_mode else f"LLVM.IntW {retw}"
        src_sem = emit_e(sretv, sdefs, argref_V, None)
        tgt_sem = emit_e(tretv, tdefs, argref_V, None)
        L.append(f"def {name}_src_sem (V : InstCombine.InputValuation {name}_ctx) : {semty} :=")
        L.append(f"  {src_sem}")
        L.append(f"def {name}_tgt_sem (V : InstCombine.InputValuation {name}_ctx) : {semty} :=")
        L.append(f"  {tgt_sem}")
        L.append(f"def {name}_ret (x : {semty}) :")
        L.append(f"    HVector TyDenote.toType [{ty(retw)}] :=")
        if ub_mode:
            L.append(f"  (x : TyDenote.toType ({ty(retw)})) ::ₕ HVector.nil")
        else:
            L.append(f"  (some x : TyDenote.toType ({ty(retw)})) ::ₕ HVector.nil")
        argref_var = {a: san[a] for a in argnames}
        src_val = emit_e(sretv, sdefs, argref_var, None)
        tgt_val = emit_e(tretv, tdefs, argref_var, None)
        binders = " ".join(f"({san[a]} : LLVM.IntW {argw[a]})" for a in argnames)
        L.append("")
        L.append(f"-- ===== THE ONLY HOLE: the value-level refinement lemma (LLM writes this) =====")
        L.append(f"theorem {name}_value {binders} :")
        L.append(f"    {src_val}")
        L.append(f"      ⊑ {tgt_val} := by")
        L.append(f"  sorry")
        L.append("")
        L.append(f"-- ===== AUTO-EMITTED glue (0 LLM) =====")
        L.append(f"theorem {name}_correct : {src_name} ⊑ {tgt_name} := by")
        L.append(f"  unfold {src_name} {tgt_name}")
        L.append(f"  intro V")
        L.append(f"  change")
        L.append(f"    (some ({name}_ret ({name}_src_sem V)) ⊑ some ({name}_ret ({name}_tgt_sem V)))")
        L.append(f"  apply ImmediateUBOr.IsRefinedBy.bothValues")
        L.append(f"  unfold {name}_ret")
        L.append(f"  constructor")
        callargs = " ".join(f"({name}_{san[a]} V)" for a in argnames)
        if ub_mode:
            L.append(f"  · exact (by")
            L.append(f"      simpa [{name}_src_sem, {name}_tgt_sem] using")
            L.append(f"        {name}_value {callargs})")
        else:
            L.append(f"  · exact ImmediateUBOr.IsRefinedBy.bothValues <| by")
            L.append(f"      simpa [{name}_src_sem, {name}_tgt_sem] using")
            L.append(f"        {name}_value {callargs}")
        L.append(f"  · exact True.intro")
        return "\n".join(L) + "\n"


    def _detect_fw(text: str) -> bool:
        ms = list(FW_DEF_RE.finditer(text))
        if len(ms) != 2: return False
        for m in ms:
            body = m.group(2)
            if len(BLOCK_HDR_RE.findall(body)) != 1: return False
            if 'llvm.cond_br' in body or 'llvm.br' in body: return False
        return True

    def detect(text: str) -> bool:
        try:
            if not isinstance(text, str): return False
            if 'llvm.assume' in text: return False
            ms = list(DEF_RE.finditer(text))
            if len(ms) != 2:


                return _detect_fw(text)
            for m in ms:
                body = m.group(4)
                if len(BLOCK_HDR_RE.findall(body)) != 1: return False
                if 'llvm.cond_br' in body or 'llvm.br' in body: return False
            return True
        except Exception:
            return False

    def emit(text: str, case: str) -> dict:
        _DIV_OR_GUARDS.clear()

        try:
            if not detect(text):

                if isinstance(text, str) and 'llvm.assume' in text:
                    reason = "llvm.assume (assume family) -> route to Shape-B recipe path"
                elif isinstance(text, str) and ('llvm.cond_br' in text or
                        any(len(BLOCK_HDR_RE.findall(m.group(4))) != 1 for m in DEF_RE.finditer(text))
                        or any(len(BLOCK_HDR_RE.findall(m.group(2))) != 1 for m in FW_DEF_RE.finditer(text))):
                    reason = "multi-block program (CFG family) -> out of Shape-A2 scope"
                elif isinstance(text, str) and FW_DEF_RE.search(text):
                    reason = f"family gate: expected exactly 2 single-block [llvm()| defs, found {len(list(FW_DEF_RE.finditer(text)))}"
                else:
                    reason = f"family gate: expected exactly 2 single-block [llvm(WV)| defs, found {len(list(DEF_RE.finditer(text))) if isinstance(text, str) else 'n/a'}"
                return {'status': 'decline', 'reason': reason, 'shape': SHAPE,
                        'expected_sorries': 0, 'files': {}}
            if len(list(DEF_RE.finditer(text))) == 2:
                out = emit_text(text, case)
            else:
                out = emit_text_fw(text, case)
            return {'status': 'ok', 'reason': 'one sorry hole', 'shape': SHAPE,
                    'expected_sorries': 1, 'files': {f'{case}.lean': out}}
        except Unsupported as e:
            return {'status': 'decline', 'reason': str(e), 'shape': SHAPE,
                    'expected_sorries': 0, 'files': {},
                    'fence_line': getattr(e, 'fence_line', None)}
        except Exception as e:
            return {'status': 'decline', 'reason': f'internal: {type(e).__name__}: {e}',
                    'shape': SHAPE, 'expected_sorries': 0, 'files': {},
                    'fence_line': getattr(e, 'fence_line', None)}

    return types.SimpleNamespace(FAMILY=FAMILY, detect=detect, emit=emit)


def _build_shape_b2():

    FAMILY = 'B2'


    TY = lambda w: f"InstCombine.LLVM.Ty.bitvec {w}"
    ICMP = {'eq','ne','slt','sle','sgt','sge','ult','ule','ugt','uge'}
    BVOP = {'add':'+','sub':'-','mul':'*','and':'&&&','or':'|||','xor':'^^^'}
    BOOLOP = {'and':'&&','or':'||','xor':'^^'}
    SHIFTOP = {'shl','lshr','ashr'}

    ICMP_NORM = {
     'eq': lambda a,b: f"({a} == {b})",   'ne': lambda a,b: f"({a} != {b})",
     'slt':lambda a,b: f"({a} <ₛ {b})",   'sle':lambda a,b: f"({a} ≤ₛ {b})",
     'sgt':lambda a,b: f"({b} <ₛ {a})",   'sge':lambda a,b: f"({b} ≤ₛ {a})",
     'ult':lambda a,b: f"({a} <ᵤ {b})",   'ule':lambda a,b: f"({a} ≤ᵤ {b})",
     'ugt':lambda a,b: f"({b} <ᵤ {a})",   'uge':lambda a,b: f"({b} ≤ᵤ {a})",
    }

    OVF = {('add','nuw'):'uaddOverflow',('add','nsw'):'saddOverflow',
           ('sub','nuw'):'usubOverflow',('sub','nsw'):'ssubOverflow',
           ('mul','nuw'):'umulOverflow',('mul','nsw'):'smulOverflow'}

    def ovf_preds(op, fl):
        if fl=='nswnuw': return [OVF[(op,'nsw')], OVF[(op,'nuw')]]
        return [OVF[(op,fl)]]


    DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*((?:\([^)]*\)\s*)+):=\s*'
        r'\[llvm\(([^)|]*)\)\|\s*\{(.*?)\}\s*\]', re.S)


    FW_DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*:=\s*'
        r'\[llvm\(\)\|\s*\{(.*?)\}\s*\]', re.S)


    EXTRA_TOKEN_RE = re.compile(r'[A-Za-z_]\w*|\d+|≤|≥|≠|<=|>=|[<>=+\-*^/%()]|\s+')

    def check_extra_binder(g, wv):
        return check_extra_binder_shared(g, (wv,))

    def extract_defs(text):
        ms = list(DEF_RE.finditer(text))
        srcs = [m for m in ms if '_src' in m.group(1) or 'src' in m.group(1)]
        tgts = [m for m in ms if '_tgt' in m.group(1) or 'tgt' in m.group(1)]
        if not srcs: raise Unsupported("no _src def")
        if not tgts: raise Unsupported("no _tgt def")
        m_src, m_tgt = srcs[0], tgts[0]
        src_name, src_binders, wv_s, src_body = m_src.groups()
        tgt_name, tgt_binders, wv_t, tgt_body = m_tgt.groups()
        if ',' in wv_s or ',' in wv_t:


            raise Unsupported(
                f"multi-width header [llvm({wv_s.strip()})| — per-arg width binders unsupported")
        wv_s, wv_t = wv_s.strip(), wv_t.strip()
        if wv_s != wv_t:
            raise Unsupported(f"width symbols differ: {wv_s!r} vs {wv_t!r}")
        norm = lambda s: re.sub(r'\s+', ' ', s.strip())
        if norm(src_binders) != norm(tgt_binders):
            raise Unsupported("src/tgt binder lists differ")
        groups = re.findall(r'\([^)]*\)', src_binders)
        g0 = re.fullmatch(r'\(\s*([A-Za-z_]\w*)\s*:\s*Nat\s*\)', groups[0].strip())
        if not g0:
            raise Unsupported(f"first binder {groups[0]!r} is not (WV : Nat)")
        wv = g0.group(1)
        if wv != wv_s:
            raise Unsupported(f"binder width {wv!r} != llvm({wv_s!r})")
        extras = [g.strip() for g in groups[1:]]
        extra_names = [check_extra_binder(g, wv) for g in extras]
        return (src_name, tgt_name, wv, extra_names, " ".join(extras),
                src_body, tgt_body, m_src.group(0), m_tgt.group(0))


    def extract_defs_fw(text):
        ms = list(FW_DEF_RE.finditer(text))
        if len(ms) != 2:
            raise Unsupported(f"expected exactly 2 binder-less [llvm()| defs, found {len(ms)}")
        (m_src, m_tgt) = ms
        src_name, src_body = m_src.groups()
        tgt_name, tgt_body = m_tgt.groups()
        if 'src' not in src_name:
            raise Unsupported(f"first def {src_name!r} has no 'src' in name")
        if re.sub('src', 'tgt', src_name) != tgt_name:
            raise Unsupported(f"def names do not pair: {src_name!r} vs {tgt_name!r}")
        return (src_name, tgt_name, src_body, tgt_body, m_src.group(0), m_tgt.group(0))

    def fw_main_width(body):
        m = re.search(r'llvm\.func\s+@\S+\(([^)]*)\)\s*->\s*(\S+)\s*\{', body)
        if not m: raise Unsupported("no func header")
        widths = set()
        for a in m.group(1).split(','):
            a = a.strip()
            if not a: continue
            am = re.fullmatch(r'%(\S+)\s*:\s*(\S+)', a)
            if not am: raise Unsupported(f"arg {a!r}")
            tm = re.fullmatch(r'i(\d+)', am.group(2))
            if not (tm and int(tm.group(1)) > 0):
                raise Unsupported(f"type {am.group(2)!r} (fixed-width dialect requires literal iK)")
            widths.add(tm.group(1))
        rm = re.fullmatch(r'i(\d+)', m.group(2))
        if not (rm and int(rm.group(1)) > 0):
            raise Unsupported(f"return type {m.group(2)!r} (fixed-width dialect requires literal iK)")
        widths.add(rm.group(1))
        ws = sorted(widths - {'1'}, key=int)
        if not ws:
            raise Unsupported("all-i1 fixed-width interface (no gate witness)")
        if rm.group(1) != '1':
            return rm.group(1)
        return ws[-1]

    def _fw_def_widths(d):
        if d[0]=='const':  return (d[2],)
        if d[0]=='bin':    return (d[4],)
        if d[0]=='shift':  return (d[3],)
        if d[0]=='select': return (d[2],)
        if d[0]=='cast':   return (d[3], d[4])
        if d[0]=='ispow2': return (d[2],)
        if d[0]=='ctop':   return (d[3],)
        if d[0]=='div':    return (d[3],)
        return ()

    def fw_val_width(v, defs, argw):
        if v in argw: return argw[v]
        d = defs.get(v)
        if d is None: return None
        if d[0]=='const':  return d[2]
        if d[0]=='icmp':   return '1'
        if d[0]=='ispow2': return '1'
        if d[0]=='bin':    return d[4]
        if d[0]=='shift':  return d[3]
        if d[0]=='select': return d[2]
        if d[0]=='cast':   return d[3]
        if d[0]=='ctop':   return d[3]
        if d[0]=='div':    return d[3]
        return None

    def check_fw_widths(defs, argw, W):
        def wd(v): return fw_val_width(v, defs, argw)
        def req(o, w, vv):
            ow = wd(o)
            if ow is not None and ow != w:
                raise Unsupported(f"fixed-width type mismatch: %{o} is i{ow} but "
                                  f"%{vv} expects i{w} (malformed input; no row)")
        for vv, d in defs.items():
            if d[0]=='bin':
                for o in d[2]: req(o, d[4], vv)
            elif d[0]=='shift':
                for o in d[2]: req(o, d[3], vv)
            elif d[0]=='div':
                for o in d[2]: req(o, d[3], vv)
            elif d[0]=='ctop':
                for o in d[2]: req(o, d[3], vv)
            elif d[0]=='icmp':
                wa, wb = wd(d[2][0]), wd(d[2][1])
                if wa is not None and wb is not None and wa != wb:
                    raise Unsupported(f"fixed-width type mismatch: icmp %{vv} compares "
                                      f"i{wa} with i{wb} (malformed input; no row)")
            elif d[0]=='select':
                req(d[1][0], '1', vv)
                req(d[1][1], d[2], vv); req(d[1][2], d[2], vv)
            elif d[0]=='cast':
                _, op, operand, dstw, srcw = d
                req(operand, srcw, vv)
                if op in ('zext','sext') and int(dstw) <= int(srcw):
                    raise Unsupported(f"llvm.{op} non-widening cast i{srcw} to i{dstw} "
                                      "(malformed input; no row)")
                if op=='trunc' and int(dstw) >= int(srcw):
                    raise Unsupported(f"llvm.trunc non-narrowing cast i{srcw} to i{dstw} "
                                      "(malformed input; no row)")
            elif d[0]=='ispow2':
                req(d[1], d[2], vv)


    def parse_type(t, wv='w'):
        t=t.strip()
        if wv.isdigit():


            m=re.fullmatch(r'i(\d+)',t)
            if m and int(m.group(1))>0: return m.group(1)
            raise Unsupported(f"type {t!r} (fixed-width dialect requires literal iK)")
        if t=='_': return wv
        if t=='i1': return '1'
        m=re.fullmatch(r'i(\d+)',t)
        if m: return m.group(1)
        if t==wv: return wv
        raise Unsupported(f"width token {t!r}")

    def const_bv(n, w='w'):
        if w.isdigit() and (n < 0 or n >= 2**int(w)):


            return f"{n % (2**int(w))}#{w}"
        if n==0: return f"0#{w}"
        if n==-1: return f"(BitVec.ofInt {w} (-1))"
        if n>=1: return f"{n}#{w}"
        raise Unsupported(f"constant {n}")

    def parse_op(op, rest, wv='w'):
        fwmode = wv.isdigit()
        typ = wv
        tm = re.search(r':\s*(\S+)\s*$', rest)
        if tm:


            typ = parse_type(tm.group(1), wv)
        elif fwmode and op not in ('zext', 'sext', 'trunc', 'icmp', 'mlir.constant'):


            raise Unsupported(f"llvm.{op} without result-type annotation "
                              f"(fixed-width dialect requires it): {rest!r}")
        if op == 'mlir.constant':
            b=re.search(r'\(\s*(true|false)\s*\)', rest)
            if b: return ('const', 1 if b.group(1)=='true' else 0, '1')
            if fwmode:


                fcm=re.search(r'\(\s*(-?\d+)\s*:\s*(\S+?)\s*\)\s*:\s*(\S+)', rest)
                if not fcm:
                    raise Unsupported(f"constant {rest!r} (fixed-width requires (N : iK) : iK)")
                inner=parse_type(fcm.group(2), wv)
                outer=parse_type(fcm.group(3), wv)
                if inner != outer:
                    raise Unsupported(f"constant width mismatch {rest!r}")
                return ('const', int(fcm.group(1)), outer)

            wm=re.search(r'\(\s*'+re.escape(wv)+r'\s*:\s*\S+?\s*\)', rest)
            if wm and not wv.isdigit():
                return ('wconst', typ)


            m=re.match(r'\(\s*(-?\d+)', rest.strip())
            if not m: raise Unsupported(f"const {rest!r}")
            return ('const', int(m.group(1)), typ)
        if op == 'icmp':
            assert_no_modifier(op, rest)
            pm=re.match(r'"(\w+)"\s+%(\w+)\s*,\s*%(\w+)', rest)
            if not pm: raise Unsupported(f"icmp {rest!r}")
            if pm.group(1) not in ICMP: raise Unsupported(f"pred {pm.group(1)}")
            return ('icmp', pm.group(1), [pm.group(2), pm.group(3)], '1')
        if op in BVOP:


            mflag, _mbody = parse_binop_modifier(op, rest)
            flag='none'
            if mflag=='disjoint': flag='disjoint'
            elif mflag=='both':   flag='nswnuw'
            elif mflag in ('nsw','nuw'): flag=mflag
            ops=re.findall(r'%(\w+)', rest)
            return ('bin', op, ops[:2], flag, typ)
        if op in SHIFTOP:


            mflag, _mbody = parse_binop_modifier(op, rest)
            if mflag=='exact': raise Unsupported(f"llvm.{op} exact")
            flag='none'
            if mflag!='none':


                if mflag=='both':
                    raise Unsupported("llvm.shl nsw+nuw combined flag (no gate witness)")
                flag=mflag
            ops=re.findall(r'%(\w+)', rest)
            if len(ops)<2: raise Unsupported(f"llvm.{op} operands {rest!r}")
            return ('shift', op, ops[:2], typ, flag)
        if op == 'select':
            assert_no_modifier(op, rest)
            ops=re.findall(r'%(\w+)', rest)
            return ('select', ops[:3], typ)
        if op in ('zext','sext'):
            if re.search(r'\bnneg\b|\bnonNeg\b|overflow', rest):
                raise Unsupported(f"llvm.{op} with flag")
            cm=re.match(r'%(\w+)\s*:\s*(\S+)\s+to\s+(\S+)\s*$', rest.strip())
            if not cm: raise Unsupported(f"cast form {rest!r}")
            srcw=parse_type(cm.group(2), wv); dstw=parse_type(cm.group(3), wv)
            return ('cast', op, cm.group(1), dstw, srcw)
        if op == 'trunc':
            if re.search(r'\bnneg\b|\bnonNeg\b|overflow|\bnsw\b|\bnuw\b', rest):
                raise Unsupported("llvm.trunc with flag (no row)")
            cm=re.match(r'%(\w+)\s*:\s*(\S+)\s+to\s+(\S+)\s*$', rest.strip())
            if not cm: raise Unsupported(f"cast form {rest!r}")
            srcw=parse_type(cm.group(2), wv); dstw=parse_type(cm.group(3), wv)
            if dstw!='1':
                raise Unsupported("llvm.trunc to non-i1 width (only the "
                                  "trunc-to-i1 select-condition normal form "
                                  "BitVec.setWidth 1 is supported)")
            return ('cast', 'trunc', cm.group(1), dstw, srcw)
        if op == 'isPowerOf2':
            assert_no_modifier(op, rest)
            ops=re.findall(r'%(\w+)', rest)
            if not ops: raise Unsupported(f"isPowerOf2 {rest!r}")
            return ('ispow2', ops[0], typ)
        if op in ('cttz','ctlz','ctpop'):


            assert_no_modifier(op, rest)
            ops=re.findall(r'%(\w+)', rest)
            if len(ops)!=1: raise Unsupported(f"llvm.{op} operand form {rest!r}")
            if op in ('cttz','ctlz'):
                fm=re.match(r'%\w+\s*,\s*(true|false)\b', rest.strip())
                if not fm: raise Unsupported(f"llvm.{op} flag form {rest!r}")
                if fm.group(1)=='true':
                    raise Unsupported(f"llvm.{op} is_zero_poison=true (the zero-input "
                                      "poison arm needs a value-level poison row; no gate witness)")
            return ('ctop', op, ops, typ)
        if op in ('sdiv','udiv'):


            mflag, _mbody = parse_binop_modifier(op, rest)
            ex = mflag=='exact'
            ops=re.findall(r'%(\w+)', rest)
            return ('div', op, ops[:2], typ, ex)
        if op in ('urem','srem'):


            parse_binop_modifier(op, rest)
            ops=re.findall(r'%(\w+)', rest)
            return ('div', op, ops[:2], typ, False)
        raise Unsupported(f"opcode llvm.{op}")

    def parse_prog(text, wv='w'):
        m=re.search(r'llvm\.func\s+@\S+\(([^)]*)\)\s*->\s*(\S+)\s*\{', text)
        if not m: raise Unsupported("no func header")
        rett=parse_type(m.group(2), wv)
        args=[]
        for a in m.group(1).split(','):
            a=a.strip()
            if not a: continue
            am=re.fullmatch(r'%(\S+)\s*:\s*(\S+)', a)
            if not am: raise Unsupported(f"arg {a!r}")
            args.append((am.group(1), parse_type(am.group(2), wv)))
        blocks=re.findall(r'\^(\w+)\([^)]*\):', text)
        if len(blocks)!=1: raise Unsupported(f"{len(blocks)} basic blocks (expect 1)")
        body=text[re.search(r'\^\w+\([^)]*\):', text).end():]
        defs={}; retvar=None; assumes=[]; order=[]
        for line in body.splitlines():
            line=line.strip().rstrip('}').strip()
            if not line: continue
            if line.startswith('--'): continue
            rm=re.match(r'llvm\.return\s+%(\w+)', line)
            if rm: retvar=rm.group(1); continue
            am=re.match(r'llvm\.assume\s+%(\w+)', line)
            if am:
                assumes.append(am.group(1)); order.append(('assume', am.group(1)))
                continue
            om=re.match(r'%(\w+)\s*=\s*llvm\.([a-zA-Z][A-Za-z0-9._]*)\s*(.*)', line)
            if not om:
                if line.startswith('llvm.') or line.startswith('%'): raise Unsupported(f"op line {line!r}")
                continue
            defs[om.group(1)]=parse_op(om.group(2), om.group(3), wv)
            order.append(('op', om.group(1)))
        if retvar is None: raise Unsupported("no return")
        if not (1 <= len(assumes)):

            pass
        return args, defs, retvar, assumes, rett, order


    class PCtx:
        def __init__(self, defs, argw, ren, wv='w'):
            self.defs=defs; self.argw=argw; self.ren=ren; self.wv=wv
            self.resolved={}
            self.i1sym=False

    def is_zero_const(v, ctx):
        d=ctx.defs.get(v)
        return d is not None and d[0]=='const' and d[1]==0

    def neg_form(v, ctx):
        d=ctx.defs.get(v)
        if d is not None and d[0]=='bin' and d[1]=='sub' and is_zero_const(d[2][0], ctx):
            return d[2][1]
        return None

    def is_i1typed(v, ctx):
        d=ctx.defs.get(v)
        if d is None:
            return ctx.argw.get(v)=='1'
        if d[0]=='icmp': return True
        if d[0]=='ispow2': return True
        if d[0]=='const': return len(d)>2 and d[2]=='1'
        if d[0]=='bin' and d[1] in BOOLOP and d[4]=='1': return True
        if d[0]=='select' and d[2]=='1': return True
        if d[0]=='cast' and d[1]=='trunc' and d[3]=='1': return True
        return False

    def is_boolprintable(v, ctx):
        d=ctx.defs.get(v)
        if d is None: return False
        if d[0]=='icmp': return True
        if d[0]=='ispow2': return True
        if d[0]=='bin' and d[1] in BOOLOP and d[4]=='1':
            return all(is_boolprintable(o, ctx) for o in d[2])
        return False

    def is_bv1printable(v, ctx):
        if is_boolprintable(v, ctx): return True
        if v in ctx.argw: return ctx.argw[v]=='1'
        d=ctx.defs.get(v)
        if d is None: return False
        if d[0]=='const': return len(d)>2 and d[2]=='1'
        if d[0]=='bin' and d[1] in BOOLOP and d[4]=='1':
            return all(is_bv1printable(o, ctx) for o in d[2])
        if d[0]=='cast' and d[1]=='trunc' and d[3]=='1': return True
        if d[0]=='select' and d[2]=='1':
            return all(is_bv1printable(o, ctx) for o in d[1])
        return False

    def bv1_expr(v, ctx, stmt=False):
        if is_boolprintable(v, ctx):
            return f"(BitVec.ofBool {bool_expr(v,ctx,stmt)})"
        if v in ctx.argw:
            if ctx.argw[v]!='1': raise Unsupported(f"bv1 print of non-i1 arg %{v}")
            return ctx.ren.get(v, v)
        d=ctx.defs.get(v)
        if d is None: raise Unsupported(f"unknown %{v}")
        if d[0]=='const' and len(d)>2 and d[2]=='1':
            return const_bv(d[1], '1')
        if d[0]=='bin' and d[1] in BOOLOP and d[4]=='1':
            return f"({bv1_expr(d[2][0],ctx,stmt)} {BVOP[d[1]]} {bv1_expr(d[2][1],ctx,stmt)})"
        if d[0]=='cast' and d[1]=='trunc' and d[3]=='1':
            return f"(BitVec.setWidth 1 {bv_expr(d[2],ctx,stmt)})"
        if d[0]=='select' and d[2]=='1':
            c,a,b=d[1]
            return (f"(if {selcond_prop(c,ctx,stmt)} then "
                    f"{bv1_expr(a,ctx,stmt)} else {bv1_expr(b,ctx,stmt)})")
        raise Unsupported(f"bv1_expr of {d}")

    def bool_prop(c, ctx, stmt=False):
        d=ctx.defs.get(c)
        if d is not None and d[0]=='bin' \
           and d[1] in ('and','or') and d[4]=='1':
            A=bool_prop(d[2][0],ctx,stmt); B=bool_prop(d[2][1],ctx,stmt)
            return f"({A} ∨ {B})" if d[1]=='or' else f"({A} ∧ {B})"
        return f"{bool_expr(c,ctx,stmt)} = true"

    def selcond_prop(c, ctx, stmt=False):
        d=ctx.defs.get(c)
        if d is not None and d[0]=='icmp' and stmt and d[1] in ('eq','ne') \
           and not any(is_i1typed(o, ctx) for o in d[2]):
            ca=bv_expr(d[2][0],ctx,stmt); cb=bv_expr(d[2][1],ctx,stmt)
            return f"{ca} = {cb}" if d[1]=='eq' else f"¬({ca} = {cb})"
        try:
            return bool_prop(c,ctx,stmt)
        except Unsupported:
            return f"{bv1_expr(c,ctx,stmt)} = 1#1"

    def fw_ground_val(v, ctx):
        if not ctx.wv.isdigit(): return None
        if v in ctx.argw: return None
        d=ctx.defs.get(v)
        if d is None: return None
        if d[0]=='const':
            w=d[2] if len(d)>2 else ctx.wv
            return (d[1] % (2**int(w)), w)
        if d[0]=='bin' and d[3]=='none' and d[1] in BVOP and d[4]!='1':
            a=fw_ground_val(d[2][0],ctx); b=fw_ground_val(d[2][1],ctx)
            if a is None or b is None: return None
            (av,aw),(bv,bw)=a,b
            if aw!=bw or aw!=d[4]: return None
            M=2**int(aw)
            val={'add':av+bv,'sub':av-bv,'mul':av*bv,
                 'and':av&bv,'or':av|bv,'xor':av^bv}[d[1]] % M
            return (val, aw)
        return None

    def fw_ground_bool(v, ctx):
        if not ctx.wv.isdigit(): return None
        d=ctx.defs.get(v)
        if d is None or d[0]!='icmp' or any(is_i1typed(o,ctx) for o in d[2]):
            return None
        a=fw_ground_val(d[2][0],ctx); b=fw_ground_val(d[2][1],ctx)
        if a is None or b is None or a[1]!=b[1]: return None
        (av,aw),(bv,_)=a,b
        M=2**int(aw)
        sa=av-M if av>=M//2 else av
        sb=bv-M if bv>=M//2 else bv
        return {'eq':av==bv,'ne':av!=bv,
                'ult':av<bv,'ule':av<=bv,'ugt':av>bv,'uge':av>=bv,
                'slt':sa<sb,'sle':sa<=sb,'sgt':sa>sb,'sge':sa>=sb}[d[1]]

    def shift_amt_nat(v, ctx, stmt=False):
        w=ctx.wv
        if ctx.wv.isdigit():
            w=fw_val_width(v, ctx.defs, ctx.argw) or ctx.wv
        if v in ctx.argw:
            if ctx.argw[v]!=w: raise Unsupported("non-width-typed shift amount")
            return f"{ctx.ren.get(v,v)}.toNat"
        d=ctx.defs.get(v)
        if d is None: raise Unsupported(f"unknown shift amount %{v}")
        if d[0]=='const':
            if w.isdigit():


                if len(d)>2 and d[2] not in (w, '1'):
                    raise Unsupported(f"shift amount constant at width i{d[2]} (mixed width)")
                return str(d[1] % (2**int(w)))


            return f"({d[1]} % 2 ^ {w} : Nat)"
        if d[0]=='bin' and d[1]=='sub':
            a,b=d[2]
            da=ctx.defs.get(a); db=ctx.defs.get(b)
            if da is not None and da[0]=='wconst' and db is not None \
               and db[0]=='const' and db[1]>=1:
                return f"((2 ^ {w} - {db[1]} % 2 ^ {w} + {w}) % 2 ^ {w})"
        raise Unsupported("composite shift amount (unstable .toNat normal form)")

    def bv_expr(v, ctx, stmt=False):
        if v in ctx.argw:


            if ctx.argw[v] not in (ctx.wv, '1') and not ctx.wv.isdigit():
                raise Unsupported(f"fixed-width arg %{v} in bv position")
            return ctx.ren.get(v, v)
        d=ctx.defs.get(v)
        if d is None: raise Unsupported(f"unknown %{v}")
        if d[0]=='const': return const_bv(d[1], d[2] if len(d)>2 else ctx.wv)
        if d[0]=='wconst':
            return f"(BitVec.ofNat {ctx.wv} {ctx.wv})"
        if d[0]=='bin':
            _,op,ops,flag,typ=d
            gv=fw_ground_val(v, ctx)
            if gv is not None:
                return const_bv(gv[0], gv[1])
            if op=='sub' and ctx.wv.isdigit():


                pa=bv_expr(ops[0],ctx,stmt); pb=bv_expr(ops[1],ctx,stmt)
                if pa==pb:
                    return f"0#{typ}"
            if op=='sub':
                if is_zero_const(ops[0], ctx):
                    return f"-{bv_expr(ops[1],ctx,stmt)}"
                nf=neg_form(ops[1], ctx)
                if nf is not None:
                    return f"({bv_expr(ops[0],ctx,stmt)} + {bv_expr(nf,ctx,stmt)})"
            return f"({bv_expr(ops[0],ctx,stmt)} {BVOP[op]} {bv_expr(ops[1],ctx,stmt)})"
        if d[0]=='shift':
            op,ops,typ=d[1],d[2],d[3]
            a=bv_expr(ops[0],ctx,stmt); amt=shift_amt_nat(ops[1],ctx,stmt)
            if a.startswith('-'):


                a=f"({a})"
            if op=='shl':  return f"({a} <<< {amt})"
            if op=='lshr': return f"({a} >>> {amt})"
            return f"({dot_recv(a)}.sshiftRight {amt})"
        if d[0]=='cast':
            _,op,operand,dstw,srcw=d
            if op=='trunc':
                if dstw!='1': raise Unsupported("llvm.trunc to non-i1 width (no row)")
                return f"(BitVec.setWidth 1 {bv_expr(operand,ctx,stmt)})"


            if dstw != ctx.wv and not (ctx.wv.isdigit() and dstw.isdigit() and dstw != '1'):
                raise Unsupported(f"llvm.{op} to fixed width i{dstw}")
            if ctx.wv.isdigit() and fw_ground_val(operand, ctx) is not None:


                raise Unsupported(f"llvm.{op} of a ground constant at fixed width "
                                  "(simproc fold not modelled; no gate witness)")
            fn = "BitVec.signExtend" if op=='sext' else "BitVec.setWidth"


            od=ctx.defs.get(operand)
            if od is not None and od[0]=='bin' and od[1] in BOOLOP and od[4]=='1':
                a=bv_expr(od[2][0],ctx,stmt); b=bv_expr(od[2][1],ctx,stmt)
                return f"(({fn} {dstw} {a}) {BVOP[od[1]]} ({fn} {dstw} {b}))"
            inner=bv_expr(operand,ctx,stmt)
            return f"({fn} {dstw} {inner})"
        if d[0]=='icmp':
            return f"(BitVec.ofBool {bool_expr(v,ctx,stmt)})"
        if d[0]=='ispow2':
            return f"(BitVec.ofBool {bool_expr(v,ctx,stmt)})"
        if d[0]=='select':
            c,a,b=d[1]
            if v in ctx.resolved:
                return bv_expr(ctx.resolved[v], ctx, stmt)
            cd=ctx.defs.get(c)
            if cd is None and ctx.argw.get(c)=='1' and ctx.i1sym:


                return (f"(if {ctx.ren.get(c,c)} = 1#1 then "
                        f"{bv_expr(a,ctx,stmt)} else {bv_expr(b,ctx,stmt)})")
            if cd is not None and cd[0]=='icmp' and stmt and cd[1] in ('eq','ne'):

                ca=bv_expr(cd[2][0],ctx,stmt); cb=bv_expr(cd[2][1],ctx,stmt)
                cond = f"{ca} = {cb}" if cd[1]=='eq' else f"¬({ca} = {cb})"
                return f"(if {cond} then {bv_expr(a,ctx,stmt)} else {bv_expr(b,ctx,stmt)})"
            try:
                return (f"(if {bool_prop(c,ctx,stmt)} then "
                        f"{bv_expr(a,ctx,stmt)} else {bv_expr(b,ctx,stmt)})")
            except Unsupported:


                return (f"(if {bv1_expr(c,ctx,stmt)} = 1#1 then "
                        f"{bv_expr(a,ctx,stmt)} else {bv_expr(b,ctx,stmt)})")
        if d[0]=='div':
            op,ops=d[1],d[2]
            a=bv_expr(ops[0],ctx,stmt); b=bv_expr(ops[1],ctx,stmt)
            if op=='sdiv': return f"({dot_recv(a)}.sdiv {b})"
            if op=='udiv': return f"({a} / {b})"
            if op=='urem': return f"({a} % {b})"
            return f"({dot_recv(a)}.srem {b})"
        if d[0]=='ctop':


            _,op,ops,typ=d
            if typ!=ctx.wv:
                raise Unsupported(f"llvm.{op} at fixed width i{typ} (no row)")
            fn={'ctpop':'LLVM.popCountNatRec',
                'cttz':'LLVM.countTrailingZerosNatRec',
                'ctlz':'LLVM.countLeadingZerosNatRec'}[op]
            return f"(BitVec.ofNat {ctx.wv} ({fn} {bv_expr(ops[0],ctx,stmt)} {ctx.wv} 0))"
        raise Unsupported(f"bv_expr of {d}")

    def bool_expr(v, ctx, stmt=False):
        d=ctx.defs.get(v)
        if d is None:
            raise Unsupported(f"raw i1 arg %{v} in bool position (needs F7)")
        if d[0]=='icmp':
            _,p,ops,_=d
            if any(is_i1typed(o, ctx) for o in ops):
                if not all(is_i1typed(o, ctx) for o in ops):
                    raise Unsupported("icmp mixing bool and bv operands")
                if p not in ('eq','ne'):
                    raise Unsupported(f"icmp {p} over i1 operands")
                if all(is_boolprintable(o, ctx) for o in ops):


                    def _pr1(o):
                        g=fw_ground_bool(o, ctx)
                        if g is not None: return ('1#1' if g else '0#1')
                        return f"BitVec.ofBool {bool_expr(o,ctx,stmt)}"
                    A=_pr1(ops[0]); B=_pr1(ops[1])
                    sym = '==' if p=='eq' else '!='
                    return f"({A} {sym} {B})"
                A=bv_expr(ops[0],ctx,stmt); B=bv_expr(ops[1],ctx,stmt)
                sym = '==' if p=='eq' else '!='
                return f"({A} {sym} {B})"
            return ICMP_NORM[p](bv_expr(ops[0],ctx,stmt), bv_expr(ops[1],ctx,stmt))
        if d[0]=='ispow2':
            a=bv_expr(d[1],ctx,stmt); w=ctx.wv
            return f"((({a} &&& ({a} - 1#{w})) == 0#{w}) && ({a} != 0#{w}))"
        if d[0]=='bin' and d[1] in BOOLOP and d[4]=='1':
            return f"({bool_expr(d[2][0],ctx,stmt)} {BOOLOP[d[1]]} {bool_expr(d[2][1],ctx,stmt)})"
        raise Unsupported(f"bool_expr of {d}")

    def prop_pred(v, ctx):
        d=ctx.defs.get(v)
        if d is not None and d[0]=='icmp' and not any(is_i1typed(o,ctx) for o in d[2]):
            a=bv_expr(d[2][0],ctx,True); b=bv_expr(d[2][1],ctx,True)
            if d[1]=='eq': return f"{a} = {b}"
            if d[1]=='ne': return f"¬({a} = {b})"
        return None


    def args_in(v, defs, argw, acc):
        if v in argw:
            if v not in acc: acc.append(v)
            return
        d=defs.get(v)
        if d is None: return
        if d[0] in ('const','wconst'): return
        if d[0] in ('bin','icmp','shift','div','ctop'):
            for o in d[2]: args_in(o, defs, argw, acc)
        if d[0]=='cast': args_in(d[2], defs, argw, acc)
        if d[0]=='ispow2': args_in(d[1], defs, argw, acc)
        if d[0]=='select':
            for o in d[1]: args_in(o, defs, argw, acc)

    def flagged_ops(v, defs, argw, acc, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add(v)
        if d[0]=='bin':
            for o in d[2]: flagged_ops(o, defs, argw, acc, seen)
            if d[3] in ('nsw','nuw','nswnuw'):
                if d[1] not in ('add','sub','mul'): raise Unsupported(f"flagged {d[1]}")
                if v not in [x[0] for x in acc]:
                    acc.append((v, d[1], d[3], d[2]))
        elif d[0] in ('icmp','shift','div','ctop'):
            for o in d[2]: flagged_ops(o, defs, argw, acc, seen)
        elif d[0]=='cast':
            flagged_ops(d[2], defs, argw, acc, seen)
        elif d[0]=='ispow2':
            flagged_ops(d[1], defs, argw, acc, seen)
        elif d[0]=='select':
            for o in d[1]: flagged_ops(o, defs, argw, acc, seen)

    def shl_flags(v, defs, argw, acc, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add(v)
        if d[0]=='shift':
            for o in d[2]: shl_flags(o, defs, argw, acc, seen)
            if len(d)>4 and d[4] in ('nsw','nuw'):
                if v not in [x[0] for x in acc]:
                    acc.append((v, d[4], d[2]))
        elif d[0] in ('bin','icmp','div','ctop'):
            for o in d[2]: shl_flags(o, defs, argw, acc, seen)
        elif d[0]=='cast':
            shl_flags(d[2], defs, argw, acc, seen)
        elif d[0]=='ispow2':
            shl_flags(d[1], defs, argw, acc, seen)
        elif d[0]=='select':
            for o in d[1]: shl_flags(o, defs, argw, acc, seen)

    def dot_recv(s):
        return f"({s})" if s and s[0].isdigit() else s

    def shl_noovf_eq(vv, ctx, stmt=False):
        d=ctx.defs[vv]
        x=bv_expr(d[2][0], ctx, stmt)
        amt=shift_amt_nat(d[2][1], ctx, stmt)
        if d[4]=='nuw':
            return f"({x} <<< {amt}) >>> {amt} = {x}"
        return f"({x} <<< {amt}).sshiftRight {amt} = {x}"

    def disjoint_ors(v, defs, argw, acc, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add(v)
        if d[0]=='bin':
            if d[1]=='or' and d[3]=='disjoint' and v not in [x[0] for x in acc]:
                acc.append((v, d[2]))
            for o in d[2]: disjoint_ors(o, defs, argw, acc, seen)
        elif d[0] in ('icmp','shift','div','ctop'):
            for o in d[2]: disjoint_ors(o, defs, argw, acc, seen)
        elif d[0]=='cast':
            disjoint_ors(d[2], defs, argw, acc, seen)
        elif d[0]=='ispow2':
            disjoint_ors(d[1], defs, argw, acc, seen)
        elif d[0]=='select':
            for o in d[1]: disjoint_ors(o, defs, argw, acc, seen)

    def find_selects(v, defs, argw, acc, depth=0):
        if v in argw: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        if d[0]=='select':
            c,a,b=d[1]
            if depth >= 3: raise Unsupported("select nesting depth >3")
            if v not in [x[0] for x in acc]:
                acc.append((v, c, a, b, depth))
            find_selects(c, defs, argw, acc, depth)
            find_selects(a, defs, argw, acc, depth+1)
            find_selects(b, defs, argw, acc, depth+1)
            return
        if d[0]=='cast':
            find_selects(d[2], defs, argw, acc, depth); return
        if d[0]=='ispow2':
            find_selects(d[1], defs, argw, acc, depth); return
        for o in (d[2] if d[0] in ('bin','icmp','shift','div','ctop') else []):
            find_selects(o, defs, argw, acc, depth)

    def shift_amounts(v, defs, argw, acc, strict=True, seen=None):
        if seen is None: seen=set()
        if v in argw or (v, strict) in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add((v, strict))
        if d[0]=='shift':
            acc[d[2][1]] = acc.get(d[2][1], False) or strict
            for o in d[2]: shift_amounts(o, defs, argw, acc, strict, seen)
        elif d[0] in ('bin','icmp','div','ctop'):
            for o in d[2]: shift_amounts(o, defs, argw, acc, strict, seen)
        elif d[0]=='cast':
            shift_amounts(d[2], defs, argw, acc, strict, seen)
        elif d[0]=='ispow2':
            shift_amounts(d[1], defs, argw, acc, strict, seen)
        elif d[0]=='select':
            shift_amounts(d[1][0], defs, argw, acc, strict, seen)
            shift_amounts(d[1][1], defs, argw, acc, False, seen)
            shift_amounts(d[1][2], defs, argw, acc, False, seen)

    def strict_poison(v, defs, argw, acc, strict=True, seen=None):
        if seen is None: seen=set()
        if v in argw or (v, strict) in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add((v, strict))
        acc[v]=acc.get(v, False) or strict
        if d[0]=='select':
            strict_poison(d[1][0], defs, argw, acc, strict, seen)
            strict_poison(d[1][1], defs, argw, acc, False, seen)
            strict_poison(d[1][2], defs, argw, acc, False, seen)
        elif d[0]=='cast':
            strict_poison(d[2], defs, argw, acc, strict, seen)
        elif d[0]=='ispow2':
            strict_poison(d[1], defs, argw, acc, strict, seen)
        else:
            for o in d[2]: strict_poison(o, defs, argw, acc, strict, seen)

    def arg_strict(v, defs, argw, acc, strict=True, seen=None):
        if seen is None: seen=set()
        if v in argw:
            acc[v]=acc.get(v, False) or strict; return
        if (v, strict) in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add((v, strict))
        if d[0]=='select':
            arg_strict(d[1][0], defs, argw, acc, strict, seen)
            arg_strict(d[1][1], defs, argw, acc, False, seen)
            arg_strict(d[1][2], defs, argw, acc, False, seen)
        elif d[0]=='cast':
            arg_strict(d[2], defs, argw, acc, strict, seen)
        elif d[0]=='ispow2':
            arg_strict(d[1], defs, argw, acc, strict, seen)
        else:
            for o in d[2]: arg_strict(o, defs, argw, acc, strict, seen)

    def sels_in(v, defs, argw, acc, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add(v)
        if d[0]=='select':
            if v not in acc: acc.append(v)
            for o in d[1]: sels_in(o, defs, argw, acc, seen)
        elif d[0]=='cast': sels_in(d[2], defs, argw, acc, seen)
        elif d[0]=='ispow2': sels_in(d[1], defs, argw, acc, seen)
        else:
            for o in d[2]: sels_in(o, defs, argw, acc, seen)

    def ofint_arith_operand(v, defs, argw, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return False
        d=defs.get(v)
        if not d: return False
        seen.add(v)
        if d[0] in ('bin','shift','div'):
            for o in d[2]:
                od=defs.get(o)
                if od is not None and od[0]=='const' and od[1]==-1: return True
            return any(ofint_arith_operand(o, defs, argw, seen) for o in d[2])
        if d[0] in ('icmp','ctop'):
            return any(ofint_arith_operand(o, defs, argw, seen) for o in d[2])
        if d[0]=='cast': return ofint_arith_operand(d[2], defs, argw, seen)
        if d[0]=='ispow2': return ofint_arith_operand(d[1], defs, argw, seen)
        if d[0]=='select':
            return any(ofint_arith_operand(o, defs, argw, seen) for o in d[1])
        return False

    def div_ops(v, defs, argw, acc, seen=None):
        if seen is None: seen=set()
        if v in argw or v in seen: return
        d=defs.get(v)
        if not d or d[0] in ('const','wconst'): return
        seen.add(v)
        if d[0]=='div':
            if v not in [x[0] for x in acc]: acc.append((v, d[1], d[2]))
            for o in d[2]: div_ops(o, defs, argw, acc, seen)
        elif d[0] in ('bin','icmp','shift','ctop'):
            for o in d[2]: div_ops(o, defs, argw, acc, seen)
        elif d[0]=='cast': div_ops(d[2], defs, argw, acc, seen)
        elif d[0]=='ispow2': div_ops(d[1], defs, argw, acc, seen)
        elif d[0]=='select':
            for o in d[1]: div_ops(o, defs, argw, acc, seen)

    def collect_opcodes(defs):
        ops=set()
        for d in defs.values():
            if d[0] in ('const','wconst'): ops.add('const')
            elif d[0]=='icmp': ops.add('icmp')
            elif d[0]=='bin': ops.add(d[1])
            elif d[0]=='shift': ops.add(d[1])
            elif d[0]=='cast': ops.add(d[1])
            elif d[0]=='ispow2': ops.add('ispow2')
            elif d[0]=='ctop': ops.add(d[1])
            elif d[0]=='div': ops.add(d[1] + ('x' if d[4] else ''))
            elif d[0]=='select': ops.add('select')
        return ops


    def simp_line(names, indent, vars_so_far, hyps_so_far, opcodes):
        core=list(names) + ["Expr.denote_unfold", "Expr.denoteOp",
              "DialectDenote.denote", "InstCombine.Op.denoteVec", "InstCombine.Op.denote",
              "Ctxt.Valuation.cons_eval"] + vars_so_far + hyps_so_far + \
             ["ImmediateUBOr.immediateUB", "ImmediateUBOr.value", "LLVM.const?",
              "LLVM.icmp", "LLVM.icmp?", "LLVM.icmp'"]
        per={'and':["LLVM.and","LLVM.and?"],'or':["LLVM.or","LLVM.or?"],'xor':["LLVM.xor","LLVM.xor?"],
             'add':["LLVM.add","LLVM.add?"],'sub':["LLVM.sub","LLVM.sub?"],'mul':["LLVM.mul","LLVM.mul?"],
             'select':["LLVM.select","InstCombine.lift3"],

             'shl':["LLVM.shl","LLVM.shl?"],'lshr':["LLVM.lshr","LLVM.lshr?"],
             'ashr':["LLVM.ashr","LLVM.ashr?"],

             'sext':["LLVM.sext","LLVM.sext?"],'zext':["LLVM.zext","LLVM.zext?"],
             'trunc':["LLVM.trunc","LLVM.trunc?"],
             'ispow2':["LLVM.isPowerOf2","LLVM.isPowerOf2?"],


             'ctpop':["LLVM.ctpop","LLVM.ctpop?"],
             'cttz':["LLVM.cttz","LLVM.cttz?"],
             'ctlz':["LLVM.ctlz","LLVM.ctlz?"],


             'sdiv':["InstCombine.lift2UB"],
             'udiv':["InstCombine.lift2UB"],
             'sdivx':["InstCombine.lift2UB"],
             'udivx':["InstCombine.lift2UB"],
             'urem':["LLVM.urem","InstCombine.lift2UB"],
             'srem':["LLVM.srem","InstCombine.lift2UB"]}
        _seen_per=set()
        for oc in sorted(opcodes):
            if oc in per:


                core+=[e for e in per[oc] if e not in _seen_per]
                _seen_per.update(per[oc])
        core.append("LLVM.assume_")
        pad=" "*indent
        return f"{pad}simp [{', '.join(core)}]"

    UB="exact ImmediateUBOr.IsRefinedBy.immediateUBLeft"

    def div_ubp(op, a, b, wv):
        if op in ('udiv','urem'):
            return f"{b} = 0#{wv}"
        if wv.isdigit() and int(wv) > 1:
            return (f"{b} = 0#{wv} ∨ ({a} = BitVec.intMin {wv} ∧ "
                    f"{b} = {2**int(wv)-1}#{wv})")
        return (f"{b} = 0#{wv} ∨ (¬ {wv} = 1 ∧ {a} = BitVec.intMin {wv} ∧ "
                f"{b} = BitVec.ofInt {wv} (-1))")


    DIV_COMPANIONS = {
     'urem': ("private theorem {n}_urem_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
              "    LLVM.urem? x y =\n"
              "      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)\n"
              "       else (.value (x % y) : LLVM.IntWUB w)) := rfl\n"),
     'srem': ("private theorem {n}_srem_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
              "    LLVM.srem? x y =\n"
              "      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))\n"
              "       then (.immediateUB : LLVM.IntWUB w)\n"
              "       else (.value (x.srem y) : LLVM.IntWUB w)) := by\n"
              "  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]\n"
              "  simp [LLVM.srem?, hneg]\n"
              "  split_ifs <;> try tauto\n"),
     'sdiv': ("private theorem {n}_sdiv_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
              "    LLVM.sdiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =\n"
              "      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))\n"
              "       then (.immediateUB : LLVM.IntWUB w)\n"
              "       else (.value (x.sdiv y) : LLVM.IntWUB w)) := by\n"
              "  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]\n"
              "  simp [LLVM.sdiv, hneg]\n"
              "  split_ifs <;> simp_all\n"),
     'udiv': ("private theorem {n}_udiv_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
              "    LLVM.udiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) =\n"
              "      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)\n"
              "       else (.value (x / y) : LLVM.IntWUB w)) := by\n"
              "  simp [LLVM.udiv]\n"),


     'udivx': ("private theorem {n}_udivx_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
               "    LLVM.udiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) {{ «exact» := true }} =\n"
               "      (if y = 0#w then (.immediateUB : LLVM.IntWUB w)\n"
               "       else if x % y = 0#w then (.value (x / y) : LLVM.IntWUB w)\n"
               "       else (.poison : LLVM.IntWUB w)) := by\n"
               "  simp [LLVM.udiv]\n"),
     'sdivx': ("private theorem {n}_sdivx_eq_if {{w : Nat}} {{x y : BitVec w}} :\n"
               "    LLVM.sdiv (LLVM.SemVal.value x) (LLVM.SemVal.value y) {{ «exact» := true }} =\n"
               "      (if (y = 0#w) ∨ (¬ w = 1 ∧ x = BitVec.intMin w ∧ y = BitVec.ofInt w (-1))\n"
               "       then (.immediateUB : LLVM.IntWUB w)\n"
               "       else if x.smod y = 0#w then (.value (x.sdiv y) : LLVM.IntWUB w)\n"
               "       else (.poison : LLVM.IntWUB w)) := by\n"
               "  have hneg : BitVec.ofInt w (-1) = -1 := by simp [BitVec.ofInt_neg, BitVec.ofInt_ofNat]\n"
               "  simp [LLVM.sdiv, hneg]\n"
               "  split_ifs <;> simp_all\n"),
    }


    DIV_POISON = ("private theorem {n}_{b}_poisonL {{w : Nat}} (y : LLVM.IntW w) (f : LLVM.ExactFlag) :\n"
                  "    LLVM.{b} (LLVM.SemVal.poison) y f = (.poison : LLVM.IntWUB w) := rfl\n\n"
                  "private theorem {n}_{b}_poisonR {{w : Nat}} (x : LLVM.IntW w) (f : LLVM.ExactFlag) :\n"
                  "    LLVM.{b} x (LLVM.SemVal.poison) f = (.poison : LLVM.IntWUB w) := by\n"
                  "  cases x <;> rfl\n")

    def poison_ret_leaf(indent, style='v1'):
        p=" "*indent
        if style=='r2':


            return (f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                    f"{p}  constructor\n"
                    f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                    f"{p}      first\n"
                    f"{p}      | exact LLVM.SemVal.poison_isRefinedBy _\n"
                    f"{p}      | (rw [LLVM.IntW.isRefinedBy_iff]; exact LLVM.SemVal.poison_isRefinedBy _)\n"
                    f"{p}      | simp [LLVM.IntW.instRefinement])\n"
                    f"{p}  · exact HVector.nil_isRefinedBy_nil)")
        if style=='simp':
            inner=f"exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)"
        else:
            inner=f"exact ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.poison_isRefinedBy _)"
        return (f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                f"{p}  constructor\n"
                f"{p}  · {inner}\n"
                f"{p}  · exact HVector.nil_isRefinedBy_nil)")

    def trivial_value_leaf(indent):
        p=" "*indent
        return (f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                f"{p}  constructor\n"
                f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)\n"
                f"{p}  · exact HVector.nil_isRefinedBy_nil)")


    def emit_text(text, case):


        fw = len(FW_DEF_RE.findall(text)) == 2
        if fw:
            (src_def, tgt_def, src_body, tgt_body,
             src_text, tgt_text) = extract_defs_fw(text)
            wv = fw_main_width(src_body)
            extra_names = []; extra_binders = ""
        else:
            (src_def, tgt_def, wv, extra_names, extra_binders,
             src_body, tgt_body, src_text, tgt_text) = extract_defs(text)
        name = case
        esig = (" " + extra_binders) if extra_binders else ""
        eapp = (" " + " ".join(extra_names)) if extra_names else ""


        wvapp = "" if fw else f" ({wv} := {wv})"

        sargs, sdefs, sret, sasms, srett, sorder = parse_prog(src_body, wv)
        targs, tdefs, tret, tasms, trett, torder = parse_prog(tgt_body, wv)
        if fw:


            check_fw_widths(sdefs, dict(sargs), wv); check_fw_widths(tdefs, dict(targs), wv)
            for a,_ in sargs:
                if not re.fullmatch(r'[A-Za-z_]\w*', a):
                    raise Unsupported(f"SSA arg name %{a} is not a Lean identifier")
        if [t for _,t in sargs] != [t for _,t in targs]: raise Unsupported("arg types differ")
        if srett != trett: raise Unsupported("return types differ")
        if not sasms: raise Unsupported("no assume in src")
        args=sargs; n=len(args)
        argw={a:t for a,t in args}
        for a,t in args:


            if t not in (wv,'1') and not fw:
                raise Unsupported(f"fixed-width arg %{a} : i{t}")


        fwmulti = fw and len({t for _,t in args if t != '1'}
                             | {w for dd in (sdefs, tdefs) for d in dd.values()
                                for w in _fw_def_widths(d) if w != '1'}) > 1
        idx={a: n-1-i for i,(a,_) in enumerate(args)}
        reserved={'V','w',wv}|set(extra_names)
        ren={a:(a+'v' if a in reserved else a) for a,_ in args}
        if wv in [a for a,_ in args]: raise Unsupported(f"width var {wv!r} collides with an SSA arg name")
        sctx=PCtx(sdefs, argw, ren, wv); tctx=PCtx(tdefs, argw, ren, wv)

        multi = len(sasms) > 1
        if len(tasms) not in (0, len(sasms)):
            raise Unsupported(f"src/tgt assume counts differ ({len(sasms)} vs {len(tasms)})")


        i1args=[a for a,t in args if t=='1']
        selcond_i1=[]
        for dd in (sdefs, tdefs):
            for vv,d in dd.items():
                if d[0]=='select' and d[1][0] in i1args and d[1][0] not in selcond_i1:
                    selcond_i1.append(d[1][0])
                if d[0]=='select' and (d[1][1] in i1args or d[1][2] in i1args):
                    raise Unsupported("i1 arg as select branch (not the B2 single-hole shape)")
        if len(selcond_i1) > 2: raise Unsupported(f"{len(selcond_i1)} select-cond i1 args (support: 2)")


        i1sym = (len(selcond_i1) == 2)
        if i1sym:
            sctx.i1sym=True; tctx.i1sym=True
        for a in i1args:
            if sret==a or tret==a: raise Unsupported(f"i1 arg %{a} returned")
        pred_args=[]
        for asm in sasms: args_in(asm, sdefs, argw, pred_args)


        has_exact = any(d[0]=='div' and d[4] for d in sdefs.values()) \
                    or any(d[0]=='div' and d[4] for d in tdefs.values())


        puretgt = has_exact and not tasms

        def _ovf_prints(fl_list, ctx_):
            acc=set()
            for (_vv,op_,fl_,ops_) in fl_list:
                for _pr in ovf_preds(op_, fl_):
                    acc.add(f"{dot_recv(bv_expr(ops_[0],ctx_,True))}.{_pr} {bv_expr(ops_[1],ctx_,True)}")
            return acc


        sshlf=[]; shl_flags(sret, sdefs, argw, sshlf)
        tshlf=[]; shl_flags(tret, tdefs, argw, tshlf)
        _pshlf=[]
        for asm in sasms: shl_flags(asm, sdefs, argw, _pshlf)
        for asm in tasms: shl_flags(asm, tdefs, argw, _pshlf)
        if _pshlf:
            raise Unsupported("llvm.shl nsw/nuw inside an assume predicate (no gate witness)")
        if (sshlf or tshlf) and not fw:


            raise Unsupported("llvm.shl nsw/nuw (shift-overflow split has no gate witness)")
        if tshlf and not sshlf:
            raise Unsupported("tgt-only llvm.shl nsw/nuw (no src overflow cover; no row)")


        psel_info={}
        if fw and len(sasms)==1:
            _pd=sdefs.get(sasms[0])
            if _pd is not None and _pd[0]=='select' and _pd[2]=='1':
                _pc,_pt,_pe=_pd[1]
                _ed=sdefs.get(_pe)
                if _ed is not None and _ed[0]=='const' and _ed[1]==0 \
                   and len(_ed)>2 and _ed[2]=='1' \
                   and is_boolprintable(_pc, sctx) and is_boolprintable(_pt, sctx):
                    _ca=[]; args_in(_pc, sdefs, argw, _ca)
                    psel_info[0]=(_pc, _pt, len(_ca))
                else:
                    raise Unsupported("i1-select assume predicate outside the short-circuit "
                                      "row (cond/then not bool-printable or else-branch not "
                                      "the false constant; no gate witness)")

        tflags_early=[]; flagged_ops(tret, tdefs, argw, tflags_early)
        tflags_ok=False
        if tflags_early and has_exact:
            _pf=[]
            for asm in sasms: flagged_ops(asm, sdefs, argw, _pf)
            tflags_ok = _ovf_prints(tflags_early, tctx) <= _ovf_prints(_pf, sctx)
        if tflags_early and not tflags_ok and fw and not has_exact:


            _sf=[]; flagged_ops(sret, sdefs, argw, _sf)
            tflags_ok = bool(_sf) and _ovf_prints(tflags_early, tctx) <= _ovf_prints(_sf, sctx)


        f9_tgtflags=[]
        if tflags_early and not tflags_ok and not has_exact:
            _pf9=[]
            for asm in sasms: flagged_ops(asm, sdefs, argw, _pf9)
            if _pf9:
                f9_tgtflags=list(tflags_early)
                tflags_ok=True
        if tflags_early and not tflags_ok:
            if fw and not has_exact and (selcond_i1 or [a for a,t in args if t=='1']):
                raise Unsupported("overflow-flagged op in tgt return under an i1-arg select "
                                  "mix: the src flags sit in opposite branches of the "
                                  "i1-cond select, so the case tree needs per-branch "
                                  "value holes")
            raise Unsupported("overflow-flagged op in tgt return (tgt poison exclusion is "
                              "assumption-dependent; needs a hole-conjunction)")


        sel_nodes=[]; find_selects(sret, sdefs, argw, sel_nodes)
        tsel_nodes=[]; find_selects(tret, tdefs, argw, tsel_nodes)
        if len(sel_nodes)+len(tsel_nodes) > 5: raise Unsupported(">5 selects")
        def sel_kind(cv, dd, ctx):
            d=dd.get(cv)
            if d is None and argw.get(cv)=='1': return 'i1arg'
            if d is not None and d[0]=='icmp': return 'bv'
            if is_bv1printable(cv, ctx): return 'bv1'
            raise Unsupported("select cond neither icmp nor i1 arg nor bv1-printable")
        s_kinds=[sel_kind(c,sdefs,sctx) for (_,c,_,_,_) in sel_nodes]
        t_kinds=[sel_kind(c,tdefs,tctx) for (_,c,_,_,_) in tsel_nodes]
        kinds=set(s_kinds+t_kinds)


        symmode = ('bv1' in kinds) or ({'bv','i1arg'} <= kinds)
        if symmode:
            i1sym=False
            sctx.i1sym=True; tctx.i1sym=True
        i1sel = ('i1arg' in kinds) and not i1sym and not symmode
        if i1sel and not selcond_i1: raise Unsupported("i1 select cond but no i1 arg")
        if i1sel:

            for nodes,ctx in ((sel_nodes,sctx),(tsel_nodes,tctx)):
                for (sv,c,a2,b2,_) in nodes:
                    ctx.resolved[sv]=b2


        pflags=[]
        for asm in sasms: flagged_ops(asm, sdefs, argw, pflags)
        pflag_prints=_ovf_prints(pflags, sctx)
        flags=[]; flagged_ops(sret, sdefs, argw, flags)
        tflags=[]; flagged_ops(tret, tdefs, argw, tflags)
        if tflags and not tflags_ok:
            raise Unsupported("overflow-flagged op in tgt return")
        tp=[]
        for asm in tasms: flagged_ops(asm, tdefs, argw, tp)
        if tp and not (has_exact and _ovf_prints(tp, tctx) <= pflag_prints):


            raise Unsupported("overflow-flagged op in tgt predicate")


        if any(fl=='nswnuw' for (_,_,fl,_) in pflags) and not (not has_exact and (fw or f9_tgtflags)):
            raise Unsupported("nsw+nuw combined flag inside assume predicate (no gate witness)")


        if symmode and (flags or pflags):
            raise Unsupported("overflow flag + bv1-cond/symbolic selects together (no gate witness)")
        sdis=[]; disjoint_ors(sret, sdefs, argw, sdis)
        tdis=[]; disjoint_ors(tret, tdefs, argw, tdis)
        if tdis: raise Unsupported("disjoint-or in tgt")
        if len(sdis) > 1: raise Unsupported(f"{len(sdis)} disjoint-ors (support: 1)")
        if fw and sdis and sdefs[sdis[0][0]][4] != wv:


            raise Unsupported("disjoint-or at a non-main fixed width (no cross-width row)")
        pdis=[]
        for asm in sasms: disjoint_ors(asm, sdefs, argw, pdis)
        if pdis: raise Unsupported("disjoint-or inside predicate")


        sdiv_all=[]; _na=0
        for k,v in sorder:
            if k=='assume': _na+=1
            elif k=='op' and sdefs[v][0]=='div':
                sdiv_all.append((v, sdefs[v][1], sdefs[v][2], _na, sdefs[v][4]))
        tdiv_all=[]
        for k,v in torder:
            if k=='op' and tdefs[v][0]=='div':
                tdiv_all.append((v, tdefs[v][1], tdefs[v][2], tdefs[v][4]))
        anydiv = bool(sdiv_all) or bool(tdiv_all)
        pred_div_by_asm={}; leaf_divs=[]; tgt_divs=[]; leaf_div_src={}
        predflag_mode=False; pred_flag_by_asm={}; exact_rows=[]


        def _div_has_sel():
            for dd,divs in ((sdefs,[ops for (_v,_o,ops,_a,_x) in sdiv_all]),
                            (tdefs,[ops for (_v,_o,ops,_x) in tdiv_all])):
                for dops in divs:
                    for o in dops:
                        _sc=[]; sels_in(o, dd, argw, _sc)
                        if _sc: return True
            return False
        fwchain = fw and (bool(sshlf) or bool(tshlf)
                          or (anydiv and bool(flags) and not pflags and not has_exact
                              and _div_has_sel()))


        divflagfw = (fw and anydiv and bool(flags) and not pflags
                     and not has_exact and not fwchain)
        fwchain_divsel=None
        if anydiv:
            if flags or pflags:


                if (fwchain or divflagfw) and flags and not pflags:
                    pass
                elif not (has_exact and pflags
                        and _ovf_prints(flags, sctx) <= pflag_prints):
                    if fw and has_exact and not pflags:
                        raise Unsupported("div + overflow flag with an exact division: "
                                          "the tgt-side `sdiv exact` value-poison needs "
                                          "an smod-vs-assumed-srem companion hole and the ret "
                                          "flags sit behind an i1-return select whose polarity "
                                          "flips their poison strictness (per-branch holes)")
                    raise Unsupported("div + overflow flag together (needs "
                                      "F9 × div × hole-conjunction)")
                else:
                    predflag_mode=True
                    flags=[]
            if sdis or tdis:
                raise Unsupported("div + disjoint-or together: the `or disjoint` "
                                  "and the nsw-add are opposite branches of the select feeding "
                                  "the srem — their poison strictness flips with the select "
                                  "polarity (per-branch guards/holes); only select-free "
                                  "hoisted guards are supported")
            if i1args:
                raise Unsupported("div + i1 arg together (no row)")
            for dd,divs in ((sdefs,[(v,o,ops) for (v,o,ops,_,_) in sdiv_all]),
                            (tdefs,[(v,o,ops) for (v,o,ops,_) in tdiv_all])):
                for (vv,dop,dops) in divs:
                    selchk=[]
                    for o in dops: sels_in(o, dd, argw, selchk)
                    if selchk:
                        if fwchain and len(set(selchk))==1 \
                           and (fwchain_divsel in (None, selchk[0])):


                            fwchain_divsel=selchk[0]
                        else:
                            raise Unsupported("div operand contains a select (the UB guard needs "
                                              "per-branch resolution into an if-form hole)")
            if has_exact:

                if sel_nodes or tsel_nodes:
                    raise Unsupported("exact div + select together (no gate witness)")
                for (vv,dop,dops,ex) in tdiv_all:
                    if ex:
                        raise Unsupported(f"llvm.{dop} exact on the TGT side (the tgt "
                                          "value-poison is not excludable by a src-side "
                                          "case tree; no row)")
                for (vv,dop,dops,ai,ex) in sdiv_all:
                    if ex and ai < len(sasms):
                        raise Unsupported(f"llvm.{dop} exact inside an assume predicate "
                                          "(no gate witness)")


            seen_ub=set(); _ub=0
            try:
                for (vv,dop,dops,ai,ex) in sdiv_all:


                    ubp=div_ubp(dop, bv_expr(dops[0],sctx,True), bv_expr(dops[1],sctx,True),
                                sdefs[vv][3])
                    if ubp in seen_ub: continue
                    seen_ub.add(ubp); _ub+=1; hn=f"hub{_ub}"
                    if ai < len(sasms):
                        pred_div_by_asm.setdefault(ai, []).append((hn, ubp))
                    else:
                        leaf_divs.append((hn, ubp))
                        leaf_div_src[hn]=(dop, dops, sdefs[vv][3])
                _tb=0
                for (vv,dop,dops,ex) in tdiv_all:
                    ubp=div_ubp(dop, bv_expr(dops[0],tctx,True), bv_expr(dops[1],tctx,True),
                                tdefs[vv][3])
                    if ubp in seen_ub: continue
                    seen_ub.add(ubp); _tb+=1
                    tgt_divs.append((f"htub{_tb}", ubp))


                if divflagfw:
                    if sel_nodes or tsel_nodes:
                        raise Unsupported("div + overflow flag with selects at fixed width "
                                          "(the select polarity flips the flags' poison "
                                          "strictness — per-branch holes; no gate witness)")
                    if pred_div_by_asm:
                        raise Unsupported("div + overflow flag with a pred-side division "
                                          "(no gate witness)")
                    if leaf_divs:
                        raise Unsupported("div + overflow flag with a src ret-side division "
                                          "(only tgt-side guards are supported)")
            except Unsupported as e:
                if has_exact and 'shift amount' in str(e):


                    raise Unsupported(str(e) + " — blocks F-divexact here: "
                                      "the INT_MAX/INT_MIN constants are built by a constant-"
                                      "amount lshr feeding the assumes' sdiv guards")
                raise
            if has_exact:


                _xn=0; _seenx=set()
                for (vv,dop,dops,ai,ex) in sdiv_all:
                    if not ex: continue
                    a_=bv_expr(dops[0],sctx,True); b_=bv_expr(dops[1],sctx,True)
                    _dw=sdefs[vv][3]
                    remp = (f"{a_} % {b_} = 0#{_dw}" if dop=='udiv'
                            else f"{dot_recv(a_)}.smod {b_} = 0#{_dw}")
                    if remp in _seenx: continue
                    _seenx.add(remp); _xn+=1
                    exact_rows.append((f"hex{_xn}", remp))
            if predflag_mode:


                _pfseen=set(); _hovn=0
                for k2,asm in enumerate(sasms):
                    acc=[]; flagged_ops(asm, sdefs, argw, acc)
                    for (vv,op_,fl_,ops_) in acc:
                        if vv in _pfseen: continue
                        _pfseen.add(vv)
                        for _pr in ovf_preds(op_, fl_):
                            _hovn+=1
                            pred_flag_by_asm.setdefault(k2, []).append(
                                (f"hov{_hovn}",
                                 f"{bv_expr(ops_[0],sctx)}.{_pr} {bv_expr(ops_[1],sctx)}",
                                 f"{bv_expr(ops_[0],sctx,True)}.{_pr} {bv_expr(ops_[1],sctx,True)}"))
        divops = {o + ('x' if ex else '') for (_,o,_,_,ex) in sdiv_all} \
               | {o + ('x' if ex else '') for (_,o,_,ex) in tdiv_all}


        for dd in (sdefs, tdefs):
            for vv,d in dd.items():
                if d[0]=='shift':
                    ad=dd.get(d[2][1])
                    if ad is not None and ad[0]=='wconst':
                        raise Unsupported("width-constant as shift amount (normal-form instability)")


        def _fw_const_amt_skip(amt, dd):
            if not fw: return False
            ad_=dd.get(amt)
            if ad_ is None or ad_[0]!='const': return False


            _aw=ad_[2] if len(ad_)>2 else wv
            if ad_[1] % (2**int(_aw)) < int(_aw): return True
            raise Unsupported(f"fixed-width constant shift amount {ad_[1]} >= width {_aw} "
                              "(always-poison shift; no gate witness)")
        def _amt_gw(amt, dd, _argw):
            if not fw: return wv
            return fw_val_width(amt, dd, _argw) or wv
        pred_amt=[]
        seen_amt=set()
        for k,asm in enumerate(sasms):
            acc={}
            if k in psel_info:


                shift_amounts(psel_info[k][0], sdefs, argw, acc)
                shift_amounts(psel_info[k][1], sdefs, argw, acc)
            else:
                shift_amounts(asm, sdefs, argw, acc)
            for amt,strict in acc.items():
                if _fw_const_amt_skip(amt, sdefs): continue
                if not strict:
                    raise Unsupported("shift under select branch in assume predicate (poison not guaranteed)")
                ad2=sdefs.get(amt)
                if ad2 is not None and ad2[0]=='const':


                    _dacc={}
                    div_ops(asm, sdefs, argw, _dacc)
                    if _dacc or has_exact:
                        raise Unsupported("constant shift amount inside assume predicate "
                                          "feeding a pred-side division: the "
                                          "shift-built value leaves the sdiv range-if stuck "
                                          "at the UB leaf; needs range-guard×division "
                                          "coexistence beyond the const-shift flip")


                key=bv_expr(amt, sctx, True)
                if key not in seen_amt:
                    seen_amt.add(key); pred_amt.append((k, key, _amt_gw(amt, sdefs, argw)))
        sacc={}; shift_amounts(sret, sdefs, argw, sacc)
        tacc={}; shift_amounts(tret, tdefs, argw, tacc)
        leaf_amt=[]
        for amt,strict in sacc.items():
            if _fw_const_amt_skip(amt, sdefs): continue
            key=bv_expr(amt, sctx, True)
            if key in seen_amt: continue
            if not strict:
                raise Unsupported("oversized shift under select branch in src return (poison not guaranteed)")
            seen_amt.add(key); leaf_amt.append((key, _amt_gw(amt, sdefs, argw)))
        exf_amt=[]
        for amt in tacc:
            if _fw_const_amt_skip(amt, tdefs): continue
            key=bv_expr(amt, tctx, True)
            if key in seen_amt: continue
            d=tdefs.get(amt)
            if not (d and d[0]=='const' and d[1]>=1 and extra_names):
                raise Unsupported("tgt-only oversized shift amount (no src poison cover)")
            seen_amt.add(key); exf_amt.append((key, _amt_gw(amt, tdefs, argw)))
        if has_exact and (pred_amt or leaf_amt or exf_amt):
            raise Unsupported("exact div + oversized-shift guard together (no gate witness)")
        if divflagfw and (pred_amt or leaf_amt or exf_amt):
            raise Unsupported("div + overflow flag + oversized-shift guard together "
                              "(no gate witness)")


        rest=[]
        for rv,dd in ((sret,sdefs),(tret,tdefs)):
            tmp=[]; args_in(rv, dd, argw, tmp)
            for a in tmp:
                if a not in pred_args and a not in rest: rest.append(a)


        divargs_rest=set()
        if fw and anydiv and rest:
            _divargs=[]
            for (vv,dop,dops,ai,ex) in sdiv_all:
                for o in dops: args_in(o, sdefs, argw, _divargs)
            for (vv,dop,dops,ex) in tdiv_all:
                for o in dops: args_in(o, tdefs, argw, _divargs)
            rest = [a for a in rest if a in _divargs] + \
                   [a for a in rest if a not in _divargs]
            divargs_rest = {a for a in rest if a in _divargs}


        fw_hoist=[]
        if fw and (leaf_divs or tgt_divs) and rest and not fwchain \
           and not (leaf_amt or exf_amt or exact_rows or has_exact):
            def _mentions_rest(u):
                return any(re.search(r'(?<![\w])'+re.escape(ren[a])+r'(?![\w])', u)
                           for a in rest)
            if not any(_mentions_rest(u) for _,u in leaf_divs + tgt_divs):
                fw_hoist=[(hn,u,False) for hn,u in leaf_divs] + \
                         [(hn,u,True)  for hn,u in tgt_divs]


        if divflagfw and tgt_divs and not fw_hoist:
            raise Unsupported("div + overflow flag with a tgt div-UB guard mentioning a "
                              "return-only arg (the tgtub hole is stated over the "
                              "pred args at the hoisted guard)")

        opcodes = collect_opcodes(sdefs)|collect_opcodes(tdefs)
        names=(src_def, tgt_def)


        has_shift = bool(opcodes & SHIFTOP) or anydiv or i1sym or symmode \
                    or (fw and bool(sel_nodes or tsel_nodes))


        need_pow_bridge = (not wv.isdigit()) and any(
            d[0] == 'shift' and (dd.get(d[2][1]) or (None,))[0] == 'const'
            for dd in (sdefs, tdefs) for d in dd.values())


        _extended_semantic = (bool(extra_names) or multi or pred_amt or leaf_amt
                   or exf_amt or anydiv or i1sym or symmode
                   or ('shl' in opcodes) or ('lshr' in opcodes)
                   or ('ashr' in opcodes) or ('sext' in opcodes) or ('zext' in opcodes)
                   or ('ispow2' in opcodes)
                   or ('ctpop' in opcodes) or ('cttz' in opcodes) or ('ctlz' in opcodes))
        newfeat = (wv!='w') or _extended_semantic


        sel_depth2 = any(n[4]>=2 for n in sel_nodes+tsel_nodes)
        retype = newfeat or (bool(tsel_nodes) and not i1sel) or sel_depth2


        features = {
            'fw': fw, 'sym': not fw,
            'pflags': bool(pflags), 'predflag_mode': bool(predflag_mode),
            'f9route': bool(pflags) and not bool(predflag_mode),
            'ret_outside_pred': bool(rest),
            'sdis': bool(sdis), 'i1args': bool(i1args),
            'shl_flagged': bool(sshlf) or bool(tshlf),
            'newfeat': bool(newfeat),
            'extra_binders': bool(extra_names),
            'multi_assume': multi,
            'leaf_amt': bool(leaf_amt), 'exf_amt': bool(exf_amt),
            'anydiv': bool(anydiv), 'i1sym': bool(i1sym),
            'symmode': bool(symmode),
            'op_trunc': 'trunc' in opcodes, 'op_ispow2': 'ispow2' in opcodes,
            'op_ctpop': 'ctpop' in opcodes, 'op_cttz': 'cttz' in opcodes,
            'op_ctlz': 'ctlz' in opcodes,
        }
        decision = interactions_decide(features)
        if os.environ.get('EMIT_SHADOW'):
            _shadow_log(case, features, decision)

        if pflags and not predflag_mode:


            _wvname_only = (decision[1] == 'f9-sym-extended'
                            and not fw and bool(f9_tgtflags)
                            and not _extended_semantic)
            if decision[0] == 'UNKNOWN' and not _wvname_only:
                legacy = decision[2] or ''
                raise Unsupported(
                    "%s [untested combination of individually supported "
                    "features: %s]" % (legacy or 'F9 combination',
                                       decision[1]))
            f9_guards=[(f"hsh{i+1}", key, gw) for i,(_k,key,gw) in enumerate(pred_amt)]
            return emit_f9(text, case, name, names, src_text, tgt_text, args, argw, idx,
                           ren, sctx, tctx, sdefs, tdefs, sasms[0], sret, tret, srett,
                           pflags, flags, sel_nodes, tsel_nodes, opcodes, fw, wv,
                           f9_guards, f9_tgtflags)


        flagsel=None
        fselowner=None
        use_seqflag=False
        has_combined = any(fl=='nswnuw' for (_,_,fl,_) in flags)
        if flags and (sel_nodes or tsel_nodes):


            sp={}; strict_poison(sret, sdefs, argw, sp)
            for (vv,_,_,_) in flags:
                if not sp.get(vv, False):
                    raise Unsupported("overflow-flagged op only under a select branch (poison not guaranteed)")
            fsel=[]; owners=[]
            for (vv,_,_,fops) in flags:
                mine=[]
                for o in fops: sels_in(o, sdefs, argw, mine)
                if mine: owners.append(vv)
                for s in mine:
                    if s not in fsel: fsel.append(s)
            if fsel:
                if len(fsel)!=1 or len(owners)!=1:
                    raise Unsupported(">1 select inside overflow-flag operands (no row)")
                svv=fsel[0]; svd=sdefs[svv]; cvar=svd[1][0]
                cd=sdefs.get(cvar)
                if cd is None or cd[0]!='icmp' or any(is_i1typed(o,sctx) for o in cd[2]):
                    raise Unsupported("flag-operand select cond not a bv icmp (no row)")
                if cd[1] in ('eq','ne'):
                    raise Unsupported("flag-operand select with eq/ne cond (propositional "
                                      "if-print diverges from the tree print; no row)")
                inner=[]
                for o in (svd[1][1], svd[1][2]): sels_in(o, sdefs, argw, inner)
                if inner:
                    raise Unsupported("nested select inside overflow-flag operand (no row)")
                flagsel=(svv, cvar); fselowner=owners[0]


            if srett == '1':
                if flagsel is None:
                    raise Unsupported("overflow flag + selects with i1 return and no "
                                      "flag-feeding select (no bridge witness)")
                use_seqflag=True
            if len(flags) > 1 or has_combined:
                if len(flags) > 1 and flagsel is None:
                    raise Unsupported(">1 overflow flag + selects together (needs F9/F7)")
                if len(flags) > 2:
                    raise Unsupported(">2 overflow flags + selects together (needs F9/F7)")
                use_seqflag=True
            if use_seqflag:
                retype=True
        if divflagfw and (has_combined or use_seqflag):
            raise Unsupported("div + combined/sequential overflow flags at fixed width "
                              "(only the single/multi-flag value leaf is supported)")
        if has_combined and not (sel_nodes or tsel_nodes):


            use_seqflag=True
            retype=True


        ovfcover=None


        features.update({
            'fwchain': bool(fwchain), 'i1sel': bool(i1sel),
            'has_exact': bool(has_exact), 'use_seqflag': bool(use_seqflag),
            'pred_div': bool(pred_div_by_asm), 'tgt_div': bool(tgt_divs),
        })
        decision = interactions_decide(features)
        if os.environ.get('EMIT_SHADOW'):
            _shadow_log(case + '#fwchain', features, decision)
        if fwchain:


            if decision[0] == 'UNKNOWN':
                raise Unsupported(
                    "%s [untested combination of individually supported "
                    "features: %s]" % (decision[2] or 'fwchain combination',
                                       decision[1]))


            _sp={}; strict_poison(sret, sdefs, argw, _sp)
            for (vv,_,_) in sshlf:
                if not _sp.get(vv, False):
                    raise Unsupported("flagged shl only under a select branch "
                                      "(poison not guaranteed; no row)")


            _shlsels=[]
            for (vv,_,ops2) in sshlf: sels_in(ops2[0], sdefs, argw, _shlsels)
            if _shlsels:
                if len(set(_shlsels))>1:
                    raise Unsupported("several selects inside fw shl-flag operands (no row)")
                _sv=_shlsels[0]
                if flagsel is not None and flagsel[0]!=_sv:
                    raise Unsupported("shl-flag select differs from the bin-flag select (no row)")
                if flagsel is None:
                    _svd=sdefs[_sv]; _cv=_svd[1][0]
                    _cd=sdefs.get(_cv)
                    if _cd is None or _cd[0]!='icmp' \
                       or any(is_i1typed(o,sctx) for o in _cd[2]) or _cd[1] in ('eq','ne'):
                        raise Unsupported("fw shl-flag operand select cond not a plain "
                                          "bv icmp (no row)")
                    _inner=[]
                    for o in (_svd[1][1], _svd[1][2]): sels_in(o, sdefs, argw, _inner)
                    if _inner:
                        raise Unsupported("nested select inside fw shl-flag operand (no row)")
                    flagsel=(_sv, _cv)
            if fwchain_divsel is not None and (flagsel is None or flagsel[0]!=fwchain_divsel):
                raise Unsupported("div-operand select is not the hoisted flag select (no row)")


            _srcstmt={shl_noovf_eq(vv, sctx, True): vv for (vv,_,_) in sshlf}
            for (tvv,tfl,tops) in tshlf:
                teq=shl_noovf_eq(tvv, tctx, True)
                if teq in _srcstmt: continue
                if ovfcover is not None:
                    raise Unsupported(">1 uncovered tgt-side flagged shl (no row)")
                if flagsel is None or len(sshlf)!=1 or flags or anydiv:
                    raise Unsupported("uncovered tgt-side flagged shl outside the supported "
                                      "OVFCOVER structure")
                (svv,sfl,sops)=sshlf[0]
                svd=sdefs[flagsel[0]]
                if sfl!=tfl or sops[0]!=flagsel[0] \
                   or shift_amt_nat(sops[1], sctx, True)!=shift_amt_nat(tops[1], tctx, True):
                    raise Unsupported("uncovered tgt-side flagged shl outside the supported "
                                      "OVFCOVER structure")
                _pols=[]
                for pol,branch in (('then',svd[1][1]), ('else',svd[1][2])):
                    sctx.resolved[flagsel[0]]=branch
                    _match = shl_noovf_eq(svv, sctx, True)==teq
                    del sctx.resolved[flagsel[0]]
                    if _match: _pols.append(pol)
                if len(_pols)!=1:
                    raise Unsupported("tgt flagged-shl operand matches no single branch of "
                                      "the hoisted select (no OVFCOVER match)")
                ovfcover=(tvv, svv, _pols[0])
            retype=True
        if sdis and flags: raise Unsupported("disjoint + overflow flag together")
        rdis = bool(sdis) and retype
        if sdis and retype and not symmode:
            raise Unsupported("disjoint + extended features (w1/multi-assume/shift/cast/tgt-select) unsupported")
        if len(tsel_nodes)>0 and not i1sel and not symmode and srett=='1':
            raise Unsupported("bv-cond select in tgt return with i1 return (unsupported bridge)")
        bo_args=[]
        if len(tsel_nodes)>0 and not i1sel and not symmode:


            accs={}; arg_strict(sret, sdefs, argw, accs)
            taccs={}; arg_strict(tret, tdefs, argw, taccs)
            for a,_ in args:
                if (a in accs or a in taccs) and not accs.get(a, False) \
                   and a not in pred_args:
                    bo_args.append(a)
            if bo_args and (srett=='1' or flags or sdis or i1args or i1sym or anydiv
                            or leaf_amt or exf_amt or multi or fwchain):
                raise Unsupported("arg reaches a return only through select branches and the "
                                  "leaf carries flags/disjoint/div/shift-guards/i1/multi-assume "
                                  "or a Bool goal — dummy-poison row unsupported here")
            if bo_args and any(argw[a] not in (wv, '1') for a in bo_args):


                raise Unsupported("branch-only arg at a non-main fixed width "
                                  "(dummy-poison row has no cross-width witness)")


        pred_specs=[]
        for asm in sasms:


            d_=sdefs.get(asm)
            if d_ is not None and d_[0]=='icmp' and d_[1]=='eq' \
               and not any(is_i1typed(o, sctx) for o in d_[2]) \
               and bv_expr(d_[2][0], sctx, True) == bv_expr(d_[2][1], sctx, True):
                pred_specs.append(('skip', None)); continue
            if len(pred_specs) in psel_info:


                pred_specs.append(('bool', bool_expr(psel_info[len(pred_specs)][1], sctx)))
                continue
            try:
                pred_specs.append(('bool', bool_expr(asm, sctx)))
            except Unsupported:
                if not symmode: raise
                pred_specs.append(('bv1', bv1_expr(asm, sctx)))
        pred_bools=[pb for _,pb in pred_specs]
        any_bv1_pred = any(k=='bv1' for k,_ in pred_specs)

        eff_idx={}
        for k,(pk_,_) in enumerate(pred_specs):
            if pk_!='skip': eff_idx[k]=len(eff_idx)
        multi_eff = len(eff_idx) > 1


        if not retype and not sdis \
           and any(ofint_arith_operand(asm, sdefs, argw) for asm in sasms):
            retype = True

        goal_bv1=False
        if srett == '1':
            try:
                src_goal = bool_expr(sret, sctx, stmt=True)
                tgt_goal = bool_expr(tret, tctx, stmt=True)
            except Unsupported:
                if (sel_nodes or tsel_nodes) and not (i1sym or symmode):
                    raise Unsupported("i1 return with raw-i1 subterms and selects (no bridge)")
                src_goal = bv1_goal(sret, sctx); tgt_goal = bv1_goal(tret, tctx)
                goal_bv1=True
        else:
            if srett != wv: raise Unsupported(f"fixed-width return i{srett}")
            src_goal = bv_expr(sret, sctx, stmt=True)
            tgt_goal = bv_expr(tret, tctx, stmt=True)


        condbridge=False
        if symmode and not (flags or sdis or anydiv or leaf_amt or exf_amt
                            or pred_amt or i1sel) and srett==wv:
            sd_=sdefs.get(sret); td_=tdefs.get(tret)
            if sd_ is not None and td_ is not None and sd_[0]=='select' and td_[0]=='select':
                try:
                    if bv_expr(sd_[1][1],sctx,True)==bv_expr(td_[1][1],tctx,True) \
                       and bv_expr(sd_[1][2],sctx,True)==bv_expr(td_[1][2],tctx,True):
                        src_goal = bv1_expr(sd_[1][0], sctx, True)
                        tgt_goal = bv1_expr(td_[1][0], tctx, True)
                        condbridge=True
                except Unsupported:
                    pass


        poisoncover=None
        if symmode and not condbridge and srett==wv and not flags and not anydiv \
           and not (leaf_amt or exf_amt) and not i1args:
            accs={}; arg_strict(sret, sdefs, argw, accs)
            taccs={}; arg_strict(tret, tdefs, argw, taccs)
            boas=[a for a,_ in args if (a in accs or a in taccs)
                  and not accs.get(a, False) and a not in pred_args]
            if boas:
                def _pcfail(msg):
                    raise Unsupported(f"branch-only arg %{boas[0]} in symmode: {msg}")
                if len(boas)!=1 or argw[boas[0]]!=wv:
                    _pcfail("several branch-only args / i1-typed (no row; F7 territory)")
                boa=boas[0]
                if not rest or rest[-1]!=boa:
                    _pcfail("not the innermost rest split (no row)")
                spol=scond=tpol=tcond=None
                for (nodes,dd,ctx_) in ((sel_nodes,sdefs,sctx),(tsel_nodes,tdefs,tctx)):
                    for (sv,c,a2,b2,_) in nodes:
                        ca=[]; args_in(c, dd, argw, ca)
                        if boa in ca: _pcfail("occurs inside a select cond (no row)")
                        ta=[]; args_in(a2, dd, argw, ta)
                        ea=[]; args_in(b2, dd, argw, ea)
                        if boa not in ta and boa not in ea: continue
                        if boa in ta and boa in ea: _pcfail("in both branches of one select (no row)")
                        pol='then' if boa in ta else 'else'
                        cp=selcond_prop(c, ctx_, True)
                        if ctx_ is sctx:
                            if spol is None: spol, scond = pol, cp
                            elif (spol,scond)!=(pol,cp):
                                _pcfail("src selects pick it under different conds/polarities "
                                        "(cond-complement not single-stateable; F7 territory)")
                        else:
                            if tpol is None: tpol, tcond = pol, cp
                            else: _pcfail("picked by several tgt selects (no row)")
                if spol is None or tpol is None:
                    _pcfail("carried on one side only (poison-ret leaf unsound; no row)")
                srcpick = scond if spol=='then' else f"¬ ({scond})"
                tgtpick = tcond if tpol=='then' else f"¬ ({tcond})"
                poisoncover=(boa, spol, scond, srcpick, tgtpick)


        fw_dummy2=None
        if fw and symmode and poisoncover is None and not condbridge and srett==wv \
           and not flags and not i1args and not sdis \
           and not (leaf_amt or exf_amt or exact_rows or has_exact) \
           and (fw_hoist or not (leaf_divs or tgt_divs)):
            accs={}; arg_strict(sret, sdefs, argw, accs)
            taccs={}; arg_strict(tret, tdefs, argw, taccs)
            boas=[a for a,_ in args if (a in accs or a in taccs)
                  and not accs.get(a, False) and a not in pred_args]
            if boas:
                def _d2fail(msg):
                    raise Unsupported(f"branch-only arg %{boas[0]} in fixed-width symmode: {msg}")
                if len(boas)!=1 or argw[boas[0]]!=wv:
                    _d2fail("several branch-only args / i1-typed (no row)")
                boa=boas[0]
                if not rest or rest[-1]!=boa:
                    _d2fail("not the innermost rest split (no row)")
                sd_=sdefs.get(sret); td_=tdefs.get(tret)
                if not (sd_ is not None and td_ is not None
                        and sd_[0]=='select' and td_[0]=='select'):
                    _d2fail("src/tgt return is not itself the picking select (no row)")
                def _pick(d_, dd, ctx_):
                    c,a2,b2=d_[1]
                    ca=[]; args_in(c, dd, argw, ca)
                    if boa in ca: _d2fail("occurs inside a select cond (no row)")
                    ta=[]; args_in(a2, dd, argw, ta)
                    ea=[]; args_in(b2, dd, argw, ea)
                    if boa in ta and boa in ea: _d2fail("in both branches (no row)")
                    if boa not in ta and boa not in ea:
                        _d2fail("not picked by the return select (no row)")
                    pol='then' if boa in ta else 'else'
                    other=b2 if pol=='then' else a2
                    mine=a2 if pol=='then' else b2
                    md=dd.get(mine)
                    if not (mine==boa or (md is None and mine==boa)):
                        _d2fail("picked branch is not the raw arg (no row)")
                    return pol, selcond_prop(c, ctx_, True), bv_expr(other, ctx_, True)
                spol_, scond_, sother = _pick(sd_, sdefs, sctx)
                tpol_, tcond_, tother = _pick(td_, tdefs, tctx)
                if sother != tother:
                    _d2fail("other-branch prints differ (needs the POISONCOVER hole2; "
                            "no div-tolerant witness)")
                srcpick_ = scond_ if spol_=='then' else f"¬ ({scond_})"
                tgtpick_ = tcond_ if tpol_=='then' else f"¬ ({tcond_})"
                fw_dummy2=(boa, srcpick_, tgtpick_)


        active_sels=[x for x in sel_nodes if x[0] not in sctx.resolved]
        if use_seqflag:
            bridge='bycases'
        elif symmode:
            bridge='sym3'
        elif i1sym:
            bridge='i1sym'
        elif i1sel:
            bridge='none'
        elif len(active_sels)==0 and len(tsel_nodes)==0:
            bridge='none'
        elif (len(active_sels)==1 and len(tsel_nodes)==0
              and active_sels[0][2] in argw and active_sels[0][3] in argw):
            bridge='hite'
        elif srett=='1':
            bridge='split'
        else:
            bridge='bycases'
        if fw and bridge in ('hite', 'split'):


            bridge='bycases'

        wargs=[a for a,t in args if t==wv]


        _argnames={a for a,_ in args}
        def _hc(k):


            base = 'hcond' if not multi_eff else f"hcond{eff_idx[k]+1}"
            return base+'q' if base[1:] in _argnames else base


        hyp_lines=[]; hyp_names=[]
        disjoint_mode = bool(sdis) and not rdis


        guard_prop = lambda key, gw=wv: f"BitVec.ofNat {gw} {gw} ≤ {key}"
        predguard_names=[]; leafguard_names=[]; exfguard_names=[]
        shl_rows=[]; tgt_shl_rows=[]
        if psel_info and (not fwchain or disjoint_mode):
            raise Unsupported("i1-select assume predicate outside the fw flag-chain row")
        gidx=0
        if disjoint_mode:
            pp=prop_pred(sasms[0], sctx)
            if pp is not None:
                hyp_lines.append(f"    (hpre : {pp})")
            else:
                hyp_lines.append(f"    (hpre : {pred_bools[0]} = true)")
            hyp_names.append('hpre')
            A=bv_expr(sdis[0][1][0], sctx, stmt=True); B=bv_expr(sdis[0][1][1], sctx, stmt=True)
            hyp_lines.append(f"    (hdis : {A} &&& {B} = 0#{wv})")
            hyp_names.append('hdis')
            dA, dB = A, B
        else:


            if psel_info:
                hyp_lines.append(f"    (hpc : {bool_expr(psel_info[0][0], sctx, True)} = true)")
                hyp_names.append('hpc')

            pred_guards_by_asm={}
            for k,amt,gw in pred_amt:
                gidx+=1; hn=f"hsh{gidx}"
                pred_guards_by_asm.setdefault(k, []).append((hn, amt, gw))
                predguard_names.append(hn)
                hyp_lines.append(f"    ({hn} : ¬ ({guard_prop(amt, gw)}))")
                hyp_names.append(hn)


            for k in sorted(pred_div_by_asm):
                for hn,ubp in pred_div_by_asm[k]:
                    predguard_names.append(hn)
                    hyp_lines.append(f"    ({hn} : ¬ ({ubp}))")
                    hyp_names.append(hn)


            for k in sorted(pred_flag_by_asm):
                for hn,_ovc,ovs in pred_flag_by_asm[k]:
                    predguard_names.append(hn)
                    hyp_lines.append(f"    ({hn} : {ovs} = false)")
                    hyp_names.append(hn)
            hcond_names=[]
            for k,(pkind,pb) in enumerate(pred_specs):
                if pkind=='skip': continue
                hp = 'hpre' if not multi_eff else f"hpre{eff_idx[k]+1}"
                hc = _hc(k)
                hcond_names.append(hc)
                if pkind=='bv1':
                    hyp_lines.append(f"    ({hp} : {pb} = 1#1)")
                else:
                    hyp_lines.append(f"    ({hp} : {pb} = true)")
                hyp_names.append(hc)
            for amt,gw in leaf_amt:
                gidx+=1; hn=f"hsh{gidx}"
                leafguard_names.append((hn, amt, gw))
                hyp_lines.append(f"    ({hn} : ¬ ({guard_prop(amt, gw)}))")
                hyp_names.append(hn)
            for amt,gw in exf_amt:
                gidx+=1; hn=f"hsh{gidx}"
                exfguard_names.append((hn, amt, gw))
                hyp_lines.append(f"    ({hn} : ¬ ({guard_prop(amt, gw)}))")
                hyp_names.append(hn)
            for hn,ubp in leaf_divs + tgt_divs:
                hyp_lines.append(f"    ({hn} : ¬ ({ubp}))")
                hyp_names.append(hn)
            for hn,remp in exact_rows:
                hyp_lines.append(f"    ({hn} : {remp})")
                hyp_names.append(hn)
            if rdis:


                A=bv_expr(sdis[0][1][0], sctx, stmt=True); B=bv_expr(sdis[0][1][1], sctx, stmt=True)
                hyp_lines.append(f"    (hdis : {A} &&& {B} = 0#{wv})")
                hyp_names.append('hdis')
                dA, dB = A, B


            _fpn=[]
            _tot=sum(len(ovf_preds(op,fl)) for (_,op,fl,_) in flags)
            for (vv,op,fl,ops) in flags:
                a=dot_recv(bv_expr(ops[0],sctx,stmt=True)); b=bv_expr(ops[1],sctx,stmt=True)
                for pred in ovf_preds(op, fl):
                    hn = 'hov' if _tot==1 else f"hov{len(_fpn)+1}"
                    _fpn.append((hn, vv))
                    hyp_lines.append(f"    ({hn} : {a}.{pred} {b} = false)")
                    hyp_names.append(hn)


            shl_rows=[]
            tgt_shl_rows=[]
            if fwchain:
                _seen_shl={}
                for (vv,_,_) in sshlf:
                    eq=shl_noovf_eq(vv, sctx, True)
                    if eq in _seen_shl: continue
                    hn=f"hso{len(_seen_shl)+1}"
                    _seen_shl[eq]=hn
                    shl_rows.append((hn, vv))
                    hyp_lines.append(f"    ({hn} : {eq})")
                    hyp_names.append(hn)
                _tn=0
                for (tvv,_,_) in tshlf:
                    teq=shl_noovf_eq(tvv, tctx, True)
                    if teq in _seen_shl: continue
                    _tn+=1; hn=f"hto{_tn}"
                    tgt_shl_rows.append((hn, tvv))
                    hyp_lines.append(f"    ({hn} : {teq})")
                    hyp_names.append(hn)


        hole_h1=None
        all_stmt_text = " ".join([src_goal, tgt_goal] + hyp_lines)
        used_i1=[a for a in i1args
                 if re.search(r'(?<![\w])'+re.escape(ren[a])+r'(?![\w])', all_stmt_text)]
        if i1sel and selcond_i1 and selcond_i1[0] in used_i1:
            hole_h1=f"    (h1 : ¬ ({ren[selcond_i1[0]]} = 1#1))"


        def occurs(a):
            return re.search(r'(?<![\w])'+re.escape(ren[a])+r'(?![\w])', all_stmt_text)
        if retype:


            binder_args=[a for a,t in args if (t!='1' and occurs(a)) or a in used_i1]
        else:
            binder_args=[a for a,t in args if t!='1' or a in used_i1]
        binders=" ".join(f"({ren[a]} : BitVec {argw[a]})" for a in binder_args)
        callargs=" ".join(ren[a] for a in binder_args)

        L=[]
        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax\n")
        L.append("open scoped InstCombine\nopen BitVec\n")
        if retype:


            L.append("set_option linter.unreachableTactic false")
            if fwchain and flagsel is not None:


                L.append("set_option linter.unnecessarySimpa false")
            L.append("set_option linter.unusedTactic false\n")
        L.append("-- ===== GIVEN (input) =====")
        L.append("-- [IR-DERIVED: src/tgt defs copied verbatim from the problem input]")
        L.append(src_text.strip()); L.append(""); L.append(tgt_text.strip()); L.append("")


        _obdef = bridge in ('split','i1sym','sym3') or (bridge=='bycases' and retype)
        if _obdef:
            L.append("private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by")
            L.append("  cases b <;> simp\n")


        fwmop = fwmulti and bridge=='bycases' and retype
        if fwmop:
            L.append(f"private theorem {name}_ofBool_zero_iff {{b : Bool}} : (BitVec.ofBool b = 0#1) ↔ (b = false) := by")
            L.append("  cases b <;> simp\n")
            L.append(f"private theorem {name}_one_eq_ofBool_iff {{b : Bool}} : (1#1 = BitVec.ofBool b) ↔ (b = true) := by")
            L.append("  cases b <;> simp\n")
            L.append(f"private theorem {name}_zero_eq_ofBool_iff {{b : Bool}} : (0#1 = BitVec.ofBool b) ↔ (b = false) := by")
            L.append("  cases b <;> simp\n")


        fw_mopups=[]
        if fw and srett=='1' and any(d[0]=='bin' and d[1] in BOOLOP and d[4]=='1'
                                     for dd in (sdefs, tdefs) for d in dd.values()):
            fw_mopups=[f"{name}_bv1_one_and", f"{name}_bv1_and_one",
                       f"{name}_bv1_one_or", f"{name}_bv1_or_one"]
            for nm, stmt_, lem in (
                ('one_and', "1#1 &&& x = x",   "BitVec.allOnes_and"),
                ('and_one', "x &&& 1#1 = x",   "BitVec.and_allOnes"),
                ('one_or',  "1#1 ||| x = 1#1", "BitVec.allOnes_or"),
                ('or_one',  "x ||| 1#1 = 1#1", "BitVec.or_allOnes")):
                L.append(f"private theorem {name}_bv1_{nm} (x : BitVec 1) : {stmt_} := by")
                L.append(f"  have h : (1#1 : BitVec 1) = BitVec.allOnes 1 := rfl")
                L.append(f"  rw [h, {lem}]\n")
        if need_pow_bridge:


            fw_mopups = fw_mopups + [f"{name}_two_pow_self_toNat_zero"]
        if has_shift:


            L.append(f"private theorem {name}_semval_bind_poison {{α β : Type}} (x : LLVM.SemVal α) :")
            L.append(f"    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =")
            L.append(f"      (LLVM.SemVal.poison : LLVM.SemVal β) := by")
            L.append(f"  cases x <;> rfl\n")
        if need_pow_bridge:


            L.append(f"private theorem {name}_two_pow_self_toNat_zero (w : Nat) :")
            L.append(f"    ((2#w : BitVec w) ^ w).toNat = 0 := by")
            L.append(f"  have gen : ∀ n, ((2#w : BitVec w) ^ n).toNat = 2 ^ n % 2 ^ w := by")
            L.append(f"    intro n")
            L.append(f"    induction n with")
            L.append(f"    | zero => simp [BitVec.pow_zero]")
            L.append(f"    | succ k ih =>")
            L.append(f"      rw [BitVec.pow_succ, BitVec.toNat_mul, ih, BitVec.toNat_ofNat]")
            L.append(f"      conv_rhs => rw [Nat.pow_succ, Nat.mul_mod]")
            L.append(f"  rw [gen, Nat.mod_self]\n")
        for _o in sorted(divops):


            L.append(DIV_COMPANIONS[_o].format(n=name))
        for _b in sorted({_o[:4] for _o in divops if _o.startswith(('sdiv','udiv'))}):

            L.append(DIV_POISON.format(n=name, b=_b))
        if i1sym or symmode:


            L.append(f"private theorem {name}_ite_semval_value {{w : Nat}} {{c : Prop}} [Decidable c]")
            L.append(f"    (a b : BitVec w) :")
            L.append(f"    (if c then LLVM.SemVal.value a else LLVM.SemVal.value b) =")
            L.append(f"      LLVM.SemVal.value (if c then a else b) := by")
            L.append(f"  split <;> rfl\n")
        if any_bv1_pred:


            L.append(f"private theorem {name}_bv1_eq_zero (b : BitVec 1) (h : ¬ b = 1#1) : b = 0#1 := by")
            L.append(f"  cases b with")
            L.append(f"  | ofFin f =>")
            L.append(f"      cases f with")
            L.append(f"      | mk n hn =>")
            L.append(f"          have hn' : n = 0 ∨ n = 1 := by omega")
            L.append(f"          rcases hn' with rfl | rfl")
            L.append(f"          · rfl")
            L.append(f"          · simp [BitVec.ofNat] at h\n")
            L.append(f"private theorem {name}_assume_zero_option :")
            L.append(f"    (match LLVM.SemVal.value (0#1 : BitVec 1) with")
            L.append(f"    | LLVM.SemVal.value 1#1 => (some () : Option Unit)")
            L.append(f"    | _ => none) = none := by")
            L.append(f"  decide\n")
        if condbridge and selcond_i1:


            L.append(f"private theorem {name}_bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by")
            L.append(f"  cases b with")
            L.append(f"  | ofFin f =>")
            L.append(f"      cases f with")
            L.append(f"      | mk n hn =>")
            L.append(f"          have hn' : n = 0 ∨ n = 1 := by omega")
            L.append(f"          rcases hn' with rfl | rfl")
            L.append(f"          · exact Or.inl rfl")
            L.append(f"          · exact Or.inr rfl\n")
        L.append("-- ===== THE ONLY HOLE: core BitVec identity (LLM writes this) =====")
        L.append("-- [IR-DERIVED: statement built from syntax alone]")
        if fw:
            L.append(f"private theorem {name}_value {binders}")
        else:
            L.append(f"private theorem {name}_value {{{wv} : Nat}}{esig} {binders}")
        hl=list(hyp_lines)
        if hole_h1 is not None: hl=[hole_h1]+hl
        for i,h in enumerate(hl):
            L.append(h + (" :" if i==len(hl)-1 else ""))
        L.append(f"    {src_goal} = {tgt_goal} := by")
        L.append("  sorry -- [HOLE: the genuinely-creative BitVec identity proof]\n")
        if ovfcover is not None:


            tvv2, svv2, pol2 = ovfcover
            _svd2=sdefs[flagsel[0]]
            _other=_svd2[1][2] if pol2=='then' else _svd2[1][1]
            sctx.resolved[flagsel[0]]=_other
            _srceq_other=shl_noovf_eq(svv2, sctx, True)
            del sctx.resolved[flagsel[0]]
            _fscond=bool_expr(flagsel[1], sctx, True)
            _npre2=((1 if psel_info else 0) + len(predguard_names)
                    + len(eff_idx) + len(leafguard_names))
            L.append("-- ===== HOLE 2: tgt flagged-shl overflow cover (LLM writes this) =====")
            L.append("-- [IR-DERIVED: statement built from syntax alone — 'when the select picks")
            L.append("--  the other branch, the tgt shl overflowing forces the src shl to overflow']")
            L.append(f"private theorem {name}_ovfcover {binders}")
            for h in hyp_lines[:_npre2]:
                L.append(h)
            if pol2=='then':
                L.append(f"    (hfs : ¬ ({_fscond} = true))")
            else:
                L.append(f"    (hfs : {_fscond} = true)")
            L.append(f"    (hto : ¬ ({shl_noovf_eq(tvv2, tctx, True)})) :")
            L.append(f"    ¬ ({_srceq_other}) := by")
            L.append("  sorry -- [HOLE: the genuinely-creative overflow-cover proof]\n")
        if poisoncover is not None:


            boa, spol, scond, srcpick, tgtpick = poisoncover
            pcbinders=" ".join(f"({ren[a]} : BitVec {argw[a]})"
                               for a in binder_args if a != boa)
            pchyps=hyp_lines[:len(predguard_names)+len(pred_specs)]
            L.append("-- ===== HOLE 2: select-cond cover for the branch-only arg (LLM writes this) =====")
            L.append("-- [IR-DERIVED: statement built from syntax alone — 'the tgt picks the")
            L.append(f"--  poisoned arg %{boa} only when the src does']")
            if fw:
                L.append(f"private theorem {name}_poisoncover {pcbinders}")
            else:
                L.append(f"private theorem {name}_poisoncover {{{wv} : Nat}}{esig} {pcbinders}")
            for h in pchyps:
                L.append(h)
            L.append(f"    (hbq : {tgtpick}) :")
            L.append(f"    {srcpick} := by")
            L.append("  sorry -- [HOLE: the genuinely-creative select-cond cover proof]\n")
        if has_exact and tgt_divs:


            _npre = (len(predguard_names) + len(hcond_names)
                     + len(leafguard_names) + len(exfguard_names) + len(leaf_divs))
            for _ti,(hn,ubp) in enumerate(tgt_divs):
                L.append(f"-- ===== HOLE {_ti+2}: tgt-side div-UB exclusion (LLM writes this) =====")
                L.append("-- [IR-DERIVED: statement built from syntax alone — 'the assumes exclude")
                L.append("--  the tgt division's UB condition']")
                if fw:
                    L.append(f"private theorem {name}_tgtub{_ti+1} {binders}")
                else:
                    L.append(f"private theorem {name}_tgtub{_ti+1} {{{wv} : Nat}}{esig} {binders}")
                for h in hyp_lines[:_npre+_ti]:
                    L.append(h)
                L.append(f"    ({hn} : {ubp}) :")
                L.append("    False := by")
                L.append("  sorry -- [HOLE: the genuinely-creative tgt-UB exclusion proof]\n")
        if divflagfw and tgt_divs:


            dfw_binder_args=[a for a in binder_args if a not in rest]
            dfw_binders=" ".join(f"({ren[a]} : BitVec {argw[a]})" for a in dfw_binder_args)
            dfw_callargs=" ".join(ren[a] for a in dfw_binder_args)
            _npre = len(predguard_names) + len(hcond_names)
            for _ti,(hn,ubp) in enumerate(tgt_divs):
                L.append(f"-- ===== HOLE {_ti+2}: tgt-side div-UB exclusion (LLM writes this) =====")
                L.append("-- [IR-DERIVED: statement built from syntax alone — 'the assumes exclude")
                L.append("--  the tgt division's UB condition']")
                L.append(f"private theorem {name}_tgtub{_ti+1} {dfw_binders}")
                for h in hyp_lines[:_npre+_ti]:
                    L.append(h)
                L.append(f"    ({hn} : {ubp}) :")
                L.append("    False := by")
                L.append("  sorry -- [HOLE: the genuinely-creative tgt-UB exclusion proof]\n")

        hb=4000000
        L.append("-- [IR-DERIVED: whole case-tree below is table-emitted]")
        L.append(f"set_option maxHeartbeats {hb} in")
        if fw:
            L.append(f"theorem {name}_correct : {src_def} ⊑ {tgt_def} := by")
        else:
            L.append(f"theorem {name}_correct ({wv} : Nat){esig} : {src_def} {wv}{eapp} ⊑ {tgt_def} {wv}{eapp} := by")
        L.append("  intro V")

        rev_types=[TY_of(argw[a]) for a,_ in reversed(args)]
        ctx_full = "[" + ", ".join(rev_types) + "]"
        for a,_ in args:
            i=idx[a]
            if i==0:
                head="[" + ", ".join(rev_types[1:]) + "]"
                L.append(f"  let {a}Var : (Ctxt.ofList {ctx_full}).Var ({TY_of(argw[a])}) :=")
                L.append(f"    Ctxt.Var.last (Ctxt.ofList {head}) ({TY_of(argw[a])})")
            else:
                L.append(f"  let {a}Var : (Ctxt.ofList {ctx_full}).Var ({TY_of(argw[a])}) := ⟨{i}, by simp⟩")


        out=[]
        product = (len(flags)>=2) or disjoint_mode or bool(i1args)
        pleaf_style = 'r2' if retype else ('simp' if (disjoint_mode or i1args) else 'v1')
        if has_shift:
            names=(src_def, tgt_def, f"{name}_semval_bind_poison")
        if divops:
            names=tuple(names)+tuple(f"{name}_{o}_eq_if" for o in sorted(divops))
            names=tuple(names)+tuple(
                f"{name}_{b}_poison{s}"
                for b in sorted({_o[:4] for _o in divops if _o.startswith(('sdiv','udiv'))})
                for s in ("L","R"))
        if symmode:


            names=tuple(names)+(f"{name}_ite_semval_value",)
        if need_pow_bridge:


            names=tuple(names)+(f"{name}_two_pow_self_toNat_zero",)

        def hv_prefix():
            return f"{name}_value{wvapp}{eapp} {callargs}"

        def hv_call_args(extra_tail):
            parts=[]
            if hole_h1 is not None: parts.append("h1")
            if psel_info: parts.append("hpc")
            parts += predguard_names
            parts += extra_tail
            return " ".join([hv_prefix()]+parts)

        def close_leaf(indent, hv_call):
            p=" "*indent
            if bridge=='hite':
                (sv,c,a2,b2,_)=active_sels[0]
                cond=bool_expr(c, sctx)
                out.extend(_div_or_rw(p)); out.append(f"{p}have hv := {hv_call}")
                out.append(f"{p}have hite : (if BitVec.ofBool {cond} = 1#1 then LLVM.SemVal.value {ren.get(a2,a2)} else LLVM.SemVal.value {ren.get(b2,b2)})")
                out.append(f"{p}    = LLVM.SemVal.value (if {cond} = true then {ren.get(a2,a2)} else {ren.get(b2,b2)}) := by")
                out.append(f"{p}  cases hite_c : {cond} <;> simp [hite_c]")
                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                out.append(f"{p}  · refine ImmediateUBOr.IsRefinedBy.bothValues ?_")
                out.append(f"{p}    rw [hite]")
                out.append(f"{p}    simp [hv, beq_iff_eq, bne_iff_ne]")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
            elif bridge=='split':
                splits=" <;> ".join(["split"]*len(active_sels))
                out.extend(_div_or_rw(p)); out.append(f"{p}have hv := {hv_call}")
                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}      rw [← hv]")
                out.append(f"{p}      simp only [ofBool_one_iff]")
                out.append(f"{p}      {splits} <;> simp_all)")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
            elif bridge=='sym3':


                atoms=[ren[a] for a in selcond_i1] if condbridge else []
                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.extend(_div_or_rw(p+"      ")); out.append(f"{p}      have hv := {hv_call}")
                if atoms:
                    chain=" <;> ".join(f"rcases {name}_bv1_cases {a} with h1c{i+1} | h1c{i+1}"
                                       for i,a in enumerate(atoms))
                    out.append(f"{p}      {chain} <;> "
                               f"simp_all [ofBool_one_iff, {name}_ite_semval_value, "
                               f"InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, "
                               f"LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])")
                else:
                    out.append(f"{p}      simp [hv, ofBool_one_iff, {name}_ite_semval_value, "
                               f"InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, "
                               f"LLVM.SemVal.isRefinedBy_self])")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
            elif bridge=='i1sym':


                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.extend(_div_or_rw(p+"      ")); out.append(f"{p}      have hv := {hv_call}")
                out.append(f"{p}      simp only [{name}_ite_semval_value]")
                out.append(f"{p}      simp [hv, InstCombine.LLVM.Ty.width, "
                           f"LLVM.SemVal.bind_value, LLVM.SemVal.isRefinedBy_self])")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
            elif bridge=='bycases':
                conds=[]
                for (sv,c,_,_,_) in active_sels:
                    cs=bool_expr(c, sctx)
                    if cs not in conds: conds.append(cs)
                for (sv,c,_,_,_) in tsel_nodes:
                    cs=bool_expr(c, tctx)
                    if cs not in conds: conds.append(cs)
                chain=" <;> ".join(f"by_cases hS{i+1} : {cs} = true" for i,cs in enumerate(conds))
                mop=(", ".join(fw_mopups)+", ") if fw_mopups else ""
                _ob=("ofBool_one_iff, " if not fwmop else
                     f"ofBool_one_iff, {name}_ofBool_zero_iff, "
                     f"{name}_one_eq_ofBool_iff, {name}_zero_eq_ofBool_iff, ")
                simps=(f"[InstCombine.LLVM.Ty.width, {_ob}{mop}LLVM.SemVal.isRefinedBy_self]"
                       if retype else "[InstCombine.LLVM.Ty.width]")
                if not conds:


                    mop2=(", "+", ".join(fw_mopups)) if fw_mopups else ""
                    out.extend(_div_or_rw(p)); out.append(f"{p}have hv := {hv_call}")
                    out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                    out.append(f"{p}  constructor")
                    out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv{mop2}] <;> rfl)")
                    out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
                    return
                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.extend(_div_or_rw(p+"      ")); out.append(f"{p}      have hv := {hv_call}")
                out.append(f"{p}      {chain} <;> simp_all {simps})")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")
            else:
                out.extend(_div_or_rw(p)); out.append(f"{p}have hv := {hv_call}")
                if puretgt:


                    out.append(f"{p}simp only [Id.pure_eq', Id.bind_eq', Id.map_eq', id_eq]")
                    vlist=", ".join([f"{a}Var" for a,_ in args] + [f"h{a}" for a,_ in args])
                    out.append(f"{p}simp [{vlist}, hv, Ctxt.Valuation.cons_last]")
                    out.append(f"{p}all_goals")
                    out.append(f"{p}  first")
                    out.append(f"{p}  | exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                    out.append(f"{p}      constructor")
                    out.append(f"{p}      · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp)")
                    out.append(f"{p}      · exact HVector.nil_isRefinedBy_nil)")
                    out.append(f"{p}  | rfl")
                    return
                out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                out.append(f"{p}  constructor")
                if retype:


                    mop=(", "+", ".join(fw_mopups)) if fw_mopups else ""
                    out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv{mop}] <;> rfl)")
                else:
                    out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by simp [hv])")
                out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")

        hcond_all = [_hc(k) for k in range(len(sasms)) if pred_specs[k][0]!='skip']

        def emit_value_core(vars_so_far, hyps_so_far, indent, tail):
            p=" "*indent
            if disjoint_mode:
                out.append(f"{p}cases hd : ({dA} &&& {dB} == 0#{wv})")
                out.append(f"{p}· have hne : ¬ ({dA} &&& {dB} = 0#{wv}) := by simpa using hd")
                out.append(simp_line(names, indent+2, vars_so_far, hyps_so_far+["hne"], opcodes))
                out.append(poison_ret_leaf(indent+2, 'simp'))
                pp=prop_pred(sasms[0], sctx)
                if pp is not None:
                    out.append(f"{p}· have hpre : {pp} := by simpa using hcond")
                else:
                    out.append(f"{p}· have hpre := hcond")
                out.append(f"{p}  have hdis : {dA} &&& {dB} = 0#{wv} := by simpa using hd")
                out.append(f"{p}  have hval : {src_goal} = {tgt_goal} :=")
                out.append(f"{p}    {name}_value{wvapp} {callargs} hpre hdis")
                out.append(simp_line(names, indent+2, vars_so_far, hyps_so_far+["hdis","hval"], opcodes))
                out.append(poison_ret_leaf(indent+2, 'simp'))
            elif use_seqflag:


                _tot_seq=sum(len(ovf_preds(op_,fl_)) for (_,op_,fl_,_) in flags)
                def _seq_name(j):
                    return 'hov' if _tot_seq==1 else f"hov{j+1}"
                def rec_f(fi, pj, hj, ind, hyps, hovtail, hoisted):
                    q=" "*ind
                    if fi==len(flags):
                        out.append(simp_line(names, ind, vars_so_far, hyps, opcodes))
                        close_leaf(ind, hv_call_args(hcond_all+tail+hovtail))
                        return
                    (vv,op,fl,ops)=flags[fi]
                    if pj==0 and flagsel is not None and vv==fselowner and not hoisted:
                        svv,cvar=flagsel
                        cs=bool_expr(cvar, sctx)
                        out.append(f"{q}by_cases hfs : {cs} = true")
                        for branchv in (sdefs[svv][1][1], sdefs[svv][1][2]):
                            out.append(f"{q}· -- {('then' if branchv==sdefs[svv][1][1] else 'else')} branch of the flag-feeding select")
                            sctx.resolved[svv]=branchv
                            rec_f(fi, 0, hj, ind+2, hyps+["hfs"], list(hovtail), True)
                            del sctx.resolved[svv]
                        return
                    preds=ovf_preds(op, fl)
                    if pj==len(preds):
                        rec_f(fi+1, 0, hj, ind, hyps, hovtail, hoisted)
                        return
                    a=bv_expr(ops[0],sctx); b=bv_expr(ops[1],sctx)
                    hn=_seq_name(hj)
                    out.append(f"{q}cases {hn} : {a}.{preds[pj]} {b}")
                    out.append(f"{q}· -- no overflow: continue")
                    arg = f"(by simpa [hfs] using {hn})" if hoisted else hn
                    rec_f(fi, pj+1, hj+1, ind+2, hyps+[hn], hovtail+[arg], hoisted)
                    out.append(f"{q}· " + simp_line(names,0,vars_so_far,
                                hyps+[hn,"ofBool_one_iff"],opcodes).strip())
                    out.append(poison_ret_leaf(ind+2, pleaf_style))
                rec_f(0, 0, 0, indent, list(hyps_so_far)+["ofBool_one_iff"], [], False)
            elif len(flags)>=2:
                out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
                out.append(f"{p}apply ImmediateUBOr.IsRefinedBy.bothValues")
                out.append(f"{p}constructor")
                out.append(f"{p}· apply ImmediateUBOr.IsRefinedBy.bothValues")
                hs=[f"hov{i+1}" for i in range(len(flags))]
                exprs=[]
                for (vv,op,fl,ops) in flags:
                    a=bv_expr(ops[0],sctx); b=bv_expr(ops[1],sctx)
                    exprs.append(f"{a}.{OVF[(op,fl)]} {b}")
                def nest(k):
                    lines=[f"cases {hs[k]} : {exprs[k]}"]
                    if k==len(flags)-1:
                        lines.append(f"· simp only [{', '.join(hs)}, Bool.false_eq_true, if_false,")
                        lines.append(f"    LLVM.SemVal.bind_value]")
                        lines.append(f"  rw [{hv_call_args(hcond_all+tail+hs)}]")
                        lines.append(f"  exact LLVM.SemVal.isRefinedBy_self _")
                    else:
                        sub=nest(k+1)
                        lines.append("· "+sub[0])
                        lines += ["  "+x for x in sub[1:]]
                    lines.append(f"· simp [{', '.join(hs[:k+1])}]")
                    return lines
                q=" "*(indent+2)
                out.extend(q+x for x in nest(0))
                out.append(f"{p}· exact HVector.nil_isRefinedBy_nil")
            elif len(flags)==1 and flagsel is not None:


                (vv,op,fl,ops)=flags[0]
                svv,cvar=flagsel
                cs=bool_expr(cvar, sctx)
                out.append(f"{p}by_cases hfs : {cs} = true")
                for branchv in (sdefs[svv][1][1], sdefs[svv][1][2]):
                    sctx.resolved[svv]=branchv
                    a=bv_expr(ops[0],sctx); b=bv_expr(ops[1],sctx)
                    del sctx.resolved[svv]
                    pred=f"{a}.{OVF[(op,fl)]} {b}"
                    out.append(f"{p}· cases hov : {pred}")
                    out.append(f"{p}  · " + simp_line(names,0,vars_so_far,
                                hyps_so_far+["hfs","hov","ofBool_one_iff"],opcodes).strip())
                    close_leaf(indent+4, hv_call_args(hcond_all+tail+["(by simpa [hfs] using hov)"]))
                    out.append(f"{p}  · " + simp_line(names,0,vars_so_far,
                                hyps_so_far+["hfs","hov","ofBool_one_iff"],opcodes).strip())
                    out.append(poison_ret_leaf(indent+4, pleaf_style))
            elif len(flags)==1:
                (vv,op,fl,ops)=flags[0]
                a=bv_expr(ops[0],sctx); b=bv_expr(ops[1],sctx)
                pred=f"{a}.{OVF[(op,fl)]} {b}"
                out.append(f"{p}cases hov : {pred}")
                out.append(f"{p}· " + simp_line(names,0,vars_so_far,hyps_so_far+["hov"],opcodes).strip())
                close_leaf(indent+2, hv_call_args(hcond_all+tail+["hov"]))
                out.append(f"{p}· " + simp_line(names,0,vars_so_far,hyps_so_far+["hov"],opcodes).strip())
                out.append(poison_ret_leaf(indent+2, pleaf_style))
            else:
                out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
                close_leaf(indent, hv_call_args(hcond_all+tail))

        def fw_chain_core(vars_so_far, hyps_so_far, indent, tail):

            base_hyps=list(hyps_so_far)+(["ofBool_one_iff"] if _obdef else [])
            def unres_hyp(hn):
                for h,l in zip(hyp_names, hyp_lines):
                    if h==hn:
                        return l.strip()[1:-1].split(' : ',1)[1]
                return None
            def emit_res(ind, hyps, res):


                if res is not None:
                    sctx.resolved[res[0]]=res[1]; tctx.resolved[res[0]]=res[1]
                try:
                    def bridge(hn, holehyp_hn, resolved_stmt):
                        if res is None: return hn
                        uh=unres_hyp(holehyp_hn)
                        return hn if uh==resolved_stmt else f"(by simpa [hfs] using {hn})"
                    steps=[]; argmap={}

                    for (hn,vv) in _fpn:
                        d2=sdefs[vv]
                        pr=ovf_preds(d2[1], d2[3])[0]
                        cp=f"{dot_recv(bv_expr(d2[2][0],sctx))}.{pr} {bv_expr(d2[2][1],sctx)}"
                        sp=f"{dot_recv(bv_expr(d2[2][0],sctx,True))}.{pr} {bv_expr(d2[2][1],sctx,True)} = false"
                        steps.append(('cases', hn, cp))
                        argmap[hn]=bridge(hn, hn, sp)

                    for (hn,_u) in leaf_divs:
                        dop2,dops2,dw2=leaf_div_src[hn]
                        up=div_ubp(dop2, bv_expr(dops2[0],sctx,True),
                                   bv_expr(dops2[1],sctx,True), dw2)
                        steps.append(('bydiv', hn, up))
                        argmap[hn]=bridge(hn, hn, f"¬ ({up})")

                    for (hn,vv) in shl_rows:
                        eq=shl_noovf_eq(vv, sctx, True)
                        steps.append(('byshl', hn, eq))
                        argmap[hn]=bridge(hn, hn, eq)


                    src_res={shl_noovf_eq(vv, sctx, True): hn for (hn,vv) in shl_rows}
                    for (hn,tvv) in tgt_shl_rows:
                        teq=shl_noovf_eq(tvv, tctx, True)
                        if teq in src_res:

                            argmap[hn]=bridge(src_res[teq], hn, teq)
                        else:
                            steps.append(('bytgt', hn, teq))
                            argmap[hn]=bridge(hn, hn, teq)
                finally:
                    if res is not None:
                        del sctx.resolved[res[0]]; del tctx.resolved[res[0]]
                ordered=[hn for hn,_ in leaf_divs] + [hn for hn,_ in _fpn] \
                        + [hn for hn,_ in shl_rows] + [hn for hn,_ in tgt_shl_rows]
                def go2(i, hyps2, ind2):
                    p2=" "*ind2
                    if i==len(steps):
                        out.append(simp_line(names, ind2, vars_so_far, hyps2, opcodes))
                        close_leaf(ind2, hv_call_args(
                            hcond_all+tail+[argmap[h] for h in ordered]))
                        return
                    kind,hn,pp=steps[i]
                    if kind=='cases':
                        out.append(f"{p2}cases {hn} : {pp}")
                        out.append(f"{p2}· -- {hn}: no overflow, the flagged op is a value")
                        go2(i+1, hyps2+[hn], ind2+2)
                        out.append(f"{p2}· -- overflow: flagged op poison → src return poison")
                        out.append(simp_line(names, ind2+2, vars_so_far, hyps2+[hn], opcodes))
                        out.append(poison_ret_leaf(ind2+2, 'r2'))
                        return
                    if kind=='bydiv':
                        out.append(f"{p2}by_cases {hn} : {pp}")
                        out.append(f"{p2}· -- division UB: src return value is value-level immediateUB")
                        out.append(simp_line(names, ind2+2, vars_so_far, hyps2, opcodes))
                        out.append(f"{p2}  simp [{hn}]")
                        out.append(f"{p2}  exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                        out.append(f"{p2}    constructor")
                        out.append(f"{p2}    · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft")
                        out.append(f"{p2}    · exact HVector.nil_isRefinedBy_nil)")
                        out.append(f"{p2}· -- {hn}: division defined")
                        go2(i+1, hyps2+[hn], ind2+2)
                        return
                    if kind=='byshl':
                        out.append(f"{p2}by_cases {hn} : {pp}")
                        out.append(f"{p2}· -- {hn}: no shl overflow")
                        go2(i+1, hyps2+[hn], ind2+2)
                        out.append(f"{p2}· -- shl overflow: flagged shl poison → src return poison")
                        out.append(simp_line(names, ind2+2, vars_so_far, hyps2+[hn], opcodes))
                        out.append(poison_ret_leaf(ind2+2, 'r2'))
                        return

                    hso_local=shl_rows[0][0]
                    ocall=" ".join([f"{name}_ovfcover {callargs}"]
                                   + (['hpc'] if psel_info else [])
                                   + predguard_names + hcond_all
                                   + [g for g,_,_ in leafguard_names]
                                   + ["hfs", hn, hso_local])
                    out.append(f"{p2}by_cases {hn} : {pp}")
                    out.append(f"{p2}· -- {hn}: the tgt shl does not overflow either")
                    go2(i+1, hyps2+[hn], ind2+2)
                    out.append(f"{p2}· -- tgt overflows while the src does not: typed-hole exclusion")
                    out.append(f"{p2}  exfalso")
                    out.append(f"{p2}  exact {ocall}")
                go2(0, list(hyps), ind)
            p=" "*indent
            if flagsel is not None:
                svv0,cvar0=flagsel
                cs=bool_expr(cvar0, sctx)
                out.append(f"{p}by_cases hfs : {cs} = true")
                for pol,branchv in (('then', sdefs[svv0][1][1]), ('else', sdefs[svv0][1][2])):
                    out.append(f"{p}· -- {pol} branch of the flag-feeding select")
                    emit_res(indent+2, base_hyps+["hfs"], (svv0, branchv))
            else:
                emit_res(indent, base_hyps, None)

        def emit_value_leaf(vars_so_far, hyps_so_far, indent):


            _ldivs = [] if (fw_hoist or fwchain) else leaf_divs
            _tdivs = [] if (fw_hoist or fwchain) else tgt_divs
            tail=[hn for hn,_,_ in fw_hoist]
            def go(gi, ei, di, ti, xi, hyps, ind):
                p=" "*ind
                if gi < len(leafguard_names):
                    hn,amt,gw=leafguard_names[gi]
                    out.append(f"{p}by_cases {hn} : {guard_prop(amt, gw)}")
                    out.append(f"{p}· -- oversized shift: src return is poison")
                    out.append(simp_line(names, ind+2, vars_so_far, hyps+[hn], opcodes))
                    out.append(poison_ret_leaf(ind+2, pleaf_style))
                    out.append(f"{p}· -- {hn}: shift amount in range")
                    tail.append(hn)
                    go(gi+1, ei, di, ti, xi, hyps+[hn], ind+2)
                    return
                if ei < len(exfguard_names):
                    hn,amt,gw=exfguard_names[ei]
                    out.append(f"{p}by_cases {hn} : {guard_prop(amt, gw)}")
                    out.append(f"{p}· -- impossible: the extra width hypothesis rules this out")
                    out.append(f"{p}  exfalso")
                    out.append(f"{p}  have hpw : {wv} < 2 ^ {wv} := Nat.lt_two_pow_self")
                    out.append(f"{p}  rw [BitVec.le_def] at {hn}")
                    out.append(f"{p}  simp only [BitVec.toNat_ofNat] at {hn}")
                    out.append(f"{p}  rw [Nat.mod_eq_of_lt hpw, Nat.mod_eq_of_lt (by omega)] at {hn}")
                    out.append(f"{p}  omega")
                    out.append(f"{p}· -- {hn}: shift amount in range")
                    tail.append(hn)
                    go(gi, ei+1, di, ti, xi, hyps+[hn], ind+2)
                    return
                if di < len(_ldivs):


                    hn,ubp=_ldivs[di]
                    _div_or_guard(hn, ubp); out.append(f"{p}by_cases {hn} : {ubp}")
                    out.append(f"{p}· -- division UB: src return value is value-level immediateUB")
                    out.append(simp_line(names, ind+2, vars_so_far, hyps, opcodes))
                    out.append(f"{p}  simp [{hn}]")
                    out.append(f"{p}  exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                    out.append(f"{p}    constructor")
                    out.append(f"{p}    · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft")
                    out.append(f"{p}    · exact HVector.nil_isRefinedBy_nil)")
                    out.append(f"{p}· -- {hn}: division defined")
                    tail.append(hn)
                    go(gi, ei, di+1, ti, xi, hyps+[hn], ind+2)
                    return
                if ti < len(_tdivs):
                    hn,ubp=_tdivs[ti]
                    _div_or_guard(hn, ubp); out.append(f"{p}by_cases {hn} : {ubp}")
                    if has_exact:


                        _h2=" ".join([f"{name}_tgtub{ti+1}{wvapp}{eapp} {callargs}"]
                                     + predguard_names + hcond_all + tail + [hn])
                        out.append(f"{p}· -- tgt-side division UB: excluded by the assumes (typed hole)")
                        out.append(f"{p}  exfalso")
                        out.append(f"{p}  exact {_h2}")
                    else:
                        out.append(f"{p}· -- tgt-side division UB: excluded by the assumes/guards")
                        out.append(f"{p}  exfalso")
                        out.append(f"{p}  simp_all")
                    out.append(f"{p}· -- {hn}: tgt division defined")
                    newh=[hn]
                    if has_exact and ' ∨ ' in ubp:


                        A2,B2=ubp.split(' ∨ ',1)
                        out.append(f"{p}  have {hn}a : ¬ ({A2}) := fun h2 => {hn} (Or.inl h2)")
                        out.append(f"{p}  have {hn}b : ¬ {B2} := fun h2 => {hn} (Or.inr h2)")
                        newh += [f"{hn}a", f"{hn}b"]
                    tail.append(hn)
                    go(gi, ei, di, ti+1, xi, hyps+newh, ind+2)
                    return
                if xi < len(exact_rows):


                    hn,remp=exact_rows[xi]
                    out.append(f"{p}by_cases {hn} : {remp}")
                    out.append(f"{p}· -- {hn}: zero remainder — the exact division is a value")
                    tail.append(hn)
                    go(gi, ei, di, ti, xi+1, hyps+[hn], ind+2)
                    out.append(f"{p}· -- nonzero remainder: the exact flag makes the src value poison")
                    out.append(simp_line(names, ind+2, vars_so_far, hyps+[hn], opcodes))
                    out.append(poison_ret_leaf(ind+2, pleaf_style))
                    return
                if rdis and 'hdis' not in tail:


                    out.append(f"{p}cases hd : ({dA} &&& {dB} == 0#{wv})")
                    out.append(f"{p}· have hne : ¬ ({dA} &&& {dB} = 0#{wv}) := by simpa using hd")
                    out.append(simp_line(names, ind+2, vars_so_far, hyps+["hne"], opcodes))
                    out.append(poison_ret_leaf(ind+2, pleaf_style))
                    out.append(f"{p}· have hdis : {dA} &&& {dB} = 0#{wv} := by simpa using hd")
                    tail.append('hdis')
                    go(gi, ei, di, ti, xi, hyps+["hdis"], ind+2)
                    return
                if fwchain:
                    fw_chain_core(vars_so_far, hyps, ind, list(tail))
                else:
                    emit_value_core(vars_so_far, hyps, ind, list(tail))
            go(0, 0, 0, 0, 0, list(hyps_so_far), indent)

        def dummy_leaf(indent, hyps_so_far, vars_so_far, dummies):
            p=" "*indent
            out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
            ca=" ".join((f"(0#{wv})" if a in dummies else ren[a]) for a in binder_args)
            parts=[]
            if hole_h1 is not None: parts.append("h1")
            parts += predguard_names + hcond_all
            hv_call=" ".join([f"{name}_value{wvapp}{eapp} {ca}"]+parts)
            conds=[]
            for (sv,c,_,_,_) in active_sels:
                cs=bool_expr(c, sctx)
                if cs not in conds: conds.append(cs)
            for (sv,c,_,_,_) in tsel_nodes:
                cs=bool_expr(c, tctx)
                if cs not in conds: conds.append(cs)
            chain=" <;> ".join(f"by_cases hS{i+1} : {cs} = true" for i,cs in enumerate(conds))
            out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.append(f"{p}  constructor")
            out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.extend(_div_or_rw(p+"      ")); out.append(f"{p}      have hv := {hv_call}")
            out.append(f"{p}      {chain} <;> simp_all [InstCombine.LLVM.Ty.width, ofBool_one_iff, "
                       f"LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])")
            out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")

        def boa_poison_leaf(indent, vars_so_far, hyps_so_far):
            p=" "*indent
            boa, spol, scond, srcpick, tgtpick = poisoncover
            out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
            pcargs=[ren[a] for a in binder_args if a != boa]
            pccall=" ".join([f"{name}_poisoncover{wvapp}{eapp}"] + pcargs
                            + predguard_names + hcond_all + ["hbq"])
            dumargs=" ".join((f"(0#{wv})" if a==boa else ren[a]) for a in binder_args)
            hvcall=" ".join([f"{name}_value{wvapp}{eapp} {dumargs}"]
                            + predguard_names + hcond_all + (["hdis0"] if rdis else []))
            leaflist=(f"ofBool_one_iff, {name}_ite_semval_value, {name}_semval_bind_poison, "
                      f"InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, "
                      f"LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy")
            def _sa(q):


                return (f"{q}simp_all [{leaflist}] <;>\n"
                        f"{q}  exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                        f"{q}    constructor\n"
                        f"{q}    · exact ImmediateUBOr.IsRefinedBy.bothValues (by\n"
                        f"{q}        first\n"
                        f"{q}        | exact LLVM.SemVal.poison_isRefinedBy _\n"
                        f"{q}        | exact LLVM.SemVal.isRefinedBy_self _\n"
                        f"{q}        | simp [LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])\n"
                        f"{q}    · exact HVector.nil_isRefinedBy_nil)")
            if rdis:


                pinned=[]
                for (sv,c,a2,b2,_) in sel_nodes:
                    ta=[]; args_in(a2, sdefs, argw, ta)
                    ea=[]; args_in(b2, sdefs, argw, ea)
                    if boa in ta: sctx.resolved[sv]=b2; pinned.append(sv)
                    elif boa in ea: sctx.resolved[sv]=a2; pinned.append(sv)
                RESA=bv_expr(sdis[0][1][0], sctx, True); RESB=bv_expr(sdis[0][1][1], sctx, True)
                for sv in pinned: del sctx.resolved[sv]
                _oldren=ren[boa]; ren[boa]=f"0#{wv}"
                DUMA=bv_expr(sdis[0][1][0], sctx, True); DUMB=bv_expr(sdis[0][1][1], sctx, True)
                ren[boa]=_oldren
            out.append(f"{p}by_cases hbq : {tgtpick}")
            out.append(f"{p}· -- tgt picks the poisoned arg: hole 2 -> src picks it too -> poison")
            out.append(f"{p}  have hbp := {pccall}")
            out.append(_sa(p+"  "))
            def emit_avoid(q):
                if rdis:
                    out.append(f"{q}cases hd : ({RESA} &&& {RESB} == 0#{wv})")
                    out.append(f"{q}· have hne : ¬ ({RESA} &&& {RESB} = 0#{wv}) := by simpa using hd")
                    out.append(_sa(q+"  "))
                    out.append(f"{q}· have hdis0 : {DUMA} &&& {DUMB} = 0#{wv} := by simpa [hbp] using hd")
                    out.append(f"{q}  have hv := {hvcall}")
                    out.append(_sa(q+"  "))
                else:
                    out.append(f"{q}have hv := {hvcall}")
                    out.append(_sa(q))
            out.append(f"{p}· by_cases hbp : {scond}")
            if spol=='else':
                out.append(f"{p}  · -- src avoids the poisoned branch: dummy value hole")
                emit_avoid(f"{p}    ")
                out.append(f"{p}  · -- src picks the poisoned branch too: poison ⊑ value")
                out.append(_sa(p+"    "))
            else:
                out.append(f"{p}  · -- src picks the poisoned branch too: poison ⊑ value")
                out.append(_sa(p+"    "))
                out.append(f"{p}  · -- src avoids the poisoned branch: dummy value hole")
                emit_avoid(f"{p}    ")

        def fw_dummy2_leaf(indent, vars_so_far, hyps_so_far):
            p=" "*indent
            boa, srcpick_, tgtpick_ = fw_dummy2
            out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
            parts = predguard_names + hcond_all + [hn for hn,_,_ in fw_hoist]
            def _dum(v):
                return " ".join((f"({v}#{wv})" if a==boa else ren[a]) for a in binder_args)
            hv0=" ".join([f"{name}_value {_dum(0)}"]+parts)
            hv1=" ".join([f"{name}_value {_dum(1)}"]+parts)
            out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.append(f"{p}  constructor")
            out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.append(f"{p}      have hv0 := {hv0}")
            out.append(f"{p}      have hv1 := {hv1}")
            out.append(f"{p}      by_cases hbq : {tgtpick_} <;> by_cases hbp : {srcpick_} <;>")
            out.append(f"{p}        simp_all [ofBool_one_iff, {name}_ite_semval_value, "
                       f"InstCombine.LLVM.Ty.width, LLVM.SemVal.bind_value, "
                       f"LLVM.SemVal.isRefinedBy_self, LLVM.SemVal.poison_isRefinedBy])")
            out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")

        def ub_split_alt(pp, vars_so_far, hyps_so_far, hn):
            if not rest:
                return []
            hu=[f"h{a}u" for a in rest]
            cs=[f"{pp}  | (cases {hu[0]} : V {rest[0]}Var <;>"]
            cs+=[f"{pp}     cases {h} : V {a}Var <;>" for a,h in zip(rest[1:], hu[1:])]
            _s=simp_line(names, 0, vars_so_far+[f"{a}Var" for a in rest],
                         hyps_so_far+hu+[hn], opcodes).strip()
            cs+=[f"{pp}     {_s} <;>",
                 f"{pp}     refine ImmediateUBOr.IsRefinedBy.bothValues ?_ <;>",
                 f"{pp}     constructor <;>",
                 f"{pp}     first",
                 f"{pp}     | exact ImmediateUBOr.IsRefinedBy.immediateUBLeft",
                 f"{pp}     | exact HVector.nil_isRefinedBy_nil",
                 f"{pp}     | (refine ImmediateUBOr.IsRefinedBy.bothValues ?_",
                 f"{pp}        first",
                 f"{pp}        | exact LLVM.SemVal.poison_isRefinedBy _",
                 f"{pp}        | (rw [LLVM.IntW.isRefinedBy_iff]; "
                 f"exact LLVM.SemVal.poison_isRefinedBy _)",
                 f"{pp}        | simp [LLVM.IntW.instRefinement]))"]
            return cs

        def rec_rest(j, vars_so_far, hyps_so_far, indent, any_poison, withform=False, dummies=()):
            p=" "*indent
            if j==len(rest):
                if any_poison:
                    out.append(simp_line(names, indent, vars_so_far, hyps_so_far, opcodes))
                    out.append(poison_ret_leaf(indent, pleaf_style))
                elif dummies:
                    dummy_leaf(indent, hyps_so_far, vars_so_far, dummies)
                else:
                    emit_value_leaf(vars_so_far, hyps_so_far, indent)
                return
            a=rest[j]; b=ren[a]


            pcase = (f"{p}| poison =>", f"{p}| value {b} =>") if withform else \
                    (f"{p}case poison =>", f"{p}case value {b} =>")
            out.append(f"{p}cases h{a} : V {a}Var" + (" with" if withform else ""))
            out.append(pcase[0])
            if retype and a not in binder_args and a not in selcond_i1:


                rec_rest(j+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], indent+2,
                         any_poison, False, dummies)
            elif poisoncover is not None and a == poisoncover[0] and not any_poison:

                boa_poison_leaf(indent+2, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"])
            elif fw_dummy2 is not None and a == fw_dummy2[0] and not any_poison:

                fw_dummy2_leaf(indent+2, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"])
            elif a in bo_args and argw[a]==wv and not any_poison:

                rec_rest(j+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], indent+2,
                         any_poison, False, dummies+(a,))
            elif (argw[a]=='1' or not product) and not any(
                    r in divargs_rest for r in rest[j+1:]):


                out.append(simp_line(names, indent+2, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], opcodes))
                out.append(poison_ret_leaf(indent+2, pleaf_style))
            else:


                rec_rest(j+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], indent+2, True, withform)
            out.append(pcase[1])
            if retype:
                out.append(f"{p}  change BitVec {argw[a]} at {b}")
            if argw[a]=='1' and a in selcond_i1 and not i1sym:
                out.append(f"{p}  by_cases h1 : {b} = 1#1")
                out.append(f"{p}  · " + simp_line(names,0,vars_so_far+[f"{a}Var"],hyps_so_far+[f"h{a}","h1"],opcodes).strip())
                out.append(trivial_value_leaf(indent+4))
                out.append(f"{p}  · -- {b} ≠ 1#1: selects on it resolve to their else branch")
                rec_rest(j+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}","h1"], indent+4, any_poison, True)
            else:
                rec_rest(j+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], indent+2, any_poison, withform, dummies)

        pred_guards_by_asm_local = {} if disjoint_mode else pred_guards_by_asm


        per_asm_args=[]
        seen_pa=set()
        for asm in sasms:
            tmp=[]; args_in(asm, sdefs, argw, tmp)
            mine=[a for a in tmp if a not in seen_pa]
            seen_pa.update(mine); per_asm_args.append(mine)

        def rec_assume_chain(k, ai, vars_so_far, hyps_so_far, indent, wf, hpc_done=False):
            p=" "*indent
            if k in psel_info and not hpc_done and ai == psel_info[k][2]:
                _pc=bool_expr(psel_info[k][0], sctx)
                out.append(f"{p}cases hpc : {_pc}")
                out.append(f"{p}· -- predicate-select cond false: short-circuits to the false constant")
                out.append(simp_line(names, indent+2, vars_so_far, hyps_so_far+["hpc"], opcodes))
                out.append(f"{p}  {UB}")
                out.append(f"{p}· -- predicate-select cond true")
                rec_assume_chain(k, ai, vars_so_far, hyps_so_far+["hpc"], indent+2, True,
                                 hpc_done=True)
                return
            if k==len(sasms):
                _dfw_prior=[]
                for hn,ubp,is_tgt in fw_hoist:


                    _div_or_guard(hn, ubp); out.append(f"{p}by_cases {hn} : {ubp}")
                    if is_tgt and divflagfw:


                        _dfw_ca=" ".join(ren[a] for a in binder_args if a not in rest)
                        _ti=len(_dfw_prior)+1
                        _hcall=" ".join([f"{name}_tgtub{_ti} {_dfw_ca}"]
                                        + predguard_names + hcond_all + _dfw_prior + [hn])
                        out.append(f"{p}· -- tgt-side division UB: excluded by the assumes (typed hole)")
                        out.append(f"{p}  exfalso")
                        out.append(f"{p}  exact {_hcall}")
                        _dfw_prior.append(hn)
                    elif is_tgt:
                        out.append(f"{p}· -- tgt-side division UB: excluded by the assumes/guards")
                        out.append(f"{p}  exfalso")
                        out.append(f"{p}  simp_all")
                    else:


                        _sl = simp_line(names, indent+2, vars_so_far,
                                        hyps_so_far, opcodes).strip()
                        out.append(f"{p}· -- division UB: src return value is value-level immediateUB")
                        out.append(f"{p}  first")


                        out.append(f"{p}  | (exfalso; simp_all; done)")
                        out.extend(ub_split_alt(p, vars_so_far, hyps_so_far, hn))
                        out.append(f"{p}  | ({_sl}")
                        out.append(f"{p}     simp [{hn}]")
                        out.append(f"{p}     exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                        out.append(f"{p}       constructor")
                        out.append(f"{p}       · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft")
                        out.append(f"{p}       · exact HVector.nil_isRefinedBy_nil))")
                    out.append(f"{p}· -- {hn}: division defined")
                    hyps_so_far=hyps_so_far+[hn]; indent+=2; p=" "*indent; wf=True
                rec_rest(0, vars_so_far, hyps_so_far, indent, False, withform=wf)
                return
            if ai < len(per_asm_args[k]):
                a=per_asm_args[k][ai]
                pcase=(f"{p}| poison =>", f"{p}| value {ren[a]} =>") if wf else \
                      (f"{p}case poison =>", f"{p}case value {ren[a]} =>")
                out.append(f"{p}cases h{a} : V {a}Var" + (" with" if wf else ""))
                out.append(pcase[0])
                out.append(simp_line(names, indent+2, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], opcodes))
                out.append(f"{p}  {UB}")
                out.append(pcase[1])
                if retype:
                    out.append(f"{p}  change BitVec {argw[a]} at {ren[a]}")
                rec_assume_chain(k, ai+1, vars_so_far+[f"{a}Var"], hyps_so_far+[f"h{a}"], indent+2, wf,
                                 hpc_done=hpc_done)
                return
            for (hn, amt, gw) in pred_guards_by_asm_local.get(k, []):
                out.append(f"{p}by_cases {hn} : {guard_prop(amt, gw)}")
                out.append(f"{p}· -- oversized shift feeds this assume: poison -> immediate UB")
                out.append(simp_line(names, indent+2, vars_so_far, hyps_so_far+[hn], opcodes))
                out.append(f"{p}  {UB}")
                out.append(f"{p}· -- {hn}: shift amount in range")
                hyps_so_far=hyps_so_far+[hn]; indent+=2; p=" "*indent; wf=True
            for (hn, ubp) in ({} if disjoint_mode else pred_div_by_asm).get(k, []):

                _div_or_guard(hn, ubp); out.append(f"{p}by_cases {hn} : {ubp}")
                out.append(f"{p}· -- division UB feeds this assume: src is immediate UB")
                out.append(simp_line(names, indent+2, vars_so_far, hyps_so_far+[hn], opcodes))
                out.append(f"{p}  {UB}")
                out.append(f"{p}· -- {hn}: division defined")
                hyps_so_far=hyps_so_far+[hn]; indent+=2; p=" "*indent; wf=True

            def _after_guards(hyps2, ind2, wf2):
                p2=" "*ind2
                if pred_specs[k][0]=='skip':


                    rec_assume_chain(k+1, 0, vars_so_far, hyps2, ind2, wf2)
                    return
                hc=_hc(k)
                if pred_specs[k][0]=='bv1':


                    out.append(f"{p2}by_cases {hc} : {pred_bools[k]} = 1#1")
                    out.append(f"{p2}· -- assume holds")
                    rec_assume_chain(k+1, 0, vars_so_far, hyps2+[hc], ind2+2, True)
                    out.append(f"{p2}· " + simp_line(names, 0, vars_so_far,
                                hyps2+[f"{name}_bv1_eq_zero _ {hc}",
                                       f"{name}_assume_zero_option"], opcodes).strip())
                    out.append(f"{p2}  {UB}")
                    return
                out.append(f"{p2}cases {hc} : {pred_bools[k]}")
                out.append(f"{p2}· " + simp_line(names, 0, vars_so_far, hyps2+[hc], opcodes).strip())
                out.append(f"{p2}  {UB}")
                out.append(f"{p2}· -- assume holds")
                rec_assume_chain(k+1, 0, vars_so_far, hyps2+[hc], ind2+2, wf2)


            fl_list = ({} if disjoint_mode else pred_flag_by_asm).get(k, [])
            def _emit_pf(fi, hyps2, ind2, wf2):
                if fi==len(fl_list):
                    _after_guards(hyps2, ind2, wf2)
                    return
                p2=" "*ind2
                hn,ovc,_ovs=fl_list[fi]
                out.append(f"{p2}cases {hn} : {ovc}")
                out.append(f"{p2}· -- {hn}: no overflow, the flagged op is a value")
                _emit_pf(fi+1, hyps2+[hn], ind2+2, wf2)
                out.append(f"{p2}· -- overflow: flagged op poison → assume of poison → immediate UB")
                out.append(simp_line(names, ind2+2, vars_so_far, hyps2+[hn], opcodes))
                out.append(f"{p2}  {UB}")
            _emit_pf(0, hyps_so_far, indent, wf)


        _order_sensitive = False


        _pred_plain = all(ps[0] == 'bool' for ps in pred_specs)


        _unified_ok = (not _order_sensitive)
        if os.environ.get('EMIT_DIAG') and not _unified_ok:
            _rz = []
            if _order_sensitive:
                _rz.append('order_sensitive:' + ','.join(
                    n for n, v in [('psel', psel_info), ('fw_hoist', fw_hoist),
                                   ('fwchain', fwchain), ('use_seqflag', use_seqflag),
                                   ('flagsel', flagsel is not None)] if v))
            if not _pred_plain:
                _rz.append('pred_nonbool:' + ','.join(
                    sorted({ps[0] for ps in pred_specs if ps[0] != 'bool'})))
            try:
                with open(os.environ['EMIT_DIAG'], 'a', encoding='utf-8') as _f:
                    _f.write('%s\t%s\n' % (name, ' | '.join(_rz)))
            except Exception:
                pass

        def emit_body_unified():
            _pg = pred_guards_by_asm_local
            _pd = {} if disjoint_mode else pred_div_by_asm
            _pf = {} if disjoint_mode else pred_flag_by_asm
            plan = []
            for k in range(len(sasms)):


                _psel_at = psel_info[k][2] if k in psel_info else None
                for ai, a in enumerate(per_asm_args[k]):
                    if ai == _psel_at:
                        plan.append(('psel', k))
                    plan.append(('parg', a))
                if _psel_at == len(per_asm_args[k]):
                    plan.append(('psel', k))
                for (hn, amt, gw) in _pg.get(k, []):
                    plan.append(('pshift', hn, amt, gw))
                for (hn, ubp) in _pd.get(k, []):
                    plan.append(('pdiv', hn, ubp))
                for (hn, ovc, _ovs) in _pf.get(k, []):
                    plan.append(('pflag', hn, ovc))
                plan.append(('pred', k))
            plan.append(('rest', None))

            def _arg(a, poison_close, vars_so_far, hyps_so_far, indent, wf, i):
                p = " " * indent
                ph = f"{p}| poison =>" if wf else f"{p}case poison =>"
                vh = f"{p}| value {ren[a]} =>" if wf else f"{p}case value {ren[a]} =>"
                out.append(f"{p}cases h{a} : V {a}Var" + (" with" if wf else ""))
                out.append(ph)
                poison_close(indent + 2, vars_so_far + [f"{a}Var"],
                             hyps_so_far + [f"h{a}"])
                out.append(vh)
                if retype:
                    out.append(f"{p}  change BitVec {argw[a]} at {ren[a]}")
                walk(i + 1, vars_so_far + [f"{a}Var"], hyps_so_far + [f"h{a}"],
                     indent + 2, wf)

            def walk(i, vars_so_far, hyps_so_far, indent, wf):
                p = " " * indent
                ev = plan[i]
                kind = ev[0]
                if kind == 'rest':


                    _vs, _hs, _ind, _wf = vars_so_far, hyps_so_far, indent, wf
                    _dfw = []
                    for (hn, ubp, is_tgt) in fw_hoist:
                        pp = " " * _ind
                        _div_or_guard(hn, ubp); out.append(f"{pp}by_cases {hn} : {ubp}")
                        if is_tgt and divflagfw:
                            _ca = " ".join(ren[a] for a in binder_args if a not in rest)
                            _hcall = " ".join(
                                [f"{name}_tgtub{len(_dfw)+1} {_ca}"]
                                + predguard_names + hcond_all + _dfw + [hn])
                            out.append(f"{pp}· -- tgt-side division UB: excluded by the assumes (typed hole)")
                            out.append(f"{pp}  exfalso")
                            out.append(f"{pp}  exact {_hcall}")
                            _dfw.append(hn)
                        elif is_tgt:
                            out.append(f"{pp}· -- tgt-side division UB: excluded by the assumes/guards")
                            out.append(f"{pp}  exfalso")
                            out.append(f"{pp}  simp_all")
                        else:


                            _sl = simp_line(names, _ind + 2, _vs, _hs,
                                            opcodes).strip()
                            out.append(f"{pp}· -- division UB: src return value is value-level immediateUB")
                            out.append(f"{pp}  first")
                            out.append(f"{pp}  | (exfalso; simp_all; done)")
                            out.extend(ub_split_alt(pp, _vs, _hs, hn))
                            out.append(f"{pp}  | ({_sl}")
                            out.append(f"{pp}     simp [{hn}]")
                            out.append(f"{pp}     exact ImmediateUBOr.IsRefinedBy.bothValues (by")
                            out.append(f"{pp}       constructor")
                            out.append(f"{pp}       · exact ImmediateUBOr.IsRefinedBy.immediateUBLeft")
                            out.append(f"{pp}       · exact HVector.nil_isRefinedBy_nil))")
                        out.append(f"{pp}· -- {hn}: division defined")
                        _hs = _hs + [hn]; _ind += 2; _wf = True
                    rec_rest(0, _vs, _hs, _ind, False, withform=_wf)
                    return
                if kind == 'psel':
                    _pc = bool_expr(psel_info[ev[1]][0], sctx)
                    out.append(f"{p}cases hpc : {_pc}")
                    out.append(f"{p}· -- predicate-select cond false: short-circuits to the false constant")
                    out.append(simp_line(names, indent + 2, vars_so_far, hyps_so_far + ["hpc"], opcodes))
                    out.append(f"{p}  {UB}")
                    out.append(f"{p}· -- predicate-select cond true")
                    walk(i + 1, vars_so_far, hyps_so_far + ["hpc"], indent + 2, True)
                    return
                if kind == 'parg':
                    def _cl(ind, vs, hs):
                        out.append(simp_line(names, ind, vs, hs, opcodes))
                        out.append(f"{' '*ind}{UB}")
                    _arg(ev[1], _cl, vars_so_far, hyps_so_far, indent, wf, i)
                    return
                if kind == 'pshift':
                    hn, amt, gw = ev[1], ev[2], ev[3]
                    out.append(f"{p}by_cases {hn} : {guard_prop(amt, gw)}")
                    out.append(f"{p}· -- oversized shift feeds this assume: poison -> immediate UB")
                    out.append(simp_line(names, indent + 2, vars_so_far, hyps_so_far + [hn], opcodes))
                    out.append(f"{p}  {UB}")
                    out.append(f"{p}· -- {hn}: shift amount in range")
                    walk(i + 1, vars_so_far, hyps_so_far + [hn], indent + 2, True)
                    return
                if kind == 'pdiv':
                    hn, ubp = ev[1], ev[2]
                    _div_or_guard(hn, ubp); out.append(f"{p}by_cases {hn} : {ubp}")
                    out.append(f"{p}· -- division UB feeds this assume: src is immediate UB")
                    out.append(simp_line(names, indent + 2, vars_so_far, hyps_so_far + [hn], opcodes))
                    out.append(f"{p}  {UB}")
                    out.append(f"{p}· -- {hn}: division defined")
                    walk(i + 1, vars_so_far, hyps_so_far + [hn], indent + 2, True)
                    return
                if kind == 'pflag':
                    hn, ovc = ev[1], ev[2]
                    out.append(f"{p}cases {hn} : {ovc}")
                    out.append(f"{p}· -- {hn}: no overflow, the flagged op is a value")
                    walk(i + 1, vars_so_far, hyps_so_far + [hn], indent + 2, wf)
                    out.append(f"{p}· -- overflow: flagged op poison → assume of poison → immediate UB")
                    out.append(simp_line(names, indent + 2, vars_so_far, hyps_so_far + [hn], opcodes))
                    out.append(f"{p}  {UB}")
                    return


                kk = ev[1]
                spec = pred_specs[kk][0]
                if spec == 'skip':


                    walk(i + 1, vars_so_far, hyps_so_far, indent, wf)
                    return
                hc = _hc(kk)
                if spec == 'bv1':


                    out.append(f"{p}by_cases {hc} : {pred_bools[kk]} = 1#1")
                    out.append(f"{p}· -- assume holds")
                    walk(i + 1, vars_so_far, hyps_so_far + [hc], indent + 2, True)
                    out.append(f"{p}· " + simp_line(names, 0, vars_so_far,
                               hyps_so_far + [f"{name}_bv1_eq_zero _ {hc}",
                                              f"{name}_assume_zero_option"],
                               opcodes).strip())
                    out.append(f"{p}  {UB}")
                    return

                out.append(f"{p}cases {hc} : {pred_bools[kk]}")
                out.append(f"{p}· " + simp_line(names, 0, vars_so_far,
                           hyps_so_far + [hc], opcodes).strip())
                out.append(f"{p}  {UB}")
                out.append(f"{p}· -- assume holds")
                walk(i + 1, vars_so_far, hyps_so_far + [hc], indent + 2, wf)

            walk(0, [], [], 2, False)


        if _unified_ok and os.environ.get('EMIT_SCHED', '1') != '0':
            emit_body_unified()
            _dl = os.environ.get('EMIT_SCHED_LOG')
            if _dl:
                try:
                    with open(_dl, 'a', encoding='utf-8') as _f:
                        _f.write(name + '\n')
                except Exception:
                    pass
        else:
            rec_assume_chain(0, 0, [], [], 2, False)
        L.append("\n".join(out))
        return "\n".join(L)+"\n"

    def bv1_goal(v, ctx):
        if v in ctx.argw:
            if ctx.argw[v]!='1': raise Unsupported("bv1 goal of non-i1 value")
            return ctx.ren.get(v, v)
        return bv_expr(v, ctx, stmt=True)

    def TY_of(w):
        return TY(w)


    def flatten_and(v, defs):
        d=defs.get(v)
        if d is not None and d[0]=='bin' and d[1]=='and' and d[4]=='1':
            return flatten_and(d[2][0], defs) + flatten_and(d[2][1], defs)
        return [v]

    def emit_f9(text, case, name, names, src_text, tgt_text, args, argw, idx, ren,
                sctx, tctx, sdefs, tdefs, sasm, sret, tret, srett,
                pflags, rflags, sel_nodes, tsel_nodes, opcodes, fw=False, wv='w',
                guards=(), tgtflags=()):
        n=len(args)
        if any(t=='1' for _,t in args): raise Unsupported("F9 with i1 arg")


        _flok = ('nsw','nuw','nswnuw') if (fw or tgtflags) else ('nsw','nuw')
        if any(fl not in _flok for (_,_,fl,_) in list(pflags)+list(rflags)+list(tgtflags)):
            raise Unsupported("nsw+nuw combined flag on the F9 path (no gate witness)")

        allflags=list(pflags)
        for f in rflags:
            if f[0] not in [x[0] for x in allflags]: allflags.append(f)

        allpreds=[]
        for (vv,op,fl,ops) in allflags:
            for _pr in ovf_preds(op, fl):
                allpreds.append((vv,op,_pr,ops))

        conj = flatten_and(sasm, sdefs)
        simple=[]; ors=[]
        for cvar in conj:
            d=sdefs.get(cvar)
            if d is None: raise Unsupported("F9: predicate conjunct is a raw arg")
            if d[0]=='bin' and d[1]=='or' and d[4]=='1':
                ors.append((bool_expr(d[2][0], sctx), bool_expr(d[2][1], sctx)))
            else:
                simple.append(bool_expr(cvar, sctx))
        if len(ors) > 1: raise Unsupported("F9: >1 or-conjunct in predicate")


        conds=[]
        for nodes,dd in ((sel_nodes,sdefs),(tsel_nodes,tdefs)):
            for (sv,c,_,_,_) in nodes:
                d=dd.get(c)
                if d is None or d[0]!='icmp': raise Unsupported("F9: select cond not an icmp")
        for (sv,c,_,_,_) in sel_nodes:
            cs=bool_expr(c, sctx)
            if cs not in conds: conds.append(cs)
        for (sv,c,_,_,_) in tsel_nodes:
            cs=bool_expr(c, tctx)
            if cs not in conds: conds.append(cs)


        goal_bv1x=False
        if srett=='1':
            try:
                src_goal=bool_expr(sret, sctx, stmt=True); tgt_goal=bool_expr(tret, tctx, stmt=True)
            except Unsupported:
                if not fw: raise
                src_goal=bv1_goal(sret, sctx); tgt_goal=bv1_goal(tret, tctx)
                goal_bv1x=True
        elif srett==wv:
            src_goal=bv_expr(sret, sctx, stmt=True); tgt_goal=bv_expr(tret, tctx, stmt=True)
        else:
            raise Unsupported(f"fixed-width return i{srett}")

        newf9 = fw and (bool(guards) or goal_bv1x or bool(conds)
                        or ('sext' in opcodes) or ('zext' in opcodes))


        if tgtflags and (ors or conds or goal_bv1x):
            raise Unsupported("F9 tgt-flag hole outside the supported row (or-conjunct/"
                              "selects/bv1-goal)")
        tf_specs=[]
        _tfseen=set()
        for (vv,op,fl,ops) in tgtflags:
            a=bv_expr(ops[0],tctx,stmt=True); b=bv_expr(ops[1],tctx,stmt=True)
            _parts=[f"({a}.{_pr} {b} = false)" for _pr in ovf_preds(op, fl)]
            stmt=" ∧ ".join(_parts) if len(_parts)>1 else _parts[0]
            if stmt in _tfseen: continue
            _tfseen.add(stmt)
            tf_specs.append((f"{name}_tgtflag{len(tf_specs)+1}", stmt, len(_parts)))


        f9bp = bool(tf_specs) or (fw and
                       any(fl=='nswnuw' for (_,_,fl,_) in list(pflags)+list(rflags)))

        binders=" ".join(f"({ren[a]} : BitVec {argw[a]})" for a,_ in args)
        callargs=" ".join(ren[a] for a,_ in args)

        ov_names=[]; hyp_lines=[]
        guard_names=[g for g,_,_ in guards]
        for (hn,key,gw) in guards:
            hyp_lines.append(f"    ({hn} : ¬ (BitVec.ofNat {gw} {gw} ≤ {key}))")
        for i,(vv,op,_pr,ops) in enumerate(allpreds):
            a=bv_expr(ops[0],sctx,stmt=True); b=bv_expr(ops[1],sctx,stmt=True)
            hn=f"hov{i+1}"; ov_names.append(hn)
            hyp_lines.append(f"    ({hn} : {a}.{_pr} {b} = false)")
        simple_names=[]
        for i,P in enumerate(simple):
            hn=f"hc{i+1}"; simple_names.append(hn)
            hyp_lines.append(f"    ({hn} : {P} = true)")
        if ors:
            A,B=ors[0]
            hyp_lines.append(f"    (hcond : ({A} = true) ∨ ({B} = true))")

        L=[]
        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax\n")
        L.append("open scoped InstCombine\nopen BitVec\n")
        L.append("-- ===== GIVEN (input) =====")
        L.append("-- [IR-DERIVED: src/tgt defs copied verbatim from the problem input]")
        L.append(src_text.strip()); L.append(""); L.append(tgt_text.strip()); L.append("")
        if newf9:

            L.append("private theorem ofBool_one_iff {b : Bool} : (BitVec.ofBool b = 1#1) ↔ (b = true) := by")
            L.append("  cases b <;> simp\n")
            L.append(f"private theorem {name}_ofBool_zero_iff {{b : Bool}} : (BitVec.ofBool b = 0#1) ↔ (b = false) := by")
            L.append("  cases b <;> simp\n")
            L.append(f"private theorem {name}_one_eq_ofBool_iff {{b : Bool}} : (1#1 = BitVec.ofBool b) ↔ (b = true) := by")
            L.append("  cases b <;> simp\n")
            L.append(f"private theorem {name}_zero_eq_ofBool_iff {{b : Bool}} : (0#1 = BitVec.ofBool b) ↔ (b = false) := by")
            L.append("  cases b <;> simp\n")
        if f9bp:


            L.append(f"private theorem {name}_semval_bind_poison {{α β : Type}} (x : LLVM.SemVal α) :")
            L.append(f"    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =")
            L.append(f"      (LLVM.SemVal.poison : LLVM.SemVal β) := by")
            L.append(f"  cases x <;> rfl\n")
            names=tuple(names[:2])+(f"{name}_semval_bind_poison",)+tuple(names[2:])
        L.append("-- ===== THE ONLY HOLE: core BitVec identity (LLM writes this) =====")
        if fw:
            L.append(f"private theorem {name}_value {binders}")
        else:

            L.append(f"private theorem {name}_value {{{wv} : Nat}} {binders}")
        for i,h in enumerate(hyp_lines):
            L.append(h + (" :" if i==len(hyp_lines)-1 else ""))
        L.append(f"    {src_goal} = {tgt_goal} := by")
        L.append("  sorry -- [HOLE: the genuinely-creative BitVec identity proof]\n")
        for _ki,(tfn,tfstmt,_np) in enumerate(tf_specs):

            L.append(f"-- ===== HOLE {_ki+2}: tgt flagged-op poison exclusion (LLM writes this) =====")
            L.append("-- [IR-DERIVED: statement built from syntax alone — 'the assumed predicate")
            L.append("--  and the src no-overflow facts exclude the tgt flagged op's poison']")
            if fw:
                L.append(f"private theorem {tfn} {binders}")
            else:
                L.append(f"private theorem {tfn} {{{wv} : Nat}} {binders}")
            for _hi,h in enumerate(hyp_lines):
                L.append(h + (" :" if _hi==len(hyp_lines)-1 else ""))
            L.append(f"    {tfstmt} := by")
            L.append("  sorry -- [HOLE: the tgt flagged op's poison exclusion (assumption-dependent)]\n")

        L.append("-- [IR-DERIVED: F9 case-tree — product poison prelude, overflow split")
        L.append("--  before predicate split, and/or component split with Or.inl/Or.inr]")
        L.append("set_option maxHeartbeats 8000000 in")
        if fw:
            L.append(f"theorem {name}_correct : {names[0]} ⊑ {names[1]} := by")
        else:
            L.append(f"theorem {name}_correct ({wv} : Nat) : {names[0]} {wv} ⊑ {names[1]} {wv} := by")
        L.append("  intro V")
        rev_types=[TY_of(argw[a]) for a,_ in reversed(args)]
        ctx_full="[" + ", ".join(rev_types) + "]"
        for a,_ in args:
            i=idx[a]
            if i==0:
                head="[" + ", ".join(rev_types[1:]) + "]"
                L.append(f"  let {a}Var : (Ctxt.ofList {ctx_full}).Var ({TY_of(argw[a])}) :=")
                L.append(f"    Ctxt.Var.last (Ctxt.ofList {head}) ({TY_of(argw[a])})")
            else:
                L.append(f"  let {a}Var : (Ctxt.ofList {ctx_full}).Var ({TY_of(argw[a])}) := ⟨{i}, by simp⟩")

        allvars=[f"{a}Var" for a,_ in args]
        allhyps=[f"h{a}" for a,_ in args]
        L.append("  " + " <;> ".join(f"cases h{a} : V {a}Var" for a,_ in args))
        L.append("  all_goals (")
        L.append("    try (")
        L.append(simp_line(names, 6, allvars, allhyps, opcodes))
        L.append("      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft))")
        L.append(f"  rename_i {' '.join(ren[a] for a,_ in args)}")
        if fw or tgtflags:


            for a,_ in args:
                L.append(f"  change BitVec {argw[a]} at {ren[a]}")

        out=[]
        def value_leaf(indent, hyps_so_far, or_witness):
            p=" "*indent
            out.append(simp_line(names, indent, allvars, hyps_so_far, opcodes))
            hv_args=" ".join([callargs]+guard_names+ov_names+simple_names
                             +([or_witness] if or_witness else []))
            chain=" <;> ".join(f"by_cases hS{i+1} : {cs} = true" for i,cs in enumerate(conds))
            hvline = (f"{p}      have hval := {name}_value {hv_args}" if fw else
                      f"{p}      have hval := {name}_value ({wv} := {wv}) {hv_args}")


            leaflist = ("InstCombine.LLVM.Ty.width" if not fw else
                        ", ".join(["InstCombine.LLVM.Ty.width"]+allvars))
            if newf9:


                leaflist = ", ".join(["InstCombine.LLVM.Ty.width"]+allvars
                                     +["ofBool_one_iff", f"{name}_ofBool_zero_iff",
                                       f"{name}_one_eq_ofBool_iff",
                                       f"{name}_zero_eq_ofBool_iff"])
            out.append(f"{p}exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.append(f"{p}  constructor")
            out.append(f"{p}  · exact ImmediateUBOr.IsRefinedBy.bothValues (by")
            out.append(hvline)
            for _ki,(tfn,_tfstmt,_np) in enumerate(tf_specs):


                _tfcall=f"{tfn} {hv_args}"
                if _np>1:
                    _pat=", ".join(f"htf{_ki+1}{chr(97+j)}" for j in range(_np))
                    out.append(f"{p}      obtain ⟨{_pat}⟩ := {_tfcall}")
                else:
                    out.append(f"{p}      have htf{_ki+1}a := {_tfcall}")
            if chain:
                out.append(f"{p}      {chain} <;> simp_all [{leaflist}])")
            else:
                out.append(f"{p}      simp_all [{leaflist}])")
            out.append(f"{p}  · exact HVector.nil_isRefinedBy_nil)")

        def rec(indent, hyps_so_far):
            p=" "*indent
            stage=len([h for h in hyps_so_far if h.startswith('hov')])
            if stage < len(allpreds):
                (vv,op,_pr,ops)=allpreds[stage]
                a=bv_expr(ops[0],sctx); b=bv_expr(ops[1],sctx)
                hn=f"hov{stage+1}"
                out.append(f"{p}cases {hn} : {a}.{_pr} {b}")
                out.append(f"{p}· -- no overflow")
                rec(indent+2, hyps_so_far+[hn])
                out.append(f"{p}· -- overflow: flagged op poison → assume poison → UB")
                out.append(simp_line(names, indent+2, allvars, hyps_so_far+[hn], opcodes))
                out.append(f"{p}  {UB}")
                return
            cstage=len([h for h in hyps_so_far if h.startswith('hc')])
            if cstage < len(simple):
                hn=f"hc{cstage+1}"
                out.append(f"{p}cases {hn} : {simple[cstage]}")
                out.append(f"{p}· -- conjunct false: assume fails")
                out.append(simp_line(names, indent+2, allvars, hyps_so_far+[hn], opcodes))
                out.append(f"{p}  {UB}")
                out.append(f"{p}· -- conjunct holds")
                rec(indent+2, hyps_so_far+[hn])
                return
            if ors:
                A,B=ors[0]
                out.append(f"{p}cases hp1 : {A} <;> cases hp2 : {B}")
                out.append(f"{p}· -- both disjuncts false: assume fails")
                out.append(simp_line(names, indent+2, allvars, hyps_so_far+["hp1","hp2"], opcodes))
                out.append(f"{p}  {UB}")
                for w_ in ("(Or.inr hp2)","(Or.inl hp1)","(Or.inl hp1)"):
                    out.append(f"{p}· -- assume holds")
                    value_leaf(indent+2, hyps_so_far+["hp1","hp2"], w_)
            else:
                value_leaf(indent, hyps_so_far, None)

        def rec_guards(gi, indent, hyps_so_far):
            p=" "*indent
            if gi==len(guards):
                rec(indent, hyps_so_far)
                return
            hn,key,gw=guards[gi]
            out.append(f"{p}by_cases {hn} : BitVec.ofNat {gw} {gw} ≤ {key}")
            out.append(f"{p}· -- oversized shift feeds this assume: poison -> immediate UB")
            out.append(simp_line(names, indent+2, allvars, hyps_so_far+[hn], opcodes))
            out.append(f"{p}  {UB}")
            out.append(f"{p}· -- {hn}: shift amount in range")
            rec_guards(gi+1, indent+2, hyps_so_far+[hn])

        rec_guards(0, 2, list(allhyps))
        L.append("\n".join(out))
        return "\n".join(L)+"\n"


    def detect(text: str) -> bool:
        try:
            if 'llvm.assume' not in text or '[llvm(' not in text:
                return False
            if re.search(r'def\s+\w*_src\w*\s*\(', text) is not None:
                return True


            return '[llvm()|' in text and len(FW_DEF_RE.findall(text)) == 2
        except Exception:
            return False

    def emit(text: str, case: str) -> dict:
        _DIV_OR_GUARDS.clear()

        try:
            if not detect(text):
                return {'status':'decline','reason':'not assume-family (detect=False)',
                        'shape':'','expected_sorries':0,'files':{}}
            content=emit_text(text, case)
            return {'status':'ok','reason':'','shape':'B2-assume',
                    'expected_sorries':content.count('sorry -- [HOLE'),
                    'files':{case+'.lean':content}}
        except Unsupported as e:
            return {'status':'decline','reason':str(e),'shape':'','expected_sorries':0,'files':{},
                    'fence_line': getattr(e, 'fence_line', None)}
        except Exception as e:
            return {'status':'decline','reason':f'internal:{type(e).__name__}:{e}',
                    'shape':'','expected_sorries':0,'files':{},
                    'fence_line': getattr(e, 'fence_line', None)}

    return types.SimpleNamespace(FAMILY=FAMILY, detect=detect, emit=emit)


def _build_shape_cfg():


    FAMILY = 'CFG'

    EMITTER_VERSION = 'cfg-1.0'


    _INT_BINOPS = ('add', 'sub', 'mul', 'and', 'or', 'xor', 'shl', 'lshr', 'ashr',
                   'sdiv', 'udiv', 'srem', 'urem')

    _C1_SYM_BINOPS = ('add', 'sub', 'mul', 'and', 'or', 'xor')


    class ParseError(Exception):
        pass


    _cur_wsym = [None]

    def _parse_ty(t):
        t = t.strip().rstrip(',')
        if t == 'ptr':
            return ('ptr', 0)
        m = re.fullmatch(r'i(\d+)', t)
        if m:
            return ('int', int(m.group(1)))


        w = _cur_wsym[0]
        if w and (t == '_' or t == w):
            return ('int', w)
        raise ParseError('unrecognized type %r' % t)


    def _parse_args(argstr):
        argstr = argstr.strip()
        if not argstr:
            return []
        out = []
        for piece in argstr.split(','):
            m = re.fullmatch(r'\s*%([\w.$-]+)\s*:\s*(\S+)\s*', piece)
            if not m:
                raise ParseError('bad arg piece %r' % piece)
            out.append((m.group(1), _parse_ty(m.group(2))))
        return out


    _OP_ASSUME = re.compile(r'^\s*llvm\.assume\s+%([\w.$-]+)\s*:\s*i1\s*$')

    _TERM_RET = re.compile(r'^\s*llvm\.return\s+%([\w.$-]+)\s*:\s*(\S+)\s*$')
    _TERM_BR = re.compile(r'^\s*llvm\.br\s+\^(\w+)\(([^)]*)\)\s*$')
    _TERM_CBR = re.compile(
        r'^\s*llvm\.cond_br\s+%([\w.$-]+)\s*:\s*i1\s*,\s*'
        r'\^(\w+)\(([^)]*)\)\s*,\s*\^(\w+)\(([^)]*)\)\s*$')
    _OP_CONST = re.compile(
        r'^\s*%([\w.$-]+)\s*=\s*llvm\.mlir\.constant\s+(-?\d+)\s*:\s*(\S+)\s*$')


    _OP_BIN_HEAD = re.compile(
        r'^\s*%([\w.$-]+)\s*=\s*llvm\.(' + '|'.join(_INT_BINOPS) + r')\s+(.*)$')
    _OP_BIN_TAIL = re.compile(
        r'^%([\w.$-]+)\s*,\s*%([\w.$-]+)\s*(?:overflow<[^>]*>\s*)?:\s*(\S+)\s*$')
    _OP_ICMP = re.compile(
        r'^\s*%([\w.$-]+)\s*=\s*llvm\.icmp\s+"(\w+)"\s+%([\w.$-]+)\s*,\s*'
        r'%([\w.$-]+)\s*:\s*(\S+)\s*$')


    def _parse_op(line):
        m = _OP_CONST.match(line)
        if m:
            return {'kind': 'const', 'dst': m.group(1), 'val': int(m.group(2)),
                    'ty': _parse_ty(m.group(3)), 'raw': line}
        m = _OP_BIN_HEAD.match(line)
        if m:


            try:
                flag, body = parse_binop_modifier(m.group(2), m.group(3))
            except Unsupported as e:
                return {'kind': 'other', 'raw': line, 'why': str(e)}
            tm = _OP_BIN_TAIL.match(body.strip())
            if tm:
                return {'kind': 'bin', 'dst': m.group(1), 'op': m.group(2),
                        'a': tm.group(1), 'b': tm.group(2),
                        'ty': _parse_ty(tm.group(3)), 'flag': flag, 'raw': line}
            return {'kind': 'other', 'raw': line,
                    'why': 'llvm.%s operand form outside the CFG int table'
                           % m.group(2)}
        m = _OP_ICMP.match(line)
        if m:
            return {'kind': 'icmp', 'dst': m.group(1), 'pred': m.group(2),
                    'a': m.group(3), 'b': m.group(4),
                    'ty': _parse_ty(m.group(5)), 'raw': line}


        m = _OP_ASSUME.match(line)
        if m:
            return {'kind': 'assume', 'cond': m.group(1), 'raw': line}
        return {'kind': 'other', 'raw': line}


    def _split_br_args(argstr):
        return _parse_args(argstr)


    def _parse_func(region):
        m = re.search(
            r'llvm\.func\s+@([\w.$-]+)\(([^)]*)\)\s*->\s*(\S+)\s*\{', region)
        if not m:
            raise ParseError('no llvm.func header')
        fname = m.group(1)
        fargs = _parse_args(m.group(2))
        fret = _parse_ty(m.group(3))
        body = region[m.end():]

        lines = [ln for ln in body.split('\n')]
        blocks = []
        cur = None
        for ln in lines:
            s = ln.strip()
            if not s or s.startswith('//') or s.startswith('--'):
                continue
            if s == '}' or s == '}]' or s == '}\n':
                break
            bm = re.match(r'^\^(\w+)\(([^)]*)\):$', s)
            if bm:
                cur = {'name': bm.group(1), 'args': _parse_args(bm.group(2)),
                       'ops': [], 'term': None, 'raw': []}
                blocks.append(cur)
                continue
            if cur is None:
                raise ParseError('op before first block: %r' % s)
            if cur['term'] is not None:
                raise ParseError('op after terminator in ^%s' % cur['name'])
            tm = _TERM_RET.match(s)
            if tm:
                cur['term'] = {'kind': 'ret', 'val': tm.group(1),
                               'ty': _parse_ty(tm.group(2))}
                cur['raw'].append(s)
                continue
            tm = _TERM_BR.match(s)
            if tm:
                cur['term'] = {'kind': 'br', 'dest': tm.group(1),
                               'args': _split_br_args(tm.group(2))}
                cur['raw'].append(s)
                continue
            tm = _TERM_CBR.match(s)
            if tm:
                cur['term'] = {'kind': 'cond_br', 'cond': tm.group(1),
                               'dest1': tm.group(2),
                               'args1': _split_br_args(tm.group(3)),
                               'dest2': tm.group(4),
                               'args2': _split_br_args(tm.group(5))}
                cur['raw'].append(s)
                continue
            cur['ops'].append(_parse_op(s))
            cur['raw'].append(s)
        if not blocks:
            raise ParseError('no blocks')
        names = [b['name'] for b in blocks]
        if len(set(names)) != len(names):
            raise ParseError('duplicate block names')
        for b in blocks:
            if b['term'] is None:
                raise ParseError('block ^%s has no terminator' % b['name'])
            for d in _successors(b):
                if d not in names:
                    raise ParseError('undefined label ^%s' % d)
        return {'fname': fname, 'args': fargs, 'ret': fret, 'blocks': blocks}


    def _successors(block):
        t = block['term']
        if t['kind'] == 'br':
            return [t['dest']]
        if t['kind'] == 'cond_br':
            return [t['dest1'], t['dest2']]
        return []


    def _is_multiblock(func):
        return len(func['blocks']) >= 2 or any(_successors(b)
                                               for b in func['blocks'])


    def _block_body_normalized(block):
        return [re.sub(r'\s+', ' ', ln).strip() for ln in block['raw']]


    _ROW_FLAGS_OK = {'C0': True, 'C1': True, 'C1W': True}


    def _int_table_ok(op, row):
        if op['kind'] in ('const', 'icmp'):
            return True, ''
        if op['kind'] == 'assume':


            if row == 'C1W':
                return True, ''
            return False, ('llvm.assume is modelled by row C1W only, not %s' % row)
        if op['kind'] == 'bin':
            flag = op.get('flag', 'none')
            if flag == 'none' or _ROW_FLAGS_OK.get(row, False):
                return True, ''
            return False, ('llvm.%s carries the %r modifier, which row %s does '
                           'not model' % (op['op'], flag, row))
        return False, op.get('why', '')


    def _int_table_why(op, row):
        _ok, why = _int_table_ok(op, row)
        return ' — ' + why if why else ''


    _ICMP_PREDS = ('eq', 'ne', 'ugt', 'uge', 'ult', 'ule',
                   'sgt', 'sge', 'slt', 'sle')


    def _bool_render(name, defs, argmap, W):
        op = defs.get(name)
        if op is None or op['kind'] != 'icmp' or op['pred'] not in _ICMP_PREDS:
            return None
        a = _bv_render(op['a'], defs, argmap, W)
        b = _bv_render(op['b'], defs, argmap, W)
        if a is None or b is None:
            return None
        return "(LLVM.icmp' LLVM.IntPred.%s %s %s)" % (op['pred'], a, b)


    def _ub_guards(op, X, Y, W):
        o = op['op']
        flag = op.get('flag', 'none')
        z = '0#%s' % W
        out = []
        if o in ('shl', 'lshr', 'ashr'):
            out.append(('shamt', 'BitVec.ofNat %s %s ≤ %s' % (W, W, Y),
                        'the shift amount reaches the bit width, so llvm.%s is poison' % o))
        if o in ('udiv', 'urem', 'sdiv', 'srem'):
            out.append(('divzero', '%s = %s' % (Y, z),
                        'a zero divisor makes llvm.%s IMMEDIATE UB' % o))
        if o in ('sdiv', 'srem'):


            out.append(('divovf',
                        '(%s ≠ 1 ∧ %s = BitVec.intMin %s ∧ %s = -1#%s)'
                        % (W, X, W, Y, W),
                        'INT_MIN / -1 makes llvm.%s IMMEDIATE UB' % o))
        SOVF = {'add': 'saddOverflow', 'sub': 'ssubOverflow', 'mul': 'smulOverflow'}
        UOVF = {'add': 'uaddOverflow', 'sub': 'usubOverflow', 'mul': 'umulOverflow'}
        if o in SOVF and flag in ('nsw', 'both'):
            out.append(('nsw', 'BitVec.%s %s %s' % (SOVF[o], X, Y),
                        'signed overflow makes llvm.%s overflow<nsw> poison' % o))
        if o in UOVF and flag in ('nuw', 'both'):
            out.append(('nuw', 'BitVec.%s %s %s' % (UOVF[o], X, Y),
                        'unsigned overflow makes llvm.%s overflow<nuw> poison' % o))


        if o == 'shl' and flag in ('nsw', 'both'):
            out.append(('nsw', '((%s <<< %s.toNat).sshiftRight %s.toNat) ≠ %s'
                        % (X, Y, Y, X),
                        'a bit shifted out disagrees with the sign bit, so '
                        'llvm.shl overflow<nsw> is poison'))
        if o == 'shl' and flag in ('nuw', 'both'):
            out.append(('nuw', '((%s <<< %s.toNat) >>> %s.toNat) ≠ %s' % (X, Y, Y, X),
                        'a set bit is shifted out, so llvm.shl overflow<nuw> is poison'))
        if flag == 'exact' and o in ('lshr', 'ashr'):
            out.append(('exact', '((%s >>> %s.toNat) <<< %s.toNat) ≠ %s' % (X, Y, Y, X),
                        'a set bit is shifted out, so llvm.%s exact is poison' % o))


        if flag == 'exact' and o == 'udiv':
            out.append(('exact', '%s ≠ %s ∧ (%s %% %s) ≠ %s' % (Y, z, X, Y, z),
                        'a non-zero remainder makes llvm.udiv exact poison'))
        if flag == 'exact' and o == 'sdiv':
            out.append(('exact', '%s ≠ %s ∧ %s.smod %s ≠ %s' % (Y, z, X, Y, z),
                        'a non-zero remainder makes llvm.sdiv exact poison'))
        if flag == 'disjoint' and o == 'or':
            out.append(('disjoint', '(%s &&& %s) ≠ %s' % (X, Y, z),
                        'the operands share a set bit, so llvm.or disjoint is poison'))
        return out


    _SRC_DISCHARGE_OK = None
    _SRC_DISCHARGE_FW_ONLY = frozenset()


    _SRC_DISCHARGE_SYM_SKIP = {('sdiv', 'exact')}


    def _entry_ub_discharges(sf, W, avname, symbolic):
        cone = _entry_ub_cone(sf)
        if not cone or len(sf['args']) != 1:
            return []
        se = sf['blocks'][0]
        argmap = {sf['args'][0][0]: avname}
        defs, out = {}, []
        for op in se['ops']:
            if op.get('dst'):
                defs[op['dst']] = op
            if op['kind'] != 'bin' or op['op'] not in _BV_BINOP:
                continue
            if op['dst'] not in cone:
                continue


            X = _bv_render(op['a'], defs, argmap, W)
            Y = _bv_render(op['b'], defs, argmap, W)
            if X is None or Y is None:
                continue
            for tag, guard, why in _ub_guards(op, X, Y, W):
                key = (op['op'], tag)
                if symbolic and key in _SRC_DISCHARGE_SYM_SKIP:
                    continue
                if _SRC_DISCHARGE_OK is not None and key not in _SRC_DISCHARGE_OK:
                    if not (key in _SRC_DISCHARGE_FW_ONLY and not symbolic):
                        continue
                out.append((tag, guard, why, op['raw'].strip()))
        return out


    def _guard_val_arg(eubs, k, pidx):
        return "av%d'" % (pidx[-1] + 1)


    def _entry_ub_discharges_multi(sf, W, argnm, covered, symbolic):
        cone = _entry_ub_cone(sf)
        if not cone:
            return []
        se = sf['blocks'][0]
        argmap = {nm: argnm[nm] for nm in covered if nm in argnm}
        defs, out = {}, []
        for op in se['ops']:
            if op.get('dst'):
                defs[op['dst']] = op
            if op['kind'] == 'assume':


                c = _bool_render(op['cond'], defs, argmap, W)
                if c is not None:
                    out.append(('assume', '¬ %s' % c,
                                'the assumed condition is false, which makes '
                                'llvm.assume IMMEDIATE UB', op['raw'].strip()))
                continue
            if op['kind'] != 'bin' or op['op'] not in _BV_BINOP:
                continue
            if op['dst'] not in cone:
                continue
            X = _bv_render(op['a'], defs, argmap, W)
            Y = _bv_render(op['b'], defs, argmap, W)
            if X is None or Y is None:
                continue
            for tag, guard, why in _ub_guards(op, X, Y, W):
                key = (op['op'], tag)
                if symbolic and key in _SRC_DISCHARGE_SYM_SKIP:
                    continue
                out.append((tag, guard, why, op['raw'].strip()))
        return out


    def _cone_in_block(block, val):
        defs = {op['dst']: op for op in block['ops'] if op.get('dst')}
        seen, stack = set(), [val]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            op = defs.get(v)
            if op is None:
                continue
            if op['kind'] == 'const':
                continue
            if op['kind'] in ('bin', 'icmp'):
                stack.append(op['a'])
                stack.append(op['b'])
                continue
            return None
        return seen


    def _arg_var(i, npar, p, ity):
        j = npar - 1 - i
        if j == 0:
            rest = ', '.join([ity] * (npar - 1))
            return 'Ctxt.Var.last (Ctxt.ofList [%s]) %s' % (rest, ity)
        return '(⟨%d, by rfl⟩ : %s_ctx.Var %s)' % (j, p, ity)


    def _cond_arg_positions(sf):
        if len(sf['blocks']) != 3:
            return None
        _se, sl, _sx = sf['blocks']
        if sl['term']['kind'] != 'cond_br':
            return None
        lnames = [n for n, _t in sl['args']]
        c = _cone_in_block(sl, sl['term']['cond'])
        if c is None:
            return None
        return [i for i, n in enumerate(lnames) if n in c]


    def _entry_ub_cone(sf):
        if len(sf['blocks']) != 3:
            return None
        se, sl = sf['blocks'][0], sf['blocks'][1]
        L, t, out = sl['name'], sf['blocks'][0]['term'], set()


        if t['kind'] == 'cond_br':
            c = _cone_in_block(se, t['cond'])
            if c is None:
                return None
            out |= c
            ebr = (t['args1'] if t['dest1'] == L
                   else t['args2'] if t['dest2'] == L else None)
        elif t['kind'] == 'br':
            ebr = t['args'] if t['dest'] == L else None
        else:
            return None


        lc = _cone_in_block(sl, sl['term']['cond']) \
            if sl['term']['kind'] == 'cond_br' else None
        if lc is None:
            return None
        out |= lc
        pos = _cond_arg_positions(sf)
        if pos and ebr is not None:
            for q in pos:
                if q >= len(ebr):
                    return None
                c = _cone_in_block(se, ebr[q][0])
                if c is None:
                    return None
                out |= c
        return out


    def _deps_in_block(block, val, argnames):
        defs = {op['dst']: op for op in block['ops'] if op.get('dst')}
        seen, out, stack = set(), set(), [val]
        while stack:
            v = stack.pop()
            if v in seen:
                continue
            seen.add(v)
            if v in argnames:
                out.add(v)
                continue
            op = defs.get(v)
            if op is None:
                return None
            if op['kind'] == 'const':
                continue
            if op['kind'] in ('bin', 'icmp'):
                stack.append(op['a'])
                stack.append(op['b'])
                continue
            return None
        return out


    def _poison_input_indices(sf):
        if len(sf['blocks']) != 3:
            return []
        cone = _entry_ub_cone(sf)
        if not cone:
            return []
        return [i for i, (nm, _t) in enumerate(sf['args']) if nm in cone]


    def _src_denote_simpset(p, sf, extra=(), hnames=('hA',)):
        base = ['%s_src' % p,
                'LLVMMemory.Com.denoteWithMemoryFuel',
                'LLVMMemory.Com.denoteWithMemoryFuelIn',
                'LLVMMemory.CFGTarget.denoteWithMemoryFuel',
                'LLVMMemory.CFGBlocks.findMemoryBlock?',
                'LLVMMemory.CFGBody.denoteWithMemoryFuelCore',
                'LLVMMemory.CFGTerm.denoteWithMemoryFuelCore',
                'LLVMMemory.Expr.denoteWithMemory',
                'LLVMMemory.throwUB'] + list(hnames) + list(extra) + [
                'DialectDenote.denote', 'InstCombine.Op.denote',
                'InstCombine.Op.denoteVec',


                'InstCombine.lift1', 'InstCombine.lift2', 'InstCombine.lift2UB',
                'Ctxt.Valuation.cons_eval', 'Ctxt.Valuation.ofHVector_cons']
        ops = set()
        has_assume = False
        for b in sf['blocks']:
            for op in b['ops']:
                if op['kind'] == 'const':
                    ops.add('const?')
                elif op['kind'] == 'icmp':
                    ops.add('icmp')
                elif op['kind'] == 'assume':
                    has_assume = True
                elif op['kind'] == 'bin':
                    ops.add(op['op'])
        if has_assume:


            base.append('LLVM.assume_')
            base.append('ImmediateUBOr.immediateUB')
        for o in sorted(ops):
            if o == 'const?':
                base.append('LLVM.const?')
            else:
                base.append('LLVM.%s' % o)
                base.append('LLVM.%s?' % o)
        return ', '.join(base)


    _BV_BINOP = {
        'add': '(%s + %s)', 'sub': '(%s - %s)', 'mul': '(%s * %s)',
        'and': '(%s &&& %s)', 'or': '(%s ||| %s)', 'xor': '(%s ^^^ %s)',
        'shl': '(%s <<< %s)', 'lshr': '(%s >>> %s)',
        "ashr": "(%s.sshiftRight' %s)",
        'udiv': '(%s / %s)', 'sdiv': '(%s.sdiv %s)',
        'urem': '(%s %% %s)', 'srem': '(BitVec.srem %s %s)',
    }


    def _bv_const(val, W):
        return ('(BitVec.ofInt %s (%d))' % (W, val) if val < 0
                else '(%d#%s)' % (val, W))


    def _bv_render(name, defs, argmap, W, depth=0):
        if depth > 24:
            return None
        if name in argmap:
            return argmap[name]
        op = defs.get(name)
        if op is None:
            return None
        if op['kind'] == 'const':
            return _bv_const(op['val'], W)
        if op['kind'] == 'bin' and op['op'] in _BV_BINOP:
            a = _bv_render(op['a'], defs, argmap, W, depth + 1)
            b = _bv_render(op['b'], defs, argmap, W, depth + 1)
            if a is None or b is None:
                return None
            return _BV_BINOP[op['op']] % (a, b)
        return None


    def _ub_obligations(op, X, Y, W):
        o = op['op']
        flag = op.get('flag', 'none')
        z = '0#%s' % W
        out = []


        if o in ('shl', 'lshr', 'ashr'):
            out.append(('shamt', '¬ (BitVec.ofNat %s %s ≤ %s)' % (W, W, Y),
                        'llvm.%s poisons when the shift amount reaches the bit width' % o))

        if o in ('udiv', 'urem'):
            out.append(('divzero', '%s ≠ %s' % (Y, z),
                        'llvm.%s: a zero divisor is IMMEDIATE UB' % o))

        if o in ('sdiv', 'srem'):
            out.append(('divzero', '%s ≠ %s' % (Y, z),
                        'llvm.%s: a zero divisor is IMMEDIATE UB' % o))
            out.append(('divovf',
                        '¬ (%s ≠ 1 ∧ %s = BitVec.intMin %s ∧ %s = -1)' % (W, X, W, Y),
                        'llvm.%s: INT_MIN / -1 is IMMEDIATE UB' % o))

        SOVF = {'add': 'saddOverflow', 'sub': 'ssubOverflow', 'mul': 'smulOverflow'}
        UOVF = {'add': 'uaddOverflow', 'sub': 'usubOverflow', 'mul': 'umulOverflow'}
        if o in SOVF and flag in ('nsw', 'both'):
            out.append(('nsw', '¬ BitVec.%s %s %s' % (SOVF[o], X, Y),
                        'llvm.%s overflow<nsw> poisons on signed overflow' % o))
        if o in UOVF and flag in ('nuw', 'both'):
            out.append(('nuw', '¬ BitVec.%s %s %s' % (UOVF[o], X, Y),
                        'llvm.%s overflow<nuw> poisons on unsigned overflow' % o))

        if o == 'shl' and flag in ('nsw', 'both'):
            out.append(('nsw', "((%s <<< %s).sshiftRight' %s) = %s" % (X, Y, Y, X),
                        'llvm.shl overflow<nsw> poisons when a bit shifted out '
                        'disagrees with the sign bit'))
        if o == 'shl' and flag in ('nuw', 'both'):
            out.append(('nuw', '((%s <<< %s) >>> %s) = %s' % (X, Y, Y, X),
                        'llvm.shl overflow<nuw> poisons when any set bit is shifted out'))

        if flag == 'exact' and o in ('lshr', 'ashr'):
            out.append(('exact', '((%s >>> %s) <<< %s) = %s' % (X, Y, Y, X),
                        'llvm.%s exact poisons when a set bit is shifted out' % o))
        if flag == 'exact' and o == 'udiv':
            out.append(('exact', '%s.umod %s = %s' % (X, Y, z),
                        'llvm.udiv exact poisons on a non-zero remainder'))
        if flag == 'exact' and o == 'sdiv':
            out.append(('exact', '%s.smod %s = %s' % (X, Y, z),
                        'llvm.sdiv exact poisons on a non-zero remainder'))

        if flag == 'disjoint' and o == 'or':
            out.append(('disjoint', '(%s &&& %s) = %s' % (X, Y, z),
                        'llvm.or disjoint poisons when the operands share a set bit'))
        return out


    def _tgt_ub_holes(block, W, prefix='a', extra=None, argsub=None):


        argmap = dict(extra or {})
        for i, (nm, _ty) in enumerate(block['args']):


            sub = argsub[i] if (argsub and i < len(argsub)) else None
            argmap[nm] = sub if sub is not None else '%s%d' % (prefix, i + 1)
        defs, out, opaque = {}, [], []
        for op in block['ops']:
            if op.get('dst'):
                defs[op['dst']] = op
            if op['kind'] == 'assume':


                c = _bool_render(op['cond'], defs, {nm: v for nm, v in argmap.items()}, W)
                if c is None:
                    opaque.append(op['raw'].strip())
                else:
                    out.append(('assume', '%s = true' % c,
                                'llvm.assume is IMMEDIATE UB unless its condition '
                                'holds', op['raw'].strip()))
                continue
            if op['kind'] in ('const', 'icmp'):
                continue
            if op['kind'] != 'bin' or op['op'] not in _BV_BINOP:
                opaque.append(op['raw'].strip())
                continue
            X = _bv_render(op['a'], defs, argmap, W)
            Y = _bv_render(op['b'], defs, argmap, W)
            if X is None or Y is None:
                opaque.append(op['raw'].strip())
                continue
            for tag, prop, why in _ub_obligations(op, X, Y, W):
                out.append((tag, prop, why, op['raw'].strip()))
        return out, opaque


    def _c1w_src_entry_hu_premises(src, W):
        try:
            sf = src['func']
            entry = sf['blocks'][0]
            obls, _opq = _tgt_ub_holes(entry, W)
            if not obls:
                return []
            sinks = set(_entry_ub_cone(sf) or ())
            for op in entry['ops']:
                if op['kind'] == 'assume':
                    c = _cone_in_block(entry, op['cond'])
                    if c:
                        sinks |= c
            IMMEDIATE = ('divzero', 'divovf', 'assume')
            out, seen = [], set()
            for tag, prop, why, raw in obls:
                if tag not in IMMEDIATE:

                    dst = (raw.split('=', 1)[0].strip().lstrip('%')
                           if '=' in raw else '')
                    if dst not in sinks:
                        continue
                if prop in seen:
                    continue
                seen.add(prop)
                out.append((tag, prop, why, raw))
            return out
        except Exception:
            return []

    def _c1w_src_first_iter_premises(src, W, npar):
        try:
            blocks = src['func']['blocks']
        except (KeyError, TypeError):
            return []
        if len(blocks) < 2:
            return []
        sentry, sloop = blocks[0], blocks[1]
        if len(sentry['args']) != npar:
            return []
        term = sentry.get('term') or {}
        if term.get('kind') != 'br':
            return []
        targs = term.get('args') or []
        if len(targs) != len(sloop['args']):
            return []
        fargmap = {nm: 'a%d' % (i + 1)
                   for i, (nm, _t) in enumerate(sentry['args'])}
        sdefs = {o['dst']: o for o in sentry['ops'] if o.get('dst')}
        init = [_bv_render(a[0], sdefs, fargmap, W) for a in targs]
        if any(v is None for v in init):
            return []
        subs, _opaque = _tgt_ub_holes(sloop, W, extra=fargmap, argsub=init)
        return subs


    _UB_BINOP = {
        'and':  ('lift2',   ''),        'xor':  ('lift2',   ''),
        'or':   ('lift2',   'DISJ'),
        'add':  ('lift2',   'NOWRAP'),  'sub':  ('lift2',   'NOWRAP'),
        'mul':  ('lift2',   'NOWRAP'),  'shl':  ('lift2',   'NOWRAP'),
        'lshr': ('lift2',   'EXACT'),   'ashr': ('lift2',   'EXACT'),
        'udiv': ('lift2UB', 'EXACT'),   'sdiv': ('lift2UB', 'EXACT'),
        'urem': ('lift2UB', ''),        'srem': ('lift2UB', ''),
    }


    def _ub_flag(op, kind):
        f = op.get('flag', 'none')
        if f == 'none':
            return ''
        if kind == 'NOWRAP':
            return {'nsw':  ' \u27e8true, false\u27e9',
                    'nuw':  ' \u27e8false, true\u27e9',
                    'both': ' \u27e8true, true\u27e9'}.get(f)
        if kind == 'EXACT' and f == 'exact':
            return ' \u27e8true\u27e9'
        if kind == 'DISJ' and f == 'disjoint':
            return ' \u27e8true\u27e9'
        return None


    def _ub_value_render(name, defs, argmap, W, depth=0):
        if depth > 24:
            return None
        if name in argmap:
            return argmap[name]
        op = defs.get(name)
        if op is None:
            return None
        if op['kind'] == 'const':
            v = op['val']
            return '(pure (LLVM.const? %s %s))' % (W, '(%d)' % v if v < 0 else v)
        if op['kind'] == 'bin' and op['op'] in _UB_BINOP:
            lifter, kind = _UB_BINOP[op['op']]
            fl = _ub_flag(op, kind)
            if fl is None:
                return None
            a = _ub_value_render(op['a'], defs, argmap, W, depth + 1)
            b = _ub_value_render(op['b'], defs, argmap, W, depth + 1)
            if a is None or b is None:
                return None
            return ('(InstCombine.%s (fun x y => LLVM.%s x y%s) %s %s)'
                    % (lifter, op['op'], fl, a, b))
        return None


    def _tgt_result_expr(tf, variant, W, p, ity, npar):
        block = tf['blocks'][0]


        argmap = {nm: '(V (%s))' % _arg_var(i, npar, p, ity)
                  for i, (nm, _t) in enumerate(block['args'])}
        defs = {}
        for op in block['ops']:
            if op.get('dst'):
                defs[op['dst']] = op
            if op['kind'] == 'assume':


                return None, 'the target entry block contains `llvm.assume`'
        term = block['term']
        if variant == 'straight':
            if term['kind'] != 'ret':
                return None, 'straight target does not end in llvm.return'
            val = term['val']
        elif variant == 'exitbr':
            if term['kind'] != 'br' or len(term['args']) != 1:
                return None, 'exitbr target entry is not `br ^exit(<one arg>)`'

            val = term['args'][0][0]
        else:
            return None, 'not a loop-free target'
        e = _ub_value_render(val, defs, argmap, W)
        if e is None:
            return None, ('the returned value flows through an op this printer '
                          'does not model (icmp changes width; select/ctpop/'
                          'sext and other ops are outside the table)')
        return e, ''


    def parse_input(text):
        imports = [ln.strip() for ln in text.split('\n')
                   if ln.strip().startswith('import ')]
        ns = [m.group(1) for m in
              re.finditer(r'^namespace\s+([\w.]+)\s*$', text, re.M)]
        defs = []
        for m in re.finditer(r'^def\s+([\w.]+)\s*((?:\([^)]*\)\s*)*):=', text, re.M):
            name = m.group(1)
            binders = m.group(2).strip()
            start = m.start()

            close = text.find('}]', m.end())
            if close < 0:
                raise ParseError('def %s: no closing }]' % name)
            verbatim = text[start:close + 2]
            lm = re.search(r'\[llvm\(([^)]*)\)\|', verbatim)
            if not lm:
                raise ParseError('def %s: no [llvm(...)| region' % name)
            width_params = lm.group(1).strip()
            region = verbatim[lm.end():]
            _cur_wsym[0] = width_params.strip() or None
            try:
                func = _parse_func(region)
            finally:
                _cur_wsym[0] = None
            defs.append({'name': name, 'verbatim': verbatim, 'binders': binders,
                         'width_params': width_params, 'func': func})
        return {'imports': imports, 'ns': ns, 'defs': defs, 'text': text}


    def _find_pair(parsed):
        srcs = {d['name'][:-4]: d for d in parsed['defs']
                if d['name'].endswith('_src')}
        tgts = {d['name'][:-4]: d for d in parsed['defs']
                if d['name'].endswith('_tgt')}
        common = sorted(set(srcs) & set(tgts))
        if len(common) != 1:
            raise ParseError('expected exactly one _src/_tgt pair, found %d'
                             % len(common))
        base = common[0]
        return base, srcs[base], tgts[base]


    def detect(text: str) -> bool:
        try:
            if '[llvm(' not in text:
                return False
            if not re.search(r'llvm\.(cond_)?br\s', text):
                return False

            if not re.search(r'^def\s+[\w.]+_src\s*(?:\([^)]*\)\s*)*:=', text, re.M):
                return False
            if not re.search(r'^def\s+[\w.]+_tgt\s*(?:\([^)]*\)\s*)*:=', text, re.M):
                return False
            return True
        except Exception:
            return False


    PINNED_IMPORTS = (
        'import SSA.Projects.InstCombine.Refinement\n'
        'import SSA.Projects.InstCombine.MemoryRefinement\n'
        'import LeanMLIR.Dialects.LLVM.Syntax\n')


    def _ns_open(ns):
        return '\n'.join('namespace %s' % n for n in ns)


    def _ns_close(ns):
        return '\n'.join('end %s' % n for n in reversed(ns))


    def _int_widths(pair_funcs):
        ws = set()
        for f in pair_funcs:
            for _, ty in f['args']:
                if ty[0] == 'int':
                    ws.add(ty[1])
            if f['ret'][0] == 'int':
                ws.add(f['ret'][1])
            for b in f['blocks']:
                for _, ty in b['args']:
                    if ty[0] == 'int':
                        ws.add(ty[1])
        return ws


    def _all_int(func):
        if func['ret'][0] != 'int':
            return False
        for _, ty in func['args']:
            if ty[0] != 'int':
                return False
        for b in func['blocks']:
            for _, ty in b['args']:
                if ty[0] != 'int':
                    return False
        return True


    def _wsym(*defs):
        syms = {d['width_params'].strip() for d in defs}
        if syms == {''}:
            return None
        if len(syms) != 1:
            raise ParseError('src/tgt width parameters differ: %r' % sorted(syms))
        w = syms.pop()
        if ',' in w:
            raise ParseError('multi-width [llvm(%s)| is out of scope for the CFG '
                             'proof family (single common width row)' % w)
        for d in defs:
            want = '(%s : Nat)' % w
            got = re.sub(r'\s+', ' ', d.get('binders', '')).strip()
            if got != want:
                raise ParseError('def %s: binder %r is not the expected %r'
                                 % (d['name'], got, want))
        return w


    def _sym_widths_ok(wsym, funcs):
        seen = set()
        def note(ty):
            if isinstance(ty, tuple) and ty and ty[0] == 'int':
                seen.add(ty[1])
        for f in funcs:
            note(f['ret'])
            for _, ty in f['args']:
                note(ty)
            for b in f['blocks']:
                for _, ty in b['args']:
                    note(ty)
                for op in b['ops']:
                    note(op.get('ty'))
                for _, ty in (b['term'].get('args') or []):
                    note(ty)
                note(b['term'].get('ty'))
        bad = sorted({str(w) for w in seen if w != 1 and w != wsym})
        return (not bad), bad


    def _symbolize(text, base, verbatims):
        prot = []
        for v in verbatims:
            i = text.find(v)
            if i >= 0:
                prot.append((i, i + len(v)))
        decls = []
        pat = r'^(?:private\s+)?(?:abbrev|def|theorem)\s+(%s_[A-Za-z0-9_]*)' % re.escape(base)
        for m in re.finditer(pat, text, re.M):
            if any(ps <= m.start(1) and m.end(1) <= pe for ps, pe in prot):
                continue
            prot.append((m.start(1), m.end(1)))
            decls.append(m.end(1))


        for m in re.finditer(r'simp(?:\s+only)?(?:\s+[+-]\w+)*\s*\[', text):
            i, depth = m.end() - 1, 0
            while i < len(text):
                if text[i] == '[':
                    depth += 1
                elif text[i] == ']':
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            prot.append((m.start(), i + 1))
        edits = []
        for m in re.finditer(r'(?<![\w.@])(%s_[A-Za-z0-9_]*)' % re.escape(base), text):
            if any(ps <= m.start() and m.end() <= pe for ps, pe in prot):
                continue
            edits.append((m.start(), m.end(), '(%s w)' % m.group(1)))
        edits.extend((d, d, ' (w : Nat)') for d in decls)
        for a, b, r in sorted(edits, key=lambda x: -x[0]):
            text = text[:a] + r + text[b:]
        return text


    def _c0_applicable(base, src, tgt):
        sf, tf = src['func'], tgt['func']


        if src['width_params'] or tgt['width_params']:
            try:
                wsym = _wsym(src, tgt)
            except ParseError as e:
                return False, 'C0: %s' % e
            ok, bad = _sym_widths_ok(wsym, [sf, tf])
            if not ok:
                return False, ('C0: symbolic-width input also carries literal '
                               'width(s) %s beside the parameter %r' % (bad, wsym))
        if not (_all_int(sf) and _all_int(tf)):
            return False, 'C0: non-int (ptr) type in signature/block args'
        if [t for _, t in sf['args']] != [t for _, t in tf['args']]:
            return False, 'C0: src/tgt param type lists differ'

        if len(tf['blocks']) != 2:
            return False, 'C0: tgt does not have exactly 2 blocks'
        tentry, tterm = tf['blocks']
        if tentry['ops'] or tentry['term']['kind'] != 'br' \
                or tentry['term']['args']:
            return False, 'C0: tgt entry is not exactly `llvm.br ^T()`'
        if tentry['term']['dest'] != tterm['name']:
            return False, 'C0: tgt entry br does not target terminal block'
        if tterm['args'] or tterm['term']['kind'] != 'ret':
            return False, 'C0: tgt terminal block has args or is not a return'
        if any(op['kind'] != 'const' for op in tterm['ops']):
            return False, 'C0: tgt terminal block has non-constant ops'
        T = tterm['name']
        ename = sf['blocks'][0]['name']
        if tf['blocks'][0]['name'] != ename:
            return False, 'C0: entry block names differ'

        sT = [b for b in sf['blocks'] if b['name'] == T]
        if not sT:
            return False, 'C0: src has no block named ^%s' % T
        sT = sT[0]
        if sT['args']:
            return False, 'C0: src ^%s takes args' % T
        if _block_body_normalized(sT) != _block_body_normalized(tterm):
            return False, 'C0: src ^%s body not identical to tgt terminal' % T

        sentry = sf['blocks'][0]
        if any(op['kind'] != 'const' for op in sentry['ops']):
            return False, 'C0: src entry has non-constant ops'
        if sentry['term']['kind'] != 'br':
            return False, 'C0: src entry terminator is not an unconditional br'
        if sentry['term']['dest'] == ename:
            return False, 'C0: src entry branches to itself'


        loopish = [b for b in sf['blocks'][1:] if b['name'] != T]
        if not loopish:
            return False, 'C0: src has no loop blocks (nothing deleted)'
        for b in loopish:
            if b['term']['kind'] != 'cond_br':
                return False, ('C0: src ^%s terminator is not cond_br '
                               '(plain-br rows unsupported)' % b['name'])
            for d in _successors(b):
                if d == ename:
                    return False, 'C0: src ^%s branches back to entry' % b['name']
            for op in b['ops']:
                if not _int_table_ok(op, 'C0')[0]:
                    return False, ('C0: src ^%s op outside int table: %r%s'
                                   % (b['name'], op['raw'],
                                      _int_table_why(op, 'C0')))
        return True, ''


    def _c0_ty(base, ty):
        if ty == ('int', 1):
            return 'LLVM.Ty.bitvec 1'

        return '%s_i%s' % (base, ty[1])


    def _c0_emit(case, parsed, base, src, tgt):
        sf, tf = src['func'], tgt['func']
        ns = parsed['ns']
        ename = sf['blocks'][0]['name']
        T = tf['blocks'][1]['name']
        retty = _c0_ty(base, sf['ret'])
        wsym = _wsym(src, tgt)


        c0tac = 'by simp' if wsym else 'by decide'
        widths = sorted((w for w in _int_widths([sf, tf]) if w != 1), key=str)
        abbrevs = '\n'.join(
            'private abbrev %s_i%s : LLVM.Ty := LLVM.Ty.bitvec %s' % (base, w, w)
            for w in widths)
        ctx_tys = ', '.join(_c0_ty(base, t) for _, t in sf['args'])
        S = base + '_src'
        Tg = base + '_tgt'
        run = base + '_cfg_run'
        sb = base + '_src_blocks'
        tb = base + '_tgt_blocks'
        rt = base + '_ret_target'
        core = base + '_src_target_refines_tgt_ret'

        simp_core = (
            '{run}, {sb}, {tb}, {S}, {Tg}, {rt}, '
            'LLVMMemory.CFGTarget.denoteWithMemoryFuel, '
            'LLVMMemory.CFGBlocks.findMemoryBlock?, '
            'LLVMMemory.CFGBody.denoteWithMemoryFuelCore, '
            'LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, '
            'LLVMMemory.Expr.denoteWithMemory, LLVMMemory.throwUB'
        ).format(run=run, sb=sb, tb=tb, S=S, Tg=Tg, rt=rt)
        simp_mismatch = (
            '{run}, {sb}, {tb}, {S}, {Tg}, {rt}, '
            'LLVMMemory.CFGTarget.denoteWithMemoryFuel, '
            'LLVMMemory.CFGBlocks.findMemoryBlock?, htys, LLVMMemory.throwUB'
        ).format(run=run, sb=sb, tb=tb, S=S, Tg=Tg, rt=rt)
        simp_terminal = (
            '{run}, {sb}, {tb}, {S}, {Tg}, {rt}, '
            'LLVMMemory.CFGTarget.denoteWithMemoryFuel, '
            'LLVMMemory.CFGBlocks.findMemoryBlock?, '
            'LLVMMemory.CFGBody.denoteWithMemoryFuelCore, '
            'LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, '
            'LLVMMemory.Expr.denoteWithMemory, '
            'Ctxt.Valuation.ofHVector_nil, Ctxt.Valuation.nil_append'
        ).format(run=run, sb=sb, tb=tb, S=S, Tg=Tg, rt=rt)


        blocks = sf['blocks']
        hyp = {}
        for b in blocks:
            hyp[b['name']] = ('hEntry' if b['name'] == ename
                              else 'h_%s' % b['name'])

        def argtys_lit(b):
            if not b['args']:
                return '[]'
            return '[%s]' % ', '.join(_c0_ty(base, t) for _, t in b['args'])

        lines = []

        def emit_arm(i, ind):
            b = blocks[i]
            name, h = b['name'], hyp[b['name']]
            p = ' ' * ind
            if i == 0:
                lines.append(p + 'by_cases %s : name = "%s"' % (h, name))
                lines.append(p + '· subst name')
                lines.append(p + '  contradiction')
            else:
                lines.append(p + '· by_cases %s : name = "%s"' % (h, name))
                q = p + '  '
                if b['name'] == T:
                    lines.append(q + '· subst name')
                    lines.append(q + '  by_cases htys : argTys = []')
                    lines.append(q + '  · subst argTys')
                    lines.append(q + '    cases args')
                    lines.append(q + '    cases extra <;>')
                    lines.append(q + '      · simp [%s]' % simp_terminal)
                    lines.append(q + '        exact mem_result_le_self _')
                    lines.append(q + '  · simp [%s]' % simp_mismatch)
                    lines.append(q + '    exact '
                                 'ImmediateUBOr.IsRefinedBy.immediateUBLeft')
                else:
                    lines.append(q + '· subst name')
                    lines.append(q + '  by_cases htys : argTys = %s'
                                 % argtys_lit(b))
                    lines.append(q + '  · subst argTys')
                    lines.append(q + '    simp [%s]' % simp_core)
                    lines.append(q + '    split <;>')
                    lines.append(q + '      first')
                    lines.append(q + '        | exact '
                                 'ImmediateUBOr.IsRefinedBy.immediateUBLeft')
                    lines.append(q + '        | (split <;>')
                    lines.append(q + '            simpa [Nat.add_assoc] using')
                    lines.append(q + '              (ih (1 + extra) _ _ s '
                                 '(%s)))' % c0tac)
                    lines.append(q + '  · simp [%s]' % simp_mismatch)
                    lines.append(q + '    exact '
                                 'ImmediateUBOr.IsRefinedBy.immediateUBLeft')
            if i + 1 < len(blocks):
                if i == 0:
                    emit_arm(i + 1, ind)
                else:
                    emit_arm(i + 1, ind + 2)
            else:

                p2 = ' ' * (ind if i == 0 else ind + 2)
                shows = ', '.join(
                    'show "%s" ≠ name by intro h; exact %s h.symm'
                    % (b2['name'], hyp[b2['name']]) for b2 in blocks)
                lines.append(p2 + '· simp [%s, %s, %s]' % (run, sb, shows)
                             + '')

                lines[-1] = (p2 + '· simp [%s, %s, %s, %s, %s, %s, %s, '
                             'LLVMMemory.CFGTarget.denoteWithMemoryFuel, '
                             'LLVMMemory.CFGBlocks.findMemoryBlock?, '
                             'LLVMMemory.throwUB]'
                             % (run, sb, shows, tb, S, Tg, rt))
                lines.append(p2 + '  exact '
                             'ImmediateUBOr.IsRefinedBy.immediateUBLeft')

        emit_arm(0, 6)
        cascade = '\n'.join(lines)

        body = '''/-
  Row C0 (loop-deletion / trivially-true coupling) FULLY CLOSED proof,
  emitted deterministically from the src/tgt IR text alone.
  Imports are PINNED (incl. MemoryRefinement): the `⊑` proved below is the
  fuel/memory-aware refinement, NOT the CFG-opaque collapse.
-/
{imports}
namespace_open

def_src

def_tgt

{abbrevs}

private abbrev {base}_ctx : Ctxt LLVM.Ty := ↑[{ctx_tys}]

private abbrev {sb} :
    CFGBlocks LLVM {base}_ctx .impure [{retty}] :=
  match {S} with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private abbrev {tb} :
    CFGBlocks LLVM {base}_ctx .impure [{retty}] :=
  match {Tg} with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private abbrev {rt} {{Γ : Ctxt LLVM.Ty}} : CFGTarget LLVM Γ :=
  {{ name := "{T}", argTys := [], args := HVector.nil }}

private abbrev {run}
    (blocks : CFGBlocks LLVM {base}_ctx .impure [{retty}])
    (fuel : Nat)
    (baseV : {base}_ctx.Valuation)
    {{Γcur : Ctxt LLVM.Ty}}
    (curV : Γcur.Valuation)
    (target : CFGTarget LLVM Γcur)
    (s : LLVMMemory.State) :
    ImmediateUBOr (HVector TyDenote.toType [{retty}] × LLVMMemory.State) :=
  StateT.run
    (ReaderT.run
      (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel blocks baseV curV target)
      ({{}} : LLVMMemory.FunctionEnv LLVMMemory.State))
    s

set_option maxHeartbeats 1000000 in
private theorem {core}
    (fuel extra : Nat)
    (baseV : {base}_ctx.Valuation)
    {{Γcur : Ctxt LLVM.Ty}}
    (curV : Γcur.Valuation)
    (target : CFGTarget LLVM Γcur)
    (s : LLVMMemory.State)
    (hentry : target.name ≠ "{ename}") :
    {run} {sb} fuel baseV curV target s
      ⊑
    {run} {tb} (fuel + extra) baseV baseV
        {rt} s := by
  induction fuel generalizing extra Γcur curV target s with
  | zero =>
      simp only [{run}, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.throwUB]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      rcases target with ⟨name, argTys, args⟩
{cascade}

set_option maxHeartbeats 1000000 in
theorem {base}_correct : {S} ⊑ {Tg} := by
  intro V s fuel
  cases fuel with
  | zero =>
      simp [{S}, {Tg},
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.throwUB]
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [{S}, {Tg},
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.Com.denoteWithMemoryFuelIn,
        LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?,
        LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore,
        LLVMMemory.Expr.denoteWithMemory]
      exact {core} fuel 0
        (InputValuation.lift V) _ _ s ({ntac})

namespace_close
'''.format(imports=PINNED_IMPORTS, abbrevs=abbrevs, base=base, sb=sb, tb=tb,
               rt=rt, run=run, core=core, S=S, Tg=Tg, T=T, ename=ename,
               retty=retty, ctx_tys=ctx_tys, cascade=cascade, ntac=c0tac)
        body = body.replace('namespace_open', _ns_open(ns))
        body = body.replace('namespace_close', _ns_close(ns))
        body = body.replace('def_src', src['verbatim'])
        body = body.replace('def_tgt', tgt['verbatim'])
        if wsym:
            body = _symbolize(body, base, (src['verbatim'], tgt['verbatim']))
        return {
            'status': 'ok',
            'reason': ('Row C0 loop-deletion trivial coupling: fully closed '
                       'fuel-induction proof, 0 sorries, MemoryRefinement pinned'
                       + (' (symbolic width %r)' % wsym if wsym else '')),
            'shape': 'C0',
            'expected_sorries': 0,
            'files': {case + '.lean': body},
        }


    def _c1_applicable(base, src, tgt):
        sf, tf = src['func'], tgt['func']
        if src['width_params'] or tgt['width_params']:
            return False, 'C1: width-generic input', None
        if not (_all_int(sf) and _all_int(tf)):
            return False, 'C1: non-int (ptr) types present', None
        if len(sf['args']) != 1 or len(tf['args']) != 1:
            return False, 'C1: v1 row requires exactly one function param', None
        if sf['args'][0][1] != tf['args'][0][1]:
            return False, 'C1: param types differ', None
        W = sf['args'][0][1][1]
        if sf['ret'] != ('int', W) or tf['ret'] != ('int', W):
            return False, 'C1: return width differs from param width', None
        if len(sf['blocks']) != 3 or len(tf['blocks']) != 3:
            return False, 'C1: v1 row requires exactly 3 blocks per side', None
        se, sl, sx = sf['blocks']
        te, tl, tx = tf['blocks']
        if se['name'] != te['name'] or sl['name'] != tl['name'] \
                or sx['name'] != tx['name']:
            return False, 'C1: block names not matched src<->tgt', None
        E, L, X = se['name'], sl['name'], sx['name']

        for xb in (sx, tx):
            if len(xb['args']) != 1 or xb['args'][0][1] != ('int', W) \
                    or xb['ops'] or xb['term']['kind'] != 'ret' \
                    or xb['term']['val'] != xb['args'][0][0]:
                return False, 'C1: exit block is not a bare return of its arg', None
        if _block_body_normalized(sx) != _block_body_normalized(tx):
            return False, 'C1: exit blocks not syntactically identical', None

        if len(se['ops']) != 1 or se['ops'][0]['kind'] != 'const' \
                or se['ops'][0]['ty'] != ('int', W):
            return False, 'C1: src entry is not a single width-W constant', None
        A = se['ops'][0]['val']
        if se['term']['kind'] != 'br' or se['term']['dest'] != L \
                or len(se['term']['args']) != 1 \
                or se['term']['args'][0][0] != se['ops'][0]['dst']:
            return False, 'C1: src entry does not br ^loop(const)', None

        if len(te['ops']) != 3:
            return False, 'C1: tgt entry is not const/const/binop', None
        o0, o1, o2 = te['ops']
        if o0['kind'] != 'const' or o0['ty'] != ('int', W) or o0['val'] != A:
            return False, ('C1: tgt entry first op is not the matched init '
                           'constant %d' % A), None
        if o1['kind'] != 'const' or o1['ty'] != ('int', W):
            return False, 'C1: tgt entry second op is not a width-W constant', None
        B = o1['val']
        if o2['kind'] != 'bin' or o2['ty'] != ('int', W) \
                or o2['op'] not in _C1_SYM_BINOPS:
            return False, ('C1: tgt entry third op is not a tabled int binop'), None
        param = tf['args'][0][0]
        if o2['a'] != param or o2['b'] != o1['dst']:
            return False, ('C1: tgt entry binop operands are not '
                           '(param, second-const)'), None
        if te['term']['kind'] != 'br' or te['term']['dest'] != L \
                or [a for a, _ in te['term']['args']] != [o0['dst'], o2['dst']]:
            return False, 'C1: tgt entry does not br ^loop(init, binop)', None

        if len(sl['args']) != 1 or sl['args'][0][1] != ('int', W):
            return False, 'C1: src loop must carry exactly one width-W arg', None
        if sl['term']['kind'] != 'cond_br':
            return False, 'C1: src loop terminator is not cond_br', None
        sdests = {sl['term']['dest1']: sl['term']['args1'],
                  sl['term']['dest2']: sl['term']['args2']}
        if set(sdests) != {L, X}:
            return False, 'C1: src loop successors are not {loop, exit}', None
        for op in sl['ops']:
            if not _int_table_ok(op, 'C1')[0]:
                return False, ('C1: src loop op outside int table: %r%s'
                               % (op['raw'], _int_table_why(op, 'C1'))), None

        if len(tl['args']) != 2 or any(t != ('int', W) for _, t in tl['args']):
            return False, 'C1: tgt loop must carry exactly two width-W args', None
        if tl['args'][0][0] != sl['args'][0][0]:
            return False, ('C1: tgt loop first carried arg not name-matched to '
                           'src carried arg'), None
        if tl['term']['kind'] != 'cond_br':
            return False, 'C1: tgt loop terminator is not cond_br', None
        tdests = {tl['term']['dest1']: tl['term']['args1'],
                  tl['term']['dest2']: tl['term']['args2']}
        if set(tdests) != {L, X}:
            return False, 'C1: tgt loop successors are not {loop, exit}', None
        if len(tdests[L]) != 2 or len(sdests[L]) != 1:
            return False, 'C1: backedge arg arity mismatch', None
        for op in tl['ops']:
            if not _int_table_ok(op, 'C1')[0]:
                return False, ('C1: tgt loop op outside int table: %r%s'
                               % (op['raw'], _int_table_why(op, 'C1'))), None
        info = {'W': W, 'A': A, 'B': B, 'op': o2['op'],
                'E': E, 'L': L, 'X': X}
        return True, '', info


    def _lit(n):
        return '(%d)' % n if n < 0 else str(n)


    def _c1_emit(case, parsed, base, src, tgt, info):
        ns = parsed['ns']
        W, A, B = info['W'], info['A'], info['B']
        op = info['op']
        E, L, X = info['E'], info['L'], info['X']
        p = base
        ity = '%s_ity' % p
        tpl = '''/-
  Row C1 multi-hole fuel-induction scaffold (name-matched single loop,
  int-only), emitted deterministically from the src/tgt IR text alone.

  IMPORT PINNING (soundness-critical): the 3-import header below INCLUDES
  SSA.Projects.InstCombine.MemoryRefinement; the meaning of ⊑ depends on
  this import.  Under these pinned imports the theorem below is the fuel/memory-aware
  refinement, not the CFG-opaque collapse.

  Holes (exactly 3 sorries):
    H1 (def)      @P@_coupling       -- invariant one-liner (LLM)
    H2 (theorem)  @P@_init_coupling  -- statement emitter-derived, proof sorry
    H3 (tactic)   succ case of @P@_loop_refine
-/
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0

namespace_open

def_src

def_tgt

-- [IR-DERIVED: scalar type abbrev from the signature]
private abbrev @ITY@ : LLVM.Ty := LLVM.Ty.bitvec @W@

-- [IR-DERIVED: function context]
private abbrev @P@_ctx : Ctxt LLVM.Ty := Ctxt.ofList [@ITY@]

-- [IR-DERIVED: fixed blocks-extractor template, one per side]
private def @P@_srcBlocks : CFGBlocks LLVM @P@_ctx .impure [@ITY@] :=
  match @P@_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

private def @P@_tgtBlocks : CFGBlocks LLVM @P@_ctx .impure [@ITY@] :=
  match @P@_tgt with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil

-- [IR-DERIVED: block-name inequality helpers for the H3 filler]
private theorem @P@_entry_ne_loop : ¬ ("@E@" = "@L@") := by
  decide

private theorem @P@_out_ne_loop : ¬ ("@X@" = "@L@") := by
  decide

-- [IR-DERIVED: canonicalization of the parser-generated function-input var]
private theorem @P@_input_var :
    (⟨0, by decide⟩ : @P@_ctx.Var @ITY@) =
      Ctxt.Var.last (Ctxt.ofList []) @ITY@ := by
  rfl

-- [IR-DERIVED: loop continuation targets from the ^@L@ block-arg lists]
private def @P@_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [@ITY@]) where
  name := "@L@"
  argTys := [@ITY@]
  args := Ctxt.Var.last (Ctxt.ofList []) @ITY@ ::ₕ HVector.nil

private def @P@_tgtLoopTarget : CFGTarget LLVM (Ctxt.ofList [@ITY@, @ITY@]) where
  name := "@L@"
  argTys := [@ITY@, @ITY@]
  args :=
    Ctxt.Var.last (Ctxt.ofList [@ITY@]) @ITY@ ::ₕ
      (⟨1, by decide⟩ : (Ctxt.ofList [@ITY@, @ITY@]).Var @ITY@) ::ₕ
        HVector.nil

-- [IR-DERIVED: loop-carried valuation constructors]
private def @P@_srcLoopVal (j : TyDenote.toType @ITY@) :
    Ctxt.Valuation (Ctxt.ofList [@ITY@]) :=
  Ctxt.Valuation.ofHVector (j ::ₕ HVector.nil)

private def @P@_tgtLoopVal (j i2 : TyDenote.toType @ITY@) :
    Ctxt.Valuation (Ctxt.ofList [@ITY@, @ITY@]) :=
  Ctxt.Valuation.ofHVector (j ::ₕ i2 ::ₕ HVector.nil)

/- [IR-DERIVED: emitter-OWNED adequacy lemma (machine-closes with the fixed
   script or the emitter declines): loop re-entry dispatch, src side.] -/
private theorem @P@_src_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation @P@_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γcur.Var @ITY@) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_srcBlocks V W
            ({ name := "@L@", argTys := [@ITY@], args := a ::ₕ HVector.nil } :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_srcBlocks V
            (@P@_srcLoopVal (W a)) @P@_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [@P@_src, @P@_srcBlocks, @P@_srcLoopTarget, @P@_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

private theorem @P@_tgt_loop_dispatch
    {Γcur : Ctxt LLVM.Ty} (V : Ctxt.Valuation @P@_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) (a b : Γcur.Var @ITY@) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_tgtBlocks V W
            ({ name := "@L@", argTys := [@ITY@, @ITY@],
                args := a ::ₕ b ::ₕ HVector.nil } : CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_tgtBlocks V
            (@P@_tgtLoopVal (W a) (W b)) @P@_tgtLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [@P@_tgt, @P@_tgtBlocks, @P@_tgtLoopTarget, @P@_tgtLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]

/- [IR-DERIVED: emitter-OWNED exit-block refinement lemma (name-matched "@X@"
   blocks with syntactically identical bodies); helper for the H3 filler.] -/
private theorem @P@_out_refine
    {Γsrc Γtgt : Ctxt LLVM.Ty} (V : Ctxt.Valuation @P@_ctx)
    (Wsrc : Ctxt.Valuation Γsrc) (Wtgt : Ctxt.Valuation Γtgt)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γsrc.Var @ITY@) (b : Γtgt.Var @ITY@)
    (h : Wsrc a = Wtgt b) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_srcBlocks V Wsrc
            ({ name := "@X@", argTys := [@ITY@], args := a ::ₕ HVector.nil } :
              CFGTarget LLVM Γsrc))
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_tgtBlocks V Wtgt
            ({ name := "@X@", argTys := [@ITY@], args := b ::ₕ HVector.nil } :
              CFGTarget LLVM Γtgt))
          ∅)
        s := by
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [@P@_src, @P@_tgt,
        @P@_srcBlocks, @P@_tgtBlocks, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, h]
      exact mem_result_le_self _

/- [IR-DERIVED: symbolic value of the ONE unmatched tgt loop-init argument,
   transcribed by the per-opcode table (@OP@ row, operand classes:
   function-input var × literal const).  Fixes the STATEMENT of hole H2.] -/
private def @P@_symInit (V : Ctxt.Valuation @P@_ctx) : TyDenote.toType @ITY@ :=
  match (V (Ctxt.Var.last (Ctxt.ofList []) @ITY@) : LLVM.IntWUB @W@) with
  | none => none
  | some x => some (LLVM.@OP@ x (LLVM.const? @W@ @B@))

/- [HOLE H1: the coupling — the value of the unmatched tgt loop-carried arg as
   a function of the src loop-carried state (j) and the function inputs (V).
   One-liner expected.  The LLM fills this.] -/
private def @P@_coupling (j : TyDenote.toType @ITY@)
    (V : Ctxt.Valuation @P@_ctx) : TyDenote.toType @ITY@ :=
  sorry

/- [HOLE H2 (proof only): init-coupling.  STATEMENT is emitter-derived: at loop
   entry the src carried value is the symbolic init `some (const? @W@ @A@)` and
   the coupling must equal the symbolic value of the unmatched tgt init
   argument (@P@_symInit).  The final assembly consumes this via
   `rw [...] at hcore` (the term-side rewrite is load-bearing).] -/
private theorem @P@_init_coupling (V : Ctxt.Valuation @P@_ctx) :
    @P@_coupling ((some (LLVM.const? @W@ @A@) : LLVM.IntWUB @W@) : TyDenote.toType @ITY@) V =
      @P@_symInit V := by
  sorry

-- [IR-DERIVED: fixed constant-denote adequacy lemma; must machine-close (rfl)]
private theorem @P@_const_denote (n : Int) :
    DialectDenote.denote (LLVM.Op.const @W@ n) HVector.nil HVector.nil =
      ((((some (LLVM.const? @W@ n) : LLVM.IntWUB @W@) : TyDenote.toType @ITY@) ::ₕ
        HVector.nil) : HVector TyDenote.toType [@ITY@]) := by
  rfl

-- [IR-DERIVED: per-opcode denote adequacy lemma (@OP@ row); machine-closes]
private theorem @P@_binop_denote_args (x y : TyDenote.toType @ITY@) :
    DialectDenote.denote (LLVM.Op.binary @W@ MOp.BinaryOp.@OP@) (x ::ₕ y ::ₕ HVector.nil)
        HVector.nil =
      (((match (x : LLVM.IntWUB @W@), (y : LLVM.IntWUB @W@) with
        | none, _ => none
        | _, none => none
        | some x', some y' => some (LLVM.@OP@ x' y')) : TyDenote.toType @ITY@) ::ₕ
          HVector.nil : HVector TyDenote.toType [@ITY@]) := by
  cases x <;> cases y <;> rfl

/- [IR-DERIVED (table row: entry-prefix normal form for a tgt entry of shape
   [const-init, const-B, binop(param, const-B)]): the LHS is the simp-normal
   form of the tgt entry-block binop denote as it appears in the final-assembly
   goal (constant-prefix valuation, de Bruijn index ⟨2,_⟩ for the function
   input in the 3-entry context).  Proof script fixed.] -/
private theorem @P@_binop_denote_in_loop
    (V : Ctxt.Valuation @P@_ctx) (j : TyDenote.toType @ITY@) :
    DialectDenote.denote (LLVM.Op.binary @W@ MOp.BinaryOp.@OP@)
        (((Ctxt.Valuation.ofHVector
              (DialectDenote.denote (LLVM.Op.const @W@ @B@) HVector.nil HVector.nil) ++
            j ::ᵥ V)
            ((⟨2, by decide⟩ :
              (Ctxt.ofList [@ITY@, @ITY@, @ITY@]).Var @ITY@))) ::ₕ
          ((Ctxt.Valuation.ofHVector
                (DialectDenote.denote (LLVM.Op.const @W@ @B@) HVector.nil HVector.nil) ++
              j ::ᵥ V)
              (Ctxt.Var.last (Ctxt.ofList [@ITY@, @ITY@]) @ITY@)) ::ₕ
            HVector.nil)
        HVector.nil
      = (@P@_symInit V ::ₕ HVector.nil) := by
  rw [@P@_const_denote, @P@_binop_denote_args]
  simp only [Ctxt.Valuation.ofHVector_cons, Ctxt.Valuation.ofHVector_nil,
    Ctxt.Valuation.cons_append, Ctxt.Valuation.nil_append]
  have hinput :
      (some (LLVM.const? @W@ @B@) ::ᵥ j ::ᵥ V)
          ((⟨2, by decide⟩ :
            (Ctxt.ofList [@ITY@, @ITY@, @ITY@]).Var @ITY@)) =
        V (Ctxt.Var.last (Ctxt.ofList []) @ITY@) := by
    rfl
  have hconst :
      (some (LLVM.const? @W@ @B@) ::ᵥ j ::ᵥ V)
          (Ctxt.Var.last (Ctxt.ofList [@ITY@, @ITY@]) @ITY@) =
        (some (LLVM.const? @W@ @B@) : TyDenote.toType @ITY@) := by
    rfl
  rw [hinput, hconst]
  cases hV : (V (Ctxt.Var.last (Ctxt.ofList []) @ITY@) : LLVM.IntWUB @W@) <;>
    simp [@P@_symInit, hV]

/- [IR-DERIVED: core fuel-induction lemma STATEMENT — src loop continuation at
   carried state j refines tgt loop continuation at (j, coupling j V); the
   name-matched arg passes through, the unmatched arg goes through the
   coupling.  Zero case auto-closed by the fixed out-of-fuel closer.] -/
set_option linter.unusedVariables false in
private theorem @P@_loop_refine
    (V : Ctxt.Valuation @P@_ctx) (s : LLVMMemory.State) (fuel : Nat)
    (j : TyDenote.toType @ITY@) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_srcBlocks V
            (@P@_srcLoopVal j) @P@_srcLoopTarget)
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_tgtBlocks V
            (@P@_tgtLoopVal j (@P@_coupling j V)) @P@_tgtLoopTarget)
          ∅)
        s := by
  induction fuel generalizing s j with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      /- [HOLE H3: the inductive step.  Framework-free IntW/BitVec math in the
         model style: case on poison of the carried value/inputs and on the
         branch condition; exit path closes via @P@_out_refine, backedge path
         re-enters via @P@_src_loop_dispatch / @P@_tgt_loop_dispatch + ih.] -/
      sorry

-- [IR-DERIVED: fixed final assembly; `rw [@P@_init_coupling] at hcore` is the
--  load-bearing term-side rewrite through the opaque coupling.]
theorem @P@_correct : @P@_src ⊑ @P@_tgt := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [@P@_src, @P@_tgt,
        LLVMMemory.Com.denoteWithMemoryFuel, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, simp_denote, simp_memory,
        Ctxt.Var.zero_eq_last]
      change
        StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_srcBlocks V.lift _ _)
              ∅)
            s
          ⊑
          StateT.run
            (ReaderT.run
              (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel @P@_tgtBlocks V.lift _ _)
              ∅)
            s
      rw [@P@_src_loop_dispatch, @P@_tgt_loop_dispatch]
      have hcore :=
        @P@_loop_refine V.lift s fuel
          ((some (LLVM.const? @W@ @A@) : LLVM.IntWUB @W@) : TyDenote.toType @ITY@)
      rw [@P@_init_coupling] at hcore
      simpa [-Ctxt.Var.zero_eq_last, @P@_srcLoopVal, @P@_tgtLoopVal,
        @P@_symInit, @P@_const_denote, @P@_binop_denote_in_loop,
        Ctxt.Var.last] using hcore

namespace_close
'''
        body = tpl.replace('@P@', p).replace('@ITY@', ity)
        body = body.replace('@W@', str(W)).replace('@A@', _lit(A))
        body = body.replace('@B@', _lit(B)).replace('@OP@', op)
        body = body.replace('@E@', E).replace('@L@', L).replace('@X@', X)
        body = body.replace('namespace_open', _ns_open(ns))
        body = body.replace('namespace_close', _ns_close(ns))
        body = body.replace('def_src', src['verbatim'])
        body = body.replace('def_tgt', tgt['verbatim'])
        return {
            'status': 'ok',
            'reason': ('Row C1 multi-hole fuel-induction skeleton: 3 typed holes '
                       '(H1 coupling def, H2 init-coupling proof, H3 succ-case); '
                       '3-import header incl. MemoryRefinement PINNED'),
            'shape': 'C1',
            'expected_sorries': 3,
            'files': {case + '.lean': body},
        }


    C1W_VERSION = 'C1W-widening-v1'


    _C1W_MAX_CARRIED = 4


    def _bare_return_block(b):
        return (len(b['args']) == 1 and not b['ops']
                and b['term']['kind'] == 'ret'
                and b['term']['val'] == b['args'][0][0])


    def _c1w_applicable(parsed, base, src, tgt):
        sf, tf = src['func'], tgt['func']


        wsym = None
        if src['width_params'] or tgt['width_params']:
            try:
                wsym = _wsym(src, tgt)
            except ParseError as e:
                return False, 'C1W: %s' % e, None
            ok, bad = _sym_widths_ok(wsym, [sf, tf])
            if not ok:
                return False, ('C1W: symbolic-width input also carries literal '
                               'width(s) %s beside the parameter %r'
                               % (bad, wsym)), None
        if not (_all_int(sf) and _all_int(tf)):
            return False, 'C1W: non-int (ptr) types present', None
        if [t for _, t in sf['args']] != [t for _, t in tf['args']]:
            return False, 'C1W: src/tgt param type lists differ', None
        ws = _int_widths([sf, tf])
        if len(ws) != 1:
            return False, ('C1W: mixed int widths in signature/block args '
                           '(single-width row)'), None
        W = ws.pop()
        if sf['ret'] != ('int', W) or tf['ret'] != ('int', W):
            return False, 'C1W: return width differs from the common width', None


        if not any('MemoryRefinement' in i for i in parsed['imports']) \
                and _is_multiblock(sf) and _is_multiblock(tf):
            return False, ('C1W: non-MemoryRefinement both-sides-multiblock '
                           'input stays in the Shape-C lane'), None

        if len(sf['blocks']) != 3:
            return False, 'C1W: src is not a 3-block entry/loop/exit CFG', None
        se, sl, sx = sf['blocks']
        E, L, X = se['name'], sl['name'], sx['name']
        if not _bare_return_block(sx):
            return False, 'C1W: src exit is not a bare return of its arg', None
        if sl['term']['kind'] != 'cond_br' or set(_successors(sl)) != {L, X}:
            return False, ('C1W: src middle block is not a cond_br self-loop '
                           'to {loop, exit}'), None
        m = len(sl['args'])
        if not (1 <= m <= _C1W_MAX_CARRIED):
            return False, ('C1W: src loop carries %d args (supported 1..%d)'
                           % (m, _C1W_MAX_CARRIED)), None
        if se['term']['kind'] == 'br':
            if se['term']['dest'] != L:
                return False, 'C1W: src entry br does not target the loop', None
        elif se['term']['kind'] == 'cond_br':
            if not set(_successors(se)) <= {L, X}:
                return False, ('C1W: src entry cond_br successors outside '
                               '{loop, exit}'), None
        else:
            return False, 'C1W: src entry terminator is a return', None
        for b in (se, sl):
            for op in b['ops']:
                if not _int_table_ok(op, 'C1W')[0]:
                    return False, ('C1W: src ^%s op outside int table: %r%s'
                                   % (b['name'], op['raw'],
                                      _int_table_why(op, 'C1W'))), None
        info = {'W': W, 'E': E, 'L': L, 'X': X, 'm': m,
                'npar': len(sf['args']), 'wsym': wsym}

        tb = tf['blocks']
        if len(tb) == 3:
            te, tl, tx = tb
            TL, TX = tl['name'], tx['name']
            if not _bare_return_block(tx):
                return False, 'C1W: tgt exit is not a bare return of its arg', None
            if tl['term']['kind'] != 'cond_br' \
                    or set(_successors(tl)) != {TL, TX}:
                return False, ('C1W: tgt middle block is not a cond_br '
                               'self-loop to {loop, exit}'), None
            k = len(tl['args'])
            if not (1 <= k <= _C1W_MAX_CARRIED):
                return False, ('C1W: tgt loop carries %d args (supported 1..%d)'
                               % (k, _C1W_MAX_CARRIED)), None
            if te['term']['kind'] != 'br' or te['term']['dest'] != TL:
                return False, 'C1W: tgt entry does not br to its loop', None
            for op in tl['ops']:
                if not _int_table_ok(op, 'C1W')[0]:
                    return False, ('C1W: tgt ^%s op outside int table: %r%s'
                                   % (tl['name'], op['raw'],
                                      _int_table_why(op, 'C1W'))), None
            info.update(variant='loop', TL=TL, TX=TX, k=k)
            return True, '', info
        if len(tb) == 2:
            te, tx = tb
            TX = tx['name']
            if not _bare_return_block(tx):
                return False, 'C1W: tgt exit is not a bare return of its arg', None
            if te['term']['kind'] != 'br' or te['term']['dest'] != TX \
                    or len(te['term']['args']) != 1:
                return False, ('C1W: tgt entry is not `br ^exit(<one arg>)`'), None
            info.update(variant='exitbr', TX=TX)
            return True, '', info
        if len(tb) == 1:
            if tb[0]['term']['kind'] != 'ret':
                return False, 'C1W: single-block tgt does not return', None


            if any(o['kind'] == 'assume' for o in tb[0]['ops']):
                return False, ('C1W: single-block tgt carries `llvm.assume`, so it '
                               'elaborates as .impure and the straight row\'s '
                               '`castPureToEff .impure` cannot apply'), None
            info.update(variant='straight')
            return True, '', info
        return False, ('C1W: tgt has %d blocks (supported: 1, 2, or 3)'
                       % len(tb)), None


    def _c1w_names(prefix, n):
        return ['%s%d' % (prefix, i + 1) for i in range(n)]


    def _c1w_var(i, tys, ity, tac='by decide'):
        return '(⟨%d, %s⟩ : (Ctxt.ofList [%s]).Var %s)' % (i, tac, tys, ity)


    def _c1w_emit(case, parsed, base, src, tgt, info):
        ns = parsed['ns']
        p = base
        ity = '%s_ity' % p
        W = info['W']
        wsym = info.get('wsym')
        vtac = 'by rfl' if wsym else 'by decide'
        variant = info['variant']
        E, L, X, m, npar = info['E'], info['L'], info['X'], info['m'], info['npar']
        js = _c1w_names('j', m)
        jbind = ' '.join(js)
        jargs = ' '.join(js)
        avars = _c1w_names('a', m)
        stys = ', '.join([ity] * m)
        ptys = ', '.join([ity] * npar)

        def hv(items):
            return ' ::ₕ '.join(items + ['HVector.nil'])

        def run(blocks, val, target, fuelx='fuel'):
            return ('StateT.run\n'
                    '          (ReaderT.run\n'
                    '            (LLVMMemory.CFGTarget.denoteWithMemoryFuel '
                    '%s %s V\n'
                    '              (%s) %s)\n'
                    '            ∅)\n'
                    '          s' % (fuelx, blocks, val, target))

        holes = []
        ubs = []


        pidx = _poison_input_indices(src['func'])
        undis = [nm for i, (nm, _t) in enumerate(src['func']['args'])
                 if i not in pidx]


        undis_note = ('' if not undis else
                      '\n         NOTE — input(s) %s are NOT discharged by the emitter: their'
                      '\n         poison never reaches a branch condition, so the source is not'
                      '\n         immediately UB and no one-step discharge exists.  Their poison'
                      '\n         has to be CARRIED by this induction to the exit, where'
                      '\n         `LLVM.SemVal.poison_isRefinedBy` closes it (poison refines'
                      '\n         anything).  Case on them here alongside the carried values.'
                      % ', '.join('`%%%s`' % nm for nm in undis))

        parts = []
        parts.append('''-- [IR-DERIVED: scalar type abbrev from the signature]
private abbrev {ity} : LLVM.Ty := LLVM.Ty.bitvec {W}

-- [IR-DERIVED: function context ({npar} param(s))]
private abbrev {p}_ctx : Ctxt LLVM.Ty := Ctxt.ofList [{ptys}]

-- [IR-DERIVED: fixed blocks-extractor template, src side]
private def {p}_srcBlocks : CFGBlocks LLVM {p}_ctx .impure [{ity}] :=
  match {p}_src with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil
'''.format(ity=ity, W=W, p=p, ptys=ptys, npar=npar))

        if variant in ('loop', 'exitbr'):
            parts.append('''private def {p}_tgtBlocks : CFGBlocks LLVM {p}_ctx .impure [{ity}] :=
  match {p}_tgt with
  | Com.cfg _ blocks _ => blocks
  | _ => CFGBlocks.nil
'''.format(p=p, ity=ity))

        parts.append('''-- [IR-DERIVED: block-name inequality helpers for the hole fillers]
private theorem {p}_entry_ne_loop : ¬ ("{E}" = "{L}") := by
  decide

private theorem {p}_out_ne_loop : ¬ ("{X}" = "{L}") := by
  decide
'''.format(p=p, E=E, L=L, X=X))


        src_args_hv = hv([_c1w_var(i, stys, ity, vtac) for i in range(m)])
        parts.append('''-- [IR-DERIVED: src loop continuation target ({m} carried arg(s))]
private def {p}_srcLoopTarget : CFGTarget LLVM (Ctxt.ofList [{stys}]) where
  name := "{L}"
  argTys := [{stys}]
  args := {args}

private def {p}_srcLoopVal ({jbind} : TyDenote.toType {ity}) :
    Ctxt.Valuation (Ctxt.ofList [{stys}]) :=
  Ctxt.Valuation.ofHVector ({jhv})
'''.format(p=p, m=m, stys=stys, L=L, args=src_args_hv, jbind=jbind, ity=ity,
               jhv=hv(js)))

        abind = ' '.join(avars)
        a_args_hv = hv(avars)
        wa = ' '.join('(W %s)' % a for a in avars)
        parts.append('''/- [IR-DERIVED: emitter-OWNED adequacy lemma (machine-closes with the fixed
   script or the emitter declines): loop re-entry dispatch, src side.] -/
private theorem {p}_src_loop_dispatch
    {{Γcur : Ctxt LLVM.Ty}} (V : Ctxt.Valuation {p}_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) ({abind} : Γcur.Var {ity}) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_srcBlocks V W
            ({{ name := "{L}", argTys := [{stys}], args := {ahv} }} :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_srcBlocks V
            ({p}_srcLoopVal {wa}) {p}_srcLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [{p}_src, {p}_srcBlocks, {p}_srcLoopTarget, {p}_srcLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]
'''.format(p=p, abind=abind, ity=ity, L=L, stys=stys, ahv=a_args_hv, wa=wa))

        if variant == 'loop':
            TL, TX, k = info['TL'], info['TX'], info['k']
            bvars = _c1w_names('b', k)
            ttys = ', '.join([ity] * k)
            tgt_args_hv = hv([_c1w_var(i, ttys, ity, vtac) for i in range(k)])
            ivars = _c1w_names('i', k)
            parts.append('''-- [IR-DERIVED: tgt loop continuation target ({k} carried arg(s))]
private def {p}_tgtLoopTarget : CFGTarget LLVM (Ctxt.ofList [{ttys}]) where
  name := "{TL}"
  argTys := [{ttys}]
  args := {args}

private def {p}_tgtLoopVal ({ibind} : TyDenote.toType {ity}) :
    Ctxt.Valuation (Ctxt.ofList [{ttys}]) :=
  Ctxt.Valuation.ofHVector ({ihv})
'''.format(p=p, k=k, ttys=ttys, TL=TL, args=tgt_args_hv,
               ibind=' '.join(ivars), ity=ity, ihv=hv(ivars)))

            bbind = ' '.join(bvars)
            b_args_hv = hv(bvars)
            wb = ' '.join('(W %s)' % b for b in bvars)
            parts.append('''private theorem {p}_tgt_loop_dispatch
    {{Γcur : Ctxt LLVM.Ty}} (V : Ctxt.Valuation {p}_ctx) (W : Ctxt.Valuation Γcur)
    (fuel : Nat) (s : LLVMMemory.State) ({bbind} : Γcur.Var {ity}) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_tgtBlocks V W
            ({{ name := "{TL}", argTys := [{ttys}], args := {bhv} }} :
              CFGTarget LLVM Γcur))
          ∅)
        s =
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_tgtBlocks V
            ({p}_tgtLoopVal {wb}) {p}_tgtLoopTarget)
          ∅)
        s := by
  cases fuel <;>
    simp [{p}_tgt, {p}_tgtBlocks, {p}_tgtLoopTarget, {p}_tgtLoopVal,
      LLVMMemory.CFGTarget.denoteWithMemoryFuel, LLVMMemory.CFGBlocks.findMemoryBlock?]
'''.format(p=p, bbind=bbind, ity=ity, TL=TL, ttys=ttys, bhv=b_args_hv, wb=wb))

        if variant in ('loop', 'exitbr'):
            TX = info['TX']
            parts.append('''/- [IR-DERIVED: emitter-OWNED exit-block refinement lemma (bare-return exit
   blocks on both sides); helper for the succ-case filler.] -/
private theorem {p}_out_refine
    {{Γsrc Γtgt : Ctxt LLVM.Ty}} (V : Ctxt.Valuation {p}_ctx)
    (Wsrc : Ctxt.Valuation Γsrc) (Wtgt : Ctxt.Valuation Γtgt)
    (fuel : Nat) (s : LLVMMemory.State) (a : Γsrc.Var {ity}) (b : Γtgt.Var {ity})
    (h : Wsrc a = Wtgt b) :
    StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_srcBlocks V Wsrc
            ({{ name := "{X}", argTys := [{ity}], args := a ::ₕ HVector.nil }} :
              CFGTarget LLVM Γsrc))
          ∅)
        s
      ⊑
      StateT.run
        (ReaderT.run
          (LLVMMemory.CFGTarget.denoteWithMemoryFuel fuel {p}_tgtBlocks V Wtgt
            ({{ name := "{TX}", argTys := [{ity}], args := b ::ₕ HVector.nil }} :
              CFGTarget LLVM Γtgt))
          ∅)
        s := by
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
      simp [{p}_src, {p}_tgt,
        {p}_srcBlocks, {p}_tgtBlocks, LLVMMemory.CFGTarget.denoteWithMemoryFuel,
        LLVMMemory.CFGBlocks.findMemoryBlock?, LLVMMemory.CFGBody.denoteWithMemoryFuelCore,
        LLVMMemory.CFGTerm.denoteWithMemoryFuelCore, h]
      exact mem_result_le_self _
'''.format(p=p, ity=ity, X=X, TX=TX))


        ubs, ubopaque = _tgt_ub_holes(tgt['func']['blocks'][0], W)
        ubbind = ' '.join('a%d' % (i + 1) for i in range(npar))
        ubsig = (' (%s : BitVec %s)' % (ubbind, W)) if npar else ''


        hu_src_pre = []
        hu_src_pre_note = 'loop'

        hu_pre_used = []

        def _emit_tgt_ub_holes():
            def _hu_needs_premises(prop):


                return bool(re.search(r'\ba\d+\b', prop))

            def _shyps_for(prop):
                use = hu_src_pre if _hu_needs_premises(prop) else []
                if use:
                    hu_pre_used.append(True)
                return use, ''.join(' (hs%d : %s)' % (i + 1, sp[1])
                                    for i, sp in enumerate(use))
            snote_t = (
                '\n   PREMISES `hs1`..`hs%d` are the SOURCE\'s OWN conditions on its FIRST\n'
                '   iteration -- the source loop body evaluated at the entry block\'s initial\n'
                '   carried values.  A target entry op that was HOISTED out of the source loop\n'
                '   (the LICM shape) is not UB-free outright: it is UB-free BECAUSE the source\n'
                '   already required the same thing.  Stated with no premise the obligation\n'
                '   quantifies over all inputs and is simply FALSE, which is why it carries\n'
                '   them.  Where a premise FAILS the source itself is poison on its first\n'
                '   iteration and a poison source refines anything, so discharging `hs*` is the\n'
                '   final-assembly hole\'s job, not this one\'s.')


            snote_e = (
                '\n   PREMISES `hs1`..`hs%d` are conditions the SOURCE\'s OWN ENTRY block\n'
                '   already imposes: its `llvm.assume` conditions, and the UB conditions of\n'
                '   its unconditionally executed entry ops.  Where one FAILS the source is\n'
                '   itself immediately UB (a false assume / a zero divisor / poison reaching\n'
                '   an assume or the loop branch), and an immediately-UB source refines\n'
                '   anything -- so discharging `hs*` is the final-assembly hole\'s job, not\n'
                '   this one\'s.  Stated with no premise this obligation would quantify over\n'
                '   ALL inputs and could be false.')
            for hn, (tag, prop, why, raw) in enumerate(ubs, 1):
                hyps = ''.join(' (hu%d : %s)' % (m, ubs[m - 1][1])
                               for m in range(1, hn))
                use, shyps = _shyps_for(prop)
                snote = ('' if not use else
                         (snote_t if hu_src_pre_note == 'loop' else snote_e)
                         % len(use))
                holes.append(('HU%d' % hn, 'target-specific UB (%s)' % tag))
                parts.append('''/- [HOLE HU{hn}: TARGET-SPECIFIC UB — the `target_ub_hole`.
   {why}.
   Target op: `{raw}`
   If it fires the TARGET is poison / immediately UB where the source was
   neither, so `src ⊑ tgt` fails.  Proving this is the obligation the
   transformation silently assumes.  The LLM proves it.{snote}] -/
private theorem {p}_tgt_ub{hn}{ubsig}{shyps}{hyps} :
    {prop} :=
  sorry
'''.format(hn=hn, why=why, raw=raw, p=p, ubsig=ubsig, hyps=hyps, prop=prop,
                   shyps=shyps, snote=snote))


        value_emitted = False


        lhs = run('%s_srcBlocks' % p, '%s_srcLoopVal %s' % (p, jargs),
                  '%s_srcLoopTarget' % p)
        lhs1 = run('%s_srcBlocks' % p, '%s_srcLoopVal %s' % (p, jargs),
                   '%s_srcLoopTarget' % p, fuelx='(fuel + 1)')

        def _emit_step_and_refine(hid, rhs, rhs1, guidance, pre='', binders=None):
            bind = jbind if binders is None else binders
            holes.append((hid, 'inductive step of the fuel induction'))
            parts.append('''/- [HOLE {hid}: the inductive step of the fuel induction, as a STANDALONE
   typed lemma — the induction hypothesis is the explicit `ih` binder, so the
   obligation kernel-checks, audits and retries on its own, exactly like the
   single-block row's holes and the `value_hole`.
   {guidance}{un}] -/
private theorem {p}_step (V : Ctxt.Valuation {p}_ctx) (fuel : Nat)
    (ih : ∀ (s : LLVMMemory.State) ({bind} : TyDenote.toType {ity}),
      {pre}{lhs}
        ⊑
        {rhs}) :
    ∀ (s : LLVMMemory.State) ({bind} : TyDenote.toType {ity}),
      {pre}{lhs1}
        ⊑
        {rhs1} :=
  sorry

/- [IR-DERIVED: core fuel-induction lemma — BOTH cases are emitted: the zero
   case by the fixed out-of-fuel closer, the succ case by the step lemma
   above.  No hole is left inside this proof.] -/
private theorem {p}_loop_refine (V : Ctxt.Valuation {p}_ctx) :
    ∀ (fuel : Nat) (s : LLVMMemory.State) ({bind} : TyDenote.toType {ity}),
      {pre}{lhs}
        ⊑
        {rhs} := by
  intro fuel
  induction fuel with
  | zero =>
      intro s {bind}{zpre}
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel ih =>
      exact {p}_step V fuel ih
'''.format(hid=hid, p=p, jb=jbind, bind=bind, ity=ity, lhs=lhs, lhs1=lhs1,
               rhs=rhs, rhs1=rhs1, pre=pre, guidance=guidance,


               un=undis_note.replace('\n         ', '\n   '),
               zpre=' _hinv' if pre else ''))

        if variant == 'loop':
            k = info['k']


            bb_all = '%s %s' % (jbind, bbind)
            ba_all = '%s %s' % (jargs, bbind)
            inv_app = '%s_inv %s V' % (p, ba_all)
            holes.append(('H1', 'relational loop invariant (src state × tgt '
                          'state × inputs)'))
            parts.append("""/- [HOLE H1: the RELATIONAL loop invariant — a predicate relating the src
   loop-carried state ({jb}) to the tgt loop-carried state ({bbv}) and the
   function inputs (V).  It must be (a) established by the two entry blocks,
   (b) preserved across the backedge, and (c) strong enough to prove the step
   below and every HL obligation.  The LLM fills this.] -/
private def {p}_inv ({jb} : TyDenote.toType {ity})
    ({bbv} : TyDenote.toType {ity})
    (V : Ctxt.Valuation {p}_ctx) : Prop :=
  sorry
""".format(p=p, jb=jbind, bbv=bbind, ity=ity))


            hu_src_pre = _c1w_src_first_iter_premises(src, W, npar)


            _emit_tgt_ub_holes()


            avars = _c1w_names('a', npar)
            fargmap = {nm: avars[i]
                       for i, (nm, _t) in enumerate(tgt['func']['args'])}
            lubs, lubopaque = _tgt_ub_holes(tgt['func']['blocks'][1], W,
                                            prefix='x', extra=fargmap)
            xvars = _c1w_names('x', k)
            for hn, (tag, prop, why, raw) in enumerate(lubs, 1):
                prev = ''.join(' (hl%d : %s)' % (m, lubs[m - 1][1])
                               for m in range(1, hn))
                holes.append(('HL%d' % hn,
                              'target-specific UB in the tgt LOOP BODY (%s)' % tag))
                parts.append("""/- [HOLE HL{hn}: TARGET-SPECIFIC UB inside the tgt LOOP BODY — a
   PER-ITERATION obligation.  {why}.
   Target op: `{raw}`
   Unlike the HU series (which is about the entry block and holds outright),
   this one only has to hold on the states the loop actually REACHES, so it is
   stated UNDER THE INVARIANT.  That premise is exactly what a relational
   invariant provides and a functional coupling cannot: quantified over all
   source states the same claim would simply be false.  The LLM proves it.] -/
private theorem {p}_tgt_loop_ub{hn}
    (V : Ctxt.Valuation {p}_ctx) ({bball} : TyDenote.toType {ity})
    (hinv : {inv})
    ({xb} : BitVec {W}){xhyps}
    ({ab} : BitVec {W}){ahyps}{prev} :
    {prop} :=
  sorry
""".format(hn=hn, why=why, raw=raw, p=p, ity=ity, W=W, inv=inv_app,
                   bball=bb_all, xb=' '.join(xvars), ab=' '.join(avars),
                   prev=prev, prop=prop,
                   xhyps=''.join(
                       ' (hx%d : %s = pure (LLVM.SemVal.value %s))'
                       % (i + 1, bvars[i], xvars[i]) for i in range(k)),
                   ahyps=''.join(
                       ' (ha%d : V (%s) = pure (LLVM.SemVal.value %s))'
                       % (i + 1, _arg_var(i, npar, p, ity), avars[i])
                       for i in range(npar))))
            if lubopaque:
                parts.append("""/- [CAUTION: {n} op(s) in the tgt LOOP BODY are outside the UB-obligation
   analysis, so any UB they carry is NOT named by an HL hole and remains the
   inductive step's responsibility: {ops}] -/
""".format(n=len(lubopaque), ops='; '.join(lubopaque[:3])))
            rhs = run('%s_tgtBlocks' % p, '%s_tgtLoopVal %s' % (p, bbind),
                      '%s_tgtLoopTarget' % p)
            rhs1 = run('%s_tgtBlocks' % p, '%s_tgtLoopVal %s' % (p, bbind),
                       '%s_tgtLoopTarget' % p, fuelx='(fuel + 1)')
            _emit_step_and_refine(
                'H2', rhs, rhs1,
                ('Framework-free IntW/BitVec math in the model style: case on\n'
                 '   poison of the carried values/inputs and on the branch\n'
                 '   condition; exit path closes via {p}_out_refine, backedge path\n'
                 '   re-enters via {p}_src_loop_dispatch / {p}_tgt_loop_dispatch\n'
                 '   + ih, RE-ESTABLISHING the invariant at the next state.\n'
                 '   The tgt loop body\'s UB obligations are the HL lemma(s) above —\n'
                 '   apply them rather than re-deriving them.').format(p=p),
                pre='%s →\n      ' % inv_app,
                binders=bb_all)
        else:


            tgtval, tgtwhy = _tgt_result_expr(tgt['func'], variant, W, p, ity, npar)


            emitted_ubnote = (
                ('' if not ubs else
                 '\n   The %d TARGET-SPECIFIC UB obligation(s) HU1..HU%d below are proved\n'
                 '   separately; this printed term is the faithful denotation, so the\n'
                 '   obligations say when it stays a plain value.' % (len(ubs), len(ubs)))
                + ('' if not ubopaque else
                   '\n   CAUTION: %d target op(s) are outside the UB-obligation analysis,\n'
                   '   so any UB they carry is NOT named by an HU hole and is still\n'
                   '   carried by this value: %s\n  ' % (len(ubopaque),
                                                         '; '.join(ubopaque[:3]))))
            ubnote = (('' if not ubs else
                       '\n   The %d TARGET-SPECIFIC UB obligation(s) HU1..HU%d below are proved\n'
                       '   separately, so this result may be written as a plain value rather\n'
                       '   than a poison-aware one.' % (len(ubs), len(ubs)))
                      + ('' if not ubopaque else
                         '\n   CAUTION: %d target op(s) are outside the UB-obligation analysis,\n'
                         '   so any UB they carry is NOT named by an HU hole and is still\n'
                         '   carried by this value: %s\n  ' % (len(ubopaque),
                                                               '; '.join(ubopaque[:3]))))
            if tgtval is not None:
                value_emitted = True
                parts.append('''/- [IR-DERIVED: the RESULT of the (loop-free) tgt side as a function of the
   inputs (V).  This is NOT a hole: a loop-free target computes an expression
   TREE that is written in the IR, so the emitter prints it rather than asking
   for it.  What has no closed form is the SOURCE loop — that is what the
   invariant and the inductive step below are for.{ubnote}] -/
private def {p}_tgtResult (V : Ctxt.Valuation {p}_ctx) : TyDenote.toType {ity} :=
  {expr}
'''.format(p=p, ity=ity, expr=tgtval, ubnote=emitted_ubnote))
            else:
                value_emitted = False
                holes.append(('H1', 'symbolic tgt result value'))
                parts.append('''/- [HOLE H1: the symbolic RESULT of the (loop-free) tgt side as a function of
   the inputs (V) — e.g. the closed form the transform introduced.  One-liner
   expected.  The LLM fills this.
   (The emitter prints this value itself when it can; here it cannot, because
   {why}.){ubnote}] -/
private def {p}_tgtResult (V : Ctxt.Valuation {p}_ctx) : TyDenote.toType {ity} :=
  sorry
'''.format(p=p, ity=ity, why=tgtwhy, ubnote=ubnote))


            hu_src_pre = _c1w_src_entry_hu_premises(src, W)
            hu_src_pre_note = 'entry'
            _emit_tgt_ub_holes()
            holes.append(('H2', 'loop invariant (coupling to the tgt result)'))
            parts.append('''/- [HOLE H2: the degenerate coupling — an invariant on the src loop-carried
   state ({jb}) strong enough to prove the core lemma below AND established
   by the src entry block.  The LLM fills this.] -/
private def {p}_inv ({jb} : TyDenote.toType {ity})
    (V : Ctxt.Valuation {p}_ctx) : Prop :=
  sorry
'''.format(p=p, jb=jbind, ity=ity))
            if variant == 'exitbr':
                TX = info['TX']
                parts.append('''-- [IR-DERIVED: tgt exit continuation target (loop-free tgt side)]
private def {p}_tgtExitTarget : CFGTarget LLVM (Ctxt.ofList [{ity}]) where
  name := "{TX}"
  argTys := [{ity}]
  args := {var} ::ₕ HVector.nil

private def {p}_tgtExitVal (r : TyDenote.toType {ity}) :
    Ctxt.Valuation (Ctxt.ofList [{ity}]) :=
  Ctxt.Valuation.ofHVector (r ::ₕ HVector.nil)
'''.format(p=p, ity=ity, TX=TX, var=_c1w_var(0, ity, ity, vtac)))
                rhs = run('%s_tgtBlocks' % p,
                          '%s_tgtExitVal (%s_tgtResult V)' % (p, p),
                          '%s_tgtExitTarget' % p)
                rhs1 = run('%s_tgtBlocks' % p,
                           '%s_tgtExitVal (%s_tgtResult V)' % (p, p),
                           '%s_tgtExitTarget' % p, fuelx='(fuel + 1)')
            else:
                rhs = ('(some ({p}_tgtResult V ::ₕ HVector.nil, s) :\n'
                       '          ImmediateUBOr (HVector TyDenote.toType [{ity}] '
                       '× LLVMMemory.State))').format(p=p, ity=ity)


                rhs1 = rhs
            _emit_step_and_refine(
                'H3', rhs, rhs1,
                ('Case on poison of the carried values / inputs and on the\n'
                 '   branch condition; exit path closes from the invariant{outref},\n'
                 '   backedge path re-enters via {p}_src_loop_dispatch + ih\n'
                 '   (re-establish the invariant).').format(
                     p=p,
                     outref=(' via %s_out_refine' % p) if variant == 'exitbr' else ''),
                pre='%s_inv %s V →\n      ' % (p, jargs))


        argnm = {nm: "av%d'" % (k + 1) for k, (nm, _t) in enumerate(src['func']['args'])}
        covered = {src['func']['args'][k][0] for k in pidx}
        eubs = (_entry_ub_discharges_multi(src['func'], W, argnm, covered,
                                           bool(wsym))
                if pidx else [])


        _has_asm = any(o['kind'] == 'assume'
                       for b in src['func']['blocks'] for o in b['ops'])
        _simp = 'simp +decide' if _has_asm else 'simp'


        _entry_ops_raw = [o.get('raw', '') or ''
                          for o in src['func']['blocks'][0]['ops']]
        _argset = {nm for nm, _t in src['func']['args']}
        _two_arg_op = any(
            len({t.lstrip('%') for t in re.findall(r'%[A-Za-z0-9_.]+', raw)
                 if t.lstrip('%') in _argset}) >= 2
            for raw in _entry_ops_raw)
        _strong_closer = _has_asm or _two_arg_op

        def _closer(setstr):
            if not _strong_closer:
                return '<;> rfl'
            return ("<;> (try (rintro a b ⟨rfl, rfl⟩)) <;> (repeat' split) "
                    "<;> (try (rintro a b ⟨rfl, rfl⟩)) "
                    "<;> (first | rfl | (intros; first | rfl | simp_all [%s]))"
                    % setstr)


        _bind_emitted = False
        if _strong_closer and pidx:
            parts.append('''/- [IR-DERIVED: binding anything to a constant poison is poison.  Needed by the
   guard discharges below, which reduce a poisoned entry-block value through the
   loop's branch condition.] -/
private theorem {p}_semval_bind_poison {{α β : Type}} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl
'''.format(p=p))
            _bind_emitted = True
        if pidx:
            simpset = _src_denote_simpset(
                p, src['func'],
                (('%s_semval_bind_poison' % p,) if _strong_closer else ()))
            _old_tail = ("<;> (try (rintro a b ⟨rfl, rfl⟩)) <;> rfl"
                         if _has_asm else '<;> rfl')


            if _strong_closer:
                step = ('        first\n'
                        '          | (%s [%s] %s)\n'
                        '          | (%s [%s] %s)'
                        % (_simp, simpset, _old_tail,
                           _simp, simpset, _closer(simpset)))
            else:
                step = '        %s [%s] %s' % (_simp, simpset, _old_tail)
            for k in pidx:
                parts.append('''/- [IR-DERIVED: emitter-OWNED poison-input discharge (argument {k}).
   Branching on poison is `throwUB` (MemoryModel.lean,
   CFGTerm.denoteWithMemoryFuelCore), and this input provably reaches a branch
   condition — the loop's, or the entry block's own when the entry ends in
   `cond_br` — so a poison input makes the SOURCE immediately UB, which refines
   whatever the target does.  This is the CFG counterpart of the single-block
   row's auto-discharged UB branches: the `poison` case of the final theorem
   below is closed by the emitter, not left inside the hole.  Three fuel cases
   because the entry block consumes one unit before the loop's cond_br fires.] -/
private theorem {p}_src_ub_of_poison_input{k}
    (V : InstCombine.InputValuation {p}_ctx) (fuel : Nat) (s : LLVMMemory.State)
    (hA : V ({avar}) = LLVM.SemVal.poison) :
    LLVMMemory.Com.denoteWithMemoryFuel fuel {p}_src
        (V := InstCombine.InputValuation.lift V) s = none := by
  match fuel with
  | 0 =>
{step}
  | 1 =>
{step}
  | (n + 2) =>
{step}
'''.format(p=p, k=k, step=step,
               avar=_arg_var(k, npar, p, ity)))
        if eubs:
            base_extra = ('hg', '%s_semval_bind_poison' % p)
            if not _bind_emitted:
                parts.append('''/- [IR-DERIVED: binding anything to a constant poison is poison.  Needed by the
   guard discharges below, which reduce a poisoned entry-block value through the
   loop's branch condition.] -/
private theorem {p}_semval_bind_poison {{α β : Type}} (x : LLVM.SemVal α) :
    (x >>= fun _ => (LLVM.SemVal.poison : LLVM.SemVal β)) =
      (LLVM.SemVal.poison : LLVM.SemVal β) := by
  cases x <;> rfl
'''.format(p=p))
            for gn, (tag, guard, why, raw) in enumerate(eubs, 1):


                prev = ''.join(' (hg%d : ¬ (%s))' % (m, eubs[m - 1][1])
                               for m in range(1, gn))


                nconj = guard.count(' ∧ ')
                parts_h = ['hgc%d' % (i + 1) for i in range(nconj + 1)]
                obtain = ('' if not nconj else
                          '        obtain ⟨%s⟩ := hg\n' % ', '.join(parts_h))
                extra_h = tuple(parts_h) if nconj else ('hg',)
                gset = _src_denote_simpset(
                    p, src['func'],
                    ('%s_semval_bind_poison' % p,) + extra_h
                    + tuple('hg%d' % m for m in range(1, gn)),
                    hnames=tuple('hA%d' % q for q in pidx))
                if _strong_closer:
                    gstep = obtain + ('        first\n'
                                      '          | (%s [%s] %s)\n'
                                      '          | (%s [%s] %s)'
                                      % (_simp, gset, _old_tail,
                                         _simp, gset, _closer(gset)))
                else:
                    gstep = obtain + '        %s [%s] %s' % (_simp, gset, _old_tail)
                parts.append('''/- [IR-DERIVED: emitter-OWNED UB discharge ({tag}).  {why}; that poison reaches
   the loop's branch condition, and branching on poison is `throwUB`, so the
   SOURCE is immediately UB — which refines anything the target does.  This is
   the CFG counterpart of the single-block row's auto-discharged UB branches.
   Entry op: `{raw}`] -/
private theorem {p}_src_ub_of_{tag}{gn}
    (V : InstCombine.InputValuation {p}_ctx) (fuel : Nat) (s : LLVMMemory.State)
    ({avb} : BitVec {W}){hAs}{prev}
    (hg : {guard}) :
    LLVMMemory.Com.denoteWithMemoryFuel fuel {p}_src
        (V := InstCombine.InputValuation.lift V) s = none := by
  match fuel with
  | 0 =>
{gstep}
  | 1 =>
{gstep}
  | (n + 2) =>
{gstep}
'''.format(p=p, ity=ity, W=W, tag=tag, gn=gn, guard=guard, why=why, raw=raw,
               gstep=gstep, prev=prev,
               avb=' '.join("av%d'" % (k + 1) for k in pidx),
               hAs=''.join(
                   ' (hA%d : V (%s) = LLVM.SemVal.value av%d\')'
                   % (k, _arg_var(k, npar, p, ity), k + 1) for k in pidx)))


        hfin = 'H3' if variant == 'loop' else 'H4'
        holes.append((hfin, 'final assembly: entry-block reduction to the core '
                      'lemma'))
        if variant == 'loop':


            guidance = ('unfold both entry blocks (simp with the two block sets\n'
                        '         + LLVMMemory.Com.denoteWithMemoryFuel/'
                        'denoteWithMemoryFuelIn +\n'
                        '         CFGTarget/CFGBody/CFGTerm denote lemmas), '
                        'dispatch both loop\n'
                        '         entries via {p}_src_loop_dispatch / '
                        '{p}_tgt_loop_dispatch, then\n'
                        '         apply {p}_loop_refine — which now requires '
                        'ESTABLISHING\n'
                        '         {p}_inv at the two entry-block initial states.'
                        ).format(p=p)


            if ubs:
                guidance += (
                    '\n         The %d TARGET-SPECIFIC UB obligation(s) HU1..HU%d above are'
                    '\n         proved separately, so the tgt entry block yields plain values'
                    '\n         on this path.' % (len(ubs), len(ubs)))


                if hu_pre_used:
                    if hu_src_pre_note == 'loop':
                        guidance += (
                            '\n         Each HU takes premises hs1..hs%d — the SOURCE\'s conditions on its'
                            '\n         FIRST iteration. Supply them HERE: case-split on them, and in the'
                            '\n         failing branch the src loop body poisons on iteration 1, so the'
                            '\n         src side is poison and refines anything (%s).'
                            % (len(hu_src_pre),
                               '; '.join(sp[1] for sp in hu_src_pre[:2])))
                    else:
                        guidance += (
                            '\n         Each HU takes premises hs1..hs%d — conditions the SOURCE ENTRY'
                            '\n         block itself imposes (its `llvm.assume`s and its unconditionally'
                            '\n         executed UB-sensitive ops). Supply them HERE: case-split on them,'
                            '\n         and in the failing branch the SOURCE is immediately UB at its own'
                            '\n         entry, which refines anything (%s).'
                            % (len(hu_src_pre),
                               '; '.join(sp[1] for sp in hu_src_pre[:2])))
            if ubopaque:
                guidance += (
                    '\n         CAUTION: %d tgt entry op(s) are outside the UB-obligation'
                    '\n         analysis, so any UB they carry is NOT named by an HU hole and'
                    '\n         remains this hole\'s responsibility: %s'
                    % (len(ubopaque), '; '.join(ubopaque[:3])))


        elif variant == 'exitbr':
            guidance = ('unfold both entry blocks, establish {p}_inv for the src\n'
                        '         loop-entry state, show the tgt entry '
                        'br-argument equals\n'
                        '         {p}_tgtResult V, then chain '
                        '{p}_src_loop_dispatch and\n'
                        '         {p}_loop_refine.').format(p=p)
        else:
            guidance = ('unfold the src entry block, establish {p}_inv for the '
                        'src\n'
                        '         loop-entry state, show the straight-line tgt '
                        'run equals\n'
                        '         some ({p}_tgtResult V ::ₕ HVector.nil, s), '
                        'then chain\n'
                        '         {p}_src_loop_dispatch and {p}_loop_refine '
                        '(handle any\n'
                        '         src-entry early-exit path directly).'
                        ).format(p=p)


        if pidx:


            hole_lines = ([
                '/- [HOLE %s: final assembly — %s' % (hfin, guidance),
                '   Every poison-input case%s already discharged, so the inputs are'
                % (' and every entry-block UB case are' if eubs else ' is'),
                '   genuine values here and no UB construct fires on this path.] -/',
                'sorry'])
            ind0 = 6 + 4 * len(pidx)
            lines = [' ' * (ind0 + 2 * len(eubs)) + l for l in hole_lines]
            for k in range(len(eubs) - 1, -1, -1):
                tag, guard, _why, _raw = eubs[k]
                gn, pad = k + 1, ' ' * (ind0 + 2 * k)
                lines = ([pad + 'by_cases hg%d : %s' % (gn, guard),
                          pad + '. rw [%s_src_ub_of_%s%d V (fuel + 1) s %s%s%s hg%d]'
                          % (p, tag, gn,
                             ' '.join("av%d'" % (q + 1) for q in pidx),
                             ''.join(' (by exact hA%d)' % q for q in pidx),
                             ''.join(' hg%d' % m for m in range(1, gn)), gn),
                          pad + '  exact ImmediateUBOr.IsRefinedBy.immediateUBLeft',
                          pad + '. ' + lines[0].strip()] + lines[1:])
            if eubs:
                pins = [' ' * ind0 + '-- pin each value at the LITERAL width: `cases` types',
                        ' ' * ind0 + '-- them `BitVec (LLVM.Ty.width ity)`, which the guards',
                        ' ' * ind0 + '-- below cannot elaborate against.  `let`, not `have`:',
                        ' ' * ind0 + '-- the definitional link is what keeps `hA` usable.']
                for k in pidx:
                    pins.append(' ' * ind0 + "let av%d' : BitVec %s := av%d"
                                % (k + 1, W, k + 1))
                lines = pins + lines
            for lvl in range(len(pidx) - 1, -1, -1):
                k = pidx[lvl]
                pad = ' ' * (6 + 4 * lvl)
                lines = ([pad + 'cases hA%d : V (%s) with'
                          % (k, _arg_var(k, npar, p, ity)),
                          pad + '| poison =>',
                          pad + '    -- AUTO-DISCHARGED by %s_src_ub_of_poison_input%d:'
                          % (p, k),
                          pad + '    -- this input reaches a branch condition, so the',
                          pad + '    -- source is immediate UB here.',
                          pad + '    rw [%s_src_ub_of_poison_input%d V (fuel + 1) s hA%d]'
                          % (p, k, k),
                          pad + '    exact ImmediateUBOr.IsRefinedBy.immediateUBLeft',
                          pad + '| value av%d =>' % (k + 1)] + lines)
            succ_body = '\n'.join(lines)
        else:
            succ_body = ('''      /- [HOLE {hfin}: final assembly — {guidance}] -/
      sorry''').format(hfin=hfin, guidance=guidance)

        if variant == 'straight':


            parts.append('''/- [IR-DERIVED: the tgt side is a straight-line PURE Com, so bare `⊑` would
   resolve to the CFG-opaque collapse relation (vacuous for the CFG src).  The theorem
   below therefore states the fuel/memory-aware refinement EXPLICITLY, with
   the pure tgt cast into `.impure` (cast preserves the denotation).] -/
theorem {p}_correct :
    IsRefinedByOnIntWInputsWithMemory {p}_src ({p}_tgt.castPureToEff .impure) := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
{succ}
'''.format(p=p, hfin=hfin, guidance=guidance, succ=succ_body))
        else:
            parts.append('''theorem {p}_correct : {p}_src ⊑ {p}_tgt := by
  intro V s fuel
  cases fuel with
  | zero =>
      exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
  | succ fuel =>
{succ}
'''.format(p=p, succ=succ_body))

        hole_lines = '\n'.join('    %-6s %s' % (h, d) for h, d in holes)


        if value_emitted:
            hole_lines = ('    %-6s %s\n' % ('H1', '(tgt result value) — EMITTED by the '
                                             'printer, NOT a hole')) + hole_lines
        header = '''/-
  Row C1W ({ver}) multi-hole fuel-induction scaffold, variant `{variant}`,
  emitted deterministically from the src/tgt IR text alone.

  IMPORT PINNING (soundness-critical): the 3-import header below INCLUDES
  SSA.Projects.InstCombine.MemoryRefinement; the meaning of ⊑ depends on
  this import.  Under these pinned imports the theorem below is the fuel/memory-aware
  refinement, not the CFG-opaque collapse.

  Holes (exactly {n} sorries):
{hole_lines}
-/
import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

set_option maxHeartbeats 0
set_option linter.unusedVariables falseASMLINTMARK

namespace_open

def_src

def_tgt

'''.format(ver=C1W_VERSION, variant=variant, n=len(holes),
               hole_lines=hole_lines)

        body = header + '\n'.join(parts) + '\nnamespace_close\n'


        body = body.replace('ASMLINTMARK',
                            '\nset_option linter.unusedTactic false' if _has_asm else '')
        body = body.replace('namespace_open', _ns_open(ns))
        body = body.replace('namespace_close', _ns_close(ns))
        body = body.replace('def_src', src['verbatim'])
        body = body.replace('def_tgt', tgt['verbatim'])
        if wsym:
            body = _symbolize(body, base, (src['verbatim'], tgt['verbatim']))
        return {
            'status': 'ok',
            'reason': ('Row C1W (%s, variant %s) multi-hole fuel-induction '
                       'skeleton: %d typed holes; 3-import header incl. '
                       'MemoryRefinement PINNED%s'
                       % (C1W_VERSION, variant, len(holes),
                          (' (symbolic width %r)' % wsym) if wsym else '')),
            'shape': 'C1W',
            'expected_sorries': len(holes),
            'files': {case + '.lean': body},
        }


    def _shapec_applicable(case, parsed, base, src, tgt):
        sf, tf = src['func'], tgt['func']


        if any('MemoryRefinement' in i for i in parsed['imports']):
            return False, ('ShapeC(a): input imports MemoryRefinement '
                           '(fuel-aware ⊑; collapse does not typecheck)')

        if src['width_params'] or tgt['width_params']:
            return False, 'ShapeC(f): width-generic [llvm(w)| input'


        if not (_is_multiblock(sf) and _is_multiblock(tf)):
            return False, ('ShapeC(b): mixed shape, one side is straight-line '
                           '(known closer failure class) '
                           '-> route to C1-or-decline')

        if [t for _, t in sf['blocks'][0]['args']] != \
                [t for _, t in tf['blocks'][0]['args']]:
            return False, 'ShapeC(c): src/tgt entry-arg type lists differ'

        if sf['ret'] != tf['ret']:
            return False, 'ShapeC(d): return types differ'
        if sf['ret'] not in [t for _, t in sf['blocks'][0]['args']]:
            return False, ('ShapeC(d): no entry argument of the return type '
                           '(fallback construction fails)')

        return True, ''


    def _shapec_emit(case, parsed, base, src, tgt):
        ns = parsed['ns']
        imports = '\n'.join(parsed['imports'])
        import_hash = hashlib.sha256(
            ('\n'.join(parsed['imports'])).encode()).hexdigest()
        S = base + '_src'
        Tg = base + '_tgt'
        cert = '''
        /--/

-- [IR-DERIVED: import block copied verbatim from the input file; applicability
--  check (a) verified syntactically that MemoryRefinement is NOT imported]
{imports}

{nsopen}

-- [IR-DERIVED: src/tgt definitions copied VERBATIM from the input file]
{src_def}

{tgt_def}

-- [IR-DERIVED: the ENTIRE proof below is a FIXED TEXT BLOCK, byte-identical
--  for every case in the family — nothing in it is case-specific except the
--  two definition names.  Zero holes.  That the closing sequence is not a
--  function of the CFG at all is precisely why this is a signature-only
--  certificate: Com.denote discards all CFG blocks.]
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem {base}_correct :
    {S} ⊑ {Tg} := by
  intro V
  first
  | -- variant A (pure-value collapse)
    (simp [{S}, {Tg}, Com.denote]
     exact ImmediateUBOr.IsRefinedBy.bothValues
       ⟨ImmediateUBOr.IsRefinedBy.bothValues (LLVM.SemVal.isRefinedBy_self _),
         HVector.nil_isRefinedBy_nil⟩)
  | -- variant B (IntW.isRefinedBy_iff route)
    (simp [{S}, {Tg}, Com.denote]
     apply ImmediateUBOr.IsRefinedBy.bothValues
     rw [HVector.cons_isRefinedBy_cons]
     constructor
     · apply ImmediateUBOr.IsRefinedBy.bothValues
       rw [LLVM.IntW.isRefinedBy_iff]
       exact LLVM.SemVal.isRefinedBy_self _
     · exact HVector.nil_isRefinedBy_nil)
  | -- variant C (defeq collapse; also the family test: `change` succeeds iff
    -- tgt.denote is DEFINITIONALLY src.denote)
    (change {S}.denote V.lift ⊑ {S}.denote V.lift
     cases {S}.denote V.lift with
     | none => exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
     | some v =>
         apply ImmediateUBOr.IsRefinedBy.bothValues
         cases v with
         | cons x xs =>
             cases xs with
             | nil =>
                 simp only [HVector.cons_isRefinedBy_cons,
                   HVector.nil_isRefinedBy_nil, and_true]
                 cases x with
                 | none => exact ImmediateUBOr.IsRefinedBy.immediateUBLeft
                 | some sv =>
                     apply ImmediateUBOr.IsRefinedBy.bothValues
                     exact LLVM.SemVal.isRefinedBy_self sv)

-- [IR-DERIVED: MANDATORY vacuity witness, emitted unconditionally with every
--  Shape-C certificate.  A kernel-checked rfl-proof that under the semantics
--  used by the certificate above, tgt.denote is definitionally src.denote:
--  the certificate cannot distinguish tgt from ANY same-signature program.
--  If this probe fails to compile, the case must NOT be classified as
--  cfg-structural (the compile gate enforces this).]
theorem {base}_audit_fallback_collapse :
    ∀ V, {Tg}.denote (InputValuation.lift V)
       = {S}.denote (InputValuation.lift V) :=
  fun _ => rfl

-- [IR-DERIVED: pointer to the paired open fuel obligation.  It CANNOT be
--  stated in this file: denoteWithMemoryFuel requires importing
--  MemoryRefinement, whose scoped HRefinement instances would silently CHANGE
--  the meaning of the ⊑ proved above.  See {case}_fuel_obligation.lean.
--  Until that sorry is filled, this certificate stays in the signature-only
--  bucket.]

{nsclose}
'''.format(base=base, case=case, S=S, Tg=Tg, imports=imports,
               nsopen=_ns_open(ns), nsclose=_ns_close(ns),
               src_def=src['verbatim'], tgt_def=tgt['verbatim'],
               ver=EMITTER_VERSION)

        fuel = '''/-
AUDIT[cfg-fuel-obligation]
  companion of: {case}.lean
  This file states the NON-vacuous obligation: fuel-bounded, loop-executing
  refinement via LLVMMemory denoteWithMemoryFuel semantics.  It is emitted
  with exactly one typed hole (`sorry`).  Only when this theorem is sorry-free
  may the case leave the signature-only reporting bucket.
  NOTE: this file deliberately imports MemoryRefinement, so inside the input's
  namespaces the scoped ⊑ instances are active; the obligation is therefore
  stated by its explicit name `IsRefinedByOnIntWInputsWithMemory`, never via
  the ambiguous ⊑ notation.
-/

import SSA.Projects.InstCombine.Refinement
import SSA.Projects.InstCombine.MemoryRefinement
import LeanMLIR.Dialects.LLVM.Syntax

{nsopen}

-- [IR-DERIVED: src/tgt copied verbatim from input, same as certificate file]
{src_def}

{tgt_def}

-- [HOLE: the genuinely-creative part.  Proving this requires reasoning about
--  the loop bodies under fuel semantics — exactly what the fixed Shape-C
--  closer does NOT establish.  A semantically divergent tgt must make THIS
--  statement unprovable; it is the discriminating obligation.]
theorem {base}_fuel_correct :
    IsRefinedByOnIntWInputsWithMemory
      {S} {Tg} := by
  sorry

{nsclose}
'''.format(base=base, case=case, S=S, Tg=Tg, nsopen=_ns_open(ns),
               nsclose=_ns_close(ns), src_def=src['verbatim'],
               tgt_def=tgt['verbatim'])

        audit = {
            'vacuous': True,
            'reason': 'fallback-collapse; loop semantics NOT compared',
            'certified': ('plain-Refinement ⊑ between the elaborated Com '
                          'terms; for multi-block CFGs Com.denote collapses to a '
                          'signature-determined fallback (Basic.lean:530), so the '
                          'proved relation is definitionally reflexive '
                          '(kernel-checked rfl witness %s_audit_fallback_collapse '
                          'in %s.lean)' % (base, case)),
            'not_certified': ('any execution of loop bodies, trip counts, or '
                              'observable behaviour; the fuel-bounded obligation '
                              '%s_fuel_correct in %s_fuel_obligation.lean remains '
                              'an open sorry' % (base, case)),
            'case': case,
            'certificate_class': 'fallback-collapse',
            'semantics': 'Com.denote',
            'loop_semantics_compared': False,
            'defeq_probe': ('in-file rfl theorem %s_audit_fallback_collapse; '
                            'compile-gated' % base),
            'emitter_version': EMITTER_VERSION,
            'closer_variant': 'first|A|B|C',
            'input_import_block_sha256': import_hash,
            'applicability_checks': {
                'no_memoryrefinement_import': True,
                'both_sides_multiblock': True,
                'entry_arg_types_identical': True,
                'single_return_type_present_in_entry_args': True,
                'all_labels_defined_terminators_last': True,
                'concrete_width_only': True,
            },
            'reporting_bucket': 'signature-only',
            'headline_countable': False,
            'fuel_obligation': {
                'file': case + '_fuel_obligation.lean',
                'theorem': base + '_fuel_correct',
                'status': 'open (sorry)',
            },
        }

        files = {
            case + '.lean': cert,
            case + '_fuel_obligation.lean': fuel,
            case + '_audit.json': json.dumps(audit, indent=2) + '\n',
        }
        result = {
            'status': 'ok',
            'reason': ('Shape-C fallback-collapse SIGNATURE-ONLY certificate '
                       '(vacuous w.r.t. loop semantics; see audit JSON); paired '
                       '1-sorry fuel obligation is the real open goal'),
            'shape': 'C',
            'expected_sorries': 1,
            'files': files,
        }
        return _finalize_shapec(case, result)


    def _finalize_shapec(case, result):
        try:
            required = {case + '.lean', case + '_fuel_obligation.lean',
                        case + '_audit.json'}
            if set(result['files']) != required:
                raise ValueError('Shape-C file set violation: %s'
                                 % sorted(result['files']))
            audit = json.loads(result['files'][case + '_audit.json'])
            if audit.get('vacuous') is not True:
                raise ValueError('Shape-C audit must declare vacuous:true')
            for k in ('reason', 'certified', 'not_certified'):
                if not audit.get(k):
                    raise ValueError('Shape-C audit missing key %r' % k)
            if 'sorry' not in result['files'][case + '_fuel_obligation.lean']:
                raise ValueError('Shape-C fuel obligation must contain the sorry')
            return result
        except Exception as e:
            return _decline('ShapeC-structural-enforcement: %s' % e)


    def _decline(reason):
        return {'status': 'decline', 'reason': reason, 'shape': '',
                'expected_sorries': 0, 'files': {}}


    def emit(text: str, case: str) -> dict:
        _DIV_OR_GUARDS.clear()

        try:
            if not detect(text):
                return _decline('not a CFG-family input (no multi-block src/tgt '
                                'pair)')
            parsed = parse_input(text)
            base, src, tgt = _find_pair(parsed)

            reasons = []
            ok, why = _c0_applicable(base, src, tgt)
            if ok:
                return _c0_emit(case, parsed, base, src, tgt)
            reasons.append(why)


            ok, why, info = _c1w_applicable(parsed, base, src, tgt)
            if ok:
                return _c1w_emit(case, parsed, base, src, tgt, info)
            reasons.append(why)

            ok, why = _shapec_applicable(case, parsed, base, src, tgt)
            if ok:
                return _shapec_emit(case, parsed, base, src, tgt)
            reasons.append(why)


            norm = _normalize_cfg_text(text)
            if norm != text:
                try:
                    nparsed = parse_input(norm)
                    nbase, nsrc, ntgt = _find_pair(nparsed)
                    ok, _why = _c0_applicable(nbase, nsrc, ntgt)
                    if ok:
                        r = _c0_emit(case, nparsed, nbase, nsrc, ntgt)
                        r['reason'] = (r.get('reason', '')
                                       + ' [normalized-quotient recovery]')
                        return r

                    ok, _why, info = _c1w_applicable(nparsed, nbase, nsrc, ntgt)
                    if ok:
                        r = _c1w_emit(case, nparsed, nbase, nsrc, ntgt, info)
                        r['reason'] = (r.get('reason', '')
                                       + ' [normalized-quotient recovery]')
                        return r
                except Exception:
                    pass

            return _decline('; '.join(reasons))
        except Exception as e:
            r = _decline('exception: %s: %s' % (type(e).__name__, e))
            r['fence_line'] = getattr(e, 'fence_line', None)
            return r

    return types.SimpleNamespace(FAMILY=FAMILY, detect=detect, emit=emit)


def _build_shape_cex():

    FAMILY = 'CEX'


    BIN_UB = {"udiv", "sdiv", "urem", "srem"}


    DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*((?:\([^)]*\)\s*)+):=\s*'
        r'\[llvm\(([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)\)\|\s*\{(.*?)\}\s*\]', re.S)

    FW_DEF_RE = re.compile(
        r'def\s+([A-Za-z_]\w*)\s*:=\s*'
        r'\[llvm\(\)\|\s*\{(.*?)\}\s*\]', re.S)

    BLOCK_HDR_RE = re.compile(r'\^\w+\([^)]*\):')
    EXTRA_TOKEN_RE = re.compile(r'[A-Za-z_]\w*|\d+|≤|≥|≠|<=|>=|[<>=+\-*^/%()]|\s+')

    def wv_list(wv):
        if wv is None:
            return None
        if isinstance(wv, str):
            return [wv]
        return list(wv)

    def parse_type(t, wv='w'):
        t = t.strip()
        wvs = wv_list(wv)
        if wvs is None:
            m = re.fullmatch(r'i(\d+)', t)
            if m and int(m.group(1)) > 0: return m.group(1)
            raise Unsupported(f"type {t!r} (fixed-width dialect requires literal iK)")
        if t == '_':

            if len(wvs) != 1:
                raise Unsupported(f"type '_' is ambiguous with {len(wvs)} width params {wvs}")
            return wvs[0]
        if t == 'i1':     return '1'
        m = re.fullmatch(r'i(\d+)', t)
        if m:             return m.group(1)
        if t in wvs:      return t
        raise Unsupported(f"type {t!r}")

    def ty(width):
        return f"InstCombine.LLVM.Ty.bitvec {width}"

    def check_extra_binder(g, wv):
        return check_extra_binder_shared(g, tuple(wv_list(wv) or ()))

    def extract_defs(text):
        ms = list(DEF_RE.finditer(text))
        if len(ms) != 2:
            raise Unsupported(f"expected exactly 2 llvm defs, found {len(ms)}")
        (m_src, m_tgt) = ms
        src_name, src_binders, wv_s, src_body = m_src.groups()
        tgt_name, tgt_binders, wv_t, tgt_body = m_tgt.groups()
        if 'src' not in src_name:
            raise Unsupported(f"first def {src_name!r} has no 'src' in name")
        if re.sub('src', 'tgt', src_name) != tgt_name:
            raise Unsupported(f"def names do not pair: {src_name!r} vs {tgt_name!r}")
        norm_w = lambda s: [x.strip() for x in s.split(',')]
        wvs_s, wvs_t = norm_w(wv_s), norm_w(wv_t)
        if wvs_s != wvs_t:
            raise Unsupported(f"width symbols differ: {wv_s!r} vs {wv_t!r}")
        if len(set(wvs_s)) != len(wvs_s):
            raise Unsupported(f"duplicate width symbol in llvm({wv_s!r})")
        norm = lambda s: re.sub(r'\s+', ' ', s.strip())
        if norm(src_binders) != norm(tgt_binders):
            raise Unsupported("src/tgt binder lists differ")
        groups = re.findall(r'\([^)]*\)', src_binders)
        g0 = re.fullmatch(r'\(\s*([A-Za-z_]\w*(?:\s+[A-Za-z_]\w*)*)\s*:\s*Nat\s*\)',
                          groups[0].strip())
        if not g0:
            raise Unsupported(f"first binder {groups[0]!r} is not (WV.. : Nat)")
        wvs = g0.group(1).split()
        if wvs != wvs_s:
            raise Unsupported(f"binder widths {wvs!r} != llvm({wv_s!r})")
        extras = [g.strip() for g in groups[1:]]
        extra_names = [check_extra_binder(g, wvs) for g in extras]
        return (src_name, tgt_name, wvs, extra_names, " ".join(extras),
                src_body, tgt_body, m_src.group(0), m_tgt.group(0))

    def extract_defs_fw(text):
        ms = list(FW_DEF_RE.finditer(text))
        if len(ms) != 2:
            raise Unsupported(f"expected exactly 2 binder-less [llvm()| defs, found {len(ms)}")
        (m_src, m_tgt) = ms
        src_name, src_body = m_src.groups()
        tgt_name, tgt_body = m_tgt.groups()
        if 'src' not in src_name:
            raise Unsupported(f"first def {src_name!r} has no 'src' in name")
        if re.sub('src', 'tgt', src_name) != tgt_name:
            raise Unsupported(f"def names do not pair: {src_name!r} vs {tgt_name!r}")
        return (src_name, tgt_name, src_body, tgt_body, m_src.group(0), m_tgt.group(0))


    def n_blocks(body):
        return len(BLOCK_HDR_RE.findall(body))


    def cex_sig(body, wv, multiblock_ok=False):
        if n_blocks(body) > 1 and not multiblock_ok:
            raise Unsupported("multi-block body (CFG) is not a straight-line signature")
        m = re.search(r'llvm\.func\s+@(\S+)\(([^)]*)\)\s*->\s*(\S+)\s*\{', body)
        if m:
            name, arglist, ret = m.group(1), m.group(2), m.group(3)
        else:
            hm = re.search(r'\^\w+\(([^)]*)\)\s*:', body)
            if not hm:
                raise Unsupported("no llvm.func header nor ^bb0 block")
            arglist = hm.group(1)
            rm = re.search(r'llvm\.return\s+%\S+?\s*:\s*(\S+)\s*$', body.strip(), re.M)
            if not rm:
                raise Unsupported("bare-bb0 form: no typed llvm.return to read the result type")
            ret, name = rm.group(1), None
        args = []
        for a in arglist.split(','):
            a = a.strip()
            if not a: continue
            am = re.fullmatch(r'%(\S+)\s*:\s*(\S+)', a)
            if not am: raise Unsupported(f"arg {a!r}")
            args.append((am.group(1), parse_type(am.group(2), wv)))
        if not args:
            raise Unsupported("zero args (nothing to build a valuation over)")
        return name, args, ret

    def has_assume(body):
        return bool(re.search(r'\bllvm\.assume\b', body))


    def load_witness(path):
        with open(path, encoding='utf-8') as f:
            return json.load(f)

    def canonical_json(obj):
        return json.dumps(obj, sort_keys=True, separators=(',', ':'))

    def candidate_id(input_sha256, witness):
        return hashlib.sha256((input_sha256 + canonical_json(witness)).encode('utf-8')).hexdigest()

    def witness_widths(witness, wvs):
        wvs = wv_list(wvs) or []
        ws, w1 = witness.get('widths'), witness.get('width')
        if ws is None and w1 is None:
            raise Unsupported("symbolic dialect requires witness.width"
                              + (f" (or witness.widths for the {len(wvs)} width params "
                                 f"{wvs})" if len(wvs) != 1 else ""))
        if ws is None:
            if len(wvs) != 1:
                raise Unsupported(f"{len(wvs)} width params {wvs} require witness.widths "
                                  f"(list or object); scalar witness.width is phi=1 only")
            out = {wvs[0]: w1}
        elif isinstance(ws, dict):
            missing = [s for s in wvs if s not in ws]
            if missing:
                raise Unsupported(f"witness.widths is missing width symbol(s) {missing}")
            unknown = [k for k in ws if k not in wvs]
            if unknown:
                raise Unsupported(f"witness.widths has unknown width symbol(s) {unknown} "
                                  f"(declared: {wvs})")
            out = {s: ws[s] for s in wvs}
        elif isinstance(ws, list):
            if len(ws) != len(wvs):
                raise Unsupported(f"witness.widths has {len(ws)} entries != {len(wvs)} "
                                  f"width params {wvs}")
            out = dict(zip(wvs, ws))
        else:
            raise Unsupported(f"witness.widths must be a list or an object, got "
                              f"{type(ws).__name__}")
        if w1 is not None and ws is not None:
            if len(wvs) != 1 or out[wvs[0]] != w1:
                raise Unsupported(f"witness.width {w1!r} disagrees with witness.widths "
                                  f"{ws!r} — stale/ambiguous witness")
        for s, v in out.items():
            if not isinstance(v, int) or isinstance(v, bool) or v <= 0:
                raise Unsupported(f"witness width for {s!r} must be a positive int, got {v!r}")
        return out


    def width_map(wvs, W):
        wvs = wv_list(wvs)
        if W is None or wvs is None:
            return {}
        if isinstance(W, dict):
            return {k: str(v) for k, v in W.items()}
        if isinstance(W, (list, tuple)):
            return {n: str(v) for n, v in zip(wvs, W)}
        return {wvs[0]: str(W)}

    def concretize(width_expr, wv, W):
        if W is None:
            return width_expr
        return width_map(wv, W).get(width_expr, width_expr)

    def subst_widths(expr, wmap):
        if not wmap:
            return expr
        pat = re.compile(r'\b(' + '|'.join(re.escape(k) for k in sorted(wmap, key=len, reverse=True)) + r')\b')
        return pat.sub(lambda m: wmap[m.group(1)], expr)


    def eff_monad(impure):
        e = 'impure' if impure else 'pure'
        return f"EffectKind.{e}.toMonad InstCombine.LLVM.m"


    def ret_type(impure, retw):
        return f"{eff_monad(impure)}\n    (HVector TyDenote.toType [{ty(retw)}])"

    def ret_value(outcome, impure, retw):
        k = outcome['kind']
        if k == 'ub':
            if not impure:
                raise Unsupported("outcome 'ub' on a pure side (no llvm.assume)")
            return "ImmediateUBOr.immediateUB"
        if k == 'value':
            n = outcome['nat']
            elt = f"LLVM.IntWUB.value ({n}#{retw})"
        elif k == 'poison':
            elt = "LLVM.IntWUB.poison"
        else:
            raise Unsupported(f"unknown outcome kind {k!r}")
        if impure:
            return (f"ImmediateUBOr.value (HVector.cons ({elt}) HVector.nil)")

        return (f"HVector.cons\n"
                f"    (show TyDenote.toType ({ty(retw)}) from\n"
                f"      {elt})\n"
                f"    (HVector.nil : HVector TyDenote.toType ([] : List InstCombine.LLVM.Ty))")

    def plumbing(name):
        return f"""def {name}_valueOfNat (w n : Nat) : LLVM.IntW w := LLVM.SemVal.value (BitVec.ofNat w n)

def {name}_ivCons {{Γ : Ctxt InstCombine.LLVM.Ty}} {{t : InstCombine.LLVM.Ty}}
    (x : LLVM.IntW (InstCombine.LLVM.Ty.width t)) (V : InstCombine.InputValuation Γ) :
    InstCombine.InputValuation (Γ.cons t) := by
  intro t' v
  revert x V
  refine Ctxt.Var.casesOn v ?_ ?_
  · intro _ _ _ v _ V
    exact V v
  · intro _ _ x _
    exact x

def {name}_ivOfHVector {{types : List InstCombine.LLVM.Ty}} :
    HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types →
      InstCombine.InputValuation (Ctxt.ofList types)
  | .nil => fun _ v => v.emptyElim
  | .cons x xs => {name}_ivCons x ({name}_ivOfHVector xs)

@[simp] theorem {name}_ivOfHVector_apply {{types : List InstCombine.LLVM.Ty}}
    (xs : HVector (fun t => LLVM.IntW (InstCombine.LLVM.Ty.width t)) types)
    (v : Ctxt.Var (Ctxt.ofList types) t) :
    {name}_ivOfHVector xs v = xs[v] := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
      cases v using Ctxt.Var.casesOn with
      | toCons v =>
          simpa [{name}_ivOfHVector, {name}_ivCons, ih] using
            (HVector.cons_getElem_toCons xs x v).symm
      | last =>
          simpa [{name}_ivOfHVector, {name}_ivCons, ih] using
            (HVector.cons_getElem_last xs x).symm"""

    def decidable_instances(name, retw, need_pure, need_impure):
        L = [f"""local instance {name}_decidableEqTyDenote :
    ∀ t : InstCombine.LLVM.Ty, DecidableEq (TyDenote.toType t) := by
  intro t
  cases t with
  | bitvec w =>
      cases w with
      | concrete n =>
          change DecidableEq (LLVM.IntWUB n)
          infer_instance
      | mvar idx => exact idx.elim0
  | _ =>
      change DecidableEq InstCombine.LLVMMemory.PtrValUB
      infer_instance

local instance {name}_decidableEqReturn :
    DecidableEq (HVector TyDenote.toType [{ty(retw)}]) := by
  infer_instance"""]
        if need_pure:
            L.append(f"""local instance {name}_decidableEqPureReturn :
    DecidableEq (EffectKind.pure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [{ty(retw)}])) := by
  change DecidableEq (HVector TyDenote.toType [{ty(retw)}])
  infer_instance""")
        if need_impure:
            L.append(f"""local instance {name}_decidableEqImpureReturn :
    DecidableEq (EffectKind.impure.toMonad InstCombine.LLVM.m
      (HVector TyDenote.toType [{ty(retw)}])) := by
  change DecidableEq (ImmediateUBOr (HVector TyDenote.toType [{ty(retw)}]))
  infer_instance""")
        return "\n\n".join(L)

    def refinement_decidables(name, retw, src_impure, tgt_impure, cfg=False):
        hv = f"HVector TyDenote.toType [{ty(retw)}]"


        a_arg = "a" if src_impure else "(ImmediateUBOr.value a)"
        b_arg = "b" if tgt_impure else "(ImmediateUBOr.value b)"
        levels = f"""local instance {name}_decRefSemVal (a b : LLVM.SemVal (BitVec {retw})) :
    Decidable (a ⊑ b) :=
  match a, b with
  | .poison, _ => isTrue (LLVM.SemVal.poison_isRefinedBy _)
  | .value _, .poison => isFalse (by rintro ⟨⟩)
  | .value x, .value y => decidable_of_iff (x = y) (by simp)

local instance {name}_decRefIntW (a b : LLVM.IntW {retw}) : Decidable (a ⊑ b) :=
  decidable_of_iff
    (@HRefinement.IsRefinedBy (LLVM.SemVal (BitVec {retw})) (LLVM.SemVal (BitVec {retw})) _ a b)
    (LLVM.IntW.isRefinedBy_iff a b).symm

local instance {name}_decRefElt (a b : TyDenote.toType ({ty(retw)})) : Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr (LLVM.IntW {retw})) (ImmediateUBOr (LLVM.IntW {retw}))
        inferInstance a b) := inferInstance
  exact d

local instance {name}_decRefRet (a b : {hv}) : Decidable (a ⊑ b) :=
  match a, b with
  | .cons x .nil, .cons y .nil => decidable_of_iff (x ⊑ y ∧ True) Iff.rfl"""
        if cfg:


            return levels
        return levels + f"""

local instance {name}_decRefDenote
    (a : {eff_monad(src_impure)}
      ({hv}))
    (b : {eff_monad(tgt_impure)}
      ({hv})) :
    Decidable (a ⊑ b) := by
  have d : Decidable
      (@HRefinement.IsRefinedBy (ImmediateUBOr ({hv})) (ImmediateUBOr ({hv}))
        inferInstance {a_arg} {b_arg}) := inferInstance
  exact d"""

    def cex_inputs(name, cons):
        ctxlist = ", ".join(ty(w) for (w, _) in cons)
        entries = []
        for (w, val) in cons:
            if val[0] == 'value':
                entries.append(f"{name}_valueOfNat {w} {val[1]}")
            else:
                entries.append(f"(LLVM.SemVal.poison : LLVM.IntW {w})")
        chain = ".nil"
        for e in reversed(entries):
            chain = f"(.cons ({e}) {chain})"
        return (f"def {name}_cexInputs : InstCombine.InputValuation\n"
                f"    (Ctxt.ofList [{ctxlist}]) :=\n"
                f"  {name}_ivOfHVector\n    {chain}")


    CEX_CFG_MAX_FUEL = 1024


    CEX_CFG_HEARTBEATS = 40000000


    def cfg_impure_abbrev(name, side, app, ctxlist, retw):
        return (f"abbrev {name}_{side}_impure :\n"
                f"    Com InstCombine.LLVM (Ctxt.ofList [{ctxlist}]) .impure\n"
                f"      [{ty(retw)}] :=\n"
                f"  {app}.castPureToEff .impure")

    def cfg_terminates(name, side, ref, tac='decide +kernel'):
        return (f"theorem {name}_{side}_terminates_at_cexFuel :\n"
                f"    (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel {name}_cexFuel {ref}\n"
                f"      (V := InstCombine.InputValuation.lift {name}_cexInputs)\n"
                f"      {name}_cexState).isSome = true := by\n"
                f"  {tac}")

    def cfg_sep_machinery(name, retw):
        hv = f"HVector TyDenote.toType [{ty(retw)}]"
        res = f"ImmediateUBOr ({hv}\n              × InstCombine.LLVMMemory.State)"
        return f"""def {name}_sepBool (A B : {res}) : Bool :=
  match A, B with
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a.1 ⊑ b.1)

theorem {name}_refute_of_sepBool (A B : {res})
    (h : {name}_sepBool A B = false) : ¬ (A ⊑ B) := by
  intro hab
  cases hab with
  | immediateUBLeft => simp [{name}_sepBool] at h
  | bothValues hp =>
      simp only [{name}_sepBool, decide_eq_false_iff_not] at h
      exact h hp.1"""

    def cfg_denote_of(name, ref):
        return (f"InstCombine.LLVMMemory.Com.denoteWithMemoryFuel {name}_cexFuel {ref}\n"
                f"          (V := InstCombine.InputValuation.lift {name}_cexInputs) "
                f"{name}_cexState")

    def cfg_emit(text, case, witness, src_name, tgt_name, src_full, tgt_full,
                 src_body, tgt_body, cons, retw, shape, cex_fuel,
                 ns_blocks, nt_blocks, hole, src_app=None, tgt_app=None, sym=None,
                 eval_tac='decide +kernel'):
        ctxlist = ", ".join(ty(w) for (w, _) in cons)


        src_app = src_app or src_name
        tgt_app = tgt_app or tgt_name
        src_term = src_app if sym is None else f"({src_app})"
        tgt_term = tgt_app if sym is None else f"({tgt_app})"

        src_ref = src_term if ns_blocks > 1 else f"{case}_src_impure"
        tgt_ref = tgt_term if nt_blocks > 1 else f"{case}_tgt_impure"

        L = []


        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import SSA.Projects.InstCombine.MemoryRefinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax")
        L.append("")
        L.append("open scoped InstCombine")
        L.append("open BitVec")
        L.append("")
        L.append("-- ===== GIVEN (input): the two programs (verbatim) =====")
        L.append(src_full.strip())
        L.append("")
        L.append(tgt_full.strip())
        L.append("")
        L.append(f"-- ===== AUTO-EMITTED CEX-CFG SCAFFOLD ({shape}; witness FROZEN "
                 f"(inputs + fuel); 0 LLM) =====")
        L.append(f"section {case}_cex")
        L.append("")
        L.append("set_option maxRecDepth 8000")
        L.append(f"set_option maxHeartbeats {CEX_CFG_HEARTBEATS}")
        L.append("")
        L.append(plumbing(case))
        L.append("")
        L.append("-- Stage 1: COMPARISON RULES.  Four levels; the")
        L.append("-- memory State is never compared (no DecidableEq for it exists).")
        L.append(refinement_decidables(case, retw, True, True, cfg=True))
        L.append("")
        L.append("-- FROZEN WITNESS: cons chain = reverse of surface-order args;")
        L.append("-- plus the initial memory state and the fuel.  Immutable.")
        L.append(cex_inputs(case, cons))
        L.append("")
        L.append(f"def {case}_cexState : InstCombine.LLVMMemory.State := default")
        L.append("")
        L.append(f"def {case}_cexFuel : Nat := {cex_fuel}")
        if ns_blocks <= 1 or nt_blocks <= 1:
            L.append("")
            L.append("-- [IR-DERIVED] a straight-line side elaborates to EffectKind.pure, but the")
            L.append("-- memory relation is impure x impure, so the pure side is cast")
            L.append("-- (Com.castPureToEff preserves the denotation).")
        if ns_blocks <= 1:
            L.append(cfg_impure_abbrev(case, 'src', src_term, ctxlist, retw))
        if nt_blocks <= 1:
            L.append(cfg_impure_abbrev(case, 'tgt', tgt_term, ctxlist, retw))
        L.append("")
        L.append("-- FUEL GUARDS (soundness-critical): fuel counts BLOCK JUMPS, so a side")
        L.append("-- that has not terminated denotes `immediateUB`.  A target that merely")
        L.append("-- needs one more jump than the source would then be `separated` from it")
        L.append("-- even when the two programs agree — a two-block and a three-block")
        L.append("-- IDENTITY function are refuted that way.  These two lemmas make the")
        L.append("-- certificate fail to compile unless BOTH sides have finished at the")
        L.append("-- witnessed fuel; then the outcomes are final and the separation below")
        L.append("-- is a genuine difference between the programs, not fuel starvation.")
        L.append(cfg_terminates(case, 'src', src_ref, eval_tac))
        L.append("")
        L.append(cfg_terminates(case, 'tgt', tgt_ref, eval_tac))
        L.append("")
        L.append("-- Stage 2: VERIFY THE CEX.  Assume the refinement at")
        L.append("-- the frozen (inputs, state, fuel) triple and derive False.  The kernel")
        L.append(f"-- evaluates both programs itself (`{eval_tac}`); the bridge below is")
        L.append("-- what keeps the memory State out of the comparison.")
        L.append(cfg_sep_machinery(case, retw))
        L.append("")
        L.append(f"theorem {case}_pointwise_cex :")
        L.append(f"    ¬ ({cfg_denote_of(case, src_ref)} ⊑")
        if hole:
            L.append(f"       {cfg_denote_of(case, tgt_ref)}) := by")
            L.append("  sorry")
            expected_sorries = 1
        else:
            L.append(f"       {cfg_denote_of(case, tgt_ref)}) :=")
            L.append(f"  {case}_refute_of_sepBool _ _ (by {eval_tac})")
            expected_sorries = 0
        L.append("")
        L.append(f"theorem {case}_correct_counterexample_witness :")
        L.append(f"    ¬ (InstCombine.IsRefinedByOnIntWInputsWithMemory {src_ref} {tgt_ref}) :=")
        L.append(f"  fun h => {case}_pointwise_cex "
                 f"(h {case}_cexInputs {case}_cexState {case}_cexFuel)")
        L.append("")
        L.append("-- RELATION AUDIT: the kernel states which relation `⊑` resolved to here.")
        L.append("-- `rfl` fails if the header ever stops pinning MemoryRefinement, or if a")
        L.append("-- higher-priority HRefinement instance takes over.")
        L.append(f"theorem {case}_audit_relation_is_memory :")
        L.append(f"    ({src_ref} ⊑ {tgt_ref})")
        L.append(f"      = InstCombine.IsRefinedByOnIntWInputsWithMemory {src_ref} {tgt_ref} := rfl")
        L.append("")
        L.append(f"theorem {case}_correct_counterexample_bare : ¬ ({src_ref} ⊑ {tgt_ref}) :=")
        L.append(f"  {case}_audit_relation_is_memory ▸ {case}_correct_counterexample_witness")
        L.append("")
        L.append(f"end {case}_cex")
        L.append("")
        L.append("-- Stage 3: REFUTE REFINEMENT.  The witness triple is")
        L.append("-- packaged into the existential, so the certificate names no free data.")
        fuel_thm = (f"{case}_correct_counterexample" if sym is None
                    else f"{case}_correct_counterexample_fuel")
        if sym is not None:


            wsyms = " ".join(sym['wv'])
            exists_binds = f"({wsyms} : Nat)" + (sym['extras_text'] or "")
            bnames = (" " + " ".join(sym['extra_names'])) if sym['extra_names'] else ""
            wit = "⟨" + ", ".join(sym['wmap'][x] for x in sym['wv'])
            for pf in sym['proofs']:
                wit += f", {pf}"
            wit += f", {case}_correct_counterexample_bare⟩"


            def _headline_side(nm, nblocks):
                app = f"{nm} {wsyms}{bnames}".rstrip()
                return app if nblocks > 1 else f"({app}).castPureToEff .impure"
            src_hd = _headline_side(src_name, ns_blocks)
            tgt_hd = _headline_side(tgt_name, nt_blocks)
            L.append(f"theorem {case}_correct_counterexample :")
            L.append(f"    ∃ {exists_binds}, ¬ ({src_hd} ⊑ {tgt_hd}) :=")
            L.append(f"  {wit}")
            L.append("")
            L.append("-- ..and the same refutation stated over the fuel/memory relation, at the")
            L.append("-- witnessed width.  This is the CFG lane's own existential; the width is")
            L.append("-- concrete here because the valuation and the guards are.")
        L.append(f"theorem {fuel_thm} :")
        L.append(f"    ∃ (V : InstCombine.InputValuation (Ctxt.ofList [{ctxlist}]))")
        L.append("      (s : InstCombine.LLVMMemory.State) (fuel : Nat) (_hf : 0 < fuel),")
        L.append(f"      ¬ (InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel {src_ref}")
        L.append("            (V := InstCombine.InputValuation.lift V) s ⊑")
        L.append(f"         InstCombine.LLVMMemory.Com.denoteWithMemoryFuel fuel {tgt_ref}")
        L.append("            (V := InstCombine.InputValuation.lift V) s) :=")
        L.append(f"  ⟨{case}_cexInputs, {case}_cexState, {case}_cexFuel, by decide, "
                 f"{case}_pointwise_cex⟩")

        content = "\n".join(L) + "\n"
        isha_val = witness.get('input_sha256') or hashlib.sha256(text.encode('utf-8')).hexdigest()
        cid = candidate_id(isha_val, witness)
        mainfile = f"{case}.cex.{cid[:12]}.lean"
        return {
            'status': 'ok',
            'reason': '',
            'shape': shape + '-CFG',
            'expected_sorries': expected_sorries,
            'candidate_id': cid,
            'mainfile': mainfile,
            'files': {mainfile: content},
        }

    def closer(name, tgt_kind, eval_tac):
        if tgt_kind == 'ub':
            return "  cases hyp"
        if tgt_kind == 'value':
            return (f"  cases hyp with\n"
                    f"  | bothValues h1 =>\n"
                    f"      have h2 := ((HVector.cons_isRefinedBy_cons).1 h1).1\n"
                    f"      exact absurd ((InstCombine.bv_isRefinedBy_iff _ _).1\n"
                    f"        ((LLVM.SemVal.value_isRefinedBy_value).1\n"
                    f"          ((ImmediateUBOr.value_isRefinedBy_value _ _).1 h2))) (by decide)")
        if tgt_kind == 'poison':
            return (f"  cases hyp with\n"
                    f"  | bothValues h1 =>\n"
                    f"      have h2 := ((HVector.cons_isRefinedBy_cons).1 h1).1\n"
                    f"      cases h2 with\n"
                    f"      | bothValues hSem => cases hSem")
        raise Unsupported(f"no closer for tgt outcome {tgt_kind!r}")

    def cex_closer(eval_tac):
        return f"  revert hyp\n  {eval_tac}"


    def emit_cex(text, case, witness, tier='strict', hole=False):
        if tier not in ('strict', 'native', 'auto', 'kernel'):
            raise Unsupported(f"unknown tier {tier!r}")


        eval_tac = ('native_decide' if tier == 'native'
                    else 'decide +kernel' if tier == 'kernel'
                    else 'decide')


        dialect = 'sym'
        try:
            (src_name, tgt_name, wv, extra_names, extras_text,
             src_body, tgt_body, src_full, tgt_full) = extract_defs(text)
        except Unsupported as e_sym:
            dialect = 'fw'
            try:
                (src_name, tgt_name, src_body, tgt_body, src_full, tgt_full) = extract_defs_fw(text)
                wv, extra_names, extras_text = None, [], ""
            except Unsupported:
                raise Unsupported(f"neither symbolic nor fixed dialect: {e_sym}")
        W = witness_widths(witness, wv) if dialect == 'sym' else None
        wmap = width_map(wv, W)


        ns_blocks, nt_blocks = n_blocks(src_body), n_blocks(tgt_body)
        cfg_mode = ns_blocks > 1 or nt_blocks > 1


        _sn, sargs, sret = cex_sig(src_body, wv, multiblock_ok=cfg_mode)
        _tn, targs, tret = cex_sig(tgt_body, wv, multiblock_ok=cfg_mode)
        if [w for _, w in sargs] != [w for _, w in targs]:
            raise Unsupported("src/tgt arg widths differ")
        if sret != tret:
            raise Unsupported("src/tgt return types differ")
        n = len(sargs)


        if witness.get('schema') != 1:
            raise Unsupported("witness schema != 1")
        wargs = witness.get('args', [])
        if len(wargs) != n:
            raise Unsupported(f"witness arity {len(wargs)} != {n} surface args")
        isha = witness.get('input_sha256')
        if isha:
            actual = hashlib.sha256(text.encode('utf-8')).hexdigest()
            if actual != isha:
                raise Unsupported("stale witness: input_sha256 mismatch")


        expected = witness.get('expected') or {}
        tgt_out = expected.get('tgt') or {}


        cex_fuel = None
        if cfg_mode:
            cex_fuel = witness.get('fuel')
            if cex_fuel is None:
                raise Unsupported("multi-block (CFG) witness needs a `fuel` key: the "
                                  "memory relation quantifies over fuel, so refuting "
                                  "it means naming one")
            if not isinstance(cex_fuel, int) or isinstance(cex_fuel, bool):
                raise Unsupported(f"witness fuel {cex_fuel!r} is not an integer")
            if cex_fuel <= 0:
                raise Unsupported("witness fuel must be positive (at fuel 0 the source "
                                  "is immediate UB, which refines everything)")
            if cex_fuel > CEX_CFG_MAX_FUEL:
                raise Unsupported(
                    f"witness fuel {cex_fuel} exceeds the CFG-CEX bound "
                    f"{CEX_CFG_MAX_FUEL} (the simp unrolling would not close; "
                    f"declining beats emitting a scaffold that cannot compile)")


        arg_cw = [concretize(w, wv, W) for _, w in sargs]
        retw = concretize(parse_type(sret, wv), wv, W)
        src_impure = has_assume(src_body)
        tgt_impure = has_assume(tgt_body)
        if cfg_mode:


            src_impure = src_impure or ns_blocks > 1
            tgt_impure = tgt_impure or nt_blocks > 1


        pairs = list(zip(arg_cw, wargs))
        cons = []
        for w_arg in reversed(pairs):
            cw, a = w_arg
            k = a.get('kind', 'value')
            if k == 'value':
                cons.append((cw, ('value', a['nat'])))
            elif k == 'poison':
                cons.append((cw, ('poison',)))
            else:
                raise Unsupported(f"witness arg kind {k!r} (value|poison only)")


        tgt_kind = tgt_out.get('kind')
        if tgt_kind is None:
            shape = 'CEX-S0'
        else:
            shape = {'value': 'CEX-S1', 'ub': 'CEX-S2', 'poison': 'CEX-S3'}.get(tgt_kind)
            if shape is None:
                raise Unsupported(f"tgt outcome kind {tgt_kind!r} unsupported")


        if dialect == 'sym':
            proofs = []
            for g in re.findall(r'\([^)]*\)', extras_text):
                bm = re.fullmatch(r'\(\s*[^:\s]+\s*:\s*(.*?)\s*\)', g.strip(), re.S)
                btype = bm.group(1)
                btype_c = subst_widths(btype, wmap)
                proofs.append(f"(by decide : {btype_c})")
            app_suffix = (" " + " ".join(proofs)) if proofs else ""
            wapp = " ".join(wmap[s] for s in wv)
            src_app = f"{src_name} {wapp}{app_suffix}"
            tgt_app = f"{tgt_name} {wapp}{app_suffix}"
        else:
            src_app, tgt_app = src_name, tgt_name


        if cfg_mode:
            sym = None if dialect == 'fw' else {
                'wv': wv, 'wmap': wmap, 'extras_text': extras_text,
                'extra_names': extra_names, 'proofs': proofs,
            }
            cfg_tac = 'native_decide' if tier == 'native' else 'decide +kernel'
            return cfg_emit(text, case, witness, src_name, tgt_name, src_full,
                            tgt_full, src_body, tgt_body, cons, retw, shape,
                            cex_fuel, ns_blocks, nt_blocks, hole,
                            src_app=src_app, tgt_app=tgt_app, sym=sym,
                            eval_tac=cfg_tac)
        L = []
        L.append("import SSA.Projects.InstCombine.Refinement")
        L.append("import LeanMLIR.Dialects.LLVM.Syntax")
        L.append("")
        L.append("open scoped InstCombine")
        L.append("open BitVec")
        L.append("")
        L.append(f"-- ===== GIVEN (input): the two programs (verbatim) =====")
        L.append(src_full.strip())
        L.append("")
        L.append(tgt_full.strip())
        L.append("")
        L.append(f"-- ===== AUTO-EMITTED CEX SCAFFOLD ({shape}; witness FROZEN "
                 f"(inputs only); 0 LLM) =====")
        L.append(f"section {case}_cex")
        L.append("")
        L.append(plumbing(case))
        L.append("")
        L.append(refinement_decidables(case, retw, src_impure, tgt_impure))
        L.append("")
        L.append("-- FROZEN WITNESS: cons chain = reverse of surface-order args; immutable.")
        L.append(cex_inputs(case, cons))
        L.append("")
        L.append(f"theorem {case}_correct_counterexample_witness : ¬ ({src_app} ⊑ {tgt_app}) := by")
        L.append(f"  intro h")
        if hole:
            L.append(f"  sorry")
            expected_sorries = 1
        else:
            L.append(f"  have hyp : InstCombine.IsRefinedByOnIntWInputs ({src_app}) ({tgt_app}) :=")
            L.append(f"    (InstCombine.isRefinedByOnIntWInputs_iff ({src_app}) ({tgt_app})).mp h")
            L.append(f"  specialize hyp {case}_cexInputs")
            L.append(cex_closer(eval_tac))
            expected_sorries = 0
        L.append("")
        L.append(f"end {case}_cex")
        L.append("")
        if dialect == 'sym':
            wsyms = " ".join(wv)
            exists_binds = f"({wsyms} : Nat)" + (extras_text if extras_text else "")
            bnames = (" " + " ".join(extra_names)) if extra_names else ""
            wit_tuple = "⟨" + ", ".join(wmap[s] for s in wv)
            for g in (re.findall(r'\([^)]*\)', extras_text) if extras_text else []):
                bm = re.fullmatch(r'\(\s*[^:\s]+\s*:\s*(.*?)\s*\)', g.strip(), re.S)
                btype_c = subst_widths(bm.group(1), wmap)
                wit_tuple += f", (by decide : {btype_c})"
            wit_tuple += f", {case}_correct_counterexample_witness⟩"
            L.append(f"theorem {case}_correct_counterexample :")
            L.append(f"    ∃ {exists_binds}, ¬ ({src_name} {wsyms}{bnames} ⊑ {tgt_name} {wsyms}{bnames}) :=")
            L.append(f"  {wit_tuple}")
        else:
            L.append(f"theorem {case}_correct_counterexample : ¬ ({src_name} ⊑ {tgt_name}) :=")
            L.append(f"  {case}_correct_counterexample_witness")

        content = "\n".join(L) + "\n"
        isha_val = witness.get('input_sha256') or hashlib.sha256(text.encode('utf-8')).hexdigest()
        cid = candidate_id(isha_val, witness)
        mainfile = f"{case}.cex.{cid[:12]}.lean"
        return {
            'status': 'ok',
            'reason': '',
            'shape': shape,
            'expected_sorries': expected_sorries,
            'candidate_id': cid,
            'mainfile': mainfile,
            'files': {mainfile: content},
        }


    def emit_cex_safe(text, case, witness, tier='strict', hole=False):
        try:
            return emit_cex(text, case, witness, tier=tier, hole=hole)
        except Unsupported as e:
            return {'status': 'decline', 'reason': str(e), 'shape': 'CEX',
                    'expected_sorries': 0, 'files': {},
                    'fence_line': getattr(e, 'fence_line', None)}
        except Exception as e:
            return {'status': 'decline', 'reason': f'internal: {type(e).__name__}: {e}',
                    'shape': 'CEX', 'expected_sorries': 0, 'files': {},
                    'fence_line': getattr(e, 'fence_line', None)}

    return types.SimpleNamespace(FAMILY=FAMILY, emit_cex=emit_cex, emit_cex_safe=emit_cex_safe, load_witness=load_witness)

A2 = _build_shape_a2()
B2 = _build_shape_b2()
CFG = _build_shape_cfg()
CEX_MOD = _build_shape_cex()


def _canon_schedule_block(lines):
    assigns = []
    others = []
    for ln in lines:
        if re.match(r'\s*%[\w]+\s*=\s*llvm\.', ln):
            assigns.append(ln)
        else:
            others.append(ln)
    if not assigns:
        return lines
    defs = {}
    for ln in assigns:
        m = re.match(r'\s*%(\w+)\s*=', ln)
        defs[m.group(1)] = ln
    dep = {}
    for dst, ln in defs.items():
        body_part = ln.split('=', 1)[1]
        dep[dst] = [u for u in re.findall(r'%(\w+)', body_part) if u in defs]

    hashes = {}

    def h(dst):
        if dst in hashes:
            return hashes[dst]
        ln = defs[dst]
        body_part = re.sub(r'%\w+', '%', ln.split('=', 1)[1].strip())
        key = (body_part, tuple(h(u) for u in dep[dst]))
        hashes[dst] = hashlib.sha256(repr(key).encode()).hexdigest()[:16]
        return hashes[dst]

    for dst in defs:
        h(dst)
    placed = set()
    ordered = []
    remaining = set(defs)
    while remaining:
        ready = sorted((d for d in remaining
                        if all(u in placed for u in dep[d])),
                       key=lambda d: hashes[d])
        if not ready:
            ordered.extend(defs[d] for d in sorted(remaining))
            break
        d = ready[0]
        ordered.append(defs[d])
        placed.add(d)
        remaining.discard(d)
    return ordered + others


def _normalize_cfg_text(text):
    def norm_region(m):
        body = m.group(0)

        lines = body.split('\n')
        out_lines = []
        block = None
        for ln in lines:
            if re.match(r'\s*\^\w+\([^)]*\):', ln):
                if block is not None:
                    out_lines.extend(_canon_schedule_block(block))
                block = []
                out_lines.append(ln)
            elif block is not None and (ln.strip().startswith('}')
                                        or ln.strip() == '}]'):
                out_lines.extend(_canon_schedule_block(block))
                block = None
                out_lines.append(ln)
            elif block is not None:
                block.append(ln)
            else:
                out_lines.append(ln)
        if block is not None:
            out_lines.extend(_canon_schedule_block(block))
        body = '\n'.join(out_lines)

        labels = []
        for lm in re.finditer(r'\^(\w+)', body):
            if lm.group(1) not in labels:
                labels.append(lm.group(1))
        lmap = {l: 'bb%d' % i for i, l in enumerate(labels)}
        body = re.sub(r'\^(\w+)', lambda mm: '^' + lmap[mm.group(1)], body)
        vals = []
        for vm in re.finditer(r'%(\w+)', body):
            if vm.group(1) not in vals:
                vals.append(vm.group(1))
        vmap = {v: 'v%d' % i for i, v in enumerate(vals)}
        body = re.sub(r'%(\w+)', lambda mm: '%' + vmap[mm.group(1)], body)
        return body
    return re.sub(r'\[llvm\([^)]*\)\|.*?\}\]', norm_region, text, flags=re.S)


def _is_multiblock(text):
    if re.search(r'llvm\.(cond_)?br\s', text):
        return True
    for m in re.finditer(r'\[llvm\([^)]*\)\|', text):
        close = text.find('}]', m.end())
        region = text[m.end(): close if close >= 0 else len(text)]
        if len(re.findall(r'\^\w+\([^)]*\):', region)) >= 2:
            return True
    return False


def route(text):
    if _is_multiblock(text):
        return CFG
    if 'llvm.assume' in text:
        return B2
    return A2


def _write_trace(outdir, case, r):
    if not os.environ.get('EMIT_TRACE'):
        return
    try:
        os.makedirs(outdir, exist_ok=True)
        with open(os.path.join(outdir, case + '.trace.json'), 'w',
                  encoding='utf-8') as f:
            json.dump({'case': case, 'status': r.get('status'),
                       'shape': r.get('shape'), 'reason': r.get('reason', ''),
                       'fence_line': r.get('fence_line'),
                       'expected_sorries': r.get('expected_sorries')}, f)
    except Exception:
        pass


def main(argv):
    if '--version' in argv:
        print(VERSION)
        return 0
    import argparse
    ap = argparse.ArgumentParser(
        prog='emit_scaffold.py',
        description='Unified deterministic scaffold emitter (A2 | B2 | CFG). '
                    'Prints CASE\\tSHAPE\\tMAINFILE\\tEXPECTED_SORRIES\\t'
                    'COMPANIONS on success (exit 0) or CASE\\tDECLINED\\t'
                    'reason (exit 2).')
    ap.add_argument('input', help='problem INPUT.lean file')
    ap.add_argument('--outdir', required=True, help='output directory')
    ap.add_argument('--case', default=None,
                    help='case name (default: basename of INPUT without .lean)')
    ap.add_argument('--cex-witness', default=None, dest='cex_witness',
                    help='WITNESS.json -> emit a deterministic counterexample '
                         'certificate instead of a proof scaffold.')
    ap.add_argument('--cex-tier', default='auto', dest='cex_tier',
                    choices=['strict', 'native', 'auto', 'kernel'],
                    help='CEX eval tier: strict=decide (0 LLM, kernel), '
                         'kernel=decide +kernel (same axioms as strict; skips the '
                         'elaborator, use when strict dies on a whnf heartbeat '
                         'timeout), native=native_decide (separate trust tier), '
                         'auto=strict.')
    ap.add_argument('--cex-hole', action='store_true', dest='cex_hole',
                    help='CEX: leave the separation closer as sorry (1 sorry) for the '
                         'LLM arm; the eval lemmas stay deterministic.')
    a = ap.parse_args(argv)
    try:
        case = a.case or os.path.splitext(os.path.basename(a.input))[0]
    except Exception:
        case = 'unknown'
    try:
        try:
            with open(a.input, encoding='utf-8') as f:
                text = f.read()
        except Exception as e:
            print('%s\tDECLINED\tcannot read input: %s' % (case, e))
            return 2


        if getattr(a, 'cex_witness', None):
            witness = CEX_MOD.load_witness(a.cex_witness)
            r = CEX_MOD.emit_cex_safe(text, case, witness,
                                      tier=a.cex_tier, hole=a.cex_hole)
            _write_trace(a.outdir, case, r)
            if r.get('status') != 'ok':
                print('%s\tDECLINED\t[CEX] %s' % (case, r.get('reason', '')))
                return 2
            mainfile = r['mainfile']
            os.makedirs(a.outdir, exist_ok=True)
            for fn, content in r['files'].items():
                with open(os.path.join(a.outdir, fn), 'w', encoding='utf-8') as f:
                    f.write(content)
            companions = ','.join(sorted(fn for fn in r['files']
                                         if fn != mainfile)) or '-'
            print('%s\t%s\t%s\t%d\t%s' % (
                case, r['shape'], os.path.join(a.outdir, mainfile),
                r['expected_sorries'], companions))
            return 0
        mod = route(text)
        r = mod.emit(text, case)
        _write_trace(a.outdir, case, r)
        if r.get('status') != 'ok':
            print('%s\tDECLINED\t[%s] %s' % (case, mod.FAMILY,
                                             r.get('reason', '')))
            return 2
        mainfile = case + '.lean'
        if mainfile not in r['files']:
            print('%s\tDECLINED\t[%s] internal: module returned no main file %s'
                  % (case, mod.FAMILY, mainfile))
            return 2
        os.makedirs(a.outdir, exist_ok=True)
        for fn, content in r['files'].items():
            with open(os.path.join(a.outdir, fn), 'w', encoding='utf-8') as f:
                f.write(content)
        companions = ','.join(sorted(fn for fn in r['files']
                                     if fn != mainfile)) or '-'
        print('%s\t%s\t%s\t%d\t%s' % (
            case, r['shape'], os.path.join(a.outdir, mainfile),
            r['expected_sorries'], companions))
        return 0
    except Exception as e:

        print('%s\tDECLINED\tinternal error: %s: %s'
              % (case, type(e).__name__, e))
        return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
