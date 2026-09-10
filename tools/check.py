#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
import sys

STD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
COMPILED_TRUST_AXIOMS = {'Lean.ofReduceBool', 'Lean.trustCompiler'}


def strip_comments(t):
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


def read(path):
    try:
        return open(path, encoding='utf-8', errors='ignore').read()
    except OSError:
        return ''


def count(path, regex):
    return len(re.findall(regex, strip_comments(read(path))))


def qualified(path, name):
    stack = []
    found = None
    for line in read(path).split('\n'):
        m = re.match(r'\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)', line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r'\s*end\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$', line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        if found is None and re.match(r'\s*(private\s+)?(theorem|lemma)\s+' + re.escape(name) + r'\b', line):
            found = list(stack)
    ns = '.'.join(found or [])
    return (ns + '.' + name) if ns else name


def statement_line(path, name):
    for line in read(path).split('\n'):
        if re.match(r'\s*(private\s+)?theorem\s+' + re.escape(name) + r'\b', line):
            return line
    return ''


def mask_hole(text):
    lines = text.split('\n')
    out = []
    i = 0
    while i < len(lines):
        L = lines[i]
        if re.match(r'theorem \w+_correct_counterexample_witness ', L):
            out.append(L)
            while ':= by' not in lines[i]:
                i += 1
                out.append(lines[i])
            out.append('  <<HOLE>>')
            i += 1
            while i < len(lines) and not lines[i].startswith('end '):
                i += 1
            continue
        out.append(L)
        i += 1
    return '\n'.join(out)


def nonhole_diff(emitted, final, hole):
    a = (mask_hole(emitted) if hole else emitted).split('\n')
    b = (mask_hole(final) if hole else final).split('\n')
    if a == b:
        return []
    viol = []
    for j in range(max(len(a), len(b))):
        la = a[j] if j < len(a) else '<EOF>'
        lb = b[j] if j < len(b) else '<EOF>'
        if la != lb:
            viol.append('line %d: emitted=%r final=%r' % (j + 1, la, lb))
            if len(viol) >= 3:
                break
    return viol


def axiom_audit(path, thm, allow_compiled, repo, timeout):
    tmp = path + '.axioms.lean'
    open(tmp, 'w', encoding='utf-8').write(read(path) + '\n#print axioms %s\n' % thm)
    try:
        p = subprocess.run(['bash', '-c', 'cd "%s" && timeout %d lake env lean "%s"' % (repo, timeout, tmp)],
                           capture_output=True, text=True)
        out = (p.stdout or '') + (p.stderr or '')
        m = re.search(r"depends on axioms:\s*\[([^\]]*)\]", out)
        if not m:
            if re.search(r"does not depend on any axioms", out):
                return [], []
            return None, ['could not read axiom list (rc=%d): %s' % (p.returncode, out.strip()[:300])]
        axset = sorted(a.strip() for a in m.group(1).split(',') if a.strip())
        allowed = STD_AXIOMS | (COMPILED_TRUST_AXIOMS if allow_compiled else set())
        extra = sorted(set(axset) - allowed)
        return axset, (['non-standard axiom(s): %s' % extra] if extra else [])
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


def main():
    ap = argparse.ArgumentParser(prog='check.py')
    sub = ap.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('count')
    c.add_argument('file')
    c.add_argument('regex')
    q = sub.add_parser('qualified')
    q.add_argument('file')
    q.add_argument('name')
    s = sub.add_parser('statement')
    s.add_argument('file')
    s.add_argument('name')
    t = sub.add_parser('trust')
    t.add_argument('emitted')
    t.add_argument('final')
    t.add_argument('--thm', default=None)
    t.add_argument('--tier', default='strict', choices=['strict', 'kernel', 'native'])
    t.add_argument('--hole', action='store_true')
    t.add_argument('--repo', default=os.environ.get('REPO', ''))
    t.add_argument('--axioms-only', action='store_true')
    t.add_argument('--allow-compiled', action='store_true')
    t.add_argument('--skip-nonhole', action='store_true')
    t.add_argument('--timeout', type=int, default=int(os.environ.get('AXIOM_TIMEOUT', '900')))
    a = ap.parse_args()
    if a.cmd == 'count':
        print(count(a.file, a.regex))
        return 0
    if a.cmd == 'qualified':
        print(qualified(a.file, a.name))
        return 0
    if a.cmd == 'statement':
        print(statement_line(a.file, a.name))
        return 0
    tier = 'native' if a.tier == 'native' else 'strict'
    fails = []
    if not a.axioms_only and not a.skip_nonhole:
        d = nonhole_diff(read(a.emitted), read(a.final), a.hole)
        if d:
            fails.append('non-hole-region-modified: ' + ' | '.join(d))
    if not a.axioms_only:
        body = strip_comments(read(a.final))
        bad = [tok for tok in ('sorry', 'admit') if re.search(r'\b' + tok + r'\b', body)]
        if tier != 'native' and re.search(r'\bnative_decide\b', body):
            bad.append('native_decide')
        if bad:
            fails.append('forbidden-tokens: ' + ', '.join(bad))
    if a.thm:
        if not a.repo:
            fails.append('axiom-audit: REPO not set')
        else:
            axset, errs = axiom_audit(a.final, a.thm, a.allow_compiled or tier == 'native', a.repo, a.timeout)
            if axset is not None:
                print('axioms: ' + ', '.join(axset))
            fails.extend('axiom-audit: ' + e for e in errs)
    if fails:
        print('trust-policy-failed')
        for f in fails:
            print('  - ' + f)
        return 3
    print('trust-OK')
    return 0


if __name__ == '__main__':
    sys.exit(main())
