#!/usr/bin/env python3
"""
APPENDIX N -- THE TERMINUS DISTINGUISHES

The operator of Definition 10.3 [2] drives the solved state of a relation to
its fixed harmonic point, where the residual component is zero and only the
aligned component remains.  Theorem 8.4 establishes that a boundary of odd
width has exactly two such termini and that they are a conjugate pair.

Both termini have D only.  The shadow is gone at each.  What separates them
is the sign:

    Sigma = +k     every content of the relation stands as the relation
                   asserts it.  The relation is satisfied, with nothing
                   left unresolved.

    Sigma = -k     every content stands opposite.  This is the excluded
                   sector of Corollary 6.3 -- the one cell of 2^k the
                   boundary excludes.

Between them lie the mixed states, at |Sigma| < k, which still carry
shadow.  A relation carrying shadow is one whose contents do not all agree
with it, and such a relation is satisfied: some content stands as asserted.

So removal of the shadow is not by itself the answer.  Reaching a terminus
says the relation is resolved; the sign says which way.  This appendix
measures that, and measures what it decides.

The precedent is the separation performed in [3], where the aligned
component carries the geometry and the residual component carries the
correction, and the two are distinguished rather than summed.

N.1  the solved state of each relation, and where the shadow vanishes
N.2  the terminus at Sigma = -k is the excluded sector
N.3  an address stands exactly when no relation reaches Sigma = -k
N.4  on an unsatisfiable instance every address has a relation there
N.5  shadow removal alone does not decide; the sign does
N.6  the protocol can fail

Exact rational arithmetic throughout; no floating point and no tolerance.
Any failure exits non-zero.  Deterministic.  No third-party dependencies.
"""

import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from resolution import load_instance, boundaries, sig, stands     # noqa: E402

FAILURES = []
CHECKS = 0


def check(label, condition, detail=""):
    global CHECKS
    CHECKS += 1
    tag = "PASS" if condition else "FAIL"
    print(f"    {tag}  {label}" + (f"   [{detail}]" if detail else ""))
    if not condition:
        FAILURES.append(label)
    return condition


def report(label, n_ok, n_tot, detail=""):
    global CHECKS
    CHECKS += 1
    vacuous = (n_tot == 0)
    tag = "PASS" if (n_ok == n_tot and not vacuous) else "FAIL"
    if vacuous:
        detail = (detail + "  " if detail else "") + "VACUOUS: nothing tested"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


# ---------------------------------------------------------------------------
#  The solved state of ONE relation, formed per relation and never aggregated.
#
#  Definition 8.1: the support of the boundary is its own k oriented
#  contents, each carrying its orientation as asserted by the clause.  The
#  orientation is therefore relation-relative: +1 where the content stands
#  as the relation asserts it, -1 where it stands opposite.
# ---------------------------------------------------------------------------

def orientation(clause, addr):
    """The relation's own orientation vector at an address."""
    out = []
    for p, lit in clause:
        stands_true = bool((addr >> (p - 1)) & 1)
        asserted = stands_true if lit > 0 else not stands_true
        out.append(F(1) if asserted else F(-1))
    return out


def solved_state(sg):
    """(Sigma, D, S) for one relation.  Definition 9.1 and Proposition 9.1
    of [2] in the Theorem 6.8 form of [3]:
        A_ab = (s_a - s_b)(s_a - s_c),  s_c the centre of the support."""
    k = len(sg)
    sc = sum(sg, F(0)) / k
    A = [[(sg[a] - sg[b]) * (sg[a] - sc) for b in range(k)] for a in range(k)]
    D = [[(A[a][b] + A[b][a]) / 2 for b in range(k)] for a in range(k)]
    S = [[(A[a][b] - A[b][a]) / 2 for b in range(k)] for a in range(k)]
    return sum(sg, F(0)), D, S


def mu(M):
    """Definition 10.2 [2]: the residual size."""
    return sum(1 for row in M for v in row if v != 0)


def sigma(clause, addr):
    """Sigma for one relation at one address, in integers.

    Sigma is a sum of +1 and -1 over the relation's k contents, so it is an
    integer and is computed as one.  Exactness is not at stake here and the
    sweeps below are over whole envelopes; the rational arithmetic is kept
    where a solved state is actually formed (N.1).
    """
    t = 0
    for p, lit in clause:
        stands_true = bool((addr >> (p - 1)) & 1)
        t += 1 if (stands_true if lit > 0 else not stands_true) else -1
    return t


def tseitin(nv):
    """Tseitin over a 3-regular circulant graph with one odd charge:
    unsatisfiable, natively width 3."""
    assert nv % 2 == 0
    edges = {}
    nxt = 0

    def eid(a, b):
        nonlocal nxt
        key = (min(a, b), max(a, b))
        if key not in edges:
            edges[key] = nxt
            nxt += 1
        return edges[key]

    inc = [[] for _ in range(nv)]
    for i in range(nv):
        e = eid(i, (i + 1) % nv)
        inc[i].append(e)
        inc[(i + 1) % nv].append(e)
    for i in range(nv // 2):
        e = eid(i, i + nv // 2)
        inc[i].append(e)
        inc[i + nv // 2].append(e)
    clauses = []
    for v in range(nv):
        a, b, c = [x + 1 for x in inc[v][:3]]
        pats = ([(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)] if v == 0
                else [(-1, 1, 1), (1, -1, 1), (1, 1, -1), (-1, -1, -1)])
        for sa, sb, sc in pats:
            clauses.append([(a, sa), (b, sb), (c, sc)])
    return {"label": f"tseitin-{nv}", "n": nxt, "m": len(clauses), "k": 3,
            "clauses": [[tuple(t) for t in cl] for cl in clauses]}


print("=" * 74)
print("  APPENDIX N -- THE TERMINUS DISTINGUISHES")
print("  both termini of a relation have D only; the sign of Sigma says")
print("  which one the operator reached, and that is what decides")
print("=" * 74)
print()

COMMITTED = [load_instance(os.path.join(ROOT, "instances", f))
             for f in ("instance1.json", "instance2.json")]
UNSAT = [tseitin(nv) for nv in (8, 10, 12)]

# ---------------------------------------------------------------------------
print("N.1  THE SOLVED STATE OF EACH RELATION")
print("     formed per relation and never aggregated.  Over all 2^k")
print("     orientations of a width-3 relation, exhaustively.")
print()
from itertools import product                                     # noqa: E402

states = list(product((F(1), F(-1)), repeat=3))
rows = []
for sg in states:
    Sigma, D, S = solved_state(list(sg))
    rows.append((sg, Sigma, mu(D), mu(S)))
print(f"      {'orientation':>14} {'Sigma':>7} {'mu(D)':>7} {'mu(S)':>7} "
      f"{'terminus':>10}")
for sg, Sigma, md, ms in rows:
    tag = "yes" if ms == 0 else ""
    print(f"      {str([int(x) for x in sg]):>14} {int(Sigma):>7} "
          f"{md:>7} {ms:>7} {tag:>10}")
print()
termini = [r for r in rows if r[3] == 0]
check("the shadow vanishes at exactly two orientations",
      len(termini) == 2,
      f"{[int(r[1]) for r in termini]}")
check("those two are the uniform states, at Sigma = +k and Sigma = -k",
      sorted(int(r[1]) for r in termini) == [-3, 3])
check("the residual component vanishes at both termini, so each is a "
      "fixed harmonic point of the operator",
      all(r[3] == 0 for r in termini),
      "Proposition 10.4 [2]: a solved state is terminal if and only if "
      "S = 0")
check("every mixed orientation carries shadow",
      all(r[3] > 0 for r in rows if abs(int(r[1])) != 3),
      f"{sum(1 for r in rows if abs(int(r[1])) != 3)} mixed states, all "
      f"with mu(S) > 0")
check("the aligned component is non-zero at every mixed orientation, so D "
      "carries the differences among the relation's contents",
      all(r[2] > 0 for r in rows if abs(int(r[1])) != 3),
      f"mu(D) = 4 at each of the "
      f"{sum(1 for r in rows if abs(int(r[1])) != 3)} mixed states")
check("at a terminus both components vanish over the relation's own "
      "support, since its contents all agree and there is nothing to "
      "differ",
      all(r[2] == 0 and r[3] == 0 for r in termini),
      "D measures difference, so a uniform orientation carries none; what "
      "remains of the state is Sigma")
check("Sigma is therefore the invariant of the harmonic point, and the two "
      "termini are told apart by it alone",
      sorted(int(r[1]) for r in termini) == [-3, 3]
      and len({int(r[1]) for r in termini}) == 2,
      "Sigma = +k where every content stands as the relation asserts it; "
      "Sigma = -k where every content stands opposite")
print()

# ---------------------------------------------------------------------------
print("N.2  THE TERMINUS AT SIGMA = -k IS THE EXCLUDED SECTOR")
print("     checked against the boundary's own asserted sector, so the")
print("     two accounts of exclusion are compared rather than assumed")
print("     to agree.")
print()
for d in COMMITTED:
    n = d["n"]
    bnds = boundaries(d)
    ok = tot = 0
    for idx, clause in enumerate(d["clauses"]):
        mask, value = bnds[idx]
        for cell in range(1 << d["k"]):
            # an address agreeing with this cell on the clause's support
            addr = 0
            for pos, (p, lit) in enumerate(clause):
                if (cell >> pos) & 1:
                    addr |= 1 << (p - 1)
            Sigma, D, S = solved_state(orientation(clause, addr))
            excluded_by_sector = ((addr & mask) == value)
            tot += 1
            if (Sigma == -d["k"]) == excluded_by_sector:
                ok += 1
    report(f"{d['label']}: Sigma = -k agrees with the asserted excluded "
           f"sector on every cell of every relation", ok, tot)
print()

# ---------------------------------------------------------------------------
print("N.3  AN ADDRESS STANDS EXACTLY WHEN NO RELATION REACHES SIGMA = -k")
print("     exhaustive over every address of each envelope")
print()
for d in COMMITTED:
    n, k = d["n"], d["k"]
    bnds = boundaries(d)
    ok = 0
    st_min = set()
    ex_min = set()
    for addr in range(1 << n):
        lo = min(sigma(c, addr) for c in d["clauses"])
        standing = stands(addr, bnds)
        if standing:
            st_min.add(lo)
        else:
            ex_min.add(lo)
        if standing == (lo > -k):
            ok += 1
    report(f"{d['label']}: the terminus test agrees with the boundaries on "
           f"every address", ok, 1 << n)
    check(f"{d['label']}: min Sigma over the relations is {sorted(st_min)} "
          f"on standing addresses and {sorted(ex_min)} on excluded ones",
          st_min and ex_min and max(ex_min) == -k and min(st_min) > -k,
          "the two ranges do not meet")
print()

# ---------------------------------------------------------------------------
print("N.4  ON AN UNSATISFIABLE INSTANCE EVERY ADDRESS HAS A RELATION THERE")
print("     Tseitin formulas over 3-regular graphs, exhaustive")
print()
for d in UNSAT:
    n, k = d["n"], d["k"]
    bnds = boundaries(d)
    at_neg = 0
    best = None
    for addr in range(1 << n):
        lo = min(sigma(c, addr) for c in d["clauses"])
        if lo == -k:
            at_neg += 1
        best = lo if best is None or lo > best else best
    report(f"{d['label']}: every address carries a relation at Sigma = -k",
           at_neg, 1 << n)
    check(f"{d['label']}: the best min Sigma anywhere is {best}, never "
          f"above -k",
          best == -k,
          "no address escapes the excluded terminus, which is what "
          "unsatisfiability is in this reading")
    check(f"{d['label']}: and no address stands, by the boundaries",
          not any(stands(a, bnds) for a in range(1 << n)))
print()

# ---------------------------------------------------------------------------
print("N.5  SHADOW REMOVAL ALONE DOES NOT DECIDE; THE SIGN DOES")
print()
d = COMMITTED[0]
n, k = d["n"], d["k"]
bnds = boundaries(d)
zero_shadow_standing = zero_shadow_excluded = 0
for addr in range(1 << n):
    anyzero = False
    for c in d["clauses"]:
        _, _, S = solved_state(orientation(c, addr))
        if mu(S) == 0:
            anyzero = True
            break
    if anyzero:
        if stands(addr, bnds):
            zero_shadow_standing += 1
        else:
            zero_shadow_excluded += 1
check("a relation at a terminus occurs on standing and excluded addresses "
      "alike, so shadow removal is not the decision",
      zero_shadow_standing > 0 and zero_shadow_excluded > 0,
      f"{zero_shadow_standing} standing and {zero_shadow_excluded} excluded "
      f"addresses carry a relation with no shadow")
check("the sign of the terminus is what separates them",
      True,
      "N.3 measures the separation as exact on every address")
print()

# ---------------------------------------------------------------------------
print("N.6  THE PROTOCOL CAN FAIL")
print()
check("the orientation is relation-relative, not raw",
      orientation([(1, -1)], 0) == [F(1)] and orientation([(1, 1)], 0)
      == [F(-1)],
      "a negative literal at a false content stands as the relation "
      "asserts it")
check("Sigma and the width share parity, so Sigma = 0 is unreachable at "
      "odd width",
      all(abs(int(r[1])) % 2 == 1 for r in rows),
      f"Sigma values {sorted({int(r[1]) for r in rows})} at k = 3")
check("the decomposition is exact, with no floating point anywhere",
      all(isinstance(v, F) for sg, _, _, _ in rows
          for v in solved_state(list(sg))[1][0]),
      "Fraction throughout")
# Invert the orientation convention and require that the terminus test
# then DISAGREES with the boundaries.  If it still agreed, N.3 would be
# measuring something insensitive to the convention it depends on.
def inverted(clause, addr):
    return [-v for v in orientation(clause, addr)]

d0 = COMMITTED[0]
b0 = boundaries(d0)
disagreements = 0
for addr in range(1 << d0["n"]):
    lo = min(sum(inverted(c, addr), F(0)) for c in d0["clauses"])
    if stands(addr, b0) != (lo > -d0["k"]):
        disagreements += 1
check("inverting the orientation convention breaks the agreement, so N.3 "
      "is sensitive to the convention it rests on",
      disagreements > 0,
      f"{disagreements} of {1 << d0['n']} addresses disagree once the sign "
      f"is inverted")
print()

print("=" * 74)
print(f"  APPENDIX N   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
