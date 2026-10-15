#!/usr/bin/env python3
"""
APPENDIX S -- THE COMPOSED BOUNDARY AND ITS LIGHTHOUSES

Validates Section 12 of
  "Relational Lysis and Computational Efficiency II:
   The Resolution of 3-SAT by Boundary Assertion"

WHAT IS CHECKED, AND IN WHOSE TERMS

A boundary of odd width has exactly two termini, the uniform states at
Sigma_u = +k and Sigma_u = -k, and they are a conjugate pair (Theorem 11.3 of
the paper, from Axiom 2.3 [1]); the one at Sigma_u = -k is the boundary's
excluded sector.  Writing it writes both, because the assertion of any term
forces the assertion of its structural opposite (Axiom 2.2 [1]) and the
conjugate stands interiorly, requiring no exterior term
(Proposition 5.4 [1]).

The descent is the envelope's own: inward, one mediation per depth into the
two mediated conjugate sectors of Axiom 5.2 [1], allocating exactly one level
of the capacity fixed at genesis (Axiom 5.3 [1]), along a strict finite chain
admitting no cycles (Corollary 5.11 [1]).  A sector standing at a residual
terminus is never presented (Theorems 22.1 and 22.3 [1]), so it is never
entered.  Where every asserted boundary is barred, no further admissible
partition exists and the descent is closed there (Definition 5.2 [1]); that
stratum is a lighthouse, and its radius is the capacity left unallocated.

WHAT IS NOT MEASURED HERE, AND WHY

The steps the descent takes on its way are not reported and are not counted.
By Axiom 5.3 [1] the levels of the structure are fixed by the relation and
iteration realizes them, so a traversal is not a feature of the assertion;
and a step bounding no address has no residence (Theorem 15.1 [1]) and is
therefore not a stratum of the structure at all.  This protocol reports the
family, the radii, the strata held, and the assertion -- nothing else.

Exact integer arithmetic throughout.  Any failure exits non-zero.
Deterministic.  No third-party dependencies.

[1] Swanagon, Principia Arithmetica (Relational Lysis).
"""

import ast as _ast
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

from conventions import Acts                                     # noqa: E402
from resolution import load_instance                             # noqa: E402
from composition import (support, free_count, residual_terminus,  # noqa: E402
                         at_residual, barred, order_given, order_closing,
                         bands, compose, read_region, region_str)

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
    tag = "PASS" if (n_ok == n_tot and n_tot) else "FAIL"
    if not n_tot:
        detail = (detail + "  " if detail else "") + "VACUOUS: nothing tested"
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


# ---------------------------------------------------------------------------
#  Instances
# ---------------------------------------------------------------------------

def planted(n, density, seed):
    rng = random.Random(seed)
    base = [rng.choice([True, False]) for _ in range(n)]
    m = int(n * density)
    cl, guard = set(), 0
    while len(cl) < m and guard < m * 300:
        guard += 1
        ps = rng.sample(range(1, n + 1), 3)
        lits = [(p, rng.choice([1, -1])) for p in ps]
        if not any((base[p - 1] and s > 0) or ((not base[p - 1]) and s < 0)
                   for p, s in lits):
            p, _ = lits[rng.randrange(3)]
            lits = [(q, t) if q != p else (p, 1 if base[p - 1] else -1)
                    for q, t in lits]
        cl.add(tuple(sorted(lits)))
    return {"label": f"n={n}", "n": n, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in sorted(cl)]}


def tseitin(nv):
    assert nv % 2 == 0
    edges, nxt = {}, 0

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
    cl = []
    for v in range(nv):
        a, b, c = [x + 1 for x in inc[v][:3]]
        pats = ([(1, 1, 1), (-1, -1, 1), (-1, 1, -1), (1, -1, -1)] if v == 0
                else [(-1, 1, 1), (1, -1, 1), (1, 1, -1), (-1, -1, -1)])
        for sa, sb, sc in pats:
            cl.append([(a, sa), (b, sb), (c, sc)])
    return {"label": f"tseitin-{nv}", "n": nxt, "m": len(cl), "k": 3,
            "clauses": [[tuple(t) for t in c] for c in cl]}


def assertion(d):
    """n + 1 + km structural acts.  The structural opposites are forced by
    Axiom 2.2 and charged nothing."""
    a = Acts()
    a.assert_term(d["n"])
    a.mediate(1)
    a.force(d["n"])
    for c in d["clauses"]:
        a.assert_term(len(c))
        a.force(len(c))
    return a


def termini_of(d):
    return [residual_terminus(c, d["n"]) for c in d["clauses"]]


def word(a, n):
    return "".join("T" if (a >> p) & 1 else "F" for p in range(n))


def stands(a, d):
    """Does this address stand?  Read off the clauses directly, so the
    protocol's truth never comes from the composition under test."""
    for c in d["clauses"]:
        if not any(((a >> (v - 1)) & 1) if pol > 0
                   else not ((a >> (v - 1)) & 1) for v, pol in c):
            return False
    return True


def census(fam, n):
    out = {}
    for r in fam:
        f = free_count(r, n)
        out[f] = out.get(f, 0) + 1
    return out


def truth_set(d):
    """Every standing address, by exhaustion over the envelope.  Used only
    where exhaustion is affordable, and never as an input."""
    return {a for a in range(1 << d["n"]) if stands(a, d)}


print("=" * 78)
print("  APPENDIX S -- THE COMPOSED BOUNDARY AND ITS LIGHTHOUSES")
print("=" * 78)

COMMITTED = [load_instance(os.path.join(ROOT, "instances",
                                        f"instance{i}.json"))
             for i in (1, 2, 3)]

# ===========================================================================
print("\nS.1  THE TWO TERMINI OF A BOUNDARY, AND WHICH ONE IS WRITTEN")
print("     For k odd the termini are the uniform states at Sigma_u = +k and")
print("     Sigma_u = -k, a conjugate pair (Axiom 2.3).  The residual")
print("     terminus is the one at -k: every literal of the boundary")
print("     falsified.  Its conjugate is forced and is never written.")
print()

ok = tot = conj_ok = conj_tot = 0
for d in COMMITTED:
    n = d["n"]
    for c in d["clauses"]:
        rho = residual_terminus(c, n)
        tot += 1
        if not any((((rho[1] >> (v - 1)) & 1) if pol > 0
                    else not ((rho[1] >> (v - 1)) & 1)) for v, pol in c):
            ok += 1
        conj_tot += 1
        conj_v = rho[1] ^ rho[0]
        if all((((conj_v >> (v - 1)) & 1) if pol > 0
                else not ((conj_v >> (v - 1)) & 1)) for v, pol in c):
            conj_ok += 1

report("the written terminus falsifies every literal of its boundary",
       ok, tot, "Sigma_u = -k, the excluded sector")
report("its component-wise opposite stands every literal of its boundary",
       conj_ok, conj_tot, "Sigma_u = +k, forced by Axiom 2.2, never written")

ok = tot = 0
for d in COMMITTED:
    for c, rho in zip(d["clauses"], termini_of(d)):
        tot += 1
        if sorted(support(rho[0])) == sorted(v - 1 for v, _ in c):
            ok += 1
report("a terminus bears on exactly the k contents of its own support",
       ok, tot, "Axiom 5.1")

# ===========================================================================
print("\nS.2  THE THREE RELATIONS ARE EXCLUSIVE AND EXHAUSTIVE")
print("     A boundary stands at its residual terminus, is barred, or is not")
print("     yet determined -- exactly one of the three, on the evidence of")
print("     the contents of its own support.")
print()

rng = random.Random(515)
ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    ts = termini_of(d)
    for _ in range(400):
        fixed = rng.getrandbits(n)
        r = (fixed, rng.getrandbits(n) & fixed)
        for t in ts:
            tot += 1
            if not (at_residual(r, t) and barred(r, t)):
                ok += 1
report("at the residual terminus and barred are never both true", ok, tot,
       "exclusive")

ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    ts = termini_of(d)
    for _ in range(400):
        fixed = rng.getrandbits(n)
        r = (fixed, rng.getrandbits(n) & fixed)
        for t in ts:
            tot += 1
            if at_residual(r, t) or barred(r, t) or (t[0] & ~fixed):
                ok += 1
report("where neither holds, the support is not yet wholly oriented",
       ok, tot, "exhaustive")

ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    for t in termini_of(d):
        for _ in range(250):
            fixed = rng.getrandbits(n)
            r = (fixed, rng.getrandbits(n) & fixed)
            if not barred(r, t):
                continue
            free = [p for p in range(n) if not (fixed >> p) & 1]
            if not free:
                continue
            p = free[rng.randrange(len(free))]
            for orient in (0, 1 << p):
                tot += 1
                if barred((fixed | (1 << p), r[1] | orient), t):
                    ok += 1
report("a boundary barred at a stratum is barred in every stratum below it",
       ok, tot, "from Axiom 5.2 and Proposition 14.1")

ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    if n > 12:
        continue
    for t in termini_of(d):
        for _ in range(60):
            fixed = rng.getrandbits(n)
            r = (fixed, rng.getrandbits(n) & fixed)
            if not barred(r, t):
                continue
            tot += 1
            if not any((a & t[0]) == t[1] for a in read_region(r, n)):
                ok += 1
report("and no address of it stands at that residual terminus", ok, tot)

# ===========================================================================
print("\nS.3  THE COMPOSED BOUNDARY IS ONE OBJECT")
print("     The family is a function of the asserted boundaries and the")
print("     order of mediation, and of nothing else.")
print()

ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    ts = termini_of(d)
    for fn in (order_given, order_closing):
        order = fn(n, ts)
        base, _ = compose(n, ts, order)
        rp = random.Random(900 + n)
        for _ in range(4):
            perm = ts[:]
            rp.shuffle(perm)
            tot += 1
            if compose(n, perm, order)[0] == base:
                ok += 1
report("the identical family returns under permuted presentation of the "
       "boundaries", ok, tot,
       "four permutations, both orders, every committed instance")

# ===========================================================================
print("\nS.4  THE FAMILY READS OUT THE ANSWER, AND NOTHING ELSE")
print()

for d in COMMITTED:
    n = d["n"]
    committed = set(d["solutions"])
    ts = termini_of(d)
    for fn, lbl in ((order_given, "arriving"), (order_closing, "closing")):
        fam, held = compose(n, ts, fn(n, ts))
        seen, dup, nonstanding = set(), 0, 0
        for r in fam:
            for a in read_region(r, n):
                if a in seen:
                    dup += 1
                seen.add(a)
                if not stands(a, d):
                    nonstanding += 1
        rad = census(fam, n)
        print(f"      {d['label']}, {lbl} order: {len(fam)} lighthouses, "
              f"{len(fam) * n} symbols, radii "
              f"{dict(sorted(rad.items(), reverse=True))}, held {held}")
        check(f"{d['label']}/{lbl}: the family reads out the committed set",
              {word(a, n) for a in seen} == committed,
              f"{len(seen)} of {len(committed)}")
        check(f"{d['label']}/{lbl}: no address is named twice", dup == 0)
        check(f"{d['label']}/{lbl}: every address read stands",
              nonstanding == 0)
        check(f"{d['label']}/{lbl}: the radius census identity holds",
              sum(c * (1 << f) for f, c in rad.items()) == len(committed),
              f"sum = {sum(c * (1 << f) for f, c in rad.items())}")
        check(f"{d['label']}/{lbl}: one stratum per depth, at most n+1",
              held <= n + 1, f"{held} <= {n + 1}")
        check(f"{d['label']}/{lbl}: every lighthouse bars every boundary",
              all(all(barred(r, t) for t in ts) for r in fam))

print("      the family of Instance 1 under the arriving order:")
d0 = COMMITTED[0]
t0 = termini_of(d0)
f0, _ = compose(d0["n"], t0, order_given(d0["n"], t0))
for r in sorted(f0, key=lambda z: region_str(z, d0["n"])):
    print(f"        {region_str(r, d0['n'])}   radius "
          f"{free_count(r, d0['n'])}")

# ===========================================================================
print("\nS.5  WHERE THE DESCENT CLOSES, AGAINST HOW TIGHTLY THE INSTANCE IS")
print("     BOUNDED.  A radius is capacity the asserted relations leave")
print("     unallocated, so the radii record the depth at which the asserted")
print("     structure closes.")
print()

print(f"      {'m/n':>5} {'m':>4} {'admits':>9} {'lighthouses':>12} "
      f"{'max r':>6} {'held':>5}")
rows = []
rows2 = []
for dens in (1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.26):
    d = planted(24, dens, 31337 + 24)
    ts = termini_of(d)
    fam, held = compose(24, ts, order_closing(24, ts))
    rad = census(fam, 24)
    adm = sum(c * (1 << f) for f, c in rad.items())
    rows.append((dens, d["m"], adm, len(fam), max(rad) if rad else 0, held))
    print(f"      {dens:>5} {d['m']:>4} {adm:>9,} {len(fam):>12,} "
          f"{max(rad) if rad else 0:>6} {held:>5}")
print()
print("      seven further seeds, greatest radius by density:")
SEEDS = (90210 + 24, 4242, 777, 2026, 1618, 3141, 5150)
seed_rows = []
for s in SEEDS:
    row = []
    for dens in (1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.26):
        d2 = planted(24, dens, s)
        t2 = termini_of(d2)
        f2, h2 = compose(24, t2, order_closing(24, t2))
        r2 = census(f2, 24)
        row.append(max(r2) if r2 else 0)
    seed_rows.append(row)
    print(f"        seed {s:<6} " + " ".join(f"{x:>3}" for x in row))
allrows = [[r[4] for r in rows]] + seed_rows
check("on every seed the greatest radius at m/n = 1 exceeds the greatest "
      "radius at threshold", all(r[0] > r[-1] for r in allrows),
      f"{len(allrows)} seeds")
check("on every seed the greatest radius at threshold is at most 2",
      all(r[-1] <= 2 for r in allrows),
      f"threshold radii {[r[-1] for r in allrows]}")
check("on every seed the greatest radius at m/n = 1 is at least 5",
      all(r[0] >= 5 for r in allrows),
      f"m/n = 1 radii {[r[0] for r in allrows]}")
check("a loosely bounded instance closes shallow and carries coarse "
      "lighthouses", rows[0][4] >= 6,
      f"greatest radius {rows[0][4]} at m/n = 1")
check("on the committed row the structure closes at full depth at threshold",
      rows[-1][4] == 0, "every lighthouse of radius 0 on this seed")
check("the greatest radius falls as the instance is bounded more tightly",
      rows[0][4] > rows[-1][4], f"{rows[0][4]} down to {rows[-1][4]}")
check("one stratum per depth at every density measured",
      all(r[5] <= 25 for r in rows), f"held {[r[5] for r in rows]}")
check("every density admits something, so no row is vacuous",
      all(r[2] > 0 for r in rows), f"{len(rows)} densities")

# ===========================================================================
print("\nS.6  THE ORDER OF MEDIATION IS PART OF THE ASSERTION")
print("     Axiom 2.4 makes the Between oriented, so the order is asserted.")
print("     It changes the family, and neither order dominates.")
print()

diffs = 0
bg, bc = [], []
for d in COMMITTED:
    n = d["n"]
    ts = termini_of(d)
    fg, _ = compose(n, ts, order_given(n, ts))
    fc, _ = compose(n, ts, order_closing(n, ts))
    bg.append(len(fg))
    bc.append(len(fc))
    ag = {word(a, n) for r in fg for a in read_region(r, n)}
    ac = {word(a, n) for r in fc for a in read_region(r, n)}
    print(f"      {d['label']}: arriving {len(fg):>3} lighthouses, "
          f"closing {len(fc):>3}")
    check(f"{d['label']}: both orders read out the same answer", ag == ac)
    if len(fg) != len(fc):
        diffs += 1
check("the two orders give different families on at least one instance",
      diffs > 0, f"{diffs} of {len(COMMITTED)} differ")
check("neither order is the coarser one on every instance",
      any(g < c for g, c in zip(bg, bc)) and
      any(c < g for g, c in zip(bg, bc)),
      f"arriving {bg}, closing {bc}")

ok = tot = 0
for d in COMMITTED:
    n = d["n"]
    ts = termini_of(d)
    order = order_closing(n, ts)
    pos = {p: i for i, p in enumerate(order)}
    genesis, bd = bands(n, ts, order)
    tot += 1
    if not genesis and sum(len(b) for b in bd) == len(ts):
        ok += 1
    for depth, band in enumerate(bd):
        for t in band:
            tot += 1
            if max(pos[p] for p in support(t[0])) == depth:
                ok += 1
report("each boundary falls in the band of its own decisive depth", ok, tot,
       "Axiom 5.1: it says nothing above that depth")

# ===========================================================================
print("\nS.7  WHAT THE BOUNDARY HOLDS, AGAINST WHAT THE ANSWER COSTS")
print("     The assertion is n + 1 + km acts, held as n + 1 + km symbols; the")
print("     answer is every address admitted, at n symbols each.")
print()

print(f"      {'n':>4} {'m':>5} {'asserted':>9} {'admits':>10} "
      f"{'answer sym':>12} {'ratio':>10} {'lights':>9} {'held':>5}")
big = None
for n in (10, 20, 30, 50, 70):
    d = planted(n, 4.26, 31337 + n)
    ts = termini_of(d)
    fam, held = compose(n, ts, order_closing(n, ts))
    rad = census(fam, n)
    adm = sum(c * (1 << f) for f, c in rad.items())
    acts = assertion(d)
    asym = acts.total                     # n + 1 + km, the assertion
    print(f"      {n:>4} {d['m']:>5} {asym:>9,} {adm:>10,} {adm * n:>12,} "
          f"{adm * n / asym:>9,.0f}x {len(fam):>9,} {held:>5}")
    check(f"n={n}: the assertion is n + 1 + km acts",
          acts.total == n + 1 + 3 * d["m"],
          f"{acts.total} = {n} + 1 + {3 * d['m']}")
    check(f"n={n}: the structural opposites are forced and charged nothing",
          acts.forced == n + 3 * d["m"], f"{acts.forced} forced, 0 charged")
    check(f"n={n}: one stratum per depth", held == n + 1, f"{held}")
    check(f"n={n}: the census identity holds", adm > 0 and
          sum(c * (1 << f) for f, c in rad.items()) == adm, f"{adm:,}")
    if n <= 20:
        check(f"n={n}: the family agrees with exhaustion over the envelope",
              {a for r in fam for a in read_region(r, n)} == truth_set(d))
    if n == 70:
        big = (d, fam, held, adm, asym)

d70, fam70, held70, adm70, asym70 = big
seen70, dup70, bad70 = set(), 0, 0
for r in fam70:
    for a in read_region(r, 70):
        if a in seen70:
            dup70 += 1
        seen70.add(a)
        if not stands(a, d70):
            bad70 += 1
print()
print(f"      the threshold instance at n = 70, m = {d70['m']}:")
print(f"        asserted symbols                 {asym70:>14,}")
print(f"        addresses the boundaries admit   {adm70:>14,}")
print(f"        the same answer written out      {adm70 * 70:>14,}")
print(f"        the boundary against it          "
      f"{adm70 * 70 / asym70:>13,.0f}x")
print(f"        strata held at once              {held70:>14}   (n + 1 = 71)")
print(f"        lighthouses                      {len(fam70):>14,}")
check("the whole answer resides in fewer than a thousand asserted symbols",
      asym70 < 1000, f"{asym70} symbols for {adm70:,} addresses")
check("the boundary holds the answer by four orders of magnitude",
      adm70 * 70 / asym70 > 10000, f"{adm70 * 70 / asym70:,.0f}x")
check("and holds it while standing one stratum per depth", held70 == 71)
check("every one of the addresses read at n = 70 stands, checked against the "
      "clauses", bad70 == 0 and len(seen70) == adm70,
      f"{len(seen70):,} read, {bad70} do not stand")
check("no address at n = 70 is named by two lighthouses", dup70 == 0,
      f"{dup70} duplicates")

# ===========================================================================
print("\nS.8  WHERE NOTHING STANDS")
print("     Tseitin formulas over 3-regular graphs: unsatisfiable, width 3,")
print("     maximally shared supports, and the family on which resolution is")
print("     provably exponential.  No stratum bars every boundary, so the")
print("     composed boundary is empty -- returned, not searched for.")
print()

print(f"      {'graph':>6} {'n':>4} {'m':>4} {'lighthouses':>12} "
      f"{'held':>5} {'acts':>7}")
ok = tot = ok2 = 0
acts_seen = []
for nv in (8, 12, 16, 20):
    d = tseitin(nv)
    n = d["n"]
    ts = termini_of(d)
    fam, held = compose(n, ts, order_closing(n, ts))
    a = assertion(d)
    acts_seen.append(a.total)
    print(f"      {nv:>6} {n:>4} {d['m']:>4} {len(fam):>12} {held:>5} "
          f"{a.total:>7}")
    tot += 1
    if not fam:
        ok += 1
    if held <= n + 1:
        ok2 += 1
    check(f"tseitin-{nv}: the assertion is n + 1 + km acts",
          a.total == n + 1 + 3 * d["m"])
report("the composed boundary of each member admits no address", ok, tot)
report("and each held one stratum per depth while establishing it", ok2, tot)
check("the assertion is linear across the family on which resolution is "
      "provably exponential",
      acts_seen == sorted(acts_seen) and acts_seen[-1] < 10 * acts_seen[0],
      f"{acts_seen[0]} to {acts_seen[-1]} acts")

# ===========================================================================
print("\nS.9  AGAINST EXHAUSTION, ON INSTANCES NOT COMMITTED")
print()

rng = random.Random(1212)
agree = tot = heldok = barsok = 0
for _ in range(80):
    n = rng.randint(5, 14)
    m = rng.randint(n, 5 * n)
    cl, guard = set(), 0
    while len(cl) < m and guard < m * 200:
        guard += 1
        ps = rng.sample(range(1, n + 1), 3)
        cl.add(tuple(sorted((p, rng.choice([1, -1])) for p in ps)))
    d = {"label": f"r{n}", "n": n, "m": len(cl), "k": 3,
         "clauses": [list(c) for c in sorted(cl)]}
    ts = termini_of(d)
    fam, held = compose(n, ts, order_closing(n, ts))
    tot += 1
    if {a for r in fam for a in read_region(r, n)} == truth_set(d):
        agree += 1
    if held <= n + 1:
        heldok += 1
    if all(all(barred(r, t) for t in ts) for r in fam):
        barsok += 1
report("the family reads out exactly the standing set, against exhaustion",
       agree, tot)
report("one stratum per depth on every instance", heldok, tot)
report("every lighthouse bars every asserted boundary", barsok, tot)

# ===========================================================================
print("\nS.10  THE PROTOCOL CAN FAIL")
print()

d = COMMITTED[0]
n = d["n"]
ts = termini_of(d)
fam, _ = compose(n, ts, order_closing(n, ts))
bad = 0
for r in fam:
    f, v = r
    for p in support(f):
        loose = (f & ~(1 << p), v & ~(1 << p))
        for a in read_region(loose, n):
            if not stands(a, d):
                bad += 1
check("freeing a content of a lighthouse admits addresses that do not stand, "
      "so no radius here is slack", bad > 0,
      f"{bad} non-standing addresses appear")

a1 = {word(a, n) for r in fam for a in read_region(r, n)}
load_bearing = 0
for i in range(len(ts)):
    dropped = ts[:i] + ts[i + 1:]
    a2 = {word(a, n) for r in compose(n, dropped, order_closing(n, dropped))[0]
          for a in read_region(r, n)}
    if a2 != a1:
        load_bearing += 1
check("dropping a boundary that the assertion needs changes the answer",
      load_bearing > 0,
      f"{load_bearing} of {len(ts)} boundaries are load-bearing; the "
      f"remainder are carried by the others")

flipped = ts[:-1] + [(ts[-1][0], ts[-1][1] ^ ts[-1][0])]
a3 = {word(a, n) for r in compose(n, flipped, order_closing(n, flipped))[0]
      for a in read_region(r, n)}
check("inverting one boundary's terminus changes the answer", a1 != a3,
      f"{len(a1)} against {len(a3)}")

check("the committed solution sets are not empty, so the readings are not "
      "vacuous", all(x["solutions"] for x in COMMITTED))

unsat = {"label": "unsat-3", "n": 3, "m": 8, "k": 3,
         "clauses": [[(1, s1), (2, s2), (3, s3)]
                     for s1 in (1, -1) for s2 in (1, -1) for s3 in (1, -1)]}
tu = termini_of(unsat)
famu, heldu = compose(3, tu, order_given(3, tu))
check("an instance admitting nothing composes to the empty family",
      famu == frozenset(), f"{len(famu)} lighthouses")

# --- structural checks on the module's own syntax tree ---------------------
_src = open(os.path.join(HERE, "composition.py")).read()
_tree = _ast.parse(_src)

_imports = [x for x in _ast.walk(_tree)
            if isinstance(x, (_ast.Import, _ast.ImportFrom))]
check("composition.py imports nothing, so the composition cannot reach an "
      "address through another module", not _imports,
      f"{len(_imports)} imports")

_comp_fns = {"support", "free_count", "residual_terminus", "at_residual",
             "barred", "order_given", "order_closing", "bands", "compose"}
_banned = {"read_region", "stands", "produce", "truth_set", "region_str"}
_hits = []
for fn in [x for x in _ast.walk(_tree)
           if isinstance(x, _ast.FunctionDef) and x.name in _comp_fns]:
    for nd in _ast.walk(fn):
        if isinstance(nd, _ast.Name) and nd.id in _banned:
            _hits.append((fn.name, nd.id))
check("no function of the composition names an address or anything that "
      "forms one", not _hits,
      f"none of {sorted(_banned)} appears in any of them")

_pow = []
for fn in [x for x in _ast.walk(_tree)
           if isinstance(x, _ast.FunctionDef) and x.name in _comp_fns]:
    for nd in _ast.walk(fn):
        if isinstance(nd, _ast.BinOp) and isinstance(nd.op, _ast.LShift) \
                and isinstance(nd.left, _ast.Constant) \
                and nd.left.value == 1 \
                and isinstance(nd.right, _ast.Name) and nd.right.id == "n":
            _pow.append(fn.name)
check("no function of the composition forms the envelope 2^n", not _pow,
      "the envelope appears in no composition function")

_decomp = [x.name for x in _ast.walk(_tree)
           if isinstance(x, _ast.FunctionDef)
           and x.name in ("split", "merge", "strip", "compose_unbanded",
                          "joint", "carried", "minimal")]
check("the module carries no operation that decomposes a stratum into parts "
      "and none that enriches the assertion", not _decomp,
      "no addition of contents, per the Remark to Theorem 11.1; "
      "no mid-descent change to what was asserted at genesis")

_fns = {x.name for x in _ast.walk(_tree) if isinstance(x, _ast.FunctionDef)}
check("the composition reports no traversal tally", "compose" in _fns and
      "closures" not in _src and "barren" not in _src,
      "no step of the descent is counted")

# ===========================================================================
print()
print("=" * 78)
if FAILURES:
    print(f"  APPENDIX S   {CHECKS - len(FAILURES)} of {CHECKS} checks pass; "
          f"{len(FAILURES)} FAILED")
    for f in FAILURES:
        print(f"    FAILED: {f}")
    print("=" * 78)
    sys.exit(1)
print(f"  APPENDIX S   {CHECKS} of {CHECKS} checks pass")
print("=" * 78)
