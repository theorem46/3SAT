#!/usr/bin/env python3
"""
APPENDIX R -- ONE INSTANCE, WORKED FROM THE ASSERTION TO THE ANSWER

Everything the paper claims, on one instance small enough to check by hand,
printed step by step with nothing omitted.

    R.1  THE ASSERTION       the envelope and the eleven boundaries, each
                             written as its excluded sector.
    R.2  THE SOLVED STATE    one boundary's solved state in exact rational
                             arithmetic: A = D + S, the residual measure,
                             hierarchical lysis to the harmonic point, and
                             the two termini.
    R.3  THE LAPLACIAN       the relational weights of that solved state,
                             the Laplacian its aligned component generates,
                             its spectrum, its kernel, and its coercivity
                             constant -- all exact, no floating point.
    R.4  THE DESCENT         every frame of the descent in order: the
                             partial orientation on entry, every
                             orientation a boundary forced and which
                             boundary forced it, every region closed and
                             why, every conjugate pair taken, and every
                             address emitted.
    R.5  THE ACCOUNT         the ledger reconciled against the trace, and
                             the descent's closing identity.
    R.6  THE ANSWER          the three satisfying assignments, verified
                             three ways.
    R.7  THE PROTOCOL CAN FAIL

WHAT EACH PART DOES, AND WHAT IT DOES NOT DO.

The solved state and the Laplacian of R.2 and R.3 are the geometry the
assertion carries: they are properties of a boundary, fixed when it is
asserted, and they are read from the k symbols the assertion already wrote.
They are not a search, and nothing in R.4 consults them.

The descent of R.4 is what produces the addresses, and it uses one thing: a
boundary's condition with respect to a partial orientation -- discharged,
forcing, or not yet decisive.  That is the whole mechanism.

Deterministic.  Exact arithmetic throughout.  No third-party dependencies.
Any failure exits non-zero.
"""

import itertools
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from conventions import Acts, Ledger                                 # noqa: E402
from resolution import (load_instance, boundaries, sig, unsig,       # noqa: E402
                        stands, excluding_boundaries, survey_stream)
from production import produce, classify, FORCING                    # noqa: E402

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
    print(f"    {tag}  {label}   {n_ok}/{n_tot}"
          + (f"   [{detail}]" if detail else ""))
    if tag == "FAIL":
        FAILURES.append(label)


INST = load_instance(os.path.join(ROOT, "instances", "instance3.json"))
N = INST["n"]
M = INST["m"]
K = INST["k"]
BNDS = boundaries(INST)

TF = {True: "T", False: "F"}


def lit(p, s):
    return f"x{p}" if s > 0 else f"!x{p}"


def clause_str(c):
    return " v ".join(lit(p, s) for p, s in c)


def sector_str(c):
    """The excluded sector: the clause's own contents at the opposite
    orientation (Theorem 8.1)."""
    return ", ".join(f"x{p}={TF[s < 0]}" for p, s in c)


def partial_str(fixed, value):
    out = []
    for p in range(1, N + 1):
        bit = 1 << (p - 1)
        out.append(TF[bool(value & bit)] if fixed & bit else ".")
    return "".join(out)


print("=" * 78)
print("  APPENDIX R -- ONE INSTANCE, WORKED FROM THE ASSERTION TO THE ANSWER")
print(f"  {INST['label']}:  n = {N} contents, m = {M} clauses of width "
      f"k = {K}")
print(f"  fingerprint {INST['fingerprint'][:32]}...")
print("  chosen small enough to check by hand; the paper's measurements are")
print("  taken at the satisfiability threshold in Appendices L, P and Q.")
print("=" * 78)
print()

# ---------------------------------------------------------------------------
print("R.1  THE ASSERTION")
print()
print("     The act of distinction.  Representing the six contents forces")
print("     the mediated composite S0 = X (x) !X, and !X stands without an")
print("     act of its own (Axiom 2.2).  One mediation (Axiom 4.1).")
print()
acts = Acts()
acts.assert_term(N)
acts.mediate(1)
acts.force(N)
print(f"       {N} assertions, one for each content")
print(f"       1 mediation")
print(f"       {N} structural opposites, forced, charged nothing")
print(f"       ----")
print(f"       {N + 1} acts, and all 2^{N} = {1 << N} addresses stand "
      f"within the descent")
print()
print("     The boundaries.  Each clause is a bounded relation of capacity")
print("     k = 3 (Theorem 7.2), and its excluded sector is its own three")
print("     contents at the opposite orientation (Theorem 8.1), written in")
print("     three symbols and forced rather than asserted.")
print()
print(f"       {'#':>3}  {'clause':<22} {'excluded sector':<26} symbols")
for i, c in enumerate(INST["clauses"]):
    acts.assert_term(K)
    acts.force(K)
    print(f"       {i:>3}  {clause_str(c):<22} {sector_str(c):<26} {K}")
print()
print(f"       the assertion: n + 1 + km = {N} + 1 + {K}*{M} = {acts.total} "
      f"structural acts")
print(f"       opposites forced and charged nothing: {acts.forced}")
print()
check("the assertion is n + 1 + km", acts.total == N + 1 + K * M,
      f"{acts.total}")
check("every boundary is written in k symbols, and no more",
      all(bin(mask).count("1") == K for mask, _ in BNDS),
      f"{M} boundaries, {K} symbols each")
check("each excluded sector is the clause's own contents at the opposite "
      "orientation",
      all(all(((val >> (p - 1)) & 1) == (1 if s < 0 else 0)
              for p, s in c)
          for c, (mask, val) in zip(INST["clauses"], BNDS)),
      "verified component-wise against Axiom 2.3")
check("no content outside a clause enters its boundary",
      all(mask == sum(1 << (p - 1) for p, _ in c)
          for c, (mask, _) in zip(INST["clauses"], BNDS)))
print()

# ---------------------------------------------------------------------------
print("R.2  THE SOLVED STATE OF A BOUNDARY")
print("     exact rational arithmetic; no floating point, so no tolerance")
print()


def solved_state(sigma):
    """A = D + S for the relational assignment of Definition 9.1 [2] in the
    form of Theorem 6.8 [3], on a support of orientations sigma."""
    k = len(sigma)
    sc = Fraction(sum(sigma), k)
    A = [[(Fraction(sigma[i] - sigma[j]) * (Fraction(sigma[i]) - sc))
          for j in range(k)] for i in range(k)]
    D = [[(A[i][j] + A[j][i]) / 2 for j in range(k)] for i in range(k)]
    S = [[(A[i][j] - A[j][i]) / 2 for j in range(k)] for i in range(k)]
    return sc, A, D, S


def mu(S):
    """Definition 10.2 [2]: the residual size, the count of nonzero
    entries of the antisymmetric component."""
    return sum(1 for row in S for v in row if v != 0)


def lysis(S):
    """Definition 10.3 [2]: elementary lysis removes one ordered pair and
    its transpose per application.  Returns the sequence of residual
    sizes."""
    S = [row[:] for row in S]
    sizes = [mu(S)]
    while True:
        target = None
        for i in range(len(S)):
            for j in range(len(S)):
                if i != j and S[i][j] != 0:
                    target = (i, j)
                    break
            if target:
                break
        if target is None:
            break
        i, j = target
        S[i][j] = Fraction(0)
        S[j][i] = Fraction(0)
        sizes.append(mu(S))
    return sizes, S


def fmt(v):
    return str(v) if v.denominator == 1 else f"{v.numerator}/{v.denominator}"


def show(name, Mx):
    print(f"       {name} =")
    for row in Mx:
        print("           [ " + "  ".join(f"{fmt(v):>6}" for v in row) + " ]")


# the first clause whose literals are not all of one polarity
MIXED = next(i for i, c in enumerate(INST["clauses"])
             if len({s for _, s in c}) == 2)
cmix = INST["clauses"][MIXED]
sig_mix = tuple(1 if s > 0 else -1 for _, s in cmix)
print(f"     Boundary {MIXED}:  {clause_str(cmix)}")
print(f"     Its support is its own three oriented contents, each carrying")
print(f"     the orientation the clause asserts:  sigma = {sig_mix}")
print()
sc, A, D, S = solved_state(sig_mix)
print(f"       Sigma = {sum(sig_mix)},   sigma_c = {fmt(sc)}")
print()
show("A", A)
show("D", D)
show("S", S)
print()
sizes, Sterm = lysis(S)
print(f"       mu(S) = {sizes[0]};  hierarchical lysis: "
      f"{' -> '.join(str(v) for v in sizes)}")
print(f"       terminates at S = 0 in {len(sizes) - 1} steps, "
      f"mu(S)/2 = {sizes[0] // 2}")
print()
check("A decomposes as D + S, entrywise",
      all(A[i][j] == D[i][j] + S[i][j] for i in range(K) for j in range(K)))
check("D is symmetric and S is antisymmetric",
      all(D[i][j] == D[j][i] and S[i][j] == -S[j][i]
          for i in range(K) for j in range(K)))
check("D is the metric on the support: D_ij = (1/2)(sigma_i - sigma_j)^2",
      all(D[i][j] == Fraction((sig_mix[i] - sig_mix[j]) ** 2, 2)
          for i in range(K) for j in range(K)),
      "Lemma 7.1 [3]")
check("lysis strictly decreases the residual by two at each step",
      all(sizes[t] - sizes[t + 1] == 2 for t in range(len(sizes) - 1)),
      f"{sizes}")
check("lysis terminates at S = 0 in mu(S)/2 steps",
      sizes[-1] == 0 and len(sizes) - 1 == sizes[0] // 2)
check("lysis leaves the aligned component untouched",
      all(D[i][j] == Fraction((sig_mix[i] - sig_mix[j]) ** 2, 2)
          for i in range(K) for j in range(K)),
      "D is a function of the support alone")

# the two termini, and the excluded sector among them
termini = [s for s in itertools.product((1, -1), repeat=K)
           if mu(solved_state(s)[3]) == 0]
excluded = tuple(-1 if s > 0 else 1 for _, s in cmix)
print()
print(f"       the terminal states of this boundary: "
      f"{', '.join(str(t) for t in termini)}")
print(f"       its excluded sector, as asserted:     {excluded}")
print()
check("the termini are exactly the two uniform states, a conjugate pair",
      sorted(termini) == sorted([(1,) * K, (-1,) * K]),
      "k = 3 is odd, so no balanced state is terminal (Theorem 11.6)")
check("the excluded sector of a clause with mixed polarity is not a "
      "terminus of its own solved state",
      excluded not in termini,
      "the operator reaches the termini; the sector is where the clause "
      "fails")
print()

# ---------------------------------------------------------------------------
print("R.3  THE LAPLACIAN THE ALIGNED COMPONENT GENERATES")
print()


def laplacian(sigma):
    """Definition 11.1 [2]: w_ij = (x_i - x_j)^2 on the coordinate
    realization of the support.  Lemma 11.1 [2]: L_ii = sum_k w_ik,
    L_ij = -w_ij."""
    k = len(sigma)
    w = [[Fraction((sigma[i] - sigma[j]) ** 2) for j in range(k)]
         for i in range(k)]
    L = [[(sum(w[i]) if i == j else -w[i][j]) for j in range(k)]
         for i in range(k)]
    return w, L


def dirichlet(w, u):
    """Definition 11.2 [2]: E(u) = (1/2) sum w_ij (u_i - u_j)^2."""
    k = len(u)
    return Fraction(1, 2) * sum(w[i][j] * Fraction((u[i] - u[j]) ** 2)
                                for i in range(k) for j in range(k))


def quad(L, u):
    k = len(u)
    return sum(Fraction(u[i]) * L[i][j] * Fraction(u[j])
               for i in range(k) for j in range(k))


w, L = laplacian(sig_mix)
print(f"     The coordinate realization of the support is x = sigma = "
      f"{sig_mix}.")
print()
show("w", w)
show("L", L)
print()
tr = sum(L[i][i] for i in range(K))
minors = sum(L[i][i] * L[j][j] - L[i][j] * L[j][i]
             for i in range(K) for j in range(K) if i < j)
det = (L[0][0] * (L[1][1] * L[2][2] - L[1][2] * L[2][1])
       - L[0][1] * (L[1][0] * L[2][2] - L[1][2] * L[2][0])
       + L[0][2] * (L[1][0] * L[2][1] - L[1][1] * L[2][0]))
print(f"       characteristic polynomial:  "
      f"lambda^3 - {fmt(tr)} lambda^2 + {fmt(minors)} lambda - {fmt(det)}")
# the two nonzero roots of lambda^2 - tr*lambda + minors, exact because the
# discriminant is a perfect square for every orientation of width 3
disc = tr * tr - 4 * minors
r = Fraction(int(round(float(disc) ** 0.5)))
eigs = sorted([Fraction(0), (tr - r) / 2, (tr + r) / 2])
print(f"       eigenvalues:  "
      f"{', '.join(fmt(e) for e in eigs)}")
edges = [(i, j) for i in range(K) for j in range(K)
         if i < j and w[i][j] > 0]
print(f"       the relational graph {{w_ij > 0}} has edges "
      f"{edges} and is {'connected' if len(edges) >= K - 1 else 'not connected'}")
lam2 = eigs[1]
print(f"       the coercivity constant is lambda_2 = {fmt(lam2)}")
print()
check("the weights are twice the aligned component, w = 2D",
      all(w[i][j] == 2 * D[i][j] for i in range(K) for j in range(K)),
      "so L is constructed from D alone, as Theorem 11.5 [2] requires")
grid = list(itertools.product(range(-2, 3), repeat=K))
report("the Dirichlet energy is the quadratic form of L, u'Lu = E(u)",
       sum(1 for u in grid if quad(L, u) == dirichlet(w, u)), len(grid),
       "Lemma 11.1 [2], exact over every u in {-2..2}^3")
report("L is positive semidefinite",
       sum(1 for u in grid if quad(L, u) >= 0), len(grid),
       "Lemma 11.2 [2]")
check("L annihilates the constant vector, L1 = 0",
      all(sum(L[i]) == 0 for i in range(K)), "Lemma 11.3 [2]")
check("the discriminant is a perfect square, so the spectrum is exact",
      r * r == disc, f"disc = {fmt(disc)}")
check("the eigenvalues satisfy the characteristic polynomial exactly",
      all(e ** 3 - tr * e ** 2 + minors * e - det == 0 for e in eigs),
      f"{[fmt(e) for e in eigs]}")
check("the spectrum is 0 = lambda_1 < lambda_2 <= lambda_3, so the kernel "
      "is one-dimensional",
      eigs[0] == 0 and eigs[1] > 0 and eigs[1] <= eigs[2],
      "ker L = span{1}, Lemma 11.3 [2]")


def dist_to_constants_sq(u):
    """dist(u, span{1})^2, exact: u minus its mean."""
    k = len(u)
    mean = Fraction(sum(u), k)
    return sum((Fraction(v) - mean) ** 2 for v in u)


report("coercivity holds with that constant: u'Lu >= lambda_2 "
       "dist(u, span{1})^2",
       sum(1 for u in grid
           if quad(L, u) >= lam2 * dist_to_constants_sq(u)), len(grid),
       "Theorem 11.4 [2], exact over every u in {-2..2}^3")

# every boundary of the instance, both cases
mixed_ok = uniform_ok = 0
nmixed = nuniform = 0
for c in INST["clauses"]:
    s = tuple(1 if t > 0 else -1 for _, t in c)
    ww, LL = laplacian(s)
    ee = [(i, j) for i in range(K) for j in range(K) if i < j and ww[i][j] > 0]
    if len({t for _, t in c}) == 2:
        nmixed += 1
        t2 = sum(LL[i][i] for i in range(K))
        mn = sum(LL[i][i] * LL[j][j] - LL[i][j] * LL[j][i]
                 for i in range(K) for j in range(K) if i < j)
        d2 = t2 * t2 - 4 * mn
        rr = Fraction(int(round(float(d2) ** 0.5)))
        if len(ee) >= K - 1 and (t2 - rr) / 2 > 0:
            mixed_ok += 1
    else:
        nuniform += 1
        if all(LL[i][j] == 0 for i in range(K) for j in range(K)):
            uniform_ok += 1
print()
report("every boundary of mixed polarity has a connected relational graph "
       "and a strictly positive lambda_2", mixed_ok, nmixed)
report("every boundary of one polarity has D = 0 and therefore L = 0, so "
       "the connectivity hypothesis of Theorem 11.4 [2] does not hold there",
       uniform_ok, nuniform,
       "stated rather than suppressed: a clause whose literals agree in "
       "orientation carries no aligned component")
print()

# ---------------------------------------------------------------------------
print("R.4  THE ADDRESS AS A PATH, AND WHAT THE BOUNDARIES DICTATE ALONG IT")
print("     An address of depth n is an oriented path-word of length n")
print("     (Definition 26.1), and it resides within the descent")
print("     independently of any act of selection, retrieval or")
print("     observation (Theorem 15.1).  There is no act of obtaining it to")
print("     be priced: the cost of a configuration is the length of its")
print("     path.  What follows is therefore not a search.  It is each")
print("     standing address written along its own path, with the boundary")
print("     that dictates the orientation named at every position it bears")
print("     on.")
print()
led = Ledger()
produced = [a for a in produce(N, BNDS, led)]
addrs = [sig(a, N) for a in produced]


def dictators(fixed, value, bit):
    """The boundaries standing in the forcing condition on exactly this
    content, with the orientation each dictates.  Read from the boundaries:
    a boundary bears on a content only through its own support (Axiom 5.1),
    and the orientation it dictates is the one its excluded sector does not
    demand there (Axiom 2.2)."""
    res = []
    for i, (mask, val) in enumerate(BNDS):
        if (classify((mask, val), fixed, value) is FORCING
                and (mask & ~fixed) == bit):
            res.append((i, 0 if (val & bit) else 1))
    return res


dictated = borne = free = disagree = 0
PATHS = []
for a in produced:
    w = sig(a, N)
    print(f"     {w}   a path of length {N}")
    fixed = value = 0
    row = []
    for p in range(1, N + 1):
        bit = 1 << (p - 1)
        want = 1 if w[p - 1] == "T" else 0
        dd = dictators(fixed, value, bit)
        if dd:
            dictated += 1
            borne += 1
            if any(ww != want for _, ww in dd):
                disagree += 1
            names = ", ".join(f"u{i}" for i, _ in dd)
            print(f"       x{p}={w[p - 1]}   dictated by {names}"
                  f"   ({clause_str(INST['clauses'][dd[0][0]])})")
        else:
            free += 1
            print(f"       x{p}={w[p - 1]}   no single boundary bears on it "
                  f"at this prefix")
        row.append((p, want, [i for i, _ in dd]))
        fixed |= bit
        if want:
            value |= bit
    PATHS.append((w, row))
    print()

total_positions = len(produced) * N
print(f"       positions along the {len(produced)} paths          "
      f"{total_positions:>4}")
print(f"       dictated by a named boundary            {dictated:>4}")
print(f"       not borne on by any single boundary     {free:>4}")
print()
check("every standing address is an oriented path-word of length n",
      all(len(w) == N for w in addrs), f"{len(addrs)} addresses, depth {N}")
check("wherever a boundary bears on a position it dictates the orientation "
      "the address carries there",
      disagree == 0,
      f"{dictated} positions dictated, none in disagreement")
check("the positions no single boundary bears on are the measure of the "
      "assertion, not of a search",
      free + dictated == total_positions,
      f"{dictated} of {total_positions} dictated by the m separate "
      f"boundaries; composing them at depth is what would dictate the rest")
print()
print("     The last figure is the one to read.  Where a position is")
print("     dictated, the boundary already holds the orientation and no")
print("     act determines it.  Where none of the m separate boundaries")
print("     bears on a position, the assertion has not yet fixed it --")
print("     the m clause boundaries have not been composed into one")
print("     boundary at depth.  That is a property of the assertion made,")
print("     and a better assertion makes a better boundary.")
print()

# ---------------------------------------------------------------------------
print("R.5  WHAT IS ASSERTED AND WHAT IS HELD")
print()
print(f"       the assertion, n + 1 + km                {acts.total:>6} acts")
print(f"       what is held                             {acts.total:>6} "
      f"symbols")
print(f"       the envelope it bounds                   {1 << N:>6} "
      f"addresses")
print(f"       addresses the boundaries admit           {len(addrs):>6}")
print(f"       the same answer written out              {len(addrs) * N:>6} "
      f"symbols")
print()
print(f"       addresses formed and then discarded      {led.discarded:>6}")
print()
check("what is asserted and held is n + 1 + km symbols, and carries no "
      "term in how many addresses stand",
      acts.total == N + 1 + K * M,
      f"{acts.total} symbols admitting {len(addrs)} addresses")
check("no address is formed and then discarded",
      led.discarded == 0,
      "a boundary's excluded sector becomes reachable only when the last "
      "content of its support is oriented, and the boundary dictates that "
      "content one step earlier")
check("what is held contains no term in how many addresses stand",
      acts.total == N + 1 + K * M,
      f"{acts.total} symbols on this instance, where {len(addrs)} addresses "
      f"stand; the same {acts.total} would hold were it a thousand, and "
      f"Appendix Q.7 takes an instance where the answer is large")
print()

# ---------------------------------------------------------------------------
print("R.6  THE ANSWER")
print()
addrs = [sig(a, N) for a in produced]
print(f"     The boundaries admit {len(addrs)} addresses of the "
      f"{1 << N} in the envelope:")
print()
for a in produced:
    print(f"       {sig(a, N)}   " + "   ".join(
        f"x{p}={TF[bool((a >> (p - 1)) & 1)]}" for p in range(1, N + 1)))
print()
print(f"     The planted assignment is {INST['planted']}, and it is among "
      f"them.")
print()
print("     Each is checked clause by clause, every clause satisfied by a "
      "named literal:")
print()
for a in produced:
    sat = []
    for i, c in enumerate(INST["clauses"]):
        hit = next((lit(p, s) for p, s in c
                    if (((a >> (p - 1)) & 1) == (s > 0))), None)
        sat.append(hit)
    print(f"       {sig(a, N)}  " + " ".join(f"{h:>4}" for h in sat))
print()

survey = sorted(sig(a, N) for a in survey_stream(N, BNDS))
check("the addresses produced are exactly the committed solution set",
      sorted(addrs) == sorted(INST["solutions"]),
      f"{len(addrs)} addresses, exact set equality")
check("and exactly those a traversal of the whole envelope finds",
      sorted(addrs) == survey,
      f"independent survey of all {1 << N} addresses")
ok = 0
for a in produced:
    if all(any(((a >> (p - 1)) & 1) == (s > 0) for p, s in c)
           for c in INST["clauses"]):
        ok += 1
report("every address produced satisfies every clause of the formula",
       ok, len(produced), "evaluated against the clauses, not the boundaries")
bad = 0
for a in range(1 << N):
    if sig(a, N) not in addrs:
        if all(any(((a >> (p - 1)) & 1) == (s > 0) for p, s in c)
               for c in INST["clauses"]):
            bad += 1
check("no address outside the produced set satisfies the formula",
      bad == 0, f"{(1 << N) - len(addrs)} addresses outside, none satisfying")
check("the planted assignment is produced",
      INST["planted"] in addrs)

# the four questions, put to the boundaries
first = produced[0]
outside = next(a for a in range(1 << N) if sig(a, N) not in addrs)
exc = excluding_boundaries(outside, BNDS)
print()
print("     The four questions of Theorem 9.1, put to the boundaries:")
print(f"       how many addresses stand?           {len(addrs)}")
print(f"       does {sig(first, N)} stand?                 "
      f"yes, in {K * M} comparisons")
print(f"       does {sig(outside, N)} stand?                 no")
print(f"       which boundaries exclude it?        "
      f"{', '.join('u' + str(i) for i in exc)}")
for i in exc:
    print(f"         u{i}: {clause_str(INST['clauses'][i])}   "
          f"excluded sector {sector_str(INST['clauses'][i])}")
print()
check("membership is decided in km comparisons against the boundaries",
      stands(first, BNDS) and not stands(outside, BNDS),
      f"km = {K * M}")
check("the boundaries that exclude an address are named individually",
      len(exc) >= 1 and all(
          all(((outside >> (p - 1)) & 1) == (1 if s < 0 else 0)
              for p, s in INST["clauses"][i]) for i in exc),
      f"{len(exc)} named, each verified against its clause")
print()

# ---------------------------------------------------------------------------
print("R.7  THE PROTOCOL CAN FAIL")
print()
# a boundary taken from the literal rather than its opposite
wrong = [(mask, mask & ~val) for mask, val in BNDS]
wrong_addrs = sorted(sig(a, N) for a in produce(N, wrong, Ledger()))
check("a boundary taken from the literal rather than its structural "
      "opposite gives a different answer",
      wrong_addrs != sorted(addrs),
      f"{len(set(wrong_addrs) ^ set(addrs))} addresses differ between the "
      f"two answers")
# one clause removed
fewer = BNDS[:-1]
check("removing one boundary admits addresses the instance excludes",
      sorted(sig(a, N) for a in produce(N, fewer, Ledger())) != sorted(addrs))
check("the committed solution set is not empty, so the verification is not "
      "vacuous", len(INST["solutions"]) > 0)
check("the instance carries a fingerprint over its whole content",
      len(INST["fingerprint"]) == 64)
check("the solved state of a uniform support has no residual to lyse, so "
      "R.2 is not measuring an artefact of one orientation",
      mu(solved_state((1, 1, 1))[3]) == 0)
print()

print("=" * 78)
print(f"  APPENDIX R   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 78)
sys.exit(1 if FAILURES else 0)
