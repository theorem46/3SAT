"""Shared body for Appendices D and E -- the resolution of one instance.

The resolution is production: the boundaries are asserted, and the standing
addresses are produced from them.  That is what step .2 does.

Steps .3 and .4 are VERIFICATION, and they are exhaustive on purpose.  They
traverse the whole envelope in order to check the resolution against a
complete truth table rather than against a sample.  A traversal performed to
verify a result is not a cost of producing it, and no figure from steps .3
or .4 is reported as a cost of any method.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT); sys.path.insert(0, HERE)
from conventions import Acts, Ledger                             # noqa: E402
from resolution import (load_instance, boundaries, assertion_cost,  # noqa: E402
                        sig, stands, excluding_boundaries, survey_stream)
from production import produce                                   # noqa: E402


def run(fname, appendix, label):
    failures = []
    checks = [0]

    def check(lbl, cond, detail=""):
        checks[0] += 1
        tag = "PASS" if cond else "FAIL"
        print(f"    {tag}  {lbl}" + (f"   [{detail}]" if detail else ""))
        if not cond:
            failures.append(lbl)

    d = load_instance(os.path.join(ROOT, "instances", fname))
    n, m, k = d["n"], d["m"], d["k"]

    print("=" * 74)
    print(f"  APPENDIX {appendix} -- THE RESOLUTION, {label.upper()}")
    print(f"  validates Theorem 4 (the resolution) on n = {n}, m = {m}, k = {k}")
    print("=" * 74)
    print()

    # ---- the assertion -------------------------------------------------
    print(f"{appendix}.1  THE ASSERTION")
    a = Acts()
    a.assert_term(n); a.mediate(1); a.force(n)          # the envelope
    bnds = boundaries(d)
    for c in d["clauses"]:
        a.assert_term(len(c)); a.force(len(c))          # Thm 7.2, Axiom 2.2
    print(f"      envelope      {n} assertions + 1 mediation = {n + 1}")
    print(f"      boundaries    {k} x {m} = {k * m}")
    print(f"      forced        {a.forced} opposites, charged 0 (Axiom 2.2)")
    print(f"      stored        {a.total} symbols; the envelope holds "
          f"{1 << n} addresses")
    print()
    check(f"acts = {a.total} = n + 1 + km", a.total == assertion_cost(d),
          f"expected {assertion_cost(d)}")
    check(f"boundaries asserted = {len(bnds)} = m", len(bnds) == m)
    check(f"every boundary carries exactly k = {k} symbols",
          all(bin(mk).count("1") == k for mk, _ in bnds))
    print()

    # ---- the resolution ------------------------------------------------
    print(f"{appendix}.2  THE RESOLUTION -- PRODUCED FROM THE BOUNDARIES")
    print("      no address is formed in order to be refused.  The ledger's")
    print("      `discarded` figure is the measurement of that.")
    print()
    led = Ledger()
    produced = [a_ for a_ in produce(n, bnds, led)]
    words = [sig(a_, n) for a_ in produced]
    print(f"      addresses standing: {len(produced)}")
    for w in sorted(words):
        print(f"        {w}")
    print()
    print(f"      produced      {led.emitted}")
    print(f"      discarded     {led.discarded}")
    print(f"      forced        {led.forced} orientations, charged 0 (Axiom 2.2)")
    print(f"      chosen        {led.chosen} orientations")
    print(f"      consultations {led.consultations} boundary reads")
    print(f"      deepest held  {led.max_depth} partial orientations")
    print()
    check(f"nothing formed and discarded: {led.discarded}",
          led.discarded == 0,
          "discarding is the signature of search")
    check(f"addresses formed ({led.emitted}) = addresses standing "
          f"({len(produced)})",
          led.emitted == len(produced) and led.emitted > 0)
    check(f"the held state is bounded by n: {led.max_depth} <= {n}",
          led.max_depth <= n)
    print()

    # ---- verification against the committed solution set ---------------
    print(f"{appendix}.3  VERIFICATION AGAINST THE COMMITTED SOLUTION SET")
    print("      the solution set ships with the instance and is computed")
    print("      independently of this resolution.  Exact set equality is")
    print("      required: one address wrong fails the run.")
    print()
    committed = set(d["solutions"])
    got = set(words)
    check("exact set equality with the committed solution set", got == committed,
          f"got {len(got)}, committed {len(committed)}, "
          f"symmetric difference {len(got ^ committed)}")
    check(f"the planted solution {d['planted']} is produced",
          d["planted"] in got)
    check("no produced address is excluded by any boundary",
          all(excluding_boundaries(a_, bnds) == [] for a_ in produced))
    print()

    # ---- adversarial ---------------------------------------------------
    print(f"{appendix}.4  ADVERSARIAL -- THE COMPLETE TRUTH TABLE")
    print("      a VERIFICATION survey, charged to no measure: each of the")
    print("      2^n addresses is resolved against the boundaries and against")
    print("      an independent clause evaluation, and the two verdicts must")
    print("      agree on every address.  The production of .2 is then")
    print("      required to equal the survey exactly.")
    print()
    agree = 0
    for a_ in range(1 << n):
        by_boundary = stands(a_, bnds)
        by_clause = all(any(((a_ >> (p - 1)) & 1) == (lit > 0) for p, lit in c)
                        for c in d["clauses"])
        if by_boundary == by_clause:
            agree += 1
    check(f"boundary verdict agrees with clause evaluation on all {1 << n}",
          agree == (1 << n), f"{agree}/{1 << n}")

    surveyed = {sig(a_, n) for a_ in survey_stream(n, bnds)}
    check("the produced set equals the surveyed set exactly",
          got == surveyed,
          f"produced {len(got)}, surveyed {len(surveyed)}")

    excluded = [a_ for a_ in range(1 << n) if not stands(a_, bnds)]
    named = all(len(excluding_boundaries(a_, bnds)) >= 1 for a_ in excluded)
    check("every excluded address is named by at least one boundary", named,
          f"{len(excluded)} excluded")
    check("standing + excluded = 2^n",
          len(produced) + len(excluded) == (1 << n))
    print()

    print("=" * 74)
    print(f"  APPENDIX {appendix}   {checks[0] - len(failures)} of {checks[0]} checks pass")
    if failures:
        print("  FAILURES:")
        for f in failures:
            print(f"    {f}")
    print("=" * 74)
    return 1 if failures else 0
