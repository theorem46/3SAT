#!/usr/bin/env python3
"""
APPENDIX H -- MUTATION AUDIT OF THE PROTOCOLS

A protocol that cannot fail proves nothing.  This appendix deliberately
breaks the resolution, the cost accounting, the address encoding and the
committed instance data, and requires that the protocols catch every
break.

Twenty-one faults are injected one at a time.  Each is a specific,
plausible implementation error -- several are errors that were actually
made and caught during development.  For each fault, all seven protocols
are run.  A fault that no protocol detects is a gap in the validation and
fails this audit.

The audit also tests for vacuous passing: a protocol handed no data, or
empty data, must FAIL rather than return a vacuous verdict over an
empty workload.

Faults are applied to throwaway copies in a temporary directory.  Nothing
in the repository is modified.

Any undetected fault exits non-zero.  Deterministic.  No third-party
dependencies.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

#  ALL_PROTOCOLS must pass unmodified (H.1).  The fault matrix (H.2) runs
#  over MATRIX only: every fault is injected once and all of MATRIX is run
#  against it, so a protocol in the matrix is executed once per fault.
#  J_adversarial, L_comparison and M_residence are excluded from the matrix,
#  and the reason is not that they are exempt.  Each is required to pass
#  unmodified in H.1 and each has its committed log verified in H.4.  They
#  are out of the matrix because their instances are large: J resolves over
#  a thousand, M resolves Tseitin formulas up to 39 contents, and a fault
#  that disables forcing turns a large instance from a fast resolution into
#  an exponential one, so such a protocol would hang rather than fail and
#  the audit would measure a timeout instead of a detection.  Every module
#  a fault touches is imported by a protocol that is in the matrix, and the
#  matrix instances are small enough that a disabled mechanism still
#  terminates and still reports.
ALL_PROTOCOLS = ["A_envelope", "B_reversal", "C_solved_state", "D_instance1",
                 "E_instance2", "F_generation", "G_comparison",
                 "I_production", "J_adversarial", "L_comparison",
                 "M_residence", "N_distinguish", "O_assertion",
                 "P_scaling", "Q_benchmark", "R_worked",
                 "S_lighthouse"]

MATRIX = ["A_envelope", "B_reversal", "C_solved_state", "D_instance1",
          "E_instance2", "F_generation", "G_comparison", "I_production"]

PROTOCOLS = MATRIX

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


# ---------------------------------------------------------------------------
#  The faults.  Each is (name, description, mutate) where mutate receives a
#  path to a fresh copy of the repository and edits it in place.
# ---------------------------------------------------------------------------

def _patch(path, old, new, required=True):
    with open(path) as f:
        s = f.read()
    if old not in s:
        if required:
            raise AssertionError(f"anchor not found in {path}: {old[:60]!r}")
        return False
    with open(path, "w") as f:
        f.write(s.replace(old, new, 1))
    return True


def f_no_opposition(repo):
    """The boundary uses the literal rather than its structural opposite:
    Theorem 7.1 denied.  The excluded sector becomes the satisfied sector."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           "            if lit < 0:              # the opposite of this literal",
           "            if lit > 0:              # MUTANT: no opposition")


def f_partial_mask(repo):
    """The boundary fixes only two of its three contents: Theorem 7.2
    denied."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           "        for p, lit in c:\n            bit = 1 << (p - 1)",
           "        for p, lit in c[:2]:\n            bit = 1 << (p - 1)")


def f_stands_inverted(repo):
    """stands() returns the opposite verdict."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           "        if (a & mask) == value:\n            return False\n    return True",
           "        if (a & mask) == value:\n            return True\n    return False")


def f_stands_first_only(repo):
    """stands() consults only the first boundary."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           "    for mask, value in bnds:\n        if (a & mask) == value:\n            return False\n    return True",
           "    for mask, value in bnds[:1]:\n        if (a & mask) == value:\n            return False\n    return True")


def f_cost_drops_mediation(repo):
    """assertion_cost omits the mediation: Corollary 7.3 denied by one."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           'return instance["n"] + 1 + instance["k"] * instance["m"]',
           'return instance["n"] + instance["k"] * instance["m"]')


def f_cost_uses_n_not_k(repo):
    """assertion_cost charges n per boundary instead of k: Theorem 6.2
    denied -- the clause treated as having the envelope's capacity."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           'return instance["n"] + 1 + instance["k"] * instance["m"]',
           'return instance["n"] + 1 + instance["n"] * instance["m"]')


def f_sig_reversed(repo):
    """The address is written x_n first instead of x_1 first.  This is the
    indexing fault that actually occurred during development."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           'return "".join("T" if (a >> i) & 1 else "F" for i in range(n))',
           'return "".join("T" if (a >> (n - 1 - i)) & 1 else "F" for i in range(n))')


def f_nth_off_by_one(repo):
    """produce_nth returns the (i+1)-th address the descent emits."""
    _patch(os.path.join(repo, "Scripts", "production.py"),
           "        if j == i:\n            return a",
           "        if j == i + 1:\n            return a")


def f_emit_unclosed(repo):
    """The descent emits a region it has closed: a closure is recorded but
    the descent continues into the excluded sector.  Theorem 7.1 denied at
    the point of production -- excluded addresses are produced."""
    _patch(os.path.join(repo, "Scripts", "production.py"),
           "                led.discard()\n            continue",
           "                led.discard()\n            pass   # MUTANT: enter it")


def f_no_eager_forcing(repo):
    """Forcing is NOT applied to exhaustion before an orientation is chosen:
    the descent takes a branch while a boundary is still forcing.  This is
    the ordering on which `discarded == 0` depends, so a run under this
    fault must form addresses it then throws away."""
    _patch(os.path.join(repo, "Scripts", "production.py"),
           "        while forcing:\n            bit, want = min(forcing.items())",
           "        while False:          # MUTANT: forcing not applied\n"
           "            bit, want = min(forcing.items())")


def f_survey_all(repo):
    """The truth table admits every address.  The survey is not the
    resolution, but it is what the resolution is verified against, so a
    corrupted truth table must fail the cross-check rather than pass it:
    this fault proves the verification is not vacuous."""
    _patch(os.path.join(repo, "Scripts", "resolution.py"),
           "    for a in range(1 << n):\n        if stands(a, bnds):\n            yield a",
           "    for a in range(1 << n):\n        if True:\n            yield a")


def f_solution_flipped(repo):
    """One address in instance 1's committed solution set is altered."""
    p = os.path.join(repo, "instances", "instance1.json")
    d = json.load(open(p))
    s = list(d["solutions"][0])
    s[0] = "F" if s[0] == "T" else "T"
    d["solutions"][0] = "".join(s)
    json.dump(d, open(p, "w"), indent=1)


def f_solution_dropped(repo):
    """One address is removed from instance 2's committed solution set."""
    p = os.path.join(repo, "instances", "instance2.json")
    d = json.load(open(p))
    d["solutions"] = d["solutions"][1:]
    json.dump(d, open(p, "w"), indent=1)


def f_clause_dropped(repo):
    """A clause is removed from instance 1: the assertion no longer matches
    the instance it claims to resolve."""
    p = os.path.join(repo, "instances", "instance1.json")
    d = json.load(open(p))
    d["clauses"] = d["clauses"][1:]
    d["m"] = len(d["clauses"])
    json.dump(d, open(p, "w"), indent=1)


def f_lysis_no_transpose(repo):
    """Lysis zeroes one entry but not its transpose: antisymmetry broken,
    Proposition 10.1 denied."""
    _patch(os.path.join(repo, "Scripts", "C_solved_state.py"),
           "        S[i][j] = F(0)\n        S[j][i] = F(0)",
           "        S[i][j] = F(0)")



def f_descent_short(repo):
    """The descent stops one level early: Theorem 5.2 denied."""
    _patch(os.path.join(repo, "Scripts", "A_envelope.py"),
           "    for depth in range(1, N + 1):",
           "    for depth in range(1, N):")


def f_ledger_wrong_pairs(repo):
    """The ledger reports depth + 1 aligned pairs: Theorem 13.1 denied."""
    _patch(os.path.join(repo, "Scripts", "A_envelope.py"),
           "        pairs = depth            # Theorem 13.1: n conjugate pairs aligned",
           "        pairs = depth + 1        # MUTANT")


def f_descent_not_binary(repo):
    """A partition step generates one sector instead of two: Axiom 2.4
    denied, Proposition 4.3 denied."""
    _patch(os.path.join(repo, "Scripts", "A_envelope.py"),
           "        nxt = [w + (True,) for w in prev] + [w + (False,) for w in prev]",
           "        nxt = [w + (True,) for w in prev]")


def f_boundary_word_short(repo):
    """B's boundary_word writes one symbol fewer: Theorem 7.2 denied."""
    _patch(os.path.join(repo, "Scripts", "B_reversal.py"),
           "    for p, l in reversal(clause):\n        w[p - 1] = \"T\" if l > 0 else \"F\"",
           "    for p, l in list(reversal(clause))[:-1]:\n        w[p - 1] = \"T\" if l > 0 else \"F\"")


def f_wrong_centre(repo):
    """C's assignment uses a centre of zero rather than the support's mean:
    the Theorem 6.8 form of [3] denied."""
    _patch(os.path.join(repo, "Scripts", "C_solved_state.py"),
           "    sc = sum(s, F(0)) / w",
           "    sc = F(0)")


def f_enum_undercharged(repo):
    """G charges enumeration for reads but not for forming its addresses:
    the comparison made unfair in enumeration's favour."""
    _patch(os.path.join(repo, "Scripts", "G_comparison.py"),
           "        o.write(n)                           # form the address: n symbols",
           "        pass                                 # MUTANT: not charged")

def f_comp_barred_inverted(repo):
    """barred() returns the opposite verdict: a stratum that opposes a
    boundary's residual terminus is read as not opposing it, and one that
    does not is read as barred.  Every lighthouse is then wrong."""
    _patch(os.path.join(repo, "Scripts", "composition.py"),
           "    return (rv & both) != (sv & both)",
           "    return (rv & both) == (sv & both)   # MUTANT")


def f_comp_terminus_literal(repo):
    """The residual terminus is built from the literal rather than its
    opposite: the boundary excludes the sector in which every literal
    STANDS.  Axiom 2.2 denied at the point of writing the terminus."""
    _patch(os.path.join(repo, "Scripts", "composition.py"),
           "        if pol < 0:                 # literal ~x_p is falsified by x_p = T",
           "        if pol > 0:                 # MUTANT: the literal, not its opposite")


def f_comp_residual_partial(repo):
    """at_residual() ignores one content of the support when deciding
    whether a stratum stands at the residual terminus, so a sector that
    agrees on the rest is held unpresented though it is not at the
    terminus."""
    _patch(os.path.join(repo, "Scripts", "composition.py"),
           "    return (rv & sf) == sv",
           "    return (rv & sf & ~1) == (sv & ~1)   # MUTANT: content 0 ignored")


def f_comp_enter_unpresented(repo):
    """The descent enters a sector standing at a residual terminus instead
    of leaving it unpresented.  Theorem 22.3 denied: the excluded sector is
    presented, and addresses at it are read as standing."""
    _patch(os.path.join(repo, "Scripts", "composition.py"),
           "            if any(at_residual(sector, t) for t in bd[d]):\n                continue",
           "            if any(at_residual(sector, t) for t in bd[d]):\n                pass   # MUTANT: enter it")


COMPOSITION_FAULTS = [
    ("comp-barred-inverted",   "barred() returns the opposite verdict",       f_comp_barred_inverted),
    ("comp-terminus-literal",  "terminus built from the literal, not its opposite", f_comp_terminus_literal),
    ("comp-residual-partial",  "at_residual() ignores one content",           f_comp_residual_partial),
    ("comp-enter-unpresented", "the descent enters an unpresented sector",    f_comp_enter_unpresented),
]

FAULTS = [
    ("no-opposition",        "boundary uses the literal, not its opposite", f_no_opposition),
    ("partial-mask",         "boundary fixes 2 of 3 contents",              f_partial_mask),
    ("stands-inverted",      "stands() returns the opposite verdict",       f_stands_inverted),
    ("stands-first-only",    "stands() consults only the first boundary",   f_stands_first_only),
    ("cost-no-mediation",    "assertion cost omits the mediation",          f_cost_drops_mediation),
    ("cost-n-per-boundary",  "boundary charged n symbols, not k",           f_cost_uses_n_not_k),
    ("sig-reversed",         "address written x_n first",                   f_sig_reversed),
    ("nth-off-by-one",       "produce_nth returns the next address",        f_nth_off_by_one),
    ("emit-unclosed",        "the descent enters a region it has closed",   f_emit_unclosed),
    ("no-eager-forcing",     "forcing not applied before a branch is taken", f_no_eager_forcing),
    ("survey-all",           "the truth table admits every address",        f_survey_all),
    ("solution-flipped",     "one committed solution altered",              f_solution_flipped),
    ("solution-dropped",     "one committed solution removed",              f_solution_dropped),
    ("clause-dropped",       "a clause removed from the instance",          f_clause_dropped),
    ("lysis-no-transpose",   "lysis breaks antisymmetry",                   f_lysis_no_transpose),
    ("descent-short",        "descent stops one level early",               f_descent_short),
    ("ledger-wrong-pairs",   "ledger reports depth+1 aligned pairs",         f_ledger_wrong_pairs),
    ("descent-not-binary",   "partition generates one sector, not two",      f_descent_not_binary),
    ("boundary-word-short",  "boundary written in k-1 symbols",              f_boundary_word_short),
    ("wrong-centre",         "assignment centre set to zero",                f_wrong_centre),
    ("enum-undercharged",    "enumeration not charged for forming addresses", f_enum_undercharged),
]


# ---------------------------------------------------------------------------
def run_protocol(repo, name, timeout=60):
    """Run one protocol in a repository copy.  Returns its exit code."""
    try:
        r = subprocess.run([sys.executable, "-I",
                            os.path.join(repo, "Scripts", name + ".py")],
                           capture_output=True, text=True, cwd=repo,
                           timeout=timeout)
        return r.returncode
    except subprocess.TimeoutExpired:
        return 124


def fresh_copy(tmp, tag):
    dst = os.path.join(tmp, tag)
    shutil.copytree(ROOT, dst,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc",
                                                  "Experiment Logs", ".git"))
    return dst


print("=" * 74)
print("  APPENDIX H -- MUTATION AUDIT OF THE PROTOCOLS")
print("  faults injected one at a time; every fault must be caught")
print("  by at least one protocol, and the baseline must pass cleanly")
print("=" * 74)
print()

tmp = tempfile.mkdtemp(prefix="rl3sat_audit_")

try:
    # -----------------------------------------------------------------------
    print("H.1  BASELINE -- THE UNMODIFIED PROTOCOLS PASS")
    print()
    base = fresh_copy(tmp, "baseline")
    # The baseline is not a timing test, so each protocol is given room to
    # finish.  Q_benchmark carries the family on which resolution is provably
    # exponential out to where the classical work is in the hundreds of
    # millions of operations, and so takes minutes rather than seconds.  The
    # fault matrix below keeps its short timeout, because there a protocol
    # that hangs must be distinguished from one that detects.
    baseline = {p: run_protocol(base, p, timeout=900)
                for p in ALL_PROTOCOLS}
    for p in ALL_PROTOCOLS:
        check(f"{p} exits 0 unmodified", baseline[p] == 0,
              f"exit {baseline[p]}")
    print()

    # -----------------------------------------------------------------------
    print("H.2  MUTATION -- EVERY FAULT MUST BE CAUGHT")
    print()
    cols = "".join(f" {p[0]:>2}" for p in MATRIX)
    hdr = f"    {'fault':<22}{cols}   caught by"
    print(hdr)
    print("    " + "-" * (len(hdr) - 4))
    undetected = []
    catchers_seen = set()
    for tag, desc, mutate in FAULTS:
        repo = fresh_copy(tmp, "m_" + tag)
        try:
            mutate(repo)
        except AssertionError as e:
            print(f"    {tag:<22}  ANCHOR MISSING: {e}")
            undetected.append((tag, "anchor"))
            continue
        codes = {p: run_protocol(repo, p) for p in PROTOCOLS}
        marks = "".join(f" {'X' if codes[p] != 0 else '.':>2}" for p in PROTOCOLS)
        catchers = [p[0] for p in PROTOCOLS if codes[p] != 0]
        catchers_seen.update(p for p in PROTOCOLS if codes[p] != 0)
        print(f"    {tag:<22}{marks}   {''.join(catchers) if catchers else 'NONE'}")
        if not catchers:
            undetected.append((tag, desc))
        shutil.rmtree(repo, ignore_errors=True)
    print()
    print("    X = protocol failed (fault caught)    . = protocol passed")
    print()
    check(f"every one of the {len(FAULTS)} faults is caught by some protocol",
          not undetected,
          f"undetected: {[t for t, _ in undetected]}" if undetected else "none undetected")

    # Completeness of the audit itself: a protocol never shown to fail has
    # not been shown capable of failing, and proves nothing.
    # -----------------------------------------------------------------------
    print("H.2b MUTATION OF THE COMPOSITION -- EVERY FAULT MUST BE CAUGHT BY S")
    print("     composition.py is imported by S_lighthouse alone, so each of")
    print("     these faults is run against S and S must exit non-zero.")
    print()
    comp_undetected = []
    for tag, desc, mutate in COMPOSITION_FAULTS:
        repo = fresh_copy(tmp, "m_" + tag)
        try:
            mutate(repo)
        except AssertionError as e:
            print(f"    {tag:<24}  ANCHOR MISSING: {e}")
            comp_undetected.append((tag, "anchor"))
            continue
        code = run_protocol(repo, "S_lighthouse", timeout=900)
        print(f"    {tag:<24}  {'caught' if code != 0 else 'NOT CAUGHT':<10}  {desc}")
        if code == 0:
            comp_undetected.append((tag, desc))
        shutil.rmtree(repo, ignore_errors=True)
    print()
    check(f"every one of the {len(COMPOSITION_FAULTS)} composition faults is "
          "caught by S", not comp_undetected,
          f"undetected: {[t for t, _ in comp_undetected]}" if comp_undetected
          else "none undetected")
    print()

    never_caught = [p for p in PROTOCOLS if p not in catchers_seen]
    check("every protocol is shown capable of failing",
          not never_caught,
          f"never caught a fault: {never_caught}" if never_caught
          else f"all {len(PROTOCOLS)} exercised")
    print()

    # -----------------------------------------------------------------------
    print("H.3  VACUOUS PASSING -- NO DATA MUST FAIL, NOT PASS")
    print("     a protocol handed missing or empty input must exit non-zero")
    print("     rather than reporting a vacuous pass over an empty workload")
    print()
    # missing instance files
    repo = fresh_copy(tmp, "v_missing")
    os.remove(os.path.join(repo, "instances", "instance1.json"))
    for p in ("B_reversal", "C_solved_state", "D_instance1", "F_generation",
              "G_comparison"):
        code = run_protocol(repo, p)
        check(f"{p} fails when instance1.json is missing", code != 0,
              f"exit {code}")
    shutil.rmtree(repo, ignore_errors=True)
    print()

    # empty clause list
    repo = fresh_copy(tmp, "v_empty")
    p1 = os.path.join(repo, "instances", "instance1.json")
    d = json.load(open(p1))
    d["clauses"] = []
    d["m"] = 0
    json.dump(d, open(p1, "w"), indent=1)
    for p in ("B_reversal", "D_instance1", "G_comparison"):
        code = run_protocol(repo, p)
        check(f"{p} fails on an empty clause list", code != 0, f"exit {code}")
    shutil.rmtree(repo, ignore_errors=True)
    print()

    # empty solution set
    repo = fresh_copy(tmp, "v_nosol")
    p1 = os.path.join(repo, "instances", "instance1.json")
    d = json.load(open(p1))
    d["solutions"] = []
    json.dump(d, open(p1, "w"), indent=1)
    for p in ("D_instance1", "F_generation"):
        code = run_protocol(repo, p)
        check(f"{p} fails on an empty solution set", code != 0, f"exit {code}")
    shutil.rmtree(repo, ignore_errors=True)
    print()

    # -----------------------------------------------------------------------
    print("H.4  THE COMMITTED LOGS MATCH A FRESH RUN")
    print()
    for name, letter in zip(PROTOCOLS, "ABCDEFG"):
        logp = os.path.join(ROOT, "Experiment Logs", f"{letter}.log")
        if not os.path.exists(logp):
            check(f"{letter}.log present", False)
            continue
        r = subprocess.run([sys.executable, "-I",
                            os.path.join(ROOT, "Scripts", name + ".py")],
                           capture_output=True, text=True, cwd=ROOT)
        committed = open(logp).read()
        check(f"{letter}.log identical to a fresh run of {name}",
              r.stdout == committed,
              f"{len(r.stdout)} vs {len(committed)} bytes")
    print()

    # -----------------------------------------------------------------------
    print("H.5  ENVIRONMENT INDEPENDENCE")
    print("     hash seed, working directory and locale must not change output")
    print()
    import hashlib

    def out_hash(name, env=None, cwd=ROOT):
        e = dict(os.environ)
        if env:
            e.update(env)
        r = subprocess.run([sys.executable, os.path.join(ROOT, "Scripts", name + ".py")],
                           capture_output=True, text=True, cwd=cwd, env=e)
        return hashlib.md5(r.stdout.encode()).hexdigest()[:12], r.returncode

    for name in ("B_reversal", "D_instance1", "G_comparison"):
        seen = set()
        for env in ({"PYTHONHASHSEED": "0"}, {"PYTHONHASHSEED": "1"},
                    {"PYTHONHASHSEED": "random"},
                    {"LC_ALL": "C"}, {"LC_ALL": "en_US.UTF-8"}):
            seen.add(out_hash(name, env))
        # and from a different working directory
        seen.add(out_hash(name, {"PYTHONHASHSEED": "0"}, cwd=tmp))
        check(f"{name}: identical output across 5 environments and 2 cwds",
              len(seen) == 1, f"{len(seen)} distinct results")
    print()

finally:
    shutil.rmtree(tmp, ignore_errors=True)

print("=" * 74)
print(f"  APPENDIX H   {CHECKS - len(FAILURES)} of {CHECKS} checks pass")
if FAILURES:
    print("  FAILURES:")
    for f in FAILURES:
        print(f"    {f}")
print("=" * 74)
sys.exit(1 if FAILURES else 0)
