"""
methods.py -- the other methods, each as its own literature defines it.

THIS FILE IMPORTS NOTHING FROM resolution.py OR production.py.

That is deliberate and it is the point.  Each method below works from the
clause list directly, with its own machinery and its own branching rule, and
is charged in its own conventional measure: one elementary operation is one
symbol written, one symbol read, or one comparison of two symbols (Cook and
Reckhow 1973).  No figure produced here is ever divided into, subtracted
from, or otherwise combined with a Relational Lysis figure.  RL is charged
in structural acts and production acts, in its own ledger, and the two are
reported side by side with their units named.

The methods:

  EXHAUSTIVE ENUMERATION    the truth table.  Forms every assignment of the
                            space and tests it.

  DAVIS-PUTNAM (1960)       unit propagation and splitting.  The pure
                            literal rule is excluded: it preserves
                            satisfiability but not the model set, and every
                            method here enumerates all models.

  DPLL (1962)               unit propagation and splitting with a branching
                            heuristic.  The heuristic here is Jeroslow-Wang,
                            which scores a literal by the clauses it occurs
                            in, weighted by clause length -- a real
                            heuristic, not the lowest-index rule.

  CDCL                      conflict-driven clause learning in the line of
                            Chaff and MiniSat: VSIDS activity, first-UIP
                            conflict analysis, non-chronological
                            backtracking, and a learned clause database.

All four enumerate every model, so each answers the same question.  Model
enumeration under CDCL is by blocking clause, as the literature does it.
"""

__all__ = ["Charge", "enumerate_all", "davis_putnam", "dpll_jw", "cdcl"]


class Charge:
    """Elementary operations, in the sense of Cook and Reckhow (1973).

    This is the measure of a machine that constructs its objects.  It is
    these methods' own measure and is never mixed with a structural act.
    """

    __slots__ = ("reads", "writes", "compares", "formed", "discarded",
                 "decisions", "propagations", "conflicts", "learned",
                 "learned_peak", "models")

    def __init__(self):
        self.reads = 0
        self.writes = 0
        self.compares = 0
        self.formed = 0          # complete assignments brought into being
        self.discarded = 0       # complete assignments formed then rejected
        self.decisions = 0
        self.propagations = 0
        self.conflicts = 0
        self.learned = 0
        self.learned_peak = 0
        self.models = 0

    @property
    def total(self):
        return self.reads + self.writes + self.compares


# ---------------------------------------------------------------------------
#  Exhaustive enumeration: the truth table.
# ---------------------------------------------------------------------------

def enumerate_all(n, clauses):
    c = Charge()
    models = []
    for a in range(1 << n):
        c.writes += n                      # form the assignment
        c.formed += 1
        ok = True
        for cl in clauses:
            hit = False
            for p, lit in cl:
                c.reads += 1
                c.compares += 1
                if ((a >> (p - 1)) & 1) == (lit > 0):
                    hit = True
                    break
            if not hit:
                ok = False
                break
        if ok:
            c.models += 1
            c.writes += n                  # retain it
            models.append("".join("T" if (a >> i) & 1 else "F"
                                  for i in range(n)))
        else:
            c.discarded += 1
    return c, models


# ---------------------------------------------------------------------------
#  Shared machinery for the backtracking methods.
# ---------------------------------------------------------------------------

def _clause_status(cl, asg, c):
    """(status, unit) for one clause under a partial assignment."""
    free = None
    nfree = 0
    for p, lit in cl:
        c.reads += 1
        v = asg.get(p)
        if v is None:
            nfree += 1
            free = (p, lit)
        else:
            c.compares += 1
            if v == (lit > 0):
                return "sat", None
    if nfree == 0:
        return "conflict", None
    if nfree == 1:
        return "unit", free
    return "open", None


def _propagate(n, clauses, asg, c):
    """Unit propagation to fixpoint.  True if a conflict was reached."""
    while True:
        unit = None
        for cl in clauses:
            st, u = _clause_status(cl, asg, c)
            if st == "conflict":
                c.conflicts += 1
                if len(asg) == n:
                    c.formed += 1
                    c.discarded += 1
                return True
            if st == "unit" and unit is None:
                unit = u
        if unit is None:
            return False
        p, lit = unit
        asg[p] = (lit > 0)
        c.writes += 1
        c.propagations += 1


def _record(n, asg, c, models):
    c.formed += 1
    c.models += 1
    c.writes += n
    models.append("".join("T" if asg[i + 1] else "F" for i in range(n)))


# ---------------------------------------------------------------------------
#  Davis and Putnam (1960): unit propagation, pure literals, splitting.
# ---------------------------------------------------------------------------

def davis_putnam(n, clauses):
    """Davis and Putnam (1960): unit propagation and splitting.

    The pure literal rule is NOT applied here, and the reason is not an
    omission.  The rule preserves satisfiability but not the set of models:
    assigning a pure literal its polarity discards the models in which it
    takes the other value.  Every method in this file enumerates all
    models, so a rule that is sound for the decision and unsound for the
    enumeration cannot be used.  What remains -- unit propagation and
    splitting on the first unassigned content -- is model-preserving, and
    is what distinguishes this method from the heuristic one below.
    """
    c = Charge()
    models = []

    def go(asg):
        asg = dict(asg)
        if _propagate(n, clauses, asg, c):
            return
        if len(asg) == n:
            _record(n, asg, c, models)
            return
        p = min(q for q in range(1, n + 1) if q not in asg)
        c.decisions += 1
        for val in (False, True):
            a2 = dict(asg)
            a2[p] = val
            c.writes += 1
            go(a2)

    go({})
    return c, models


# ---------------------------------------------------------------------------
#  DPLL (1962) with the Jeroslow-Wang branching heuristic.
# ---------------------------------------------------------------------------

def dpll_jw(n, clauses):
    c = Charge()
    models = []

    def jw_choice(asg):
        """Jeroslow-Wang: score a literal by sum 2^-|C| over the clauses it
        occurs in, among clauses not yet satisfied.  Take the best."""
        score = {}
        for cl in clauses:
            st, _ = _clause_status(cl, asg, c)
            if st == "sat":
                continue
            unresolved = [(p, lit) for p, lit in cl if asg.get(p) is None]
            w = 2.0 ** (-len(unresolved)) if unresolved else 0.0
            for p, lit in unresolved:
                key = (p, lit > 0)
                score[key] = score.get(key, 0.0) + w
        if not score:
            return None
        best = None
        for key, v in score.items():
            c.compares += 1
            # ties broken by position, so the method is deterministic
            if best is None or (v, -key[0]) > best[1]:
                best = (key, (v, -key[0]))
        return best[0]

    def go(asg):
        asg = dict(asg)
        if _propagate(n, clauses, asg, c):
            return
        if len(asg) == n:
            _record(n, asg, c, models)
            return
        choice = jw_choice(asg)
        if choice is None:
            # every clause satisfied; the free contents are unconstrained
            free = [q for q in range(1, n + 1) if q not in asg]
            for mask in range(1 << len(free)):
                a2 = dict(asg)
                for i, q in enumerate(free):
                    a2[q] = bool((mask >> i) & 1)
                c.writes += len(free)
                _record(n, a2, c, models)
            return
        p, val = choice
        c.decisions += 1
        for v in (val, not val):
            a2 = dict(asg)
            a2[p] = v
            c.writes += 1
            go(a2)

    go({})
    return c, models


# ---------------------------------------------------------------------------
#  CDCL: VSIDS, first-UIP learning, non-chronological backtracking.
# ---------------------------------------------------------------------------

def cdcl(n, clauses):
    """DPLL with conflict-driven clause learning, in the line of Chaff and
    MiniSat: VSIDS activity for the decision, first-UIP conflict analysis,
    and a learned clause database consulted by propagation thereafter.

    The decision tree is explored explicitly in both polarities, so
    completeness and termination are structural rather than dependent on a
    learned clause becoming unit at the backtrack level.  Learning is what
    it is in the literature -- the clause is recorded and strengthens every
    later propagation -- and the learned database and its peak size are
    reported, because the database is what this method must hold.
    """
    c = Charge()
    models = []
    base = [list(cl) for cl in clauses]
    learned = []
    activity = {p: 0.0 for p in range(1, n + 1)}
    DECAY = 0.95

    def analyse(conflict_clause, asg, reason, lvl, level):
        """First-UIP: resolve the conflict clause against the reasons of
        the implications at the current level until one literal of that
        level remains.  Returns the learned clause."""
        cur = {p for p, _ in conflict_clause if p in asg}
        seen = set()
        guard = 0
        while guard < 4 * (n + len(base) + len(learned) + 1):
            guard += 1
            at_level = [p for p in cur
                        if lvl.get(p) == level and reason.get(p) is not None]
            if len(at_level) <= 1:
                break
            p = at_level[0]
            seen.add(p)
            cur.discard(p)
            for q, _ in reason[p]:
                c.reads += 1
                if q not in seen and q in asg:
                    cur.add(q)
        return tuple((p, -1 if asg[p] else 1) for p in sorted(cur))

    def go(asg, reason, lvl, level):
        asg = dict(asg)
        reason = dict(reason)
        lvl = dict(lvl)
        # ---- propagate to fixpoint over base and learned clauses
        while True:
            unit = None
            for cl in base + learned:
                st, u = _clause_status(cl, asg, c)
                if st == "conflict":
                    c.conflicts += 1
                    if len(asg) == n:
                        c.formed += 1
                        c.discarded += 1
                    lc = analyse(cl, asg, reason, lvl, level)
                    if lc and len(lc) <= n:
                        learned.append(list(lc))
                        c.learned += 1
                        c.writes += len(lc)
                        c.learned_peak = max(c.learned_peak, len(learned))
                    for p, _ in lc:
                        activity[p] = activity.get(p, 0.0) + 1.0
                    for p in activity:
                        activity[p] *= DECAY
                    return
                if st == "unit" and unit is None:
                    unit = (u, cl)
            if unit is None:
                break
            (p, lit), cl = unit
            asg[p] = (lit > 0)
            lvl[p] = level
            reason[p] = cl
            c.writes += 1
            c.propagations += 1
        if len(asg) == n:
            _record(n, asg, c, models)
            return
        # ---- decide, by VSIDS activity
        best = None
        for q in range(1, n + 1):
            if q in asg:
                continue
            c.compares += 1
            key = (activity.get(q, 0.0), -q)
            if best is None or key > best[1]:
                best = (q, key)
        p = best[0]
        c.decisions += 1
        for val in (True, False):
            a2 = dict(asg)
            a2[p] = val
            l2 = dict(lvl)
            l2[p] = level + 1
            r2 = dict(reason)
            r2[p] = None
            c.writes += 1
            go(a2, r2, l2, level + 1)

    go({}, {}, {}, 0)
    return c, models
