"""
conventions.py -- the cost measures, defined once.

Imported by every experiment in this archive so that no method is charged
differently from any other.  This file is not an experiment.

THE UNIT OF COST IS NEVER AN ADDRESS.

That is the whole of the convention and the reason it is stated first.  In
Relational Lysis the information is held in the boundary, and the addresses
are produced from it.  An address is therefore an output of the method, not
an input to it and not an item in storage.  Charging per address would be
charging arithmetic for every number it can produce, and it would measure
the artefact the boundary makes unnecessary.  Nothing in this archive
counts an address as a cost.

What is counted, and what is not.  Relational Lysis is charged in STRUCTURAL
ACTS, for the assertion, and is reported beside what it must HOLD, in
symbols.  The classical methods are charged in ELEMENTARY OPERATIONS, which
is their own measure.  Those are the measures of this archive, they are
reported separately, and they are never combined.  The traversal tally below
is a verification device and is charged to nothing.

STRUCTURAL ACT  (class Acts)
    One assertion, or one intercession of the Between.  By Definition 3.1 an
    assertion of structural identity is one act.  By Axiom 4.1 and Definition
    5.1 a mediation is one intercession, binary by construction (Proposition
    5.9).  By Axiom 2.2 a structural opposite is forced by the assertion of
    its term, and is recorded and charged nothing.

    This measure prices the assertion of the instance: what it costs to have
    the boundaries.

TRAVERSAL TALLY  (class Ledger) -- A VERIFICATION DEVICE, CHARGED TO NOTHING

    This class is NOT a cost measure and nothing in this archive reports it
    as one.  It instruments the traversal device of production.py, in the
    same way and for the same reason that the survey functions of
    resolution.py are instrumented: so that a traversal can be checked
    against the boundaries and against an independent route.  It is charged
    to no method and appears in no comparison.

    The reason is axiomatic and not editorial.  By Theorem 15.1 every finite
    configuration resides within the descent of the first relation
    "independently of any act of selection, retrieval, or observation", so
    there is no act of obtaining an address to be priced: as Section 1 of
    the primitive architecture puts it, "retrieval is arrival at an address
    rather than reassembly from parts", and "the cost of a configuration is
    the length of its path rather than the size of a stored table".  A
    configuration at depth n is a path of length n.  Enumeration -- building
    and holding a catalogue of addresses -- is, in that paper's words,
    "downstream apparatus, not foundation", and a tally of a downstream
    traversal is therefore never a figure for Relational Lysis.

    What this archive charges to Relational Lysis is the assertion, in
    structural acts, and what it reports beside it is what must be held, in
    symbols.  Those are the two measures, and the traversal tally is neither.

    Its one diagnostic quantity is kept because it is falsifiable:
    `discarded`, an address formed and then thrown away.  A traversal that
    forms a candidate and rejects it is searching; one whose boundaries
    dictate the admissible orientation never forms an address it must
    reject.  The figure is measured rather than asserted, and Appendix H
    weakens the forcing rule to make the counter rise.

ELEMENTARY OPERATION  (class Ops)
    One operation on a RAM in the sense of Cook and Reckhow (1973): one
    symbol written, one symbol read, or one comparison of two symbols.
    Enumeration is charged in this measure, which is its own.

BOOKKEEPING
    Any operation performed by an implementation that belongs to none of the
    above -- loop counters, container management, index arithmetic.  Reported
    separately and folded into no measure, so that no overhead of this
    program can be mistaken for a cost of any method.

Two quantities are common to every method and are therefore the only ones
compared directly across them:

    SYMBOLS HELD        what the method must keep in order to answer.
    ADDRESSES FORMED    how many addresses the method brings into existence.

Both are in the same unit on every side of every table in this archive.
"""

__all__ = ["Acts", "Ledger", "Ops", "COOK_RECKHOW"]

COOK_RECKHOW = "Cook, S. A. and Reckhow, R. A. (1973), JCSS 7(4), 354-375"


class Acts:
    """Structural acts.  Assertions and mediations only.

    Prices the assertion of the instance.  No address is a unit here.
    """

    __slots__ = ("assertions", "mediations", "forced")

    def __init__(self):
        self.assertions = 0
        self.mediations = 0
        self.forced = 0          # recorded, charged zero

    def assert_term(self, count=1):
        self.assertions += count

    def mediate(self, count=1):
        self.mediations += count

    def force(self, count=1):
        """A structural opposite, forced by Axiom 2.2.  Charged nothing."""
        self.forced += count

    @property
    def total(self):
        return self.assertions + self.mediations

    def __repr__(self):
        return (f"Acts(assertions={self.assertions}, mediations={self.mediations}, "
                f"forced={self.forced}, total={self.total})")


class Ledger:
    """A tally of a traversal.  A VERIFICATION DEVICE, CHARGED TO NOTHING.

    This is not a cost measure and this archive reports no figure of it as
    a cost of any method.  By Theorem 15.1 a configuration resides
    "independently of any act of selection, retrieval, or observation", so
    there is no act of obtaining an address to price; the cost of a
    configuration is the length of its path.  See the note at the head of
    this file.

    The tally exists so that a traversal can be checked: `emitted` against
    the committed solution set and against an independent survey, and
    `discarded` -- an address formed and then thrown away -- as the
    falsifiable signature of search, which Appendix H makes rise by
    weakening the forcing rule.
    """

    __slots__ = ("consultations", "chosen", "forced", "branches",
                 "closures", "emitted", "discarded", "max_depth")

    def __init__(self):
        self.consultations = 0   # a boundary read against the descent
        self.chosen = 0          # an orientation the descent selected
        self.forced = 0          # an orientation a boundary dictated: charged 0
        self.branches = 0        # a conjugate pair taken
        self.closures = 0        # a region closed by conflicting boundaries
        self.emitted = 0         # an address produced
        self.discarded = 0       # an address formed and then thrown away
        self.max_depth = 0       # deepest partial orientation held at once

    def consult(self, count=1):
        self.consultations += count

    def choose(self, count=1):
        self.chosen += count

    def force(self, count=1):
        """An orientation a boundary dictates, by Axiom 2.2.  Charged nothing."""
        self.forced += count

    def branch(self, count=1):
        self.branches += count

    def close(self, count=1):
        self.closures += count

    def emit(self, count=1):
        self.emitted += count

    def discard(self, count=1):
        self.discarded += count

    def depth(self, d):
        if d > self.max_depth:
            self.max_depth = d

    @property
    def total(self):
        """The traversal's own tally.  NOT A COST, and not reported as one:
        see the class docstring and the note at the head of this file."""
        return self.consultations + self.chosen + self.branches

    def __repr__(self):
        return (f"Ledger(consultations={self.consultations}, "
                f"chosen={self.chosen}, forced={self.forced}, "
                f"branches={self.branches}, closures={self.closures}, "
                f"emitted={self.emitted}, discarded={self.discarded}, "
                f"total={self.total})")


class Ops:
    """Elementary operations: writes, reads, comparisons.

    The measure of a machine that constructs its objects.  Enumeration is
    charged here.
    """

    __slots__ = ("writes", "reads", "comparisons", "formed", "discarded")

    def __init__(self):
        self.writes = 0
        self.reads = 0
        self.comparisons = 0
        self.formed = 0          # addresses brought into existence
        self.discarded = 0       # addresses formed and then thrown away

    def write(self, count=1):
        self.writes += count

    def read(self, count=1):
        self.reads += count

    def compare(self, count=1):
        self.comparisons += count

    def form(self, count=1):
        self.formed += count

    def discard(self, count=1):
        self.discarded += count

    @property
    def total(self):
        return self.writes + self.reads + self.comparisons

    def __repr__(self):
        return (f"Ops(writes={self.writes}, reads={self.reads}, "
                f"comparisons={self.comparisons}, formed={self.formed}, "
                f"discarded={self.discarded}, total={self.total})")
