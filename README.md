# Relational Lysis and Computational Efficiency II — Validation Archive

### Computational validation for *The Resolution of 3-SAT by Boundary Assertion*

**Author:** Dr. David Swanagon
**Affiliation:** ORCID: 0009-0005-9506-4609, Dallas, Texas, United States

---

## 📄 Read the paper

The manuscript is **not** hosted in this repository. It is published open access:

| | |
| --- | --- |
| **Zenodo** | https://doi.org/10.5281/zenodo.23401824 |
| **ResearchGate** | https://www.researchgate.net/publication/415911315_Relational_Lysis_and_Computational_Efficiency_II_The_Resolution_of_3-SAT_by_Boundary_Assertion |

This repository contains only the experiments behind the paper's appendices and their recorded output, so that any claim in the paper can be re-run and checked independently.

---

## 1. What the paper claims

Two theses, each made exact and each measured.

**Structure precedes enumeration.** The space of assignments is not built and then searched. It stands at genesis, in the act of distinction, and the clauses bound it from above. A 3-SAT instance over *n* contents with *m* clauses of width *k* is asserted in exactly *n* + 1 + *km* structural acts, with no address constructed individually and nothing tested in the course of it — verified to *n* = 10,000.

**The information is in the boundary.** What is asserted is the whole of what is held. Membership of any address, the boundary that excludes any other, any admitted address as a path, the count of satisfying assignments and the *i*th of them are each read from the asserted boundaries and from nothing else; no list of assignments is created, kept or summarised at any point. On a threshold instance over 70 contents the whole answer — 597,681 satisfying assignments, 41,837,670 symbols written out — resides in the 965 symbols of the assertion.

Three consequences are measured here rather than asserted:

**Nothing is formed and then discarded.** Across 1,232 instances, 254 of them with no satisfying assignment at all, the count of addresses formed and then rejected is zero. The reason is derived, not observed: a clause's excluded sector is its residual terminus, forced-asserted by Axiom 2.2 of [1] and enfolded at no stratum (Definition 22.1 of [1]), so it is never presented and never entered.

**The boundaries compose, and the composition reads out.** The *m* clause boundaries compose, by one mediation per depth and with no address formed, into one boundary at depth whose strata are **lighthouses**: every address of a lighthouse stands, so the list is read with nothing to reject and no test to perform. The family is invariant under the order the boundaries are presented in, the descent holds one stratum per depth, and the radius census identity holds at every size.

**Better boundaries make shorter paths.** A lighthouse's radius is the capacity the asserted relations leave unallocated, and it moves with how tightly the instance is bounded: across eight seeds at *n* = 24 the greatest radius is 5–9 where *m*/*n* = 1 and 0–2 at the satisfiability threshold. The order of mediation is part of the assertion, written once at genesis, and changes the family measurably. The frontier the paper opens is not an algorithm that searches a space better; it is the construction of better boundaries.

## 2. Foundational papers

This work rests on the Relational Lysis framework:

* Swanagon, D. (2026). *Relational Lysis: The Primitive Architecture of Structure, Constants, and Physical Law.* Zenodo. https://doi.org/10.5281/zenodo.21496929 — cited as **[1]**
* Swanagon, D. (2026). *Relational Lysis and the Necessity of Geometric Solved States: A Structural Resolution of the Yang–Mills Mass Gap.* Zenodo. https://doi.org/10.5281/zenodo.19116249 — cited as **[2]**
* Swanagon, D. (2026). *Relational Lysis and the Three-Body Problem: A Deterministic Derivation of Newtonian Gravity and General Relativity from Solved-State Geometry.* Zenodo. https://doi.org/10.5281/zenodo.19144445 — cited as **[3]**
* Swanagon, D. (2026). *Relational Lysis and Computational Efficiency: An Introductory Examination of the P vs NP Problem Using Relational Structure.* Zenodo. https://doi.org/10.5281/zenodo.23305964 — the companion paper, whose Transfer paragraph names this one

## 3. Contents

```
Scripts/            the eighteen experiment programs, one per appendix, plus the
                    four modules they share
Experiment Logs/    recorded output of each program, as published
instances/          the three committed instances, with their complete solution sets
conventions.py      the two cost measures, defined once
LICENSE
```

The four shared modules are not experiments. `Scripts/resolution.py` writes the assertion; `Scripts/composition.py` composes the boundaries into their lighthouses and imports nothing; `Scripts/production.py` is the verification traversal, charged to no measure; `Scripts/methods.py` implements the classical methods and imports neither of the first two, which Appendix L checks. `conventions.py` defines the two cost measures — structural acts, and RAM elementary operations in the sense of Cook and Reckhow (1973) — so that every method compared is charged identically; every program imports it from the repository root, so it must stay there.

The three instances are committed with their complete solution sets and a SHA-256 fingerprint of their clauses, pinned in `Scripts/resolution.py`; a protocol that cannot load its instance fails rather than reporting a vacuous pass.

## 4. Running the experiments

Python 3.8 or later. No third-party dependencies.

```bash
python3 -I Scripts/A_envelope.py
python3 -I Scripts/B_reversal.py
python3 -I Scripts/C_solved_state.py
python3 -I Scripts/D_instance1.py
python3 -I Scripts/E_instance2.py
python3 -I Scripts/F_generation.py
python3 -I Scripts/G_comparison.py
python3 -I Scripts/I_production.py
python3 -I Scripts/J_adversarial.py
python3 -I Scripts/L_comparison.py
python3 -I Scripts/M_residence.py
python3 -I Scripts/N_distinguish.py
python3 -I Scripts/O_assertion.py
python3 -I Scripts/P_scaling.py
python3 -I Scripts/Q_benchmark.py
python3 -I Scripts/R_worked.py
python3 -I Scripts/S_lighthouse.py
python3 -I Scripts/H_mutation_audit.py
```

Each program is self-contained, resolves its own paths, uses fixed seeds, prints its structural output followed by its verdicts, and exits non-zero if any check fails. They may be run from any working directory. Output should match `Experiment Logs/` exactly; Appendix H re-runs every other protocol and requires that it does. H is run last and takes the longest, since it runs each protocol once per injected fault.

## 5. What each experiment establishes

| Program | Appendix | Establishes |
| --- | --- | --- |
| `A_envelope.py` | A | **The envelope.** The descent run from S₀ by Proposition 5.5 of [1] alone and rebuilt by an independent route; capacity *n*, all 2ⁿ addresses resident at genesis, and the Theorem 12.2 and 13.1 ledgers of [1] at every depth. |
| `B_reversal.py` | B | **The three-symbol boundary.** Over all 94 boundaries of the two committed instances, the excluded sector is the clause's own contents at the opposite orientation, tested against an independently computed cell, written in *k* symbols whatever *n* is; width independence at *k* = 3, 4, 5. |
| `C_solved_state.py` | C | **The solved state of a boundary.** The relational assignment of [2] and [3] on each boundary's own support, decomposed uniquely as *A* = *D* + *S*, and reduced by elementary lysis to its fixed harmonic point in exact rational arithmetic; the two termini at *k* = 3 and the balanced family at even width. |
| `D_instance1.py`, `E_instance2.py` | D, E | **The two committed instances.** Assertion at *n* + 1 + *km*; production equals the committed solution set exactly; an independent clause evaluation of every one of the 2ⁿ addresses agrees with the boundary verdict on all of them; nothing formed and discarded. |
| `F_generation.py` | F | **Generation without storage.** The memory held does not grow with the number of satisfying assignments; the *i*th assignment is produced on demand with no list. |
| `G_comparison.py` | G | **The two cost measures, never combined.** Structural acts for the assertion against elementary operations for the classical methods, with implementation bookkeeping reported separately and charged to no one; enumeration's address counts taken off instrumented counters, not from 2ⁿ. |
| `I_production.py` | I | **Production.** Every address produced stands, every standing address is produced, and the forcing device of the traversal is shown necessary by its removal. |
| `J_adversarial.py` | J | **Adversarial.** 1,232 instances across densities 2.0–8.0, planted and unplanted, 254 of them unsatisfiable: zero addresses formed and discarded on every one. |
| `L_comparison.py` | L | **The classical anchors.** Davis–Putnam, DPLL with Jeroslow–Wang and clause learning implemented in a module that imports neither the assertion nor the traversal, agreeing with production on every model set. |
| `M_residence.py` | M | **The joint structure resides in the boundaries.** The joint relations of each instance read from the written sectors alone and witnessed in both directions; on Tseitin formulas exactly 3*m* at every size. |
| `N_distinguish.py` | N | **The termini of a boundary.** The operator reaches both termini of every boundary without its written form changing; the conjugate pair at odd width. |
| `O_assertion.py` | O | **What arises at the assertion.** The harmonic points read from the asserted symbols equal the same points carved from the cells, on every relation of both instances; the triangle census evaluated at depth one million without forming a descent. |
| `P_scaling.py` | P | **Scaling.** The assertion is *n* + 1 + *km* on every instance of a sweep to *n* = 40, and linear across the Tseitin family on which resolution is provably exponential. |
| `Q_benchmark.py` | Q | **The standard computational tests.** Correctness gate across five methods; the assertion to *n* = 10,000 at 137,801 acts; what each method must hold, in symbols; addresses formed and discarded; the threshold instance at *n* = 70; Tseitin; and the Turing-machine reference model with its closed forms checked against an instrumented machine. |
| `R_worked.py` | R | **One instance, worked.** The assertion, the solved state in exact fractions, the Laplacian with eigenvalues 0, 4, 12 and λ₂ = 4, each standing address along its own path with the dictating boundary named at every position, and the answer verified three ways. |
| `S_lighthouse.py` | S | **The composed boundary and its lighthouses.** The two termini and which one is written; the three relations of a boundary to a stratum, exclusive and exhaustive; the family invariant under presentation order; every reading verified against its committed set and, on 80 uncommitted instances, against exhaustion; the radius census identity; the depth of closure against density on eight seeds; the assertion against the answer to *n* = 70, every one of the 597,681 addresses read and checked against the clauses; Tseitin admitting none; and the composition shown free of enumeration against its own syntax tree. |
| `H_mutation_audit.py` | H | **The audit of A–S.** Twenty-five faults injected one at a time, four of them into the composition and caught by S; every fault must be caught and every protocol in the matrix shown capable of failing; vacuous-pass resistance, committed-log fidelity, and environment independence. |

## 6. Current verdicts

```
APPENDIX A     169 checks pass
APPENDIX B      23 checks pass
APPENDIX C      28 checks pass
APPENDIX D      13 checks pass
APPENDIX E      13 checks pass
APPENDIX F      44 checks pass
APPENDIX G      37 checks pass
APPENDIX I      79 checks pass
APPENDIX J      20 checks pass
APPENDIX L      36 checks pass
APPENDIX M      33 checks pass
APPENDIX N      28 checks pass
APPENDIX O      26 checks pass
APPENDIX P      18 checks pass
APPENDIX Q      47 checks pass
APPENDIX R      40 checks pass
APPENDIX S     105 checks pass
APPENDIX H      40 checks pass
               799 total
```

Full output for each is in `Experiment Logs/`.

## 7. Falsifiability

The paper states its failure modes explicitly, each targeting a distinct item of its dependency chain and each tested by a named protocol here. Failure of any protocol in Appendices A–S is a direct refutation, and this archive exists so that the attempt costs one command.

One standing criterion of the framework belongs here, because this is where it would fail first. Relational Lysis is primitive and the classical methods are downstream projections of it, so a relational resolution can never cost more than its own projection at the same resolution. Should a classical method be shown to beat the boundary assertion on some instance, the conclusion is that the asserted repertoire was incomplete — not that the framework is wrong.

## 8. Citation

If you use this work, please cite the paper rather than the repository.

## 9. License

See `LICENSE`.
