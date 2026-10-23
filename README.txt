Lu--Raz completed family: exact closure count and statement correspondence

For every natural x>=3, q=x+1 and n=4q, the explicitly completed family has
  (23x^2+81x+16)/2
distinct unions of nonempty subfamilies. If the empty subfamily is permitted,
the count is (23x^2+81x+18)/2. No finite upper bound on x is assumed.

The missing source row is uniquely forced by the other printed rows and their
asserted uniform column frequency. This reconstruction and both closure
conventions have been formally checked, alongside the fourteen-class count.
Author intent, source clarification, external mathematical acceptance, priority
and prize eligibility are not established by a local Lean check.

Read PROOF.txt for the mathematical argument, STATEMENT_CORRESPONDENCE.txt for
the exact source/Lean comparison, PRIOR_WORK.txt for the bounded search and its
limits, and ATTRIBUTION.txt for source credits and AI-assistance disclosure.

Lean entry points
 LuRazClosure.closure_cardinality_for_every_x
 LuRazSubmission.nonempty_count_in_paper_range
 LuRazSubmission.omitted_row_forced
 LuRazSubmission.balanced_completion_unique
 LuRazSubmission.every_balanced_completion_count
 LuRazSubmission.nonempty_subfamily_iff
 LuRazSubmission.including_empty_count
 LuRazSubmission.nonempty_count_n_scaled
 LuRazParametric.completed_for_every_x

The main count is an exact Nodup list of predicates on the original Fin(4q)
ground set, with both directions of membership correspondence and a proved
length. The bridges identify this with arbitrary predicate-selected subfamilies
of the actual source. The conditional completion theorem assumes precisely the
other printed row formulas and the printed equal-frequency assertion; it proves
the omitted row rather than assuming its equality with our definition. The
explicit-family count theorem needs no such completion hypothesis.

Reproduction
Requirements: Python 3.11 or later, Lean 4.35.0 with bundled Std, and elan/lake.
No Mathlib, additional package, dependency download or installation is performed.
Use an already installed toolchain name, for example
  python -X utf8 reproduce.py --toolchain leanprover/lean4:v4.35.0
or replace the name with an existing local Lean 4.35.0 alias. The script rejects
an uninstalled toolchain instead of downloading it.

The script checks source hashes and prohibited placeholders/bypasses, builds
all targets, audits every theorem declaration's transitive axioms, replays all
local proof modules with the bundled leanchecker, then performs independent
finite comparisons. LEAN_NUM_THREADS=1 limits concurrent replay resources.
Reports record the actual completed level and whether a project build cache
existed before the run. Public logs redact installation/workspace directory
prefixes, without changing proof diagnostics or outcomes.

The permitted standard axioms are propext, Classical.choice and Quot.sound.
The bundled replay uses Lean's own kernel implementation and trusts imported
upstream Std artifacts. It is not a second independently implemented kernel or
an independent mathematical reviewer. Source-level statement comparison remains
necessary even if a build, axiom audit and replay all pass.

RuntimeCheck.lean is test-only and is not imported by theorem modules. It exports
actual Lean source rows and class enumerations; check_runtime.py independently
constructs the family and calculates its closure. Five parameter points
x=3,5,12,32,64 compare 499 source rows, all 70 core classes, and complete closure
sets, including a largest closure of 49,704 sets. Those checks detect transcription
errors and do not substitute for the universal proofs.

Source: https://arxiv.org/html/2405.10639v2
Related statement: https://mathdb.com/p/363119/the-quadratic-union-closure-conjecture-for-the-constructed-f
The related page is not a confirmed mapping into a prize program.
