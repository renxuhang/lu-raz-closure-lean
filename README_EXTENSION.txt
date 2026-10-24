LU--RAZ SUBMISSION: PRIMARY COUNT PROOF AND SEPARATE EXTENSIONS
24 October 2026

Primary contribution
The primary submission is the exact nonempty union-closure count of the
explicitly completed original family of Lu and Raz (2024). For every x>=3,
q=x+1 and n=4q, this count is (23x^2+81x+16)/2. The printed conjecture's x>=5
range is included. Including the empty subfamily adds exactly one member.
The omitted row is forced by the other rows and the equal column frequencies.
Subsequent inspection of the paper-linked author programs supports both this
row and the nonempty convention; see SOURCE_PROGRAM_EVIDENCE.txt.

The original proof, statement bridges, English mathematical explanation,
attribution and clean reproduction reports remain fixed at:
https://github.com/renxuhang/lu-raz-closure-lean/tree/e12a3abd3fb93aedd4816e780a1caf1156e45c1a
Its original 97 public files are retained without modification by this update.
The original reproduction builds 79 modules, audits 605 explicit theorems,
replays 79 modules with Lean's bundled kernel, and performs finite comparisons.

Separate extensions
The three-row source V and six-row source B are explicitly modified families.
Their nonempty closure counts, for every integer q>=4, are respectively
 (23q^2+31q-30)/2 and (23q^2+7q+2)/2.
The six-row difference against V is classified into exactly 27 removed groups
and 16 added groups, all exhaustive and semantically duplicate-free. Their
sizes are 25q-24 and 13q-8. This reduces V's count by 12q-16, and the original
completed S count by 14q-22. The quadratic leading coefficient is unchanged.

The extension includes the full 14-part coordinate frequency spectrum of the
actual closure C_B, exact extrema (including the q=4 maximum tie), sharp
uniform frequency bounds, the q>=7 threshold for every frequency exceeding
15/23 of the closure size, and total weight
 2W_B=69q^3+15q^2-18q-34.
Within this B parameter family, the minimum coordinate-frequency ratio is
uniquely maximized at q=13, with value 653/995. This is a family-specific
optimization. The source B itself is not union-closed; the spectrum describes
its actual union-closed nonempty closure C_B.

Read PROOF_EXTENSION.txt for the mathematical argument and all group/spectrum
tables, STATEMENT_CORRESPONDENCE_EXTENSION.txt for exact Lean endpoints,
ATTRIBUTION_EXTENSION.txt for original credits and AI-assistance disclosure.
extension-api.json identifies the principal actual-spectrum and bound results;
extension-closure-api.json identifies exact difference and cardinality results.
The original SubmissionBridge remains at the fixed primary commit above.

Reproduction of the extension
Requirements: Python 3.11+ and an already installed Lean 4.35.0 toolchain with
the bundled Std library and leanchecker. No Mathlib or package download.
  python -X utf8 reproduce_extension.py --toolchain leanprover/lean4:v4.35.0
Or specify another already installed Lean 4.35.0 alias. The script rejects an
uninstalled toolchain instead of downloading it. It checks all manifest hashes,
compiles the 341-module source graph, audits all 8720 explicit public theorems,
and replays each local module using up to four separate leanchecker processes.
It records whether a project build cache existed before that run; use a fresh
extraction for an empty-project-cache reproduction. It trusts the installed
upstream Std artifacts. The replay uses Lean's bundled kernel implementation.

The original reproduce.py/source-manifest.json continue to refer to the fixed
primary proof. reproduce_extension.py/extension-manifest.json refer to the
separate extension graph. Either can be run from the repository root.
The historical staged audits are described in the mathematical note. The
consolidated all-dependency rebuild is recorded separately in
extension-reproduction.json and extension-all-axioms.json.

The self-contained extension archive includes finite/derive_spectrum.py and its
stdlib-only adapters. These independent numerical cross-checks do not replace
the all-parameter Lean proofs. The archive also includes the fresh sanitized
build/replay log, complete axiom closures and source/cache digests.

Submission and scope
The existing topic/scope/eligibility inquiry is
https://github.com/TheJustinSunPrize/awards/issues/5130
We request review of the primary count and guidance on whether the separate
extensions should be considered together or registered separately. A MathDB
reference is not itself a confirmed prize-program mapping. Global novelty,
priority, contributor/recipient eligibility, problem acceptance and any award
remain subject to external review. No global minimum construction, improved
quadratic leading coefficient, or solution of Frankl's conjecture is claimed.
The source construction and conjecture remain credited to Kengbo Lu and
Abigail Raz. Development used OpenAI Codex under the direction of renxuhang.
