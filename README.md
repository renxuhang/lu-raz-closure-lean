# Lu--Raz count proof and separate extensions

The primary submission is the exact count for the completed original Lu--Raz family.
Read [PROOF.txt](PROOF.txt), [STATEMENT_CORRESPONDENCE.txt](STATEMENT_CORRESPONDENCE.txt),
and the subsequent [author-program evidence](SOURCE_PROGRAM_EVIDENCE.txt).
The [original fixed version](https://github.com/renxuhang/lu-raz-closure-lean/tree/e12a3abd3fb93aedd4816e780a1caf1156e45c1a) remains unchanged.

The separately labeled three-row/six-row research now has an [English overview](README_EXTENSION.txt),
[mathematical proof](PROOF_EXTENSION.txt), [statement correspondence](STATEMENT_CORRESPONDENCE_EXTENSION.txt),
and [attribution disclosure](ATTRIBUTION_EXTENSION.txt). The six-row result includes the exact 27/16 difference groups,
full frequency spectrum, extrema, thresholds and total weight for every integer q>=4.

A fresh project-cache-free build compiled all 341 extension dependency modules;
all 8720 explicit theorems passed the transitive axiom audit; all 341 modules
passed replay with Lean's bundled kernel. See [the complete record](extension-reproduction.json).
The historical staged reports and this consolidated verification are distinct.
No external human mathematical review or second independent kernel is asserted.

With Lean 4.35.0 already installed, run:

```
python -X utf8 reproduce.py --toolchain leanprover/lean4:v4.35.0
python -X utf8 reproduce_extension.py --toolchain leanprover/lean4:v4.35.0
```

The first command reproduces the original primary proof; the second builds the full extension graph.
Each checks its own manifest and performs its recorded audits. No dependencies are downloaded.
The self-contained submission archive additionally contains both primary and extension sources,
independent numerical scripts, and full sanitized verification logs.

The [existing inquiry #5130](https://github.com/TheJustinSunPrize/awards/issues/5130) requests technical review and topic/scope/eligibility guidance.
Acceptance, global priority, contributor eligibility and any reward remain pending.
The extensions retain the quadratic leading coefficient and make no global optimality claim.
Original construction/conjecture credit belongs to Kengbo Lu and Abigail Raz;
new development used OpenAI Codex under the direction of renxuhang.
