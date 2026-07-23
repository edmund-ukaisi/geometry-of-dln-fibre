# §-note: AUTHORITATIVE battery on arch-C-4's F₂ render @ REBAKE2 1a113e4db

Every row on the EXACT rendered `canonNormalizationOf` (3 branches), transcribed verbatim from
`MonumentAtlas.lean:906-966`, NO hand model (charter §3). Script: `verify/f2_render_battery.py` (exit 0).
Witnesses `(2,2,2,2)`/`(2,3,2)`/`(2,3,2,2)` + `(3,2,2,2)`/`(3,3,3,2)` for the S≥1 branch-(iii) rows.

The rendered def (verified against the file): branch (i) `q.1.1=S ∧ row≠a ∧ col≠b ∧ cleared≤row,col →
−w_{row,b}·w_{a,col}` (interior Schur); (ii) `q.1.1=S+1 ∧ col=a → +∑_{i≥cleared,i≠a} w_{i,b}·A^{(S+1)}_{row,i}`
(+γ output recoord `A_{S+1}·Q₁⁻¹`, scoped); (iii) `q.1.1+1=S ∧ row=b → +∑_{k≥cleared,k≠b} w_{a,k}·A^{(S−1)}_{k,col}`
(`Q₂⁻¹·A_{S−1}` input recoord, scoped, S≥1). r4Clear is NOT in the fold (boostReady-proof device only).

Criterion correction (from the Lean StepInv, `PrincipalInv.lean:82`): StepInv is a CONTINUOUS-quotient
DIVISIBILITY `(Fᵢ∘g)=∑ q(b·resid)`, `q` ContinuousOn — NOT polynomial entry-ideal-equality (§8(j)). So the
recursion closes by the det-1 CoV `g=foldG` (the 3 shears), not coreGen entry-equality.

## Rows — 5 PASS, row 3 is a documentation nuance (not a soundness issue)
| row | result |
|---|---|
| **1. recursion CoV (3-shear det-1)** | **PASS** — det J = 1, triangular (each branch reads only UNWRITTEN coords), all witnesses incl. S=1 (all 3 branches). The recursion closes by the unipotent CoV; the ideal rides it (§8(j)). [Diagnostic, expected-fail per §8(j): polynomial coreGen entry-ideal-equality — fails, correctly not the criterion.] |
| **2. block-form / boostReady** | **PASS** — residual multilinear (`deg_u₀₀₁=1`, `deg_u₀₁₀=1`), all witnesses. `Deg1SupportedOn ed.center` holds. |
| **3. scope** | **NUANCE (see below)** — the render's foldResid is `deg_u₀₀₁ ≤ 1` BOTH scoped and unscoped (NO `u₀₀₁²`). The scope changes VALUES (keeps E_J col-0 free of the pivot-row coord `u₀₀₁`), NOT the boostReady degree. |
| **4. on-frame polynomiality** | **PASS** — every branch displacement is polynomial (readEntry products/sums, no division / no `A₁⁻¹`). |
| **5. corner (S=0)** | **PASS** — branch-(iii) VACUOUS (guard `L+1=S=0` impossible); only (i)+(ii) fire; det-1. The corner pivot-row = the global `GL_{d₀}` end-factor gauge (§9 ruling A). |
| **6. interior (S=1)** | **PASS** — all three branches fire; branch-(iii) genuinely ACTIVE (writes layer-`(S−1)` row-`b` coords, the input recoord); det-1. The path `(2,2,2,2)`-all-corner did not exercise. |

## Row 3 — the scope nuance (fidelity-positive; documentation-imprecise; flag for the elder)
The render's foldResid is `coreGen(3-shear fold)` with r4Clear NOT applied (branch (i) does the interior
Schur, cross KEPT). On this object, all four `(2,2,2,2)` reuse-node entries are `deg_u₀₀₁ ≤ 1`, scoped AND
unscoped — there is NO `u₀₀₁²`. The docstring's "the UNSCOPED +γ-paired sum STILL gives the inter-edge
`u₀₀₁²` (f2_paired_boostready, all witnesses)" is the CLEAR-model (`f2_paired`, block literally cleared to
diag) behavior — it does NOT hold for the RENDER's foldResid (no literal clear in the fold). What the scope
actually does on the render: it keeps the E_J (col-0 / cleared column) FREE of the pivot-row coord `u₀₀₁`
(scoped col-0 has `deg_u₀₀₁=0`; unscoped col-0 carries `u₀₀₁·u₀₁₀·u₁₀₀` terms, still degree-1). So the scope
is the faithful choice (the cleared column should not carry the pivot-row coord — her accumulated `Q₂'⁻¹`
current-chart semantics), but the STATED justification (`u₀₀₁²`) is about a different object. Net: the scope
is correctly KEPT (fidelity to the clean E_J), boostReady holds either way; the docstring's `u₀₀₁²` phrasing
should read "keeps E_J free of the pivot-row coord" for the render's object. NOT a merge blocker — a
documentation-precision note. (The whole `u₀₀₁²`/§7/F₂ arc was about the clear-in-fold models; the §9
render's three-home design — recursion = shears only, clear = boostReady device — SIDESTEPS it, which is
exactly why the render is cleaner. The `u₀₀₁²` never arises in the render's actual recursion.)

## Verdict
The F₂ render @ 1a113e4db PASSES the authoritative battery on all soundness rows (recursion CoV det-1;
boostReady multilinear; polynomial; corner branch-(iii) vacuous; interior branch-(iii) active + det-1). The
one nuance (row 3) is a documentation-precision point on the scope's stated justification, fidelity-positive
and not a blocker. My half of the merge gate is GREEN; seat-L4D's 11-item slot-confirm + the elder's
delta-read remain.
