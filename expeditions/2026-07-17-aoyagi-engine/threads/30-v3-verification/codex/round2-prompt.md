<task>
ROUND 2 of an adversarial counterexample hunt on a Lean 4 blueprint (v4, commit 749b336d4) for Aoyagi's DLN RLCT result. Round 1 (on v3) produced verified kills: (a) Object-A lemmas false via the `Real.rpow 0^(-c)=0` junk (a dominated K vanishing on a half-line); (b) the single-chart CoV false (`K=x²+y⁴`, `g=(u,uv)`: 3/4 ≠ 1); (c) single-chart cover uninhabitable at blow-ups. v4 claims to fix all three: A now guarded by `LocallyNullZeros`; B is now an ATLAS (`Chart` per-chart certificate + `Resolution` with compact source domains `dom c` and an a.e.-localizing cover `hcover : volume (U \ ⋃ c, g_c '' dom c) = 0`); the CoV is `rlctAt_sumSqFam_eq_iInf_charts` (min over charts). Your job: BREAK v4's statements — a structure satisfying ALL stated hypotheses where the conclusion fails.

READ (checkout at 749b336d4):
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/MonomialRLCT.lean
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/Engine.lean
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/Order.lean
- /tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean
Paper: /tmp/aoyagi-v3-review/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex (Lemma-1 sign corrected to ≤). Banked defs: /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Analysis/RLCT/Basic.lean (rlctAt/negPow), and for target 5: /tmp/aoyagi-v3-review/lean/DLNFibre/DLN/RLCT/Validate/DeepestMinRlct.lean + the ParamsFlat module (locate it).

PRIORITY TARGETS:
1. **`rlctAt_sumSqFam_eq_iInf_charts` (the atlas CoV) — hunt hardest.** Read the `Chart` and `Resolution` records field-by-field FIRST. Attack angles: (a) ADVERSARIAL REDUNDANT CHART — can I add to a good atlas an extra chart (satisfying every per-chart field, image possibly a sliver already covered by others) whose per-chart threshold is STRICTLY SMALLER than the true rlctAt, dragging the iInf below the truth? What field (injectivity? the per-chart ideal identity `hideal_*`? the chain? hg0?) blocks an adversarial low-threshold chart — check whether injectivity per chart survived the v4 refactor at all, and whether WITHOUT it an infinite-multiplicity chart makes the pullback diverge spuriously (threshold too small → iInf too small → equality false). (b) the ≥ direction: does the a.e.-compact-cover genuinely bound rlctAt below by the min (mass escaping between the images? overlap over-counting is harmless for divergence but is UNDER-counting possible — a divergence downstairs not seen by any chart because it sits on the measure-zero uncovered set + chart boundaries)? (c) the ≤ direction (`rlctAt_sumSqFam_le_chart`, PROVED): read its actual statement — does it say what the equality needs (iInf ≤ …) or is it a different inequality than advertised?
2. **The guarded A statements** (`rlctAt_mono_of_eventually_le` + the two germRepresents ≤ + both two-sided eqs, all with `LocallyNullZeros`): is the guard SUFFICIENT, or is there a residual junk path (e.g. K with null zero set but the comparison constant degenerating along a sequence; or the weighted form's W vanishing on a positive-measure set — is W guarded too)?
3. **`no_unit_forces_axis_jac_coupled`** with the new `∀ᶠ u in 𝓝 0` quantifier: still true?
4. **`coreGen` concreteness + `coreReduction`**: read `coreGen`'s definition against the actual `mult`/`lossDLN` — is it genuinely the flattened ∏C entry family (indices right, e 0 = 0 case right)? Is `coreReduction`'s statement (rlctGlobal (lossDLN d 0) = ofReal-bridge rlctAt (∑ coreGen²) 0 — read the exact form) sound per the paper's Thm 4 + flatten?
5. **Banked-signature reuse check** (the architect did NOT re-verify): does `deepest_le_of_homogeneous_core` (DeepestMinRlct.lean:157) + the ParamsFlat flatten actually have the signatures `exists_flatten`/`coreReduction` presuppose (general widths, or (2,2,2)-only)? Report the exact signatures.
6. **Atlas inhabitation** (the architect's positive test): verify the claim that the ℝ² blow-up (two charts (u,uv)/(uv,v)-style, compact boxes) satisfies EVERY `Chart` + `Resolution` field for the ideal ⟨x,y⟩ — check each field, esp. hjac (per-chart Jacobian certificate), the chain, and the a.e.-cover with compact domains.
</task>

<output_contract>
Per target 1–6: VERDICT — SOUND-as-stated / COUNTEREXAMPLE (explicit structure + arithmetic) / GAP (what's missing) / MISMATCH (for 5: the exact signature deltas). Mark VERIFIED vs INFERRED. Then OVERALL: does v4 clear the "no false frontier statements" bar — ranked kills first if not.
</output_contract>

<grounding_rules>
Read the actual Lean record fields and definitions before judging — do NOT assume from names or from my summary (the summary may be wrong about what survived the refactor; the FILES are the truth). Compute counterexamples exactly. Distinguish false-as-stated (kill) / gap (insufficient-hypotheses risk) / harder-than-labeled (finding) / style (ignore).
</grounding_rules>
