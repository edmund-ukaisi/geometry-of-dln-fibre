<task>
You are an independent mathematical reviewer. Cross-check and sense-check a Lean 4 formalization BLUEPRINT of Aoyagi's deep-linear-network (DLN) RLCT result against the (corrected) Aoyagi paper. This is a SKELETON — typed, `sorry`-carrying theorems where the STATEMENTS matter, not the proofs. Two jobs: (1) FIDELITY — do the Lean statements faithfully transcribe Aoyagi's actual theorems? (2) MATH SENSE-CHECK — is the decomposition mathematically sound and honest (no vacuous or circular statements)?

BACKGROUND. The target theorem: rlct(square-Frobenius DLN loss) = ½·codim ("DLNs are mildly singular"). A blueprint of objects A–E + a corollary was built; a fidelity review FAILED it because the resolution was "dodged" — an opaque field `transfer` asserted an rlct-equality with NO geometric constraint on the resolution divisors `b`, making object B near-vacuous ("∃ some b with equal rlct"), object D circular (logically = the engine conclusion), and object A orphaned (off the dependency cone). It was then REPAIRED. You are the INDEPENDENT cross-check on whether the repair genuinely fixes this.

READ THESE (Lean modules, read-only):
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean   (Object A: Aoyagi Lemma 1 two-sided RLCT ideal-invariance + a weighted RLCT `wrlctAt`)
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/MonomialRLCT.lean   (Object C: the boxed monomial-RLCT rule)
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean   (Object B: `⟨∏C⟩=⟨diag b⟩` resolution — the 3-field `Monomialisation` record + the DERIVED `transfer`)
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/Engine.lean   (assembly + Object D: `boxedRLCT_eq_half_cCodim`)
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/Core/Aoyagi/Order.lean   (Object E: order ρ, deferred)
- /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-af915257641e569b7/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean   (the corollary rlctGlobal(K^DLN_0)=C/2)

THE PAPER: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/aoyagi-engine/root/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex
IMPORTANT — the reproduction had a SIGN TYPO near line 156 (printed `≥`; the correct direction, matching Aoyagi's original Lemma 1 and the built `rlctAt` convention `∫|F|^{-c}`, is `≤`: λ(∑G²) ≤ λ(∑F²) when G ∈ ⟨F⟩). Cross-check against the CORRECTED reading (`≤`).

THE STRUCTURE you are checking (post-repair):
- A: two-sided `rlctAt(∑fᵢ²)` depends only on the ideal ⟨fᵢ⟩ (Lemma 1); + a weighted variant `wrlctAt` (Def-1 RLCT with a nonneg weight = the resolution's change-of-variables Jacobian).
- B: `Monomialisation d` carries 3 fields — (1) `ideal_identity`: ⟨diag b⟩ = ⟨(∏C)∘g⟩ (the geometric Cases-1&2 resolution); (2) `vanish_spec`: kⱼ = minᵢ (b i j); (3) `divisor_spec`: {jacⱼ+1} ranges exactly over the QIP-codim values {Gqip d e : e ∈ qipFeasible}. `transfer` (rlct F = rlct of the diagonal monomial) is DERIVED (no sorry) from a proper-map-CoV frontier ∘ A's weighted ideal-invariance applied to `ideal_identity`.
- C: Aoyagi's boxed rule — the weighted monomial RLCT = ⨅ⱼ axisRatio(jacⱼ)(kⱼ).
- D: `boxedRLCT_eq_half_cCodim`: ⨅ⱼ(jacⱼ+1) = qipMin = cCodim (Core-native, via `cCodim_eq_qipMin`).
- Corollary: rlctGlobal(K^DLN_0) = C/2 (Aoyagi Thm 4, deepest point).
</task>

<output_contract>
Structured, per-question:
1. FIDELITY (per object A / B / C / D / corollary): does the Lean statement match Aoyagi's actual claim? Cite the paper location. Flag any mis-transcription, over-claim, or under-claim.
2. MATH SENSE-CHECK:
   (a) Is B's `ideal_identity` genuinely NON-VACUOUS — does a generic b FAIL it (does it really pin b to the product ideal ⟨∏C⟩)?
   (b) Is D's `boxedRLCT_eq_half_cCodim` STATEMENT genuinely NON-CIRCULAR — a real min-over-QIP-image computation, NOT logically equivalent to the engine conclusion rlct=½cCodim?
   (c) Is A's weighted-RLCT ideal-invariance the CORRECT tool, and is `transfer` honestly DERIVED (not silently re-assuming the rlct-equality)?
   (d) Is the proper-map-CoV frontier a SOUND bridge between the tuple-space RLCT and the resolution-space RLCT (does the monomial Jacobian weight belong there)?
   (e) Any mathematical unsoundness, vacuity, circularity, or "smell" in the A–E decomposition.
3. VERDICT: does the repaired blueprint faithfully + soundly capture Aoyagi's mechanism, or are there load-bearing defects? Ranked, most severe first.
</output_contract>

<grounding_rules>
Read the actual Lean files and the paper before claiming anything. Flag each finding as VERIFIED (you read it) vs INFERRED. The worked.tex:156 `≥` is a KNOWN typo — treat `≤` as correct; do NOT report it as a Lean error. A sorried statement (frontier leaf) is EXPECTED — judge the STATEMENT's fidelity/soundness, not the missing proof. Distinguish a genuine defect (false/circular/vacuous statement, infidelity to the paper) from a stylistic nit.
</grounding_rules>
