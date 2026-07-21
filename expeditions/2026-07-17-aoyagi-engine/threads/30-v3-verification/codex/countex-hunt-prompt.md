<task>
You are an adversarial mathematical reviewer. HUNT FOR COUNTEREXAMPLES to the frontier statements of a Lean 4 blueprint (v3) formalising Aoyagi's DLN RLCT result. v2 of this blueprint died exactly this way: two "frontier" lemmas were FALSE AS STATED (a change-of-variables lemma over an unconstrained chart record — killed by g=(xy²,x²y), jacWeight(1,1) vs |det Dg|=3x²y², asserting 1=2/3; and an axis-only monomial rule missing coupled valuations). v3 claims to fix both with certificate fields and guard hypotheses. Your job: try to BREAK v3's statements the same way — find a structure satisfying ALL stated hypotheses where the conclusion FAILS. A sorried statement is expected (it's a blueprint); a FALSE sorried statement is the kill.

READ (Lean, read-only, checkout at the reviewed commit):
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/IdealInvariance.lean   (Object A)
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/MonomialRLCT.lean      (Object C)
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/ProductResolution.lean (Object B: the `Resolution` record + CoV)
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/Engine.lean            (Object D, fully proved)
- /tmp/aoyagi-v3-review/lean/DLNFibre/Core/Aoyagi/Order.lean             (Object E, deferred node)
- /tmp/aoyagi-v3-review/lean/DLNFibre/DLN/Aoyagi/LearningCoefficient.lean (corollary + existence monument)
THE PAPER: /tmp/aoyagi-v3-review/theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex (its Lemma-1 sign is corrected: ≤ for G ∈ ⟨F⟩).

PRIORITY TARGETS (hunt hardest, in order):
1. `rlctAt_sumSqFam_eq_wrlctAt` (ProductResolution) — the CoV frontier over the certified `Resolution` record. The record now carries: `hg0 : g 0 = x₀`; `hg_analytic : AnalyticOnNhd ℝ g univ`; `hcover : ∀ᶠ w in 𝓝 x₀, ∃ u, g u = w`; `hg_inj : InjOn g excepᶜ` with `excep` null; `hjac : ∀ᶠ u in 𝓝 0, |jacDet g u| = jacWeight jac u * |unit u|` with `unit` continuous, `unit 0 ≠ 0`; plus divisor min-attainment fields. QUESTION: are these fields SUFFICIENT for the local rlct equality rlctAt(∑F²)(x₀) = wrlctAt(weight)(∑(F∘g)²)(0)? Probe specifically: (a) NON-PROPERNESS — `hcover` gives local surjectivity but nothing bounds g⁻¹(small ball); can mass escape to infinity in the u-space and break one direction of the integrability transfer (e.g. a chart whose domain is all of ℝⁿ with |det Dg| decaying at infinity)? Does the LOCAL nature of both sides (germ at 0 / at x₀) save it — i.e. is wrlctAt genuinely local-at-0 in their definition (READ the actual `wrlctAt`/`rlctAt` definitions in the files)? (b) the unit certified only NEAR 0 (∀ᶠ) while `hcover` is a neighbourhood of x₀ — any gap between "g covers a nbhd of x₀" and "g restricted to a small ball at 0 covers a nbhd of x₀"? A counterexample where the covering points u_w do NOT tend to 0 as w → x₀ (so the local chart at 0 misses part of every neighbourhood of x₀) would be the v2-class kill.
2. `monomialSumSq_wrlctAt_eq` (MonomialRLCT) — the boxed rule NOW GUARDED by `hchain : ∀ k d, e k₀ d ≤ e k d` (a dominant/dividing monomial). Is the chain hypothesis SUFFICIENT for the weighted threshold to equal the axis formula? Probe: 2–3 variable weighted examples WITH a valid chain where the Newton-polyhedron/coupled valuation still beats the axis value (can the WEIGHT couple what the monomials don't?). Compute at least one exact example by hand/scaling argument.
3. `exists_coreResolution` (LearningCoefficient) — the existence monument, guarded by `0 < N`, `∀ k, 0 < d k`. SATISFIABILITY probe: any width vector where NO structure with ALL the Resolution fields (single chart + hcover + chain + min-attainment + unit-Jacobian certificate) can exist? (The paper claims the construction; you are checking the Lean record doesn't accidentally demand MORE than the construction provides — e.g. `hg_analytic` on ALL of univ vs the construction's chart domain; `hcover` full-neighbourhood vs the construction covering only a.e.; `hchain` GLOBAL vs per-chart.)
4. `rlctAt_mono_of_ae_le` (IdealInvariance) — a.e.-domination monotonicity. Sanity: fine a.e. since integrals ignore null sets? Check their exact statement (which filter, which measure).
5. STRUCTURAL: count the REAL sorries per file (excluding comment/docstring mentions) — the architect claims 15; raw token count is 19. Verify D (Engine.lean) and E (Order.lean) genuinely carry ZERO sorries and that the two negative guards (`not_divChain_coupled_example`, `no_unit_forces_axis_jac_coupled`) are PROVED (no sorry in their proofs).
</task>

<output_contract>
1. Per priority target 1–4: VERDICT — SOUND-as-stated (with the reason the hypotheses block your attacks) or COUNTEREXAMPLE/GAP (with the explicit structure + the arithmetic, v2-style). Mark each claim VERIFIED (you read/computed it) vs INFERRED.
2. Target 5: the real sorry counts + the two guard-proof confirmations.
3. Any OTHER false/vacuous/over-strong statement you find (bar-iv scan of every sorried statement).
4. OVERALL: does v3 clear the "no false frontier statements" bar, or ranked kills, most severe first.
</output_contract>

<grounding_rules>
Read the actual Lean definitions (esp. `rlctAt`, `wrlctAt`, `jacWeight`, `Resolution`) before judging any statement — do NOT assume the definitions from the names. Compute counterexample candidates exactly (scaling/polar arguments suffice; show the exponent arithmetic). The paper's line-156 sign is corrected (≤); do not report it. Distinguish "false as stated" (kill) from "harder than labeled" (finding) from "style" (ignore).
</grounding_rules>
