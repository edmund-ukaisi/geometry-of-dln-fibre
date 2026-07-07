# #120 re-adjudication — the ∀-L grouped deepest-gauge diffeo

**Seat:** pen-and-paper (witness). **Question:** is `deepest_gauge_squeeze_exists`
(#120, `DeepestGaugeChart.lean:353`, the L≥3 grouped diffeo) a genuine research wall,
or does it lift structurally from the now-validated L=2 machinery?

## VERDICT: A — APPROACHABLE (bounded structural/recursive lift). Confidence: high.

Not an intrinsic L≥3 wall. The L=2 construction is a genuine template; the general-L
version reuses the same `rlctAtOn_comp_localDiffeo` (IFT) machinery on a recursively-defined
absorbing diffeo. The prior "research-grade / roadmap" verdict was conservative — it predates
(i) the exact recursive-LDU verification and (ii) the observation that the absorbing diffeo has
`dΨ(0)=I` for free (the vanishing-core factor), so no L=2-style core-independent inverse is needed.

## The gap is exactly 3 sorries (all in `DeepestL2Wiring.lean`, L≥3 arm)

- `:913, :916` — interior-frame triviality `Qf s = 1`, `Pf (s+1) = 1`.
- `:1058` — `hstep2`, the grouped-G0 diffeo bridge `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)`.

The general-L loss-side is ALREADY sorry-free: `DeepestGaugeConstruction.lean` has zero tactic
sorries (AxCheck.lean:149-152); `deepest_loss_squeeze` proves the Score-sandwich
`loss ≍ Sreg + frobSq(Rcore)` for all L, consuming only `hinterface` (the interior-frame hyp).
So "h1 lifts by grouping" is DONE; only "h2" (Score↔coreΦ) + interior frames remain.

## DATA (exact algebra — my own, independent of Codex)

`codex/schur_ldu2.py`, `codex/psi_diffeo.py`, `codex/psi_diffeo_deep.py`, `codex/schur_ldu_recursion.py`.

- **F1** `Sch(A·B) = S_A·(I−K)·S_B`, `K = B₂₁(AB)₁₁⁻¹A₁₂`, `(I−K)(0)=I`: HOLDS, r,M∈{1,2}
  (exact-rational near-0). Codex ALSO gave a clean block-LDU proof (no commutativity). AGREE.
- **F2** `Rcore = S₀(I−K₁)S₁(I−K₂)S₂···(I−K_{L−1})S_{L−1}`, `K_k=(C_k)₂₁(P_k)₁₁⁻¹(P_{k−1})₁₂`,
  each analytic, `(I−K_k)(0)=I`: HOLDS, matrix/non-commutative, L=3,4, r,M∈{1,2}. AGREE.
- **F5 (the crux)** absorbing diffeo `Ψ: S_i ↦ (I−K_i)S_i` gives `Score = coreΦ∘Ψ` and
  `dΨ(0)=I` exactly:
  - L=3, r=1, scalar core: dΨ(0)=I on 4 core coords, 0 on all reg dirs — True.
  - **L=3, r=1, 2×2 NON-SCALAR core**: dΨ(0)=I on all 12 core coords, 0 on reg — True.
  - **L=4, r=1, scalar core**: dΨ(0)=I on all 4 core coords, 0 on reg — True.
  Holds *even though K₂ depends on the cores* (via `T₁=S₁+Z₁(1+X₁)⁻¹Y₁`): every cross-term
  carries the vanishing factor `S_i(0)=0`. The non-scalar L=3 + scalar L=4 confirmations convert
  the L=2-analogy into an ∀L structural claim.

DATA vs INTERPRETATION: F1/F2/F5 are DATA (exact-symbolic/rational). The `(P_k)₁₁` invertibility
on a nbhd is my own elementary reading (`(P_k)₁₁(0)=I_r` since each `C_s(0)=blockdiag[I_r,0]`;
continuity ⇒ invertible near 0), corroborated by Codex — not Codex-only. `Sreg∘Ψ=Sreg` is a
construction fact (Ψ fixes reg/spec). **No load-bearing step rests on Codex's word alone.**

## L=2 → L≥3 route DIVERGENCE (the one genuine difference)

At L=2, `K` is core-INDEPENDENT (`deepestEFull_coreConstant`), giving an explicit fibrewise-linear
inverse `S₁↦(I−K)⁻¹S₁`. At L≥3, `K_i` (i≥2) is core-DEPENDENT (F3), so that explicit inverse is
unavailable. Resolution (mine + Codex, agree): use the full **inverse function theorem** — `Ψ` is a
global-smooth self-map (after a cutoff) with `HasStrictFDerivAt Ψ id 0`, so it's a local diffeo at 0.
This is proof-packaging, not new math — and the L≥3 arm ALREADY deploys the IFT pattern
(`hTilde`/`deepestEFull_deriv`/`HasStrictFDerivAt … eTilde 0`, DeepestL2Wiring.lean:825-884).

## REACHABILITY of the statement AS WRITTEN (the crux the controller flagged)

**Provable by the IFT route with NO reshaping.** The `DeepestGaugeChart` structure fields are
RLCT EQUALITIES (`coreAbsorb_rlct`, `regAbsorb_rlct`, `loss_squeeze`) + a bare `regStraighten :
DeepestSplit → DeepestSplit` continuous function. NO field bakes in a fibrewise-linear inverse —
the diffeo lives INSIDE the equality proofs. `hstep2` is a plain RLCT equality
`rlctAtOn Φscore = rlctAtOn Φcore`, which the IFT-diffeo route produces directly. The consumer
`rlctAt_deepest_le_of_optimal` (Skeleton.lean:1172, via `deepest_squeeze_transport`) reads the
fields as equalities and needs only `Nonempty (DeepestGaugeChart …)` — unaffected. No signature
change, no consumer churn.

## Formaliser runway — the 4 sub-lemmas (each has an L=2 template)

1. **Recursive Schur-product LDU** (F1→F2): generalize the banked 2-factor `schur_product_ldu` to
   L factors by induction. The load-bearing algebra; hits the documented `prodAux`/dependent-width
   cast-grind (lean/CLAUDE.md) — plausibly multi-tide but bounded.
2. **Analyticity/domain**: `I+X_s` and `(P_k)₁₁` invertible near 0 ⇒ `S_s`, `K_k`, `Ψ` smooth
   (matrix-inverse ContDiff where invertible). A cutoff makes Ψ globally `ContDiff ⊤` (the
   established `regStraightenOf2` pattern — needed because sub-lemma 4 asks for global ContDiff).
3. **Derivative of Ψ**: `Ψ(0)=0`, `HasStrictFDerivAt Ψ (ContinuousLinearMap.id) 0` (dΨ(0)=I,
   DATA-verified). Template: `deepestEFull_deriv` / the `hTilde` strict-deriv lemmas.
4. **RLCT bridge**: **the interface ALREADY EXISTS and is general enough** —
   `rlctAtOn_comp_localDiffeo` (`DeepestRegAbsorbIFT.lean:283`) is universe-polymorphic
   `{M : Type*}`, takes a global-`ContDiff ⊤` `f` + invertible strict-deriv `e : M ≃L[ℝ] M` +
   `f wstar = wstar`, and concludes `rlctAtOn(F∘f) = rlctAtOn F` via the IFT internally. Apply with
   `f = Ψ`, `e = id`. **NOT a new interface piece.** Separately, the interior-frame gap (sub-3
   above) needs a `DeepestPivotFrame`-chooser refinement that picks identity interior frames —
   valid because `deepestPoint`'s interior layers ARE `blockdiag[I_r,0]` (Skeleton.lean:972-975,
   `IsDeepLayers` clause 3). Bounded engineering, no new math.

## Most likely thing to break it (honest)

Not the mathematics — the Lean **formalisation labor**: sub-lemma 1's block-matrix
Schur-of-product induction is where the dependent-width cast-grind bites (could be a multi-tide
build even though bounded). Second watch-item: the **endpoint-frame decoration** of S₀/S_{L−1}
(9th catch, discuss-at-close.md:413-426) — the w-independent O(1) frames Pf₀/Qf_L must be carried
as constant units through Ψ's endpoint components. Neither is a wall.

## Next step to settle the open part

Build sub-lemma 1 (the L-factor recursive Schur LDU, inducting the banked 2-factor
`schur_product_ldu`) first — it's the load-bearing identity; sub-lemmas 3-4 then follow the
`deepest_diffeo_bridge_L2_assembled` template.

Decorrelated Codex (xhigh) reached verdict A independently, re-derived F1, found no L≥3-only
obstruction: `codex/hstep2-lift-prompt.md`, `codex/hstep2-lift-answer.md`.
