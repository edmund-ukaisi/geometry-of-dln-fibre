# backbone-cert — the (S,J)-descent RECURSION BACKBONE (reduce-to-shorter-chain), designed to bedrock

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`, backbone commission. **Date:** 2026-07-16.
**NO Lean.** Design only (reduction + CoV + exponent bookkeeping + banked pieces + the unbuilt core + traps).
Verified: exact-ℕ gate scan (`scripts/kill_check`-style, reliable), the satred/D-cert density work, an
Explore full-body structure map of the Lean chart-tree, and a **decorrelated Codex xhigh** soundness audit
(`codex/backbone-{prompt,answer}.md`) with my conclusion WITHHELD. The single central piece — every arm
(interior, edge, deep) consumes it.

---

## ★ VERDICT

**The naive one-line backbone — "split off the corank charge `peelCharge/2`, absorb the invertible pivot
`P`, land in `routeMLayerBoxIntegral(redChain t M)` at the shifted exponent" — is NOT sound as stated**
(decorrelated-Codex-verified, two independent obstructions). **The VALID backbone is the REFINED DECORATED
JOINT DESCENT** — retain the coupled front factor `[P|B₁₂]·[z₀;A_cor]`, stratify its minors/ranks, and carry
the marginal logs / Gram weights into a DECORATED shorter-chain comparator (`cornerComparator(redChain t M)`,
NOT `routeMLayerBoxIntegral(redChain t M)` directly), then the decorated recursion + the arity−1 IH. This is
exactly the banked `deeperFlag_shell_le` route, gated by the two unbuilt bricks **F** and **D**. **No `(□)`
wall** — the true chart integral is finite (`⊆ RMBTF(M)`; Codex "the true integral may still be proved finite
by a refined joint descent") — but the reduction is NOT the one-liner; "1 IH call" (edgeasm) / "single-chain
verified" (my earlier gloss) both glossed the pivot singularity + the corank edge. The exponent gate is safe.

---

## 1. The route (Explore full-body map; the plumbing is BANKED)

`gammaPeelIntegral M t ρ κ c'` (`RouteMSJResolution:517`; outer `∫ A' ∈ paramsBoxM(tailChain M)`, inner
`∫ A₀ ∈ matBox ∩ pivotChart ρ κ`, integrand `frobSq(rmatMul A₀ (prod(tailChain M) A'))^{−c'}`) descends:

1. `routeMLayerBoxIntegral_front_split` (`RouteMSJResolution:461`, BANKED) — `routeMLayerBoxIntegral M` =
   outer-tail × inner-front-factor; `gammaPeelIntegral` = this with the inner ∩ `pivotChart`.
2. `gammaPeelIntegral_schurShearFree_eq` (`RouteMSJFreedPeel:78`, BANKED equality) — the freed-Γ triple
   `∫_{A'}∫_{x∈outerDom t a b}∫_Γ freedSchurLoss^{−c'}`, `freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ +
   Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹B₁₂Q_b` ⟹ **`P·Q̃ₚ = P·Q_p + B₁₂·Q_b = [P|B₁₂]·[Q_p;Q_b]`** (the coupled
   front factor, full row rank t via P — the key object).
3. shell cover `offSector_cover_le` / `singularShell_iUnion` (BANKED) → `∑ shellSpineIntegrand`.
4. **`deeperFlag_shell_le` (`RouteMSJDeeperFlagCore:750`) — the reduce-to-shorter-chain, GATED:**
   `shellSpineIntegrand M (t+j) κ ε … c' ≤ C · cornerComparator(redChain (t+j) M) k jc . integral(c' −
   peelCharge M (t+j)/2)`, `C<⊤`, comparator `adm`-admissible. **Target is the DECORATED
   `cornerComparator(redChain)` (`decLoss = commonDivisor²·frobSq(prod(redChain) z)` — the reduced box
   integrand × the P-radial exceptional monomial), NOT `routeMLayerBoxIntegral(redChain)` directly.**
5. decorated recursion (`radialAttach` / `SJDecoration.integral` / `decoratedBoxThresholdFinite_trivial_iff`,
   BANKED) links `cornerComparator(redChain).integral` to `RouteMBoxThresholdFinite(redChain t M)` — the
   arity−1 IH (the skeleton's `hIH`).

**BANKED:** all of 1–3, the arithmetic gate (§4), the finite covers, `cornerComparator` + `cornerComparator_adm`,
the decorated recursion. **UNBUILT:** step 4's two bricks (§3) + the good-chain scoping (waist base absent).

## 2. Why the naive one-line backbone FAILS (decorrelated Codex, two independent obstructions)

**(O1) The bare invertible pivot is INSUFFICIENT — it adds a genuine lower-rank singularity, not just a CoV
artifact.** Codex's explicit counterexample, **INDEPENDENTLY RE-VERIFIED by me** (exact-ℕ minAdm/gate +
analytic power-law criterion + scipy.quad, NO MC — `scripts/backbone_counterexample.py`; reproduces exactly:
gate SAFE, `2q=3/2`, `∫_ε^1 p^{−3/2}dp = 2(ε^{−1/2}−1)→∞` while `∫_{disk}‖z‖^{−3/2}dz<∞`, so the naive
factorized model `(DIVERGES)·(FINITE)=∞`): `M=(2,2,2), t=1` (`minAdm=3, d_t=peelCharge=1, R_t=minAdm(redChain)=2`),
`c'=5/4<3/2 ⟹ q=3/4<1=R_t/2` (gate SAFE), yet
`∫_{p≠0, z∈[−1,1]²} ‖p·z‖^{−2q} dp dz = (∫₀¹ p^{−3/2}dp)(∫‖z‖^{−3/2}dz) = ∞` — the reduced z-box is finite but
the **bare pivot `p→0` gives a real `p^{−2q}` divergence**. So "absorb the invertible pivot, land in
`routeMLayerBoxIntegral(redChain)`" is FALSE. The `|det P|^{−M₂}` is PARTLY a domain-enlargement artifact
(the shrinking image cancels it), BUT a genuine `p^{−2q}` remains. **Fix: the coupled `[P|B₁₂]·[z₀;A_cor]`
(full row rank) — but even full row rank is INSUFFICIENT (it may approach rank-drop); those regions need
minor/rank STRATIFICATION** (⟹ my satred a<u leaf / a≥u fuller lemma — the `∫_{sphere}‖Q̃ₚω‖^{−a}` finite-iff-`a<u`).

**(O2) The corank charge is NOT uniformly `ab/2` — the Wishart edge (matches my D-cert / corneradj term-for-term).**
Codex: `λ_cor = ½·min_{0≤s≤min(a,b)}[(a−s)(b−s)+sρ]` (a=M₀−t, b=M₁−t, ρ=deepTailMin). ρ≥a+b: clean `ab/2`.
ρ=a+b−1: `ab/2` but with a **LOG** (no uniform K). ρ≤a+b−2: **strict undershoot** `λ_cor<ab/2`. (Scalar edge
`a=b=ρ=1`: `∫(w+γ²y²)^{−c'} ≍ w^{1/2−c'}log(1/w)`.) Also: if `Z_deep`'s nonzero singular values are not
bounded below, even the clean-regime constant is not uniform — **the Gram weight must remain in the induction.**

## 3. The VALID backbone — the REFINED DECORATED JOINT DESCENT (Codex option 2 = the banked route)

Retain the coupled `[P|B₁₂]·[z₀;A_cor] = z̃₀` (do NOT split pivot from corank pointwise); stratify its
minors/ranks; carry the marginal logs + Gram weights into the DECORATED `cornerComparator(redChain t M)`,
then the decorated recursion → the arity−1 IH. Concretely, this IS `deeperFlag_shell_le`, whose analytic
content is the two unbuilt bricks:

**Brick D — `headSplit_domination` (`RouteMSJDeeperFlagCore:544`): the coupled, minor-stratified MEASURE
domination with finite/marginal `C`.** This is the analytic core, and its content is my **satred/D-cert**:
- The three interface hyps of `freedSchurLoss_inner_peel_lt_top` (pivot energy `>0`; `Q_bQ_bᵀ` PosDef;
  `c'>ab/2`) **FAIL POINTWISE** (null loci: w=0, rank-deficient Q_b) — so Brick D must be a **MEASURE**
  statement (integrated), NOT pointwise. The **density** (satred §3-4: the pushforward of `[P|B₁₂]·[z₀;A_cor]`)
  integrates the null loci.
- **Minor/rank stratification** (satred/D-cert, verified): `a<t` clean leaf (`corner_block_lintegral_lt_top`,
  `∫_{sphere}‖Q̃ₚω‖^{−a}` finite iff `a<t`) + `a≥t` fuller (`gammaAtom_aniso_shifted_eq` C-integral +
  `qbox_lintegral_lt_top` per-level, driven by the reduced-chain recursion). **NEVER** `qbox` on the corank
  `Q_b` at the edge (`a=q−b+1` trap).
- **Marginal logs carried** (D-cert): the corank Wishart edge `ρ=a+b−1` (⟹ `a=ρ−b+1`, the tie) gives a LOG,
  folded by the **δ-slack** (`one_add_log_inv_le_rpow`) — per-exponent, using the STRICT gate `c'<½minAdm(M)`
  (§4). The deep undershoot `ρ≤a+b−2` is the joint rank-sector (D-cert §2, min-over-strata = minAdm).
- **Gram weight carried** into the DECORATED comparator: the `commonDivisor²` monomial (P-radial exceptional
  divisor) + the `Z_deep` Gram = `cornerComparator`'s `decLoss`, handled by the decorated recursion
  (`radialAttach`), NOT discarded (Codex: "the Gram weight must remain in the induction").

**Brick F — `exists_headSplitFrame` (`RouteMSJDeeperFlagCore:501`): the measurable piecewise pivot-frame
selector** (Borel functional calculus; the `(ρ,κ)` pivot-chart selection is measurable). A MEASURABILITY
lemma (non-spectral chart-tree carrier), NOT analytic-hard; the finite covers it rides
(`pivotLocus_eq_iUnion`, `singularShell_iUnion`) are BANKED.

## 4. The exponent gate (ii) — BANKED + reliably re-verified

`carrierThreshold_shift` (`RouteMSJDecorated:71`): `c' − peelCharge(t)/2 < ½·minAdm(redChain t M)` whenever
`c' < ½·minAdm M`. ℕ backbone `minAdm_le_peelCharge_add_redChain` (`RouteMSJDecoratedCharge:52`:
`minAdm M ≤ peelCharge(t) + minAdm(redChain t M)`). **Reliably re-verified (exact ℕ): 0 fails — arity-4
9261/9261 cuts, arity-5 10000/10000.** Codex Q1 concurs (always strict; equality only when t minimizes, but
the final IH stays strict since `c'<½minAdm M`). **The gate is NOT an obstruction** — the crux is Brick D
(the coupled minor-stratified domination), not the arithmetic.

## 5. Levels kept apart / the carrier (iii)

- **Carrier (non-spectral chart-tree):** the freed form (`gammaPeelIntegral_schurShearFree_eq`) + the finite
  covers (`pivotChart`/`pivotLocus_eq_iUnion`, `singularShell`/`offSector_cover_le`) + `blockSplitEquiv` +
  `outerDom`/`schurShift` + `cornerComparator` — ALL BANKED. The resolution-of-singularities RECURSION proper
  (the object that carries the front-factor pivot data through the (S,J) double induction) = Bricks F+D.
- **Level separation:** the backbone is the **finiteness/(□)** reduction (box-integral → shorter box-integral);
  it does not touch the codim `(C,θ)` count or the cited `rlct=½codim` — `carrierThreshold M = ½minAdm M` is
  the codim budget the recursion descends on (banked arithmetic), not an RLCT claim.

## Close

- **Firmest result.** The backbone route is fully mapped and its plumbing + gate are BANKED; the reduce-to-
  shorter-chain is `deeperFlag_shell_le` → decorated `cornerComparator(redChain t M).integral(c'−peelCharge/2)`
  → decorated recursion → arity−1 IH, with the exponent gate reliably safe (0/9261). The naive
  "absorb-invertible-pivot → routeMLayerBoxIntegral(redChain) directly" is **decorrelated-Codex-UNSOUND** (the
  bare-pivot `p^{−2q}` counterexample at `(2,2,2)@t=1` + the corank Wishart edge). The VALID backbone is the
  **refined decorated joint descent** = Bricks F+D, whose analytic content is my satred/D-cert (coupled
  `[P|B₁₂]`, minor/rank stratification `a<t`/`a≥t`, marginal δ-slack at the edge, Gram weight into the
  decorated comparator). **No `(□)` wall** (the true integral is finite).
- **Most likely to break the BUILD.** (i) Any build that reduces to `routeMLayerBoxIntegral(redChain)` DIRECTLY
  (dropping the `commonDivisor²`/Gram decoration) or absorbs the bare invertible pivot — UNSOUND (O1). Must go
  through the DECORATED `cornerComparator` + retain the coupled `[P|B₁₂]` + minor-stratify. (ii) The corank
  edge `ρ=a+b−1` log must be δ-folded (per-exponent), not claimed as a uniform `ab/2` constant (O2). (iii) The
  full-row-rank front factor approaching rank-drop needs the `a<t`/`a≥t` stratification (not "full row rank
  suffices"). (iv) Brick D must be a MEASURE domination (the interface hyps fail pointwise).
- **Next construction.** Build Brick F (measurable frame selector — measurability, moderate) then Brick D (the
  coupled minor-stratified measure domination with the marginal δ-slack + the Gram weight into the decorated
  comparator — the analytic core, = satred/D-cert content). The decorated recursion + gate are banked; the
  arms (interior clean / edge corank-one / deep rank-sector) supply the arm-specific corank charge into Brick
  D. A dedicated tide builds F then D; I'll pin the exact Brick-D statement per arm on request.

Files (absolute):
- `…/threads/genm-satred/backbone-cert.md` (this cert); `D-cert.md`, `satred-cert.md` (the arm content)
- `…/threads/genm-satred/codex/backbone-{prompt,answer}.md`, `backbone-run.log` (decorrelated Codex, the
  unsoundness verdict + the (2,2,2)@t=1 counterexample + the `λ_cor` Wishart-edge formula)
