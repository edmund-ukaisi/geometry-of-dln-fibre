# Cert D2 — theorem4-localization: transcribe-vs-dissolve adjudication (covdesign-t02)

**Seat:** pen-and-paper (obstruction-first). **Date:** 2026-07-17.
**Map node:** `theorem4-localization` (amended form: EXACT CoV to strictly-smaller arity + MinAdmMono).
**Method:** read Entropy-2013 Theorem 2/3 proofs (cost transcription); exact Newton-polytope RLCT machine
(`battery-drafts/_rlct.py`, rational vertex enum + scipy float cross-check); the `/tmp/d2_reduction_census.py`
stratum census; grep of the banked `deepest_le_of_homogeneous_core` / `MinAdmMono` status. NO Lean built,
NO `rlct = c*` consumed.

---

## VERDICT: DISSOLVE, backed by the banked homogeneity domination. Both halves are native + banked; the ONE
new piece is small. Acyclic by strict arity decrease.

The engine's box object (verified at `RouteMBoxReduction.lean:62,165`) is literally
`routeMLayerBoxIntegral M c' 1 = ∫_{[-1,1]^N} ‖prod_s C^{(s)}‖^{-2c'}` — the **homogeneous** core loss
over the parameter box (degree `2L` homogeneous; no `B`, no prior `φ`). This single fact drives the
adjudication: the non-deepest points are points of a *homogeneous* core, so the cheap tools apply.

---

## 1. What Theorem 4 actually is, and its cost (Entropy-2013, image-read `/tmp/entropy2013.txt`)

Aoyagi-2023's "Theorem 4 [22]" = **Entropy-2013 Theorem 2** (deepest singular point). Statement: for
`f_1..f_m` homogeneous in `w_1..w_j` and a `ψ`-condition,
`λ_{(0,..,0,w*_{j+1},..)}(Σf_i², ψ) ≤ λ_{(w*_1,..,w*_d)}(Σf_i², ψ)` — a **domination**, not a value. Proof:
blow up `{v=0, w_i=0}`, `w_i = v w_i'`, giving `v^{2n_i}f_i²(w') ≤ f_i²(w')` for `|v|<1`, then Lemma 1
(ideal-λ monotonicity). **This content is already BANKED, native, hypothesis-free:**
`deepest_le_of_homogeneous_core` (`DeepestMinRlct.lean:157`, PROVEN via `rlctAtOn_lsc_at_origin` +
`rlctAtOn_ray_scaling_invariant`; "measurable + homogeneous" only — no Aoyagi cite). **So transcribing the
domination costs ZERO.** It applies to the engine's core `F = frobSq(prod M ·)` (degree `2L` homogeneous) at
*every* point `v`, unconditionally: `rlctAtOn F 0 ≤ rlctAtOn F v`.

Entropy-2013 also has **Theorem 3 ("method to add variables" / set-nonzero-as-constant)** — THIS is the
"exact CoV to strictly-smaller arity": if `w_1* ≠ 0`, set `w_1 = 1`; then `λ_{w*}(F) = λ_{w*/w1*}(F')`,
`F'(w_2,..) = F(1,w_2,..)`, ONE fewer variable. Proof: `f_i(w) = w_1^{n_i} f_i'`, and `w_1^{n_i} ≠ 0`
near `w_1*` gives `C·(Σf_i²) ≤ Σf_i'² ≤ C'·(Σf_i²)`, so Lemma 1 makes the λ's EQUAL. This is exact
(a unit sandwich), not lossy.

**Load-bearing ℝ-warnings from the same paper (kill-conditions):**
- Remark 1(1): `f=(y-1+x²)²` (NOT homogeneous) has `λ_{f=0}=1/2` but `λ_{f(x,1)=0}=1/4` — dehomogenising a
  NON-homogeneous residual BREAKS. The CoV is exact only *because* the core is homogeneous.
- Remark 1(2) + "Theorem 4 [11]": the naive hyperplane restriction `λ_g ≤ λ_f` is **true over ℂ, FALSE over
  ℝ** (`(Σx_i²+y-1)²`: `1/2` vs `5/4`). Any dissolve step that "restricts to `w_1=0`" instead of the
  homogeneous blow-up / unit-sandwich is unsound over ℝ.
- Example 3: `λ_{w0} ≤ λ_{w*}` is FALSE in general even at a critical point — the domination needs the
  homogeneity hypothesis, not just criticality.

These are the reasons the domination must go through homogeneity (banked lemma), never a naive restriction.

## 2. The exact reduction (dissolve form), CERTIFIED on the controller's instances

At a non-deepest point of `(2,2,2)` where layer-1 `C^{(1)}` has rank `t_1`, block elimination (Aoyagi
Lemma 2 = a UNIT CoV, RLCT-preserving by Lemma 1) splits `F` (L=2 ⇒ disjoint variables) into a regular
front block + a residual core:

    t_1 = 1:  regular (1,2)-block [rlct 1]  ⊕  (1,1,2)-residual core [rlct 1/2]   ⇒  rlct_w = 3/2
    t_1 = 2:  the (2,2)-instance ‖C^{(2)}‖² [4 Morse coords]                       ⇒  rlct_w = 2

Both are the controller's "(1,2)- or (2,2)-instance." Certified two independent ways (Newton-LP on the
block-eliminated monomial ideal == closed form `½[nReg + minAdm(M')]`), `/tmp/rlct_newton.py`:
`(2,2,2) rank-1 → 3/2`, `full-rank → 2`. Census (`/tmp/d2_reduction_census.py`, all `[LP==CF]`) over
`(2,2,2),(2,2,3),(3,3,4),(3,2,3)`: **every** non-deepest first-layer stratum satisfies
`rlct_w = ½[nReg + minAdm(M')] ≥ ½ minAdm(M)` (the domination), tight at the minimising rank.

**The threshold-preservation is NOT the banked #149 `MinAdmMono`.** Banked #149 is the *componentwise*
`minAdm M' ≤ minAdm M` (widths-drop lowers minAdm) — the opposite direction. What the dissolve needs is the
compensation `nReg + minAdm(M') ≥ minAdm(M)`, which is the **`minAdm`-as-minimum / `inf'_le` property**
(`minAdm(M) = inf_{admissible t} Mval(t)`, so any stratum's codim `= Mval(t) ≥ minAdm`): banked as
`minAdm_le_Mval_toNat` / `PivotWitness.minAdm_le` (verify-r1-135). **Pin this distinction** — a formaliser
reaching for `MinAdmMono` (#149) will grab the wrong inequality.

## 3. Recommended branch + the precise statement to pin

**Recommend DISSOLVE, with the banked domination as the coupling-free backbone.** The non-deepest handling =
`deepest_le_of_homogeneous_core` (banked) supplies `rlct_w ≥ rlct_0` for ALL `v`, homogeneity-only, no
coupling, no arity IH; the "exact CoV to strictly-smaller arity + `inf'_le`" is the *constructive*
box-integral reduction where the reduction is clean, and the arithmetic guarantee that no threshold drops.

Statement for the architect to pin (region-glue owns this; ONE owner):

> **theorem4-localization (assembly-only).** For the homogeneous core `F = frobSq (prod M ·)` and any
> `v` in the box, `rlctAtOn F 0 ≤ rlctAtOn F v` (`= deepest_le_of_homogeneous_core`, BANKED). Hence for
> `c' < ½ minAdm(M) ≤ rlctAtOn F 0`, `F^{-c'}` is locally integrable at every `v`; a finite subcover of
> the compact box gives `routeMLayerBoxIntegral M c' 1 < ⊤`. The far/non-deepest regions where an exact
> unit CoV applies reduce to strictly-smaller arity with threshold preserved by `nReg + minAdm(M') ≥
> minAdm(M)` (`minAdm_le_Mval`).

**The far-point bridge — CLEANER than LSC (decorrelated Codex, verified).** Because `F` is homogeneous of
degree `2L`, the whole-box integral is an EXACT scalar multiple of a small-box integral:

    I_B(c') = ∫_{[-1,1]^N} F^{-c'} = ρ^{2Lc' - N} · I_{ρB}(c')     (sub x = ρw; F(ρw) = ρ^{2L}F(w)).

Pick `ρ` small enough that `ρB = [-ρ,ρ]^N ⊂ V`, the neighborhood the resolution (coverage) resolves; then
`I_{ρB}(c') < ⊤` from the charts, so `I_B(c') < ⊤` — a finite multiple. **This replaces the
LSC/finite-subcover bridge entirely for the FAR points**: no LSC of `rlctAtOn`, no open cover of `B \ V` —
just the homogeneity scaling identity (its pointwise shadow `rlctAtOn_ray_scaling_invariant` is banked,
`DeepestMinRlct.lean:148`). So the box reduces to a resolved neighborhood by an EXACT CoV (the ρ-scaling),
consuming no `rlct=c*`.

**What genuinely remains** is then INSIDE coverage: the non-origin *singular* points of the zero locus that
lie in `V` (the resolution must be NC over a full neighborhood, not only at the origin). Those points have a
strictly-smaller-arity local core (the dissolve / arity-IH of §2), and at `L ≥ 3` partial rank they couple
(§5). This is the same obligation, now correctly located: the "non-deepest reduction" is coverage's
neighborhood-resolution, not a separate far-region argument.

## 4. Acyclicity (no coverage ↔ theorem4 cycle)

- `deepest_le_of_homogeneous_core` is a pure homogeneity/ray-scaling fact — it calls **nothing** (not
  coverage, not the resolution). Trivially acyclic.
- The exact-CoV reductions **strictly decrease arity** (fewer coordinates / fewer layers — verified:
  `(2,2,2)→(1,1,2)` drops 8→3 free entries, `(2,2,2)→(2,2)` drops `L` by 1), so an arity well-founded
  recursion `hbox(M) ⟵ hbox(M')` never revisits `M`.
- **Coverage (Layer C) owns only the origin-neighborhood (tracked cells).** It does NOT invoke
  theorem4-localization at the same arity. theorem4-localization owns the non-deepest/far region and either
  (a) discharges it by the banked domination (calls nothing) or (b) reduces to `hbox(M')` at strictly
  smaller arity. Well-founded on arity; the two obligations partition the box (near ∪ far) with disjoint
  owners. **No cycle.** (This matches the controller's Item 4 "acyclic assembly-only region-glue.")

## 5. Firmest result / most likely to break / next step

- **Firmest:** the domination is banked native (transcribe = free); the dissolve arithmetic is exact and
  banked (`inf'_le`); both certified on `(2,2,2)/(2,2,3)/(3,3,4)/(3,2,3)`. Acyclic by strict arity drop.
- **Most likely to break it (the honest open leg):** a **partial-rank non-deepest point at `L ≥ 3`**. There
  the exact CoV yields a *coupled* residual core (shared deep factor `C^{(s)}`, diag(b) sharing —
  `g-coupled-binding-334`, verify-r1-light-recursion), which is **not a clean chain `M'`**, so the
  chain-arity-IH `hbox(M')` does NOT directly apply. **Resolution:** at those points fall back to the banked
  `deepest_le_of_homogeneous_core` (coupling-free — this is exactly why the domination, not a chain-IH, is
  the backbone). So the recommendation stands, but the "dissolve as chain-IH" must NOT be sold as general;
  it is the clean-reduction mechanism only, with the domination the general discharge.
- **Next step to settle the open part:** the far-point bridge is now the homogeneity scaling identity
  `I_B = ρ^{2Lc'-N} I_{ρB}` (no LSC needed) — confirm the resolution resolves a full solid neighborhood `ρB`
  (coverage's job, D3), so the only genuine analytic content is coverage's neighborhood-NC-resolution with
  the sharing data. The `L ≥ 3` partial-rank non-origin singular points (the coupling) are handled INSIDE
  coverage (which already carries the diag(b) support), not by a separate chain-IH.
