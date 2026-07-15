# gaugelift — the general-L exponent gate (brick B): CLEAN (ring + banked `inf'_le`), NO obstruction; `C_{ℓ,s}` is `M₂`-parametrized (NOT `M_last`)

**Seat:** pen-and-paper (adjudication: the general-L exponent gate is a `ring`+banked-`inf'_le`, no
genuine obstruction), aoyagi-full Stage 2, `genm-gaugelift`. **Date:** 2026-07-15. **NO Lean edits, NO
build.** Exact ℕ-arithmetic (matching the Lean `minAdmRec` recursion) + a decorrelated
`local-codex-consult` (gpt-5.x, xhigh, my conclusion WITHHELD; prompt framed "argue whichever way"):
`codex/gaugelift-{prompt,answer}.md`, `run.log`. Numerics (exhaustive, guide + certificate):
`/tmp/gaugelift/gate_check{,2,3}.py`.

**Consumed / verified (git show on the sj5 branches, not paraphrased):**
`genm-routeverify/routeverify-cert.md` §3/§6/§7, `genm-incidencepp/incidence-cert.md` §3/§3b (the L=0
resolution), the Lean: `RouteMSJIncidenceExponent.lean` (`clsCodim` L45, `clsCodim_add_ab_eq` L51,
`clsCodim_gate` L82, `minAdm_arity3` L68 — all `Fin 3`, `origin/genm-sj5-brickdcont`),
`RouteMLayerSplit.lean` (`redChain` L40, `minAdm` L51, `minAdmRec` L58, `minAdmRec_succ_succ` L66,
`LayerSplit_value_eq_minAdm` L436), `RouteMSJDecoratedCharge.lean` (`peelCharge` L45,
`minAdm_le_peelCharge_add_redChain` L52), `RouteMSJDecoratedStep.lean` (`deepTailMin` L103,
`minAdm_le_head_mul_tailInf` L110, `minAdm_redChain_le_deepTailMin` L131 —
`origin/genm-sj5-good`/`-waist`), `RouteMSJDeeperFlagCore.lean` (`deeperFlagCoreIntegrand` L339,
`deeperFlag_shell_core_le` L368, `shellSpineIntegrand` L444, `deeperFlagZdeep` L466,
`tailMinWidth` L458).

---

## ★ VERDICT (definitive)

**The general-`L` exponent gate is `ring` + banked `inf'_le` — NO genuine obstruction, and it is
STRICTLY CLEANER than the L=0 gate.** Three findings:

1. **`C_{ℓ,s}` is parametrized by `M₂` (the SECOND width = `Z_deep`'s ROW dim = the corank space where
   `A_cor` lives), NOT `n = M_last`.** The banked `Fin 3` `clsCodim` / `clsCodim_add_ab_eq` are REUSED
   VERBATIM (they read only `M 0, M 1, M 2`). `M_last` enters the geometry only through the bounded PD
   unit `Z_deep Z_deepᵀ` (`M₂×M₂`), which does not change any codimension. **This is a correction to the
   brief's framing "`C_{ℓ,s}` parametrized by `n = M_last`"** — the deep FACTOR is `M₂×n` (`n=M_last`),
   but the front-cell CODIMENSION is `M₂`-controlled. (Decorrelated Codex Q1 concurs: `d = M₂ − b`, with
   an independent `U = (ZZᵀ)^{−1/2}Z` orthonormalization argument — both `Q_p, Q_b ⊆ row(Z)` (dim `M₂`),
   the `n−M₂` directions in `row(Z)^⊥` contribute zero normal directions.)

2. **The `ℓ`-independence ring identity is UNCHANGED at general `L`:** `clsCodim + ab = (M₀−s)(M₁−s) +
   s·M₂` (pure `ring` over ℤ after the `b=M₁−u`, `d=M₂−b` substitution — the SAME `clsCodim_add_ab_eq`,
   a `Fin 3` statement). **The deep chain does NOT introduce an extra ring term into `C_{ℓ,s}`.** The
   deep chain's finer degeneracy (which brings `s·M₂` DOWN to `minAdm(redChain s M)`) is NOT in the
   front cell — it lives in the comparator `cornerComparator(redChain u M)`, resolved by the decorated
   IH. (Codex Q2 concurs: **polynomial-per-cell, NOT nested-min-per-cell** — `rank(P_pivot·Z) =
   rank(P_pivot)` on the full-row-rank `Z`-chart, so `Q_p`'s rank loss is a condition on the DEEP
   variables, not on `(A_cor, front)`; a nested min appears only after minimizing over the deep cells.)

3. **The gate `minAdm(M) ≤ clsCodim + ab` (⟺ `min_{ℓ,s} C_{ℓ,s}/2 ≥ T1_q = (minAdm M − ab)/2`) holds
   ∀`L`, UNCONDITIONALLY (no `a+b≤M₂` scope needed — that scope is only for corank integrability), via a
   3-link chain of BANKED lemmas + one `inf'_le`:**

       minAdm M
         ≤  (M₀−s)(M₁−s) + minAdm (redChain s M)     -- minAdm_le_peelCharge_add_redChain M s  (BANKED)
         ≤  (M₀−s)(M₁−s) + s · deepTailMin M          -- minAdm_redChain_le_deepTailMin M s      (BANKED)
         ≤  (M₀−s)(M₁−s) + s · M₂                      -- deepTailMin M ≤ M 2   (Finset.inf'_le, i=0)
          =  clsCodim ![M₀,M₁,M₂] u ℓ s + ab           -- clsCodim_add_ab_eq                       (BANKED, ring)

   **`decide`-free, sweep-free, ∀-quantified.** Exhaustive certificate: **0 fails over 130 935 feasible
   `(M,u,ℓ,s)` strata** (arity 3–5, widths 1–6, `/tmp/gaugelift/gate_check3.py`), plus the recursion
   anchors match Lean (`minAdm(2,2,2)=3`, `(3,3,4)=8`, `(4,4,2,2)=4`, `(3,3,2,2)=4`).

---

## 1. The general-`L` object, precisely (verified against Lean)

At a cut `u ≤ min(M₀,M₁)` of a chain `M : Fin (L+1+1+1) → ℕ`, the head-split (`RouteMSJDeeperFlagCore`)
factors the reduced product through a SINGLE deep factor:

    prod (redChain u M) z = (z 0) · Z_deep z,   Z_deep z : M₂ × n,  M₂ = M 2,  n = M_last  (deeperFlagZdeep L466)
    Q_p = prod (redChain u M) z  (u × n) = (z 0) · Z_deep,     Q_b = A_cor · Z_deep  (b × n),  A_cor free (b × M₂).

`a = M₀−u`, `b = M₁−u`, `ab = peelCharge M u` (`RouteMSJDecoratedCharge`). The corank weight
`det(Q_b Q_bᵀ)^{−a/2} = det(A_cor·(Z_deep Z_deepᵀ)·A_corᵀ)^{−a/2}` integrates over `A_cor ∈ matBox b M₂`,
Wishart/corank threshold `a < rank(Z_deep) − b + 1 ⟺ a + b ≤ M₂` (`m = M₂ = rank Z_deep`; the
`shell_corankOffSector_le_unif` `hconv`). The comparator is `cornerComparator (redChain u M)`, RLCT
`½·minAdm(redChain u M)`, at the shifted exponent `c' − ab/2` (`deeperFlag_shell_core_le` conclusion).

**Why `M₂`, not `M_last` (the load-bearing structural point).** `A_cor` is a free `b×M₂` matrix; `Z_deep`
is a FIXED full-row-rank `M₂×n` factor. So `Q_b = A_cor·Z_deep` ranges over a `b·M₂`-dimensional family
(NOT `b·n`), living entirely in `row(Z_deep)` (dim `M₂`). All incidence/transverse-Schur codimension is
counted in this `M₂`-space; the `n−M₂` extra columns are `row(Z_deep)^⊥` where `Q_p, Q_b ≡ 0` (no normal
directions). Hence the L=0 formula ports with `d = M₂ − b` UNCHANGED:

    C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s·(M₂ − b − ℓ)         (= `clsCodim ![M₀,M₁,M₂] u ℓ s`)

reading ONLY the arity-3 head `(M₀,M₁,M₂)`. `M_last` is absent (enters only via the bounded unit
`Z_deep Z_deepᵀ ≻ 0`).

## 2. The identity — clean `ring`, no extra term (answers brief Q2)

`clsCodim_add_ab_eq` (banked, `Fin 3`) is the L≥1 identity verbatim:

    clsCodim ![M₀,M₁,M₂] u ℓ s + (M₀−u)(M₁−u) = (M₀−s)(M₁−s) + s·M₂         (ℓ-terms cancel; `zify`+`ring`)

**No deep-chain term enters the identity.** The brief's conjectured form `… + s·(deep-chain codim summand
at rank s)` resolves as follows: the L=0 "deep summand" `s·M₂` is *exactly* `minAdm(redChain s M)` at L=0
(`redChain s M = (s,M₂)` is a leaf, `minAdm = s·M₂`); at L≥1 the geometric front cell keeps the NAIVE
monomial `s·M₂` (Codex Q2: polynomial-per-cell), and the tight `minAdm(redChain s M) ≤ s·M₂` shows up in
the GATE (§3), NOT the identity. So the answer to "clean ring or extra terms": **clean `ring`, unchanged
from L=0; the deep chain is absorbed by the banked gate lemmas, never the identity.**

*(Alternative tight bookkeeping — NOT recommended, stated for completeness.)* One could instead DEFINE a
tight per-stratum codim `C_{ℓ,s}^tight := (M₀−s)(M₁−s) + minAdm(redChain s M) − ab`; then the gate is
LITERALLY `minAdm_le_peelCharge_add_redChain M s` (one banked line, no `deepTailMin` step). But
`C_{ℓ,s}^tight` carries a nested `min` (not a single-chart monomial exponent), does not match the radial
blow-up `∫r^{C−1−2q}dr` picture, and the geometry gives the naive form (Codex Q1/Q2). Keep `clsCodim`.

## 3. The gate — `ring` + banked `inf'_le`, unconditional (answers brief Q3)

**The Lean the tide adds (one lemma; sketch verified against the banked signatures):**

    theorem clsCodim_gate_genL {L} (M : Fin (L+1+1+1) → ℕ) (u ℓ s : ℕ)
        (hu : u ≤ min (M 0) (M 1)) (hs : s ≤ u) (hℓs : ℓ + s ≤ u) (hbℓ : (M 1 - u) + ℓ ≤ M 2) :
        minAdm M ≤ clsCodim ![M 0, M 1, M 2] u ℓ s + (M 0 - u) * (M 1 - u) := by
      -- rewrite RHS by the banked Fin-3 ring identity (its hyps: hu/hs/hℓs/hbℓ port with ![M0,M1,M2])
      rw [clsCodim_add_ab_eq ![M 0, M 1, M 2] u ℓ s (by simpa using hu) hs hℓs (by simpa using hbℓ)]
      -- goal: minAdm M ≤ (M 0 - s) * (M 1 - s) + s * M 2
      have hs' : s ≤ min (M 0) (M 1) := le_trans hs hu
      have h1 := minAdm_le_peelCharge_add_redChain M s hs'        -- ≤ (M₀−s)(M₁−s) + minAdm(redChain s M)
      have h2 := minAdm_redChain_le_deepTailMin M s               -- minAdm(redChain s M) ≤ s·deepTailMin M
      have h3 : deepTailMin M ≤ M 2 :=                            -- inf'_le at i=0 (M 0.succ.succ = M 2)
        Finset.inf'_le _ (Finset.mem_univ 0)
      -- peelCharge M s = (M₀−s)(M₁−s); chain h1,h2,h3 with omega/nlinarith
      simp only [peelCharge] at h1; nlinarith [h1, h2, Nat.mul_le_mul_left s h3]

**Reduction confirmed (brief Q3): the general-`L` gate = "min-over-feasible ≥ min-over-full = minAdm" +
the banked recursion fact.** In the min form, `min_{(ℓ,s) feasible} clsCodim = minAdm_feas(u) − ab` where
`minAdm_feas(u) = min_{0≤s≤u}[(M₀−s)(M₁−s)+s·M₂]`; then
- `minAdm_feas(u) ≥ min_{0≤s≤min(M₀,M₁)}[(M₀−s)(M₁−s)+s·M₂] = minAdm3(M₀,M₁,M₂)` (subrange `inf'` monotonicity), and
- `minAdm3(M₀,M₁,M₂) ≥ minAdm(M)` — the NEW-at-L≥1 step, `= minAdm_le_peelCharge_add_redChain` ∘
  `minAdm_redChain_le_deepTailMin` ∘ `deepTailMin ≤ M₂` (the 3-link chain above).

**Verdict: `ring`+`inf'_le`, NO genuine general-`L` obstruction.** No case sweep, no `decide`. The gate is
UNCONDITIONAL (verified without the `a+b≤M₂` filter — that scope is corank-integrability, a separate
analytic condition, not the exponent gate). It is CLEANER than the L=0 `clsCodim_gate` (which routed
through `minAdm_arity3`); the general-`L` version uses the layer-peeling recursion facts directly.

## 4. Where the true RLCT `T1 = ½·minAdm(M)` lives (the honest scope of the front gate)

At L=0 the front strata BIND at `T1_q` (`min C/2 = T1_q`; `minAdm3 = minAdm`). **At L≥1 the front strata
generically do NOT bind at `T1_q`** — `min_{ℓ,s} C_{ℓ,s}/2 = (minAdm3(M₀,M₁,M₂) − ab)/2 ≥ T1_q`, STRICT
when the deep chain binds (**6048 / 9288 chains have `minAdm3 > minAdm(M)`**; Codex's `(3,3,3,3)` example:
`minAdm3(3,3,3)=7 > minAdm(3,3,3,3)=6`, matching my `gate_check.py`). The true singularity `T1` is
delivered by the DEEP COMPARATOR `cornerComparator(redChain u M)` (finite up to `½·minAdm(redChain u M) ≥
T1_q` by the banked `minAdm_le_peelCharge_add_redChain` = the recursion `inf'_le` at `t=u`), NOT by the
front strata. This is consistent (both LHS-front and RHS-comparator thresholds `≥ T1_q`, so the
per-exponent ratio `K = Σ K_{ℓ,s}` is finite for `c' < T1`) — sharpness is NOT needed for the domination,
only `≥`. **Do NOT try to make the front strata bind at `T1` for L≥1; they do not, and the incidence
route does not need them to.**

## 5. Numerics (GUIDE + certificate; exact algebra §2/§3 is load-bearing)

- `gate_check.py` (9288 chains, arity 3–5, widths 1–6): F2 `minAdm(redChain t M) ≤ t·M₂` 0 fails; NAIVE
  gate `minAdm(M) ≤ (M₀−s)(M₁−s)+s·M₂` 0 fails; TIGHT gate (=banked at s) 0 fails; recursion exact 0
  fails; `minAdm ≤ minAdm3` 0 fails; **6048 chains with `minAdm3 > minAdm(M)`** (deep binds).
- `gate_check2.py` (arity 3–6, widths 0–7): `minAdm(0,…)=0` 0 fails; F2 0 fails; TIGHT gate 0 fails;
  recursion-min-achieved 0 fails; min-over-feasible-`[0,u]` `≥ minAdm` 0 fails.
- `gate_check3.py` (**130 935 feasible `(M,u,ℓ,s)`**, exact `clsCodim`): identity `clsCodim+ab =
  (M₀−s)(M₁−s)+s·M₂` 0 fails; GATE `minAdm(M) ≤ clsCodim+ab` 0 fails; step1/step2/`deepTailMin≤M₂` 0
  fails.

## 6. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way") — CONCURS on all three

`codex/gaugelift-{prompt,answer}.md` (xhigh). Independent, reached the identical verdict:
- **Q1 [FACT]** `d = M₂ − b` (not `n − b`), via `U = (ZZᵀ)^{−1/2}Z`, `UUᵀ = I_{M₂}`; both `Q_p,Q_b ⊆
  row(Z)` (dim `M₂`); `row(Z)^⊥` contributes no normal directions ⟹ `s(M₂−b−ℓ)`.
- **Q2 [FACT]** POLYNOMIAL-per-cell, not nested-min: `rank(P_pivot·Z)=rank(P_pivot)` on the full-rank-`Z`
  chart ⟹ `Q_p`-rank-loss is a DEEP condition, its normal directions belong to the separate comparator;
  a nested min appears only after minimizing over deep cells.
- **Q3 [FACT]** front gate governed by `M₂`; the naive front min CAN be strictly larger than the true
  chain min; the gap is carried by DEEPER COMPARATOR STRATA (example `(3,3,3,3)`), not by replacing `M₂`
  with `n` or altering the front-cell codim. *(Minor imprecision: Codex's example uses cut `u=3` and
  calls `minAdm(3,3,3,3)=6` the "3×3×3 comparator min" — the binding cut is actually `u=2`,
  `minAdm(3,3,3)=7`; the conclusion (naive 7 > true 6, gap in deeper strata) is unaffected and matches my
  exact `gate_check.py`.)*

## Close

- **Firmest result.** The general-`L` exponent gate `minAdm(M) ≤ clsCodim ![M₀,M₁,M₂] u ℓ s + ab` (⟺
  `min_{ℓ,s} C_{ℓ,s}/2 ≥ T1_q`) is a `ring` (`clsCodim_add_ab_eq`, banked, UNCHANGED) plus a 3-link chain
  of BANKED lemmas + one `Finset.inf'_le` (`minAdm_le_peelCharge_add_redChain M s` ∘
  `minAdm_redChain_le_deepTailMin M s` ∘ `deepTailMin M ≤ M 2`). Sweep-free, `decide`-free, unconditional
  (no `a+b≤M₂`). Exhaustive 0/130 935; decorrelated Codex concurs on the `M₂`-parametrization and the
  polynomial-per-cell structure. **No genuine general-`L` obstruction.**
- **The flag (brief GUARD).** The brief's "`C_{ℓ,s}` parametrized by `n = M_last`" is imprecise: the
  front-cell CODIM is `M₂`-controlled (the corank space; `Z_deep`'s ROW dim), `M_last` is a bounded unit.
  The banked `Fin 3` `clsCodim`/`clsCodim_add_ab_eq` are REUSED VERBATIM — the ONLY new Lean is the
  ≤10-line `clsCodim_gate_genL`. The deep chain does **not** break the ring identity; it is absorbed by
  the banked gate lemmas. (No isolated "extra term" to report — that outcome did not occur.)
- **Most likely to break it.** (i) If the tide instead adopts the naive formula with `d = M_last − b`
  (mis-reading the brief), the gate STILL closes (`minAdm(redChain s M) ≤ s·deepTailMin ≤ s·M_last`, F1L
  0 fails) but the identity would read `+ s·M_last` and NOT match the banked `clsCodim_add_ab_eq` — so use
  `M₂` to reuse the banked identity. (ii) The gate is exponent-only (Nat/codim); it does NOT license the
  coupled analytic estimate (`headSplit_domination`/route B is dead, routeverify §2) — the incidence
  route must still land `shellSpineIntegrand ≤ K·cornerComparator(redChain u M).integral(c'−ab/2)`
  directly (bricks A/C/D). This cert de-risks brick **B** only.
- **Next.** The formaliser adds `clsCodim_gate_genL` (§3) to `RouteMSJIncidenceExponent` (reusing the
  banked `clsCodim`/`clsCodim_add_ab_eq` verbatim + the three banked chain lemmas). The `deepTailMin M ≤
  M 2` `inf'_le` and the `peelCharge` unfold are the only fiddly bits. Then brick B is discharged; the
  remaining spec is A (top-level assembly) + C (index-completeness) + the coupled analytic content.

Files (absolute):
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-gaugelift/gaugelift-cert.md` (this cert)
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-gaugelift/codex/gaugelift-{prompt,answer}.md`, `run.log`
- `/tmp/gaugelift/gate_check{,2,3}.py` (exact-arithmetic certificates)
