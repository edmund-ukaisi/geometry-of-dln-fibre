# Box-Morse per-corank closure — the route spec for `sjJointResolution` / `gammaPeelIntegral < ⊤`

> ⚠️ **SUPERSEDED by `sjjoint-exponents-cert.md` (2026-07-10).** `forkreview`'s Lean-tractability
> assessment + my confirmation: box-Morse's brick (ii) — the codim-`D` sublevel/tube measure
> `vol{rank≤q−1 within ρ} ≲ ρ^D` — has NO v4.29 support (banked `cCodim` gives ALGEBRAIC codim, not the
> Lebesgue tube bound; elementary slicing stalls at `t¹ < θ_true`; the sharp `t^D` = the whole-minor-ideal
> = the flag in disguise). The route pivots to the native `(S,J)` resolution. **Retained as the record of
> WHY the front-peel cannot cheaply close in Lean; the exponent TARGETS (`θ_true`, `D`, the linchpin) are
> carried into `sjjoint-exponents-cert.md`.**

**Seat:** pen-and-paper (witness). **Task #111 (downscoped).** **Date:** 2026-07-10. **NO Lean.**
**Charge:** pin the box-Morse per-corank closure — the replacement for the lossy `reducedMorseFront`
whole-space peel — to a Lean-friendly certificate the build tide formalises. **Decorrelated:** builds on
the `forkreview` adjudication (which refuted my earlier no-go; §CONCESSION in `cert.md`) + a fresh
Codex on the box-atom Lean shape (`codex/boxatom-{prompt,answer}.md`).

**Where the live sorry is:** `sjJointResolution` (`RouteMSJResolution.lean:797–803`) — per-chart
finiteness of `gammaPeelIntegral M t ρ κ c'` (`RouteMSJResolution.lean:517`) below `½·minAdm M`, given
the arity IH `hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M'`.

---

## 0. The exact mapping onto the CURRENT carrier (read this first)

The carrier peels the **front factor `A₀`** (M₀×M₁), pivot cut `t` = a `t×t` unit minor of `A₀` (rank
`A₀ ≥ t`), NOT the tail product. On the chart the banked block identity `frobSq_schur_block_split`
(`RouteMSJChartAlgebra`) gives
> `frobSq(A₀·Q) = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`, `Q = prod(tailChain M) A'` (M₁×M_L),

`A` = A₀'s `t×t` pivot, `C` = A₀'s bottom-left, `Γ = D − CA⁻¹B` = A₀'s `(M₀−t)×(M₁−t)` corank Schur
block, `Q̃_p, Q_b` = Q's row-blocks (`Q_b` = the bottom `(M₁−t)` rows = a **reduced tail product**). The
MP shear `D ↦ Γ` (`measurePreserving_shearSub`) frees `Γ`. The inner `Γ`-integral is the corank atom.

**The current route's LOSSY step (the exact wall).** The banked anisotropic Γ-atom
(`RouteMSJGammaAtom`) does the **Gram change of variables `Γ ↦ Γ·Q_b`** (whole-space), which injects the
Jacobian `det(Q_b Q_bᵀ)^{−(M₀−t)/2}`. That atom is **explicitly scoped to the full-rank slice** (`Q_b
Q_bᵀ` posdef; `RouteMSJGammaAtom.lean:140`: *"degenerate rank-drop strata route to a deeper boundary"*).
The **"standing L≥3 wall (750/5440 charts): `M₁−t > min(deeper widths)` ⟹ `Q_b` rank-deficient"**
(`sjJointResolution` docstring) is **exactly** the locus where `det(Q_b Q_bᵀ) → 0` and the whole-space
Gram Jacobian blows up. This is the *same phenomenon* forkreview and I resolved: a **whole-space** peel is
lossy where a direction collapses.

**The fix (this cert).** On the rank-drop strata, do NOT push `Γ` to whole space via the Gram CoV. Keep
`Γ` over its **BOX** and bound `∫_{Γ box} frobSq(Γ·Q_b)^{−c'}` directly. The collapsing singular
direction of `Q_b` is then **bounded by the box** (contributes `O(1)`, not `σ^{−(M₀−t)}`), giving a
smaller exponent that the geometric **linchpin** closes. The elementary linchpin fact:
> `∫_{−1}^{1}(σ² z² + w)^{−c'} dz → 2·w^{−c'}` (BOUNDED) as `σ → 0` — the box caps the soft direction;
> only the whole line gives `σ^{−1}`.

---

## 1. THE BOX-EXPONENT LEMMA (the load-bearing NEW brick)

**Statement (box corank Γ-atom, uniform as `Q_b` rank-drops — the replacement for the full-rank
anisotropic atom).** For `Γ : Fin p → Fin q → ℝ` over the box `matBox p q T`, a coupling `R : q×n`
(`= Q_b`), a shift `S`, `w > 0`. Let `G = R Rᵀ`, orthogonally diagonalised `O G Oᵀ = diag(σ_1²,…,σ_q²)`,
and choose a STIFF set `J`, `|J| = k`, with `σ_i > 0` (i.e. `σ_i ≥ δ`) on `J`; the other `q−k` are SOFT.
Then the atom is **PIECEWISE** (Codex math-correction — the residual power needs `c'` above the
STIFF-rank threshold `pk/2`; `k` = peeled stiff rank, not necessarily algebraic rank):
> **Above threshold (`c' > pk/2`):**
> `∫_{Γ ∈ matBox p q T}(w + ‖Γ·R + S‖²)^{−c'} dΓ ≤ (2B)^{p(q−k)}·(∏_{i∈J}σ_i)^{−p}·Cresid(pk,c')·w^{−(c'−pk/2)}`,
> `B = √q·T` (box enlargement under the rotation). Cruder Lean-friendly form: `(∏σ_i)^{−p} → δ^{−pk}`.
>
> **Sub-critical (`c' < pk/2`):** finite UNIFORMLY in `w` (no residual power): `≤ (2B)^{p(q−k)}·δ^{−2c'}·K`.

**No `det(R Rᵀ)^{−p/2}` full-Gram factor appears; the `q−k` SOFT directions contribute only the box-volume
factor `(2B)^{p(q−k)}`, and if a soft `σ_i → 0` the bound is UNCHANGED.** When `R` is full row rank
(`k=q`) this recovers the banked full-space value (`∏σ_i = √det(RRᵀ)`); the point is it stays FINITE and
controlled as `k < q` (the wall), where the full-space atom diverges.

**Proof route (Lean, Codex-pinned — split-index first, then a Gram-split wrapper; NO full SVD).**
- **(Layer 1) coordinate atom over pre-split coords** `Z : Fin p → (Fin k ⊕ Fin s) → ℝ` (`s = q−k`),
  stiff weights `σ : Fin k → ℝ` (`>0`), soft energy DROPPED (nonneg):
  ```lean
  theorem box_stiff_soft_residual_le (σ : Fin k → ℝ) (hσ : ∀ i, 0 < σ i)
      (hc : (p*k : ℝ)/2 < c') (hw : 0 < w) :
    ∫⁻ Z in splitBox p k s B, ENNReal.ofReal ((w + stiffEnergy σ Z + softEnergy Z)^(-c'))
    ≤ ENNReal.ofReal ((2*B)^(p*s) * (∏ i, (σ i ^ p)⁻¹) * Cresid (p*k) c' * w^(-(c'-(p*k:ℝ)/2)))
  ```
  proved by: drop `softEnergy ≥ 0` (monotone), stiff change-of-vars (Jacobian `∏σ_i^{−p}`), the banked
  isotropic box atom `matBox_corank_residual_le` (`RouteMSJCorankResidual.lean:114`, uniform in `T`); the
  soft coords contribute `(2B)^{ps}` by `setLIntegral_const`. Sub-critical branch: `RouteMSJCorankPure:87`.
- **(Layer 2) matrix wrapper** via a `GramStiffSplit R` structure (Codex): `O` orthogonal with
  `O G Oᵀ = diag(σ² ⊕ soft²)`, reindex `Fin q ≃ Fin k ⊕ Fin s`; then `Γ ↦ Γ·Oᵀ` (`rightMulₚ`,
  `RouteMSJGammaAtom:48`, det-1 orthogonal ⟹ MP), box enlargement `[−T,T]→[−B,B]`, energy
  diagonalisation `‖ΓR‖² = ∑σ_i²‖Z_i‖²`, then Layer 1. The `GramStiffSplit` is inhabited from Mathlib
  `Matrix.IsHermitian.spectral_theorem` (enough for exact `σ_i`; full SVD unnecessary). First impl: take
  `GramStiffSplit` as DATA, instantiate from spectral theorem later.
- Mathlib/banked bricks: `Cresid`, `matBox_corank_residual_le`, `radial_morse_residual_power_le`
  (`RadialResidualPower`), `rightMulₚ`+det (`RouteMSJGammaAtom:48`), `Matrix.IsHermitian.spectral_theorem`,
  `RouteMSJCorankPure:87` (sub-critical), `PiLp.volume_preserving_toLp`.
- **Codex uncertainty (fold in):** opaque `Fin q` rank-`r` wrapper is CAST-HEAVY — prove the split-index
  `Fin k ⊕ Fin s` theorem first, add the `Fin q` reindex last; box volume `(2B)^{ps}` can hide behind
  `volume (matBox p s B)`.

**Status:** NEW brick, bounded (spectral-theorem Gram split + the banked isotropic box atom). It is the
anisotropic Γ-atom of `RouteMSJGammaAtom` with the **full-rank scope removed** (valid on rank-drop strata)
by keeping the box instead of the whole-space Gram CoV, and made PIECEWISE at the stiff-rank threshold.

---

## 2. THE LINCHPIN `minAdm(M) ≤ D + (M₀−t)(rank drop)` (the geometric closer)

**Statement.** With `q := M₁ − t` the corank-block width and `D := codim{rank Q_b ≤ q−1}` in the
tail-parameter space (`Q_b` = the reduced tail product):
> `minAdm(M) ≤ D + (M₀−t)·(q − (rank drop))`  — precisely, the containment version:
> `Y := {rank Q_b ≤ q−1} ∩ {A₀ kills the image} ⊆ Z :=` zero-product locus, and `codim Y = D + (M₀−t)·k`
> at rank-drop `k`, so `minAdm(M) = codim Z ≤ codim Y = D + (M₀−t)·k`.

**Consequence (the closure — Codex A'-integration form).** After the box atom (§1), the outer integral
near a rank-drop locus of codim `D` has the shape `∫_{A'} Π_J(A')^{−p}·w(A')^{−e} dA'`, `e = c'−pk/2`,
`Π_J = ∏_{i∈J}σ_i(Q_b)` (the STIFF Gram — soft σ's excluded, so NO full-Gram pole). If locally
`Π_J ∼ ρ^β`, `w ∼ ρ^γ` (`ρ` = distance to the locus), the radial normal integral is
`∫_0^ε ρ^{D−1−pβ−γe} dρ`, **convergent iff `pβ + γe < D`**. When `w` is bounded below (`γ=0`) this is
`pβ < D` — controlled by the linchpin (the stiff-Gram vanishing order `β` against the codim `D`). This is
the precise, Codex-independent form of the closure: the soft directions do NOT enter `Π_J`, so a
collapsing direction creates NO determinant pole — the deeper boundary is integrable, **no simultaneous
rank-flag resolution needed.**

**Lean route (banked vs new):**
- `codim Z = C` at `r = 0` is **BANKED**: `codimRepCanonical_fibre_zero_eq_cCodim` (`RlctPayoff.lean`),
  and general-`r` `codimRepCanonical Σ̄^r = cCodim d r` is **BANKED** (RlctPayoffGeneral "Brick A",
  `codimRepCanonical_fibre_eq_cCodim_add_shift` / `Core.FibreCodimFinal`, via Voigt, char-0).
- `C = minAdm` bridge: **NEEDS PINNING** — the (C,θ) engine gives `cCodim d 0`, Aoyagi's route gives
  `minAdm`; both are `codim(zero-product locus)`, so `cCodim d 0 = minAdm M` should be a banked or
  short-derivable equality. **Flag:** confirm `cCodim_eq_minAdm` exists or is a residual ℕ/geometric
  lemma. (If not banked, the linchpin can alternatively be proved as a **pure ℕ inequality**
  `minAdm(M) ≤ cCodim(tailChain M)(q−1) + (M₀−t)k`, generalising the banked `minAdm_rrp_subadd`
  (`RouteMSchurThresholdP.lean:104`, the stratum-lift codim sub-additivity) — avoiding geometry entirely.)
- The containment `Y ⊆ Z` is set-theoretic (easy); `codim Y = D + (M₀−t)k` is a generic-fibre-dimension
  add (the "A₀ kills a `k`-dim image" codim `(M₀−t)k` — actually `(M₀)·k` for the full `A₀`; reconcile
  the `t`-shift with the carrier's `Γ`-block dimension `(M₀−t)` — a bookkeeping check for the tide).

**Verification (exact):** the single-matrix-tail linchpin `minAdm(M) ≤ (m₁−q+1)(m_L−q+1) + m₀(q−1)`:
**0 violations / 546** (`/tmp/linchpin.py`, `D` exact determinantal). `α < D` for `c' < ½minAdm`: holds
always (the `α = D` cases are exactly the excluded `c' = ½minAdm` log-borderline).

---

## 3. THE CODIM `D = codim{rank(reduced tail product) ≤ q−1}` (banked)

`D = cCodim (tailChain M) (q−1)` — the product-rank-locus codim — is **BANKED** as RlctPayoffGeneral
Brick A: `codimRepCanonical Σ̄^{q−1} = cCodim d (q−1)` (via Voigt `codimRep_orbitRankLocus_eq_orbitLinearCodim`,
`Core.VoigtDischarge`, char-0; the rank-locus closedness `isZariskiClosed_orbitRankLocus` is
`Core.RankLocusClosed`). **My earlier single-bottleneck PROXY for `D` was WRONG** (underestimated it,
producing false divergences in the retracted §COUPLED-PIVOT-RESOLUTION) — the correct `D` is this
combinatorial `cCodim`, and it is large enough for the linchpin. **Caveat:** the geometric `cCodim` route
carries `[IsAlgClosed k] [CharZero k]`; the analytic finiteness works over ℝ. The bridge is that the
**real** codim of `{rank Q_b ≤ q−1}` (a real determinantal variety) equals the complex `cCodim` (both are
the determinantal codim, char-0) — a standard fact; pin whether it needs a real-vs-complex codim lemma or
is elementary (the real determinantal locus has the same codim). This is the one geometry↔analysis seam.

---

## 4. COMPOSITION → `gammaPeelIntegral M t ρ κ c' < ⊤` (closing `sjJointResolution:803`)

Per-`(t,ρ,κ)`-chart, over `A' ∈ paramsBoxM (tailChain M) 1`:
1. **Block identity + MP shear** (BANKED): `frobSq_schur_block_split` + `measurePreserving_shearSub` free
   `Γ` over its box (`RouteMSJChartAlgebra`, `RouteMSJPivotChart`).
2. **Inner `Γ`-integral via the BOX atom (§1), NOT the full-space Gram CoV.** On EVERY `A'` (full-rank
   AND rank-drop `Q_b`), the box atom (§1) gives the `A'`-a.e. bound
   `≤ Cresid((M₀−t)·r, c') · (∏σ_i(Q_b))^{−(M₀−t)} · P_tail^{−(c'−a/2)}`, `r = rank Q_b`, `a=(M₀−t)r`.
   On the full-rank slice this is the banked Gram residual; on the rank-drop strata (the wall) it stays
   finite (the `q−r` soft directions box-capped).
3. **Outer `A'`-integral.** Split `A' box = ⊔_r {rank Q_b = r}` (finite rank stratification of the
   reduced tail product). On each stratum, the box-atom bound integrates against the stratum's codim
   `D_r = cCodim(tailChain)(r−1)`-type via the linchpin (§2): `α_r < D_r`, so each stratum's contribution
   is finite; finite sum over `r`. The generic (full-rank) stratum is the banked
   `(S,J)` monomial endpoint (pieces 4/5/7 as-is); the rank-drop strata (the 750/5440 wall) are closed by
   the box atom + linchpin. **This dissolves the standing L≥3 wall.**
4. **IH usage — per-stratum, arity-clean.** Each stratum's reduced problem consumes `hIH` at the
   STRICTLY-shorter chain (`redChain t M` / `tailChain M`, arity `L+1 < L+2`) — the carrier's existing
   arity IH suffices, because the box atom's residual `P_tail^{−(c'−a/2)}` is the box integral of a
   shorter chain (`sjSubordination` `a/2 ≤ ½minAdm(tailChain M)` keeps the shifted exponent below
   threshold, BANKED). **No total-width induction needed** — the linchpin closes the deeper strata
   GEOMETRICALLY (codim), not by recursing into a same-arity sub-problem. (This corrects my earlier
   "needs total-width" claim: the same-arity `(m₀,redTail)` sub-problem is NOT re-entered; the deeper
   strata are bounded locally by the linchpin.)
5. **Reused endpoints (BANKED):** `shiftedThreshold` / `frontCharge_ge_minAdm` (exponent accounting),
   `outerRankCover` / `pivotChartCover_lintegral_le_sum` (the finite cover), `sjSubordination`,
   `monomialIntegrand_integrable_of_lt` (the monomial endpoint), `matBox_corank_residual_le` (isotropic
   box atom, the §1 stiff peel), `radial_morse_residual_power_le` (the A₀-Morse, if peeled separately).

**Net:** `sjJointResolution:803` closes by replacing the full-rank-scoped Gram CoV with the box atom (§1)
+ the per-stratum linchpin bound (§2), summed over the finite `rank Q_b` stratification. The two genuinely
NEW bricks are (§1) the box corank Γ-atom uniform over rank-drop and (§2/§3) the linchpin + the real-codim
`D` (mostly banked via Brick A / Voigt).

---

## 5. What to pin / watch (for the build tide + a reviewer)

- **NEW brick §1** (box corank Γ-atom uniform over `Q_b` rank): the load-bearing replacement. Lean shape
  in `codex/boxatom-answer.md`. Opaque-width feasibility is the main formalisation risk (the stiff/soft
  split by `rank Q_b`); Codex advises orthonormal-completion over full SVD.
- **`C = minAdm` bridge** (§2): confirm banked or land the ℕ inequality (generalise `minAdm_rrp_subadd`).
- **Real-vs-complex codim `D`** (§3): the one geometry↔analysis seam (real determinantal codim = `cCodim`).
- **The `(M₀−t)` vs `m₀` block-dimension bookkeeping** (§2 codim-`Y` add): reconcile the `t`-shift.
- **Retract-corrected:** NO (S,J) mountain, NO total-width induction, NO reducedMorseFront. The closure is
  the box atom + the linchpin, per-stratum, on the CURRENT arity IH. The single-matrix linchpin is
  0/546-verified; the general `D` is banked (Brick A).

## 6. Verification artifacts
`/tmp/linchpin.py` (linchpin 0/546, α<D), `/tmp/box_scaling.py` (box exponent MC slope −0.75≈−α),
`/tmp/fork_*.py` (the retracted lossy analysis, kept for the record). Codex: `boxatom-{prompt,answer}.md`
(box-atom Lean shape), `fork-neutral-answer.md` (the neutral both-θ-withheld confirmation of α = box
exponent). Prior cert: `cert.md` §CONCESSION (the retraction + the forkreview adjudication).
