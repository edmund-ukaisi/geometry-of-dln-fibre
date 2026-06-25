# Genuine-diffeo `(3,3,4)` chart spec — the per-node honest c-o-v atom (replaces degenerate `phi334`)

**Seat:** `pen-and-paper` (CONSTRUCT, build-ready spec). **Date:** 2026-06-24.
**Purpose:** the precise, formaliser-ready spec for the GENUINE-DIFFEO `(3,3,4)` chart replacing the
degenerate `phi334` (dropped `u₂,u₃` → Jacobian `det ≡ 0` → null image → false `cov = ⊤`). This is the
**shared per-node c-o-v atom** that unblocks BOTH `hdiv` (one leaf) and `hfin` (the recursion).
**Method:** exact sympy (the Jacobian determinant + the loss factorization, NOT floats); every
load-bearing identity verified symbolically.
**Artefacts:** `/tmp/genuine_chart_334{c,d,e,f,g,h}.py` (the construction + the degeneracy diagnoses +
the deepest-point tension). The load-bearing verified file is `/tmp/genuine_chart_334c.py`.

> **Soundness banner (read first).** This spec has TWO honest layers. **Layer 1 (the normal-form
> chart, FULLY VERIFIED-EXACT):** a genuine `(Fin 21 → ℝ) → (Fin 21 → ℝ)` diffeo, all 21 coords live,
> `det Dφ = −u₀⁷` (sympy-exact, not `≡0`), `F∘φ = u₀²·U` (sympy-exact), `U` bounded both sides. This is
> the build-ready replacement for `phi334`'s broken `cov` and the degeneracy is FIXED. **Layer 2 (the
> deepest-point reach, a flagged residual):** the Layer-1 chart's image sits at a NON-deepest point of
> the zero-fibre `{AC=0}`; reaching the flat origin (which the `cover_ge_div` box is centred on) needs
> an additional measure-preserving orbit-straightening — the genuine `a=0` content. I give its precise
> structure and TWO sound discharge options; I do NOT claim it as verified. **The naive "just scale
> everything by `u₀`" deepest-point chart is REFUTED here (`det = u₀¹⁰`, wrong threshold 5½) — do not
> build it.**

---

## 0. The degeneracy of `phi334`, exactly

`chartA334`/`chartC334` (`RouteMLayerCoverGEL2.lean:207,214`) hardwire `A(0,1) = A(0,2) = 0` (the cross
strip `b`), so the chart map **never reads input coords `u₂, u₃`**. As a map `(Fin 21 → ℝ) → (Fin 21 →
ℝ)`, two of its Jacobian columns (for `u₂, u₃`) are identically zero ⟹ `det Dφ ≡ 0` ⟹ the image is a
codim-≥2 null subvariety ⟹ the change-of-variables field `cov` (which asserts the box integral equals
the pulled-back integral) reduces to `0 = ⊤`, FALSE. The factorization `F∘φ = u₀²·U` and the divergence
ASSEMBLY are sound and reusable; only the c-o-v is broken, and it is broken because **coords were
dropped**, not for a subtle measure reason.

**The non-negotiable for the replacement:** every one of the 21 input coords appears in the chart map,
so no Jacobian column is zero. Verified below by computing `det Dφ` symbolically (it is `−u₀⁷ ≠ 0`).

---

## 1. The genuine normal-form chart `φ` (Layer 1 — VERIFIED-EXACT, build-ready)

Flat `(3,3,4)` coords: `A` (3×3, 9 coords), `C` (3×4, 12 coords), total 21. Block `A = [[a,b],[c,E]]`
(`a` scalar `1×1`, `b` `1×2`, `c` `2×1`, `E` `2×2`); `C = [[y],[S]]` (`y` `1×4`, `S` `2×4`).

**The 21 chart coordinates `u : Fin 21 → ℝ` and their roles** (`/tmp/genuine_chart_334c.py`):

| chart coord | role | scaled by `u₀`? |
|---|---|---|
| `u₀` | the PIVOT / binding axis (the blow-up centre) | — (it IS the pivot) |
| `u₁ = a` | the pivot-minor `A(0,0)` (spectator; on the box `a ∈ [½,1]`) | no |
| `u₂ = b₀`, `u₃ = b₁` | the cross strip `b = (A(0,1), A(0,2))` (spectator) — **the coords `phi334` dropped** | no |
| `u₄ = c₀`, `u₅ = c₁` | the column `c = (A(1,0), A(2,0))` (spectator) | no |
| `u₆…u₉ = Δ` | the `2×2` residual `D`-block direction, BLOWN UP | yes (`E = u₀·Δ + c·a⁻¹b`) |
| `u₁₀…u₁₂ = τ` | the top-row direction `(1,τ)`, BLOWN UP | yes (`T = u₀·(1,τ)`) |
| `u₁₃…u₂₀ = S` | the `2×4` free block (spectator, 8 coords) | no |

**The chart map (flat output, all 21 coords read):**

      A(0,0) = a = u₁
      A(0,1) = b₀ = u₂,   A(0,2) = b₁ = u₃          ← READ (phi334 set these to 0)
      A(1,0) = c₀ = u₄,   A(2,0) = c₁ = u₅
      E = A[1:3,1:3] = u₀·Δ + c·a⁻¹·b                ← the shear correction (so D = E − c·a⁻¹b = u₀·Δ)
      C[0,:] = y = u₀·(1,τ) − a⁻¹·b·S                ← the inverse shear (so T = y + a⁻¹b S = u₀(1,τ))
      C[1:3,:] = S = (u₁₃…u₂₀)

The `a⁻¹` is the Schur-shear term; it is **regular on the box** because `a = u₁ ∈ [½,1]` is bounded
away from 0 (the shear singularity is at `a=0`, which the box excludes — see §3 for why this is the
honest move and where the deepest-point subtlety enters).

**(i) All 21 coords live — `det Dφ = −u₀⁷` (sympy-exact, `/tmp/genuine_chart_334c.py`).** The Jacobian
of the 21 flat outputs against the 21 chart coords has determinant `−u₀⁷`, i.e. `|det Dφ| = |u₀|⁷`,
**not `≡ 0`**. (The `phi334` failure mode — zero columns for `u₂,u₃` — cannot recur: `b₀=u₂`, `b₁=u₃`
appear in both `A(0,1),A(0,2)` and in the shear corrections to `y` and `E`.)

**(ii) `F∘φ = u₀²·U` (sympy-exact, same file).** The shear cancels the stray `b·S` term: `A·C =
[[a·u₀·(1,τ)], [c·u₀·(1,τ) + u₀·Δ·S]]`, so `F = ‖A·C‖² = u₀²·U` with `U = a²‖(1,τ)‖² +
‖c·(1,τ)+Δ·S‖²` exactly the banked `Uval334` (`RouteMLayerCoverGEL2.lean:72`). `U` is `u₀`-free.
**This is the SAME `U` already banked** — the new chart reproduces `dlnLoss_chartParams334`'s
factorization, so the downstream divergence assembly is unchanged.

**(iii) The unit is bounded BOTH sides on the box** (better than `phi334`). `U ≥ a² ≥ ¼ > 0`
everywhere on the box (`Uval334_ge_sq` + `a = u₁ ≥ ½`), and `U` is continuous on the compact box ⟹
`U ≤ B` for some `B`. So `U ∈ [¼, B]` and `U^{−c'} ∈ [B^{−c'}, 4^{c'}]` — **no vanishing-`U` locus to
drop** (unlike `phi334`, whose `a = u₁` was unconstrained so `U → 0` was possible). The divergence drop
`U^{−c'} ≥ B^{−c'} > 0` is clean.

**(iv) InjOn + image off the null exceptional set.** `φ = (Schur shear, a triangular det-1 diffeo) ∘
(pivot blow-up of the 8 active coords)`. The pivot blow-up `pivotBlowupOn` is `InjOn` off `{u₀=0}`
(banked, `S1G5Charts`); the shear is a global diffeo (triangular, `a⁻¹` regular for `a≥½`). The
composite is `InjOn` off `{u₀=0}` (a codim-1 null set). Because `det Dφ = −u₀⁷ ≠ 0` off `{u₀=0}`, `φ`
is a **local diffeo there**, so its image is full-dimensional (open) off the exceptional divisor ⟹
**positive measure** — the `phi334` null-image defect is fixed.

**Binding axis / threshold (unchanged, banked):** the binding axis is `u₀` with `(k,h) = (1,7) =
(1, minAdm−1)`, threshold `(7+1)/2 = 4 = ½·minAdm` (`leafK334`/`leafH334`,
`leafMonomialThreshold334_le`). The leaf integrand `|u₀|⁷·(u₀²·U)^{−c'}` diverges iff `c' ≥ 4`.

---

## 2. The Jacobian verification (the anti-`phi334` check) — DO THIS IN LEAN

The single check that would have caught the `phi334` slip: **`det Dφ ≢ 0`.** Two ways for the
formaliser to discharge it (the sympy value is `−u₀⁷`):
1. *Structural:* `φ = shear ∘ pivotBlowup8`; `det(shear) = 1` (triangular, unit diagonal — the Schur
   shear is `id + (strictly-lower-triangular)`), `det(pivotBlowup8 Deriv) = u₀^{8−1} = u₀⁷`
   (`pivotBlowupOnDeriv` det, banked for active.card = 8). Product `= u₀⁷ · 1`. **No 21×21 determinant
   blow-up** — factor through the two pieces.
2. *Direct (cross-check only):* the sympy `det` of the explicit 21-coord map is `−u₀⁷`
   (`/tmp/genuine_chart_334c.py`); a per-entry Lean `Matrix.det` would time out — use route 1.

The `cov` field then holds via Mathlib's `MeasureTheory.integral_image_eq_integral_abs_det_fderiv` (or
`lintegral_image_eq…`) on `{u₀ ≠ 0}` (det `≠ 0`, InjOn), with the null `{u₀=0}` dropped. **This is the
field that was `sorry`/false in `phi334`; it is now closable because `det = −u₀⁷ ≠ 0`.**

---

## 3. The deepest-point reach (Layer 2 — the genuine `a=0` content; FLAGGED, not verified)

**The honest gap.** `cover_ge_div` integrates over the cube `[−ε,ε]^N` centred on the **flat origin**
(the deepest point `A=C=0`). The Layer-1 chart has `a = u₁ ∈ [½,1]`, so `φ(0,a,0,…) = (A=diag(a,0,0),
C=0)` — a point of norm `~1`, a NON-deepest point of the zero-fibre `{AC=0}` (where `F=0` too, since
`diag(a,0,0)·0 = 0`). So `φ(box) ⊄ [−ε,ε]^N`; the Layer-1 chart does **not** directly lower-bound the
origin's box integral. Forcing `a → 0` to reach the origin re-introduces the shear singularity `a⁻¹` —
**this is the genuine `a=0` obstruction, correctly located** (it is about reaching the deepest point,
not about reading `b`).

**Why the naive fix is WRONG (refuted, `/tmp/genuine_chart_334h.py`).** "Scale everything by `u₀` to
reach the origin" gives `det = u₀¹⁰` (active set of 10, not 8) ⟹ binding axis `(1,9)` ⟹ threshold
`(9+1)/2 = 5½ ≠ 4`. Over-scaling inflates the threshold. **Do not build this.** The active set must be
EXACTLY the 8 codim-normal coords; the other 13 (orbit-tangent) directions must NOT carry the pivot.

**The clean Layer-2 structure (the deepest-point coupled resolution).** `φ_deep = orbitStraighten ∘
pivotBlowup8`:
- `pivotBlowup8`: blow up exactly the **8 codim-normal coords** (`Δ`-block 4 + `T`-row 4) by `u₀`;
  Jacobian `u₀⁷`; the 13 orbit-tangent coords are free in a small box. `F∘pivotBlowup8 = u₀²·U` in
  normal-form coords (= the Layer-1 factorization).
- `orbitStraighten`: the measure-preserving (det-1) diffeo from flat coords to (normal, orbit-tangent)
  coords. This is **Aoyagi's Lemma 2 as a GLOBAL change of variables**, not a pointwise `a⁻¹`. The
  resolution writes `a = u₀·â` with `â ∈ [½,1]` (the *direction* of `a`, bounded away from 0), so the
  shear becomes `a⁻¹b = â⁻¹b̂` — **regular**. The achiever curve is then `{u₀ → 0}` with `â` free,
  reaching the origin as `u₀ → 0` while the shear stays regular. This is exactly the **corank-2
  coupling** (`a` and `b` enter the exceptional blow-up together) that the `hfin` design certificate
  (§3, the monomial-sum refinement) and the light-recursion obstruction (`verify-r1-light-recursion.md`)
  identified — confirming the unification: **this Layer-2 atom IS the `hfin` per-node coupled chart.**

**TWO sound discharge options for Layer 2** (for the controller / formaliser to choose):
- **(A) Build `orbitStraighten` (the clean, gap-free route).** The measure-preserving orbit c-o-v +
  the corank-2 blow-up reaching the origin. This is the genuine per-node atom; it is the same Lemma-2
  straightening the L2 gauge-chart work (`DeepestGauge*`) already builds, re-homed to the resolution
  chart. Recompute `det` (expected `u₀⁷` with the 8-active set + the det-1 straightening) — do NOT let
  the active set grow to 10.
- **(B) Orbit-homogeneity transfer (lighter, if the architecture allows).** `F` vanishes to the same
  order along the smooth locus of `{AC=0}` (the loss is invariant under the `GL`-orbit action that
  moves `(diag(a,0,0),0)` to the origin's neighbourhood). If the box integral around the origin equals
  (up to the orbit volume) the integral around `(diag(â,0,0),0)`, the Layer-1 chart at `â ∈ [½,1]`
  computes the same divergence. This needs the homogeneity/orbit-invariance lemma (the loss is
  `GL`-equivariant) — possibly already available from the `LossHomogeneity` / `NodeHomogeneity` modules.

**Recommendation:** option (A) — it is the gap-free deepest-point resolution and IS the reusable `hfin`
per-node atom, so building it serves both legs (the unification). Option (B) is a shortcut worth
checking only if `LossHomogeneity` already supplies the orbit-invariance cheaply.

---

## 4. The monomial-sum refinement — SEPARATE composition, NOT part of this chart

The monomial-sum refinement (the `hfin` §3 crux — turning a disjoint sum `r²U_T + a²s²U_D` into a
single-monomial leaf) is a **further blow-up composed AFTER** this per-node chart, not part of it. The
`(3,3,4)` single node already lands a single monomial `u₀²·U` (the `L=2` RRR node is the leaf — no
disjoint sum at this depth), so **the refinement is NOT needed for the `(3,3,4)` chart itself**. It
enters only for `L ≥ 3` (where the residual `U` recurses and disjoint sums appear) or when assembling
multiple nodes. So: build this chart standalone (Layers 1+2); the refinement is a later, separate lemma.

---

## 5. Build order for the formaliser (the de-risked path)

1. **Layer 1 first** (verified-exact, lowest risk): replace `chartA334`/`chartC334` with the §1 map
   (read `u₂,u₃`; fold the shear into `y`,`E`). Re-prove `dlnLoss_chartParams334` (same `Uval334`, same
   `ring` — the factorization is identical). Prove `det Dφ = −u₀⁷` via the structural route (§2,
   `shear` det-1 × `pivotBlowup8` det `u₀⁷`) — **the anti-`phi334` check**. Close `cov` via Mathlib's
   det-Jacobian image lemma on `{u₀≠0}`. This banks a genuine chart with `det ≠ 0` and fixes the slip.
2. **Layer 2** (the deepest-point reach): build `orbitStraighten` (option A) so `φ(box) ⊆ [−ε,ε]^N`
   reaching the origin, OR invoke orbit-homogeneity (option B) if `LossHomogeneity` supplies it.
   Recompute `det` — guard the active set at 8 (threshold 4), NOT 10 (the refuted `u₀¹⁰`).
3. The divergence ASSEMBLY (`routeM334_box_diverges_of_chart`) and the leaf-integrand identity are
   already banked sorry-free and consume the chart bundle unchanged.

---

## 6. Caveats, scope, what would break this

- **Layer 1 is VERIFIED-EXACT; Layer 2 is FLAGGED, not verified.** I have the symbolic `det = −u₀⁷`
  and `F∘φ = u₀²U` for the normal-form chart (Layer 1). The deepest-point reach (Layer 2) I have only
  STRUCTURED (the two options) — I refuted the naive over-scale (`u₀¹⁰`) but did not build the
  `orbitStraighten` det. The formaliser must recompute the Layer-2 Jacobian and guard the threshold at 4.
- **The single thing most likely to break it:** Layer 2's `orbitStraighten` det growing past `u₀⁷` (the
  over-scale trap, refuted at `u₀¹⁰`). The active set MUST be the 8 codim-normal coords; the 13
  orbit-tangent directions must be straightened (det-1), not blown up. If the straightening accidentally
  scales an orbit direction, the threshold inflates and the value is wrong.
- **Levels separate.** This is the chart (the geometric c-o-v) + its `F∘φ = u₀²U` factorization. The
  value `½·minAdm = 4` and the `rlct = ½·codim` reading are unchanged (the cited bound). S2
  (`monomial_rlct`) is the only citation, at the leaf.
- **The degeneracy class to avoid (the lesson):** any chart that omits an input coord (a zero Jacobian
  column) has `det ≡ 0` and a null image — the `phi334` failure. **The det-`≠0` check (§2) is the gate.**
