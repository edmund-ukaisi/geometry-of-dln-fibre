# Certificate — the two analytic facts of the smeared L=2 R1-LOWER leg, ADJUDICATED

**Seat:** pen-and-paper (adjudication; exact algebra + decorrelated Codex; NO Lean). **Date:** 2026-06-29.
**Branch:** `pnp/smeared-l2-adjudicate` (off `expedition/aoyagi-full`). **Scope of the dispatch:** the two
isolated analytic hypotheses left by `genm-smeared4`'s `routeMCore_smearedL2` (the L=2 smeared headline,
∀ opaque widths). Read against the source on `origin/genm-smeared4`
(`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedDecodeL2.lean` + `…/RouteMSmearedHeadlineL2.lean` +
`…/RouteMSmearedProjCancel.lean` + `…/RouteMSmearedFrontFactor.lean`), the `(2,3,1)` anchor
(`…/RouteM231Smeared.lean`), and `certificate-genM-smeared.md` §1–3.

## The exact objects (from source, not paraphrase)

`M : Fin 3 → ℕ`; widths `M0, M1, M2`. The chart vector `u : Fin (routeMAmbient M) → ℝ`. A split
`hrs : r + s = M1`, `0 < r`, `0 < M2`. From `RouteMSmearedDecodeL2.lean`:

- `A0u u` — the FREE front matrix `M0 × M1` (entries are direct flat coords `u (coordOf (frontSlot i j))`).
- `P1u = A0u[:, deepWidthEquiv(inl)]` (`M0 × r`); `P2u = A0u[:, deepWidthEquiv(inr)]` (`M0 × s`).
- `Lam0u = (P1uᵀP1u)⁻¹ P1uᵀ P2u` (`r × s`).
- `HbarUnit` — `r × M2` angular unit, pivot `(⟨0⟩,⟨0⟩) = 1`, others free top coords.
- `Sbotu` — `s × M2` free residual.
- Decoded deep factor (`chartL2Deep`): top `r` rows `= z·H̄ − Λ₀·S_bot`, bottom `s` rows `= S_bot`.

**Fact (1) — `hcancel`:** `P1u · Lam0u = P2u` on each peeled point.
Banked `Lam0u_cancel_of_factoring` reduces it to `P2u = P1u·K` (col(P₂) ⊆ col(P₁)) **+** `det(P1uᵀP1u) ≠ 0`.

**Fact (2) — field A:** `hSpre : condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ ⊆ (ψ∘R)⁻¹(cubeBox ε)`, plus
`hUpos`. Mechanism (from `(2,3,1)`): every decoded flat coord is a matrix entry; bound each `≤ ε` (`ε = 2δ`).
The load-bearing input is a uniform bound on `‖Λ₀‖` on the conditioned box.

---

## HEADLINE ANSWER

**The smeared L=2 leg is UNCONDITIONALLY ∀M-closeable, BUT only because the genuine smeared L=2 stratum
forces `r = M0` (square `P₁`). The Lean theorem `routeMCore_smearedL2` is stated more generally than the
stratum it serves (it takes `r` as a free split parameter); its two hypotheses are dischargeable exactly on
the square slice `r = M0` (equivalently `M0 < M1`), which is the ENTIRE genuine smeared L=2 stratum.**

So: **not scope-limited within the smeared L=2 stratum** (every smeared L=2 `M` is `M0 < M1`, `r = M0`,
and both facts close); **scope-limited as a statement about the bare theorem's free `r`** (a formaliser must
instantiate `r = M0`, not an arbitrary split — at `r < M0` Fact (1) is FALSE for the free `A0u`).

---

## CERTIFICATE 1 — the off-pole cancellation

### The exact regime the smeared stratum requires (the resolution of the `r`-tension)

For L=2 the "front product" is layer 0 alone: `P = A⁰`. The front-bottleneck structural fact
(`certificate-genM-smeared.md` §1, validated 652/652) gives `deepRank = r = min(M0,…,M_{L−1}) = min(M0,M1)`.
The smeared sub-class is `deepRank < deepRows` (`RouteMBoundaryClass.lean`), and `deepRows = Wext M (L−1) = M1`.
So **smeared L=2 ⟺ `r = min(M0,M1) < M1`**, which forces `M0 < M1` and `r = M0`.

| regime | `r = min(M0,M1)` | `s = M1 − r` | `P₁` shape | smeared? |
|---|---|---|---|---|
| `M0 < M1` | `M0` | `M1 − M0 > 0` | `M0 × M0` **square** | **YES** |
| `M0 = M1` | `M0` | `0` | square | no (`s=0`, cancellation vacuous) |
| `M0 > M1` | `M1` | `0` | tall | no (`s=0`, cancellation vacuous) |

`fact1_l2_enum.py`: every smeared (`s>0`) L=2 case is `M0 < M1`, `r = M0`, `P₁` square. **There is no
smeared L=2 configuration with `s > 0` and a genuinely tall `P₁`** (a tall `P₁` needs `M0 > M1`, which
forces `s = 0`).

### The exact factoring identity (square case)

For square `P₁` (`r = M0`) invertible: `col(P₁) = ℝ^{M0} ⊇ col(P₂)`, so `K := P₁⁻¹·P₂` satisfies
`P₂ = P₁·K` for **any** `P₂`. Then `Lam0u = (P₁ᵀP₁)⁻¹P₁ᵀP₂ = P₁⁻¹P₂ = K` and `P₁·Λ₀ = P₂`. The det
condition `det(P₁ᵀP₁) = det(P₁)² ≠ 0` is exactly `P₁` invertible. (This is the `(2,3,1)` `P1_lam231`
pattern; banked `proj_cancel_of_factorsThrough` consumes `(K, hfac, hdet)`.)

### What FAILS, and where the boundary bites (exact-algebra, `fact1_cancel.py` / `fact1_confirm.py`)

- **Square free `A0u` (`r = M0`):** `P₁·Λ₀ = P₂` holds ∀ free `A0u` off the pole. ✓ (symbolic + exact-rational)
- **Tall free `A0u` (`r < M0`):** FAILS. Exact rational point `M0=3,M1=3,r=2`: `det(P₁ᵀP₁)=289525/144 ≠ 0`,
  residual `P₁Λ₀−P₂ ≠ 0`. (Codex's minimal witness: `M0=2,M1=2,r=1`, `P₁=[1;0]`, `P₂=[0;1]`, `Λ₀=0≠P₂`.)
  This is the regime a free-`r` instantiation of the bare Lean theorem would hit — but it is **outside the
  smeared L=2 stratum** (`r < M0` with `s > 0` needs `M0 < M1` AND `r < M0`, contradicting `r = min(M0,M1)`).
- **Wide (`r > M0`):** `det(P₁ᵀP₁) ≡ 0` symbolically (Gram rank `≤ M0 < r`) ⟹ the off-pole regime is **empty**.

### Proof structure for the formaliser

Discharge `hcancel` via `Lam0u_cancel_of_factoring M hrs u K hfac hdet` with, at `r = M0`:
- `K := (P1u)⁻¹ * P2u` (square inverse);
- `hfac : P2u = P1u * K` — from `P1u * (P1u)⁻¹ = 1` (`Matrix.mul_nonsing_inv`, needs `det P1u ≠ 0`);
- `hdet : det(P1uᵀ P1u) ≠ 0` — from `det(P1uᵀP1u) = det(P1u)²` and `det P1u ≠ 0`.

`det P1u ≠ 0` is supplied by the conditioned box (Certificate 2: strict diagonal dominance ⟹ invertible
**everywhere on the box**, not merely a.e.). NOTE the existing `front_factorsThrough_general` /
`frontShear_cancel_general` (banked) prove the general-`r` tall case via a `U·V` factorization of the
front PRODUCT — but that needs `A0u` to BE a constrained rank-`r` product, which the chart's free `A0u` is
not. For L=2 the square route is both correct and simpler; the general-`r` machinery is for L ≥ 3 (where
the front is a genuine product `A⁰···A^{L−2}` of generic rank `r = min` < its column count).

---

## CERTIFICATE 2 — field A (the conditioned `Λ₀` inverse-norm bound), square case `r = M0`

### The conditioned box and the bound

Conditioning (the opaque-width `subBox231` shape, with the off-diagonal width a per-`r` FREE box choice):
diagonal of `P₁` (front coords) in `[δ/2, δ]`; all off-diagonal `P₁` entries, all `P₂` entries, all
`H̄`-angular and `S_bot` entries in `[−η, η]`; pivot `z ∈ (0,δ)`.

Choose `η = δ/(4(r−1))` for `r ≥ 2`, `η = δ/4` for `r = 1`. (The `(2,3,1)` anchor uses `η = δ/8`, which
is the `r ≤ 4` special case — see scope note.)

**The estimate chain (`varah.py`, `fact2_verify.py`, `fullcheck.py`):**

1. **Strict diagonal dominance.** Row margin `γ = δ/2 − (r−1)·η = δ/4 > 0` (`r ≥ 2`; `γ = δ/2`, `r = 1`).
   ⟹ `P₁` strictly diagonally dominant ⟹ `det P₁ ≠ 0` **at every point of the box** (Levy–Desplanques),
   so `det(P₁ᵀP₁) ≠ 0` on the box — the off-pole condition of Certificate 1 is discharged unconditionally.
2. **Varah inverse bound.** `‖P₁⁻¹‖_∞ ≤ 1/γ = 4/δ` (`r ≥ 2`; `2/δ`, `r = 1`).
3. **`Λ₀ = P₁⁻¹P₂` (square), entry bound.** `‖Λ₀‖_∞ ≤ ‖P₁⁻¹‖_∞ · ‖P₂‖_∞ ≤ (4/δ)·(s·η) = s/(r−1)`
   (delta-INDEPENDENT; `r = 1`: `≤ s/2`). Anchor `(2,3,1)`: `s/(r−1) = 1` vs the file's looser `9/8`.
4. **Containment `≤ 2δ`.** Decoded deep-top entry `|z·H̄_aj − (Λ₀·S_bot)_aj| ≤ |z|·|H̄_aj| + ‖Λ₀‖_∞·(M2·η)
   = O(δ)`; front and deep-bottom entries `≤ δ`. With the box above every flat coord is `≤ 2δ`, so
   `condBox ⊆ (ψ∘R)⁻¹(cubeBox 2δ)`. `U`-positivity `‖P₁·H̄‖² > 0` follows from `P₁` invertible and
   `H̄(0,0)=1` (`U ≥ |P₁ e₀|² > 0`).

`fullcheck.py` end-to-end (cancellation + full containment): `(2,3,1)`, `(2,4,2)`, `(3,5,2)`, `(1,4,3)`,
`(5,7,2)` — 0 cancel-fails, 0 containment-fails, max decoded entry `< 2δ` (each over 120 exact-rational pts).

### Scope note (load-bearing, decorrelated-confirmed by Codex)

The **specific** `(δ/2, δ/8)` conditioning of `(2,3,1)` is diagonally dominant only for `r ≤ 4`
(`γ = δ(5−r)/8 > 0 ⟺ r ≤ 4`). Codex's exact counterexample (`codex_ce.py`, confirmed): for `r ≥ 5`,
`B_ii = 1/2`, `B_ij = −1/(2(r−1))` lies in the `δ/8` box (`|B_ij| ≤ 1/8`) yet is SINGULAR (`B·1 = 0`,
`det = 0`); a perturbation `B_ij + t` makes `‖Λ₀‖ ~ 1/t` blow up. So field A with the **fixed** `δ/8`
width does NOT generalize past `r = 4`. The FIX is purely a per-`r` box choice (`η = δ/(4(r−1))`), which
is a free parameter of the Lean `condBox`/`box` — **not** a math obstruction. For the formaliser: do not
hard-code `δ/8`; scale the off-diagonal/residual width with `r`.

---

## Decorrelation (Codex, xhigh)

Fired `/local-codex-consult` with hypothesis withheld (`smeared-l2-prompt.md` / `smeared-l2-answer.md`).
Codex independently reached: Q1 cancellation holds generically iff `r = M0`; L=2 bottleneck ⟹ only `s>0`
case is `M0<M1`, `r=M0` square, no tall-with-`s>0` exists; Q2 `‖Λ₀‖ ≤ 1/(5−r)` for the `δ/8` box at
`r ≤ 4`, and the sharp `r ≥ 5` singular counterexample inside the `δ/8` box. Full agreement on every
load-bearing point; its `r≥5` counterexample sharpened the field-A scope note (verified exactly here).

## Verdict

- **Fact (1):** CERTIFIED closeable ∀ smeared L=2 `M`, via the square route `r = M0` (the entire stratum).
  Identity: `K = P₁⁻¹P₂`, `det P₁ ≠ 0` from the conditioned box. Scope boundary: FALSE for free `A0u` at
  `r < M0` (outside the stratum) — the bare theorem's free `r` must be instantiated at `M0`.
- **Fact (2):** CERTIFIED closeable ∀ smeared L=2 `M`, via strict diagonal dominance + Varah, with the
  off-diagonal box width scaled `η = δ/(4(r−1))`. `‖Λ₀‖_∞ ≤ s/(r−1)` (δ-free). The `(2,3,1)` `δ/8` box is
  the `r ≤ 4` special case; do not hard-code it.

## Most likely thing to break it / next step

- **Risk:** a formaliser proves a `∀ r` lemma off the bare theorem and trips the `r < M0` failure of Fact
  (1). MITIGATION: state the Lean lemma's applicability hypothesis as `r = M0` (or `M0 < M1` with
  `r := M0`), naming the theorem by its true scope ("for the smeared L=2 stratum `M0 < M1`, …"), and pass
  `det P1u ≠ 0` from the diagonally-dominant box, not as a bare a.e. assumption.
- **Next construction:** the formaliser's two bricks — (a) `det P1u ≠ 0` on `condBox` via Levy–Desplanques
  (Mathlib `Matrix.det_ne_zero_of_…`/diagonal-dominance; if absent, a direct Gershgorin/Hadamard argument),
  and (b) the `‖Λ₀‖_∞ ≤ s/(r−1)` Varah bound feeding the per-entry `≤ 2δ` containment. Both are square-`P₁`
  facts; no tall-`P₁` machinery needed at L=2.
- **Open (out of L=2 scope):** for L ≥ 3 the front is a genuine product and `P₁` is tall with col(P₂) ⊆
  col(P₁) imposed by the front-bottleneck; there the banked `front_factorsThrough_general` is the right
  tool. That is the genm-smeared general-L leg, not this one.
