# Design review: cleanest formalization decomposition for a joint change-of-variables finiteness

You are a second, decorrelated expert (measure theory + real algebraic geometry + Lean 4/Mathlib
formalization). I want your INDEPENDENT read on the cleanest way to prove ONE finiteness statement in Lean.
Argue for whatever decomposition you think is cleanest; I am withholding my own tentative plan so as not
to anchor you. Be concrete about the change-of-variables SEQUENCE and where each is a measure-preserving
shear vs a genuine Jacobian CoV.

## The setting (deep linear network RLCT; a single "shell" estimate)

Fix naturals `u, a = M₀−u, b = M₁−u` (corner dims), `M₂`, `n` (`= M_last`), with `1 ≤ a,b` and the SCOPE
`a + b ≤ M₂` and `b ≤ M₂ ≤ n`. Fix a real exponent `c'` with `ab/2 < c' < T1`, where
`T1 = ½·minAdm(M)` and `minAdm(M) = min_{0≤t≤min(M₀,M₁)} [(M₀−t)(M₁−t) + t·minAdm(redChain t M)]`
(a layer-peeling recursion; `redChain t M = (t, M₂, …, M_last)`). Set `q = c' − ab/2`.

Variables (all real matrices, all integrated over `[−1,1]`-entry boxes unless noted):
- `z` : the deep parameters. Through a "head split" they yield a DEEP FACTOR `Z_deep = Z_deep(z)`, an
  `M₂ × n` matrix, and a pivot row block `Q_p = (z₀)·Z_deep`, `u × n` (`z₀` a `u × M₂` block of `z`).
  `Z_deep` is generically full row rank `M₂` (this is a threaded genericity hypothesis; assume it).
- `A_cor` : a `b × M₂` matrix. The corank row block is `Q_b = A_cor · Z_deep`, `b × n`.
- The full stack `hsQ = [Q_p ; Q_b] = [z₀ ; A_cor] · Z_deep`, an `(u+b) × n` matrix.
- Front block `x = (P, B₁₂, C)` : `P : u×u` (restricted to the invertible-`P` chart `IsUnit P`),
  `B₁₂ : u×b`, `C : a×u`, over a box.

Define (all `frobSq` = sum of squares of entries):
- `Q̃ₚ = Q_p + P⁻¹·B₁₂·Q_b`  (`u × n`).
- `E_top = frobSq(P·Q̃ₚ)`. On the invertible-`P` chart this equals `frobSq(P·Q_p + B₁₂·Q_b)` (a
  polynomial, no inverse) — I have this identity.
- `Π_b = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b` (orthogonal projection onto row(Q_b)); `E_tr = frobSq(C·Q̃ₚ·(I − Π_b))`.

The Γ-block (a `a×b` corank matrix) has ALREADY been integrated out (a banked "morse peel"), producing the
COUPLED corank charge `det(Q_b Q_bᵀ)^{−a/2} · Cresid(ab,c')` (`Cresid` a finite positive constant) and the
exponent shift `c' → q`. So the object left is:

    frontChargeIntegral :=
      ∫_{z∈box} ∫_{A_cor∈box}  det(Q_b Q_bᵀ)^{−a/2} · Cresid ·
          [ ∫_{x∈box, IsUnit P}  (E_top + E_tr)^{−q}  dx ]  dA_cor dz         (all `ofReal`, in ℝ≥0∞)

**GOAL: prove `frontChargeIntegral < ⊤`** for `ab/2 < c' < T1`, in scope `a+b ≤ M₂`. (I do NOT need the
exact value or an exact ratio to a comparator — only `< ⊤`. But note the finiteness is genuinely JOINT:
the inner `∫_x` front loss is NOT uniformly finite in `(z,A_cor)` — on the locus where `Q_p` degenerates
into `row(Q_b)` it blows up like `δ^{k−2q}`; the finiteness only holds after the `(z,A_cor)`-integration,
whose codimension absorbs the front blow-up.)

## Banked Lean pieces I can consume (all sorry-free)

1. `det_chartGram`: on the minor chart `Q_b = D·[I_b | X]` (`D : b×b` invertible, `X : b×d`, `n_cols = b+d`),
   `det(Q_b Q_bᵀ) = (det D)² · det(I_b + X Xᵀ)`. The rank-drop singularity is entirely `(det D)²`;
   `det(I+XXᵀ) ≥ 1` is a `D`-independent bounded unit.
2. `transverseSchurGram`: for `Q_p = [U | U X + W]`, `Q_p (I − Π_b) Q_pᵀ = W (I + Xᵀ X)⁻¹ Wᵀ`
   (the transverse energy carried entirely by `W = Q_p·N`, `N = [−X; I_d]`; `I+XᵀX` a bounded unit).
3. `chart4_Htilde_fibre_lt_top`: `∫_{H̃ ∈ ℝ^N} (‖H̃‖² + τ²)^{−q} dH̃ < ⊤` for `τ>0` and `2q > N`
   (and `= τ^{N−2q}·K`, `K = ∫(‖V‖²+1)^{−q}` finite iff `2q>N`).
4. `chart5_bigcell_cov`: the determinantal big-cell CoV of `W` — on `{det W₁₁ ≠ 0}`,
   `W ↦ (W₁₁,W₁₂,W₂₁, E)`, `E = W₂₂ − W₂₁W₁₁⁻¹W₁₂` the Schur complement, Jacobian ≡ 1 (a `W₂₂`-translation,
   measure-preserving unconditionally); `rank W ≤ ℓ ⟺ E = 0`.
5. `clsCodim_gate_genL`: the exponent gate. For a valid stratum `(ℓ,s)` at cut `u`, `minAdm(M) ≤ C_{ℓ,s} + ab`
   where `C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)` is the joint-stratum normal codimension. Consequence
   (an exact ring identity): `C_{ℓ,s} + ab = (M₀−s)(M₁−s) + s·M₂`, INDEPENDENT of ℓ, and `min_{ℓ,s} C_{ℓ,s}/2
   = T1 − ab/2 = T1_q`. So `q < T1_q ≤ C_{ℓ,s}/2` for every stratum.
6. `lintegral_lt_top_of_finset_cover`: if a finite family of measurable cells covers the domain up to a null
   set and each cell has finite integral, the domain integral is finite.
7. `corankBlock_morsePeel_setLE` (already used to produce the charge): the Γ-peel.
8. A radial polar factor `∫_{ℝ^N} f = ∫_{sphere} ∫_{r>0} r^{N−1} f(r·ω)`, and a matrix version.

## Hard constraint (Lean measure diamond)

Matrix-space Lebesgue CoV hits an instance diamond: `Matrix.module` vs `NormedSpace.toModule`. The Haar CoV
lemma `map_linearMap_addHaar_eq_smul_addHaar` / `lintegral_image_eq_lintegral_abs_det_fderiv_mul` needs the
NormedSpace-derived module instance; a `LinearMap` built over `Matrix.module` sits on the other branch and
won't unify. The banked workaround: transcribe the CoV map over the RAW pi type `Fin _ → Fin _ → ℝ`,
column-indexed, where left-multiplication is block-diagonal per column so `det` factors via `det_pi`.

## My questions (please answer each concretely)

**Q1 (the general-`L` reduction — the crux).** Everything factors through `hsQ = R · Z_deep` with
`R = [z₀ ; A_cor]` an `(u+b)×M₂` "reduced stack" and `Z_deep` an `M₂×n` generic full-rank deep factor.
The charge `det(Q_bQ_bᵀ) = det(A_cor·Z_deep·Z_deepᵀ·A_corᵀ)` and the front loss all read `hsQ` only through
`R` and the Gram `G := Z_deep Z_deepᵀ` (`M₂×M₂` PosDef). Can the `n`-column deep factor be ABSORBED — i.e.
is there a clean CoV / linear change (on `A_cor`, on `z₀`, and inside `frobSq`) that reduces the whole
`frontChargeIntegral < ⊤` to the LEAF case `n = M₂`, `Z_deep = I_{M₂}` (so `Q_b = A_cor`, `Q_p = z₀`),
up to bounded-unit Jacobian factors (powers of `det G`)? Or does `Z_deep` genuinely obstruct the reduction
(e.g. because `frobSq(M·Z_deep) ≠ frobSq(M)` — `Z_deep` is not orthonormal)? If it reduces, state the exact
CoV and the surviving `det G` powers. If not, say what breaks and how you'd handle the `n`-columns directly.

**Q2 (the CoV sequence).** Give the cleanest ORDERED sequence of changes of variables to land `< ⊤`, naming
for each step: the variable changed, whether it's a measure-preserving shear (Jacobian 1) or a genuine
`|det|`-Jacobian CoV, and which banked piece it uses. In particular: in what order do you integrate
`z / A_cor / x`? Where does the `A_cor = D·[I|X]` minor chart go (it's a CoV on `A_cor`), and where does the
front-block `H̃`-completion + polar (`chart4`) + the `W` big-cell (`chart5`) go? How do you avoid needing a
per-`(z,A_cor)` finite front loss (which is false)?

**Q3 (Tonelli order & the joint codimension).** The finiteness rests on `min_{ℓ,s} C_{ℓ,s}/2 = T1_q ≥ q`.
Concretely, after all CoVs, the integrand should be a monomial `∏ rᵢ^{Cᵢ − 1 − 2q}` on each cell, finite iff
`q < Cᵢ/2`. Which radial variables are the `rᵢ`? How does the `det D` (charge) exponent, the `W`-big-cell
`E`-block, and the `Y`-block (`Y=(P;C)`) rank stratum each contribute a factor to `C_{ℓ,s}`? I want the
map from "Lean radial CoV variables" to "the `C_{ℓ,s}` summands `u·b + M₀ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)`".

**Q4 (a shorter route to `< ⊤`?).** Since I only need `< ⊤` (not the exact ratio), is there a materially
SHORTER path than the full determinantal atlas — e.g. a cruder domination of `E_top + E_tr` from below by a
product of independent monomials whose radial integrals are each finite, avoiding the big-cell stratification?
Or is the stratification genuinely necessary (because the min-codimension is attained at an interior stratum,
not a corner)? If a crude lower bound exists, give it.

**Q5 (the finset atlas + null coverage in Lean).** The `(ℓ,s)`-strata cover the domain up to a null set. In
Lean, what is the cleanest way to (a) index the finite atlas (minor subsets of `A_cor`, of `W`, of `Y`), and
(b) prove the up-to-null coverage `μ(D \ ⋃ cells) = 0`? Is there a Mathlib pattern for "generic minor is
invertible ⟹ the union of non-vanishing-minor charts is co-null"?

Answer concisely and concretely; where you are uncertain, say so and give the safest Lean-robust option.
