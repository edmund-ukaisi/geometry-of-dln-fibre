# Thread 26 → Thread 27 — the exact Lean interface the H4 capstone consumes

The H4 assembly (`Core.FibreDimHeadlineProbe`) closes `codimRepCanonical (fibre d B) = C+δ` from
**per-minimal-prime height bounds**. Thread 27 produces the Jacobian-rank facts; this records the
precise shape the assembly needs and the conversion in between, so thread 27 targets exactly what
lands.

## What the capstone consumes (LANDED, green)

`codimRepCanonical_fibre_eq_of_minimalPrimes_height_bounds [IsAlgClosed k] (d) (B) (v)`
- `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height`
- `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v`
- ⟹ `codimRepCanonical (fibre d B) = v`.

And the **G1-transported** version (`…_of_rank_of_height_bounds_at_witness`, `[Infinite k]`, `hN`):
the bounds at ONE rank-`r` witness `B*` give `codim(fibre B) = v` for **every** rank-`r` `B`. So thread
27 may pick the most tractable `B*`.

Set `v = C + δ = (cCodim d r).toNat + r(d_0 + d_N − r)` (as `ℕ∞`).

## The conversion thread 27 must bridge (Jacobian-rank → `J.height`)

For a minimal prime `J` of `fibreGenIdeal d B` (an irreducible component of the fibre), with `R =
MvPolynomial (RepCoord d) k`:

1. **catenary (LANDED, `NullstellensatzCodim.height_add_ringKrullDim_quotient_eq_card`):**
   `(J.height : WithBot ℕ∞) + ringKrullDim (R ⧸ J) = card`. So `J.height = card − dim(R ⧸ J)`.
2. **generic smoothness (engine substrate, `SmoothPointRegular` / `SmoothLocalRelativeDimension.
   ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` + `FibreJacobian` H3a):** at a generic smooth
   point `A` of the component `V(J)`, `dim(R ⧸ J) = dim_A(component) = finrank (ker (fibreJacobian d B
   A)) = card − rank(fibreJacobianMatrix d B A)` (H3a `finrank_ker_add_rank_fibreJacobianMatrix`).
3. So `J.height = rank(fibreJacobianMatrix d B A)` at a generic smooth `A ∈ V(J)`.

Hence:
- `hge` (`v ≤ J.height`) ⟸ **`rank(fibreJacobianMatrix d B A) ≥ C+δ` at a generic point of every
  component** — thread 27's headline.
- `hle` (`∃ J, J.height ≤ v`) ⟸ **`rank ≤ C+δ` at a generic point of ONE (top) component** — the H3
  cert's `rank = C+δ` at the top component gives this directly (`≤`).

## The independence caveat (flagged to the controller)

The structural lower bound `rank(d mult_A) ≥ δ` (image ⊇ the δ-dim GL×GL-orbit tangent of `E`) is
clean and correct, but combining it with `≥ C` gives only `≥ max(C, δ)`, **not** `≥ C+δ`. The sum needs
the orbit/stratum directions and the Σ̄^r-transverse directions to be **linearly independent** in the
image of `d(mult)`. That independence is the real content of `= C+δ` (numerically tight: `(2,2,2) r=1`
has `C+δ = 4 = d_N·d_0`, a full submersion onto the target). The clean structural target is therefore:

> `Im(d mult_A) ⊇ T_E(rank-r stratum) ⊕ (a C-dim complement)`, the two summands independent,

i.e. `rank(d mult_A) = δ + (the codim of Σ̄^r seen transversally) = δ + C` at a generic top-component
point. Thread 27 owns this.

## Generic-smoothness sub-point (step 2) — the one place to be careful

`dim(R ⧸ J) = card − rank(Jacobian)` at a generic point needs the point to be a **smooth** point of the
component `V(J)` (char-0 generic smoothness). The engine has the smooth-point ⟹ regular-local-ring +
local-dim = relative-dim machinery (`SmoothPointRegular.smooth_point_isRegularLocalRing`,
`SmoothLocalRelativeDimension.ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`), all flatness-free
(étale/regular route). Identifying a smooth point + that its Jacobian rank is the component codim is the
remaining glue — thread 27's certificate should state which generic point per component and that the
Jacobian rank there equals the component codim.
