# Codex consult — rung 2: the REGULAR-section gap in the single-chart trivialization (Lean v4.29)

Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
varietyDim F = δ + varietyDim F`.

## The gap I hit

The LANDED `exists_baseChange_of_rank_eq` is EXISTENTIAL: for each rank-r target `B` it gives SOME
`P ∈ H = GL_{d_N}×GL_{d_0}` with `P_N·E·P_0⁻¹ = B` (E = the standard rank-r `diag(I_r,0)`). The sweep
`Σ^r = ⋃_P (P•·)''F` is then a set-union. But a per-point existential `P` does NOT give a REGULAR
map `U_P → H` (a section), and Codex's own prior warning was: a bare set bijection does not preserve
`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
pivot chart.

## The structures available

- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
- `H` acts, `mult` is `H`-equivariant (`mult_smul`), `F = mult⁻¹(E)`.
- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).

## My questions

1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
   normalizing section `σ : U_P → H` with `σ(B)_N · E · σ(B)_0⁻¹ = B` for all `B ∈ U_P`?** For a
   rank-r matrix with invertible top-left r×r block, row/column reduction to `diag(I_r,0)` uses only
   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
   YES, a regular section EXISTS on each pivot chart (this is the standard "Bruhat/pivot cell is an
   affine cell with a regular trivialization" fact). Confirm, and tell me the cleanest Lean-shape:
   build `σ` as an explicit `H`-valued regular map via the block inverse, OR is there a slicker route?

2. **Given a regular section `σ`, is the chart iso `Φ : mult⁻¹(U_P) ∩ Σ^r → U_P × F`, `A ↦ (mult A,
   σ(mult A)⁻¹ • A)` a regular iso?** Inverse `(B, A') ↦ σ(B) • A'`. Both directions are regular
   (compositions of `mult`, the regular `σ`, and the `H`-action which is regular). So this should be
   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
   need `mult A ∈ U_P` exactly, and is the codomain `U_P × F` or `U_P × (chart∩F)`)?

3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
   `ringKrullDim`-of-coordinate-ring; a regular iso of affine varieties induces a `k`-algebra iso of
   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
   defined on SUBSETS of a FIXED affine space `RepCoord d → k` via `vanishingIdeal` in THAT ambient
   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
   (`mult⁻¹(U)∩Σ^r ⊆ RepCoord d` vs `U_P × F ⊆ (base coords) × (RepCoord d)`) needs the coordinate-
   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
   the coordinate-ring `ringKrullDim` and prove a `ringEquiv`-transport lemma, or (b) stay in one
   ambient space (realize `U_P × F` as a subset of `RepCoord d` too)? Which is less Lean friction?

4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
   δ + dim F` that does NOT build the explicit chart trivialization — e.g. (a) the action map `α : H
   × F → Σ^r` regular + surjective, `dim Σ^r = dim(H×F) − dim(generic α-fibre)`, with the generic
   α-fibre = the stabilizer (`dim H − δ`)? That reintroduces a fibre-dim count for `α` but over a
   GROUP (homogeneous, so the generic fibre dim might be computable as a stabilizer dim). Is that
   cheaper than the pivot-chart trivialization, or does it hit the same product-dimension wall?

Give me: confirm the regular section exists on a pivot chart (and the cleanest Lean construction),
the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
iso.
