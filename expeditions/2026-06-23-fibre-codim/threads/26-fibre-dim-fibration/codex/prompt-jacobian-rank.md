# Codex consult — the uniform Jacobian-rank lower bound `rank(d mult_A) ≥ C + δ` (structural)

## Setup (deep linear networks, char-0 alg-closed field k)

`Rep_d` = tuples of matrices `A = (A_1, …, A_N)`, `A_i : Mat_{d_{i+1} × d_i}(k)`. The multiplication
map `mult(A) = A_N ⋯ A_1 : Mat_{d_N × d_0}`. Fix a target `E = diag(I_r, 0)` of rank `r ≤ min_i d_i`.
The fibre `F = mult⁻¹(E)`.

Two integers:
- `δ = r(d_0 + d_N − r) = dim` of the rank-`≤ r` determinantal locus in the TARGET `Mat_{d_N×d_0}`
  (= `dim` of the GL_{d_N}×GL_{d_0}-orbit of `E`, the rank-exactly-`r` stratum).
- `C = cCodim d r` = the quiver/Kostant codimension of `Σ̄^r = {A : rank(mult A) ≤ r}` in `Rep_d`
  (the type-A `Ext` codimension; LANDED in the engine).

**Certified (pen-and-paper, thread 25, sympy on 13 cases):** at a generic point `A*` of a
**top-dimensional** component of `F`, the Jacobian `d(mult)_{A*}` has rank **exactly** `C + δ`. Examples:
`(2,2,2) r=1`: `C=1, δ=3, rank=4 = d_N·d_0` (full submersion onto target). `(2,2,3) r=1`: `rank=5 <
d_N·d_0=6` (NOT full — so the independence below is genuine).

## The differential (engine, LANDED)

`d(mult)_A` is linear `T_A Rep_d = ∏_i Mat_{d_{i+1}×d_i} → Mat_{d_N×d_0}`, product rule:
`d(mult)_A(Ẋ) = Σ_i (A_N ⋯ A_{i+1}) · Ẋ_i · (A_{i-1} ⋯ A_1)` (the `(r,c)`-entry is
`multSuffix_{i+1} · multPrefix_{i-1}`, engine `fibreJacobianMatrix_apply`).

## The TARGET to formalise in Lean 4 / Mathlib v4.29

The **uniform** lower bound:

> `rank(d(mult)_A) ≥ C + δ` for **every** `A ∈ F` (or at least at a generic point of every irreducible
> component of `F`).

Combined with generic smoothness (`dim(component) = card − rank(d mult)` at a smooth point) and the
per-component minimum, this gives `codim(F) ≥ C + δ` (the hard direction; the `≤` is separate).

## The STRUCTURAL route the controller proposes (vet it)

1. **`rank ≥ δ` via the endpoint group action.** The GL_{d_N}×GL_{d_0} action on the END factors
   (`A_N ↦ P A_N`, `A_1 ↦ A_1 Q⁻¹`) gives `mult((P,Q)·A) = P · mult(A) · Q⁻¹`. At `A ∈ F`
   (`mult A = E`), the orbit curve `t ↦ (P(t),Q(t))·A` has `mult = P(t)·E·Q(t)⁻¹`; differentiating at
   `id` sweeps `{p·E − E·q : p ∈ gl_{d_N}, q ∈ gl_{d_0}}` = `T_E(rank-r locus)`, dimension `δ`. The
   end-factor variations `Ẋ_N = p·A_N`, `Ẋ_1 = −A_1·q` realise these in `image(d mult_A)`. So
   `image(d mult_A) ⊇ T_E(rank-r locus)`, giving `rank ≥ δ`. **Is this airtight for EVERY `A ∈ F`?**
   (Subtlety: does `{p·A_N : p} = ` enough? `A_N` may not be surjective if `d_N > rank`. Does the
   image of the end-factor variations actually equal `T_E(rank-r locus)` = `{p E − E q}`, or only a
   subspace? Check: the end-factor image is `{(A_N⋯A_2)·Ẋ_1 + Ẋ_N·(A_{N-1}⋯A_1)}`… careful with which
   factors. Is the δ bound uniform or only generic?)

2. **The extra `+C`.** The `+C` should come from the MIDDLE-factor variations (`Ẋ_i`, `1 < i < N`) /
   the deformation-complex `Ext` structure of `Σ̄^r`. **What is the clean structural source of `+C`,
   and crucially: why is the `C`-dim contribution LINEARLY INDEPENDENT (in `image(d mult_A) ⊆
   Mat_{d_N×d_0}`) from the `δ`-dim end-factor contribution?** Separately `rank ≥ δ` and `rank ≥ C`
   give only `rank ≥ max(C,δ)`; the SUM `≥ C+δ` needs the independence. Is there a clean splitting of
   the target tangent `Mat_{d_N×d_0} = (end directions, dim δ) ⊕ (middle directions, dim C) ⊕ rest`?

## QUESTIONS (be concrete + skeptical)

1. Is the structural `rank ≥ δ` (step 1) airtight UNIFORMLY (every `A ∈ F`), or only generically? Give
   the precise linear-algebra statement (which variations, why they span `T_E(rank-r locus)`).
2. Is there a clean structural source + independence proof for the `+C` (step 2)? Or is the `+C`
   genuinely per-component / dimension-dependent (so the uniform structural bound fails and one must go
   per-component via Kostant)? The H3 cert says lower-dim components carry HIGHER rank — consistent with
   `rank ≥ C+δ` UNIFORMLY, but is it PROVABLE uniformly or only `≥ C+δ` at generic points?
3. If uniform `rank ≥ C+δ` is NOT cleanly provable, what is the cleanest PER-COMPONENT route: at a
   generic point of a component with Kostant profile `m`, `rank(d mult) = ` (codim of that component) =
   `C_m ≥ C`? Is `rank ≥ C_m + δ`? How does `δ` interact with the per-component codim `C_m`?
4. For the LEAN realisation: is the cleanest target (a) the uniform bound `rank(fibreJacobianMatrix d E
   A) ≥ C+δ` for all `A ∈ F` (then no genericity/smoothness needed for the `≥` — just `dim ≤ card −
   rank`), or (b) the per-generic-point bound + generic smoothness? Which avoids identifying smooth
   points? Note: in the engine, `finrank(ker) + rank = card` is LANDED (H3a), and `dim(component) ≤
   finrank(ker at any point)` is NOT generally true (only at smooth points) — but `dim(component) =
   card − rank` at a smooth point. Is there a way to get `dim(F) ≤ card − (C+δ)` from a UNIFORM rank
   lower bound WITHOUT smoothness (e.g. via upper-semicontinuity: `dim F ≤ dim T_A F = card − rank` at
   ANY point only bounds BELOW; the tangent dim is ≥ the local dim, giving `card − rank ≥ dim`, i.e.
   `rank ≤ card − dim` — the WRONG direction)? Clarify which direction a uniform rank bound gives and
   whether smoothness is escapable.

Give: (a) verdict on the structural `rank ≥ δ` uniformity; (b) the `+C` independence — clean source or
genuinely per-component; (c) the cleanest Lean target shape (uniform vs per-component, smoothness
needed or not) and which direction (`≥`/`≤`) a uniform Jacobian-rank bound actually delivers for the
fibre dimension. Flag any step that needs smoothness/genericity vs holds at every point.
