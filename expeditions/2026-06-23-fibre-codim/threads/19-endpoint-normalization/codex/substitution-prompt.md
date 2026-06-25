# Lean 4 / Mathlib formalisation design review — endpoint-normalization AlgEquiv

I am formalising one rung of a larger affine-AG construction in Lean 4 (Mathlib v4.29). I want a
decorrelated design review of the construction below BEFORE I build it. Focus on: (1) is the
substitution direction correct so that the mult-transport comes out as stated, (2) the `N=1`
endpoint-coincidence pitfall, (3) the cleanest matrix-inverse API. Do NOT write full Lean; give me
the math + the API names + the traps.

## The objects (fixed conventions, already in the codebase)

- `d : Fin (N + 1) → ℕ` a dimension vector. `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`.
  Factor `i : Fin N` is an `(d (i+1)) × (d i)` matrix. So factor `0` (the FIRST factor, source side)
  is `(d 1) × (d 0)`; factor `N-1` (the LAST factor, target side) is `(d N) × (d (N-1))`.
- `mult d A = A_{N-1} · A_{N-2} · ... · A_1 · A_0 : Matrix (Fin (d (last N))) (Fin (d 0)) k`.
  (built by successive LEFT-multiplication: `multPrefix succ i = A i * multPrefix castSucc i`.)
- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)`. A coordinate is `⟨i, (row, col)⟩`:
  edge `i`, row in target dim, col in source dim.
- `multPoly d : Fin (d last) → Fin (d 0) → MvPolynomial (RepCoord d) R` — the generic product entries
  (= `mult d genericTuple` where `genericTuple i a b = X ⟨i,(a,b)⟩`).

## The pre-staged contract (must instantiate this exact shape)

```
example {R} [CommRing R] (d : Fin (N+1) → ℕ)
    (toSub fromSub : RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from : ∀ x, aeval toSub (fromSub x) = X x)
    (h_from_to : ∀ x, aeval fromSub (toSub x) = X x) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub) ... ...
```

## The construction I intend

Endpoint normalization: with invertible `H : Matrix (Fin (d 0)) (Fin (d 0)) R` (right factor on
source side) and `L : Matrix (Fin (d last)) (Fin (d last)) R` (left factor on target side), I
right-multiply the FIRST factor `A_0` by `H⁻¹` and left-multiply the LAST factor `A_{N-1}` by `L⁻¹`,
all middle factors fixed. Then `mult(Ã) = L⁻¹ · mult(A) · H⁻¹`.

I will parametrize by `[Invertible H]`, `[Invertible L]` and use `⅟H`, `⅟L` (avoid `nonsing_inv`,
works over any CommRing R, no field needed).

The single-edge substitution for "right-multiply edge `e` (an `m×n` block) by a matrix `U : Matrix
(Fin n) (Fin n) R`": the coordinate `X ⟨e,(i,j)⟩` maps to `∑_l U_{l,j} · X ⟨e,(i,l)⟩`. (Because
`(A·U)_{i,j} = ∑_l A_{i,l} U_{l,j}`.) Left-multiply edge `e` by `V : Matrix (Fin m) (Fin m) R`:
`X ⟨e,(i,j)⟩ ↦ ∑_l V_{i,l} · X ⟨e,(l,j)⟩`.

For the endpoint normalization, `toSub` (the substitution that, via `aeval`, computes the entries of
`Ã` as polynomials in `A`'s variables) should encode `Ã_0 = A_0 · H⁻¹` on edge 0 and
`Ã_{N-1} = L⁻¹ · A_{N-1}` on edge `N-1`, identity on all other edges.

QUESTIONS:
1. To get `aeval toSub (multPoly d r c) = (L⁻¹ · multPoly · H⁻¹) r c` (the transport for `Ã`), what
   EXACTLY should `toSub ⟨e,(i,j)⟩` be on edge 0 and on edge `N-1`? Give the direction precisely —
   should edge 0 carry `H⁻¹` or `H` in the substitution, given `aeval` does p ↦ p(toSub)? Walk
   through the N=1 sanity check (a single matrix M, `mult = M`, `Ã = L⁻¹ M H⁻¹`).
2. `N=1`: edge 0 IS edge N-1 (`Fin 1`, only index 0). Both substitutions apply to the same edge.
   The correct combined substitution must be `Ã = L⁻¹ · A_0 · H⁻¹` simultaneously. What is the
   single substitution `X ⟨0,(i,j)⟩ ↦ ∑_{l,m} (L⁻¹)_{i,l} (H⁻¹)_{m,j} X ⟨0,(l,m)⟩`? Confirm the
   round-trip (`toSub`/`fromSub` mutually inverse) still holds in the coincident case and that
   composing the two single-sided subs in either order gives this (does order matter for the FINAL
   answer, vs intermediate)?
3. The round-trip `fromSub`: should be the same construction with `H`, `L` in place of `H⁻¹`, `L⁻¹`.
   The collapse `aeval toSub (fromSub (X⟨e,(i,j)⟩)) = X⟨e,(i,j)⟩` reduces to a matrix identity
   `∑ (H⁻¹)(H) = δ` i.e. `H⁻¹ H = 1`. Over `MvPolynomial`, is the cleanest route to prove this on
   generators: expand `aeval` of the sum, swap to `Finset.sum`, recognize `∑_l (⅟U)_{?,l} U_{l,?}`
   as `(⅟U * U)_{?,?} = 1_{?,?}` via `Matrix.mul_apply` + `invOf_mul_self`, then `Matrix.one_apply`?
   Any pitfall with the double sum in the N=1 coincident case (Fubini / `Finset.sum_comm`)?
4. Is there a SIMPLER overall structuring: define ONE general single-edge "linear substitution by an
   endomorphism on edge e" `AlgHom`, prove the composition law `(sub by U) ∘ (sub by V) = sub by
   (U*V)` ONCE, and get round-trip + N=1 coincidence as corollaries? Or is per-direction `aeval`
   with explicit double-sum proofs less painful in practice? I lean toward the composition-law
   approach to avoid duplicating the inverse-collapse proof. Critique.
5. Any reason the mult-transport `aeval toSub (multPoly d r c) = (⅟L · M · ⅟H) r c` (with M the
   generic-product matrix `Matrix.of (multPoly d)`) would NOT factor through `aeval`-commutes-with-
   matrix-product + the entrywise substitution on the endpoint factors? The middle factors are fixed
   by `toSub` (identity substitution) — does `aeval id_on_middle (multPrefix ...) = multPrefix` need
   an induction, or does it fall out because `toSub` is identity on those edges' variables?

Give me the cleanest construction + the precise substitution formulas + the API names
(`Matrix.mul_apply`, `invOf_mul_self`, `Finset.sum`, `aeval`, `MvPolynomial.algHom_ext`,
`map_sum`, `aeval_X`, ...) and flag every trap.
