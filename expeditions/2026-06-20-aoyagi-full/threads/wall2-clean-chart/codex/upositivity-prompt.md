<task>
Lean 4 + Mathlib v4.29. I have proved the RATE leg of a "clean achiever chart": `routeMCore M (cleanPhi u)
= (u p)^2 * U(u)` where `U(u) := dlnLoss M 0 (unblownParams u)`, with:

- `dlnLoss M 0 A := ∑ i ∑ j (prod M A i j)^2` (squared Frobenius of the matrix product A^(0)·...·A^(L-1)).
- `prod M A : Matrix (Fin (M 0)) (Fin (M last)) ℝ` — the left-folded matrix product over `Params M :=
  ∀ s : Fin L, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ`.
- `unblownParams M hL hne u := (paramsEquivFlat M).symm (unblownFlat M hL hne u)` where
  `unblownFlat u c := if c = deepestPivot then 1 else u c` (a `Fin N → ℝ`, N = routeMAmbient M = flatDim M).
- DECODE (PROVED): `((paramsEquivFlat M).symm x) q.1.1 q.1.2 q.2 = x (flatCoordOf M q)` for `q : FlatIdx M`
  (per-coordinate, generic). And `flatCoordOf M q ∈ deepestCoords M hL ↔ q.1.1 = deepLayer M hL` (PROVED).

I need to fill the `NodeAchieverChart M` field `Ubound`: for every δ, ∃ B>0 with U ≤ B on the box [0,δ]^N
AND U > 0 a.e. on that box. The hard part is U > 0 a.e.

## Banked machinery I can reuse

1. `MvPolynomial.ae_eval_ne_zero (p : MvPolynomial (Fin N) ℝ) (hp : p ≠ 0) : ∀ᵐ x, eval x p ≠ 0`
   (banked, the zero set of a nonzero MvPolynomial is Lebesgue-null). This is the ONLY route to "U>0 a.e."
   that I have — it requires writing `U(u) = eval u (UPolyClean)` for an explicit NONZERO MvPolynomial.

2. The validate-small instance (M=(4,4,2,2), concrete) did exactly this: defined `UPoly4422 : MvPolynomial
   (Fin 28) ℝ` as the EXPLICIT sum-of-squares of the product with `X k` for coords and `C 1` for the pivot
   slot; proved `eval u UPoly4422 = Uval4422 u` by `simp [map_sum, map_pow, map_mul]` + entrywise matrix
   accessor matching (`fin_cases`); proved `UPoly4422 ≠ 0` by evaluating at an explicit witness point giving 2.

3. The INTERIOR tide built generic naturality: a `chainOfMt_map`, `genBlkFlatStruct_genBlkMap` etc., showing
   the polynomial chain maps under `eval x` to the ℝ chain (because each block reader returns a single coord
   `eval x (X j) = x j`, and the block constructors commute with `Matrix.map`). It then defined `UPolyGen :=
   sqSumHmat0 (polynomial chain)` and proved `eval x UPolyGen = achieverUfun x`. But that's for a DIFFERENT
   (Schur-frame) chart, tied to `genBlkFlatStruct`/`VvalGen` — NOT my clean `dlnLoss ∘ unblownParams`.

4. NO `prod_map` / `prodAux_map` / `dlnLoss`-over-MvPolynomial naturality lemma exists yet.

## The two candidate routes for ∀M (rank + pick)

ROUTE 1 ("polynomial Params + prod naturality"): Define `unblownFlatPoly : Fin N → MvPolynomial (Fin N) ℝ`,
`c ↦ if c = p then C 1 else X c`. Define `unblownParamsPoly := (paramsEquivFlatPoly).symm (unblownFlatPoly)`
— but `paramsEquivFlat` is over ℝ; I'd need a polynomial flattening, OR I observe the decode is per-coord so
I can define the polynomial Params tuple directly via the same FlatIdx decode. Then build `UPolyClean :=
∑ i ∑ j (prodPoly M unblownParamsPoly i j)^2` where `prodPoly` is `prod` over `MvPolynomial`. PROVE `eval u
UPolyClean = U(u)` via a `prod`/`prodAux` `Matrix.map`-naturality lemma `(prod M A).map f = prod M (A.map f)`
(matrix product commutes with ring hom `map`). Is `Matrix.map_mul` + a `prodAux` induction the clean way to
get `prodAux_map`? Then `eval u (prodPoly ... i j) = prod (ℝ unblownParams) ... i j` because each
`unblownParamsPoly s i j = eval-preimage of unblownParams s i j` (decode: poly slot = `unblownFlatPoly
(flatCoordOf q)`, eval gives `unblownFlat u (flatCoordOf q)`). Then UPolyClean ≠ 0 by a witness point.

ROUTE 2 ("U ≥ a single squared coordinate" — the (3,3,4) trick): is there ANY clean lower bound `U ≥ (u c)^2`
or `U ≥ const > 0` that avoids the polynomial entirely? For clean M the deepest factor A^(L-1) is the full
rank-carrying block; with the pivot slot = 1, maybe one product entry is a single coordinate. But the
product entries are bilinear/multilinear across L layers, so I doubt a single-coordinate bound exists for
L ≥ 3. (The validate-small explicitly says NO clean single-coord bound exists for (4,4,2,2).)

## Specific questions

1. Confirm ROUTE 1 is the way (or propose better). Give the cleanest `prodAux_map` statement + proof
   skeleton: `(prodAux H A k hk).map f = prodAux H (fun s => (A s).map f) k hk` for a RingHom
   `f : ℝ →+* S` (here `f` will be... wait, I need the OPPOSITE direction: I have a polynomial tuple `Apoly`
   and want `eval u (prodPoly Apoly i j) = prod (eval-mapped Apoly) i j`, i.e. `(prodAux Apoly k).map (eval u)
   = prodAux (Apoly.map (eval u)) k`). The matrix-map-through-product lemma. Does `Matrix.map_mul` hold for a
   general RingHom in v4.29 (`(A*B).map f = A.map f * B.map f`)? Flag the prodAux dependent-Fin-cast issue:
   `prodAux` has an internal `Eq.mpr`/`rw [e1,e2]` cast at the succ step (the layer is reindexed). Will
   `Matrix.map` commute through that cast cleanly, or do I need `prodAux_succ`/`prodAux_step` (HEq form)?

2. For the polynomial Params tuple: rather than a polynomial flattening, can I define `unblownParamsPoly :
   Params-over-MvPolynomial` DIRECTLY by `fun s i j => unblownFlatPoly (flatCoordOf M ⟨⟨s,i⟩,j⟩)` and prove
   `(unblownParamsPoly s).map (eval u) = unblownParams M hL hne u s` entrywise from the decode + `eval (if
   c=p then C 1 else X c) = if c=p then 1 else u c`? This sidesteps building a polynomial `paramsEquivFlat`.
   Is `Params (over a CommRing S) := ∀ s, Matrix _ _ S` available, or is Params hardcoded to ℝ? (It is
   hardcoded to ℝ in this repo.) If hardcoded, do I just use a bare `∀ s, Matrix _ _ (MvPolynomial ...)` and
   a bespoke `prodPoly`, never touching `Params`?

3. The witness `UPolyClean ≠ 0`: for clean M (deepest factor full row rank, `minAdm = m1·M_L`), what is the
   robust witness point? Candidate: set all free coords so that A^(0),...,A^(L-2) are "identity-like"
   (rectangular identity `[I|0]` or `[I;0]`) and A^(L-1) = the pivot-stripped deepest with M̄(0,0)=1, rest 0,
   giving prod = a rectangular-identity-ish matrix with a 1 in position (0,0), so U = ∑∑(prod)² ≥ 1 > 0. But
   proving prod = that explicit matrix at the witness, ∀M, through the opaque decode, seems as hard as the
   rate. Is there a SLICKER nonvanishing argument: e.g. "U as a polynomial is not identically zero because
   `prod` at SOME point is nonzero, and I can exhibit that point abstractly via `prod (1-ish tuple) ≠ 0`"?
   Specifically: is there a Mathlib/repo fact that the product of rectangular identities is nonzero, or that
   `dlnLoss M 0 A > 0` for SOME explicit A? Or: can I argue `UPolyClean ≠ 0` by showing its evaluation at the
   tuple `A* := (paramsEquivFlat).symm (unblownFlat u*)` for a specific u* is positive, REUSING the rate
   identity backwards (routeMCore at a point where the loss is known nonzero)?

</task>

<output_contract>
Answer Q1, Q2, Q3 in order. For Q1 give the exact `prodAux_map` lemma statement + whether `Matrix.map_mul`
exists in v4.29 (flag "verify") + how to handle the prodAux cast (prodAux_step HEq route vs direct). For Q2
give yes/no + the one-line construction. For Q3, give the SINGLE most robust witness strategy for ∀M clean M
(the one least likely to require re-deriving the product through the opaque decode) — be concrete about what
point and why U>0 there. End with a 3-bullet build order for the U-positivity field.
</output_contract>

<grounding_rules>
No repo access. Treat the definitions as ground truth. Flag any Mathlib lemma name you are unsure exists at
v4.29 as "verify exists". Distinguish "standard idiom" from "should work". Do not invent repo lemma names
beyond those listed.
</grounding_rules>
