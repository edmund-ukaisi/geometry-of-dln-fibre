**Q1**

Yes: the cleanest Lean object is an image-union definition, with an extensional membership lemma as the public API.

Lean-shaped definition:

```lean
-- L = 2
def k0 : Fin 2 := ⟨0, by decide⟩
def kLeaf : Fin 2 := ⟨1, by decide⟩

-- E is the outermost Sum.inr in (((K ⊕ X) ⊕ N) ⊕ E).
def boundaryESlot (e : Fin (r * c)) : ChartIdx :=
  ⟨k0, Sum.inl ((frameSplitEquiv k0).symm (Sum.inr e))⟩

-- If leaf schurDim is not definitionally Text_L * Wext_L, insert the relevant equivalence here.
def leafSlot (a : Fin (Text 2 * Wext 2)) : ChartIdx :=
  ⟨kLeaf, Sum.inl a⟩

def active : Finset (Fin N) :=
  {structPivot} ∪
    (Finset.univ.image fun e : Fin (r * c) =>
      chartIdxEquiv.symm (boundaryESlot e)) ∪
    ((Finset.univ.erase leafAnchor).image fun a : Fin (Text 2 * Wext 2) =>
      chartIdxEquiv.symm (leafSlot a))
```

Equivalent membership predicate:

```lean
i ∈ active ↔
  i = structPivot ∨
  (∃ e : Fin (r * c),
    chartIdxEquiv i = boundaryESlot e) ∨
  (∃ a : Fin (Text 2 * Wext 2),
    a ≠ leafAnchor ∧ chartIdxEquiv i = leafSlot a)
```

Subtleties to pin in Lean:

- If `frameSplitEquiv k0` is oriented from role-sum to `Fin (schurDim k0)`, remove `.symm`.
- The E-role is specifically `Sum.inr e` in `(((K ⊕ X) ⊕ N) ⊕ E)`.
- `leafAnchor : Fin (Text 2 * Wext 2)` must be fixed once and excluded from the leaf image.
- You need a proof that `structPivot` is not an E-role slot and not a leaf slot. Usually this follows because it is a K/core slot at `k0`.

**Q2**

Proof-level part:

For the correct set above, the cardinal proof is structural:

```lean
#active
= 1 + #(Fin (r * c)) + (#(Fin (Text 2 * Wext 2)) - 1)
= 1 + r * c + (Text 2 * Wext 2 - 1)
= r * c + Text 2 * Wext 2
= minAdm
```

The disjointness comes from:

- `chartIdxEquiv` is injective,
- boundary `k0` and leaf `kLeaf` are different,
- inside boundary `k0`, the E-role is disjoint from the K/core pivot role,
- `erase leafAnchor` removes exactly one leaf coordinate.

Determinant logic:

```text
D(phi) = D(B ∘ pivotBlowupOn active p)
       = DB(pivotBlowupOn active p) · D(pivotBlowupOn active p)
```

For `p = structPivot ∈ active`, with `u = x_p`,

```text
det D(pivotBlowupOn active p) = u^(#active - 1)
```

so for the correct active set:

```text
det Dphi = det(DB) · u^(minAdm - 1).
```

The nonzero determinant is therefore not from cardinality alone. It needs both:

1. `#active = minAdm`, the budget/squareness pin;
2. `det(DB) ≠ 0` generically, meaning the de-radialized map `B` is a square local isomorphism.

The mis-allocation case is important: if you anchor/fix a K-core coordinate instead of excluding one leaf coordinate, the count can still look square, but the structure is wrong. The leaf residual block keeps one radial/projective redundancy, while an independent K/core degree of freedom has been removed. Thus `DB` loses rank: one infinitesimal direction is redundant/dependent and `B` is no longer a local iso. So the determinant vanishes because `det(DB) ≡ 0`, not because the blowup Jacobian monomial vanishes.

So the precise statement is:

```text
Correct structural active set + #active = minAdm + generic det(DB) ≠ 0
  ⇒ det Dphi = ± u^(minAdm - 1) generically nonzero.

Same cardinality but wrong allocation
  ⇒ DB singular ⇒ det Dphi ≡ 0.
```

Cardinality is necessary for the budget, but not sufficient for non-degeneracy.

**Q3**

Confirmed, with the anchor caveat.

`pivotBlowupOn active p` supplies exactly the radial scaling on active coordinates:

```text
x_p ↦ x_p
x_i ↦ x_p * x_i     for i ∈ active, i ≠ p
x_j ↦ x_j           for j ∉ active
```

Thus the E-role coordinates and the non-anchor leaf residual coordinates become `u · E` and `u · Rfin_free`.

For the excluded leaf anchor, the usual affine reading is:

```text
Rfin = (anchor = 1, free leaf coordinates)
u · Rfin = (u, u · free leaf coordinates)
```

The anchor component gets its `u` from the pivot itself, not from being an active coordinate. So yes: this is the faithful reading of `phiGen_smul_radial`, provided the leaf anchor is interpreted as the fixed affine coordinate.