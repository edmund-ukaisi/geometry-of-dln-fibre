**1. Principal Opens**
No. The principal-open facts make `dim G` and `dim Stab(M)` morally cheap, but they do not give the image-dimension bridge.

Also, as phrased, `dim(image) ≥ rank(differential at a point)` is the easy-side inequality; it follows from tangent inclusion at a smooth image point. The hard side needs:

```lean
dim closure(range μ_M) ≤ rank (dμ_M at 1)
```

or equivalently `dim image = generic differential rank` for this separable constant-rank orbit map.

Mathlib status:
- `KNOWN`: localization/principal-open algebra, `Localization.Away`, polynomial rings, Kähler/Jacobian infrastructure.
- `MISSING`: affine image dimension from differential rank.
- `MISSING`: fibre-dimension theorem.
- `MISSING`: quotient `G/Stab` scheme machinery.

Verdict for route 1: the “principal open of a linear space” lever is useful for stabilizer/source dimensions, but it is a red herring for the bridge.

**2. Noether Pullback**
This is not a real shortcut. You can identify

```lean
R ⧸ ker μ_M^* ≃ₐ[k] AlgHom.range μ_M^*
```

and then Noether-normalize the image ring. But to prove

```lean
ringKrullDim (AlgHom.range μ_M^*) ≤ finrank k (LinearMap.range δ⁰)
```

you must show that the Noether-normalization variables cannot have more algebraically independent directions than the rank of the Jacobian/differential of `μ_M`.

That is exactly the missing theorem:

```lean
trdeg Frac(image μ_M^*) ≤ generic_rank dμ_M
```

or equivalently a Jacobian criterion for transcendence degree.

Mathlib status:
- `KNOWN`: `Algebra.trdeg` exists as a `Cardinal`.
- `MISSING`: `ringKrullDim = trdeg` for finite-type domains.
- `MISSING`: `trdeg(image) ≤ rank Jacobian`.
- `MISSING`: finite-type image dimension via Noether normalization alone.

So route 2 hides the same submersion/image-dimension theorem.

**3. Minimal Bridge**
The cleanest minimal theorem is not full fibre dimension; it is an affine image-rank theorem for maps from principal opens:

```lean
theorem affine_image_dim_le_const_jacobianRank
    [Field k] [CharZero k]
    {m n r : ℕ}
    {s : MvPolynomial (Fin m) k} (hs : s ≠ 0)
    (F : Fin n → Localization.Away s)
    (hconst :
      genericJacobianRank F = r) :
    ringKrullDim
      (MvPolynomial (Fin n) k ⧸
        RingHom.ker (MvPolynomial.aeval F).toRingHom)
      ≤ (r : WithBot ℕ∞)
```

Then specialize:

```lean
theorem orbitPullback_dim_le_finrank_range_delta
    [Field k] [CharZero k]
    {d : Fin (N+1) → ℕ} (M : Tuple (k := k) d) :
    ringKrullDim
      (MvPolynomial (RepCoord d) k ⧸
        RingHom.ker (orbitPullback M).toRingHom)
      ≤
    (finrank k (LinearMap.range (deformationδ M M)) : WithBot ℕ∞)
```

Module counts:
- (a) Fibre-dimension specialized to `μ_M`: about **5 modules**. Hardest sublemma: affine finite-type fibre-dimension / generic fibre height formula.
- (b) Smooth quotient/local structure `G → O_M`: **7+ modules**. Hardest sublemma: represented quotient or algebraic local sections for the orbit map.
- (c) Differential image-rank bridge: **4 modules**. Hardest sublemma: Jacobian rank controls transcendence degree / Kähler differentials of the image function field.

Mathlib status:
- `KNOWN`: `AlgebraicGeometry.Group.Smooth.smooth_of_grpObj_of_isAlgClosed` exists but is group-object-specific.
- `MISSING`: reusable external-action orbit submersion theorem.
- `MISSING`: generic differential rank equals image dimension.

**4. Characteristic**
Your localization instinct is right for proof engineering: `CharZero` or separability enters only in the hard image/submersion bridge.

The easy direction is char-free: it is just `O_M ⊆ Z_M`, chain rule, and tangent inclusion.

The landed Jacobian stack is also char-free as stated over `[IsAlgClosed k]`: Nullstellensatz, Noether normalization, Krull dimension, cotangent/Jacobian comparison, and smooth-point regularity do not require `[CharZero k]`. The smooth-to-regular part needs perfectness; `[IsAlgClosed k]` supplies that.

For the hard direction:
- `CharZero` is a convenient sufficient hypothesis for separability of function fields.
- Mathematically, this specific action should not need char zero, because `Stab(M)=Aut(M)` is a smooth principal open in `End(M)`.
- Lean-wise, avoiding `[CharZero]` means proving the separability/smooth-stabilizer orbit-map bridge, which is more work.

Mathlib status:
- `KNOWN`: algebraically closed fields are perfect enough for the existing smooth/cotangent stack.
- `MISSING`: separability-aware image-rank theorem.
- `INFER`: smooth stabilizer should imply separability of this orbit map, but not available as Mathlib infrastructure.

**5. Bottom Line**
Not a 1-2 module build if you want the hard direction proved, not cited. The explicit linear structure of `G` and `Stab(M)` reduces stabilizer bookkeeping, but it does not collapse the missing image/fibre bridge.

Best path: port a focused affine image-rank theorem and specialize it to `orbitPullback`.

One-line verdict: **SUB-EXPEDITION-4-modules**.