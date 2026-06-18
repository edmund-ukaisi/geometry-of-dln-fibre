**VERDICT:** PREFERRED: `Ideal.height (MvPolynomial.vanishingIdeal k V) : ℕ∞`; single reason: Mathlib v4.29 has this affine vanishing-ideal/height API, but no ready Zariski topology on raw `Tuple d` / `Fin n → k`.

**Recommended Def**
```lean
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Height

noncomputable def affineClosedCodim
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type v} [Finite σ]
    (V : Set (σ → k)) : ℕ∞ :=
  (MvPolynomial.vanishingIdeal k V).height
```

For representations, avoid flattening to `Fin n` unless you need it. Use a finite coordinate index such as:
```lean
-- schematic: adapt local names/types
abbrev RepCoord (d : Fin (N + 1) → ℕ) :=
  Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)

noncomputable def codimRep
    {k : Type u} [Field k] [IsAlgClosed k]
    (coord : Tuple d ≃ (RepCoord d → k))
    (Z : Set (Tuple d)) : ℕ∞ :=
  affineClosedCodim (k := k) (σ := RepCoord d) (coord '' Z)
```

Then state Voigt as:
```lean
hVoigt :
  codimRep coord (orbitRankLocus M) =
    (orbitLinearCodim M : ℕ∞)
```

If you later need a `ℕ`, use a finite wrapper:
```lean
noncomputable def codimRepNat
    (hfin : codimRep coord Z ≠ ⊤) : ℕ :=
  (codimRep coord Z).toNat
```
Relevant exact names verified at v4.29: `MvPolynomial.vanishingIdeal`, `MvPolynomial.zeroLocus`, `Ideal.height`, `Ideal.primeHeight`, `Order.krullDim`, `topologicalKrullDim`, `ringKrullDim`, `ENat.toNat`, `ENat.coe_toNat`.

**Scaffolding Cost**
1. `RepCoord d`: 1 abbrev/def.
2. `coord : Tuple d ≃ (RepCoord d → k)`: 1 equivalence def, plus optional simp lemmas.
3. `affineClosedCodim`: 1 def.
4. `codimRep`: 1 def.

No topology instance, no scheme object, no proof of closedness, no ambient dimension theorem, no `finrank` theorem. If you insist on `Fin n`, add one finite-coordinate equivalence; otherwise `MvPolynomial σ k` works for any finite `σ`.

**Future Discharge**
Yes, this is the right target. Future work proves the determinantal/rank locus has the expected height. For closed sets given by equations, `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` exists, with `[IsAlgClosed K] [Finite σ]`, and connects zero-loci to radical ideals.

**v4.29 Traps**
- `topologicalKrullDim` returns `WithBot ℕ∞`; `Ideal.height` returns `ℕ∞`. Do not define codimension by subtraction now.
- There is `PrimeSpectrum.zariskiTopology`, but no ready `TopologicalSpace (Fin n → k)` Zariski instance.
- `MvPolynomial.vanishingIdeal` is point-set faithful as geometric codimension under the algebraically closed-field convention. Over arbitrary non-algebraically-closed fields, a raw `Set (k^n)` can lose scheme/ideal data, so use an explicit defining ideal instead:
```lean
noncomputable def affineIdealCodim
    {k : Type u} [Field k] {σ : Type v}
    (I : Ideal (MvPolynomial σ k)) : ℕ∞ :=
  I.height
```