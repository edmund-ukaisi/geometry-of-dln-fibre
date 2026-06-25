Your 3-step plan is the clean route. I would only tweak it by normalizing the localized monoid to `Submonoid.powers (C f : B)` early, because that makes disjointness and `height_map_of_disjoint` line up with less rewriting.

Let

```lean
Rτ := MvPolynomial τ k
B  := MvPolynomial σ Rτ
Sd := Localization.Away f
P  := MvPolynomial σ Sd
K0 := Ideal.span (Set.range fun b ↦ (MvPolynomial.X b : B))
K  := Ideal.span (Set.range fun b ↦ (MvPolynomial.X b : P))
```

**Plan validation:** yes.

1. `K = K0.map (algebraMap B P)`.
2. `(K0.map (algebraMap B P)).height = K0.height` by `IsLocalization.height_map_of_disjoint`.
3. `K0.height = Nat.card σ` by landed `height_coordIdeal_eq`.

**Q1: map of coordinate ideal**

Use:

- `Ideal.map_span` `(confident-exists-v4.29)`
- `Set.range_comp'` `(confident-exists-v4.29)`
- `MvPolynomial.algebraMap_def` `(confident-exists-v4.29)`
- `MvPolynomial.map_X` `(confident-exists-v4.29)`

Sketch:

```lean
local attribute [instance] MvPolynomial.algebraMvPolynomial

have hKmap : K0.map (algebraMap B P) = K := by
  rw [K0, K, Ideal.map_span]
  rw [← Set.range_comp' (algebraMap B P) (fun b : σ ↦ (MvPolynomial.X b : B))]
  congr
  funext b
  simp [MvPolynomial.algebraMap_def]
```

The defeq trap is real: `MvPolynomial.algebraMvPolynomial` is intentionally not a global instance. Install it locally, or use `letI : Algebra B P := MvPolynomial.algebraMvPolynomial`. Under that algebra structure, `algebraMap B P = MvPolynomial.map (algebraMap Rτ Sd)`, and `simp [MvPolynomial.algebraMap_def]` rewrites `X b ↦ X b`.

**Q2: disjointness**

Use:

- `Ideal.disjoint_powers_iff_notMem` `(confident-exists-v4.29)`
- `Ideal.IsPrime.isRadical` / `hprime.isRadical` `(confident-exists-v4.29)`
- `Submonoid.map_powers` `(confident-exists-v4.29)`
- landed `graphIdeal_isPrime` `(local)`
- landed `ker_aeval_eq_graphIdeal` `(local)`

Recommended chain:

```lean
have hK0prime : K0.IsPrime := by
  -- rewrite K0 to graphIdeal (fun _ ↦ 0), then:
  simpa [K0, DLNFibre.Core.graphIdeal] using
    (DLNFibre.Core.graphIdeal_isPrime
      (R := Rτ) (ι := σ) (fun _ : σ ↦ (0 : Rτ)))

have hCf_not : (MvPolynomial.C f : B) ∉ K0 := by
  intro hmem
  have hker :
      (MvPolynomial.C f : B) ∈
        RingHom.ker (MvPolynomial.aeval (R := Rτ) (fun _ : σ ↦ (0 : Rτ))).toRingHom := by
    -- rewrite K0 to graphIdeal 0, then use ker_aeval_eq_graphIdeal
    rwa [DLNFibre.Core.ker_aeval_eq_graphIdeal]
  exact hf (by simpa using RingHom.mem_ker.mp hker)

have hdisj :
    Disjoint (Submonoid.powers (MvPolynomial.C f : B) : Set B) (K0 : Set B) :=
  (Ideal.disjoint_powers_iff_notMem
    (I := K0) (MvPolynomial.C f) hK0prime.isRadical).2 hCf_not
```

Then either pass `powers (C f)` to `height_map_of_disjoint`, or rewrite the mapped monoid:

```lean
have hdisj_map :
    Disjoint (((Submonoid.powers f).map (MvPolynomial.C (σ := σ)) : Submonoid B) : Set B)
      (K0 : Set B) := by
  simpa [Submonoid.map_powers] using hdisj
```

**Q3: simpler route?**

No strictly simpler route in v4.29. A direct catenary proof over `Sd` would require localized catenary/dimension infrastructure and cancellation for `ringKrullDim Sd`; that is more infrastructure than transporting the already-landed field result through `IsLocalization.height_map_of_disjoint`.

**Q4: minimal instances**

Use these:

```lean
variable {k : Type u} [Field k]
variable {σ τ : Type u} [Finite σ] [Finite τ]
variable (f : MvPolynomial τ k) (hf : f ≠ 0)

local attribute [instance] MvPolynomial.algebraMvPolynomial
```

Then ensure the localization instance is the one height transport sees:

```lean
haveI :
    IsLocalization
      (Submonoid.powers (MvPolynomial.C f : B)) P := by
  simpa [Submonoid.map_powers] using
    (MvPolynomial.isLocalization
      (σ := σ) (M := Submonoid.powers f) (S := Sd))
```

Finally:

```lean
have hheight :
    (K0.map (algebraMap B P)).height = K0.height :=
  IsLocalization.height_map_of_disjoint
    (Submonoid.powers (MvPolynomial.C f : B)) K0 hdisj
```

Then close with `rw [← hKmap, hheight, height_coordIdeal_eq]` or the equivalent orientation.