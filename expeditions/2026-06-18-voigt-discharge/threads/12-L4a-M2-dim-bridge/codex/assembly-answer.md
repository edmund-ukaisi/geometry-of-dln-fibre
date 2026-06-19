**1. Step E**

I did not find a direct general lemma “finite-type map from Jacobson ring contracts maximals to maximals”. The cleanest Mathlib route is shorter than the explicit `B/p ↪ S/q` submodule fallback:

```lean
let B := MvPolynomial (Fin n) k
let h : B →+* S ⧸ q := (Ideal.Quotient.mk q).comp g.toRingHom
```

Then prove:

- `q.IsMaximal` first:
  `IsLocalization.isMaximal_of_isMaximal_disjoint` in `RingTheory/Jacobson/Ring.lean`.
  It needs `[IsJacobsonRing A]`, supplied by `isJacobsonRing_of_finiteType`, and `f ∉ m`.

- `h.FiniteType`:
  from `g.Etale` use
  `RingHom.Etale.iff_flat_and_formallyUnramified` then
  `RingHom.FiniteType.of_finitePresentation`, and compose with the quotient via
  `RingHom.FiniteType.comp_surjective`.

- Since `S ⧸ q` is a field (`letI := Ideal.Quotient.field q`) and `B` is Jacobson, Zariski:
  `finite_of_finite_type_of_isJacobsonRing B (S ⧸ q)` gives `Module.Finite B (S ⧸ q)`.
  Convert to `h.Finite` using `RingHom.finite_algebraMap`, then to integral via
  `RingHom.Finite.to_isIntegral`.

- Contract `⊥`:
  `isMaximal_comap_of_isIntegral_of_isMaximal' h h.IsIntegral ⊥`, with
  `haveI : (⊥ : Ideal (S ⧸ q)).IsMaximal := Ideal.bot_isMaximal`.

- Identify the contraction:
  `RingHom.comap_ker` plus `Ideal.mk_ker` gives
  `q.comap g.toRingHom = RingHom.ker h`.

This proves `p.IsMaximal`. It does not need algebraic closedness.

**2. Step B**

Yes: `IsLocalization.height_map_of_disjoint` plus two uses of
`IsLocalization.AtPrime.ringKrullDim_eq_height` is enough. No explicit local-localization iso is needed in your proof.

Disjointness is exactly:

```lean
(Ideal.disjoint_powers_iff_notMem f m.isPrime.isRadical).2 hf
```

for `hf : f ∉ m`.

**3. Step C**

Use the chart-local definition:

```lean
let n := Module.finrank S Ω[S⁄k]
```

Then, after `haveI : Algebra.IsStandardSmooth k S := ...`:

- freeness: `Algebra.IsStandardSmooth.free_kaehlerDifferential`;
- finiteness: `KaehlerDifferential.finite`, via `EssFiniteType.of_finiteType`;
- rank/finrank:
  `Module.finrank_eq_rank` gives
  ```lean
  Module.rank S Ω[S⁄k] = (n : Cardinal)
  ```
  by symmetry and `simpa [n]`.

Then install:
```lean
(Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth (R := k) (S := S) n).2 hrank
```

Watch `[Nontrivial S]`; derive it from `q.IsMaximal` if typeclass search stalls.

**4. Step D**

Use a local algebraization block:

```lean
algebraize [g.toRingHom]
haveI : Algebra.Etale B S := RingHom.etale_algebraMap.mp hg
```

After this, `algebraMap B S` is definitionally `g.toRingHom`, so:

```lean
q.under B = q.comap g.toRingHom
```

by `Ideal.under_def`/`rfl`.

Avoid having another competing `Algebra B S` instance in scope. Keep this in a small `letI`/`algebraize` section around M1.

**5. Rank-Ω Transport**

Not needed for M2’s headline. Defer unless M3 needs it.

For M3, the verified pieces are:

- `KaehlerDifferential.isLocalizedModule_map`;
- `Module.lift_rank_of_isLocalizedModule_of_free`;
- `Module.finrank_of_isLocalizedModule_of_free`.

This is the right route because Ω is free on the standard-smooth chart; it avoids the non-zero-divisor hypothesis in `IsLocalizedModule.lift_rank_eq`.

**6. Hidden Balloons**

The real kill-condition is the definition of `n`. If `n := Module.finrank A Ω[A⁄k]` globally, M2 is not true from smoothness at `m` alone in general. Use the chart/local definition, or prove a separate brick identifying the global `finrank` with the local Ω-rank under stronger hypotheses.

The rank transport to `Localization.AtPrime m` is also M3 work, not M2 work. The dimension equality can be finished without it.