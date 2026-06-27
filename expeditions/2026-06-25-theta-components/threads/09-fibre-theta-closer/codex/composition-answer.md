**1. Chain Composes?**

Yes, modulo three explicit orientation/endpoint notes.

Use final `d : Fin (N+2) → ℕ`; instantiate E0 with `(N := N+1) (d := d)`. Then:

```lean
closed Σ≤r
  = exact sweepSigmaRing        -- W0
  = Away chartDsig              -- W1.symm if going source → chart
  = Away chartGfib              -- ChartE
  = MvPolynomial SchurVar O(F)  -- W2
  = O(F)                        -- Poly
  = O(fibre)                    -- W3.symm after vanishingIdeal = radical fibreGenIdeal
```

The W2 endpoint matches Poly: W2 with
`A := MvPolynomial (SchurVar ...) (sweepFibreRing k d r hp hq)` gives RHS exactly the Poly LHS.

ChartE’s codomain is also exactly `Localization.Away (chartGfib k d r hp hq)`, and `chartGfib` has type
`MvPolynomial (SchurVar ...) (sweepFibreRing ...)`. So W2’s `A` is the chart-e codomain base ring. The risk is elaboration/instance path, not a mathematical ring mismatch.

Rungs needing rewrites/extra identities:

- **W0** is the real missing identity: closed `sigmaIdeal` quotient vs exact `sweepSigmaRing`.
- **W3** needs the concrete rewrite
  `vanishingIdeal k (sweepFibre k d r hp hq) = (fibreGenIdeal d E).radical`.
- **FibreUnit** should not be appended if the headline endpoint is `R ⧸ fibreGenIdeal`. It gives the sibling localized endpoint
  `O(fibre) = O(fibre)[1/Δ]`; use it only if the theorem’s LHS is the localized fibre ring.

**2. W0 Route**

Use **set equality of `quotTopDimSet`**, not a direct `BijOn`. The quotient-side bijection is already abstracted by `ncard_topDimMinPrimes_quotient_eq`; a direct `BijOn` would duplicate quotient/comap bookkeeping.

Prove a small generic lemma:

```lean
quotTopDimSet_eq_of_same_top_minimalPrimes
  (hheight : I.height = J.height)
  (hIJ : ∀ q, q ∈ I.minimalPrimes → q.height = I.height → q ∈ J.minimalPrimes)
  (hJI : ∀ q, q ∈ J.minimalPrimes → q.height = J.height → q ∈ I.minimalPrimes) :
  quotTopDimSet I = quotTopDimSet J
```

Then W0 is:

```lean
rw [ncard_topDimMinPrimes_quotient_eq,
    ncard_topDimMinPrimes_quotient_eq,
    quotTopDimSet_sigma_exact_eq]
```

Containment direction is:

```lean
sigmaIdeal = vanishingIdeal(LE) ≤ vanishingIdeal(exact)
```

because `exact ⊆ LE` and `vanishingIdeal` is antitone.

Minimal W0 facts:

- `Ile := sigmaIdeal`, `Ieq := vanishingIdeal exact`, with `Ile ≤ Ieq`.
- `Ile.height = C` and `Ieq.height = C`.
- Closed-top hard direction: if `q ∈ Ile.minimalPrimes` and `q.height = C`, prove `Ieq ≤ q` via recovery:
  `q = partitionIdeal m`, realizer orbit lies in exact rank locus, so `vanishingIdeal exact ≤ q`.
- Then apply `Ideal.mem_minimalPrimes_of_height_eq` [VERIFY] to get `q ∈ Ieq.minimalPrimes`.
- Easy direction: if `q ∈ Ieq.minimalPrimes` and `q.height = C`, then `Ile ≤ Ieq ≤ q`; apply the same lemma to get `q ∈ Ile.minimalPrimes`.

This packages “lower strata are not top” as height equality plus strict lower-stratum height, rather than as full minimal-prime equality.

**3. Keystone Instance Diamond**

Yes: introduce reducible `abbrev`s to pin one instance path.

```lean
abbrev FibrePolyRing :=
  MvPolynomial (SchurVar (d 0) (d (Fin.last (N+1))) r)
    (sweepFibreRing k d r hp hq)
```

Then in the proof:

```lean
let A : Type u := FibrePolyRing k d r hp hq
letI : CommRing A := inferInstance
letI : Algebra k A := inferInstance
let gF : A := chartGfib k d r hp hq
```

For **hper**, do not expose `A ⧸ Ideal.map C q`. Use the keystone’s arbitrary prime `p` directly:

```lean
have hper : ∀ p ∈ TopDimMinPrimes A,
    ringKrullDim (Localization.Away (Ideal.Quotient.mk p gF)) = ringKrullDim (A ⧸ p) := by
  intro p hp
  haveI : p.IsPrime := isPrime_of_mem_topDimMinPrimes hp
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  haveI : Algebra.FiniteType k (A ⧸ p) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p)
      (Ideal.Quotient.mkₐ_surjective k p) -- [VERIFY]
  have hg : Ideal.Quotient.mk p gF ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem] -- [VERIFY]
    exact havoid p hp
  exact ringKrullDim_localizationAway_eq_of_fg_domain (k := k) (A ⧸ p)
    (Ideal.Quotient.mk p gF) hg
```

Use `map C q` only for **havoid**:

```lean
let q := Ideal.comap (C : sweepFibreRing k d r hp hq →+* A) p
have hmap : Ideal.map (C : sweepFibreRing k d r hp hq →+* A) q = p := ...
rw [← hmap]
exact chartGfib_not_mem_map_C d r hp hq q
```

A local `set_option synthInstance.maxHeartbeats 400000` is acceptable around a tiny helper after the ring aliases are pinned. If it is needed to elaborate `A ⧸ Ideal.map C q`, it is masking the wrong shape; avoid that quotient expression.

**4. Risks**

Main correction: `FibreUnit` overshoots the stated nonlocalized headline unless the theorem endpoint is explicitly localized.

W0 is not formal from `sigmaIdeal ≤ exactIdeal`; the hard input is `exactIdeal ≤ q` for every closed top component `q`. That is exactly where recovery plus realizer-in-exact-rank is needed.

W1/W2 have the DVR-style per-prime risk: ambient no-drop plus avoidance is not enough. For each top prime `p`, you need `f̄ ≠ 0` in the affine domain `A ⧸ p`, then apply the finite-type-domain no-drop.

Extra hypotheses to keep visible: `[Infinite k]` for ChartE, `[IsNoetherianRing O(F)]` and finite `SchurVar` for Poly, finite-type quotient instances for hper, and `[IsAlgClosed k]` for vanishing-ideal/radical identifications.