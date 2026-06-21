# Statement card — A6 capstone: `hVoigt` discharged, geometric-codim headline unconditional

Status: **sorry-free**, axiom-clean (`[propext, Classical.choice, Quot.sound]`). Whole library green.

## Claim

Voigt's lemma for the equioriented type-`A` quiver: the **geometric** codimension of the `G_d`-orbit
closure `Ō_M` (the determinantal rank locus `orbitRankLocus M`, Lehalleur–Rimányi Thm 3.8 cited) equals
the **expected** (tangent-space) codimension `orbitLinearCodim M = dim Ext¹(M,M)`. Discharging this makes
the geometric-codimension headline (Cor 3.5, the paper's quadratic form) hold with no open hypothesis.

## Lean

Module: `lean/DLNFibre/Core/VoigtDischarge.lean` (A6.2) + `lean/DLNFibre/Core/OrbitTangentCotangent.lean` (A6.1).

### The discharge (`hVoigt`)
```
theorem codimRep_orbitRankLocus_eq_orbitLinearCodim
    [IsAlgClosed k] [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)
```
This is exactly the `hVoigt` hypothesis that `codimRepCanonical_orbitRankLocus_eq_multSum` was stated
modulo; supplying it makes that headline unconditional.

### The unconditional headline (the deliverable)
```
theorem codimRepCanonical_orbitRankLocus_eq_multSum_unconditional
    [IsAlgClosed k] [CharZero k] (L : List (Fin (N + 1) × Fin (N + 1))) :
    ((codimRepCanonical (orbitRankLocus (intervalDirectSum (k := k) L))).toNat : ℤ)
      = ∑ i ∈ Finset.Icc (1 : ℤ) N, ∑ u ∈ Finset.Icc i N, ∑ j ∈ Finset.Icc u N, ∑ v ∈ Finset.Icc j N,
          multiplicityArray L (i-1) (j-1) * multiplicityArray L u v
```

### The reverse inequality (A6.1, char-free content)
```
theorem finrank_range_deformationδ_le_varietyDim
    [IsAlgClosed k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    (finrank k (LinearMap.range (deformationδ M M)) : ℕ∞)
      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M)
```

### The squeeze
```
theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
    [IsAlgClosed k] [CharZero k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
    varietyDim (canonicalCoord d '' orbitRankLocus M)
      = (finrank k (LinearMap.range (deformationδ M M)) : ℕ∞)
```

### The crux R2★ (the one genuinely new lemma)
```
theorem dirDeriv_orbitIdeal_eq_zero [Infinite k] (M : Tuple (k := k) d) (φ : cochain0 (k := k) d d)
    {f : MvPolynomial (RepCoord d) k} (hf : f ∈ orbitIdeal M) : dirDeriv M φ f = 0
```
Orbit directions `δ⁰ φ` kill the orbit ideal `I` to first order. Proved with the dual-number group
element `P_ε = 1 + ε φ`: `orbitPullback M f = 0` ⟹ `aeval (orbitPointε M φ) f = evalGroupRingε M φ
(orbitPullback M f) = 0`, and `dirDeriv M φ f` is the `ε`-coefficient (`snd`) of that evaluation.
`orbitPointε M φ = (M)_x + ε·(δ⁰φ)_x` by the landed `orbitAction_eps_eq_deformationδ`.

## Hypotheses (the honest scope)
- `[IsAlgClosed k]` — L0 (Nullstellensatz), L1 (primeness), M3 (smooth ⟹ regular over a perfect
  field), the rational-point residue-field identification. (`IsAlgClosed ⟹ Infinite`.)
- `[CharZero k]` — enters ONLY through A4's forward inequality (separability / `DiffIndepCriterion`).
  The reverse inequality A6.1 and the L7 arithmetic are char-free; `[CharZero k]` is on the
  `hVoigt`-discharge because of A4, confirming thread-29/30's scope finding.

## Proof architecture (thread 38 design, INTRINSIC route)
- **A6.1** = R1 (`dirDeriv` directional functional `sndHom ∘ aeval (orbitPointε M φ)`) · R2★ ·
  R3 (`Ideal.Cotangent.lift` factorization, `cotFunctional`) · R4 (`cotPairing` injection,
  `ker cotPairing ⊆ ker δ⁰` via coordinate test `X x − C a_x`) · R5 (rank-nullity + `Subspace.dual_finrank_eq`)
  · R6 (`finrank k (m_M.Cotangent) = varietyDim`: L2a localization collapse + κ/k bridge GAP2 + M3 + GAP3 + L6.4).
- **3 gap-lemmas**: GAP1 `card_repCoord_eq_finrank_cochain1`; GAP2 `residueFieldAtPrimeNormalFormEquiv`
  + `finrank_eq_finrank_of_residueField_equiv`; GAP3 `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`
  (Fintype-indexed L4d via `renameEquiv`).
- **A6.2** = squeeze (`le_antisymm` A4 + A6.1) + L7 (additive cancellation of finite `r = finrank(range δ⁰)`
  from `codimRep + r = card` [L0+squeeze] and `orbitLinearCodim + r = card` [rank-nullity + GAP1]).

## Verification
- `scripts/sorries`: `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `#print axioms codimRepCanonical_orbitRankLocus_eq_multSum_unconditional` → `[propext, Classical.choice, Quot.sound]`.
- Codex consult (xhigh) on R2★ design: `codex/r2star-{prompt,answer}.md` — confirmed dual-number route over
  the (secretly-false) `Polynomial`-curve route, `IsLocalization.liftAlgHom` for ψ over `DualNumber k`.

## Fidelity caveat
`orbitRankLocus M = Ō_M` is the orbit closure **by the cited Thm 3.8** (not proved here, as flagged in
`OrbitCodim`). The geometric codimension `codimRep` is `Ideal.height` of the vanishing ideal at the
canonical entry-flattening. `hVoigt` is now PROVED (not assumed). The `rlct = ½·codim` reading remains
Cited (Aoyagi/Watanabe) — out of scope for this thread.
