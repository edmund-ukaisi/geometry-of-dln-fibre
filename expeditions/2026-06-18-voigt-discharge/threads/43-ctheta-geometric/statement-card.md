# Statement card — thread 43, `Core.CThetaGeometric` (geometric reading of `C`)

**Thread:** 43-ctheta-geometric (voigt-discharge expedition; wiring the discharged `hVoigt` into the
combinatorial `(C,θ)` so the per-orbit geometric reading is formal + unconditional).
**Pinned commit:** `bb23e70` (branch `expedition/voigt-discharge`).
**Module:** `lean/DLNFibre/Core/CThetaGeometric.lean` (new; imported at the END of `lean/DLNFibre.lean`).
**Build:** whole `DLNFibre` library green (3012 jobs); `scripts/sorries` = 0; all five new headlines
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**Scope of all headlines:** `[Field k] [IsAlgClosed k] [CharZero k]` (the scope of the discharged
Voigt lemma). These are geometric **codimension** statements — NOT RLCT, NOT `½·codim` (the RLCT
payoff is a separate, `DLN`-side, Cited reading).

---

## Deliverable 1 — per-orbit geometric reading (UNCONDITIONAL)

> **Claim.** For an interval list `L`, the genuine geometric codimension of the orbit closure `Ō_M`
> of `M = ⊕_{(a,b)∈L} M_{ab}` (the rank locus, Thm 3.8 proved in-engine), read at the canonical flattening,
> equals the combinatorial Cor 3.5 form `codimForm N (multiplicityArray L)`.
>
> - **Lean:** `DLNFibre.Core.codimRepCanonical_orbitRankLocus_eq_codimForm`
>   (`lean/DLNFibre/Core/CThetaGeometric.lean` @ `bb23e70`)
> - **Signature.** `[IsAlgClosed k] [CharZero k] (L) : ((codimRepCanonical (orbitRankLocus
>   (intervalDirectSum (k := k) L))).toNat : ℤ) = codimForm N (multiplicityArray L)`
> - **Gloss.** The `Ideal.height` of the vanishing ideal of the orbit closure (read at the canonical
>   one-variable-per-matrix-entry flattening), coerced `ℕ∞ → ℕ → ℤ`, equals the paper's quadratic
>   form `∑_{1≤i≤u≤j≤v≤N} m_{i-1,j-1} m_{uv}`. "The combinatorial codimension form IS the geometric
>   orbit-closure codimension."
> - **Proved.** Unconditionally for `[IsAlgClosed k] [CharZero k]`: feeds the discharged Voigt lemma
>   `Core.VoigtDischarge.codimRep_orbitRankLocus_eq_orbitLinearCodim` into the (formerly conditional)
>   `Core.OrbitCodim.codimRepCanonical_orbitRankLocus_eq_multSum`, then folds the RHS into `codimForm`
>   via the `rfl`-bridge `codimForm_multiplicityArray`.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]` (named instance hypotheses).
> - **Cited.** none. Thm 3.8 (orbit closure = rank locus `orbitRankLocus`, the ideal-level identity
>   `Core.OrbitClosure.vanishingIdeal_orbitRankLocus_eq_orbitSet`) is **Proved in the engine**, not
>   merely cited; Voigt's lemma is **Proved** in `Core.VoigtDischarge`. The paper attributions
>   (Lehalleur–Rimányi Thm 3.8, Cor 3.5, Voigt) name the *source* of the results, all reproved here.
> - **Deferred.** none (for the per-orbit reading).
> - **Status.** sorry-free, axiom-clean.

Companion ℕ∞ form: `codimRepCanonical_orbitRankLocus_eq_orbitLinearCodim` —
`codimRepCanonical (orbitRankLocus (⊕L)) = (orbitLinearCodim (⊕L) : ℕ∞)`.

---

## Deliverable 2 — `cCodim` as the minimum of GEOMETRIC codimensions (UNCONDITIONAL)

> **Claim.** The combinatorial codimension `cCodim d r` equals the minimum, over the Kostant
> partitions `m` of `d` with corner `r`, of the genuine geometric codimension of the orbit closure of
> `⊕_{(a,b)} M_{ab}^{m}`.
>
> - **Lean:** `DLNFibre.Core.cCodim_eq_inf_geomCodim`
>   (`lean/DLNFibre/Core/CThetaGeometric.lean` @ `bb23e70`)
> - **Signature.** `[IsAlgClosed k] [CharZero k] (d) (r) (h : (kostantPartitions d r).Nonempty) :
>   cCodim d r h = (kostantPartitions d r).inf' h (fun m ↦ ((codimRepCanonical (orbitRankLocus
>   (intervalDirectSum (k := k) (listOfPartition m)))).toNat : ℤ))`
> - **Gloss.** `cCodim d r` (the min of the combinatorial form over Kostant partitions) is exactly the
>   minimum over those same partitions of the actual geometric orbit-closure codimension — `C` is the
>   smallest orbit-closure codimension among the rank-`r` orbits.
> - **Proved.** Unconditionally for `[IsAlgClosed k] [CharZero k]`. Bridge: `listOfPartition m`
>   realises the array (`multiplicityArray_listOfPartition : multiplicityArray (listOfPartition m) =
>   extendℤ m`), so the per-partition summand `codimForm N (extendℤ m)` equals the geometric codim of
>   the corresponding orbit closure (`codimForm_extendℤ_eq_geomCodim`); the minimum transports by
>   `Finset.inf'_congr`.
> - **Assumed.** `[IsAlgClosed k] [CharZero k]`; `h : (kostantPartitions d r).Nonempty` (carried by
>   `cCodim` itself).
> - **Cited.** none (Thm 3.8 proved in-engine, as in deliverable 1).
> - **Deferred.** none (for this per-orbit-aggregated-over-partitions reading).
> - **Status.** sorry-free, axiom-clean.

Supporting lemmas (same module, axiom-clean): `listOfPartition`, `sum_flatMap_replicate_map`,
`multiplicityArray_listOfPartition`, `codimForm_extendℤ_eq_geomCodim`.

---

## The remaining step (ROADMAP — documented in the module, NOT built)

The full **`Σ^r`-aggregate** reading — "`cCodim d r` = geometric codimension of the *whole* rank-`r`
product locus `Σ^r`" and "`numTop d r` = number of top-dimensional **geometric** components of `Σ^r`"
— is **NOT** formalised. `Σ^r` is not defined as a geometric variety in `Core` (only prose, in
`Core.Setup` / docstrings). Closing it needs, for a future tide: (i) a geometric def of `Σ^r`;
(ii) its orbit stratification `Σ^r = ⋃_M Ō_M`; (iii) codim-of-a-union = min-over-components, and the
analogous top-component count. The per-orbit reading (deliverables 1, 2) is the input to that step;
the component-count half of `numTop`'s geometric reading remains open. (See the
`numTop_d222_zero` docstring in `Core.CTheta`.)

---

## Docstring refreshes (precision: deferral pointers updated to "proved")

The combinatorial `cCodim`/`numTop` defs and their combinatorial theorems are **unchanged** (they stay
honest combinatorics). Only docstrings that read "rides on / rests on the DEFERRED `hVoigt`" were
repointed at the now-proved `Core.CThetaGeometric`:

- `Core.CTheta` — module docstring, `cCodim` docstring, rank-shift section, `numTop_d222_zero`
  (the last keeps the `Σ^r`-aggregate component-count as OPEN, per the roadmap).
- `Core.CThetaQIPConverse` — `cCodim_eq_qipMin` docstring.
- `Core.OrbitLinearCodim` — module docstring + `orbitLinearCodim` / `orbitLinearCodim_eq_multSum` /
  witness docstrings (the object stays the "linear shadow"; the geometric bridge is proved elsewhere).
- `Core.OrbitCodim` — **unchanged**: its conditional headlines genuinely *take* `hVoigt` as a
  hypothesis, so "modulo Voigt" is name = content for those; the unconditional versions live in
  `Core.VoigtDischarge`.

## Fidelity note (for the reviewer)

- The geometric object is `codimRepCanonical = codimRep (canonicalCoord d)` = `Ideal.height` of the
  vanishing ideal at THE canonical linear flattening (one variable per matrix entry) — not an
  arbitrary set-bijection. This is the coordinatisation at which the height is the genuine geometric
  codimension; the discharged Voigt lemma is stated there.
- `codimForm N (multiplicityArray L)` is the committed Cor 3.5 RHS by `codimForm_multiplicityArray`
  (`rfl`); `codimForm N (extendℤ m)` is what `cCodim` minimises, and `multiplicityArray_listOfPartition`
  is full function equality `multiplicityArray (listOfPartition m) = extendℤ m` (not just on the box).
- Name = content: every headline is a **codimension** statement (no `rlct`, no `½`). The hypotheses
  `[IsAlgClosed k] [CharZero k]` are carried honestly (the scope of the discharged `hVoigt`).
