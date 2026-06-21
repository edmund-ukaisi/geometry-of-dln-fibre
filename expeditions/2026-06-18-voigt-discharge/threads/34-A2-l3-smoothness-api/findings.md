# Thread 34 — Mathlib v4.29 API map for the L3 smoothness build (`IsSmoothAt k m_M` via homogeneity)

scout (Mathlib-coverage recon), 2026-06-20. All `#check`s below COMPILED at the v4.29 pin
(`import Mathlib`, `lake env lean` against the pinned olean cache). Codex (xhigh) consulted on the
crux (item 4); artefacts `codex/crux-{prompt,answer}.md`.

## VERDICT (one line)

**L3 is BUILDABLE at v4.29, 5–7 modules, and the crux is NOT a Borel "orbit-is-locally-closed"
theorem.** Every Mathlib brick (i)–(iv) is PRESENT with a confirmed signature. The thread-29
break-point — `IsOpen O_M` — **dissolves**: you never prove `O_M` open. You prove the orbit's
**closed points are DENSE** in `Spec A` (their vanishing ideal is `⊥`, straight from the landed L6
ideal equality), then intersect the dense-open smooth locus with that dense set. The single hardest
must-build lemma is `vanishingIdeal {orbit closed points} = ⊥` — a CHEAP consequence of L6.

## API TABLE (claim · Mathlib name · status · signature sketch)

### Item 1 — `IsSmoothAt` unfolding + smoothLocus

| Claim | Mathlib name | Status | Signature |
|---|---|---|---|
| `IsSmoothAt R p ≡ FormallySmooth R (AtPrime p)` | `Algebra.IsSmoothAt` (abbrev) | PRESENT | `abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] := Algebra.FormallySmooth R (Localization.AtPrime p)`. The `example … = … := rfl` COMPILED — it is *definitionally* this. |
| smooth locus set | `Algebra.smoothLocus R A` | PRESENT | `: Set (PrimeSpectrum A) := {p | IsSmoothAt R p.asIdeal}` |
| smooth locus open | `Algebra.isOpen_smoothLocus` | PRESENT | `[FinitePresentation R A] → IsOpen (smoothLocus R A)` |
| smooth locus = univ ↔ smooth | `Algebra.smoothLocus_eq_univ_iff` | PRESENT | `[FinitePresentation R A] → smoothLocus R A = univ ↔ FormallySmooth R A` |
| smooth ⟹ nearby basic open smooth | `Algebra.IsSmoothAt.exists_notMem_smooth` | PRESENT | `[FinitePresentation R A] (p) [IsSmoothAt R p] → ∃ f ∉ p, Smooth R (Localization.Away f)` |

Ring-side generic smoothness is ABSENT (no `smoothLocus` nonempty/dense at v4.29) — this is exactly
why item 2 detours through schemes. `isOpen_smoothLocus`/`eq_univ_iff` need `[FinitePresentation R A]`.

### Item 2 — generic smoothness (the Spec detour) + closed-point extraction + back-transport

| Claim | Mathlib name | Status | Signature / hypotheses |
|---|---|---|---|
| smooth locus DENSE over perfect field | `Scheme.Hom.dense_smoothLocus_of_perfectField` | PRESENT | `{K}[Field K][PerfectField K][IsReduced X] (f : X ⟶ Spec(.of K)) [LocallyOfFinitePresentation f] → Dense ↑(f.smoothLocus)` |
| generic point is smooth | `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` | PRESENT | needs `[IsIntegral X]` (vs `[IsReduced X]` for the dense version) |
| smooth locus as an open subscheme | `Scheme.Hom.smoothLocus` | PRESENT | `(f) [LocallyOfFinitePresentation f] → X.Opens` (carries `IsOpen`) |
| membership | `Scheme.Hom.mem_smoothLocus` | PRESENT | `x ∈ f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth` |
| stalk-FS ↔ ring smoothLocus | `AlgebraicGeometry.formallySmooth_stalkMap_iff` | PRESENT | the affine-local dictionary `(stalkMap).hom.FormallySmooth ↔ primeIdealOf ∈ Algebra.smoothLocus Γ(Y,U) Γ(X,V)` |
| preimage along open imm. | `Scheme.Hom.preimage_smoothLocus_eq` | PRESENT | `[IsOpenImmersion f][LocallyOfFinitePresentation g] → f ⁻¹ᵁ g.smoothLocus = (f≫g).smoothLocus` |
| k-points ↔ closed points | `AlgebraicGeometry.pointEquivClosedPoint` | PRESENT | `[IsAlgClosed K] (f)[LocallyOfFiniteType f] → {p // p≫f=𝟙} ≃ closedPoints X` |
| k-point from closed point | `AlgebraicGeometry.pointOfClosedPoint` | PRESENT | `(x)(IsClosed {x}) → (Spec(.of K) ⟶ X)` |
| Jacobson ⟹ closed point in locally-closed | `nonempty_inter_closedPoints` | PRESENT | `[JacobsonSpace X] {Z} → Z.Nonempty → IsLocallyClosed Z → (Z ∩ closedPoints X).Nonempty` |
| f.t. over Jacobson is Jacobson | `LocallyOfFiniteType.jacobsonSpace` | PRESENT | `(f)[LocallyOfFiniteType f][JacobsonSpace Y] → JacobsonSpace X` |
| stalk ≃ₐ AtPrime (back-transport) | `StructureSheaf.stalkIso` | PRESENT | `(x : PrimeSpectrum R) → Localization.AtPrime x.asIdeal ≃ₐ[R] stalk x`. **WRINKLE: `≃ₐ[R]` over the RING R, not the base field k.** Transport `FormallySmooth k` needs `restrictScalars` / `formallySmooth_algebraMap`. The cleaner path is `formallySmooth_stalkMap_iff` (above): it converts the scheme-side `stalkMap.FormallySmooth` directly to ring-side `∈ Algebra.smoothLocus`, which IS the `IsSmoothAt`. |

### Item 5 — residue field κ(m_M) = k (rational point)

| Claim | Mathlib name | Status | Signature |
|---|---|---|---|
| residue field of closed k-point ≅ k | `AlgebraicGeometry.residueFieldIsoBase` | PRESENT | `[IsAlgClosed K] (f)[LocallyOfFiniteType f] (x)(IsClosed {x}) → X.residueField x ≅ .of K` |
| closed point ↔ maximal ideal | `PrimeSpectrum.isClosed_singleton_iff_isMaximal` | PRESENT | `(x) → IsClosed {x} ↔ x.asIdeal.IsMaximal` |

`m_M = ker(eval_M)` is the point ideal of the k-rational tuple M; over `[IsAlgClosed k]` it is
maximal (Nullstellensatz) with residue field k. The L2a brick `CotangentJacobian` already assumes a
`k`-RATIONAL point with `κ = k`; this is consistent. No new Mathlib gap here.

### Item 3 — G-stability transfer

| Claim | Mathlib name | Status | Signature |
|---|---|---|---|
| transfer FS across algebra equiv | `Algebra.FormallySmooth.of_equiv` | PRESENT | `[FormallySmooth R A] (e : A ≃ₐ[R] B) → FormallySmooth R B` |
| iff version | `Algebra.FormallySmooth.iff_of_equiv` | PRESENT | `(e : A ≃ₐ[R] B) → (FormallySmooth R A ↔ FormallySmooth R B)` |
| perfect-field stalk is FS | `Algebra.FormallySmooth.of_perfectField` | PRESENT | `[PerfectField K][EssFiniteType K L] → FormallySmooth K L` (used inside the generic-point lemma) |
| RingHom-FS ↔ Algebra-FS | `RingHom.formallySmooth_algebraMap` | PRESENT | `(algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S` |

The G-action's coordinate change is LANDED as an AlgHom: `Core.OrbitClosure.baseChangePullback P :
MvPolynomial (RepCoord d) k →ₐ[k] MvPolynomial (RepCoord d) k` (= `aeval (baseChangeSub P)`), with
`eval_baseChangePullback` (= eval at the shifted point) already proved. L3.0 upgrades this to an
`AlgEquiv` (inverse via `P⁻¹`), checks `comap (vanishingIdeal Z_M) = vanishingIdeal Z_M`
(G-stability, also essentially landed: `orbitSet_baseChange_stable`,
`baseChangePullback_mem_vanishingIdeal_orbitSet`), descends to `A ≃ₐ[k] A`, localizes to
`AtPrime m_{P•M} ≃ₐ[k] AtPrime m_M`, then `iff_of_equiv`.

### Item 4 — the "crux" bricks (rank-stratum open / dense-orbit-closed-points)

| Claim | Mathlib name | Status | Signature |
|---|---|---|---|
| basic open is open | `PrimeSpectrum.isOpen_basicOpen` | PRESENT | `IsOpen ↑(basicOpen a)` |
| zero locus is closed | `PrimeSpectrum.isClosed_zeroLocus` | PRESENT | `IsClosed (zeroLocus s)` |
| closure = zeroLocus(vanishingIdeal) | `PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure` | PRESENT | `zeroLocus (vanishingIdeal t) = closure t` |
| zeroLocus ⊥ = univ | `PrimeSpectrum.zeroLocus_bot` | PRESENT | `zeroLocus ⊥ = univ` |
| dense meets nonempty open | `Dense.inter_open_nonempty` | PRESENT | `Dense s → ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty` (alias of `dense_iff_inter_open`) |
| dense ↔ closure = univ | `dense_iff_closure_eq` | PRESENT | |
| open/closed ⟹ locally closed | `IsOpen.isLocallyClosed` / `IsClosed.isLocallyClosed` | PRESENT | feeds `nonempty_inter_closedPoints` |
| Chevalley (ring-side) | `PrimeSpectrum.isConstructible_range_comap` | PRESENT | `f.FinitePresentation → IsConstructible (range (comap f))` (light hyps) |
| Chevalley (scheme-side) | `Scheme.Hom.isConstructible_image` | PRESENT | needs `[QuasiCompact f][CompactSpace Y][QuasiSeparatedSpace Y]` (heavier — avoid if the dense route works) |
| **matrix-rank lower-semicontinuity / "rank ≥ r is open"** | — | **ABSENT** | grep-confirmed: no such Mathlib lemma at v4.29. The open stratum is built BY HAND from the landed `RankLocusClosed.rank_le_iff_forall_submatrix_det_eq_zero` + `eval_minorPoly`, NOT from a Mathlib semicontinuity result. |

Structural bricks for modelling `Spec A` (`A = R/I` a domain): `IsReduced (Spec R)` from `[IsReduced
R]` (PRESENT, `Properties.lean`); `isReduced_of_isIntegral`, `irreducibleSpace_of_isIntegral`,
`isIntegral_of_irreducibleSpace_of_isReduced` (PRESENT); `IsDomain A ⟹ IsReduced A` (instance,
COMPILED); `IsAlgClosed k ⟹ PerfectField k` (instance, COMPILED); structure morphism
`Spec(.of A) ⟶ Spec(.of k) := Spec.map (CommRingCat.ofHom (algebraMap k A))` (type-checks,
`noncomputable`).

---

## THE CRUX (item 4), resolved — `IsOpen O_M` is the WRONG target

Thread-29 flagged `exists_closed_smooth_point_mem_openOrbit` (needing `IsOpen O_M`) as the
hardest must-build lemma. **It is reachable, and there are two routes, neither needing a Borel
orbit-locally-closed theorem.** Codex (decorrelated, xhigh) converged independently and supplied the
better one.

### The point-set TRAP (Codex's load-bearing correction)
`orbitSet M : Set (RepCoord d → k)` is a set of CLOSED points (k-rational tuples). On the ring side
it maps to a set of MAXIMAL ideals of `A`. A set of closed points is **NOT open** in a
positive-dimensional `Spec A` (it omits the generic point). So "transport O_M to an open subset of
Spec A" — the naive reading of thread-29's `IsOpen O_M` — is **false as stated**. There are two
honest things one can prove instead:

### Route DENSE (RECOMMENDED — cheapest, uses L6 directly; Codex's pick)
Do not prove anything open about O_M. Prove the orbit's closed points are **dense**:

    Dense { p : PrimeSpectrum A | ∃ x ∈ orbitSet M, p = pointIdeal x }

via `zeroLocus_vanishingIdeal_eq_closure` + `zeroLocus_bot`: the set is dense iff its vanishingIdeal
is `⊥` (A reduced, being a domain). And `vanishingIdeal {orbit closed points} = ⊥` is immediate from
the landed L6 equality `vanishingIdeal (orbitSet M) = vanishingIdeal (canonicalCoord '' orbitRankLocus
M) = I` (the ideal we quotiented by) — a polynomial vanishing on every orbit point lies in `I`, hence
is `0` in `A`. Then the dense-open smooth locus `S` meets this dense set
(`Dense.inter_open_nonempty`), so the smooth point IS an orbit point; `nonempty_inter_closedPoints`
(Jacobson) hands a closed one; transitivity (`rankPattern_eq_iff_orbit` + L3.0/L3.1) carries
smoothness to `m_M`.
- **Single hardest must-build lemma:** `vanishingIdeal {orbit closed points in A} = ⊥`. CHEAP — a
  rewrite of the landed L6 ideal equality through the quotient. No determinantal openness, no
  semicontinuity, no Chevalley.

### Route OPEN-STRATUM (heavier; only if genuine `IsOpen` is wanted downstream)
The rank-EQUALITY stratum is a genuine open of `Spec A`:

    U_M = ⋂_{i≤j} ⋃_{er,ec : Fin r_ij → …} D( q(minorPoly i j hij er ec) ),   r_ij = rankPattern M i j

(`q` = quotient map `R → A`; `er,ec` index `r_ij × r_ij` submatrices of the interval product).
`U_M` is open (finite ∩ of finite ∪ of basic opens). Its CLOSED k-points are exactly O_M. The
complement `Z_M \ U_M = ⋃_{i≤j} {rank ≤ r_ij − 1}` is a finite union of determinantal closed loci.
- **Build cost:** MODERATE (2–3 modules). Must package "rank ≥ r ⟺ some r×r minor ≠ 0" as a
  basic-open union FROM SCRATCH (Mathlib's rank-semicontinuity is ABSENT), reusing the landed
  `rank_le_iff_forall_submatrix_det_eq_zero`, `exists_submatrix_det_ne_zero_of_le_rank`,
  `eval_minorPoly`. Codex's caveat: do NOT claim each `{rank ≤ r_ij − 1}` stratum is itself an
  `orbitRankLocus` of a smaller tuple (the lowered pattern need not be realizable) — it is "merely" a
  determinantal closed set, which is all that is needed.

**Recommendation:** take Route DENSE for L3. It is strictly cheaper, leans on the L6 deliverable
that the ladder already assumes, and sidesteps the point-set topology entirely. Reserve Route
OPEN-STRATUM only if a later result needs `U_M` open as an object (none currently does).

---

## THE A3 BUILD PLAN (L3.0–L3.4)

`A = R/I`, `R = MvPolynomial (RepCoord d) k`, `I = vanishingIdeal(canonicalCoord '' orbitRankLocus M)`.
`[IsAlgClosed k]` (⟹ `PerfectField k`); `A` is a finite-presentation domain (L1'/L6). Target instance
`Algebra.IsSmoothAt k m_M` (≡ `FormallySmooth k (AtPrime m_M)`, by `rfl`).

| Sub-module | Statement | Reuse vs build | Sizing |
|---|---|---|---|
| **L3.0** `GActionRingAuto` | `α_P : A ≃ₐ[k] A` from `P : BaseChangeGroup d`; `α_P (m_{P•M}) = m_M`; localizes to `AtPrime m_{P•M} ≃ₐ[k] AtPrime m_M`. | REUSE landed `baseChangePullback` (AlgHom), `eval_baseChangePullback`, `orbitSet_baseChange_stable`, `baseChangePullback_mem_vanishingIdeal_orbitSet`. BUILD: AlgHom→AlgEquiv upgrade (inverse via `P⁻¹`), descent to quotient (`Ideal.quotientEquivAlgOfEq`/`comap`), localization equiv. | ~1 module |
| **L3.1** `GStabilitySmooth` | `IsSmoothAt k m_{P•M} ↔ IsSmoothAt k m_M`. | REUSE `Algebra.FormallySmooth.iff_of_equiv` ∘ L3.0. | ~0.5 module |
| **L3.2** `SpecModel` + generic smoothness | model `X = Spec(.of A)`, `f = Spec.map (algebraMap k A)`; instances `IsReduced`/`IsIntegral X` (from domain), `LocallyOfFinitePresentation f`, `JacobsonSpace X`; obtain dense-open smooth locus `S`. | REUSE `dense_smoothLocus_of_perfectField`, `Scheme.Hom.smoothLocus` (open), `LocallyOfFiniteType.jacobsonSpace`, the integral/reduced bridges, `Spec`-functor API. BUILD: the instance plumbing (`FinitePresentation k A → LocallyOfFinitePresentation`, the `Spec.of A` ↔ ring `A` identifications). | ~2 modules (instance-heavy) |
| **L3.3** `DenseOrbitClosedPoints` (Route DENSE) | `Dense {p | ∃ x ∈ orbitSet M, p = pointIdeal x}` in `Spec A`. | REUSE `zeroLocus_vanishingIdeal_eq_closure`, `zeroLocus_bot`, landed L6 ideal equality. BUILD: the single lemma `vanishingIdeal{orbit closed points} = ⊥` (CHEAP) + the closed-point/maximal-ideal dictionary glue. | ~1 module |
| **L3.4** `Assemble` | `S` dense-open ∩ dense orbit-closed-points → a smooth closed orbit k-point (`Dense.inter_open_nonempty` + `nonempty_inter_closedPoints`); `pointEquivClosedPoint`/`residueFieldIsoBase` give it as a k-point of O_M; `formallySmooth_stalkMap_iff`/`StructureSheaf.stalkIso` bring smoothness ring-side as `IsSmoothAt k m_{x}`; transitivity (L3.1 + `rankPattern_eq_iff_orbit`) moves it to `m_M`. Register `IsSmoothAt k m_M`. | REUSE all of the above + `formallySmooth_stalkMap_iff`. BUILD: the assembly chain (the `smooth_of_grpObj` proof body, lines 38–60, is the reusable TEMPLATE — minus `GrpObj.mulRight`, replaced by L3.0's `α_P`). | ~1.5 modules |

**Module count: 6** (L3.2 is 2, others ~1 each; matches thread-29's 5–7). If Route OPEN-STRATUM is
taken instead of L3.3, add 1–2 modules.

### The single hardest must-build lemma
**`vanishingIdeal {orbit closed points} = ⊥` in `A`** (Route DENSE's L3.3 core) — but this is CHEAP
(a rewrite through L6). The genuinely *fiddly* (not deep) work is **L3.2's instance plumbing**: making
Lean see `Spec(.of A)` as reduced+integral+finite-presentation+Jacobson over `k`, and the
scheme-side `stalkMap.FormallySmooth` ↔ ring-side `Algebra.smoothLocus` translation via
`formallySmooth_stalkMap_iff` on an explicit affine cover (the affine case is `⊤`, so the cover is
trivial, but the `IsAffineOpen.primeIdealOf` bookkeeping is real). That plumbing — not any single
theorem — is where the time goes. No from-scratch mathematics; it is all landed-brick assembly.

## Is `IsOpen O_M` reachable? — final answer
- As literally stated (O_M open as a point set in `Spec A`): **FALSE** (set of closed points).
- As the rank-equality scheme-stratum `U_M` open: **YES, MODERATE** (2–3 modules, builds the
  rank-≥-r-is-basic-open-union brick by hand; Mathlib lacks rank semicontinuity).
- **You don't need it.** Route DENSE replaces `IsOpen O_M` with `Dense {orbit closed points}`
  (CHEAP, from L6) and finishes L3. This is the recommended path; it removes thread-29's flagged
  hardest sub-lemma.

## Scope reminder (inherited, not re-derived)
L3 itself is char-free (smoothness of the closure at the normal-form point). The `[CharZero k]`
hypothesis is needed only DOWNSTREAM, in L2b★ (separability of the orbit map; the Frobenius witness),
not in L3. L3 needs `[IsAlgClosed k]` (⟹ perfect, Jacobson, k-points = closed points).

## Honest gaps / risks
- L3.2 instance plumbing is the realistic time sink (fiddly, not hard). De-risk by first wiring the
  `Spec(.of A)` model + its `IsIntegral`/`FinitePresentation`/`Jacobson` instances in a standalone
  `example` before the smoothness body.
- The `StructureSheaf.stalkIso` is `≃ₐ[R]` not `≃ₐ[k]`; the clean route is to NOT use it directly but
  to use `formallySmooth_stalkMap_iff` (scheme-side FS ↔ ring `smoothLocus` membership) which already
  bakes in the base. Flag for the formaliser.
- Route DENSE's `vanishingIdeal{orbit closed points} = ⊥` assumes the orbit-closed-points are the
  k-rational maximal ideals and that L6 is delivered as a `vanishingIdeal` equality (it is). If L6
  delivers only set-equality of closures, add one `congrArg vanishingIdeal` (thread-29 L1' already
  notes this).
