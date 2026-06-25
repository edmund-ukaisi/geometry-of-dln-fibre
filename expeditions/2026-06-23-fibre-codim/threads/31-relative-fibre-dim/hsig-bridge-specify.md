# Thread 31 — `hsig` (source no-drop): the ring verdict + the lemma chain

*Seat: pen-and-paper, witness direction. Question: which ring should the localized chart AlgEquiv `e`
and the source no-drop `hsig` be over — `O(Σ^r)` [=r] or `O(Σ̄^r)` [≤r] — to discharge `hsig` cleanly
with NO ideal-equality trap and NO rank-raising/density theorem? Read-only; no Lean writes, no builds.
Decorrelated xhigh Codex fired independently (hypothesis withheld).*

## RING VERDICT (one line)

**Keep `e` + the no-drop over `O(Σ^r)` [the =r ring] — do NOT restate the wrapper over `O(Σ̄^r)`.**
The committed `Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv` is correctly anchored on `O(Σ^r)`.

**The one decisive reason:** a top-dimensional minimal prime `P` of `sigmaIdeal d r` (the ≤r ideal),
where Facts A+B are clean, **already contains** `vanishingIdeal(Σ^r) = I_eq` — so `P/I_eq` is a
*genuine* full-dimensional prime of `O(Σ^r)` avoiding `detΔ`, and the LANDED no-drop
`ringKrullDim_localizationAway_eq_of_avoids_top_prime` applies directly over `O(Σ^r)`. The containment
`I_eq ⊆ P` is the FREE `vanishingIdeal_repClosure` fact applied to the LANDED corner-`r` orbit
`orbitAsTuples(realizerD) ⊆ Σ^r` whose closure is exactly `V(P)` — **NOT** the global rank-raising
density theorem.

---

## The entanglement, resolved (why this is not the ideal-equality trap)

The brief's worry: the no-drop needs a top prime `p₀` of the **=r** ring `O(Σ^r)` (with `detΔ ∉ p₀`),
but Facts A/B live over the **≤r** ideal `sigmaIdeal` (`O(Σ̄^r)`); and `I_eq = vanishingIdeal(Σ^r)`,
`I_le = sigmaIdeal = vanishingIdeal(Σ̄^r)` are equal *only* via the unbuilt set-closure identity
`repClosure(Σ^r) = Σ̄^r`. So one cannot freely transport a top prime from `O(Σ̄^r)` to `O(Σ^r)`.

**The resolution does NOT need the full ideal equality.** It needs only the *one-directional*
containment `I_eq ⊆ P` for the **single, specific** top prime `P` we pick — and that containment is
free, by a per-component argument:

- `I_le ⊆ I_eq` (`ClosureBridge.productRankLocus_subset_productRankLocusLE` ⟹ anti-mono), so
  `Spec(O(Σ^r)) ⊆ Spec(O(Σ̄^r))` as a *closed* subscheme: a prime `P ⊇ I_le` descends to a prime of
  `O(Σ^r)` **iff** additionally `I_eq ⊆ P`. This is NOT automatic for arbitrary primes of `O(Σ̄^r)`
  (Codex flagged the same Spec relationship independently) — but it IS automatic for our chosen `P`.

- **Why `I_eq ⊆ P` for the top prime `P`.** By Fact A, the top prime `P = partitionIdeal d r m =
  vanishingIdeal(canonicalCoord '' orbitRankLocus(realizerD hm))` for a corner-**exactly**-`r` Kostant
  partition `m`. Two LANDED facts close it with **no** density theorem:
  1. The corner-`r` orbit sits in `Σ^r`: `orbitAsTuples(realizerD hm) ⊆ productRankLocus d r`
     (`ClosureBridge.orbitAsTuples_realizerD_subset_productRankLocus hm`), so
     `orbitSet(realizerD hm) = canonicalCoord '' orbitAsTuples(realizerD hm) ⊆ canonicalCoord '' Σ^r`
     (`ClosureBridge.image_orbitAsTuples`, `rfl`).
  2. The orbit rank locus is the Zariski closure of the orbit:
     `canonicalCoord '' orbitRankLocus M = repClosure(orbitSet M)`
     (`OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet`, `[Infinite k]`).
  Chain (anti-mono of `vanishingIdeal`, `OrbitClosure.vanishingIdeal_repClosure` — the **FREE**
  `u_l_u_eq_u` identity, no algebraic-closedness):

      I_eq = vanishingIdeal(canonicalCoord '' Σ^r)
           ⊆ vanishingIdeal(orbitSet(realizerD hm))                      -- (1) + anti-mono
           = vanishingIdeal(repClosure(orbitSet(realizerD hm)))          -- vanishingIdeal_repClosure (FREE)
           = vanishingIdeal(canonicalCoord '' orbitRankLocus(realizerD)) -- (2)
           = P.                                                          -- Fact A

  This is **cleaner than Codex's route** (Codex routed through "`D(detΔ) ∩ V(P)` dense in `V(P)`", a
  point-set dense-open argument at k-points). My route never touches `detΔ` for the *containment* — it
  uses only the LANDED orbit-in-Σ^r membership and the FREE closure-invisible-to-vanishingIdeal fact.
  `detΔ` is needed only for the SEPARATE `detΔ ∉ P` step (Fact B). Both routes avoid the global
  density theorem; mine has a strictly smaller must-build surface.

So `P/I_eq` is a prime of `O(Σ^r)`, full-dimensional (catenary, below) and avoiding `detΔ` (Fact B) —
the exact `(p₀, g)` the LANDED no-drop wants, over `O(Σ^r)`. **No ideal equality, no density theorem.**

---

## The exact `hsig` lemma chain (each step LANDED / cheap / must-build)

Let `R = sweepSigmaRing k d r = MvPolynomial (RepCoord d) k ⧸ I_eq`, `I_eq = vanishingIdeal(canonicalCoord
d '' productRankLocus d r)`, `I_le = sigmaIdeal d r`, `C = cCodim d r h`, `dsig =` image of `ΔPdeep d r
hp hq` (= `detΔ`) under `Ideal.Quotient.mk I_eq`. Target:
`hsig : ringKrullDim (Localization.Away dsig) = ringKrullDim R`.

| # | Step | Status |
|---|---|---|
| 0 | Pick a minimising Kostant partition `m₀` (`Finset.exists_mem_eq_inf'`) and `P := partitionIdeal d r m₀ = vanishingIdeal(canonicalCoord '' orbitRankLocus(realizerD hm₀))`. | LANDED (`ThetaComponentCount.partitionIdeal_of_mem`, `realizerD`) |
| 1 | `P.IsPrime`. | LANDED (`OrbitClosure.isPrime_vanishingIdeal_orbitRankLocus`, `[IsAlgClosed k]`) |
| 2 | `I_eq ⊆ P` — the per-component containment (the orbit-in-Σ^r + `vanishingIdeal_repClosure` chain above). | **must-build ~0.5 mod** (assemble 3 LANDED facts + 1 FREE; no density thm). Equivalently this IS Codex step 6, but via the orbit route not the dense-open route. |
| 3 | `P` carries full dim: `ringKrullDim (MvPolynomial/P) = ringKrullDim O(Σ̄^r)`. From `height P = C.toNat` (the `topComponents` selector — for the minimiser, `codimRepCanonical(orbitRankLocus realizerD) = C`, `ClosureBridge`/`SigmaCodim` `hreal`) and the catenary `height P + ringKrullDim(MvPolynomial/P) = card` (`RadicalCatenary.height_add_ringKrullDim_quotient_eq_card_of_ne_top`), minus the same catenary for `I_le` (`codim Σ̄^r = C`, `SigmaCodim`). | LANDED inputs; **~0.5 mod** to assemble |
| 4 | `ringKrullDim O(Σ̄^r) = ringKrullDim O(Σ^r) = ringKrullDim R`. | LANDED (**F1 = hClosure**, `ClosureBridge.varietyDim_productRankLocus_eq_productRankLocusLE`; `varietyDim Z = ringKrullDim(MvPolynomial/vanishingIdeal Z)` by def, `NullstellensatzCodim.varietyDim`) |
| 5 | The top prime of `R = O(Σ^r)` is `p₀ := P.map (Ideal.Quotient.mk I_eq) = P/I_eq` (well-defined since `I_eq ⊆ P`, step 2); `p₀.IsPrime`, and `ringKrullDim (R/p₀) = ringKrullDim (MvPolynomial/P) = ringKrullDim R` (steps 3+4, `Ideal.quotientQuotientEquivQuotient` / `DoubleQuot`). | **must-build ~0.5 mod** (quotient-of-quotient bookkeeping; standard Mathlib `DoubleQuot.quotQuotEquivQuotOfLE` for `I_eq ⊆ P`) |
| 6 | `detΔ ∉ P` (**Fact B**): on the corner-`r` component `V(P)`, the top-left r×r product minor is not identically zero — H'-stability of `V(P)` (`OrbitClosure.orbitSet_baseChange_stable` + the sweep) + a `GL_{d_N}×GL_{d_0}` permutation moving a nonzero r×r minor of the rank-r product to the top-left slot (`FibreNormalForm.mult_smul`). | **must-build ~1 mod** (the `nodrop-density-adjudication.md` certificate, NOT yet a Lean lemma) |
| 7 | `dsig ∉ p₀`: transport `detΔ ∉ P` across the quotient (`Ideal.Quotient.eq_zero_iff_mem` / `mem_map` for `I_eq ⊆ P`). | cheap (~0.2 mod, rides on step 6) |
| 8 | Apply `Core.AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_avoids_top_prime R dsig p₀ htop hg` ⟹ `hsig`. | LANDED (**F4**) — `R` is f.g. Noetherian `k`-algebra (quotient of `MvPolynomial (RepCoord d) k`); `htop` = step 5, `hg` = step 7. |

**No step is the density / rank-raising theorem. No step assumes `I_eq = I_le`.**

### Hypothesis threading
`ringKrullDim_localizationAway_eq_of_avoids_top_prime` wants `[IsNoetherianRing R] [Algebra k R]
[Algebra.FiniteType k R]` — all hold for `R = MvPolynomial(RepCoord d) k ⧸ I_eq` (quotient of a f.g.
poly ring, `RepCoord d` finite). Facts A/B carry `[IsAlgClosed k] [CharZero k]`; `hClosure` carries the
same; `image_orbitRankLocus_eq_repClosure_orbitSet` carries `[Infinite k]` (implied by `IsAlgClosed` +
`CharZero`). So the discharged `hsig` lives at `[IsAlgClosed k] [CharZero k]` — exactly the
`sweep_of_localizedChartAlgEquiv` / DLN-application scope. Benign.

---

## Does the wrapper need restating? **NO.**

`sweep_of_localizedChartAlgEquiv` (`ChartSweepWiring.lean:107`) takes `hsig` over `sweepSigmaRing =
O(Σ^r)` and feeds the chart-`AlgEquiv` wrapper `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv`
with `Osig = O(Σ^r)`; `RouteCAssembly` + `ClosureBridge` then transport `varietyDim Σ^r → varietyDim
Σ̄^r` via the LANDED `hClosure` at the FINAL assembly step. The entire downstream pipeline is anchored
on the =r ring with `hClosure` as the only ≤r-bridge — and `hClosure` is the DIMENSION equality, which
is exactly what step 4 above also uses. **Restating over `O(Σ̄^r)` would be a strict regression:** it
would force the chart AlgEquiv `e` and the Schur-side `hP` to be re-derived over the ≤r ring, and the
δ-Schur-coordinate freeness (the `e`-tide's core, the `O(F)[δ vars]_{detΔ}` presentation) is built
against the =r chart. So the `e` tide (#58) should **target `O(Σ^r)`** for `dsig` (= image of `ΔPdeep`)
and `e : Localization.Away dsig ≃ₐ[k] Localization.Away gF`, as currently committed.

> **Flag for the `e` tide (#58):** `dsig` must be the image of `ΔPdeep d r hp hq` under
> `Ideal.Quotient.mk I_eq` (i.e. the chart element in `O(Σ^r)`), so that step 6/7's `detΔ ∉ P`
> transports to `dsig ∉ p₀`. If `e` is built with a different `dsig`, the `hsig`-cert's `g = dsig`
> must match it. This is the one coupling between the `e` tide and the `hsig` tide.

---

## Why route 1 (the FREE ideal equality `I_eq = I_le`) is the wrong frame — adjudicated

The brief's route-1 candidate: "`vanishingIdeal(closure S) = vanishingIdeal S` IS free, so IF
`Σ̄^r = repClosure(Σ^r)` then `I_eq = I_le` is free, and `O(Σ^r) = O(Σ̄^r)`." **The premise
`Σ̄^r = repClosure(Σ^r)` is the unbuilt rank-raising/density theorem — NOT cheap, NOT landed.**
The `ClosureBridge` docstring (`:14`) states this explicitly: the codim-sandwich was built precisely to
**avoid** the set-closure identity. Searched the whole engine: no `repClosure(productRankLocus) =
productRankLocusLE` and no `vanishingIdeal(=r) = vanishingIdeal(≤r)` lemma exists.

The decisive insight is that the FULL equality is **overkill**. The no-drop needs `I_eq ⊆ P` for ONE
prime, which is the *easy, one-directional* half (`Σ^r ⊆ Σ̄^r` side is free; the hard half is the
density theorem). The corner-`r` orbit-in-`Σ^r` + `vanishingIdeal_repClosure` route delivers exactly
that one-directional containment per top component, freely. So route 1's "free" framing is right about
`vanishingIdeal_repClosure` being free, but wrong about reaching for the *global* `repClosure(Σ^r) =
Σ̄^r` — the per-component containment is the part that is genuinely free.

(Brief route-2 — restate over the ≤r ring + `hClosure` dim-transport — is *feasible* but a regression,
as argued above; route-3 verdict: the ring is `O(Σ^r)` [=r].)

---

## Module estimate (the `hsig` cert, given the `e` tide lands `dsig` = image of `ΔPdeep`)

| Block | Content | Cost |
|---|---|---|
| step 2 | `I_eq ⊆ P` (orbit-in-Σ^r + `vanishingIdeal_repClosure`) | ~0.5 mod |
| steps 3–5 | full-dim `p₀ = P/I_eq` of `O(Σ^r)` (catenary + quotient-of-quotient) | ~1 mod |
| step 6 | `detΔ ∉ P` (Fact B: H'-stability + permutation-moves-minor) | ~1 mod |
| steps 7–8 | transport `detΔ ∉ p₀` + apply the LANDED no-drop | ~0.3 mod |

**Total `hsig` ≈ 2.5–3 modules.** The single must-build with real content is **step 6 (Fact B)** — the
`detΔ`-avoidance, currently only a pen-and-paper certificate (`nodrop-density-adjudication.md`); the
rest is bookkeeping over LANDED facts (Fact A, `hClosure`, the no-drop, the catenary). This matches the
`nodrop-density-adjudication.md` step-4 estimate (≈1.5–2 mod for 4a+4b) once the +catenary/quotient
plumbing (steps 3–5) is counted.

---

## Engine handles VERIFIED (file:line)

LANDED:
- `Core.ChartSweepWiring.sweep_of_localizedChartAlgEquiv` (`:107`) — the wrapper, `hsig` over
  `sweepSigmaRing = O(Σ^r)` [=r]. **Confirmed: =r ring, no restate needed.**
- `Core.AffineLocalizationNoDrop.ringKrullDim_localizationAway_eq_of_avoids_top_prime` (`:123`) — F4,
  the no-drop; **minimality of `p₀` NOT required**, only "prime carrying full dim + `g ∉ p₀`" (`:121`).
- `Core.ClosureBridge.orbitAsTuples_realizerD_subset_productRankLocus` (`:59`) — corner-`r` orbit ⊆ Σ^r.
- `Core.ClosureBridge.image_orbitAsTuples` (`:54`) — `canonicalCoord '' orbitAsTuples M = orbitSet M`.
- `Core.OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet` (`:993`) — orbit rank locus = closure.
- `Core.OrbitClosure.vanishingIdeal_repClosure` (`:953`) — the **FREE** `u_l_u_eq_u` (no alg-closed).
- `Core.ClosureBridge.varietyDim_productRankLocus_eq_productRankLocusLE` (`:127`) — **F1 = hClosure**
  (DIM equality, NOT ideal equality — explicitly avoids `repClosure(Σ^r)=Σ̄^r`, `:14`).
- `Core.CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of` (`:378`) — **Fact A**: top
  component = corner-`r` partition ideal.
- `Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq` (`:206`) / `Core.ThetaComponentCount.topComponents`
  (`:297`) — top components = min-codim minimal primes of `sigmaIdeal` (≤r).
- `Core.RadicalCatenary.height_add_ringKrullDim_quotient_eq_card_of_ne_top` +
  `codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`:179`) — the catenary for step 3.
- `Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim_enat` (`:101`) — `codim Σ̄^r = C`.
- `Core.NullstellensatzCodim.varietyDim` (`:139`) — `varietyDim Z = ringKrullDim(MvPolynomial/vanishingIdeal Z)`.
- `Core.EndBaseChangeSweep.productRankLocus_eq_iUnion_smul_fibre` (`:81`) + `FibreNormalForm.mult_smul`
  + `OrbitClosure.orbitSet_baseChange_stable` (`:189`) — H'-stability, the input for Fact B (step 6).
- `Core.DeepChartRing.ΔPdeep` (`:107`) — `detΔ` = top-left r×r minor of the deep generic product.

MUST-BUILD (no density theorem in any):
- step 2 (`I_eq ⊆ P`), steps 3–5 (full-dim `p₀ = P/I_eq` over `O(Σ^r)`), step 6 (Fact B, `detΔ ∉ P`),
  step 7 (transport).

SEARCHED AND ABSENT (the trap we avoid):
- `repClosure(canonicalCoord '' productRankLocus) = canonicalCoord '' productRankLocusLE` (set closure
  / rank-raising) — NOT landed, NOT cheap; route 1's hidden premise. Avoided by the per-component
  containment.
- `vanishingIdeal(=r) = vanishingIdeal(≤r)` (ideal equality) — NOT landed; avoided.

---

## Decorrelated Codex (xhigh, default gpt-5.x) — independent read

Fired with the hypothesis WITHHELD (I gave F0–F5, the two routes A/B, the constraint "no density / no
ideal equality", and asked it to pick the ring + give the chain — I did NOT tell it my "keep O(Σ^r) via
the orbit route" verdict). Transcript: `codex/hsig-bridge-{prompt,answer}.md`. Codex independently:
- **chose `O(Σ^r)` [=r]** as the ring, NOT restating the wrapper — same verdict;
- reached the **same Spec relationship** (`I_le ⊆ I_eq ⟹ Spec(O_eq) ⊆ Spec(O_le)` closed inclusion; a
  prime of `O_le` descends iff it contains `I_eq` — "not automatic for arbitrary primes") — the exact
  load-bearing distinction;
- proved `I_eq ⊆ P` for the top prime `P` via a **local dense-open** argument (`D(detΔ) ∩ V(P) ⊆ Σ^r`,
  dense in irreducible `V(P)`, so functions vanishing on `Σ^r` vanish on `V(P)`), explicitly "not the
  forbidden global density theorem";
- gave the **identical 9-step chain** and named **step 6 (`I_eq ⊆ P`) as the one fragile must-build**.

**Convergence on every load-bearing point** (ring = `O(Σ^r)`; the no-drop applies once `P` is shown to
carry `I_eq`; no global density). **The one place I improve on Codex:** the `I_eq ⊆ P` containment is
cleaner via the LANDED corner-`r`-orbit-in-`Σ^r` + FREE `vanishingIdeal_repClosure` (steps 1–2 above)
than via Codex's point-set dense-open argument — same conclusion, smaller must-build, and it reuses
exactly the realizer-orbit object `ClosureBridge` already built for the codim-sandwich.

---

## Close

- **Firmest result (the verdict + certificate):** state `e` and the no-drop over **`O(Σ^r)` [=r]**; do
  NOT restate the wrapper. Discharge `hsig` via the LANDED `ringKrullDim_localizationAway_eq_of_avoids_
  top_prime` at the prime `p₀ = P/I_eq`, where `P` is the corner-`r` top minimal prime of `sigmaIdeal`
  (Fact A), `I_eq ⊆ P` is FREE (orbit-in-Σ^r + `vanishingIdeal_repClosure`), `p₀` is full-dim (catenary
  + `hClosure` dim-equality), and `detΔ ∉ p₀` (Fact B). NO ideal-equality trap, NO density theorem.
  Module estimate ≈ 2.5–3.
- **Most likely thing to break it:** **step 6 — Fact B (`detΔ ∉ P`)** — the only must-build with real
  mathematical content (H'-stability of the corner-`r` component + a permutation in `GL_{d_N}×GL_{d_0}`
  moving a nonzero r×r product-minor to the top-left). It is the pen-and-paper certificate from
  `nodrop-density-adjudication.md`, not yet Lean. Secondary risk: the quotient-of-quotient bookkeeping
  in step 5 (`DoubleQuot.quotQuotEquivQuotOfLE` for `I_eq ⊆ P`) if the height/coheight transport across
  the double quotient is fiddlier than expected (low risk — standard Mathlib).
- **Next construction/consult to settle the open part:** a focused SPECIFY/tide on **Fact B** — pin the
  exact Lean shape `ΔPdeep d r hp hq ∉ partitionIdeal d r m` for `m ∈ kostantPartitions d r` (corner-r),
  via H'-stability + permutation-moves-minor — and confirm the permutation-moves-minor step is the
  elementary `GL`-orbit move (it is: `mult_smul` + a permutation matrix). That single cert fixes the
  `hsig` cost at ≈2.5–3 modules and makes the whole `hsig` chain LANDED-bookkeeping-plus-one-real-lemma.
- **Coupling flag for #58 (the `e` tide):** target `dsig` = image of `ΔPdeep d r hp hq` under
  `Ideal.Quotient.mk I_eq` so the Fact-B avoidance transports to `dsig ∉ p₀`.
