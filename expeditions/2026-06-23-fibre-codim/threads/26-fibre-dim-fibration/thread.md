# thread 26 — H4: the fibre dimension via the fibration (the substantive remaining rung)

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(progress) → PROVE → AUDIT`. The crux
remaining rung of the HEIGHT-DIRECT route. The math is **certified** (thread 25); this is the AG-heavy
Lean assembly. **Operator discipline: break it into manageable pieces and work through them meditatively
holding the big picture — do NOT declare a wall; if a piece is hard, break it smaller.**

## The target
```
varietyDim (canonicalCoord d '' fibre d E) = card − C − δ          (H4, the substantive fact)
```
where `card = Fintype.card (RepCoord d) = Σ_i d_{i+1}·d_i`, `C = cCodim d r`, `δ = r(d_N+d_0−r)`,
`E = diag(I_r,0)` the rank-`r` normal form. Then **immediately** (the catenary closer is LANDED):
```
codimRepCanonical (fibre d E) = C + δ
```
via `Core.NullstellensatzCodim.codimRepCanonical_eq_card_sub_varietyDim` (`codimRepCanonical Z =
card − varietyDim Z`, `[IsAlgClosed k]`). That `codim(fibre over E) = C + δ` is the **headline** for this
tide. (Lifting to general rank-`r` `B` via G1 `FibreNormalForm` + discharging `BundleShiftInterface` is
the follow-on G4 tide — not this one.)

## The certified math (thread 25 — read `threads/25-jacobian-rank-cert/certificate.md` first)
The restricted multiplication `mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` is **dominant** (`Σ̄^r = {A : rank(mult A)
≤ r}` maps onto the rank-`≤r` target matrices); `E` is a **generic** (rank-exactly-`r`) point of
`Mat^{≤r}`. The **generic-fibre-dimension theorem** then gives
```
varietyDim(fibre over E) = varietyDim(Σ̄^r) − varietyDim(Mat^{≤r}) = (card − C) − δ.
```
`+C` = the `Σ̄^r` codim (Kostant/Ext, LANDED); `+δ` = the target rank-locus dim. **No flatness** (generic
flatness is free) — this sidesteps the thread-20 radicality/trivialization wall AND the per-component
Jacobian-rank bookkeeping. **Scope (load-bearing):** the fibre is REDUCIBLE; the equality is the
**top-component** dimension (lower-dim components carry higher rank). Hypothesis: `r ≤ min_i d_i`
(`E` realizable / dominance). Only generic behaviour on the top component is used.

## Engine handles (all LANDED — confirm signatures in SPECIFY)
- `Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim` — `codim Σ̄^r = C`; with the closer ⟹
  `varietyDim(Σ̄^r) = card − C`.
- `Core.DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum [IsAlgClosed k][CharZero k]` —
  `varietyDim(Mat^{≤r}) = r(n+m−r) = δ`.
- `Core.NullstellensatzCodim`: `varietyDim`, `codimRepCanonical_eq_card_sub_varietyDim`,
  `height_vanishingIdeal_add_varietyDim_eq_card`, `codimRep_add_varietyDim_eq_card`.
- `Core.AffineNoetherRank`: `ringKrullDim_quotient_unbotD_eq_trdeg_toNat`, `trdeg_eq_of_integral_injective`
  (`ringKrullDim = trdeg`).
- `Core.AffineDomainDimension`: `affine_domain_height_add_ringKrullDim_quotient_eq` (equidim
  `height p + ringKrullDim(A/p) = ringKrullDim A`), `height_eq_ringKrullDim_of_isMaximal`.
- `Core.MultComorphism` (`multComap`/`multPoly`/`fibre`), `Core.FibreNormalForm` (the normal form `E`),
  `Core.DeterminantalStratumDim` (`Mat^{≤r}` = `productRankLocusLE ![n,m] r`).

## The substantive piece (the generic-fibre-dimension, via trdeg)
The dominant morphism gives a `k`-algebra map `O(Mat^{≤r}) →ₐ[k] O(top component of Σ̄^r)` (via
`multComap` / the coordinate ring of `mult`), injective (dominant) into the domain `O(top comp)`. Then
`ringKrullDim O(top comp) = ringKrullDim O(Mat^{≤r}) + trdeg_{Frac}(...)` and the generic fibre dim =
trdeg (`AffineNoetherRank`). Assemble: `varietyDim(fibre over E) = varietyDim(Σ̄^r) − varietyDim(Mat^{≤r})`.
Identify/handle the top component via Brick A (`Core.SigmaComponents.minimalPrimes_sigmaIdeal_eq`). **Break
this into sub-pieces** (the dominant ring map; the trdeg/dimension-additivity; the generic point `E`; the
reducibility/top-component) — bank each as a seam.

## SPECIFY-first — progress checkpoint (NOT a fork)
1. SPECIFY: pin the engine signatures above; decide the cleanest Lean realization of the generic-fibre-dim
   (trdeg-additivity on the top component vs a direct `varietyDim` subtraction); pre-stage uncertain API
   with `example`. **Fire your own `local-codex-consult` (xhigh)** on the Lean realization of the
   generic-fibre-dim for `mult|_{Σ̄^r} ↠ Mat^{≤r}` via the trdeg toolkit; save under `threads/26-.../codex/`.
2. **CHECKPOINT — message `main`** with the decomposition + which engine pieces assemble + reachability +
   your first seam. This is a PROGRESS report so I can steer; **keep building** unless you hit a genuine
   Mathlib-absence — if you do, break THAT into a sub-build (the engine has the trdeg/dimension toolkit),
   do not declare a wall or fork.
3. PROVE (bank seams) → AUDIT.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` EXPLICITLY every shell
call; `scripts/lb` only; `source ~/.elan/env`. Zero sorry/axiom/native_decide/#exit. `↦`; `decide
+kernel`; name = content (prefix new witness/scratch defs with the module name, e.g. `fibreDim…`, to dodge
aggregation collisions). **Core only — never import `DLNFibre.DLN`.** NEVER `git add -A`; commit seams;
**commit finished work BEFORE going idle.** Don't edit the aggregator — REPORT the import line. **You are
the SOLE write-tide on `expedition/fibre-codimension`.** Write any doc/cert/card to the WORKTREE path
(`…/.claude/worktrees/fibre-codim/expeditions/…`), NOT the bare repo path.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`; non-vacuity witness (the `(2,2,2), r=1` fibre: `varietyDim = 8−1−3 = 4`, `codim = 4`).
Report: theorem names + signatures; green/sorries/axioms; module path + aggregator import line; the exact
state of `codimRepCanonical(fibre d E) = C + δ` (landed? or the residual sub-piece); handoff to G4.

## Scope
**H4 + the immediate codim closer** (`varietyDim(fibre E) = card−C−δ` ⟹ `codimRepCanonical(fibre E) = C+δ`).
G1-lift to general `B` + G4 discharge of `BundleShiftInterface` = the follow-on tide. **No
`BundleShiftInterface` discharge here.**
