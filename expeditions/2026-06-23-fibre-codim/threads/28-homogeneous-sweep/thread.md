# thread 28 — route c: the equivariant homogeneous SWEEP (closes `codim(fibre) = C+δ`)

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(progress) → PROVE → AUDIT`. The clean
route to the fibre-codimension headline, certified by thread 27 (pen-and-paper, 2 decorrelated Codices,
9-case exact validation). It proves **BOTH directions at once** via an orbit-dimension count — NO
Jacobians, NO generic smoothness, NO flatness, NO component classification. Route B (Jacobian rank) is
**certified CIRCULAR** (thread 27 §1) — do NOT build it.

**Read first:** `threads/27-jacobian-rank-general/certificate.md` (§2 the argument, §4 the
formaliser-facing lemma, §6 kill-conditions). Then `synthesis.md` §"H3 CERTIFICATE…" / the route-c entry.

## The target (cert §4)
```
-- Step B (the ONE new rung — the homogeneous-sweep dimension identity):
theorem varietyDim_productRankLocusEQ_eq_delta_add_fibre [IsAlgClosed k] [CharZero k]
    (d) (r) (hN : (0:Fin (N+1)) ≠ Fin.last N) (hr : r ≤ ⨅ i, d i) :
  varietyDim (Σ^r d r)  =  r*(d (last) + d 0 − r)  +  varietyDim (fibre d (E d r))
-- Step C (closure/density, CITED LR 4.4/4.5 — try to PROVE it cheaply, else name it):
  varietyDim (Σ^r d r) = varietyDim (Σ̄^r d r)
-- Step D (assembly, LANDED bricks):  varietyDim (Σ̄^r) = card − C  (SigmaCodim)  ⟹
  codimRepCanonical (fibre d (E d r)) = cCodim d r + r*(d (last) + d 0 − r)
-- then G1 lifts to every rank-r B:  codimRepCanonical_fibre_eq_of_rank_eq.
```
`Σ^r = mult⁻¹(Mat^{=r})` (exact rank `r`), `Σ̄^r = productRankLocusLE d r` (rank `≤ r`),
`F = fibre d E`, `δ = r(d_N+d_0−r) = dim Mat^{=r}`, `C = cCodim d r`.

## The argument (cert §2)
`H = GL_{d_N}×GL_{d_0}` acts through the end vertices (`BaseChange.baseChange`, inner units `=1`); `mult`
is `H`-equivariant (`FibreNormalForm.mult_smul`). `Mat^{=r} = H·E` is a single orbit
(`exists_baseChange_of_rank_eq`), so `Σ^r = H·F`. The action map `α : H×F → Σ^r` has `Stab_H(E)`-coset
fibres ⟹ `dim Σ^r = dim H + dim F − dim K = δ + dim F` (the homogeneity gives uniform fibres — NO
flatness needed; `dim H − dim K = dim(H·E) = δ`). Step C transfers to the closure `Σ̄^r`; Step D plugs
the landed `dim Σ̄^r = card − C`.

## Engine handles (LANDED — confirm signatures in SPECIFY)
- `Core.FibreNormalForm`: `mult_smul` (H-equivariance), `exists_baseChange_of_rank_eq` (`Mat^{=r}` one
  orbit), `codimRepCanonical_fibre_eq_of_rank_eq` (G1 lift).
- `Core.DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum` — `dim Mat^{≤r} = δ` (Step A).
- `Core.OrbitImageDim` (`varietyDim_eq_ringKrullDim_range_orbitPullback`), `Core.JacobianTrdeg`,
  `Core.OrbitVariety`/`OrbitPullbackDim` — the orbit-dimension substrate for Step B.
- `Core.SigmaCodim` (`dim Σ̄^r = card − C`), `Core.NullstellensatzCodim` (`varietyDim`, the catenary
  closer `codimRepCanonical_eq_card_sub_varietyDim`, `height_add_…`), `Core.BaseChange` (the H-action).

## SPECIFY-first — progress checkpoint
1. SPECIFY: pin how the orbit-dimension machinery realizes **Step B** (`dim Σ^r = δ + dim F` — the
   action map `α`'s coset fibres / the orbit-stabilizer dimension count; reuse `OrbitImageDim`'s
   `varietyDim = ringKrullDim(orbitPullback.range) = trdeg` pattern). **Probe Step C cheapness** — is
   `varietyDim Σ^r = varietyDim Σ̄^r` free/cheap given `varietyDim` IS closure-dimension (`Σ̄^r =
   closure Σ^r`)? If cheap, PROVE it (no Cite); if not, carry it as a single explicit named hypothesis
   `hClosure` (the ONE Cited bridge, LR 4.4/4.5). Pre-stage with `example`. **Fire your own xhigh
   `local-codex-consult`** on the Lean realization of Step B (the orbit-dim sweep); save under
   `threads/28-homogeneous-sweep/codex/`.
2. **CHECKPOINT — message `main`** with the Step-B decomposition + the Step-C verdict (cheap-proof vs
   named-Cite) + reachability + your first seam. A PROGRESS report, not a fork — keep building unless a
   sub-piece needs a genuine Mathlib/engine sub-build (then break it smaller, don't wall).
3. PROVE (bank seams: Step A, Step B sub-pieces, Step C, the assembly + G1 lift) → AUDIT.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` EVERY shell call;
`scripts/lb` only; `source ~/.elan/env`. Zero sorry/axiom/native_decide/#exit. `↦`; `decide +kernel`;
name = content (module-prefix new witness/scratch defs — lesson J). **Core only — never import
`DLNFibre.DLN`.** NEVER `git add -A`; commit seams; **commit finished work BEFORE going idle.** Don't
edit the aggregator — REPORT the import line. Write any doc to the WORKTREE path
(`…/.claude/worktrees/fibre-codim/expeditions/…`), not the bare repo path. **Sole write-tide on the
branch.** The H4 tide's banked bricks (`FibreDimFibration` base-δ + equidim, `SigmaCodim`, etc.) are your
substrate — reuse, don't rebuild.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` axiom-clean; non-vacuity at
`(2,2,2),r=1` (`δ=3`, `dim F=4`, `codim=4`) and ideally `(3,3,3),r=1` (`δ=5`, `dim F=10`, `codim=8`).
Report: theorem names + signatures; green/sorries/axioms; module path + aggregator import line; whether
Step C is **proved** or carried as the named Cited hypothesis `hClosure`; the exact state of
`codimRepCanonical(fibre d B) = C+δ`; and the handoff to G4 (the DLN `BundleShiftInterface` discharge).

## Scope
**Route c: Steps A–D + the G1 lift ⟹ `codimRepCanonical(fibre d B) = cCodim d r + r(d_N+d_0−r)` for all
rank-r B (Core).** This SUBSUMES the easy direction (proves `=`). **NOT** the DLN `BundleShiftInterface`
discharge (G4) — that's the final tide (touches `DLN.RlctPayoffGeneral`, gets the full reviewer + Codex
soundness gate). **Honesty:** if Step C stays Cited, the headline is `codim = C+δ` modulo the named
density `dim Σ^r = dim Σ̄^r` — state that explicitly; no unconditional claim beyond what's proved.
