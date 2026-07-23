# REBAKE2 turn-key spec — the R4 wiring / bridge / StepInv re-thread (arch-C-3)

> **STATUS GATE (read first): DO NOT EXECUTE (a)–(d) YET.** The bridge these steps bake
> (`uncleared ∈ ⟨cleared⟩`) is **Gröbner-FALSE** on the E_J / pivot-column residual entries in the
> naive model (seat-L4D `r4clear_bridge_soundness.py`, f392084fd), and seat-L4D confirms **branch-(ii)
> does NOT rescue it** — both signs (`±γ`) and the `b`-weighted variant still fail
> (`r4clear_bridge_with_branchii.py`, cda8f431e). The suspect therefore **leans §7**: the pure-pivot-cross-zero
> `r4Clear` appears to break the StepInv ideal on the pivot column (E_J), and the *sound* R4 would need the
> **Q₂⁻¹ neighbour-absorption** (redistribute the `β,γ` cross entries onto their neighbours rather than
> zero them) — which touches the fold order (`stepMap`/`foldG`) = the **§7 tripwire**. **pnp is running the
> faithful full-structure decider** (real `foldB` + exact composition + wide witness + residual-vs-ledger
> for col-0); **the elder rules on it.** This spec executes AS-IS only if that decider says branch-(ii)
> ABSORBS the remainder on the exact composition; if it SURVIVES, the spec is **re-ruled** (R4 mechanism
> changes to Q₂⁻¹-absorption) before anyone executes it. Task #54 tracks the decider.

## What is already landed (green, on REBAKE2, committed + pushed)

`MonumentAtlas.lean`, census delta 0 (no new sorries), `Case1Wire` builds green (8450 jobs):

- **DEF-EDIT-1** — `supportAt` descended branch `blockCoords d (S+1)` → `layerCoords d (S+1)`; `blockCoords`
  + `supportAt` docstrings corrected (center-cap vs descended-residual). `J=0` + `blockCoords` unchanged.
  Clean `Deg1SupportedSlot` kept (no `BChainFactoredSlot`/`flatColOf`/field — retracted field ABSENT).
- **DEF-EDIT-3(b)** — `canonNormalizationOf` branch-(ii) negated (`−γ`, `A_{S+1}·Q₁`, worked.tex:445) +
  scoped (`i < s.cleared → 0`, i.e. `i ≥ cleared`, §8(m)); docstring updated.
- **`r4Clear` def** (DEF-EDIT-3(a), STAGED, unused) — the pivot-cross clearing, case12/case2-conditioned;
  matches pnp's validated `r3r4_recoord_scope.py`. **Its soundness as the R4 mechanism is the open gate.**

The **decomposition** (verbatim, elder-accepted): `canonNormalizationOf` keeps BOTH det-1 branches —
branch-(i) interior Schur reads the pivot row/col to shift the interior (unipotent), branch-(ii) recoord
reads off-target coords (unipotent); ONLY the pivot-cross CLEAR reads its own coordinate, so it is R4, a
generator-level residual-READ normalization, never in `blockShear` (`foldG`/`hshear` untouched).

## (a) `foldResid` read-argument wiring (both branches) — mechanical; extend equations re-prove by `rfl`

In `MonumentAtlas.foldResid`'s `.step` non-terminal body (currently ~:450-457):
- **δ=1** read arg: `fun k => blockBlowupCoordQuot pivot k (fun k' => r4Clear d p.conState cse pivot k' (edgeShearRaw d cse shearφ u))`
- **δ=0** read arg: `blockBlowupMap center pivot (fun k' => r4Clear d p.conState cse pivot k' (edgeShearRaw d cse shearφ u))`
  (i.e. `stepMapRaw = blockBlowupMap ∘ edgeShearRaw`, with `r4Clear` inserted between; order shear → R4 → blow-up).

Then re-state, in `Case1Wire`:
- `foldResid_extend_delta1` (~:89-97): RHS gains `fun k' => r4Clear d p.conState ed.case ed.pivot k' (edgeShear d ed u)` inside the `blockBlowupCoordQuot`. Proof `rw [foldResid, dif_neg hlt, if_pos hδ]; rfl` — **re-proves by `rfl` (confirmed).**
- `foldResid_extend_delta0` (~:100-107): RHS becomes `blockBlowupMap ed.center ed.pivot (fun k' => r4Clear d p.conState ed.case ed.pivot k' (edgeShear d ed u))` (no longer `stepMap d ed u`). Proof same shape — **re-proves by `rfl` (confirmed).**

Ground-truthed: wiring + these two re-statements build; the ONLY breakage is the two StepInv helpers below.
`foldG`/`foldB`/`stepMap`/`hshear` are UNTOUCHED (the Jacobian is not perturbed — `r4Clear` is read-side only).

## (b) Commutation lemma — provable (clean)

`r4Clear` commutes with BOTH blow-ups: `blockBlowup(r4Clear v) = r4Clear(blockBlowup v)`. Proof by `funext k`,
casing `k = pivot` (excluded from the cross ⟹ untouched by `r4Clear`, set to `1`/`v_pivot` by the blow-up on
both sides) / `k ∈` pivot-cross (`r4Clear` → 0; blow-up of 0 is 0 for a center coord `u_pivot·0`, 0 for a
spectator) / else (both identity). Holds for `blockBlowupMap` and `blockBlowupCoordQuot`. Consequence: the
child reads `r4Clear` applied to the OLD child point (`qm` at δ=1, `stepMap u` at δ=0), so ONE generic bridge
on a coordinate vector `W` serves both consumers.

## (c) The M-bridge — the +1 named frontier (IF sound) — `foldResid_r4Clear_regionRepresents`

**Shape (seat-L4D): a `RegionRepresents` relation, NOT an equality** (`Core.Aoyagi.IdealInvariance` :84 API):
```
RegionRepresents (fun j ↦ foldResid_p j ∘ M) (fun j ↦ foldResid_p j ∘ (r4Clear ∘ M)) V
```
parametrized by the read-arg map `M` (δ=0 instantiates `M := stepMap`; δ=1 `M := blockBlowupCoordQuot ∘ edgeShear`).
Direction: **uncleared ∈ ⟨cleared⟩** (each uncleared entry is a continuous-cofactor combination of the cleared
entries), so the parent StepInv's membership transfers to the cleared child via `RegionRepresents.trans`.
Consumes the parent `Deg1SupportedOn (foldResid d e p) ed.center` — the SAME hypothesis as
`foldResid_stepMap_eq_pivot_mul` (Case1Wire:36).

**NOT an equality — the refinement + its reason:** `foldResid_p` genuinely *changes* under `r4Clear`, because
the **pivot-COLUMN part of the cross lies IN `ed.center`** (`c = b < widthMinUpto`), so zeroing it drops
center-supported terms. Hence the relation is the module/ideal `RegionRepresents`, not `foldResid_p ∘ M =
foldResid_p ∘ (r4Clear ∘ M)`. My earlier "M = Q₁/Q₂ inverse (matrix)" premise is WRONG — pure-zero `r4Clear`
is not invertible (it drops `β,γ`), so there is no matrix inverse; the cofactors come from Aoyagi's Lemma-2
generator inverse `Q₁⁻¹·diag(1,e₂)·Q₂⁻¹`, riding G1.

**4-check (elder delta-read):** (a) states the ideal-faithfulness = Lemma 2; (b) rides G1 (`g1_unimodularity`)
+ Lemma 1 (`RegionRepresents` ideal-transfer); (c) generic over `M` ⟹ both consumers, weakest form; (d) matches
pnp's `r4Clear` model exactly.

**Derivability SPLIT (seat-L4D):** PLUMBING = `RegionRepresents.trans` threading (`.refl`/`.trans`/`.mono`/`.of_eqOn`
banked in IdealInvariance) is DERIVABLE ⟹ PROVE. CORE = the specific `RegionRepresents uncleared cleared` needs
the R4 cofactor matrix (`g1_unimodularity` is sympy-only, NOT a Lean lemma) ⟹ genuinely-open, the +1 frontier.
Discriminator to re-check when rendering: **grep `IdealInvariance` for a unimodular→`RegionRepresents` constructor**;
if one is banked (beyond refl/trans/mono/of_eqOn, which compose but don't create), the core flips to PROVE (census 0).

> **BUT (the gate):** the CORE membership is currently Gröbner-FALSE on E_J col-0 in the naive+branch-ii models.
> This bridge is only bakeable (even as a sorried frontier) if pnp's faithful decider clears the E_J membership
> on the EXACT composition. If it does not, the mechanism is wrong (see §7 note) — re-rule before baking.

## (d) StepInv re-thread — the witness rewrite (PROVE, plumbing, IF the bridge holds)

`stepInv_child_delta0` (Case1Wire ~:138-173) and `stepInv_child_delta1_append` (~:332-372) change their witness
from `q'ᵢⱼ' = qᵢⱼ'(stepMap u)` to `q'ᵢⱼ'' = ∑ⱼ' qᵢⱼ'(stepMap u) · Mⱼ'ⱼ''` (compose the parent `q` with the
bridge's cofactor `M` via `RegionRepresents.trans` + a `Finset.sum` swap). The rest of each proof (continuity of
`q'`, the `hq0`/origin leg) carries. This is mechanical GIVEN a sound bridge.

## Honest framing (REQUIRED at the claim site, charter §3)

`stepInv_child_delta0` and `stepInv_child_delta1_append` were **proofs about the WRONG (un-cleared) object**
under the broken def; the faithful (R4-cleared) def **re-opens them honestly**, conditional on the one
`foldResid_r4Clear_regionRepresents` bridge. That is the fidelity fix's true price surfacing in Lean terms —
not a census line, a stated re-opening.

## Verbatim battery formulas (for pnp; already in the render report)

- branch-(i): `-(readEntry s.layer (q.1.2) (qp.2)) * readEntry s.layer (qp.1.2) (q.2)` [guard: layer=s.layer ∧ q.1.2≠a ∧ q.2≠b ∧ cleared≤q.1.2 ∧ cleared≤q.2].
- branch-(ii): `-(∑ i ∈ range(d q.1.1.castSucc), if i=q.2 ∨ i<s.cleared then 0 else readEntry s.layer i (qp.2) * readEntry (s.layer+1) (q.1.2) i)` [guard: layer=s.layer+1 ∧ q.2=a].
- `r4Clear`: `match cse | case12|case2 => if layer=s.layer ∧ cleared≤q.1.2 ∧ cleared≤q.2 ∧ ((q.1.2=a∧q.2≠b)∨(q.1.2≠a∧q.2=b)) then 0 else w k | _ => w k`.

## If §7 fires (branch-ii does NOT absorb — the current lean)

The sound R4 is NOT pure-pivot-cross-zero. It is Aoyagi's Lemma-2 `Q₂` acting as a **neighbour-absorption**:
the cross entries `β,γ` are redistributed onto the remaining block (the `A₂/A₃ ↦ F₂/F₃` re-coordinatization,
`F₂ = −A₁⁻¹A₂ = −A₂` at the normalized pivot), NOT zeroed. Zeroing changes the ideal (the Gröbner failure);
absorbing PRESERVES it. The elder leans **CONTAINED** (same class as the recoord itself — a bounded det-±1
coordinate map — so likely a recoord-branch refinement, not a fold redesign; seat-L4D's def-feasibility read
confirms). In that case `r4Clear` (as committed, staged) is a placeholder to be replaced by an `r4Absorb`
form (or the recoord branch extended), DEF-EDIT-3(a) is re-ruled, and (a)–(d) are revised before execution.

**The cheerful sub-case (seat-L4D def-feasibility lean, forward pointer):** under F₂-absorption the M-bridge
(c) likely **DISSOLVES** rather than needing a frontier. Because absorption is an INVERTIBLE (det-1)
re-parametrization with neighbour-compensation, it PRESERVES the product, so the StepInv close becomes an
**EQUALITY** via the det-1 recoord (`child = parent ∘ σ`, exactly the pre-R4 shape) — NOT an
ideal-`RegionRepresents`-membership. So the +1 core would close at **census 0** by the residual reading
through the det-1 recoord (no unimodular→`RegionRepresents` constructor needed on that path — consistent with
the grep, which found none: none is needed). Confirmed only if pnp says SURVIVES; then the full (a)–(d) +
seat-L4D's Gröbner verification land against the F₂ form.
