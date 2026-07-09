# genm-seam — build spec: the §2 sub-generic SEAM CHART (the final #72 brick)

**Mandate (operator, 2026-07-09): build this to FINISH the expedition.** This is the sole remaining
brick between the (proven, clean-three) fully-general headline `aoyagi_learning_coefficient_gen` and
its *unconditional* form: it discharges `hRValue` (the general-L R1 reduced-core RLCT value) by closing
the sub-generic strata in `sjJointResolution`.

## The construction (review-agent analysis, controller-verified inventory — discuss-at-close #80)
An **Ext-free, no-Core, independence-preserving** chart. At a corank-`q` point of the product
rank-drop locus:
1. **(i) Block-normalize** via banked iterated pivot/corner elimination → `q` identity threads ⊕ the
   shifted configuration `(M₁−q, …, M_L−q)`.
2. **(ii) GAUGE-ABSORPTION LEMMA — the ONE genuinely new brick.** Every first-order deformation of the
   thread block + the thread↔C cross-blocks lies in the image of the linearized base-change action,
   leaving exactly the shifted-chain entries as normal directions. **Proof:** the cross-block equations
   `X_s·I − I·X_{s−1} = (given)` are triangular along the chain; solve FORWARD from the source for one
   triangle, BACKWARD from the sink for the other; never falls off an end because the thread spans the
   whole chain (this forward/backward solvability IS the concrete content of "`M_{0N}` is projective +
   injective" — but proved DIRECTLY, no Ext). **GENRE: identical to the banked `psiSplitRawGen`
   accumulator (`Ŵ_{s+1} = Ŵ_s·M_s·S̃_s`)** — see `DeepestPsiHcdGen.hcd_psiSplitRawGen` (:729) + the
   `Deepest*Gen` accumulator files (D1). This is a proof-shape we have shipped once.
3. **(iii) IFT:** the assembly map's derivative = `id ⊕ (the (ii) splitting)` at the base → local
   diffeo, Jacobian 1 at base. Use the banked IFT/diffeo triple machinery.
4. **(iv) Loss identification on the slice** via the banked LDU / readout identities.
5. **(v)** pivot-indexed finite chart cover of the stratum, a.e. (banked pattern).

## Why the zero-slack "wall" does NOT obstruct this (discuss-at-close #77/#80, §3)
`r1subgenwall`'s zero-slack proves SOFT bounds (domination/IH) fail as `c′→½·minAdm`. It says nothing
against this EXACT shifted-chart recursion — the chart is an identity + IFT, containing NO borderline
integral. For each FIXED `c′ < ½·minAdm` the stratum-aware accounting
(`M₀·s′ + minAdm(shifted) = minAdm(full)`) gives STRICT inequality through the shifted-chain IH once
the chart exists.

## The plug-in target (the honest size question — fail-fast on it)
The chart discharges the sub-generic obligation in `RouteMSJResolution.lean`:
- `sjBoundaryPeel` (piece 3, named sorry — cover+shear measure-plumbing), and
- pieces 4/5/7 (named sorry — the joint-resolution finiteness / `(S,J)` double-induction, residual =
  the `[E_J|D_J]` **carrier** invariant).
**The pivotal uncertainty:** the review says the seam chart PLUGS INTO the already-banked contract
(charge budget `minAdmRec`/`sjChargeUpdate_accum`/`sjSubordination` banked; `schurRecStep_p` clean-three
∀p∀corank) ⟹ ~one lemma. `addlongscope` (#77) warned the `[E_J|D_J]` carrier could be ~15–35 tides of
data-structure/invariant engineering. **BUILD ORDER + CHECKPOINT:** build the **(ii) gauge-absorption
lemma FIRST** (crux, `psiSplitRawGen`-genre), then determine + REPORT whether it plugs into the banked
recursion (one-lemma, review) or requires building the carrier (mountain, addlongscope). That report is
a spend-decision checkpoint — do NOT silently sink weeks into the carrier without flagging.

## Discipline
- **Independence:** Ext-free, NO `Core` import, no quiver/codim/C-2. Explicit coordinate CoV
  (`Jacobian.lean`) + monomial integrability (S2) only. Reuse D1's `psiSplitRawGen` shape.
- `scripts/lb` only; force-recompile; forced `#print axioms` (clean modulo the allowed S2 `monomial_rlct`)
  on each public result; no sorry-scaffold — if a rung hits a genuine ceiling, report the shrunk ladder.
- Checkpoint (commit+push a `genm-seam*` branch) at: the (ii) crux green, the plug-in determination, and
  strand-complete. Fire a decorrelated codex-consult on the (ii) soundness if it feels gnarly.
