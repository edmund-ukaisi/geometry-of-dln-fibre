# genm-sjpure — statement / scope card (R1-UPPER pure R-BLOWUP recursion)

**Thread `genm-sjpure`** (branch `genm-sjpure` off `expedition/aoyagi-full @4faa82fa`, isolated worktree).
Mission: build the R1-UPPER (S,J) recursion via the PURE R-BLOWUP route → `RouteMBoxThresholdFinite M` (∀L)
→ close `sjJointResolution` (`RouteMSJResolution.lean:803`). No Lean edits landed this tide — the honest
finding is a **scope recalibration** (below), decorrelated-Codex-confirmed, banked as STEP-0 + the consult.

## STEP-0 — VERDICT: PASS (`step0.md`)

Re-ran r1flip's exact-algebra probes (`flip2`, `flip3`, sympy 1.14) on the corank-2 product anchor
`(3,3,3,4) t=(1,0,0)`. The PURE peel (coordinate radial `‖(u•Δ)·Q‖² = u²‖Δ·Q‖²` + det-1 unit Schur-clear
`L·Dp·R = diag(1, δ')`, `det L = det R = 1` + descend) reaches the monomial normal-crossing endpoint
end-to-end with COORDINATE centers only; `det(Qb Qbᵀ)` never forms; front-first shared radial factors from
both coupled terms; branch exponents sum to `Mval = 7 = minAdm(3,3,3,4)`, threshold `7/2`. **The pure route
does NOT secretly need the Gram det** — the false wall stays removed. Build is NOT blocked by a missing
theorem.

## The recalibration — the pure-route CARRIER is ALREADY BANKED; the sole gap is one measure-CoV brick

Contrary to the mission's "build the pure `ChainDecoration` carrier" framing, r1carrier's Deliverable A
carrier re-scope is **already banked** in `RouteMSJDecorated.lean` — and it is already the pure route (not
the atom route):

| pure-peel step (r1flip) | banked object |
|---|---|
| carrier indexed by the (remaining) chain, threshold `½·minAdm` **descendable** | `SJDecoration {L} (M : Fin (L+1)→ℕ)` + `DecoratedBoxThresholdFinite (D : SJDecoration M)` (threshold `carrierThreshold M = ½·minAdm M` reads the decoration's OWN chain — r1carrier's "cannot descend" concern is addressed) |
| (a) det-1 unit Schur clear | `RouteMSJDecoratedRowMix` (`rowMix`, constant support) |
| (b) coordinate radial `u₀` (fully shared) | `SJDecoration.radialAttach` + `radialAttach_decLoss` (`u₀²` factor) |
| the pointwise per-step identity (Gram-det never forms) | `RouteMSJCorankStep.corankStep` / `corankStep_prefactor` |
| charge accounting / threshold shift | `minAdm_le_peelCharge_add_redChain`, `carrierThreshold_shift` (both `0/171`) |
| the monomial terminal + shared-divisor ledger | `sjLoss_terminal_lintegral_lt_top`, `iInf_axisRatio_le_monomialThreshold`, the `SJSupport` `min_i` ledger |
| π=∅ recovery → `RouteMBoxThresholdFinite M` | `decoratedBoxThresholdFinite_trivial_iff` (sorry-free) |
| the two isotropic block regimes | `matBox_corank_dominates_absZ_lt_top` (`c'<pq/2`, terminal), `matBox_corank_residual_absZ_le` (`c'>pq/2`, shift) |

A NEW `ChainDecoration` module would DUPLICATE `SJDecoration` (which is already chain-generic) and risk name
clashes — no value. The sole unbanked piece is the assembler:

**`decorated_peel_step`** (named, unbuilt in `RouteMSJDecorated` header): the measure-theoretic change of
variables that composes {radial attach (b) + unit Schur clear (a) + `corankStep` + descend} into a SOUND
peel `DecoratedBoxThresholdFinite (peeled D) → DecoratedBoxThresholdFinite D`, producing the exponent shift
`c' ↦ c' − ½·pq` and descending to `redChain u M`. This is exactly the analytic content of the
`sjJointResolution` sorry — the two are the same brick in two dresses.

## The precise remaining sub-brick (decorrelated Codex xhigh, `codex/scope-answer.md`)

**VERDICT: multi-tide new construction (BOUNDED but substantial), NOT a one-tide composition of the banked
pieces.** Load-bearing reason (Codex, independent of my leaning): the banked isotropic peels handle a block
entering via its OWN energy `frobSq Δ`; the chart loss has the corank block as `frobSq(C·Q̃ + Γ·Q_b)` —
ANISOTROPIC (`Γ` coupled to `Q_b`) with an additive cross term `C·Q̃`. Removing the anisotropy + cross term
is NOT a measure-preserving consequence of `corankStep`; it needs either the Gram CoV (the false wall) or the
pure blow-up Jacobian, which is unbanked.

**Central unbanked sub-brick:** a chartwise coordinate blow-up CoV `Γ = u•Γ'`, Jacobian `|u|^{pq−1}`,
compatible with the Schur-cleared loss, descending the integral to `redChain t M` at exponent `c' − pq/2`;
plus the pivot/corank double-recursion interleaving (Aoyagi's (S,J)). Mathlib has the primitive
(`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`, the sphere-product polar decomposition
with `r^{n−1}` density), so this is BOUNDED, not research-grade. Two caveats make it multi-tide:
- the anisotropic block integral `∫_{Δ} ‖Δ·Q_b‖^{−2c'}` **diverges on the rank-deficient-`Q_b` locus**
  (`RouteMSJCorankResidual` finding, `genm-sjpeel-blow`), so there is NO clean standalone finiteness atom —
  the pivot resolution and the corank blow-up must be INTERLEAVED (peel `Q_b`'s own layers when it is rank
  deficient); the recursion is irreducible to a single lemma;
- the CoV must track the shared-divisor `diag(b)` ledger generator-by-generator (`frobSq`-level `corankStep`
  is too coarse — `RouteMSJLedger` header), so the blow-up chart bookkeeping is the bulk of the labour.

## Recommendation (KNOWING decision to surface)

The mission's "one-tide bounded build" is refined to **"multi-tide bounded build; carrier + pointwise + terminal
already banked; the sole remaining brick is `decorated_peel_step` (the anisotropic corank blow-up CoV +
(S,J) interleaving)."** Two honest options for the operator:
- **BUILD** — a dedicated multi-tide sub-expedition on `decorated_peel_step` alone (the sphere-product CoV on
  the flattened block via `measurePreserving_homeomorphUnitSphereProd`, then the interleaved pivot/corank
  descent + the `diag(b)` ledger). No missing theorem; substantial Lean measure-theory labour.
- **CITE** — the existing `RlctInterface.cited_aoyagi_dln` (`rlct = ½·codim`) already supplies the value;
  **footprint-neutral** (no new interface/axiom; there is NO determinantal-principalisation theorem to cite —
  that was the atom-route false wall). Scope the library to the banked bricks.

**Do NOT launder** `sjJointResolution` into an equivalent `decorated_peel_step` sorry (they are the same
brick) — left UNTOUCHED this tide. **Do NOT** build a duplicative `ChainDecoration` module. **Do NOT** form
the Gram determinant / integrate `Γ` out mid-way (the atom-route false wall).

## Ledger

- Files: `step0.md`, `codex/scope-{prompt,answer}.md`, this card. No Lean edits (build baseline intact, 20
  named sorries incl. `sjJointResolution:803`; my mission target).
- Build status: untouched (`@4faa82fa`); no new sorries/axioms introduced.
- Blocker: `decorated_peel_step` = multi-tide anisotropic-corank blow-up CoV (BOUNDED, Codex-confirmed).
