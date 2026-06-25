# Thread 21 — `hdiv_achiever` (achiever-path box-integral divergence)

**Seat:** formaliser (tide). **Date:** 2026-06-24. **Branch:** `fm-r1-hdiv-achiever` (off
`expedition/aoyagi-full`, base `7482066c`; uncommitted — controller integrates).
**Target:** the R1.6 lower-bound atom `hdiv_achiever` (cert: thread 20, §"single most load-bearing
residual atom").

## Result

Module `lean/DLNFibre/DLN/RLCT/Validate/RouteMLayerCoverGE.lean` (green build; one honest `sorry`).

- **`layerCover_thresholdGe_half_minAdm`** (sorry-free) — every layer leaf threshold `≥ ½·minAdm M`.
- **`layerCover_exists_achiever`** (sorry-free) — the achiever leaf realises `= ½·minAdm M`.
- **`layerCover_exists_thresholdLe_iff_half_le`** (sorry-free) — `(∃ leaf ≤ c') ⟺ ½·minAdm M ≤ c'`.
- **`routeMCore_box_diverges_achiever`** (the ONE honest `sorry`, CORRECT statement) — the genuine
  flat-coordinate box divergence atom.
- **`layerCover_hdiv`** (sorry-free wiring) — discharges `routeMLayerCover_of_atoms`'s `hdiv` field
  from the atom + the premise reduction. Type-checked to plug in with no adaptation.

## Adjudication answers (to the controller)

1. **Does achiever-only suffice for the `hdiv` discharge?** YES. The cover's `hdiv` premise is
   `∃`-quantified over leaves; the achiever attains the minimum threshold, so any leaf below `c'`
   forces `½·minAdm M ≤ c'`, and divergence on the single achiever leaf discharges the field. The
   banked `routeM_coverGeDiv_of_boxDiverges` needs no more than one diverging leaf. The atom is
   unchanged from the cert.

2. **Is the atom provable from the banked machinery?** NO — it walls. This thread's validation +
   a decorrelated `local-codex-consult` (gpt-5.5, xhigh) both reached: the banked squeeze
   (`rlctAtOn_squeeze`, `schur_recursion_step_squeeze`) computes only the POINT RLCT, giving
   `rlctAtOn (routeMCore M) 0 ≤ ½·minAdm M`. That is STRICTLY WEAKER than the boundary box-divergence
   the atom demands: `rlctAtOn ≤ t` is an `sSup` bound constraining only `c' > t`, while the atom asks
   for divergence AT-AND-ABOVE `t` (`c' = ½·minAdm M`, sharp). Asserting `=⊤` from the point bound is
   the forbidden value-correct-germ-degenerate fill (Codex Q4 trap) — NOT done.

3. **The precise sub-blocker.** The general-`M` achiever **geometric chart / wedge**: a map
   `φ : box → flat` with a measure change-of-variables and a pullback UPPER bound
   `|routeMCore M ∘ φ| ≤ C · (achiever monomial)` on a positive-measure box, so the sharp monomial
   divergence `monomialIntegrand_lintegral_box_eq_top` transcribes to `F`. This does not exist: the
   `(2,2,2)` chart `phiUnit` is a depth-2 miracle (the Jacobian tower loses triangularity after the
   first pivot), and the layer atlas `routeLayerAtlas` is purely COMBINATORIAL exponent data (no
   chart map). This is the "squeeze-to-box-integral bridge" the `RouteMLayerCover` header names as the
   open lower-bound content.

4. **Axiom footprint.** Wiring lemmas: `[propext, Classical.choice, Quot.sound, monomial_rlct]` (the
   single authorized S2 citation, via the value lane). The atom: `[propext, sorryAx, Classical.choice,
   Quot.sound]` — one honest `sorry`, NO extra axiom, no `native_decide`, no `#exit`. `layerCover_hdiv`
   carries `sorryAx` + `monomial_rlct` (as expected, consuming the atom).

## Next construction (for the controller to scope)

Per Codex's tractability ranking, the most promising honest route to close the atom is an **achiever
WEDGE / tube** (Codex option (a)): a low-dim achiever curve `γ(t) → 0` with `F(γ(t)) ≲ t^{minAdm}`
and a tubular box where Fubini reduces to the divergent 1-D monomial test integral — load-bearing
sub-lemma: a measurable tube parametrisation with positive transverse measure + `F ≤ C·(critical
monomial)` on it. Heavier alternative (b): the full composed-blow-up achiever chart (one pivot per
achiever-path node, with Jacobian control). NOT route: `rlctAtOn ≤ t ⇒ atom` (too weak at boundary).

## Artefacts

- `statement-card.md` — the two cards (wiring sorry-free; atom honest-sorry) + the adjudication note.
- `codex/mechanism-{prompt,answer}.md` — the decorrelated consult (Q1–Q4).
- ANCHOR: `do not commit to expedition/aoyagi-full` (controller integrates); `DLNFibre.lean` untouched
  (single-writer aggregator — the controller wires the new module).
