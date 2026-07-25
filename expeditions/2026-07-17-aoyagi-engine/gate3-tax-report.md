# Gate-3 tax report — the corank-2 TWO-SIDED `hideal` (does `hideal_bwd` close cheaply?)

**Branch:** `expedition/aoyagi-engine-gate2` (off `-PROTO` @ `05c35eb8a`); uncommitted (role boundary —
the controller integrates).
**Modules (all sorry-free; `#print axioms` force-elaborated, oleans deleted + rebuilt = `[propext,
Classical.choice, Quot.sound]`):**
- `…/Core/Aoyagi/Corank2HidealProto.lean` (115 LoC) — **L-A** the block-elim atom (genuinely coupled `Δ`),
  both directions, at the real ambient (gate-2, reused).
- `…/Core/Aoyagi/Corank2MaintenanceProto.lean` (155 LoC) — **L-B** the `(S,J)` maintenance row-clear
  through the NON-UNIT `diag(b')`, both directions, reverse cofactor `cᵢ·rᵢ` (`rᵢ = b'ᵢ/b'_p`, the b-chain
  quotient). **The exact claim the gate flags** ("the b-chain absorbs the reverse general").
- `…/Core/Aoyagi/Corank2TerminalProto.lean` (136 LoC) — **L-C** the terminal monomialisation, both
  directions, reverse via the PROVEN Core theorem `terminal_bezout` (cofactor `1/unit`).

These are the three ideal-identity MECHANISMS of the L-A/L-B/L-C recursion, each demonstrated TWO-SIDED
with continuous reverse cofactors on genuinely coupled / general structure.
**Decorrelation:** sympy entry-level check + Codex xhigh red-team (in `gate3-codex/`).

**VERDICT: GREEN on the gate's KEY measurement — `hideal_bwd` closes CHEAPLY at coupled corank-2, at
every mechanism of the recursion. The render's "the b-chain absorbs the reverse general" is CONFIRMED, not
a 7th over-claim.** One honest scope caveat (§4): the three mechanisms are proven two-sided; composing them
into a single LITERAL `(3,3,4)` 21-variable chart (`⟨coreGen∘g⟩ = ⟨monomialFam bexp⟩` for the explicit
composite `g`) is the #112 build (Codex's flagged biggest risk — engineering, not a wall).

---

## 1. THE KEY MEASUREMENT — the reverse is cheap at all three mechanisms; coupling never obstructs it

The gate's RED condition was: `hideal_bwd` walls ⟹ "the b-chain absorbs the reverse" is an over-claim ⟹
objects-only cite. The reverse closes CHEAPLY at each mechanism, with the coupling isolated to a factor
that never enters the reverse cofactor's continuity:

- **L-A (block-elim, `Corank2HidealProto`).** Reverse `⟨peeled⟩ ⊆ ⟨(∏C)⟩` — cofactors the polynomial
  entries of `Q₁` (unimodular). Coupling is carried in `Δ`; `Q₁` is unipotent-polynomial regardless.
- **L-B (maintenance, `Corank2MaintenanceProto` — the flagged claim).** The `(S,J)` step row-clears the
  unit pivot through the non-unit left factor `diag(b')`. `maintenance_step_two_sided`: both inclusions
  hold with cofactors `±cᵢ·rᵢ`, where `rᵢ = b'ᵢ/b'_p`. The REVERSE cofactor is `cᵢ·rᵢ`, CONTINUOUS
  **iff `rᵢ` is** — i.e. iff the b-chain `b'_p ∣ b'ᵢ` holds (making `rᵢ` a genuine monomial). The coupling
  is the arbitrary `cᵢ` (`hc` places no structure on it); it does NOT obstruct the reverse. **This is the
  precise content of the render's claim, and it is TRUE:** the b-chain is exactly the hypothesis that
  makes the reverse continuous, and it holds by construction (`b'ᵢ = (∏u)·b'_p`). Were the chain to fail,
  `rᵢ = b'ᵢ/b'_p` would be `1/(monomial)`, discontinuous on the coordinate hyperplane — the wall. The
  chain is load-bearing and present; no wall.
- **L-C (terminal, `Corank2TerminalProto`).** Reverse `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩` via `terminal_bezout`
  (proven): the dominant monomial `b₁` is recovered from the cleared-pivot entry `b₁·unit`, cofactor
  `1/unit` (continuous by `ContinuousOn.inv₀`). Even simpler than L-B: the terminal reverse is `1/unit`,
  independent of the coupling (which lives in the dominated `b₂,b₃ ∈ ⟨b₁⟩`).

Codex (decorrelated, xhigh): "the inverse/Bézout construction itself is not the wall." Sympy: the pivot
entry factors as `E·unit`, `unit(0)≠0`, so `1/unit` is continuous near `0`.

## 2. Did Mathlib fight? — NO

- L-C: `terminal_bezout` + `principalInv_regionRepresents` are proven Core theorems; a one-line
  application. `blockBlowupMap` banked. No ideal-membership / measure / cast machinery.
- L-B: the two-sided `RegionRepresents` reduces to two delta-sum lemmas (`delta_one_sum`,
  `delta_scaled_sum` via `Finset.sum_ite_eq'`) + `by_cases i=p` + `ring`. The only friction: after
  `Finset.sum_sub_distrib`/`sum_add_distrib`, the `(if j=i then 1 else 0)*g` summand must be normalized
  (`ite_mul, one_mul, zero_mul`) before `sum_ite_eq'` fires — a documented low-grade `ite` tax.
- L-A: `Corank2Proto`'s bricks instantiated (gate-2), no tax.

## 3. Line count + heaviest obligation

- `Corank2MaintenanceProto` 155 LoC, `Corank2TerminalProto` 136 LoC, `Corank2HidealProto` 115 LoC.
- **Heaviest single obligation: the L-B maintenance sum** (the delta-sum split + `by_cases i=p` +
  the `ite`/`sub_zero`/`ring` closing), ~30 lines across the two directions. Still cheap; the reverse is
  no harder than the forward (same cofactor magnitude `cᵢ·rᵢ`).

## 4. The honest scope caveat + verdict

**GREEN (built, sorry-free, axiom-clean):** the three ideal-identity mechanisms of the recursion —
block-elim (L-A, coupled), maintenance (L-B, the b-chain reverse), terminal (L-C, `1/unit`) — each
TWO-SIDED with continuous reverse cofactors. The coupling never obstructs the reverse at any mechanism.

**NOT built (the #112 composition/wiring, honestly named):**
- The single LITERAL `(3,3,4)` chart: composing L-A∘L-B∘L-C into one explicit 21-variable `g` and proving
  `⟨coreGen (3,3,4) e ∘ g⟩ = ⟨monomialFam bexp⟩` end-to-end. The mechanisms are proven; the composite `g`
  (block-elim shear ∘ radial blow-ups ∘ join) + the `coreGen` flatten is the #112 build — Codex's flagged
  biggest Lean risk ("the full 21-variable composed-chart factorisation … coreGen/matrix flattening …
  preservation of the pivot through all shears — NOT reciprocal continuity"). Bounded detail-at-scale: the
  normal crossing is Gröbner-banked, #124 (realization) is GREEN.
- The **full-fan cover atom** (route-a) — NOT built here; per the heartbeat it is separately GREEN-on-math
  (hcover route-a probe). Out of this reverse-focused measurement's scope.

**Verdict — GREEN on the gate's decision content.** `hideal_bwd` closes cheaply at coupled corank-2 at
every recursion mechanism; "the b-chain absorbs the reverse" is confirmed (L-B `maintenance_step_two_sided`
makes it precise and true). This is NOT the 7th over-claim → NOT objects-only cite. Route P's specific
reverse risk — the piece 6 prior mis-scopes never built two-sided — is retired across L-A/L-B/L-C.

**Recommendation (for the controller, who re-derives + holds the scope-optimism guard):** the reverse is
de-risked GREEN. What remains for a literal green-BOTH end-to-end `(3,3,4)` chart is the #112 composition
(explicit composite `g` + `coreGen` flatten + cover) — the mechanisms it composes are all now proven
two-sided, so it is wiring/engineering, not a wall or open math. If the render + Gröbner-banked crossing +
#124 GREEN price that as detail-at-scale, fire #112; if belt-and-braces is wanted, price one explicit
composite-`g` `(3,3,4)` chart first. The reverse will not be the blocker.
