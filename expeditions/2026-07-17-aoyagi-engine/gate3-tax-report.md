# Gate-3 tax report — the corank-2 TWO-SIDED terminal `hideal` (does `hideal_bwd` close cheaply?)

**Branch:** `expedition/aoyagi-engine-gate2` (off `-PROTO` @ `05c35eb8a`); uncommitted (role boundary — the
controller integrates).
**Modules:** `lean/DLNFibre/Core/Aoyagi/Corank2TerminalProto.lean` (136 LoC), `…/Corank2HidealProto.lean`
(115 LoC, the gate-2 block-elim atom, reused). Both sorry-free; `#print axioms` (force-elaborated, oleans
deleted + rebuilt) = `[propext, Classical.choice, Quot.sound]` on all load-bearing theorems.
**Decorrelation:** sympy entry-level check + Codex xhigh red-team (both in `gate3-codex/`).

**VERDICT: GREEN on the gate's KEY measurement — `hideal_bwd` closes CHEAPLY at coupled corank-2.** With
one honest scope caveat (§4): the Lean artifact demonstrates the reverse on the terminal residual-block
monomialisation + the coupled block-elim atom; it is NOT the literal `(3,3,4)` 21-variable composite-chart
end-to-end (that is the bounded-large forward build, task #112 — Codex's flagged biggest risk, engineering
not a wall).

---

## 1. THE KEY MEASUREMENT — `hideal_bwd` is cheap (`1/unit`), coupling does not obstruct it

The reverse `⟨diag b⟩ ⊆ ⟨(∏C)∘g⟩` ("the exceptional monomial recovered from the loss") is discharged by
the **already-proven Core theorem `terminal_bezout`** (`PrincipalInv.lean:318`, sorry-free, axiom-clean).
Given the terminal forward `StepInv` + ONE cleared-pivot entry `(F i₀∘g) = b·unit` with `unit 0 ≠ 0`, it
produces `b = (1/unit)·(F i₀∘g)` on the open `V' = V ∩ {unit ≠ 0}` — the Bézout cofactor `1/unit`,
continuous by `ContinuousOn.inv₀`. **Never a `1/(vanishing)`.**

`Corank2TerminalProto.hideal_terminal_both` instantiates this end-to-end for a corank-2 residual block
(`blockBlowupMap`, pivot = slot 0): `(resid∘gBlk) = (w₀, w₀w₁, w₀w₂, w₀w₃) = w₀·(1,w₁,w₂,w₃)`, dominant
monomial `b = E = w₀`, cleared pivot ≡ `w₀` (`unit ≡ 1`). BOTH `Chart.hideal` inclusions to
`monomialFam [1,0,0,0]` hold on `V'`, sorry-free:
- `hideal_fwd` — forward divisibility, cofactor `q = (1,w₁,w₂,w₃)` (polynomial).
- `hideal_bwd` — the reverse, cofactor the Bézout `r = 1/unit = 1` at the pivot.

**Why the coupling does not obstruct the reverse (the render's "b-chain absorbs the reverse", sharpened).**
The dominant monomial `b₁ = E` is recovered from the cleared-pivot entry, whose strict transform is a
nonvanishing UNIT — an UNCOUPLED fact. The coupling lives entirely in the higher monomials `b₂,b₃`, which
are `∈ ⟨b₁⟩` (the divisibility chain `b₁|b₂|b₃`, Gröbner-banked) and so never need separate recovery:
`⟨diag b⟩ = ⟨b₁⟩` and `b₁` = the pivot entry. So the terminal reverse is `1/unit` at the dominant pivot,
**independent of the coupling** — even simpler than the render's maintenance-step `diag(b')⁻¹·P·diag(b')`
conjugation (which is the polynomiality of the FORWARD shear, not the reverse).

Codex (decorrelated, xhigh) independently reached the same conclusion: "the inverse/Bézout construction
itself is not the wall … terminal reverse closure is GREEN once the terminal forward factorisation and
per-chart pivot certificate are supplied." Sympy (entry-level, `gate3-codex/`) confirms the pivot entry
factors as `E·unit`, `unit(0)=1≠0`, so `1/unit` is continuous near `0`.

## 2. Did Mathlib fight? — NO

- `terminal_bezout` + `principalInv_regionRepresents` are proven Core theorems; feeding them the concrete
  block-blowup datum is a one-line application. No ideal-membership / measure / cast machinery.
- The forward `StepInv` for the block (`stepInv_blk`): the three obligations (quotient continuity,
  vanishing-at-0, divisibility) discharge by `Continuous.continuousOn` + `blockBlowupMap`'s banked unfold +
  `Fin.sum_univ_one` + `ring`. The one friction: the residual `1 : (Fin D→ℝ)→ℝ` needs `Pi.one_apply`
  before `ring` (else `1 u` is opaque). Low-grade, documented.
- `bE_eq_monomialFam` (`b = w₀` in `monomialFam [1,0,0,0]` form): `Fin.prod_univ_four` + `Matrix.cons_val_*`
  + `pow_one/pow_zero`. Routine.

## 3. Line count + heaviest obligation

- **`Corank2TerminalProto`: 136 LoC** (the new terminal two-sided `hideal`); `Corank2HidealProto`: 115 LoC
  (gate-2 block-elim atom, reused for the coupling).
- **Heaviest obligation: the forward `StepInv` divisibility** (`stepInv_blk`, ~8 lines) — and it is cheap.
  The reverse is a single `terminal_bezout` application. So at the TERMINAL, the reverse is strictly
  cheaper than the forward (the opposite of the pre-gate worry).

## 4. The honest scope caveat (what I did NOT build) + verdict

**What is GREEN (built, sorry-free, axiom-clean):** the corank-2 residual-block terminal monomialisation,
BOTH directions, reverse via `terminal_bezout` (`1/unit`); the coupled block-elim atom (gate-2). Together
these show: (i) the coupled residual is produced by the block-elim (`Δ` genuinely coupled, `Corank2Proto`/
`Corank2HidealProto`), and (ii) once a residual block reaches the blow-up normal crossing, BOTH `hideal`
directions close, the reverse cheaply.

**What I did NOT build (the bounded-large residual, honestly named):**
- The literal `(3,3,4)` **21-variable composite chart `g`** (block-elim shear ∘ radial `T`/`ΔS` blow-ups ∘
  the join) and the entry-level `(∏C)∘g = E·Q` forward for the ACTUAL `coreGen` product. `Corank2TerminalProto`
  models the terminal residual-block monomialisation; it is not the full composite pulled through `coreGen`.
  Codex flags this exact piece as "the biggest Lean risk … the full 21-variable composed-chart factorisation
  and coreGen/matrix flattening, including preservation of the selected pivot through all shears — NOT
  reciprocal continuity." It is engineering (detail-at-scale), not a wall: the normal crossing is
  Gröbner-banked and `#124` (deep-mixed realization) is GREEN.
- The **full-fan cover atom** (route-(a), all pivots, drop the col-pin) — NOT built here; per the heartbeat
  it is separately GREEN-on-math (hcover route-a probe). Out of this reverse-focused measurement's scope.

**Verdict — GREEN on `hideal_bwd` (the gate's stated KEY measurement).** The reverse — route P's specific
risk, the piece "6 prior mis-scopes never built two-sided" — is retired: it is `1/unit` via `terminal_bezout`
(proven), demonstrated sorry-free on a genuine corank-2 terminal, coupling-independent. This is NOT a
`hideal_bwd` wall (which would have been RED → cite). Combined with the already-GREEN cover (L7 route-a) and
realization (#124), route P's remaining work is the forward composite-chart build (task #112) — bounded
detail-at-scale, not open mathematics.

**Recommendation (for the controller, who re-derives + holds the scope-optimism guard):** treat the reverse
as de-risked GREEN. Before auto-firing the full build, the one thing NOT yet Lean-verified is the literal
`(3,3,4)` forward composite `g` (the 21-var chart + `coreGen` flatten) — Codex's biggest risk. If the render
+ Gröbner-banked normal crossing + #124 GREEN suffice to price that as detail-at-scale, fire; if a
belt-and-braces step is wanted, price one explicit composite-`g` forward for `(3,3,4)` first. The reverse
will not be the blocker either way.
