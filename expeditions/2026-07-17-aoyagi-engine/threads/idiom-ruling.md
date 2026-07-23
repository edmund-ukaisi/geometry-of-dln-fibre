# Idiom ruling — the canonFlatten boundary (elder-standing, 2026-07-23)

**Charge (team-lead, priority; gates three lanes — wall #38, lastLayer, CaseStepAssembly case1'').** Two
seats independently hit the ∀e-vs-`canonFlatten` boundary; two idioms are in play (pin-hypothesis
`he : e = canonFlatten d` vs consume-structure `hslot : Deg1SupportedSlot…` + anchor at L5). Rule ONE.

## The ruling in one line

**Pin exactly where the property is BORN (derived from the concrete `coreGen`); stay general-e exactly
where a lemma TRANSPORTS a hypothesized property. Thread the pin `he : e = canonFlatten d` through the
derivation-invoking spine to the payoff (rfl-discharge). No `∀`-node consume-hypothesis for a
canonFlatten-only property — that is a pin in disguise.**

## The criterion: derive vs transport

The degree-1 / homogeneity / boost-center support properties are **false at general (even linear) e** and
true only at `e = canonFlatten d` — the concrete flatten aligns the flat coordinates so the reused-pivot
coordinate factors cleanly (`IsLinearMap` is INSUFFICIENT: an abstract linear e mixes coordinates and
breaks the `u_{e₂}·coeff` split; the `(1,1,1)` unipotent-scrambler / KILLED-BY-e countermodel, L4D+Codex).
Two lemma classes:

- **DERIVATION / BASE** — establishes a canonFlatten-alignment property *from the concrete `coreGen`*
  (born here; false ∀e). **→ PIN `e = canonFlatten d`.** Members: `coreGen_layerHomogeneous` (the L2 base
  atom, already canonFlatten-pinned by necessity); `realBranch_boostReady_case11` (the wall — `Deg1SupportedOn
  ed.center` born from the b-chain at a case11 node).
- **TRANSPORT / STEP** — propagates a *hypothesized* property (parent slot → child slot), genuinely true
  ∀e given the hypothesis, `he_lin`-free. **→ STAY general-e (consume).** Members:
  `realBranch_multiAffine_step` (the slot descent — case1/case2 conjunct B); `foldResid_layerHomogeneous'`
  (the L3T3 homogeneity step). These are the codebase's existing consume shape and are CORRECT as-is; they
  are consumed *at* `canonFlatten` by the pinned lemmas (a general-e lemma instantiated at canonFlatten is
  fine).
- **DERIVATION-INVOKING** — any lemma that calls a DERIVATION member. **→ PIN** (it must supply
  `e = canonFlatten` to call the pinned derivation). Members: `case1_conjA`, `case1_preserves_stepInv'`
  (conjunct A calls the wall), and hence the assembly `leaf_stepInv_of_path'`,
  `exists_atlasRealizesExponents'`, and the lastLayer conjA-δ=1 family.

## Why NOT consume-structure for the derivation-invoking spine

Three reasons, decisive together:

1. **Consume relocates, it does not dissolve** (the per-node subtlety, team-lead's summit point 3). The
   boost-split fact is needed *per case11 node* inside the induction. Consume-style then means either (a)
   carry `Deg1` in the invariant `FoldStepInvAt` and PRESERVE it through case11 — but preservation through
   case11 IS the wall, canonFlatten-specific, so the need moves rather than vanishes; or (b) consume a
   `∀`-node `Deg1` hypothesis — which discharges only at canonFlatten (via the wall / homogeneity lane), i.e.
   **a pin in disguise**.
2. **Honesty / name = content.** `he : e = canonFlatten d` names the ACTUAL condition. A consumed
   `hboost : Deg1SupportedOn…` (only dischargeable at canonFlatten) names a *derived* property as if it
   were an independent hypothesis — hiding where the mathematics lives. A single clean equation `he` beats a
   `∀`-node structure hypothesis on every axis (lighter, honest, un-hidden).
3. **Paper fidelity.** Aoyagi's resolution IS at the concrete blow-up charts (the recoord
   `A'^{(S+1)} = Q₂'⁻¹A^{(S+1)}`, worked.tex:445; the inductive invariant is stated at the concrete
   exceptional-divisor coordinates `u_{s,k}`, source pp.15). The pin matches where her mathematics lives; an
   abstract-e statement re-introduced via a hypothesis is *less* faithful. (Confirmed by the C6 prose-intent
   pass: nothing the wall anchors to is at an abstract reparametrization.)

The "keep it general" benefit of consume is **illusory here**: the summit verification shows the current
∀-linear-e assembly statements rest on a case1 conjunct that is *false* at general linear e — they always
needed amendment. There is no genuine generality to preserve; the transports (`multiAffine_step`) that ARE
genuinely general keep their general-e statements untouched.

## Concrete application (old → new shapes)

The pin is a **visible hypothesis** `(he : e = canonFlatten d)`; it discharges by `rfl` at the payoff
(which is already at canonFlatten — so this is ladder-restating, NOT destination-touching).

1. **`realBranch_boostReady_case11`** (`Case1Wire.lean:386`) — DERIVATION.
   - OLD: `(d) (e) {p} (ed) (hδ) (hc11) (hbranch) (hslot) : Deg1SupportedOn (foldResid d e p) ed.center …`
   - NEW: add `(he : e = canonFlatten d)`. Proof uses `he` to get the b-chain factoring. Conclusion unchanged.

2. **`case1_conjA`** (`Case1Wire.lean:402`) — DERIVATION-INVOKING.
   - NEW: add `(he : e = canonFlatten d)`; pass to `realBranch_boostReady_case11 … he …` at :418. (δ=0 and
     δ=1-case12 branches don't need it, but the lemma carries it for the case11 branch.)

3. **`case1_preserves_stepInv'`** (`Case1Wire.lean:434`) — DERIVATION-INVOKING (conjunct A).
   - NEW: add `(he : e = canonFlatten d)`; pass to `case1_conjA`. **Conjunct B UNCHANGED** —
     `realBranch_multiAffine_step hpos e p ed hlayer hbranch hinv.2` is the transport, general-e, called at
     this e (= canonFlatten by `he`, but it doesn't need `he`).

4. **`realBranch_multiAffine_step`** (`MultiAffineStepWire.lean:805`) — TRANSPORT. **UNCHANGED** (general-e +
   `hslot`, `he_lin`-free). This is the canonical consume shape and stays.

5. **`leaf_stepInv_of_path'`** (`MonumentAssembly.lean:30–32`) — DERIVATION-INVOKING (calls
   case1_preserves_stepInv').
   - OLD: abstracts `(e) (he0 : e 0 = 0) (he_lin : IsLinearMap ℝ e)`.
   - NEW: **replace `(he0, he_lin)` with the single `(he : e = canonFlatten d)`** (which implies both, and
     fixes the *insufficient* `he_lin`). Thread `he` to `case1_preserves_stepInv'`.

6. **`exists_atlasRealizesExponents'`** (`MonumentAssembly.lean:49–51`) — DERIVATION-INVOKING.
   - NEW: same as #5 — `(he0, he_lin)` → `(he : e = canonFlatten d)`; discharges `rfl` at the payoff (e IS
     canonFlatten there). Payoff statement UNCHANGED.

7. **lastLayer conjA-δ=1 family** (`lastLayer_clear_preserves'` and the LastLayerInv feeders) — LL renders.
   **Ruling: PIN (LL's option (a)), NOT consume (option (b)).** The all-Deg1 it needs is the
   canonFlatten-derived homogeneity-lane output; consuming it (b) is pin-in-disguise (discharges only at
   canonFlatten) or relocates the need to the invariant preservation (the homogeneity lane, canonFlatten).
   Pin `e = canonFlatten d` across the lastLayer family. **Accept the arch-C general-e stub re-bake** — it
   is mechanical (ladder-restate, no new math) and makes the stub honest (the general-e stub asserts a
   false-at-general-e / vacuous slot condition).

8. **`coreGen_layerHomogeneous`** (`MonumentAtlas.lean:1392`) — DERIVATION base, already canonFlatten-pinned.
   Confirm it stays pinned; it is the root the transport steps anchor at.

## Ownership + sequencing

- **L4D** renders the wall side (#1–3) on this ruling; **LL** the lastLayer side (#7); **L3T3** finishes
  case1'' / CaseStepAssembly consuming the pinned `case1_preserves_stepInv'`.
- The transports (#4, `foldResid_layerHomogeneous'`) are untouched — no re-render.
- The pin is confined to the derivation + derivation-invoking spine; it never appears alongside a redundant
  structure-hypothesis for the same property (that would be the ugly mixing — avoided here by the clean
  derive/transport split).
- Payoff + destination UNCHANGED (the pin rfl-discharges at canonFlatten); this is ladder-restating within
  the staked boundary, not a definition-of-done change.
