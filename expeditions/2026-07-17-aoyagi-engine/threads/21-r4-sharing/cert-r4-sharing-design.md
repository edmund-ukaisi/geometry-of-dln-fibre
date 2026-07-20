# Cert — R4 support / sharing propagation (the design de-risk)

*Seat: `pen-and-paper` (pnp-r4, design/cert direction), navigator's "start the design NOW so the
LARGE build starts warm at the spine's discharge." Exact symbolic (`sympy` 1.14, `positive=True`
sources); NO Lean building. Batteries alongside (`battery/r4_bchain_support.py`,
`battery/r4_ledger_propagation.py`, both exit-0). Decorrelated Codex leg (`codex/design-{prompt,
answer}.md`, xhigh, my conclusions withheld — Codex re-derived the b-recursion, the generator
content, the (3,3,4) branch and the kill-condition from scratch and CONVERGED on the verdict, adding
one load-bearing qualification I have folded in). Pinned to the LANDED carrier:
`StepData`/`LeafData`/`RootLedger` + `stepUpdate`/`StepRel`/`IsFullMonomialization` (`EngineDefs.lean`,
`ResolutionTree.lean`); `ConState` + `stepCase11`/`stepAppendAdvance`/`stepRollover` + `conRoot` +
the `OracleInv`/`conRel` blindness lemmas (`EngineConstruction.lean`); `LeafPullback` (the residual
normalization); `GeoAlphaGauge` (the `bChain` consumer). The rung this de-risks is R4 (priorities.md;
compass fork 3/10/11).*

---

## VERDICTS (one line each)

- **The sharing data is DERIVED, not independent.** Solving Aoyagi's b-recursion (worked.tex:484)
  gives `b_i = ∏_{t̃_k < i} u_k` (each divisor squarefree), so the divisor content of every loss
  generator is its ROW's b-value, and `support(row i) = {k : divTilde k < i}` — a function of
  `divProfile` (via `divTilde = tildeOf ∘ divProfile`) already carried first-class at R1. No `Finset`
  is transported across the per-divisor re-indexing.
- **`genDivExp`/`numGen` should be DROPPED as primitive fields (or made derived), not faithfully
  propagated.** They duplicate `divProfile`-determined data. The elder charge-6 "don't duplicate what
  the state carries first-class" applies exactly. This REVISES the literal fork-3 "typed FIELDS"
  wording while honoring its WHY (the coupling is real and typed — via `divProfile`, per-divisor, full
  identity retained; deriving a set over the actual divisor indices is NOT the per-row-multiplicity
  flatten fork-3 forbids). Flag for elder ratification (it touches a settled fork).
- **`bExp` should become a DEFINITION** `bExp i k := if divTilde k < i then 1 else 0`, and
  **`bChain : Monotone bExp` a THEOREM** (immediate from the def). This also discharges the SEPARATE
  deferred "real b-chain population" (EngineConstruction:336 placeholder `bExp := fun _ _ => 0`) — the
  same work. The exact spec is strictly stronger than the current `Monotone` field and pins THE
  Aoyagi chain (Codex: `Monotone` alone is insufficient).
- **The propagation "proofs" collapse to two facts, both already owned:** (a) `divProfile`
  propagation (R1, page-verified in `stepUpdate`/`StepRel`); (b) the definitional identity
  `bExp'/support' = f(divTilde')` maintained because `divTilde'` is `tildeOf` of the propagated
  `divProfile'`. There is nothing per-generator to transport.
- **The one load-bearing hypothesis (Codex):** derivability needs the residual block to be
  DIVISOR-FREE (strict-transform). A non-normalized state that hides an extra `u` in the residual
  breaks the formula (`⟨x,uy⟩` rlct 1 vs `⟨ux,uy⟩` rlct ½ — same b-chain + profile, different value).
  This is ALREADY encoded by `LeafPullback`'s `0 < lo` residualCore lower bound (the `∏ divCoord²`
  monomial captures ALL divisor content; the residual is a positive unit). It is the kill-condition,
  and it is closed.
- **Size verdict: the compass "balloons" is PRICED DOWN — R4 is SMALL, not LARGE.** No `Finset`
  transport, no new per-case data flow. The work is: make `bExp`/`support` derived defs (delete two
  placeholder fields), prove `bChain` and the `bExp_spec` (one lemma), re-check the two batteries.
  Estimate below: ~1 module + ~10 mechanical constructor-site edits.

---

## §1 The field design

### §1.1 What the sharing data IS (the paper's object)

The recursion maintains (worked.tex:475–490, indexed by layer `S` and cleared-count `J`)

    ⟨∏_{s=1}^L C^{(s)}⟩ = ⟨diag(b_1,…,b_{M(S)}) · [E_J O ; O D_J] · ∏_{s=S+1}^L C^{(s)}⟩,

with `b_0 = 1`, `b_i = (∏_{t̃_{s,k} = i-1} u_{s,k}) · b_{i-1}`. The exceptional coordinates `u_{s,k}`
are the exceptional divisors; `t̃_{s,k} = min T_{s,k}` is the divisor's clearing level. At the terminal
leaf (`S = L+1`) the block is fully diagonal and `F = ∑_i b_i²` (normal crossings). The "sharing"
that fork-3 mandates typing — the coupling that makes corank-≥2 branches bind (worked.tex:600–649) —
is exactly: WHICH `u_{s,k}` divide WHICH generator of the loss ideal, i.e. `support : Gen → Finset
DivVar` (worked.tex:645).

**Solving the recursion (D1, Codex Q1).** By induction, `b_i = ∏_{t̃_{s,k} ≤ i-1} u_{s,k}`, each
divisor to power exactly 1 (squarefree):

    ν_{u_k}(b_i) = 1 if t̃_k < i, else 0.          [bExp_spec]

Case-1(1) increases a divisor's JACOBIAN exponent `divExp = M_{s,k}` (the change-of-variables power),
NOT its exponent in any `b_i` (which stays 0/1). So `divExp` and `bExp` are genuinely different reads
of the ledger (cf. cert-ledger-accumulation §7.2: `divExp − 1` accumulates; the `b`-power does not).

**Generator content (D2, Codex Q2).** Write `H = [E_J O ; O D_J] ∏_{s>S} C^{(s)}`. The generator in
matrix-row `i`, column `c`, is `G_{ic} = b_i · H_{ic}`. In Aoyagi's normalized ratio / strict-
transform coordinates `H` carries no extracted exceptional factor, so

    ν_{u_k}(G_{ic}) = ν_{u_k}(b_i) = 𝟙_{t̃_k < i},   independent of the column c.

So the divisor content of a generator depends ONLY on its row `i`, and equals `support(b_i)`.

**Conclusion.** `support(generator in row i) = {k : t̃_k < i} = {k : divTilde k < i}`. For a residual-
block LOCAL row `a` (global row `i = J + 1 + a`), `support = {k : divTilde k ≤ J + a}` (Codex Q4).
The full sharing pattern — including which divisors are shared across the corank-≥2 block (a divisor
with `t̃_k ≤ J` divides EVERY residual row; the corank-2 coupling is a length-≥2 equal run of the
b-chain) — is determined by `divProfile` and the structural row-index. This is `genDivExp`'s content,
computed, not stored.

### §1.2 Where it lives, and the compat story

- **Primitive:** `divProfile : Fin numDiv → (Fin L → ℕ)` (already on `StepData`/`ConState`/`LeafData`
  /`RootLedger`, R1). `divTilde k := tildeOf (divProfile k)` (already defined, all four carriers).
- **Derived (new defs, replacing fields):**
  - `bExp i k := if divTilde k < i then 1 else 0` (indexing convention: 1-indexed row `i ∈ 1..M(S)`;
    0-indexed Lean `Fin numB` uses `divTilde k ≤ i.val`, since Lean row `r` is mathematical `b_{r+1}`
    — Codex Q3). `bChain : Monotone bExp` follows (`t̃_k < i ⇒ t̃_k < i+1`).
  - `support (i) := Finset.univ.filter (fun k => divTilde k < i)` — a def keyed by the diagonal-row
    index, NOT an abstract `Fin numGen`. The existing `StepData.support g = {k | genDivExp g k ≠ 0}`
    becomes `= bExp (genRow g)`'s nonzero locus, i.e. `{k : divTilde k < genRow g}`.
- **Dropped:** the `numGen` and `genDivExp` FIELDS on `StepData` and `ConState`; the `numB`/`bExp`/
  `bChain` FIELDS become derived (or `numB := M(S)` a def + `bExp`/`bChain` derived). The consumer
  `GeoAlphaGauge` (which reads `bChain` for "the ratios `bᵢ/b₁` are polynomials") is UNAFFECTED: the
  derived `bExp` is monotone, so the ratios are still polynomials; the exact `bExp_spec` is available
  if a consumer wants more.

**Why deriving is not the fork-3 flatten (D3, Codex Q4).** The g-delta-flatten kill (`⟨δx,δy⟩` rlct
½ vs `⟨δ₁x,δ₂y⟩` rlct 1) forbids collapsing to a per-output-row scalar multiplicity that loses WHICH
divisor is shared. Deriving `support = {k : divTilde k < i}` does the OPPOSITE: it keeps each divisor's
full identity (`divProfile` is per-divisor with the full `T`-vector) and returns a SET over the actual
divisor indices `k`. The two configs of the kill have DIFFERENT `divProfile` ledgers — "one divisor
shared across two rows" is `numDiv=1, t̃=[0]` (b-chain `b₁=b₂=δ`); "two divisors, one per row" is
`numDiv=2, t̃=[0,1]` (b-chain `b₁=δ₁, b₂=δ₁δ₂`). No information is lost. (Codex's refinement: the
literal incomparable `{δ₁},{δ₂}` config lies OUTSIDE the normalized nested row-chain — it is not an
Aoyagi state — so it is not even a config the carrier must represent; but the `numDiv`/`t̃`
distinction is what makes the derivation faithful regardless.)

---

## §2 The propagation invariant (Lean-ready)

### §2.1 The threaded statement

For a state `s` (a `StepData`/`ConState` reachable in the construction), define the sharing read
purely from `divProfile`:

    Support(s)(i) : Finset (Fin s.numDiv) := {k | s.divTilde k < i}      (i : Fin (numB s), numB s = M(S))

The propagation invariant is the COHERENCE of the derived read with the paper's actual b-chain:

    ShareInv(s) : ∀ i, (the divisor set dividing the row-i generators of ⟨…s…⟩) = Support(s)(i)
                ∧ Monotone (Support(s))                                          -- bChain
                ∧ ∀ i k, ν_{u_k}(b_i^{(s)}) = if s.divTilde k < i then 1 else 0  -- bExp_spec

Because `Support`, `Monotone`, and `bExp_spec` are ALL definitional functions of `s.divProfile`, the
only genuine content is the FIRST conjunct — the tie to the geometry — which is exactly the b-chain
solution (§1.1, D1/D2) under the residual-divisor-free hypothesis (§4). It is established ONCE
(not per step) as the b-recursion lemma; its per-state instance follows by `divProfile` congruence.

### §2.2 conRoot base

`conRoot = ⟨0,0,0,Fin.elim0,Fin.elim0,…⟩` has `numDiv = 0` (EngineConstruction:2166). So
`Support(conRoot)(i) = ∅` for every `i`, `Monotone` is vacuous, and `bExp_spec` is vacuous (`b_i = 1`,
no divisor). `ShareInv(conRoot)` holds by vacuity — the empty start (every divisor is born
below). Mirrors `OracleInv_conRoot`'s "`numDiv = 0` ⇒ per-divisor clauses vacuous."

### §2.3 The four per-`stepUpdate`-case maintenance identities

Each shows `ShareInv(s) → ShareInv(s')` for the child `s' = stepUpdate/step… s`. Because `Support`
is `tildeOf ∘ divProfile`-derived, each reduces to the ALREADY-PROVEN `divProfile` transition
(EngineDefs:180–221 / EngineConstruction:180–198) plus a one-line set-congruence. Write
`t̃'_k = tildeOf (divProfile'_k)`.

**(1) case-1(1) — `stepCase11 i`** (`divProfile` mutated at `i` by `setTail`, `t̃_i ↦ J`; others
unchanged; `numDiv` unchanged). `divExp_i += runLen·resCols` (Jacobian only — does NOT touch the
0/1 b-content). MAINTENANCE: `Support'(row) = {k : t̃'_k < row}`; only `k=i` changed its `t̃` (down to
`J`), so a divisor previously entering the chain at level `t̃_i` now enters at level `J ≤ t̃_i` — the
merge onto the diagonal, monotone preserved. Lean shape: `Function.update` congruence + `tildeOf_
setTail_le` (already banked, EngineConstruction:209). **The exponent bump is invisible to `Support`.**

**(2) case-1(2) — `stepAppendAdvance` (split)** (`numDiv+1`; new divisor `T₀ := setTail (divProfile
mergeIdx)`; `cleared+1`). The new divisor inherits the merged divisor's head-profile with the tail
written to `J`, so `t̃_new = J`. MAINTENANCE: `Support'` on the OLD divisors is unchanged
(`divProfile` carried); the new divisor enters the chain at level `J` — it divides every row `i > J`.
Lean shape: `Fin.snoc` congruence + `divTilde (Fin.snoc …) = …` (the new column's `t̃`).
**REPLACES the current placeholder** `fun g => Fin.snoc (s.genDivExp g) 0` (EngineConstruction:192) —
which sets the new column to `0` (WRONG: a born divisor divides the generators of its rows). Under the
derived design there is no column to set; `Support'` recomputes from `divProfile'`.

**(3) case-2 — `stepAppendAdvance` (full block)** (`numDiv+1`; new divisor `T₀ := setTail (fun p =>
runMinWidth M p)`; `cleared+1`). Same shape as (2): the new divisor is the FULL-BLOCK pivot, `t̃_new =
J`. THE COUPLING lives here: a case-2 birth of a `k×k` residual block (`k = resRows` = corank) creates
ONE divisor at level `J` whose diagonal cell spans an EQUAL RUN of length `k` in the b-chain (it
divides all `k` residual rows) — the corank-≥2 sharing. `Support'` captures it: `{i : new ∈
Support'(i)} = {i : J < i ≤ M(S)}`, a run of length `resRows`. Lean shape: `Fin.snoc` congruence.

**(4) rollover — `stepRollover`** (`layer+1`, `cleared:=0`; `numDiv`/`divExp`/`divProfile` carried
VERBATIM). `divProfile` unchanged ⇒ `t̃` unchanged ⇒ `Support` unchanged on the carried divisors;
`numB` re-reads at the new layer (the diagonal size `M(S+1)`), but the b-content per divisor is
identical. `ShareInv(s) → ShareInv(s')` immediately. Lean shape: `rfl`-class on `divProfile`.

All four are congruences of a `divProfile`-derived function under the R1-propagated `divProfile` — no
new data flow, no `Finset` transport, no per-generator bookkeeping.

---

## §3 sympy verification (`battery/`, both exit-0)

- **`r4_bchain_support.py`** — the field-design facts.
  - **D1** `b_i = ∏_{t̃_k < i} u_k`, exponents ∈ {0,1}: built symbolically over `u`-coords for five
    divisor configurations (simple chain, equal run, gap, the shared 2×2 block, mixed), each matching
    `{k : t̃_k < i}`; `bChain` monotone (support nested) on all five.
  - **D2** row-determines-content: `diag(b)·D` with a symbolic divisor-FREE ratio block `D`; the
    divisor content of every entry is constant along its row and equals `support(b_i)`.
  - **D3** discrimination: SHARED (`numDiv=1, t̃=[0]`, `b₁=b₂=d`) vs SPLIT (`numDiv=2, t̃=[0,1]`,
    `b₁=d₁, b₂=d₁d₂`) have DIFFERENT `divProfile` fingerprints — deriving loses no information.
- **`r4_ledger_propagation.py`** — a ledger simulator implementing `stepUpdate`'s four cases verbatim
  (`setTail`, `case11`/`case12`/`case2`/`rollover`), checking `Support(s)(i) = {k : divTilde k < i}`
  + `bChain` monotone at EVERY reachable state.
  - **Run A** — (3,3,4): value banked (`Mval(1,0)=8`, `minAdm=8`, rlct 4, via `_minadm`); the
    corank-2 case-2 birth of the 2×2 residual produces a length-2 equal run (`t̃=1` divisor shared
    across b-rows [2,3]) — the coupling; and the corank-≤1 restriction (`minAdm=9 > 8`) confirms the
    equal-run cut is load-bearing.
  - **Run B** — (2,2,2,2), L=3: a mixed depth-3 branch (case-2 birth → case-1(2) split → rollover →
    case-1(1) merge → rollover → case-2 birth) with the support identity maintained across every
    step, and the rollover carrying `divProfile` verbatim.
- **Codex decorrelation** (`codex/design-answer.md`, xhigh, conclusions withheld): independently
  derived `b_i = ∏_{q_k<i} u_k`, the column-independence, `support(g)=({k:min divProfile(k) ≤ J+a})`,
  the (3,3,4) branch (binding `δ` at `t̃=1` shared across the 2×2 block, `M_δ=8`, rlct 4), and the
  verdict "derive `genDivExp`/`support`; do not transport." Added the residual-divisor-free
  qualification (§4). Two decorrelated derivations agree to the component.

---

## §4 Kill-condition

**What would falsify the derived-support design:** a reachable state whose ACTUAL generator sharing is
NOT `{k : divTilde k < i}` — i.e. two states with identical `divProfile` ledgers (hence identical
`divTilde`, hence identical `Support`) but different generator-sharing, hence different RLCT.

**The only mechanism (Codex Q6, exact):** a residual block that is NOT divisor-free. If `H_{ic}` hides
an extracted exceptional factor, `ν_{u_k}(G_{ic}) = 𝟙_{t̃_k<i} + ν_{u_k}(H_{ic})` and the derived
`Support` undercounts. Witness (Codex): `t̃_u = 1`, `b = (1,u)`:

    I₁ = ⟨x, u·y⟩  (H₁ = (x,y),  divisor-free)   → rlct 1
    I₂ = ⟨u·x, u·y⟩ (H₂ = (u·x,y), hides a u)     → rlct ½

Both have the SAME b-chain `(1,u)` and the SAME profile ledger, yet different value. `I₂` is a
NON-Aoyagi (non-strict-transform) state.

**Why it is closed (already encoded).** The engine's `LeafPullback` (EngineDefs:43–48) states
`frobSq(prod(chartMap w)) = (∏_k divCoord_k²)·residualCore w` with `0 < lo` and `lo·residualBaseForm
≤ residualCore ≤ hi·residualBaseForm`. The residualCore bounded BELOW by a positive multiple of the
base form (`‖z‖²` Morse or `1`) means it carries NO divisor vanishing beyond the base Morse form — ALL
divisor content is in the `∏ divCoord²` monomial. That is exactly "the residual is divisor-free," and
it EXCLUDES the `I₂` kill on the constructed atlas. `IsFullMonomialization` (`divExp = Mval divProfile`
+ the B'-coherence) pins the same normalization at the ledger level. So the derived-support design's
one hypothesis is a THEOREM of the carrier, not a new obligation.

**Secondary tripwire (design-internal, cheap to guard):** if a future step ever writes a `divProfile`
whose `divTilde` does not match a divisor's actual chain-entry level, `Support` desyncs. Guard: the
`bExp_spec` conjunct of `ShareInv` (an equality checked per state) — it fires if the derivation and
the geometry ever disagree. This is the executable kill-condition to keep in the battery.

---

## §5 Transcription notes + size re-estimate

### §5.1 Transcription notes (Lean-ready shapes, keyed to landed names)

- **New defs (one small module, e.g. `Engine/SharingDerived.lean`, imports `ResolutionTree`):**
  - `StepData.bExpD (n) : Fin (numB n) → Fin n.numDiv → ℕ := fun i k => if n.divTilde k < i then 1
    else 0` (and the `LeafData`/`ConState` analogs); `numB n := runMinWidth`-diagonal size `M(S)`.
  - `StepData.bChainD : Monotone n.bExpD` — one lemma (`if`-monotone in `i`).
  - `StepData.supportD (n) (i) : Finset (Fin n.numDiv) := univ.filter (fun k => n.divTilde k < i)`.
  - `bExp_spec` / `support_spec` — the two definitional `rfl`-class lemmas.
- **The maintenance lemmas (four, §2.3):** each `stepX_bExpD` / `stepX_supportD` is a `divProfile`
  congruence:
  - case-1(1): reuse `tildeOf_setTail_le` (EngineConstruction:209) + `Function.update` congruence.
  - case-1(2)/case-2: `Fin.snoc` congruence + `divTilde_snoc` (the new column's `t̃ = J`).
  - rollover: `rfl` on `divProfile` (EngineConstruction:198 carries it verbatim).
- **The one geometric lemma (`ShareInv` first conjunct):** `b_i = ∏_{t̃_k<i} u` is the b-recursion
  solution; its geometric instance uses the residual-divisor-free fact from `LeafPullback`/
  `IsFullMonomialization`. This is the ONLY non-congruence content, established once.
- **Field-drop edits (mechanical, ~10 sites):** remove `numGen`/`genDivExp` from `ConState`
  (EngineConstruction:54–57) and `StepData` (ResolutionTree:116–121); drop them from the constructor
  calls (`stepCase11`:183, `stepAppendAdvance`:190–193 — deletes the `Fin.snoc … 0` placeholder,
  `stepRollover`:198, the `leafOfState`-class projection:352–353); simplify the two blindness lemmas
  (`OracleInv`/`conRel` blind to `divExp/numGen/genDivExp`, :1698/:1712 — the `numGen'/genDivExp'`
  quantifiers drop); update the witnesses (`CanonicalWitness224.lean`:35/145, `CoRank2Spike.lean`:90).
  Replace `numB := 1; bExp := fun _ _ => 0` placeholders (EngineConstruction:336/348, all witnesses)
  with the derived `bExpD`. `bChain` consumers (`GeoAlphaGauge`:515) rebind to `bChainD` unchanged.
- **Keep-the-field fallback (COHERE, if the drop is disruptive):** leave `genDivExp` a field, add
  `genDivExp_coh : genDivExp g = bExpD (genRow g)` to `ShareInv`, prove it maintained across the four
  steps (still a `divProfile` congruence, NOT a `Finset` transport). Larger than DERIVE but still
  bounded. DERIVE is recommended (elder charge-6).

### §5.2 Size re-estimate — the "balloon" priced down

The compass named support propagation the "second cost center — balloons" (fork 10, EngineDefs:170,
ResolutionTree:263) on the assumption of transporting `support`/`genDivExp` `Finset`s across the
per-divisor re-indexing. **That transport is unnecessary — the sharing is a `divProfile`-derived
function.** With the design in hand:

- **New content:** 1 small module (~4 defs + `bChainD` + 2 spec lemmas + the 4 congruence maintenance
  lemmas + the 1 geometric b-recursion lemma). Every maintenance lemma is a congruence of a derived
  function under an ALREADY-PROVEN `divProfile` transition — the class of proof already discharged for
  `divTilde`/`pendingCount` (EngineConstruction:204–219).
- **Mechanical churn:** ~10 constructor-site edits + 2 witness updates + 2 blindness-lemma
  simplifications (all deletions/renames — the blindness lemmas get SMALLER).
- **No long pole:** nothing here touches the spine (coverage/region_glue); it does not consume
  `rlct=c*`/`cited_aoyagi_dln`; the finiteness cert is provably blind to it (the blindness lemmas).

**Verdict: R4 is SMALL (≈ a MEDIUM at the outside if the field-drop refactor is counted), not LARGE.**
The LARGE estimate was pricing a transport that the mathematics does not require.

---

## Close

- **Firmest (battery-verified + Codex-decorrelated):** `b_i = ∏_{t̃_k<i} u` squarefree (§1.1/D1); the
  column-independent generator content (§1.1/D2); `support(row i) = {k : divTilde k < i}` derived from
  `divProfile` (§1.2/D3); the four-case maintenance as `divProfile` congruences (§2.3); the (3,3,4)
  corank-2 coupling as a length-2 equal run, load-bearing (§3 Run A).
- **The design verdict:** DERIVE `bExp`/`support` from `divProfile`; DROP `numGen`/`genDivExp` (or
  COHERE as fallback); make `bChain` a theorem + strengthen to `bExp_spec`. This discharges BOTH the
  deferred b-chain population AND the R4 genDivExp propagation with one derived read. Requires elder
  ratification (revises fork-3's literal "typed FIELDS" while honoring its WHY).
- **The kill-condition:** a non-divisor-free residual (`⟨ux,uy⟩`-class) — CLOSED by `LeafPullback`'s
  `0 < lo` residualCore normalization; kept executable as the `bExp_spec` conjunct.
- **Most likely to break it:** a step that writes a `divProfile` whose `divTilde` desyncs from the
  actual chain level (the `bExp_spec` tripwire catches it), or a consumer that needs the residual's
  own divisor structure (none exists — region_glue never consults `support`, compass region-glue §;
  `GeoAlphaGauge` needs only `Monotone`).
- **Next:** the design is fully specified; the remaining work is the Lean transcription of §5.1. No
  further paper adjudication is owed — §1–§2 pin the field + its maintenance exactly, §3 double-
  verifies, §4 closes the kill-condition.
