# Cert — slot-stability: is a divisor's flat coordinate its immutable birth corner?

*Seat: `pen-and-paper` (pnp-slot), commissioned (journal tick 208) to adjudicate ONE page-pinned
truth-value that sizes the carrier's divisor→flat-slot mechanism (`divCoord`, `LeafData`). Paper
certificate only, NO Lean edits. Primary source: Aoyagi 2023 preprint pp.14–22 (the Case-1 / Case-2
recursive blow-up), read verbatim from `theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt`
(PDF PAGE markers = Aoyagi's pagination). Exact integer simulation of the page-faithful recursion
(`battery/slot-stability.py`, `battery/merge-slot-audit.py`, both exit-0). Decorrelated Codex leg
(`codex/slot-stability-{prompt,answer}.md`, xhigh, my conclusions withheld — independent derivation
from the chart structure). Ledger structure cross-checked against `StepData`
(`ResolutionTree.lean:87`: per-divisor `divProfile`=T, `divExp`=M; NO birth field) and the consumer
`divCoord : Fin numDiv → Fin (flatDim M)` (`EngineDefs.lean`, placeholder today).*

---

## VERDICTS (one line each)

- **T-slot = YES.** Every existing divisor `u_{s,k}` occupies ONE immutable flat slot for its whole
  life — its **birth corner** `(s_birth, J_birth, J_birth)` = `(birth layer, cleared-at-birth,
  cleared-at-birth)`. No case-step substitution ever relocates a divisor between flat slots. The
  substitutions operate IN PLACE exactly as the controller hypothesised (tick 208). `[Proved-by-page-read
  pp.15–22 + Hand-verified exact sim]`
- **The one nuance (not a scope restriction on the verdict):** in Case 1(2) the pre-existing center
  divisor's *value* is rescaled in place — `u_{s,k} = u_{S,J+1}·u'_{s,k}`, then `u'_{s,k}` renamed back
  to `u_{s,k}` in the SAME slot. This is a value-level det-1 source gauge (exactly the `α_d` of
  `cert-psi-mix` R-b), NOT a slot move. The flat SLOT is immutable throughout.
- **Secondary — recoverability = NO (ambiguous).** The birth corner is NOT a function of the current
  `divProfile` (`(T, M)`, equivalently `(T, M, t̃)`). Same `(T, M)` sits at different slots in different
  leaves (θ-multiplicity). Within any single reachable state, `(T, M)` IS injective on live divisors, so
  an immutable per-divisor field is well-defined; but no pure function `current-profile → slot` exists.
  `[Hand-verified exact sim; Codex-corroborated with an independent witness]`
- **Mechanism = IMMUTABLE FIELD** (`divBirthCoord` set at birth = the birth corner, carried verbatim;
  maintenance is congruence). NOT no-field (recompute-from-profile is unsound — the profile does not
  determine the corner). NOT dynamic-map (no transition moves a slot). `[Hand-verified]`

---

## 1. The flat-slot convention (what a "slot" is)

`FlatIdx H = Σ (⟨s, i⟩ : Σ s:Fin L, Fin H⁽ˢ⁾), Fin H⁽ˢ⁺¹⁾` (`ParamsFlat.lean:60–64`): a flat slot is a
triple `(layer s, row i, col j)` — one entry of the original parameter matrix `C⁽ˢ⁾` (size
`M⁽ˢ⁾ × M⁽ˢ⁺¹⁾`). Blow-up charts are dimension-preserving birational maps of this ambient `ℝ^N`, so
every chart's SOURCE reuses the same `N` slots; some hold divisor variables `u`, others hold
residual/ratio or spectator entries. The carrier's `divCoord k` names the slot of divisor `k`.

At node `(S, J)` the residual block `D_J` occupies the layer-`S` slots `(S, J+a, J+b)` for
`0 ≤ a < resRows, 0 ≤ b < resCols` (`M(S)=min{M⁽¹⁾..M⁽ˢ⁾}` rows, `M⁽ˢ⁺¹⁾−J` cols) — pure arithmetic of
the node, as the gate said (tick 206). Its **corner** is `(S, J, J)` (0-indexed; Aoyagi's 1-indexed
`d_{J+1,J+1}`). `[Proved-by-page-read: the residual block is `D_J=(d_{ij}), J+1≤i≤M(S), J+1≤j≤M⁽ˢ⁺¹⁾`,
PAGE 15]`

## 2. T-slot — the per-transition trace (Proved-by-page-read, pp.15–22)

The recursion invariant (PAGE 15): `⟨∏C⁽ˢ⁾⟩ = ⟨diag(b₁,…,b_{M(S)})·[[E_J,O],[O,D_J]]·∏_{s>S}C⁽ˢ⁾⟩`,
where `b_i` are monomials in the divisors introduced so far. The transitions a divisor survives:

| Transition | Page | Substitution (which flat slots it rewrites) | Effect on a `u`-slot |
|---|---|---|---|
| **Case 1(1)** — the u-pivot / MERGE | p.16 (line 982), p.16 exps | `d_{ij}=u_{s,k}·d'_{ij}` on the J₁-block; each ratio `d'_{ij}` stays in slot `(S,i,j)`. The pivot `u_{s,k}` is unchanged in value. Bookkeeping: `t̃_{s,k}:=J`, `M'_{s,k}=M_{s,k}+J₁(M⁽ˢ⁺¹⁾−J)`. | **Slot UNCHANGED.** `u_{s,k}` is the pivot — keeps its (earlier) birth slot; the (T,M) bump is not relocation. |
| **Case 1(2)** — d-corner pivot / NEW divisor | p.16–18 (lines 1027, 1045) | Corner `d_{J+1,J+1}=u_{S,J+1}` (new divisor at slot `(S,J,J)`); every other center coord divided by the pivot, staying in its own slot; the pre-existing center divisor is rescaled `u_{s,k}=u_{S,J+1}·u'_{s,k}`. Then `u'→u` rename. | **Slots UNCHANGED.** New divisor at the corner `(S,J,J)`; the old divisor's strict transform `u'_{s,k}` occupies the OLD `u_{s,k}` slot (value rescaled — the R-b `α_d` gauge). |
| **Case 2** — full-block pivot / NEW divisor | p.19–21 (line 1306) | Corner `d_{J+1,J+1}=u_{S,J+1}` (new divisor at `(S,J,J)`); nonpivot block entries → ratios in their own slots. NO `u` in the Case-2 center. | **Slots UNCHANGED.** New divisor at `(S,J,J)`; all earlier `u`-slots pure spectators (not even rescaled). |
| **Q gauge** | p.17, p.20 (lines 1068, 1339) | Unipotent on the residual d-block columns + `C⁽ˢ⁺¹⁾→Q⁻¹C⁽ˢ⁺¹⁾` (spectator). Rewrites residual/spectator slots in place. | **No `u`-slot touched.** Q acts on `d`/`C` entries only. |
| **P gauge** | p.18, p.21 (lines 1165, 1422) | Unipotent (left) cleaning the block's first column → `D'''_J=[[1,O],[O,D_{J+1}]]`. Its coefficients are `b`-ratios but it ACTS on residual `d` rows. | **No `u`-slot touched.** The `b`-monomials appear as coefficients, are not the substitution target. |
| **Rollover** | p.19, p.22 (lines 1246, 1499) | `J+1 > M(S+1)`: block collapses to `(1,0,…,0)`, `S += 1`, `J := 0`; residual continues on layer `S+1`. Chartless — no substitution. | **No `u`-slot touched.** Accumulated divisors keep their slots. |

**Conclusion (page level):** the only substitutions that ever write a `u`-carrier slot are the
BIRTHS (Case 1(2), Case 2), which write a FRESH corner slot `(S,J,J)`. Every later transition a
divisor survives either uses it as a pivot in its own slot (1(1)), rescales its value in its own slot
(1(2)), or leaves it a spectator (Case 2 / Q / P / rollover). No divisor is ever renamed to a
different `(layer,row,col)`. `[Proved-by-page-read]`

## 3. New-divisor slot = the birth corner (Proved-by-page-read)

A divisor born at node `(S, J)` (Case 1(2) or Case 2) is the corner pivot `u_{S,J+1} = d_{J+1,J+1}`,
so its flat slot is `(S, J, J)` (0-indexed) — `(birth layer, cleared-at-birth, cleared-at-birth)`, the
diagonal corner of the birth layer's matrix. Case 1(1) births NO divisor (it merges an existing one).
So along any single leaf, births happen at distinct nodes → distinct diagonal corners, and different
layers use different `layer` indices → the birth corners are pairwise distinct. `[Proved-by-page-read
for the corner position; Hand-verified for distinctness — §4]`

## 4. Ledger-level confirmation (Hand-verified, exact integer sim)

`battery/slot-stability.py` instruments the banked page-faithful recursion (rules verbatim, runmin /
FIX-A head-reset; validated against the known `t̃=0` atlases) with an **immutable** per-divisor birth
corner set at creation, carried verbatim through 1(1) merges. Across
`(2,2,2),(3,3,4),(2,2,2,2),(2,2,3,2),(3,3,2,2),(2,2,3,3,2)` and (audit) `(3,2,4,2),(4,4,2,2),(3,3,3,3)`:

- **birth-corner rewrite violations = 0** — no divisor's slot ever changes after creation.
- **within-state slot collisions = 0** — in every reachable state, all live divisors sit at DISTINCT
  slots (so `divCoord` is injective by construction — matches the ChartBridge clause, task #4).

Worked instances (required):

**(2,2,2)** — 2 leaves, each with 4 divisors on the diagonals of layers 1,2 (`(S,J,J)` slots):
- leaf0: `(1,0,0)`T=(0,0)M=4 · `(1,1,1)`T=(1,0)M=3 · `(2,0,0)`T=(2,0)M=4 · `(2,1,1)`T=(2,1)M=1
- leaf1: `(1,0,0)`T=(0,0)M=4 · `(1,1,1)`T=(1,1)M=1 · `(2,0,0)`T=(1,0)M=3 · `(2,1,1)`T=(2,1)M=1
  All slots distinct within each leaf. The divisor `(T=(1,0),M=3)` sits at slot `(1,1,1)` in leaf0 but
  `(2,0,0)` in leaf1 — **same profile, different birth corner** (the recoverability witness, §5).

**(3,3,4)** — 5 leaves, 6 divisors each on the layer-1/2 diagonals `(1,0,0),(1,1,1),(1,2,2),
(2,0,0),(2,1,1),(2,2,2)`; all distinct within every leaf (full trace in the battery output). The
minimal exponent `M=8=minAdm` appears at slot `(1,1,1)` (T=(1,0)) in every leaf — but that same
`(T=(1,0),M=8)` is ALSO born at `(2,0,0)` in other branches (§5).

## 5. Secondary — recoverability from the current divProfile (Hand-verified)

The ledger's per-divisor data is `divProfile = T` and `divExp = M` (`StepData`; `t̃ = min T` is
derived — no extra content). Two readings, both settled:

- **Global (no state-independent function).** The map `(T,M) → birth-corner` is many-to-one. Exact
  witness `(2,2,2)`: `(T=(1,0), M=3)` is born at `(1,1,1)` (clearing layer-1's 2nd pivot as a fresh
  divisor) AND at `(2,0,0)` (opening layer 2), in different leaves. Larger instances have more classes
  (`(3,3,4)`: 3; `(3,3,2,2)`: 6; `(3,3,3,3)`: 10). T-only is equally ambiguous. **So a "recompute the
  slot from the current profile" (no-field) carrier is UNSOUND.**
- **Within-state (injective, but not a computation).** In every reachable state, no two live divisors
  share `(T,M)` with different corners (0 within-state ambiguities across all instances). This means an
  immutable per-divisor field is WELL-DEFINED (never asked to hold two conflicting values), but it does
  NOT let you compute the corner from the profile — you must have recorded it.

**Why the ambiguity is structural (interpretation).** Two different exceptional divisors — one from a
partial layer-1 clear, one from opening the next layer — can realise the SAME admissible rank-profile
with the SAME codimension exponent. That is precisely the θ-multiplicity (the count of top-dimensional
components): distinct leaves realise the same minimal profile via distinct birth corners. The profile
names the STRATUM; the birth corner names WHICH blow-up produced it. They are different data.

**The merge sharpens it (`battery/merge-slot-audit.py`).** At EVERY Case-1(1) node, the chosen
divisor's true birth corner ≠ the current node's corner `(S,J,J)` (mismatch rate 100% — merge nodes ==
mismatches, all instances). Structural reason: the merged divisor has `t̃ = J+J₁ > J`, so it was born
strictly-above/earlier and its `J_birth > J` (or `s_birth < S`). So a carrier that guessed the divisor
slot from the CURRENT node (the naive node-local arithmetic the gate's "derivable by pure arithmetic"
verdict would suggest) is wrong at every merge. This is exactly the tick-208 finding, made
quantitative — and it is why the residual-block part IS node-local arithmetic (§1) while the u-pivot
part is NOT.

## 6. Mechanism recommendation — IMMUTABLE FIELD

Add one immutable per-divisor field (this IS what `divCoord`/`LeafData.divCoord` should be):
`divBirthCoord k = (s_birth, J_birth, J_birth)`, set when divisor `k` is born (Case 1(2)/Case 2) to the
current node's corner, and carried **verbatim** thereafter. Maintenance is congruence, not invariant
work: Case 1(1) keeps the pivot's field; Case 1(2) keeps the old fields and appends the new corner;
Case 2 appends the new corner; rollover / Q / P leave all fields unchanged (only the `Fin numDiv`
index set grows, under the standard injection). No dynamic per-transition slot-update rule is needed
(0 rewrites), and no-field is impossible (§5 global ambiguity). This makes `divCoord` a real,
injective map into `Fin (flatDim M)` (the diagonal birth corners), replacing the `fun _ => ⟨0,h⟩`
placeholder, and it is what the Case-1(1) center's `u`-coordinate index needs — the piece tick 208
isolated. `[Hand-verified + Proved-by-page-read for the birth-corner value]`

## 7. Codex decorrelation (hypothesis withheld; independent derivation)

`[OBS]` Given only Aoyagi's chart structure (my verdicts withheld), Codex (xhigh) independently
derived, by its own algebra: (1) **YES** — every `u_{s,k}` stays in one immutable slot for life;
(2) a per-transition table agreeing on all six transitions (Case-1(1) pivot keeps its slot; Case-1(2)
`u'_{s,k}` stays at the old slot, new divisor at the corner; Case-2 corner birth; rollover/Q/P touch no
`u`-slot); (3) new-divisor slot `= (S,J+1,J+1)` (1-indexed) = my `(S,J,J)`; (4) **not** reconstructible
from `(T,M)` — its own across-leaf witness at `M=(2,3,2)`; (5) a **single immutable per-divisor
carrier field, set at birth, no dynamic update** — verbatim my §6. Two independent derivations agreeing
to the component. *Correction logged:* Codex's `(2,3,2)` hand-arithmetic slipped on the Case-2 exponent
(it wrote `codim−1=1` where `(M(1)−J)(M⁽²⁾−J)=(2−1)(3−1)=2`), so its witness exponent is off; my exact
sim confirms the SAME phenomenon at `(2,3,2)` lands at `(T=(1,0),M=4)` (corners `(1,1,1)`/`(2,0,0)`),
and my clean primary witness is `(2,2,2)` `(T=(1,0),M=3)`. The structural convergence stands; the
arithmetic detail is corrected by the battery, not the page-read.

## Close

- **Firmest (Proved-by-page-read + Hand-verified):** every divisor occupies its immutable birth corner
  `(s_birth, J_birth, J_birth)` for its whole life; births write a fresh diagonal corner, no later
  substitution relocates a divisor; mechanism = one immutable per-divisor field (= real `divCoord`),
  maintenance by congruence.
- **Most likely to break it (the watch):** the ledger's `divProfile` does NOT determine the slot
  (θ-multiplicity), so any coverage/`divCoord` step that tries to *derive* the u-pivot slot from the
  current profile is unsound — the field MUST be threaded as state. A formaliser should also not assume
  node-local `(S,J,J)` for the Case-1(1) center's `u` (100% wrong at merges); it is the chosen divisor's
  BIRTH corner, read off the carried field.
- **Next construction/consult that settles the open part:** none for this truth-value — it is closed.
  The one owed downstream piece is t05's: populate `divCoord`/`divBirthCoord` at the two birth cases
  (`= (layer, cleared, cleared)`), carry it through the `stepUpdate` index re-indexing, and discharge
  `divCoord` injectivity from "births at distinct diagonal corners" (§4's 0-collision fact). That is a
  bounded, banked-shape build; no further paper adjudication is needed.
