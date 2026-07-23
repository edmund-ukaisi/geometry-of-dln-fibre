# Consolidated ruling — the faithful carried invariant (elder-standing, 2026-07-23)

> GATE: this ruling gates ALL bakes and ALL descended-slot consumption. Task #40.
> Method (operator directive, binding): PAPER-FIRST. Each ruled point LEADS with Aoyagi's own text
> (worked.tex, materialised from branch HEAD); the candidates are judged as TRANSCRIPTIONS of her
> invariant, not as designs. Decorrelated Codex read (xhigh) on both fidelity claims banked at
> `threads/L4-case1-core/codex/carried-invariant-fidelity-{prompt,answer}.md` — all four sub-claims
> CONFIRMED, with one load-bearing refinement (§FIELD) preserved.

## 0. The finding in one paragraph

The baked carried invariant `FoldStepInvAt` (MonumentAtlas:590–595), through `supportAt`
(:572–575) and `Deg1SupportedSlot` (:544–549), UNDER-TRANSCRIBES Aoyagi's stage-`(S,J)` inductive
invariant (worked.tex:562–577) in exactly two places, and BOTH are transcription gaps of
paper-resolved content — not new mathematics:
- **(i) SUPPORT too tight.** Her residual block `D_J` is `(M(S)−J) × (M^(S+1)−J)`: the running min
  `M(S)` governs the ROW / cleared-prefix axis, and the COLUMN axis is the **raw** next-layer width
  `M^(S+1)−J`. The Lean caps that column axis at the running min `widthMinUpto(S+1)`. On a wide
  branch (`d_{S+1} > min(d_0..d_S)`) the cap is strictly tighter than her block, and the residual
  genuinely reads the out-of-cap columns. Fix: the descended support is `layerCoords(S+1)`, her raw
  block, not `blockCoords(S+1)`.
- **(ii) FORM too weak.** Her invariant carries `diag(b_1,…,b_{M(S)})` with `b_i` explicit monomials
  in the exceptional coordinates and `b_1 | … | b_M` by construction. The case-1(1) reuse step is
  "the `d`-block `= u_{s,k}·d'`" — a genuine **factoring** of the residual by the reused divisor's
  exceptional coordinate. The Lean records only `resid = ∑_{i} c_i·u_i` with `c_i` CONTINUOUS — no
  factoring. That is insufficient for the case-11 boost split (Codex: continuity-only cannot yield
  the boost split; `hslot` counterexample `F = u_q`).

Both defects live in the SAME baked object and MEET at the reused divisor's earlier descended clear
(the intro obligation rides the descended shape). Ruling: **FORK (B) — one coordinated re-bake that
fixes both**, at the faithful (weakest-that-inducts) shapes below. (A) patches the free-standing
form and leaves the construction under-transcribed; (C) abandons `∀e`-honesty. Neither is faithful;
(B) is Aoyagi's own induction data, transcribed.

---

## 1. SHAPE — the descended support is her raw residual block `layerCoords(S+1)`

### Her text (worked.tex:562–577), on a wide instance
> `M(S)=min{M^(s):1≤s≤S}`. The recursion maintains, indexed by `(S,J)`,
> `⟨∏C^(s)⟩ = ⟨diag(b_1,…,b_{M(S)})·[[E_J,0],[0,D_J]]·∏_{s=S+1}^L C^(s)⟩`,
> where **`D_J` is the `(M(S)−J)×(M^(S+1)−J)` residual block** … When `J` reaches
> `M(S+1)=min{M(S),M^(S+1)}` the layer is done and `S` increments.

Read on a wide instance `d=(2,3,2,2)`, clear layer 0, descend to layer 1. Her `M^(2)`-side column
axis of `D_J` is the **raw** width `M^(2)=d_1=3`; the running min `M(S)=min(d_0,d_1)=2` is applied
to the OTHER (row / cleared-prefix) axis and to the stopping value of `J`, never to the column side
of the block currently being resolved. So her residual block spans **all three** layer-1 columns.
Theorem 3's step (worked.tex:451–458) confirms she does **not** dispose of the wide remnant rows
before descent: `Q''_1` clears only the bottom-left `F'_3`; the Schur complement
`C^(S+1)=−A'_3 A'_1^{-1} A'_2 + A'_4` and the residual carry forward at the raw width. The remnant
rows stay live and are read — exactly the INHERENT arm pnp-transport found (the residual reads the
out-of-cap column with NO recoord, under any pivot, via `coreGen`'s wide-remnant-row cross-term).

### The Lean object (MonumentAtlas)
`blockCoords d ℓ` (:556–558) caps the flat-col at `widthMinUpto d ℓ`; its docstring (:551–555)
asserts "the residual block is `widthMinUpto`-capped … matches `canonCenterOf`'s cap." **That is
the transcription error, stated in the docstring.** It conflates two distinct objects Aoyagi keeps
distinct (and which the `supportAt` docstring at :569–570 even declares distinct):
- the **blow-up CENTER** at the current step (`canonCenterOf`), which is the block being blown up.
  Its running-min-capped axis is FAITHFUL — Aoyagi's `D_J` center has one axis at `M(S)` (running
  min) and one at raw `M^(S+1)`, and `canonCenterOf` correctly caps one axis and leaves the other
  raw. The center is NOT too tight.
- the **descended RESIDUAL support** the cofactor `C'^(S+1)=Q⁻¹·C^(S+1)` reads after the clear.
  This is the NEXT factor at its raw width `M^(S+1)`, one layer deeper than the center. `supportAt`
  borrows the center's cap for this too — and that is wrong on a wide branch.

`supportAt d S J` (:572–575): `J=0 → blockCoords d S`; `J≥1 ∧ S+1<N → blockCoords d (S+1)`;
else `∅`.

### Ruling — candidate (a) WIDEN, on the descended branch only
**Adopt (a): the descended (`J≥1`) support is `layerCoords d (S+1)`.** This is Aoyagi's raw
residual block, not a design choice. Candidates (b) REMNANT (cap ∪ escape account) and (c)
THROUGH-RECOORD (support in the `N_p`-image frame) are REJECTED: they preserve a cap that Aoyagi's
residual block never had. (b) is a redundant re-derivation of a set that is simply the full layer;
(c) bets on a recoord-confinement that is false (the escape is inherent, recoord-independent).

**The `J=0` branch stays `blockCoords d S` — do NOT widen it.** At `J=0` the residual's support IS
the block being blown up (= the center), so it correctly carries the center's cap; and
`realBranch_cover` (`supportAt ⊆ ed.center` at `cleared=0`) depends on it. The empirical table
confirms both: root node in-cap, every descended node out-of-cap. The single-line def edit is the
descended branch: `blockCoords d (S+1) → layerCoords d (S+1)`. **`blockCoords` survives** as the
center's cap object — do not delete it.

### Evidence
- Codex xhigh, CLAIM 1: **CONFIRMED (FACT)** — "`D_J` has dimensions `(M(S)−J)×(M^(S+1)−J)`; the
  running minimum controls the row/cleared-prefix side and the stopping value of `J`, while the
  column side retains the raw next-layer width `M^(S+1)−J`."
- Empirical (exact sympy, exit-0): `empirical_invariant_table.py` — every descended node on
  `(2,3,2,2)` has layer-1 support `{0,1,2}` incl. out-of-cap col 2; `recoord_cap_escape.py` — the
  inherent remnant-row read, recoord-independent. `(2,2,2,2)` (non-wide) coincides with the cap —
  why the defect hid.
- Consumer interlock: L3T2's one load-bearing UNKNOWN (does any consumer need the S+1 cap?) resolved
  NO by L4D's scope check (`boostReady` reads layer-`S` + the earlier reused pivot, never the
  descended `S+1` slot) ⟹ widen is consumer-safe. Paper-first now makes it not merely safe but
  faithful.

### Predecessor's cap-escape flags — dispositions
- **fix-β (row-cap the fan to the live square) and fix-γ (recoord-image subspace): both RETIRED.**
  Superseded twice over: the read-side INHERENT arm (remnant-row read escapes with no recoord, any
  pivot) already killed fix-β; and paper-first shows there is no cap to preserve — the residual block
  IS wide. The predecessor's interim preference is formally retracted.
- **fan/slot coupling observation: RETIRED as the escape diagnosis** (the escape is not a fan
  artefact — it is inherent to the wide block). The REAL coupling (shape ⟂ field meet at the
  descended clear) is kept, §3.
- **pnp-fan live-square cover sub-question: RETIRED as a gate.** With fix-β dead the support widens
  regardless, so "does the cover need pivots outside the live square" no longer gates the shape. The
  cover DOES use interior pivots and they monomialise (npivot-certificate §4a, settled); not
  load-bearing here.

---

## 2. FIELD — the coherent product factoring in the running chart frame

### Her text (worked.tex:570–571, 598–601, 609–618)
> `b_0=1`, `b_i=(∏_{t̃_{s,k}=i−1} u_{s,k}) b_{i−1}` … unrolling `b_i=∏_{t̃_{s,k}<i} u_{s,k}`, whence
> `b_1|b_2|…|b_M` by construction.
> Case 1(1): **the `d`-block `= u_{s,k}·d'`** sets `t̃_{s,k}=J` and adds `M'_{s,k}=…`.

Her carried object is the `diag(b)` normal form with `b_i` an explicit PRODUCT of exceptional
coordinates. The reuse step is a literal factoring `d = u_{s,k}·d'` in the local ring. The vanishing
the wall needs is not a value-locus fact; it is this factoring.

### The Lean object + the wall
`Deg1SupportedSlot` (:544–549): `∃c, (∀i, ContinuousOn c_i) ∧ resid = ∑_{i∈S} c_i·u_i` plus the
per-layer degree bound. Continuity-only. The wall `realBranch_boostReady_case11`
(Case1Wire:386–395, SORRIED) must re-express the residual — supported on the larger layer block —
onto the SMALLER boost center `ed.center = {pivot} ∪ partialBlock`, which needs the untouched
`support ∖ center` coefficients to carry `u_pivot` (the docstring already says so: "carry `u_pivot`
in their non-dominant b-chain coefficient `b_i/b_1`"). The case-12/case-2 cover route
(`deg1SupportedOn_center_of_hslot`, PROVEN) needs no field because there `support ⊆ center` (padding
UP); case-11 is the reverse (contracting onto a smaller center) — that is why it, and only it, needs
the field.

### Ruling — the coherent product FACTORING, running-frame-pinned
The field is a NEW conjunct on the carried invariant: for each active divisor `k`, the extra-block
coordinates (col `≥ t̃_k`) of the residual factor as

    c_i(u) = m_k(u) · β_i(u),   m_k = the b-chain monomial in the active exceptional coords,  β_i continuous,

i.e. Aoyagi's `d`-block `= u_{s,k}·d'`, carried coherently as the product `diag(b)` structure — NOT
as a conjunction of isolated per-divisor value-vanishings, and NOT as a continuity-only `∃c`.

This is a CORRECTION to seat-L4D's candidate labels. "Form V (value/vanishing)" as *pure vanishing
on `{u_pivot=0}`* is REJECTED — too weak: for continuous coefficients, vanishing on a hypersurface
does not give a continuous quotient (no factoring). "Form S (structural)" is adopted **in its
factoring content** — the coherent product `m_k·β_i` — but the numeric exponent ledger `M_{s,k}` is
NOT carried in the slot (it is combinatorial, lives in the already-banked Objects C/D; npivot §3).
So the ruled field = Form S's product STRUCTURE, minus the ε-transport numeric ledger. This is the
weakest form that inducts.

**Frame (mandatory, stated IN the field).** The divisor coordinate whose factor the field names is
the exceptional coordinate in the node's RUNNING (post-Schur) chart frame — the value `foldResid`'s
argument actually holds after the shears — NOT the literal root-frame birth corner. On `(2,2,2,2)`
this is the Schur-reduced `e_2 = u_{011} − u_{010}·u_{001}` read at the birth-corner slot, not
`u_{011}`. Because `foldResid` composes through `pathMap`, its argument is already in the running
frame, so naming "the coordinate at divisor `k`'s birth-corner slot, in `foldResid`'s argument"
is frame-correct — but the STATEMENT must pin this (it is the exact ambiguity class that hid the
cap-escape and the earlier unfaithful-shear). A field stated in the root frame names the wrong locus.

### Evidence
- Codex xhigh, CLAIM 2a: **CONFIRMED (FACT)** — "`d=u_{s,k}d'` is genuine factorization in the local
  function ring … Mere vanishing on `u_{s,k}=0` is insufficient for continuous coefficients because
  it need not provide a continuous quotient."
- Codex xhigh, CLAIM 2b (the refinement to PRESERVE): per-divisor divisibility conjunction is the
  weakest encoding **only in the analytic/polynomial setting** (distinct exceptional params prime ⟹
  divisibility-by-each ⟹ divisibility-by-product). "This equivalence FAILS for merely continuous
  functions; moreover, dividing out one factor need not preserve the others, so a continuous
  formalisation needs COHERENT PRODUCT FACTORIZATION, not isolated divisibility witnesses." → the
  field must be the product `m_k·β_i`, matching Aoyagi's `diag(b)`. "The exponent ledger `M_{s,k}` is
  unnecessary for the reuse factorization itself but remains necessary for the final
  learning-coefficient exponent calculation" (⟹ not in the slot; in Objects C/D, banked).
- Codex xhigh, CLAIM 2c: **CONFIRMED** — `u_{s,k}` is the exceptional parameter in the current
  (post-Schur) chart; naming the literal root coordinate identifies the wrong locus.
- Empirical §3: the extra-block coeffs carry the Schur pivot `e_2` in the running frame (faithful
  `N_p`), absent under the old `canonShearOf` (the `F=x+yz` countermodel) — the frame-dependence,
  node-explicit.
- Independent-of-hedge: seat-L4D PART 1 showed the SUPPORT defect is FORCED regardless of the b-chain
  hedge; Codex confirmed `hslot` cannot yield the boost split. Both defects are forced; the hedge is
  RESOLVED (re-bake both). PerLayerDeg1From SURVIVES node-by-node (empirical (3)) — the degree
  conjunct (clause-2) is UNCHANGED; the re-bake's blast radius is clause-1 (support) + the new field.

### §7 ε-table col-a flag (predecessor) — disposition
With the support widened to `layerCoords(S+1)`, the field's factoring ranges over the full layer
incl. the out-of-cap column, so the col-a term is accounted by the widened support + coherent
factoring. The NUMERIC `chainWeight`/`M_{s,k}` ledger (the ε-transport) is NOT in the slot and is
untouched (npivot §3: b-chain/`M` combinatorial, `N_p` det-1). Flag RESOLVED.

---

## 3. COUPLING — the field's intro rides the reused divisor's descended clear

Shape and field are orthogonal axes (shape = which coordinate set in clause-1; field = the factoring
conjunct), and they are one JOINT re-bake because they meet at exactly one place: the field's INTRO
obligation. A divisor is born at a case-12/case-2 clear (a DESCENDED state); its factoring is
introduced there, over the descended support — which is now the WIDENED `layerCoords(S+1)`. So the
intro must be STATED over the ruled (widened) shape. seat-L4D confirmed the meet point:
`boostReady`'s read/conclusion are same-layer (layer `S`), but the field's intro rides the reused
divisor's earlier descended clear. One coordinated re-bake, not two.

---

## 4. The minimal re-statement set (the bake plan the gate authorises)

DEF edits (2):
1. `supportAt` (MonumentAtlas:572–575): descended branch `blockCoords d (S+1) → layerCoords d (S+1)`.
   `J=0` branch and `blockCoords` itself UNCHANGED.
2. The FIELD conjunct on `Deg1SupportedSlot` (:544–549) or `FoldStepInvAt` (:590–595): the coherent
   product factoring on extra-block coords (col `≥ t̃_k`), running-frame-pinned. Exact Lean shape is
   the seat's (arch-C / seat-L4D) to render; the field records, per active divisor, `c_i = m_k·β_i`
   with `m_k` the b-chain monomial and `β_i` continuous. Clause-2 (`PerLayerDeg1From`) UNCHANGED.

Consumers (mechanical thread of shape + field; per the L3T2 consumer grid):
- SHAPE-widen (clause-1 → `layerCoords(S+1)`): `realBranch_appendResidDescent`,
  `realBranch_multiAffine_step(')`, `descent_delta1_append`, `descent_delta0`,
  `case1_preserves_stepInv(')`, `case2_preserves_stepInv(')`.
- FIELD-thread (new conjunct through `hinv`/conclusion): the same list + `descent_delta1_case11`.
- UNCHANGED on shape (verify field threads vacuously): `deg1SupportedOn_center_of_hslot`
  (cover route — `support ⊆ center` at `J=0`, unaffected), `realBranch_cover`, the L3T
  homogeneity lane (reads `layerCoords` already — shape-insensitive), the L5 base
  (`blockCoords(0)=layerCoords(0)`, field vacuous at root `b_0=1`), lastLayer/terminal (support `∅`).

The PAYOFF (why the re-bake earns its cost): `realBranch_boostReady_case11` (Case1Wire:386) becomes
PROVABLE — the field's factoring on the extra block is exactly the boost split
`∑_{partial} α·u_i + u_pivot·∑_{extra} β·u_i` the wall consumes. The intro + per-step preservation +
the L5 canonFlatten base are the genuinely-new proof content (Codex: the boost-form payload is
largely pre-built — `deg1SupportedOn_boostForm` is clean-three).

New proof obligations (the honest new work, all strike-able):
- INTRO: at a divisor's birth (`blockBlowupMap` multiplies center coords by `u_pivot`), the
  freshly-cleared extra coords gain the `u_pivot` factor — Aoyagi's `d=u_{s,k}·d'`.
- PRESERVE: through `blockBlowupMap ∘ N_p` the coherent factoring survives (recoord per-(S+1)-linear,
  det-1; npivot §2).
- BASE: L5 discharges the intro at the `canonFlatten` root (`∀e`-honest — false/vacuous for a
  scrambling `e`; Codex CLAIM 2b).

---

## 5. Acceptance battery (charter §3 def-fidelity gate — every battery MUST exercise the LEAN def AND a WIDE witness)

Witnesses: `(2,3,2)` (smallest wide) and `(2,3,2,2)` (smallest wide-with-descent). `(3,3,4)` is NOT
wide on the recoord/col axis (`d_1=3=widthMinUpto(1)`) — it does NOT exercise the escape; do not
accept a battery that uses only `(2,2,2,2)`/`(3,3,4)`/`(3,3,2,2)`.

- **SHAPE test (def-level).** Instantiate the ACTUAL Lean `supportAt` + `foldResid ∘ pathMap` (the
  real composition, not a sympy hand model) at a descended node on `(2,3,2,2)`; confirm the residual
  reads the out-of-cap column, so `layerCoords(S+1)` is necessary and `blockCoords(S+1)` is FALSE.
  (seat-L4D's both-sides def-trace + `empirical_invariant_table.py` are the pen-and-paper half;
  the Lean-def half is the gate — a `#eval`/scratch on the baked def, or L4D's def-trace against
  the baked `supportAt`.)
- **FIELD + FRAME test (def-level).** At a case-11 reuse node on the wide witness, trace the baked
  `foldResid` (through the actual `canonNormalizationOf` (ii) recoord, MonumentAtlas:877–882 — NOT a
  hand shear) and confirm the extra-block coefficient factors as `u_pivot·β` where `u_pivot` is the
  running-frame exceptional coordinate; confirm the SAME statement in the root frame names the wrong
  locus (the battery must be able to FAIL on the frame error). `honest_clear_2222.py` has the
  running-frame `e_2` factoring; the gate needs the wide + baked-def version.
- **Regression.** `PerLayerDeg1From` unchanged — re-confirm degree-2 on the cleared layer below
  support, degree-1 from `supportLayer` up (empirical (3)).

A battery that traces only a faithful HAND model green-lights the intended MATH over a possibly-wrong
ENCODING — the worst failure (charter §3). The kill-battery must consume the baked object.

---

## 6. Verdict

- **Both defects: CONFIRMED at the def, paper-first, decorrelated (Codex xhigh, all four sub-claims).**
- **SHAPE: (a) WIDEN the descended support to `layerCoords(S+1)`** — Aoyagi's raw residual block.
  `J=0`/`blockCoords` unchanged. fix-β/γ, fan/slot-escape-diagnosis, live-square sub-question RETIRED.
- **FIELD: the coherent product FACTORING `c_i = m_k·β_i`, running-frame-pinned** — Form S's product
  structure, minus the numeric `M_{s,k}` ledger; pure value-vanishing rejected (Codex 2a/2b). §7
  col-a flag resolved.
- **FORK (B): one coordinated re-bake** (shape + field meet at the descended-clear intro). (A)/(C)
  rejected on mathematical-necessity grounds (patch-the-universal / abandon-`∀e`).
- The minimal re-statement set (§4) + the WIDE-witness, LEAN-def battery (§5) are the authorised bake.
- Nothing outside §4 changes; `PerLayerDeg1From` and the numeric b-chain/`M_{s,k}` ledger (Objects
  C/D) are UNTOUCHED. Payoff isolation holds. **The gate LIFTS for bakes conforming to §4–§5.**
