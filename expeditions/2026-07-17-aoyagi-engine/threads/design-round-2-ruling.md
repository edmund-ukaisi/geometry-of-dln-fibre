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

**The hedge is CLOSED — (B) is forced with no escape branch (banked after this ruling opened;
confirms, does not reopen).** pnp-transport modeled a scrambling `e` exactly (validated against the
`Fbad` kill-witness): on `(2,2,2,2)` it produces at the boost parent the monomial `u₂₀₀·u₁₀₁²` —
degree 2 in a single extra-block coordinate, **in the base `coreGen_e`** (upstream of any shear, so
recoord-encoding-independent). BoostSplit needs degree-1 in the layer-1 extras and the recoord is
layer-1-linear, so this is irreparable: the `∀e` wall statement is **FALSE, not merely unprovable**;
the `canonFlatten` base pin is NECESSARY and the b-chain field is STRICTLY necessary (no unfolding
route exists). This resolves in the negative the one open branch (Codex's §4 "plausible but
unverified", the predecessor's hedge). The re-bake stands with no escape;
`threads/L4-case1-core/scrambled-e-hedge-note.md` + `verify/scrambled_e_hedge.py` (exit-0).

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

**Frame (mandatory, stated IN the field) — AMENDED after seat-L4D's def-verification.** seat-L4D
verified at the def (`foldG_eq_pathMap` + `pathMap_append`, MonumentAtlas:391–399): `foldResid`'s
argument `u` is the DEEPEST / node-`p` chart frame, **PRE the path's shears** — the shears are
applied on the way DOWN to `coreGen` (the root frame). So the reused divisor's Schur exceptional,
in `foldResid`'s argument frame, is a **CONTINUOUS COMBINATION** `e₂ₖ(u)` — on `(2,2,2,2)`,
`e₂ = u_{011} − u_{010}·u_{001}` — **NOT the bare birth-corner coordinate** `u_{011}` (which is the
root-frame single-coordinate reading, the WRONG locus in the node frame). The factor `m_k` in the
field is therefore the product of the active divisors' Schur exceptionals **as native-frame
combinations**. This MUST be pinned in the statement — it is the exact ambiguity class that hid the
cap-escape and the unfaithful shear; a field stated with a raw birth-corner coordinate names the
wrong locus. (This corrects a "post-shear" mis-statement in the pre-verification draft of this §.)

**Precision — the factoring supersedes the per-divisor vanishing conjunction.** seat-L4D's
recommended "Form V" is a per-divisor VALUE-VANISHING (`∀u, e₂ₖ(u)=0 → c_i u = 0`) conjoined over
active divisors. That is NOT the ruled form: (a) pure value-vanishing gives no continuous quotient
(Codex 2a); (b) a conjunction of per-divisor vanishings does not compose for continuous coefficients
— a coordinate that is "extra" for two divisors `f,g` would need `c_i` divisible by both `e₂_f` and
`e₂_g`, and two continuous factorings `c_i=e₂_f·β_f=e₂_g·β_g` do NOT yield `c_i=e₂_f·e₂_g·β` (Codex
2b). The invariant must therefore carry the COHERENT PRODUCT directly:
`c_i = (∏_{active k: t̃_k ≤ col(i)} e₂ₖ) · β_i` — Aoyagi's `diag(b)` monomial, transcribed. For
polynomial coefficients this equals the per-divisor vanishing (each `e₂ₖ` is irreducible ⟹ prime),
but the carried object is the product, not the vanishing family.

**Coords-of-record ruling — F-value (native frame), NOT F-frame (recoord).** The exceptional is a
coordinate in Aoyagi's per-chart recoordinatized frame (her `b`'s ARE coordinates because she changes
coordinates). Two faithful options, both priced by seat-L4D:
- **F-value (RULED):** state the field in `foldResid`'s native (pre-shear) frame, factor = the
  combination `e₂ₖ(u)`. COHERENT with the `(a)`-widen support (same frame, native coords); it is the
  VALUE-faithful transcription (the vanishing locus is frame-independent by Lemma 1 — Aoyagi's
  coordinate-frame is her representational choice, not a constraint on ours). PRICE: the banked
  `deg1SupportedOn_boostForm` carries a bare-coordinate pivot; its factor generalises to the
  combination `e₂ₖ` (or the boost split pre-expands `e₂ₖ` onto its center-constituent coordinates —
  validated on the witness, where boost-readiness is `(True,True,True)`). The seat picks the render.
- **F-frame (REJECTED):** state the field in the recoord frame where `e₂ₖ` is a coordinate. This
  forces `foldResid` through the recoord, which drags the SUPPORT clause into the recoord image =
  option `(c)` — the one I rejected (the escape is inherent; the recoord does not confine). Keeping
  the support native `(a)` while the field is recoord is a TWO-FRAME slot — the ambiguity-class
  hazard the def-fidelity gate exists to refuse. So F-frame is incoherent with the support ruling.
The field lives in ONE frame, `foldResid`'s native pre-shear frame, matching `(a)`-widen. Documented
as the coords-of-record decision (not a silent choice; compass F5).

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
  C/D) are UNTOUCHED. Payoff isolation holds. **The gate LIFTS for bakes conforming to §4–§5** — with
  the §7 prerequisite.

---

## 7. Prerequisite def-edit (3) — the UNPAIRED RECOORD (found by the §5 harness; the gate working)

pnp-transport's §5 harness — the first instrument transcribing the ACTUAL baked
`canonNormalizationOf`/`readEntry`/`blockEntryFlat` (MonumentAtlas:832–882), NOT a hand model —
found the baked def applies the deeper recoord (ii, `A_{S+1}·Q₁⁻¹`) UNPAIRED: branch (i)'s guard
excludes the pivot cross (`col ≠ b ∧ row ≠ a`), so the pivot-column clearing `Q₁·A_S` (worked.tex:453
`Q''_1` "to clear the bottom-left"; npivot-certificate §1 "`row/col→0`") was DROPPED in the render.
The recoord without its paired clearing does not cancel — it DOUBLES: on `(2,2,2,2)`,
`(A_1·A_0)[0][0] = u₁₀₀ + 2·u₀₁₀·u₁₀₁`, which in the running-chart frame is `w₁₀₀ + u₀₁₀·u₁₀₁` — a
leftover whose extra-block coord `u₁₀₁` carries `u₀₁₀` (the `F=x+yz` defect coord), NOT the pivot.
The triangle: full-clear → 0 (boost-ready); `canonShearOf` (no recoord) → coeff 1; baked (recoord,
no clear) → coeff 2 (strictly worse). Banked: `threads/L4-case1-core/faithful-harness-note.md` +
`verify/faithful_lean_harness.py` (exit-0), seat-L4D adjudicating at the def.

**This does NOT touch §1 (SHAPE) or §2 (FIELD) — both are paper-anchored.** It is one level below:
whether the baked `canonNormalizationOf` faithfully implements the certificate's `N_p` the N_p bake
was ratified against. But it is a PREREQUISITE for the ruled field to be TRUE on the baked def — the
field asserts the extra-block coeff factors by the reused divisor's exceptional; on the current
(unpaired) def it factors by `u₀₁₀` (a non-pivot coord), so the field's INTRO is UNPROVABLE. So this
is not optional and not merely additive.

**GATE RULING — STAGED on seat-L4D's def-level verdict (term-by-term vs certificate §1, BOTH
directions incl. harness mis-transcription):**
- **IF a genuine def gap AND the pivot-cross clearing is representable as a (pre-quotient) shear
  displacement in the current fold order** (`blockBlowupCoordQuot ∘ edgeShear`): the recoord-completion
  (extend branch (i) to the pivot cross so `A_{S+1}·Q₁⁻¹` is paired with `Q₁·A_S`) is AUTHORISED
  within this re-bake as fidelity-restoration — making the baked def satisfy npivot-certificate §1.
  It is def-edit (3), rides the same re-bake, my delta-read covers all three.
- **IF the clearing is NOT cleanly representable** — the harness's own caveat: Aoyagi's
  `γ = A_S[row][b]/A_S[a][b]` needs the pivot INVERTED (a division, not a polynomial displacement),
  and the fold order sets pivot→1 only at the quotient AFTER the shear — then this is a FOLD-ARCHITECTURE
  question (a SKELETON REVISION), **NOT within the re-bake and NOT mine to wave through: it returns to
  the elder (route-adoption gate), and to the operator if it moves the definition of done.** Do NOT let
  def-edit (3) become a silent fold redesign under the "fidelity-restoration" banner.
- **EITHER way, seat-L4D re-verifies the N_p BAKE's OWN ratified claims on the COMPLETED def**, not
  only on the certificate: ideal-preservation / `StepInv` (the unpaired recoord means the baked step
  is `A_{S+1}·Q₁⁻¹·A_S`, not `A_{S+1}·A_S` — does it still preserve `⟨∏C⟩`? — check by Gröbner
  ideal-equality, NOT coefficient-matching, per compass F4), monomialisation (block `= u·unit`), and
  `M_{s,k}` preservation. This is the THIRD instance of the same gap — the N_p ratification (task #26)
  verified the CERTIFICATE's `N_p`, not the BAKED encoding; identical in class to the cap-escape
  (ratified value/Jacobian, not support) and the original unfaithful shear (hand model had `Q₁⁻¹`, def
  did not). The §5 harness-transcribes-the-baked-def discipline is exactly the fix, and the charter §3
  gate now mandates it at every bake — but the N_p bake's monomialisation/`M` claims must be
  re-confirmed on the completed def before any downstream leans on them.

def-edit (1) (SHAPE widen) is INDEPENDENT of this verdict (the support-set widen does not touch the
recoord) — arch-C proceeds on it. def-edit (2) (FIELD) + the INTRO/PRESERVE/BASE frontiers HOLD until
the recoord verdict lands (the field is not true until the pairing is in the fold). Correct sequencing.

---

## 8. FINALIZATION — the verdict landed; §2's FIELD is RETRACTED; §7 resolved by R3 (recoord direction)

The council-of-two (elder + Codex xhigh, `codex/invariant-shape-council-answer.md`) has convened and
CONVERGES with worked.tex and both instruments (pnp-transport, seat-L4D). The crisis resolves cleaner
and smaller than §7 feared. Supersedes §2's FIELD and §7's staging.

**(a) The recoord DIRECTION (R3) — the whole fix, faithful.** The baked `canonNormalizationOf`
branch (ii) had the WRONG inverse: `A_{S+1}·Q₁⁻¹` (`+γ`) DOUBLES the uncleared cross-term; the
correct `A_{S+1}·Q₁` (`−γ`) CANCELS it, clean, unipotent. Codex Q1 CONFIRMED the direction against
worked.tex:445: Aoyagi's `A'=R⁻¹A` is old-to-new; the chart substitution is `A=RA'` (new-to-old);
reversing/transposing the product turns her left-mult into a right-mult, giving `Ã=Ã'·Q₁` — the
apparent inverse in the N_p certificate §1 was an old-to-new/new-to-old confusion, NOT a real inverse.
So R3 is a single-branch sign flip, manifestly unipotent, and it is the FAITHFUL realization of
Aoyagi's clearing (achieved ideal-level on the deeper factor, F1-consistent — no rank-reducing
coordinate clear). **R4 (generator-transform component) STANDS DOWN** — R3 achieves the clean form
directly and is far smaller.

**(b) The invariant SHAPE — Reading B (CLEAN), §2's FIELD RETRACTED.** Codex Q2 (FACT, "not genuinely
ambiguous"): the invariant `diag(b)·[[E_J|D_J]]` keeps the exceptional monomials in the EXTERNAL
row-weight ledger, NOT inside `D_J`; Case-1(1)'s `d=u_{s,k}d'` is the transient blow-up-chart
substitution, absorbed into the b-chain before the invariant is carried onward — not a divisibility
condition on the normalized residual. worked.tex:619-620/628-629 confirms: the regular `Q,P` reduce
each step to `[[1,O],[O,D_{J+1}]]` (the clean block). So `foldResid` = the CLEAN residual `D_J`;
`foldB` = the external b-ledger (already carries the exceptionals, incl. the reused divisor's). **§2's
FIELD conjunct — in BOTH the additive `∃c`-factoring form I first ruled AND the `m_k·β` product — is
RETRACTED.** It was fitted to the broken def's coeff-2 additive symptom; the exceptional the wall needs
lives in `foldB`, not inside the residual. My earlier Codex read (`carried-invariant-fidelity-answer`
§2a/2b) confirmed a factoring premised on the residual carrying extras — that premise was the broken
def; with R3 the residual is clean and the premise dissolves.

**(c) BOOST-READINESS is DIRECT — no internal field.** Codex Q2 (INFERENCE): boost-readiness follows
from the separated normal form — partial-block rows contribute a center coordinate from the clean
`D_J`; complementary rows acquire the reused exceptional from their EXTERNAL `b_i` (in `foldB`). No
hypothesis that extra-block coefficients INSIDE `D_J` factor by the exceptional. So the 11th "form too
weak" catch DISSOLVES: `realBranch_boostReady_case11` is proved from the clean residual + the existing
`StepInv`/`foldB` ledger, not a new carried field. **DEF EDIT 2 is NOT a field conjunct** — it is
`Deg1SupportedSlot` over the CLEAN (Reading-B) residual, the b-chain staying in `foldB` where it
already is. Simpler than V or S; her literal normal form.

**(d) The crisis is BOUNDED — no monument reopening, no operator escalation.** Both instruments concur
(pnp `recoord-ideal-matched-note.md`; seat-L4D): the baked fold is a globally invertible polynomial
automorphism (det-1, structurally triangular) ∘ proper blow-ups, so the RLCT VALUE was NEVER at risk
and the resolution is VALID ("valid-but-different presentation"); `⟨baked⟩≠⟨faithful⟩` as ideals but
by an INVERTIBLE change, RLCT-preserving. What genuinely FAILS is MONOMIALISATION (the baked residual
is `[[1,β],[γ,e₂]]`, not `diag(1,e₂)`) — and the fix is required for the PROOF VEHICLE (the `M_{s,k}`
ledger reads the value off the monomialised block), NOT for soundness. So §7's escalation-to-operator
branch does NOT fire; R3 is a contained def sign-flip within the re-bake.

**(e) pnp's R5 (restate to the non-diagonal unit-det block, prove termination without clearing) —
REJECTED as UNFAITHFUL.** worked.tex:619-629 shows Aoyagi REDUCES to the clean `[[1,O],[O,D_{J+1}]]`
each step (via the regular `Q,P`); she does NOT carry a non-diagonal block. R3 reproduces her clean
reduction via the invertible recoord; R5 would carry a block she never carries. Her open-fact (non-diag
termination) is MOOT for the faithful route. (F5: Aoyagi is the touchstone — reproduce her choice.)

**(f) honest_clear vs R3-flip — likely NO real disagreement.** honest_clear's "extras carry e₂" is
`e₂`-as-a-COORDINATE-of-the-clean-block `D_{J+1}` (the Schur coordinate), not `e₂`-as-the-defect; R3-flip
removes the DEFECT leftover `u₀₁₀·u₁₀₁`. Both give the clean block. The object-labeled reuse-node forms
confirm this reconciliation.

**(g) TWO DISTINCT AXES — correcting an over-claim in (a)/(e).** I conflated two properties, and
"R3 is the whole fix / R4 stands down" was premature. They are separate:
- **PRODUCT / BOOST-READINESS axis** (`foldResid` supported on the center): R3 (the recoord direction)
  resolves it — Reading B, field retracted, boost-readiness direct. (a)-(f) STAND for this axis.
- **BLOCK / MONOMIALISATION axis** (`D_J = [[1,β],[γ,e₂]]` → `diag(1,e₂)`, which the `M_{s,k}`
  normal-crossings read-off needs): boost-readiness (support on center) is a DIFFERENT property from
  block-diagonality (off-diagonal `β,γ = 0`); a residual can be boost-ready with a non-diagonal block.
  R3 acts on the `A_{S+1}` side; the block's `γ` is on the `A_S` side, so R3 may leave the block
  non-diagonal. WHETHER R3 alone diagonalises the block, or an ADDITIONAL generator transform is
  needed, is the block-form-under-R3 question (seat-L4D producing).
- **PAPER-FIRST FRAME:** Aoyagi DOES reach the block-diagonal `[[1,O],[O,D_{J+1}]]` each step
  (worked.tex:619-629), and the FULLY diagonal terminal form is where `M_{s,k}` is read off
  (worked.tex:574-575, 668-676) — via INVERTIBLE regular `Q,P` (row/column operations = Gaussian
  elimination on the entry). That is a GENERATOR transform (unipotent, det-1, NOT rank-reducing) — my
  F1 point again. seat-L4D's "clearing is rank-reducing (jacDet 0)" was about clearing a COORDINATE
  (setting a variable to 0); clearing a matrix ENTRY via row/col ops is unipotent. So the block
  diagonalisation IS achievable — **via R4 (the generator transform `Q·block·P`), which is therefore
  NOT stood down**: it is the block-diagonalisation mechanism IF the block-form-under-R3 shows the block
  stays non-diagonal. Both R3 and R4 are CONTAINED + G1-clean (established), so EITHER WAY (R3 alone, or
  R3 + R4) is within the re-bake with NO escalation. pnp's R5 (carry the non-diag block) stays REJECTED
  — the diagonal is reachable via R4, so there is no need to carry a block Aoyagi never carries.

**Status: the BOOST-READINESS/FIELD axis is FINALIZED (Reading B, R3, field retracted, bounded); the
BLOCK/MONOMIALISATION axis is PENDING the block-form-under-R3 data.** Confirmation battery (paper-first):
(1) seat-L4D — the block form under R3 (does R3 diagonalise, or is R4 also needed?) + the worked.tex:445
direction cross-check + the `foldB` def-fact; (2) pnp — the object-labeled reuse-node forms (both wide
witnesses; clean-block vs b-scaled) + the Gröbner triple on the R3-flipped def. RE-OPEN trigger: the
reuse-node residual not clean under R3 (product axis), OR the block not diagonalisable by R3+R4 within
the fold (block axis). The RLCT VALUE stays safe throughout (invertibility + combinatorial `M_{s,k}`);
the block axis is about the FORMAL normal-crossings read-off, not soundness — still bounded, no operator.
§1 SHAPE (widen) STANDS untouched; §2 FRAME/coords-of-record MOOT. DEF EDIT 2 = clean-residual
`Deg1SupportedSlot`, b-chain in `foldB`. The gate LIFTS for the product axis; the block axis's final
mechanism (R3 alone vs R3+R4) I rule when the block-form data lands.

**(h) The DIRECTION SUBTLETY (ii) — CRITERION ruled, mechanism gated on #49.** seat-L4D's battery
DEF-CONFIRMED Reading B: `foldB` (MonumentAtlas:402-406) carries the b's SEPARATELY, `StepInv` factors
as `∑ q·(b·resid)`, so `foldResid` IS the clean-block slot — my §2 retraction is now DEF-grounded (the
field put the b-factor in the WRONG SLOT, `foldResid` instead of `foldB`). The TWO-SIGN finding
vindicated the "not just `ed1[0][0]`" bar: flipping branch-(ii) alone leaves a defect at `[0][1]`;
DEF-EDIT-3 is TWO sign flips (branch-(i) Schur AND branch-(ii) recoord). The one OPEN question,
seat-L4D honestly deferred to me: is Aoyagi's clean-`D_J` mechanism the PRODUCT-PRESERVING recoord
(`Q'₂⁻¹` = recoord + paired column-clear, R4-like, = `honest_clear`) or the two-sign-flip (RLCT-safe
but possibly NOT product-preserving)?

**PAPER-FIRST RULING on the CRITERION (decisive, not ambiguous):** Aoyagi's invariant is an IDEAL
EQUALITY — `⟨∏C⟩ = ⟨diag(b)·[[E_J|D_J]]·∏C⟩` maintained EVERY step (worked.tex:565-567) — and the
`M_{s,k}` ledger reads off HER `diag(b)` (worked.tex:668-676). So her mechanism is necessarily
PRODUCT-PRESERVING (it maintains the ideal). The FAITHFUL criterion is therefore
**`⟨fold output⟩ = ⟨faithful⟩` as IDEALS** (Gröbner ideal-equality to her `diag(b)·[clean block]`
presentation) — NOT merely "the `ed1` entries are clean" (which a non-product-preserving sign-fiddle
achieves too, RLCT-safe via invertibility but the WRONG presentation, so the block does not monomialise
to her `diag(b)`). The council's Q1 gave the correct recoord DIRECTION (`A_{S+1}·Q₁`); product-preservation
requires it PAIRED with the column-clear (`Q₁⁻¹·A_S`) = the R4-like generator transform. R3-alone (recoord
only, no paired clear) is NOT her mechanism.

**THE DECISIVE TEST = #49** (Gröbner triple on the R3-flipped def): does `⟨R3-flipped⟩ = ⟨faithful⟩` as
ideals? IF YES → the two-sign-flip IS product-preserving = faithful; the block monomialises to her
`diag(b)`; DEF-EDIT-3 (two sign flips) is the whole block fix, R4 not separately needed. IF NO → the
two-sign-flip is RLCT-safe but not product-preserving; **R4 (the explicit paired column-clear, the
product-preserving generator transform) is the faithful block mechanism.** Either way CONTAINED +
G1-clean (no escalation); the RLCT VALUE is safe throughout. pnp's reuse-node forms (#50) confirm at the
reuse node (against the product-preservation criterion, NOT entry-cleanliness); the both-flipped block
corner `u₀₁₁ + γβ` (not the classical Schur) is read against the `e₂`/ledger bookkeeping. The deflation
(Reading B, field dissolved, boost-readiness direct) STANDS regardless — def-confirmed; only the block
MECHANISM is open, and its criterion (product-preservation) is now ruled.
