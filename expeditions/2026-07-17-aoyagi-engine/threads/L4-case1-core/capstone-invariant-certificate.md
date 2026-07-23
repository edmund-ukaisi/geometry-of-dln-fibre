# Capstone certificate — the per-edge b-ledger invariant for `foldResid_case11_mergeBoostSplit_canon`

pnp-transport, task #68/#70, on the §7-§7.8 ruled object. This is the fresh-formaliser render brief:
the mathematical content + the exact-algebra facts (all verified, scripts exit 0) + the induction
structure, precise enough to render without design decisions. Lean statement-shape and wiring are the
render seat's call with L4D as def-owner consult; this fixes the MATH.

All facts below are verified in `verify/` (exit 0): `capstone_split_oracle.py`,
`capstone_split_diagnosis.py`, `capstone_split_sourcecleared.py`, `capstone_adjudication.py`,
`capstone_closing_ii.py`, `capstone_straightening_psi.py`, `capstone_psi_gen_build.py`,
`capstone_lift_certificate.py`. Decorrelated Codex: `codex/capstone-split-frame-*`,
`codex/capstone-bridge-iii-*`.

---

## 0. The object (§7 ruling) — what the split is about

**NOTATION (fixed — the overload WILL bite the render seat otherwise).**
`∏A := A_{N-1}···A_1·A_0` is the PRODUCT of the network's matrices (Aoyagi's `∏ C^{(s)}`; `coreGen` = its
entries). `C := sourceClearedResid` is the CLEARED chart residual object (defined below). These are
DIFFERENT objects; this certificate never writes a bare "∏C". `D_J` is Aoyagi's residual block, `E_J` the
cleared unit block, `b_i` the accumulated exceptional monomial.

The raw shears-only `foldResid d (canonFlatten d) p` does NOT satisfy `Deg1SupportedOn … ed.center`
(the obstruction, §1 below). The (D)-carrier is the **Case-1(1) chart residual**

    sourceClearedResid d p  :=  foldResid d (canonFlatten d) p ∘ (ancestor-column-clear)

where the ancestor-column-clear zeros, for every ancestor `case2`/`case12` edge clearing pivot `(a,b)`
at layer `L`, the below-pivot entries of the cleared column: `u_{(L,r,b)} → 0` for `r > a` (in-chart,
after the δ=1 quotient normalizes the pivot to 1). Equivalently `sourceClearedResid = foldResid|_{couplings=0}`.
This is Aoyagi's `E_J = identity` cleared-column structure (pp. 15-18/20-21), NOT an arbitrary hyperplane
(B2, §3). **The recursion `foldResid` is UNCHANGED (§7.8 Option 2′); the RLCT reads on
`sourceClearedResid`; the append consumes it on the ORIGINAL `ed.center`.**

The target (Lean `MergeBoostSplit.lean:93`, re-pointed to this object):

    for a case11 child edge `ed` off `p` (`hδ : edgeδ d p = true`, `hc11`, `hbranch`):
      ∃ e₂ ∈ ed.center, ∃ part extra, part ⊆ ed.center ∧ e₂ ∉ part ∧ (∀ k ∈ extra, k ∉ ed.center) ∧
        MergeBoostSplit d (sourceClearedResid d p) e₂ part extra ed.center (foldRegion d (canonFlatten d) p)

with `e₂ = canonPivotOf` (the reused divisor's BIRTH corner, `MonumentAtlas:837`),
`part = supportAt ∩ ed.center`, `extra = supportAt ∖ ed.center`, `supportAt = blockCoords d S` (since
`hδ ⟹ cleared = 0`), `ed.center = canonCenterOf` case11 branch (`:853`).

---

## 1. WHY the object changed (the obstruction — do not re-litigate)

On the raw fold, `Deg1SupportedOn (foldResid p) ed.center` is FALSE. Witness (2,2,2,2), case11 at
(layer 1, cl 0), `e₂ = (0,1,1)`, `ed.center = {(0,1,1),(1,0,0),(1,1,0)}`:

    slot 0 = u₁₀₀u₂₀₀ + u₁₁₀u₂₀₁ + 2·u₀₁₀u₁₀₁u₂₀₀ + 2·u₀₁₀u₁₁₁u₂₀₁

On the center's zero-variety `{u₀₁₁=u₁₀₀=u₁₁₀=0}`, slot 0 = `2·u₀₁₀u₁₀₁u₂₀₀ + 2·u₀₁₀u₁₁₁u₂₀₁ ≠ 0`,
so no continuous `∑_{i∈center} c_i·u_i` reproduces it. Triple-confirmed (exact Gröbner + L4D re-derivation
+ Codex). The obstruction coord `u₀₁₀` is the below-pivot entry of the ancestor-cleared input column; the
shears-only fold applies branch-(ii)'s `Q₁⁻¹` compensator but NOT the `Q₁` row-clear (§9), leaving the
`2·u₀₁₀` coupling. LESSON (banked): degree≤1 (property B, what the batteries proved) does NOT imply
`⟨ed.center⟩`-membership (property D, what the wall needs).

---

## 2. THE BRIDGE — why re-stating on `sourceClearedResid` is RLCT-sound (§7.7/§7.8, verified)

`sourceClearedResid` and the raw fold differ by the **parameter-space unipotent `Q₁` gauge**
(`capstone_lift_certificate.py`, all witnesses incl. wide (3,3,3,2) + intermediate (2,2,2,2,2)):
per ancestor clear, `A_L → Q₁·A_L`, `A_{L+1} → A_{L+1}·Q₁⁻¹`, `Q₁ = I − Σ_{r>a} A_L(r,b)·E_{r,a}`.

- **det-1 with the pivot FREE** (unipotent); degenerates to det-0 only IN-CHART (pivot=1).
- **product-preserving** (`∏A` invariant) ⟹ the loss `∑‖∏A‖²` is gauge-INVARIANT ⟹ `RLCT` literally
  preserved, **rlctGlobal-intrinsic, no resolution-chart Jacobian weight transported**.

So `RLCT(loss) = RLCT via ⟨sourceClearedResid⟩ = ½·min M_{s,k}` (Aoyagi p.15 invariant + p.22 boxed rule,
the LANDED atlas `rlctAt_sumSqFam_eq_iInf_charts`), and the raw-fold `foldResid` supplies the recursion's
ideal-equality to `∏A` for the VALUE. The two reconcile because `sourceClearedResid` IS the faithful
Case-1(1) local coordinate (B2). The Codex measure-caveat is DISCHARGED by product-preservation (no
weighted integral is transported). This is the LIFT (§7.8 item 2).

**SCOPING of ψ (airtight, per §7.8(3)) — two node classes, both sound, measure-caveat vacuous in each:**
The parameter-space `Q₁`-lift (det-1, product-preserving) holds for ALL node classes — the loss is
literally gauge-invariant, so RLCT-preservation is DIRECT and rlctGlobal-intrinsic everywhere; no weighted
integral is ever transported. Where the classes differ is only in HOW the split/faithfulness is exhibited:
- **single-coupling nodes** (layer-0 reuse): the explicit fold-coordinate straightening `ψ` (F∘ψ = C, det-1,
  `capstone_straightening_psi.py`) constructs cleanly — `ψ` IS the fold-chart image of the `Q₁`-lift, so the
  bridge is witnessed by an explicit CoV.
- **multi-coupling nodes** (wide / intermediate reuse): a single fold-coordinate `ψ` does NOT construct (a
  chart-normalization artifact — the couplings interact in-chart), but this is NOT needed: (a) the
  `Q₁`-lift still holds at the matrix level (each `Q₁` independently unipotent — `capstone_lift_certificate.py`),
  giving RLCT-preservation directly; (b) the split/faithfulness (B2) is exhibited by the DIRECT argument
  (couplings are ancestor `E_J`-coords; the `extra` block VANISHES — a VERIFIED property, not a structural
  expectation). So the value chain reads on `C` via the cover from the start; NO weighted integral is
  transported, and the measure-caveat is vacuous by construction (§7.8(4) discharged).

---

## 3. B1 / B2 / B3 — the cover (min-over-charts is Aoyagi's own framework, p.22)

- **B1 cover-completeness** — CITATION, not re-proved here, and the demotion is honest: (1) the `Q₁`-lift
  (§2) now gives RLCT-preservation DIRECTLY for ALL node classes (the loss is literally gauge-invariant),
  so the cover is NO LONGER load-bearing for RLCT-SOUNDNESS — it is the FIDELITY narrative (Aoyagi's own
  p.22 min-over-charts framing). (2) The genuine cover-completeness proof obligation lives where the
  formalisation ladder already carries it — **L7 `leafPath_compactCover`** (the fibre-exhaustion frontier,
  consuming lemma Q + the fan certificate #11-14); re-proving it inside this certificate would DUPLICATE
  L7's debt. So: cover completeness = L7's obligation, consumed there; cited here as the fidelity frame.
- **B2 chart-faithfulness** — `sourceClearedResid` IS the Case-1(1) chart residual. VERIFIED:
  the coupling coords are below-pivot entries of ANCESTOR-cleared columns (`E_J = identity`), and clearing
  them makes the `extra` block VANISH. At the (2,2,2,2,2) layer-2 intermediate crux the couplings are
  `(0,1,0)` [layer-0] and `(1,1,0)` [layer-1], BOTH ancestor `E_J` coords — NEITHER an uncovered output
  coord (the layer-3 factor `u₃₀₀` is the shared output row). Re-open trigger DISARMED.
- **B3 min-over-charts** — `RLCT = ½·min_charts M_{s,k}` (Aoyagi p.22 = the landed atlas). B3 is a TIE to
  existing analytic machinery, not a build; the case11 chart's `M_{s,k}` (via `sourceClearedResid`, where
  the read-off §5 gives the monomial form) is a legitimate term.

---

## 4. THE PER-EDGE INVARIANT (the content lemma's induction on the concrete `foldResid` recursion)

State the invariant on the CONCRETE recursion (`MonumentAtlas:474-488`), carried on `sourceClearedResid`.
The invariant `INV(p)`: `sourceClearedResid d p` is degree-1 supported on `supportAt(p)` with the exact
**b-ledger** coefficient structure — each slot

    resid_j(u) = ∑_{i ∈ supportAt(p)} c_{j,i}(u) · u_i,   c_{j,i} = b_{row(i)}(u) · (clean D_J entry),

where `b_i = ∏_{t̃_{s,k} < i} u_{s,k}` (worked.tex:562-577; `b_0=1`, `b_i = (∏_{t̃=i-1} u_{s,k})·b_{i-1}`)
is the accumulated exceptional monomial, and the `clean D_J entry` is a single support coordinate (the
`v_j/1` degree-1 regime). This carries the per-layer degree ≤ 1 grade (`PerLayerDeg1From`).

**`supportAt` version + the width-INCREASING (cap-bite) axis (`capstone_coverage_wide.py`, exit 0).** Since
`hδ ⟹ cleared = 0`, `supportAt(p) = blockCoords d S` — the running-min-CAPPED col axis (`col < widthMinUpto d S`,
`MonumentAtlas:617` J=0 branch, the current elder-ruled def). On a WIDE layer (`d_{S} > widthMinUpto d S`) the
cap excludes the raw-remnant columns `col ≥ widthMinUpto`. VERIFIED on the width-increasing witnesses
`(2,3,2,2)`, `(2,3,3,2)`, `(2,4,2,2)` (all with a case11 node): the RAW fold DOES read the cap-escaped
columns (cap too tight for the RAW object), but the SOURCE-CLEAR REMOVES that dependence — those columns
enter only through the ancestor input coupling — so `sourceClearedResid`'s support lies WITHIN the capped
`blockCoords`, and `INV`, the single-`e₂` read-off, and the `Q₁`-lift all HOLD. So the capped `supportAt`
at J=0 is FAITHFUL for `sourceClearedResid` (a bonus: the source-clear resolves the J=0 cap-escape too).
[Distinct from the DESCENDED (J≥1) support, which is `layerCoords d (S+1)` (raw, uncapped) per the
consolidated ruling — a separate branch not exercised by the case11 read-off.]

### (i) ROOT base case  (`MonumentAtlas:476`)
`sourceClearedResid d .root = coreGen d (canonFlatten d)` (the ancestor-clear is empty at root).
`coreGen d e k u = (mult d (e u))[decode k]` = the entries of `∏A = A_{N-1}···A_0`
(`LearningCoefficient:50`). At `S=J=0`, `D_0 = ∏A`, `b_i ≡ 1` (no exceptional yet) — `INV(.root)` holds:
each product entry is multilinear degree-1 per layer, support = the full block (`coreGen_layerHomogeneous`,
banked L3T2/L3T3). VERIFIED numerically (`capstone_split_oracle.py`).

### (ii) δ=1 transport  (`edgeδ d p = true ⟺ p.conState.cleared = 0`; `:482-485`)
Child residual = PARENT `sourceClearedResid d p (Fin.cast … j)` at the STRICT-TRANSFORM argument
`fun k ↦ blockBlowupCoordQuot pivot k (edgeShearRaw d cse shearφ u)` (`BlockDivision:30`
`blockBlowupCoordQuot p j = if j=p then 1 else w j`). Mechanism: on `INV(p)`
(support-decomposition ∈ `⟨ed.center⟩` after the source-clear), the blow-up sends each `ed.center` coord to
`u_pivot · quot` (`blockBlowupMap_shear_center_eq`), so the pivot factor divides out EXACTLY, and the
b-ledger ACCUMULATES: a fresh exceptional `u_{S,J+1}` is BORN (`t̃ = J`, `b'_i = u_{S,J+1}·b_i` on the run
rows), matching worked.tex Case 1(2)/Case 2. `#{u | t̃ = J+J₁}` decrements by one (the merge inner
recursion). The strict transform is well-defined and preserves `INV`. [Consumer facts §5 read HERE.]

### (iii) δ=0 transport  (`:486-488`)
Child residual = parent at the PULLBACK `stepMapRaw d cse center pivot shearφ u`
(`= blockBlowupMap center pivot ∘ edgeShearRaw`, `:325`, blow-up OUTERMOST). No new `u_pivot` factor
(`δ=0`); the order balances (the b-ledger RELABELS, no birth). `edgeShearRaw` is `id` at case11/rollover,
`blockShear canonNormalizationOf` at case12/case2. `INV` is preserved: the shear is det-1 unipotent
(reads only unwritten coords), the blow-up multiplies center coords by the pivot (degree-1 preserved on
the descended support `layerCoords d (S+1)`). VERIFIED (`capstone_adjudication.py`, per-layer deg≤1 TRUE
all nodes).

### (iv) READ-OFF at a case11 edge — the `MergeBoostSplit` shape
At a case11 child `ed` off `p` (`hδ`, `hc11`), `INV(p)` on `sourceClearedResid` yields, per slot `j`:

    resid_j(u) = (∑_{i ∈ part} α_{j,i}(u)·u_i) + u_{e₂} · (∑_{i ∈ extra} β_{j,i}(u)·u_i)

with `e₂ = canonPivotOf` (single, reused-pivot birth corner — validated at source by the elder,
`24b125759`: one exceptional per case11 step, multiplicity in the ACCUMULATED ledger), `α,β` continuous +
`IgnoresCoords ed.center`, and the b-ledger content:

- `part = supportAt ∩ ed.center` (the run block, cols `< cleared + runLen`): `α_{j,i} = b_i·(clean entry)`;
- `extra = supportAt ∖ ed.center` (cols `≥ cleared + runLen`): the boost `b'_i = u_{s,k}·b_i` factors the
  run-row dependence through the SINGLE reused exceptional `u_{e₂}` — so `β_{j,i} = (b_i/b_1)·(clean entry)`.

VERIFIED on `sourceClearedResid` (`capstone_split_sourcecleared.py`, all slots, both (2,2,2,2) and
(3,3,2,2)): the single-`e₂` split HOLDS with `e₂ = canonPivotOf`. This wires DIRECTLY into
`MergeBoostSplit.deg1SupportedOn` (PROVEN clean-three, `MergeBoostSplit.lean`), giving
`Deg1SupportedOn (sourceClearedResid p) ed.center`.

---

## 5. CONSUMER FACTS (`split-consumers-needed-facts.md`, carried by the certificate)

- **born-unit** (Consumer 4; case12/case2 δ=1 GENUINE clear, child.cleared=1 — NOT case11): `∃ j,
  c_{e₂}(j) 0 ≠ 0` (the fresh pivot coefficient is non-vanishing at the origin) ⟹ `sourceClearedResid
  child j 0 = c_{e₂}(j) 0` = the born unit `b_i` (a non-vanishing monomial). From the δ=1 birth (§4 ii).
- **conjunct-2** (Consumer 3; per-slot `Deg1SupportedSlot ∨ unit`): case11 (cleared=0) — remainder is
  Deg1 on `blockCoords(N-1)` after dehomog, pivot-carrying slots flagged units; case12/2 (cleared≥1) —
  `supportAt(child)=∅`, each slot ≡ 0 or a unit. ⟹ the per-slot pivot-XOR disjunction.
- **conjunct-1 / LL S=L**: consume `Deg1SupportedOn ed.center` (the §4 iv read-off) directly.

`extra ∩ ed.center = ∅` is automatic (`extra = supportAt ∖ ed.center`), supplying `MergeBoostSplit.deg1SupportedOn`'s `hex`.

---

## 6. canonFlatten-SPECIFICITY (KILLED-BY-e)

The ∀e form is FALSE (route-β): a generic scrambler `e` breaks the single-`e₂` split
(`capstone_split_chartframe.py`, KILLED-BY-e block). The certificate consumes the CONCRETE `coreGen` at
`e = canonFlatten d` (each flat coord = one matrix entry, so `coreGen` is per-layer multilinear), NOT
`hslot`. `isLinearMap_canonFlatten` (`LearningCoefficient:215`) is the load-bearing pin.

---

## 7. What the render seat builds (turn-key)

`MergeBoostSplit` predicate + `MergeBoostSplit.deg1SupportedOn` (assembly, PROVEN clean-three) +
`realBranch_boostReady_case11'` are REUSABLE UNCHANGED on `sourceClearedResid` (L4D def-owner read). The
render seat: (a) re-point the content lemma statement to `sourceClearedResid`; (b) render the §4
induction (root/δ=1/δ=0/read-off) as the proof of the content lemma; (c) wire the §2 Q₁-lift as the
RLCT-equivalence bridge (Lean side = the landed det-1-CoV machinery, `integrableOn_image_iff` class — this
certificate supplies existence/explicitness, not new analysis); (d) the append crux
`foldResid_stepMap_eq_pivot_mul` (`Case1Wire:36-72`) consumes `Deg1SupportedOn (sourceClearedResid p)
ed.center` on the ORIGINAL center (Option 2′). L4D owns the exact append re-point.

---

## 8. Kill-conditions per section (what would falsify each; the render seat re-checks on failure)

- **§2 bridge / lift** — if, on any real case11 witness, the paired `Q₁` gauge FAILS to preserve `∏A`
  (loss not gauge-invariant) or the `Q₁` is NOT det-1 with the pivot free, the RLCT-intrinsic lift is
  refuted → the measure-caveat becomes real and the elder fires Codex. (Checked TRUE on
  (2,2,2,2)/(2,2,2,2,2)-both/(3,3,3,2); `capstone_lift_certificate.py`.)
- **§3 B2** — if a real case11 node has a coupling coord that is NOT a below-pivot entry of an
  ancestor-cleared column (an UNCOVERED output-coordinate coupling), then `sourceClearedResid` is not the
  faithful chart residual → re-open (elder §7.7 trigger). (Checked FALSE-of-trigger at the intermediate
  crux (2,2,2,2,2): both couplings are ancestor `E_J` coords.)
- **§4 induction** — if `INV(p)` is NOT preserved by the δ=1 (`blockBlowupCoordQuot`) or δ=0
  (`stepMapRaw`) transport (e.g. a slot gains per-layer degree ≥ 2, or the strict-transform pivot factor
  fails to divide), the b-ledger invariant breaks. (Checked: per-layer deg≤1 TRUE all nodes,
  `capstone_adjudication.py`; the δ=1 division is the `blockBlowupMap_shear_center_eq` factoring.)
- **§4 iv read-off** — if the single-`e₂` split FAILS on `sourceClearedResid` for `e₂ = canonPivotOf`
  (some extra coeff not divisible by `u_{e₂}`, or `α/β` reading `ed.center`), the `MergeBoostSplit` shape
  is wrong. (Checked TRUE, all slots, `capstone_split_sourcecleared.py`.) NOTE: this holds on
  `sourceClearedResid`, NOT the raw fold (§1) — the render MUST target `sourceClearedResid`.
- **§5 born-unit** — if at a case12/case2 δ=1 clear NO slot has `c_{e₂}(j) 0 ≠ 0`, the born-unit consumer
  fails. (The fresh pivot is the blow-up coordinate; its coefficient is the non-vanishing `b_i`.)
- **§6 KILLED-BY-e** — if the split held for a generic scrambler `e`, the canonFlatten-specificity (and
  the whole route-β-is-dead ruling) would be wrong. (Checked: scrambler BREAKS it,
  `capstone_split_chartframe.py`.)
