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
ideal-equality to `∏C` for the VALUE. The two reconcile because `sourceClearedResid` IS the faithful
Case-1(1) local coordinate (B2). The Codex measure-caveat is DISCHARGED by product-preservation (no
weighted integral is transported). This is the LIFT (§7.8 item 2).

---

## 3. B1 / B2 / B3 — the cover (min-over-charts is Aoyagi's own framework, p.22)

- **B1 cover-completeness** — the `coupling ≠ 0` locus is carried by the sibling charts
  (Case 1(2) / Case 2 / complementary). CITED to the landed fan-cover certificate (pnp-fan #11-14: the
  fanned-spine predicate, the cover argument over the fanned tree, the worked (2,2,2) instance). [If the
  render wants it re-verified at (2,2,2,2,2), it is a short oracle-charts-cover check; folded as a citation
  here per the fan asset.]
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

### (i) ROOT base case  (`MonumentAtlas:476`)
`sourceClearedResid d .root = coreGen d (canonFlatten d)` (the ancestor-clear is empty at root).
`coreGen d e k u = (mult d (e u))[decode k]` = the entries of `∏C = A_{N-1}···A_0`
(`LearningCoefficient:50`). At `S=J=0`, `D_0 = ∏C`, `b_i ≡ 1` (no exceptional yet) — `INV(.root)` holds:
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
