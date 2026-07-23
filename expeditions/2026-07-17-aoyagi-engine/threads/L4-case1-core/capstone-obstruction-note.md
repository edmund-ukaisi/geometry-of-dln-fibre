# §-note: the capstone content lemma is FALSE on the RAW `foldResid` — OBSTRUCTION certificate

pnp-transport, task #68 (dispatched to WITNESS the invariant certificate for
`foldResid_case11_mergeBoostSplit_canon`; found an OBSTRUCTION instead). Exact algebra
(sympy + grevlex Gröbner, exit 0) + decorrelated Codex (xhigh, hypothesis withheld) — both agree.

Scripts: `verify/capstone_split_oracle.py`, `verify/capstone_split_diagnosis.py`,
`verify/capstone_split_chartframe.py`. Codex: `codex/capstone-split-frame-{prompt,answer}.md`.

## The target (MergeBoostSplit.lean:93 → Case1Wire.lean:390 `realBranch_boostReady_case11`)
For a real case11 (merge) edge `ed` off parent `p` at δ=1 (parent `cleared = 0`), the wall concludes
`Deg1SupportedOn (foldResid d (canonFlatten d) p) ed.center (foldRegion … p)` — i.e. each of the
`foldNR = d_N·d_0` residual SLOTS splits as `∑_{i∈part} α_i·u_i + u_{e₂}·∑_{i∈extra} β_i·u_i`,
`e₂ = canonPivotOf`, coefficients continuous + ignoring `ed.center`.

## VERDICT: FALSE as stated (single-e₂ split does not hold on the raw shears-only `foldResid(p)`).
Real canonical branch for **d=(2,2,2,2)** (oracle-driven, `oracle_edges`): parent
`[case2(L0,cl0,δ1), case2(L0,cl1,δ0), rollover(L0,cl2)]`, state (L1,cl0); the FIRST `case11` reuses
the divisor born at (L0,cl1), so `e₂ = canonPivotOf = cornerToFlat d 0 1 = (0,1,1)`,
`ed.center = {(0,1,1),(1,0,0),(1,1,0)}`, `supportAt = layer 1`,
`part = {(1,0,0),(1,1,0)}`, `extra = {(1,0,1),(1,1,1)}`.

Composing `foldResid(p) = coreGen ∘ (3 ancestor transforms)` with the EXACT 3-branch
`canonNormalizationOf` render (MonumentAtlas:906-966, scoped), `A_2·A_1·A_0` entries (slot `j` =
output `(j//2, j%2)`):

    slot 0 = u₁₀₀·u₂₀₀ + u₁₁₀·u₂₀₁ + 2·u₀₁₀·u₁₀₁·u₂₀₀ + 2·u₀₁₀·u₁₁₁·u₂₀₁
    slot 1 = u₀₀₁·u₁₀₀·u₂₀₀ + u₀₀₁·u₁₁₀·u₂₀₁ + u₀₁₁·u₁₀₁·u₂₀₀ + u₀₁₁·u₁₁₁·u₂₀₁
    (slots 2,3 = same with u₂₁ⱼ)

**Exact Gröbner:** each slot ∈ ⟨supportAt⟩ (the CARRIED invariant `Deg1SupportedOn supportAt`
HOLDS); but slots 0, 2 ∉ ⟨ed.center⟩ = ⟨u₀₁₁,u₁₀₀,u₁₁₀⟩ ⟹ `Deg1SupportedOn ed.center` FAILS.
Cleanest proof (kills even the continuous-coefficient reading): on the center's zero-variety
`{u₀₁₁=u₁₀₀=u₁₁₀=0}`, slot 0 = `2·u₀₁₀·u₁₀₁·u₂₀₀ + 2·u₀₁₀·u₁₁₁·u₂₀₁ ≠ 0`, while any
`∑_{i∈center} c_i·u_i = 0` there — no continuous `c` can reproduce it.

The coordinate the "extra" block factors through DEPENDS ON THE OUTPUT COLUMN: output col 0
(slots 0,2) → `u₀₁₀ = (0,1,0)`; output col 1 (slots 1,3) → `u₀₁₁ = e₂`. So **no single e₂**.
Same verdict on **d=(3,3,2,2)** (double-boost witness): slots 0,3 ∉ ⟨ed.center⟩.

## The structural cause (Codex Q2, corroborated)
Column 0 of `A_1^♯·A_0^♯` = `(b_0 + x·b_1)·1 + b_1·x = b_0 + 2·x·b_1`, `x = u₀₁₀`, `b_1 = u₁₀₁`.
The `2·x·b_1` = branch-(ii)'s compensator `x·A_{1,*1}` (the `+γ = A_{S+1}·Q₁⁻¹` recoord) PLUS the
un-zeroed input below-pivot entry `A_{0,10} = x` acting through ordinary matrix multiplication. The
shears-only fold applies the branch-(ii) COMPENSATOR for a pivot-column clear it never PERFORMS
(the pivot-cross clear is `r4Clear`, kept OUT of the recursion by §9 "RECURSION=ideal / BOOSTREADY=form").
In column 1 branch-(i) cancels the cross-term, which is why only output col 1 factors through `e₂`.

## The object on which the split DOES hold (Codex Q3/Q4 — the fix, FACT)
Clear the input coupling `u₀₁₀` **at the source, BEFORE branch-(ii)** (equivalently: `A_0`'s cleared
column becomes the unit `[1,0]`). Then col 0 = `b_0`, col 1 = `y·b_0 + z·b_1` (`z = u₀₁₁ = e₂`), and
the single-`e₂` split holds. Clearing only `u₀₁₀` suffices; **ordering matters** — an `A_0`-only clear
applied AFTER the shear leaves `b_0 + x·b_1`, still non-`e₂`-divisible.

## Relation to the task #54 r4Clear-bridge verdict (SAME E_J obstruction, DIFFERENT property)
This is the same col-0 / E_J failure #54 found. There, F₂ (the `+γ`-paired `Q₁⁻¹` + `Q₂⁻¹`
compensators) fixed the RECURSION bridge `⟨cleared⟩ = ⟨uncleared⟩` (product-preserving, census 0) —
sound for closing `StepInv`. But `Deg1SupportedOn ed.center` is a STRICTLY STRONGER, DIFFERENT
property (membership in the SUB-ideal ⟨ed.center⟩, not equality of the full residual ideals), and F₂
does NOT establish it. `foldNR = d_N·d_0` (all product entries) ⟹ the StepInv is all-entries ⟹ the
E_J entries are in scope. The tension is genuine: the recursion needs shears-only (det-1,
product-preserving) to close StepInv; boostReady needs the SOURCE input-clear (det-0) to get
`Deg1SupportedOn ed.center`. Both cannot hold on the SAME `foldResid` object.

## Resolution options (for the def-owner L4D + source-validator elder — NOT mine to pick)
1. **Re-state the content lemma on the source-cleared residual** — `MergeBoostSplit` about
   `foldResid(p) ∘ (input-clear)` (or a `foldResid` whose δ=1 step composes the pivot-cross clear at
   the source). Requires the downstream δ=1 append crux (`foldResid_appendResidDescent`) to consume
   the cleared form; propagates a statement-shape change.
2. **Enlarge `ed.center`** to include the reused divisor's full below-pivot INPUT row
   `{(0,1,·)}` (not just the diagonal corner (0,1,1)). Then slots 0,2 land in ⟨center⟩ — but this
   changes the geometry/codimension bookkeeping and needs an e₂ per output column (contradicts the
   single-`e₂` predicate). Likely NOT the intended fix.
3. **Splice the pivot-cross clear into the recursion** (reverse §9's shears-only decision). Then
   `foldResid` is the clear-model and `Deg1SupportedOn ed.center` may hold — but the clear is det-0,
   breaking the product-preserving StepInv closure F₂ secured. Trades one failure for the other.

Option 1 (source-clear composed into what the split is about) matches Codex's "split-carrying object"
and is the least destabilising; the exact wiring is L4D's call.

## FIX object — the source-cleared residual satisfies the split, but is a RESTRICTION (RLCT caveat)
`verify/capstone_split_sourcecleared.py` (exit 0). On both witnesses (2,2,2,2)/(3,3,2,2), ALL slots:
the SOURCE column-clear — for each ancestor clear at `(L,J)`, zero the cleared column's below-pivot
entries `(L,r,J)` for `r>J` BEFORE that edge's shear — makes the single-`e₂` `MergeBoostSplit` HOLD
(each slot ∈ ⟨ed.center⟩, extra coeff ÷ `u_{e₂}`, α/β center-ignoring), `e₂=canonPivotOf=(0,1,1)`.
Column-clear alone suffices.

**BUT it is not a free swap — the cleared↔raw bridge is genuine design content (exact datum).**
`⟨src slots⟩ ≠ ⟨raw slots⟩` (Gröbner, neither contains the other) and `src = raw|_{u₀₁₀=0}`: the
fix-object is the raw fold RESTRICTED to the hyperplane `{coupling=0}`, NOT related to the raw fold by
a product-preserving/det-1 CoV. A hyperplane restriction can change the RLCT, so re-stating boostReady
on it is only sound where the coupling coord is a GAUGE coordinate the resolution legitimately fixes:
- **layer-0 reuse** (all of (2,2,2,2)/(3,3,3,2)/(3,3,2,2)): the coupling `u₀₁₀` is a layer-0 INPUT
  coord = the global `GL_{d₀}` end-factor gauge `P₁` (corner ruling #61/#62, worked.tex:426-428,437),
  absorbed once via Lemma 1 — so clearing it is gauge-fixing, plausibly RLCT-preserving.
- **intermediate-layer reuse EXISTS** (e.g. (2,2,2,2,2): case11 at layer 2 reusing a layer-1 divisor):
  the obstruction still holds, but manifests through OUTPUT-layer coords — the `GL_{d₀}` gauge argument
  does NOT obviously transfer, and RLCT-soundness of the source-clear there is OPEN.

So Option 1 is CONSTRUCTIVE for the split but its RLCT-soundness is the pnp+elder+controller design
gate (the cleared↔raw bridge). The POSITIVE (L4D def-owner read): the `MergeBoostSplit` PREDICATE and
`MergeBoostSplit.deg1SupportedOn` ASSEMBLY survive unchanged on the cleared object — only the content
lemma's OBJECT changes. The fresh formaliser can render an induction for the ratified object once the
bridge is settled.

## DEFINITIVE ADJUDICATION (def-owners' kill-condition, `verify/capstone_adjudication.py`, exit 0)
L4D + team-lead's binary gate: with `Φ_p` computed DEF-EXACT (`coreGen ∘` per-edge argument
transforms; split edges apply `edgeShearRaw = blockShear canonNormalizationOf` = the F₂ 3-branch
recoord AS MERGED, NOT a naive shear; `case11`/`rollover` id-shear; the reused-divisor BIRTH edge's
recoord IS inside `Φ_p`), does the extra block factor through RAW `u_{e₂}`?

Corrected oracle: `case11` KEEPS `cleared` (`DescendView`), so a double-boost is stacked merges at
the SAME node. Tested at EVERY case11 node (incl. the stacked second merges runLen=2), SCOPED AND
UNSCOPED, on **(2,2,2,2)** minimal, **(3,3,3,2)** wide-interior (3×3 layer-0 Schur), **(3,3,2,2)**
double-boost:

| property | result (every node, every scope) |
|---|---|
| (A) raw-`u_{e₂}` split | **FALSE** |
| (B) degree ≤ 1 in every coord (no `u_{e₂}²`) — the design "multilinear-clean" / battery claim | **TRUE** |
| (D) each slot ∈ ⟨ed.center⟩ (`Deg1SupportedOn ed.center`) | **FALSE** |

**VERDICT: CHART-ONLY.** The raw-split is FALSE on all real case11 nodes even with the F₂ recoord
def-exactly applied. The chart value `(Φ_p u)_{e₂} = u₀₁₁ − u₀₀₁·u₀₁₀` (the birth Schur exceptional);
the extra factors through ITS constituent `u₀₁₀` (and output-layer coords), never raw `u_{e₂}`.

**The evidence tension, resolved (no contradiction).** The batteries #48–56 / `r3r4_chartframe_boostready`
proved property **(B)** — "u₀₀₁² RESOLVED" = degree ≤ 1 — which my re-run CONFIRMS. The wall needs
property **(D)** — membership in the SUB-ideal ⟨ed.center⟩. **(B) does not imply (D).** The F₂ recoord
does exactly its job (degree ≤ 1, product-preserving `StepInv` closure) but cannot deliver (D): the
shears-only fold retains the input-layer coupling `u₀₁₀`, which is degree-1 (so (B) holds) yet lies
outside ⟨ed.center⟩ (so (D) fails). The instruments were degree/chart-frame checks; they never tested
(D). Decorrelated Codex (`codex/capstone-split-frame-answer.md`, 3-branch recoord in the prompt)
independently reached "raw-split impossible" and diagnosed the branch-(ii) double-count.

Per team-lead's kill-condition: CHART-ONLY ⟹ STOP, do not certificate around it, escalate as a
statement-soundness re-shape (task #69). The FIX-object (source-column-cleared residual, below) is the
constructive target for the re-shape.

## CLOSING-CONTRACT (ii)/(iii) on the ruled `sourceClearedResid` — BOTH named bridges FAIL (exact)
`verify/capstone_closing_ii.py` (exit 0), ruled object `sourceClearedResid := foldResid ∘
(ancestor-column-clear)`, three witnesses (2,2,2,2)/(3,3,2,2)/(3,3,3,2):

- **(ii) ideal-equality `⟨sourceClearedResid⟩ = ⟨foldResid⟩`: FALSE** (both inclusions fail, every
  witness). The "column-clear is regular / Lemma-1-neutral" expectation does NOT hold at the slot-ideal
  level. Also `⟨coreGen⟩` (the ∏C product) is NOT preserved by the clear — the clear genuinely changes
  the product, so it is not a product-preserving CoV.
- **L4D's decomposition route (b) also FAILS as sketched:** the coupling remainder `r_j = foldResid_j −
  sourceCleared_j` (= `2·u₀₁₀·(…)` on (2,2,2,2)) is in NONE of `⟨sourceCleared⟩`, `⟨ed.center⟩`,
  `⟨pivot⟩` — in particular it is NOT `u_{pivot}`-divisible, so the δ=1 strict-transform discharge of the
  remainder does not go through.
- **(iii) StepInv `∃q` transport — cannot go via either named bridge.** The append crux
  `foldResid_stepMap_eq_pivot_mul` needs the parent residual ∈ `⟨ed.center⟩` for a continuous `q`; on the
  RAW object that is FALSE (the whole obstruction), and neither (ii) (ideal-equality) nor (b)
  (pivot-divisible remainder) supplies a route to re-derive it for the cleared object. **Kill-condition
  (team-lead's (iii)) is TRIGGERED.**

## THE STRAIGHTENING ψ — raw↔cleared IS a det-1 CoV; RLCT PRESERVED (decorrelated-Codex-found, VERIFIED)
`verify/capstone_straightening_psi.py` (exit 0); `codex/capstone-bridge-iii-answer.md`. This CORRECTS
an over-claim I made above (struck): I inferred "no det-1 CoV can bridge raw and cleared (dimension)".
That is FALSE. There is an explicit det-1 polynomial automorphism (Codex-found, re-derived exactly here):

    ψ:  b₀ ↦ b₀ − 2x·b₁,   d₀ ↦ d₀ − 2x·d₁,   z ↦ z + 2x·y   (others fixed)
        x=u₀₁₀, y=u₀₀₁, z=u₀₁₁=e₂, b₀=u₁₀₀, b₁=u₁₀₁, d₀=u₁₁₀, d₁=u₁₁₁

with **`F∘ψ = C` (all slots), `det Dψ = 1`**, and a nonvanishing flat vector field `V = ∂ₓ − 2b₁∂_{b₀} −
2d₁∂_{d₀} + 2y∂_z` with `V(F_j)=0 ∀j, V(x)=1`. So raw `foldResid` has a genuine FLAT direction; ψ
straightens it to the source-cleared object.

**CONSEQUENCE (the positive resolution):** F and C are related by a VOLUME-PRESERVING automorphism, so
`RLCT(∑F²) = RLCT(∑C²) = RLCT(∑F²|_{x=0})` (verified: `∑F² = (∑C²)∘ψ⁻¹`). **Fixing the coupling coord is
RLCT-preserving — Option 1 (re-state on `sourceClearedResid`) IS RLCT-SOUND; the learning coefficient is
NOT at risk.** The `(ii)` ideal-*equality* stays FALSE, but that was the wrong test: the true bridge is
ideal-*EQUIVALENCE* `ψ*⟨F⟩ = ⟨C⟩` via a det-1 map, which HOLDS.

**THE STRUCTURAL CAVEAT (what the re-wire must handle):** ψ CONJUGATES the center —
`I=(z,b₀,d₀) ↦ ψ(I) = (z+2xy, b₀−2xb₁, d₀−2xd₁)`. So ψ repairs the split on a MOVED pivot/center, NOT the
original `z`-edge (any automorphism preserving `I` would force `F_j∈I` from `C_j∈I`, contradicting
non-membership). This is exactly the elder's §7.5 CHART/COVER (B2 chart-faithfulness) structure: the
chart relating the raw fold to the cleared object is det-1 (faithful) and moves the center — the append
transports to the conjugated edge, not the original. Codex's RLCT caveat: with an ordinary smooth
positive measure the det-1 ψ suffices; if a resolution chart carries an independent vanishing monomial
Jacobian weight, one must additionally check the fibre-marginal after ψ has the same singular order
(det-1 alone does not preserve an independently-specified vanishing weight) — a check for the
formaliser/elder on the accumulated chart measure.

**ψ_gen build outcome (`verify/capstone_psi_gen_build.py`, exit 0) — single-coupling clean, multi-coupling
rides the cover.** Constructing ψ_gen as the composite of per-coupling flat-field straightenings:
- **VERIFIED** (F∘ψ_gen=C, det 1, RLCT-equivalence): (2,2,2,2) archetype; **(2,2,2,2,2) deep single-reuse
  (layer-1)** — the clean B2 witness for single-coupling (layer-0-reuse) nodes.
- **NOT constructed** for the MULTI-coupling nodes — (2,2,2,2,2) layer-2 intermediate ({(0,1,0),(1,1,0)})
  and (3,3,3,2) wide ({(0,1,0),(0,2,0),(0,2,1)}). Reason (exact): `F` is degree-1 in each coupling, but no
  constant-coefficient flat field moves them and no per-coupling flat field exists up to degree 3 — the
  couplings INTERACT (the intermediate extra coeff `2·u₃₀₀·(u₀₁₀·u₁₁₁ + u₁₁₀)` mixes couplings `u₀₁₀`,
  `u₁₁₀`). A single det-1 ψ_gen for these may need a joint (non-per-coupling) construction, or may not exist
  as one map.

**This is NOT a re-open trigger and NOT load-bearing (§7.7).** For the multi-coupling nodes:
- **B2 chart-faithfulness HOLDS via the direct argument** (verified): the coupling coords are the below-pivot
  entries of ANCESTOR-cleared columns (the `E_J = identity` structure), and clearing them makes the extra
  block VANISH — so `sourceClearedResid` IS the genuine Case-1(1) chart residual, not an arbitrary
  hyperplane. At the (2,2,2,2,2) layer-2 intermediate the couplings are `(0,1,0)` (layer-0) and `(1,1,0)`
  (layer-1), BOTH ancestor E_J coords — NEITHER an uncovered output coord (the layer-3 factor `u₃₀₀` is the
  shared output row, present in every coeff). Re-open trigger DISARMED, confirming §7.7.
- **RLCT reads on C via min-over-charts (B3, the landed atlas)**, not via a single ψ. So the multi-coupling
  RLCT-soundness rides the cover (B1 completeness + B2 faithfulness + B3 min-tie), with ψ_gen as the
  belt-and-braces working lemma where it constructs (single-coupling). This matches team-lead's framing
  ("ψ slots in as the B2 witness INSIDE min-over-charts; the cover is the fidelity narrative").

## Kill-condition for THIS obstruction
If a real canonical case11 branch is exhibited on which `Deg1SupportedOn (foldResid p) ed.center`
HOLDS (each slot in ⟨ed.center⟩ on the center's zero-variety), the obstruction is refuted for that
branch — but (2,2,2,2) and (3,3,2,2) are the smallest real case11 witnesses and both fail, so the
statement-as-written is false for them regardless.
