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

## FIX-CERTIFICATE — the source-cleared residual satisfies the FULL split (verified)
`verify/capstone_split_sourcecleared.py` (exit 0). On BOTH real witnesses (2,2,2,2) and (3,3,2,2),
ALL slots: applying the SOURCE column-clear — for each ancestor case2/case12 clear at `(L, J)`, zero
the cleared column's below-pivot input entries `(L, r, J)` for `r > J`, BEFORE that edge's shear —
makes the single-`e₂` `MergeBoostSplit` HOLD (each slot ∈ ⟨ed.center⟩; every extra coeff divisible
by `u_{e₂}`; α/β center-ignoring), with `e₂ = canonPivotOf = (0,1,1)` (the diagonal corner IS the
right pivot once the input coupling is cleared). The column-clear ALONE (C1) suffices; the pivot-row
clear (C2) is not needed for the split. So option 1 is CONSTRUCTIVE: the content lemma is TRUE on the
source-column-cleared residual — the fresh formaliser CAN render an induction for that object.

## Kill-condition for THIS obstruction
If a real canonical case11 branch is exhibited on which `Deg1SupportedOn (foldResid p) ed.center`
HOLDS (each slot in ⟨ed.center⟩ on the center's zero-variety), the obstruction is refuted for that
branch — but (2,2,2,2) and (3,3,2,2) are the smallest real case11 witnesses and both fail, so the
statement-as-written is false for them regardless.
