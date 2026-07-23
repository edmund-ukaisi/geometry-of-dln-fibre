# Elder ruling — the capstone-object obstruction (boostReady is about the CLEARED residual)

Ruling on pnp-transport's obstruction (`capstone-obstruction-note.md`, b31a3cc8c; exact Gröbner +
decorrelated Codex xhigh, both agree). Amends design-round-2-ruling §9 (PROPERTY-HOME). elder-standing,
2026-07-24.

## 1. OBSTRUCTION ACCEPTED — the content lemma is FALSE as stated

`Deg1SupportedOn (foldResid d (canonFlatten d) p) ed.center` (the conclusion of
`realBranch_boostReady_case11`, and the target of `foldResid_case11_mergeBoostSplit_canon`) is **FALSE on
the raw shears-only `foldResid`** for the smallest real case11 branches (2,2,2,2), (3,3,2,2). Ground truth,
not defended. On (2,2,2,2): slot 0 = `b_0 + 2x·b_1` in column 0 (`x=u₀₁₀`, `b_1=u₁₀₁`); on the center's
zero-variety `{u₀₁₁=u₁₀₀=u₁₁₀=0}` it equals `2·u₀₁₀·(…) ≠ 0`, so no continuous `c` over `ed.center`
reproduces it. pnp's calibration was right — a certificate for a false lemma must not ship.

## 2. My source-validation STANDS but is REFINED (honest self-correction)

The MergeBoostSplit predicate-fidelity verdict (predicate SHAPE faithful to Aoyagi's separated normal form)
is correct — but it validated the shape against Aoyagi's **CLEARED `D_J`** (the residual *after* the
Lemma-2 clear). The error is the **OBJECT**: the content lemma applies the (faithful) predicate to the
**raw `foldResid`**, which is NOT the cleared `D_J`. My verdict inherited the §8(i)(c) premise "foldResid at
case11 = the CLEAN BLOCK D_J"; pnp's Gröbner shows that premise is **false** — the shears-only foldResid
carries branch-(ii)'s `+γ` compensator (`b_0→b_0+x·b_1`) WITHOUT the paired input-clear of A_0's
below-pivot entry `x`, leaving the double-count `b_0+2x·b_1`. The predicate is faithful; the object it is
asserted on is wrong.

## 3. The precise structure (recursion is fine; only the SUB-ideal descent fails)

- **Recursion / StepInv — UNAFFECTED.** Every slot IS in `⟨supportAt⟩` (pnp confirmed); the double-count
  `2x·b_1 = u₀₁₀·u₁₀₁·(…) ∈ ⟨u₁₀₁⟩ ⊆ ⟨supportAt⟩`. So §9's shears-only recursion (StepInv on `supportAt`,
  product-preserving, census 0) STANDS, and the **F₂ delta-read I GREEN'd is NOT contradicted** — F₂
  secured the recursion/ideal closure on `supportAt`, which holds. This obstruction is about the
  **strictly stronger, different** property `Deg1SupportedOn ed.center` (descent to the smaller boost-center
  sub-ideal `⟨ed.center⟩`), which F₂ never claimed to establish (same E_J col-0 as #54, different property).
- **boostReady — FALSE on the raw object.** The descent `supportAt → ed.center` requires the missing clear.

## 4. RULING: the boostReady/content-lemma OBJECT is the CLEARED residual (Option 1), recursion untouched

The `Deg1SupportedOn ed.center` (boost-center descent) property is a fact about the **cleared residual**
(Aoyagi's `D_J` after the Lemma-2 clear), NOT the raw shears-only foldResid. So it must be **stated on the
cleared object** — `foldResid` composed with the source input-clear that removes the unpaired double-count
(clear A_0's below-pivot `u₀₁₀` at the source, BEFORE branch-(ii); ordering matters — Codex Q3/Q4). This is
pnp's **Option 1**, and it is the ruling.

- **§9 RECONCILED, not reversed.** §9 correctly kept the recursion shears-only and homed the *clear* with
  boostReady. The refinement: §9's "boostReady = the clear as a DEVICE" under-specified the CONCLUSION's
  OBJECT — boostReady's conclusion `Deg1SupportedOn ed.center` is about an object, and that object is the
  **cleared** residual, not the raw foldResid. The clear belongs in the boostReady STATEMENT (the object the
  form-property is about), not merely its proof. The recursion (foldResid, StepInv on supportAt) does **not**
  change.
- **Option 2 REJECTED** (enlarge `ed.center` to the full below-pivot input row): needs an `e₂` per output
  column, contradicting the single-`e₂` predicate and changing the codim bookkeeping — unfaithful to
  Aoyagi's single-exceptional-per-step (which my (a)-fidelity confirmed).
- **Option 3 REJECTED** (splice the det-0 pivot-cross clear `r4Clear` into the recursion): breaks the
  product-preserving StepInv closure F₂ secured. Not this.

## 5. THE DECISIVE OPEN QUESTION (for L4D-render + pnp-algebra — NOT the elder to guess)

*What is the det-character of the source input-clear* (the "`A_0`'s cleared column → unit `[1,0]`",
`u₀₁₀=0`-at-source operation)? This decides HOW Option 1 is rendered:

- **STRONG PRIOR — it is a DET-1 unpaired-compensator render bug, fixable in the recursion.** The clean
  `col 0 = b_0` is what the FULL paired conjugation `(A_1·Q₁⁻¹)·(Q₁·A_0)` gives (the `Q₁` unipotent factors
  cancel — det-1, product-preserving). The render applied only the compensator half `A_1·Q₁⁻¹` (branch-(ii))
  and dropped the paired input-clear half `Q₁·A_0` (a unipotent below-pivot ROW-clear of A_0 — Aoyagi's
  `Q₁`/`F₃` half of Lemma 2, det-1). If so, the fix is a **RENDER FIX**: complete branch-(ii)'s pairing
  (apply `Q₁·A_0` too), which is det-1/product-preserving, §9-compatible (the det-0 `r4Clear` stays out),
  makes `foldResid` the properly-cleared residual, and **DISSOLVES the tension** — both StepInv AND
  boostReady then hold on the same, correctly-paired, `foldResid`, with NO statement-shape change and NO
  consumer re-wiring. This is strictly better than a separate cleared-object composition.
- **FALLBACK — if the clear is genuinely det-0/rank-reducing** (not pairable): then Option 1 proper —
  re-state the content lemma / boostReady on `foldResid ∘ clear` as a separate object; the δ=1 append crux
  (`stepInv_child_delta1_append`, `Case1Wire:333`) must consume the cleared form, and `⟨cleared⟩ = ⟨raw⟩`
  (ideal-preservation) must be checked so the child StepInv (ideal-level) transfers.

**pnp — the pointed question:** on the (2,2,2,2) witness, is the `u₀₁₀` source-clear realizable as a
**det-1 PAIRED conjugation** `(A_1·Q₁⁻¹)·(Q₁·A_0) = A_1·A_0` (product-preserving, clean `col 0 = b_0`)? Your
note's "det-0" (Option 3) referred to the pivot-CROSS clear `r4Clear` — a *different* operation from this
below-pivot input row-clear. If the input-clear is the det-1 `Q₁·A_0` half, the fix is L4D completing the
pairing in `canonNormalizationOf`, not a statement change. Confirm the det-character + whether the render's
branch-(ii) is the unpaired half.

## 6. Bottom line

The capstone target's *shape* is faithful (my (a)/(b)/(c) verdict holds); its *object* is wrong (raw
foldResid, not cleared). The recursion and F₂ are untouched. Most likely a det-1 unpaired-compensator render
bug in `canonNormalizationOf` (complete branch-(ii)'s pairing) — L4D + pnp confirm the det-character; on
det-1, it is a render fix that dissolves the tension; on det-0, Option 1's separate cleared object with the
append-crux re-wire. Options 2 and 3 are out either way.
