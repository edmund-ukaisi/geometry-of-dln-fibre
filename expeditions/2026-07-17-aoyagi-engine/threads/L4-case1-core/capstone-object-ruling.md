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

## 6. Bottom line (superseded by §7 — all inputs now in)

The capstone target's *shape* is faithful (my (a)/(b)/(c) verdict holds); its *object* is wrong (raw
foldResid, not cleared). The recursion and F₂ are untouched. [My §5 "det-1 render-bug, complete the pairing
in the recursion" prior is **withdrawn** — see §7: the verified repair is a source-COLUMN-clear on ANCESTOR
edges, a derived object, and the merged recursion is untouchable by constraint; it is Option 1 proper, not a
recursion-branch fix.]

---

## 7. FINAL RULING (#69; all inputs in — kill-condition FINAL, repair VERIFIED, paper-first confirmed)

**Status of inputs.** Kill-condition FINAL = **CHART-ONLY** (pnp 02049b6ac + Codex concur). Repair
**VERIFIED** (pnp 672007eb8, both witnesses, all slots, exit-0). Triple-confirmed (pnp + Codex + L4D
def-owner). My source-validation **vindicated** (level-confusion, not error). This section supersedes §5's
open det-character question.

### 7.1 PAPER-FIRST (step 1, the operator's rule) — CONFIRMED at the source

Her recursion carries boost-readiness **of the CLEARED representative**, not the raw product. Confirmed on
pp.15–18 (fresh): the invariant (p.15, :562–577) is the **ideal equality** `⟨∏C⟩ = ⟨diag(b)·[E_J|D_J]·∏C⟩`;
the step (pp.17–18) applies **regular** matrices `Q`, `P` (unipotent, Lemma-1-neutral) and factors
`u_{S,J+1}` to produce the NEXT cleared normal form `diag(b')·[E_{J+1}|D_{J+1}]`, and recurses on THAT. The
raw product `∏C` appears **only inside the ideal `⟨·⟩`**. So boost-readiness (the b-ledger, the `D_J`
structure) is a property of her **cleared** `D_J`. **The Lean raw-`foldResid` statement of the property
rendered it of the WRONG OBJECT.**

### 7.2 The (B)/(D) language (adopt it in the re-shaped statements)

- **(B)** — degree ≤ 1 per coordinate, no `u_{e₂}²` ("multilinear-clean"): **TRUE of the raw shears-only
  foldResid, everywhere.** This is what F₂ delivers, what batteries #48–56 proved; a correct raw fact,
  already consumed correctly. It STAYS on the raw object.
- **(D)** — slots `∈ ⟨ed.center⟩` (`Deg1SupportedOn`, the wall's conclusion): **FALSE of raw, TRUE of the
  source-cleared object.** (B) ⊬ (D): the input coupling `u₀₁₀` is degree-1 (so (B)) but outside
  `⟨ed.center⟩` (so ¬(D)). The 25 prior instruments tested (B); the wall needs (D) — why they missed it.
- The chart value at the `e₂` slot is the birth Schur exceptional `u₀₁₁ − u₀₀₁·u₀₁₀`; the extra block
  factors through its CONSTITUENT `u₀₁₀`, never raw `u_{e₂}`.

### 7.3 THE RULING — a named cleared object + an ideal-equality bridge (Option 1 proper)

1. **New derived object `sourceClearedResid d p`** := `foldResid d (canonFlatten d) p` composed with the
   ancestor-column-clear map (pnp's verified repair: clear each ancestor case2/case12 cleared-column's
   below-pivot INPUT entries BEFORE that edge's shear; the **COLUMN-clear alone suffices**, the row-clear is
   not needed). This object is canonFlatten-pinned (a concrete-chart operation — consistent with the idiom
   ruling: the derivation lives at canonFlatten).
2. **(D) is re-stated OF `sourceClearedResid`.** `realBranch_boostReady_case11` concludes
   `Deg1SupportedOn (sourceClearedResid d p) ed.center`; `foldResid_case11_mergeBoostSplit_canon` asserts
   `MergeBoostSplit` of `sourceClearedResid`. This makes §9's "BOOSTREADY = the form" **literal**: the form
   is a NAMED OBJECT, not a device inside a proof of a false raw statement.
3. **The merged recursion is UNTOUCHED.** `foldResid` (StepInv, product-preserving, census-0) stays raw and
   shears-only; the source-clear does NOT enter `foldResid`. (B) stays a raw fact.
4. **The CLEARED↔RAW BRIDGE (the gating design item) = an ideal-equality bridge.** The source-column-clear
   is a **regular / Lemma-1-neutral** operation (her `Q`,`P` are regular; the column-clear is unipotent,
   det-1, ideal-preserving), so `⟨sourceClearedResid⟩ = ⟨foldResid⟩`. The append crux
   (`stepInv_child_delta1_append`, `Case1Wire:332–369`) is re-wired to consume **cleared-(D)** and produce
   the child StepInv; the raw child's StepInv `∃q`-witness transports through the Lemma-1-neutral clear (the
   StepInv is an existential ideal-divisibility, so the specific `q` may change — the `∃` absorbs the
   transport; only the ideal fact must transport, and it does under a regular clear). **This matches HER
   accumulation exactly:** she carries the invariant of the cleared representative and the raw product
   appears only inside `⟨·⟩`; the Lean shape (cleared object carries (D); the raw StepInv rides the
   ideal-equality) is the faithful transcription of that.

### 7.4 The re-shaped chain (old → new; L4D def-owner renders, pnp certifies)

| lemma | OLD | NEW |
|---|---|---|
| `sourceClearedResid` | — | NEW: `foldResid ∘ ancestor-column-clear` (canonFlatten-pinned) |
| `foldResid_case11_mergeBoostSplit_canon` | `MergeBoostSplit … (foldResid …) …` | `MergeBoostSplit … (sourceClearedResid …) …` |
| `realBranch_boostReady_case11` | `Deg1SupportedOn (foldResid p) ed.center` | `Deg1SupportedOn (sourceClearedResid p) ed.center` |
| `MergeBoostSplit.deg1SupportedOn` (assembly) | — | **UNCHANGED** (true implication, reusable — L4D confirmed) |
| `case1_conjA` / `stepInv_child_delta1_append` | consumes `hdeg1` on raw `foldResid` | consumes cleared-(D) + the **ideal-equality bridge** → raw child StepInv `∃q` |
| LL case11 / conjunct-2 / born-unit contract | on raw `foldResid` | re-point to `sourceClearedResid` + the same bridge |

### 7.5 Rejections + the honest self-correction

- **Option 2** (enlarge `ed.center` to the below-pivot input row) REJECTED — needs an `e₂` per output
  column, contradicts single-`e₂`, breaks the codim bookkeeping; unfaithful (my (a)-fidelity + her
  single-exceptional-per-step).
- **Option 3** (splice the clear into the recursion) REJECTED — forbidden by the "merged recursion
  untouched / render-around forbidden" constraint, and it breaks F₂'s census-0 closure.
- **Self-correction (owned):** my §5 prior ("det-1 render-bug — complete branch-(ii)'s pairing IN the
  recursion") is WITHDRAWN. pnp's verified repair is a source-column-clear on ANCESTOR edges (a global
  derived object), not a local case11 recursion-branch; and the constraint forbids touching the merged
  recursion. Direction (Option 1, cleared object) was right; the recursion-branch rendering was wrong.

### 7.6 What pnp certifies / L4D renders (the closing contract)

- **pnp** — the positive per-edge certificate for `sourceClearedResid`: (i) cleared-(D) holds (done — the
  verified repair); (ii) `⟨sourceClearedResid⟩ = ⟨foldResid⟩` (Lemma-1-neutrality of the column-clear);
  (iii) the append's StepInv `∃q` transports across the bridge (the one genuinely-open verification — that
  cleared-(D) → the raw child StepInv the append needs).
- **L4D** — define `sourceClearedResid` (the ancestor-column-clear map); re-state the chain (7.4); render
  the ideal-equality bridge lemma; re-point the append crux + LL's contract. The payoff/destination
  unchanged; the merged recursion untouched.

The wall's *shape* was faithful; its *object* is corrected to the cleared representative her recursion
actually carries. The remaining critical path (fresh formaliser, pnp's certificate, LL's two renders) is
unblocked on this ruling.

---

## §7.5 AMENDMENT — the bridge is NOT ideal-equality; it is COVER/CHART-membership (pnp crossing 5aa7dadad)

### RETRACTION (owned — my second correction in this arc)

§7.3 item 4 asserted the bridge = ideal-equality `⟨sourceClearedResid⟩ = ⟨foldResid⟩` via "the column-clear
is regular/Lemma-1-neutral." **pnp's exact Gröbner REFUTES it:** `sourceClearedResid = foldResid`
restricted to the hyperplane `{coupling = 0}` — a **RESTRICTION** (`⟨src⟩ ≠ ⟨raw⟩`, ideal-**changing**),
NOT a regular transform, NOT product-preserving. My "regular column-clear ⟹ ideal-neutral" was wrong: a
restriction is not a conjugation. Consequently the per-slot `(D)` is **not ideal-invariant** (a restriction
can change the RLCT), so no ideal-equality bridge exists, and closing-contract item (ii) as I dispatched it
would FAIL. Owned.

### PAPER-FIRST (the amendment's step 1) — CONFIRMED: Case 1(1) is a BLOW-UP CHART

Re-read pp.15–16 (fresh) with the pointed question. p.15: "**Construct the blow-up** along the submanifold
`{d_{ij}=0 (…), u_{s,k}=0}`." p.16: "**Case 1(1): Consider instances in which** [the `J₁`-row block]
`= u_{s,k}·[d']`"; Case 1(2): the complementary instances (only the first row factors, `u_{s,k}=u_{S,J+1}·u'`).
So **Case 1(1)/1(2)/Case 2 are the CHARTS of the blow-up cover** — the RLCT is the **min over charts** (the
boxed rule). The `{coupling=0}` is Aoyagi's `E_J = identity` (the cleared columns' below-pivot = 0),
established at **ANCESTOR** edges by her regular Lemma-2 clears — ideal-neutral *at the ancestor's product*
— and manifested at the case11 edge as the chart's coordinate structure. This is candidate **(b) CHART/COVER**
(with candidate (a) — the ancestor clears are regular — as *why* the coupling is legitimately fixed). It is
NOT candidate (c): the source is explicit that Case 1(1) is a blow-up chart.

### THE BRIDGE'S TRUE SHAPE — cover/chart-membership (the fan), not ideal-equality

`sourceClearedResid` is the residual **on the Case-1(1) chart** of the blow-up, where the coupling is fixed
by the chart's coordinates (the ancestor `E_J = identity`). `(D)` holds on this chart. **RLCT-soundness =
the boxed rule's min-over-charts:** the case11 chart is ONE branch of a COMPLETE cover (Case 1(1)/1(2)/Case 2
— the fan), which covers `coupling ≠ 0` in the other branches. So re-stating `(D)` on the chart is
RLCT-legitimate *because it is a genuine blow-up chart of a complete cover*, not because of any
ideal-equality. **The `pnp-fan` machinery (tasks #11–14, the fanned cover) is the relevant banked asset** —
the bridge is cover-membership, and the fan certificate is what carries the RLCT-soundness.

### INTERMEDIATE-layer RLCT-soundness (team-lead's OPEN item) — LIKELY RESOLVED, pnp verifies

The blow-up chart structure is **UNIFORM over `S`** (Case 1(1) applies at every `S = 1,…,L`, pp.15). So the
chart-legitimacy of fixing the coupling is NOT a layer-0-only gauge argument (that was the corner ruling
#61/#62's frame) — it is the uniform blow-up chart structure, which applies at intermediate layers equally.
**So the intermediate case is EXPECTED to resolve uniformly** — but it rides a verification only pnp can do:

**THE POINTED VERIFICATION (pnp):** on the intermediate witness `(2,2,2,2,2)` (case11 at layer 2 reusing a
layer-1 divisor), is the coupling coordinate fixed by a **genuine ancestor blow-up chart** (the ancestor
case2/case12 `E_J = identity` clear), so `{coupling=0}` IS a real chart of the cover (RLCT-legitimate)? OR
does the coupling manifest through output-layer coords that NO ancestor chart fixes (an uncovered coupling →
a genuine gap, re-open, candidate (c) after all)? Your (5aa7dadad) already localised the openness here; this
names what settles it.

### CORRECTED CLOSING CONTRACT (supersedes §7.6)

- **pnp:** (i) cleared-`(D)` on the chart [done]; **(ii) RETRACTED** — do NOT certify ideal-equality (it is
  false). INSTEAD: certify that `sourceClearedResid` IS the Case-1(1) blow-up-chart residual (the
  `{coupling=0}` is the chart's coordinate fixing / ancestor `E_J=identity`, not an arbitrary hyperplane) on
  BOTH a layer-0 witness AND the intermediate `(2,2,2,2,2)`; **(iii)** the RLCT-soundness — the chart is one
  branch of a COMPLETE cover, so min-over-charts gives the right RLCT (tie to the `pnp-fan` cover
  certificate). The old "StepInv `∃q` transport across an ideal-equality bridge" (#70's linchpin) is
  RE-CAST: it is a **cover/leaf** obligation (the case11 chart's `(D)` feeds the per-leaf value; the RLCT is
  the min over the fan), not an ideal-transport.
- **L4D:** `sourceClearedResid` := the Case-1(1) chart residual (derived object); `(D)` stated of it; the
  append/consumer bridges by **cover structure** (the fan/leaf machinery carries RLCT-soundness), NOT an
  ideal-equality lemma. Merged recursion (per-branch foldResid) untouched; payoff/destination unchanged.
- **RE-OPEN trigger:** if pnp's (ii)/(iii) shows the intermediate coupling is NOT chart-legitimate (an
  uncovered output-coord coupling), the cover-membership bridge fails at intermediate layers → genuine gap;
  I then fire a decorrelated Codex and re-adjudicate (candidate (c)).

**Net:** the bridge is cover-membership (the fan), not ideal-equality (retracted). Paper-first grounds it
(Case 1(1) = blow-up chart, uniform over `S`). The one open verification is pnp's chart-legitimacy of the
intermediate coupling — expected to hold (uniform chart structure), which would close the arc via the banked
`pnp-fan` cover asset.

---

## §7.6 THE PRECISE BRIDGE (for pnp certification) — grounded in Aoyagi p.22's explicit min-over-charts

The algebraic design space is CLOSED (pnp 9bdbb29e3): ideal-equality FALSE, decomposition FALSE, and the
**dimension argument** (`sourceClearedResid = raw|_{u₀₁₀=0}` has strictly fewer essential coordinates than
raw — no det-1 CoV bridges a function to one with fewer essential coords) **permanently kills the det-1
render-fix class**. So the bridge is neither ideal nor CoV; it is **cover-membership**, and it is Aoyagi's
OWN framework:

**PAPER GROUND (p.22, verbatim intent):** "Candidates for the log canonical threshold of `‖∏C‖²` **on this
local coordinate** are `½·min{M_{s,k} : t̃_{s,k}=0}`." Her recursion produces **local coordinates (charts)** —
the leaves of the resolution tree (Case 1(1)/1(2) split a partial run, Case 2 splits a full run; each
"consider instances in which …" is a chart); the RLCT is `½·min over charts` of the candidate `M_{s,k}`. This
IS the boxed rule, and the Lean side has it: `rlctAt_sumSqFam_eq_iInf_charts` (LANDED).

**THE BRIDGE, precise:**
1. The case11 chart is ONE local coordinate (leaf-subtree) of the cover. Its residual is the cleared
   representative `diag(b)·[E_J|D_J]` with `E_J = identity` — the coupling `u₀₁₀` fixed BY the chart's
   coordinate structure (the ancestor regular `Q`,`P` clears that build `E_J`, pp.17–18/20–21). This chart
   residual **is** `sourceClearedResid`; `(D)` holds on it.
2. The coupling `u₀₁₀ ≠ 0` locus is covered by SIBLING charts (Case 1(2) / Case 2 / the complementary
   blow-up chart), each with its own candidate `M_{s,k}`.
3. `RLCT = ½·min over ALL charts`. The case11 chart contributes its `(D)`-based candidate; the siblings
   contribute theirs. So `(D)` on `sourceClearedResid` is RLCT-legitimate **because the chart is one member
   of a complete cover and the RLCT is the min** — NOT because fixing `u₀₁₀` is RLCT-neutral (it is not; the
   dimension argument shows raw genuinely depends on `u₀₁₀`, and a lone restriction WOULD change the RLCT —
   but the sibling charts restore the missing locus).

**CERTIFICATION OBLIGATIONS (pnp — RLCT/cover-level, not slot-Gröbner; the `pnp-fan` cover asset + a
Jacobian/`M_{s,k}` argument):**
- **(B1) cover completeness** — the charts cover; the `u₀₁₀ ≠ 0` locus lies in sibling charts. Verify at the
  intermediate witness `(2,2,2,2,2)` (the fan certificate #11–14 + Aoyagi's "consider instances" splits).
- **(B2) chart faithfulness** — `sourceClearedResid = foldResid|_{u₀₁₀=0}` IS the case11 chart's residual
  (the `{u₀₁₀=0}` is the ancestor `E_J=identity` chart-coordinate fixing, NOT an arbitrary hyperplane), at
  layer-0 AND intermediate. This is the crux at intermediate reuse: is the coupling coord a genuine ancestor
  chart coordinate, or an uncovered output coord?
- **(B3) min-over-charts** — `RLCT = ½·min over charts` (Aoyagi p.22; Lean `rlctAt_sumSqFam_eq_iInf_charts`
  LANDED). The case11 chart's `M_{s,k}` (read via `sourceClearedResid`, where `(D)` gives the monomial form)
  is a legitimate term.

**THE ONE HONEST WORRY to certify (the Lean/paper reconciliation):** the Lean recursion's per-branch object
is the shears-only `foldResid` (coupling surviving); Aoyagi's local coordinate is the cleared chart residual
(coupling fixed). They are ideal-DIFFERENT (pnp). The bridge's soundness is that the RLCT **read-off** uses
`sourceClearedResid` (the faithful chart, `(D)` holds, `M_{s,k}` read), while the recursion's `foldResid`
supplies the ideal-equality to `∏C` for the VALUE — and the two reconcile in the min-over-charts because
`sourceClearedResid` IS Aoyagi's local coordinate for that leaf. pnp certifies that `sourceClearedResid`'s
`M_{s,k}` is the true chart candidate and the min over charts is the RLCT.

**Layer-0** stays covered by the corner/gauge ruling (#61/#62; `u₀₁₀` = the `GL_{d₀}` input gauge, P₁
absorbed once). **Intermediate** ((2,2,2,2,2)) rides B1/B2 — expected to hold (uniform chart structure), the
`pnp-fan` asset carrying it. **RE-OPEN** only if B2 fails at intermediate (the coupling is an uncovered
output coord) — then I fire decorrelated Codex + re-adjudicate.

**My role ends here** (the bridge is stated precisely + paper-grounded); the certification is pnp's
RLCT/cover-level work, and L4D renders `sourceClearedResid` + the cover-structured append on pnp's positive
certificate.
