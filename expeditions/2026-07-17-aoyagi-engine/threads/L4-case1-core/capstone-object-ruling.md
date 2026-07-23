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

---

## §7.7 THE BRIDGE — CONVERGED to a det-1 automorphism ψ (pnp bb411f1b6; supersedes §7.6's dimension arg)

pnp found + verified (Codex-corroborated) a **det-1 polynomial automorphism** `ψ` with `F∘ψ = C`,
`det Dψ = 1`: `ψ : b₀↦b₀−2x·b₁, d₀↦d₀−2x·d₁, z↦z+2xy` (`x=u₀₁₀`=coupling, `z=u₀₁₁`=e₂). This **RETRACTS
pnp's own dimension argument** (which §7.6 leaned on): raw `F` has a flat direction, and `ψ` straightens it
to the source-cleared `C`. The bridge is therefore:

- **A det-1 IDEAL-EQUIVALENCE `ψ*⟨F⟩ = ⟨C⟩` (not ideal-equality, not a restriction), RLCT-PRESERVING**
  (`ψ` volume-preserving ⟹ `RLCT(∑F²) = RLCT(∑C²)`). This is the concrete form of the "Lemma-1-internal /
  chart" reading: `ψ` = the unipotent `Q₁` conjugation that MOVES the pivot to the cleared chart
  (`ψ` conjugates the center `I ↦ ψ(I)`). It **unifies** the det-1 and cover readings — `ψ` is the chart
  transition map. (It also vindicates the Round-1 det-1 instinct §5 withdrew; the withdrawal tracked pnp's
  since-retracted dimension argument, not an independent error.)

- **THE VALUE CHAIN (clean, read on `C`):** `RLCT(loss) = RLCT(∏C)` [def] `= RLCT via ⟨C⟩` [Aoyagi's
  invariant `⟨∏C⟩ = ⟨C⟩`, Lemma 1, p.15] `= ½·min M_{s,k}` read on `C` [Aoyagi p.22; `(D)` on `C` gives the
  monomial form]. `ψ` (det-1) separately certifies `RLCT(F) = RLCT(C)` — i.e. the Lean raw fold is
  RLCT-faithful to the cleared object. So the read-off is on `C = sourceClearedResid`; `ψ` and Lemma 1 are
  the two (consistent) bridges.

- **MEASURE-COMPATIBILITY (pnp's Codex caveat, my lane) — DISSOLVES under read-on-`C`.** pnp flagged: an
  independent accumulated-resolution Jacobian weight need not be preserved by a det-1 CoV that touches the
  exceptional (`ψ` shifts `z=e₂`: `z↦z+2xy`). **Resolution:** the faithful read is on `C` DIRECTLY (Aoyagi's
  `M_{s,k}`, p.22, which already accounts for `C`'s resolution Jacobian); `ψ` is used only for the
  **ideal-equivalence** `F ~ C` (the value), NOT to transport a *weighted integral* from `F` to `C`. So no
  `ψ`-transform of the accumulated weight is invoked — the weighted threshold is `C`'s own, read via `(D)`.
  **FALLBACK:** if the Lean architecture forces reading on `F` and transporting the weighted threshold via
  `ψ` (rather than reading on `C`), then the transformed-weight check IS needed (`ψ`'s `z`-shift) and I fire
  decorrelated Codex. The faithful read-on-`C` shape (this ruling) avoids it.

- **OPEN — the chart-faithfulness lemma (B2), pnp constructs:** `ψ` is verified for `(2,2,2,2)`
  single-coupling; wide/deep have MULTIPLE couplings (`(3,3,3,2)`: 3), and `ψ_gen` = the composite of
  per-coupling unipotent `Q₁` row-clears. Each `Q₁` is unipotent/product-preserving, so `ψ_gen` is expected
  to exist generally; constructing/verifying it explicitly on wide+deep witnesses IS the chart-faithfulness
  lemma. Layer-0 reuse: `ψ` realizes the `GL_{d₀}` gauge per-chart (corner #61/#62); intermediate reuse:
  `ψ` is the internal-layer unipotent conjugation.

**UPDATED CLOSING CONTRACT (supersedes §7.6's):** pnp — construct/verify `ψ_gen` (the chart-faithfulness
lemma B2, det-1, multiple couplings, wide+deep). L4D — render `sourceClearedResid = C`; the RLCT read-off ON
`C` (via `(D)` + the boxed rule); the `F ~ C` bridge as the det-1 `ψ` (or Lemma-1 ideal-equivalence). The
measure-compatibility dissolves under read-on-`C`; the merged recursion (F, StepInv ideal) untouched. This
is the cleanest form yet — a genuine det-1 CoV, RLCT-preserving, = Aoyagi's chart transition — and it closes
the bridge question modulo pnp's `ψ_gen` construction.

---

## §7.8 CONFIRMATION — Option 2 (spine on `C`); the append shape; the measure-compat assignment (render-brief freeze)

**(1) THE WIRING FORK — RULE Option 2′ (the controller's cleaner resolution): FOLD DEF UNCHANGED, the
READ-OFF runs on `C`.** The fork's Option-2 economy (reuse the `Deg1SupportedOn`/`MergeBoostSplit`/clean-three
machinery on the cleared object) is obtained WITHOUT superseding "recursion untouched": the fold/recursion
def stays on the raw `F` (merged, census-0, untouched); only the RLCT **read-off** (boostReady / `M_{s,k}`)
runs on `C = sourceClearedResid`, with `ψ` the proven det-1 RLCT-bridge `F ↔ C`. Both economy AND
recursion-untouched are satisfied (controller-confirmed; no operator escalation needed). It is **MORE
faithful**, not a shortcut: §7.6/§7.7 established HER read-off is on the cleared local coordinate
(`C = diag(b)·[E_J|D_J]`, p.22), so reading on `C` IS reading what Aoyagi reads; the raw `F` was the §9 Lean
artifact. Option 1 (raw spine + conjugated polynomial center) is both more expensive and LESS faithful.
Ruling: **Option 2′**, subject to the three provisos (payoff character unchanged; `ψ`-bridge PROVEN via the
landed det-1-CoV machinery, never cited; fidelity her own p.15/p.22) — all three hold.

**(2) THE APPEND SHAPE — `C` over the ORIGINAL center, NOT the conjugated-center transport.** Under Option
2 the append (`stepInv_child_delta1_append` / `foldResid_stepMap_eq_pivot_mul`) consumes `Deg1SupportedOn`
over the ORIGINAL coordinate center on `C` — the existing hard constraint is met verbatim. The
conjugated-center transport (`ψ` moves `I ↦ ψ(I)`, append consumes the transported edge) is **Option 1's**
shape and is NOT taken. So: the center-conjugation is NOT blessed as the append re-wire; Option 2's
original-center-on-`C` is.

**(3) THE `ψ`-BRIDGE STATEMENT + B2 content.** The bridge lemma: `rlctGlobal(∑F²) = rlctGlobal(∑C²)` via the
det-1 CoV `ψ` (`F∘ψ = C`, `det Dψ = 1`), by the landed
`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` machinery. Its CONTENT is exactly pnp's `ψ_gen`
(B2): the existence of the det-1 straightening for every real case11 branch (single + multi-coupling). So
**B2/`ψ_gen` suffices as the bridge's content**; the RLCT-preservation is then the landed det-1-CoV fact,
not new analysis.

**(4) THE MEASURE-COMPATIBILITY CAVEAT — REAL, and its disposition ASSIGNED.** Yes, it is a real potential
obligation: our blow-up charts DO carry exceptional-divisor (accumulated-Jacobian) weights, and `ψ` shifts
an exceptional coordinate (`z = e₂ ↦ z + 2xy`), so a *post-resolution* `ψ` applied to a weighted in-chart
integral would transform the weight (`W ↦ W∘ψ⁻¹`, non-normal-crossing) and need a singular-order check. **It
DISSOLVES iff `ψ` lifts to a PARAMETER-SPACE (pre-resolution) det-1 CoV** — which it does on pnp's own
framing: `ψ` = the unipotent `Q₁` matrix conjugation on the `A_i`, a det-1 operation on the *parameters*,
so it bridges `rlctGlobal` of the LOSS **intrinsically** (before any chart weight), and the accumulated
weight stays internal to `C`'s own resolution (Aoyagi's `M_{s,k}`, p.22) — no weighted-transport is invoked.
**ASSIGNMENT:** pnp owes a certificate item — confirm `ψ_gen` lifts to a parameter-space det-1 CoV (the `Q₁`
conjugation on the `A_i`), so the bridge is `rlctGlobal(loss)`-level (det-1 CoV of the loss), NOT an in-chart
weighted transport. The render seat consumes that as the det-1-CoV-of-`rlctGlobal` bridge lemma (landed
machinery). **Strong prior: it lifts** (`ψ` IS the `Q₁` matrix conjugation). **RE-OPEN trigger:** if pnp
finds `ψ_gen` does NOT lift to the parameter space (genuinely post-resolution only), the transported-weight
singular-order check becomes a real pnp/render obligation and I fire a decorrelated Codex on it. This is the
one item the render brief must carry as a named certificate obligation (not silently assumed).

**(5) "RECURSION UNTOUCHED" (§7.3) — PRESERVED LITERALLY (controller's Option-2′), not superseded.** The
fold/recursion def stays on the raw `F` (merged, `StepInv`, census-0 — untouched); the `F₂` work stands. Only
the RLCT **read-off** runs on `C`, bridged by the det-1 `ψ` (`rlctGlobal(F) = rlctGlobal(C)`). So the earlier
"the spine computes `C` / recursion-untouched superseded" phrasing is withdrawn — the controller's cleaner
split keeps the fold def unchanged and moves only the read-off to `C`. Both the Option-2 economy (machinery
reused on `C`) and recursion-untouched hold; the operator escalation the fork seemed to need is not required.

**Net (render-brief freeze):** Option 2; append on `C` over the original center; the `ψ`-bridge =
`rlctGlobal(∑F²)=rlctGlobal(∑C²)` with `ψ_gen` (B2) as content; the measure-compat caveat is a NAMED pnp
certificate obligation (confirm `ψ_gen` lifts to a parameter-space det-1 CoV — expected — else re-open +
Codex); "recursion untouched" → the spine computes `C`, honestly superseded. Gates before render: this §7.8
+ pnp's full `ψ_gen` (in flight).

---

## §8 THE GLOBAL MOVE — the WHOLE recursion invariant lives on `C` (18th event; pnp ∃q afa901662/d6924b708)

**The C→F bridge I flagged does NOT exist — pnp's ∃q necessity argument (Codex-confirmed, two witnesses):**
the raw case11 child `StepInv` FAILS route-independently at the continuous level. `foldB` is a product of
coordinates, so `StepInv` forces `foldB | coreGen∘foldG`; that is FALSE at the E_J slots (the SAME slots as
the boostReady obstruction). The V-restriction escape is illegitimate for an RLCT claim; L4D's whole-product
hope fails; the `∃` absorbs nothing. So there is no raw-`F` `StepInv` at case11 to bridge *to* — the raw
invariant itself is false there. **The per-node C→F bridge cannot exist; the GLOBAL MOVE is forced:
`FoldStepInvAt` + the entire `StepInv` chain live wholesale on the CLEARED object `C`.**

### RULING (direction; render GATED on pnp's soundness check)

**(1) CONFIRM the global move — and it is FAITHFUL, not costly (paper-first).** Aoyagi recurses on the
CLEARED normal form `diag(b)·[E_J|D_J]` (worked.tex:562–577 — the carried object IS the cleared
representative); she never runs on a raw shears-only fold. The raw `F` fold was OUR §9 artifact (the clear
kept out of the recursion). So moving the whole recursion invariant to `C` is **the render finally matching
the paper's own object** — the culmination of the object-split arc (§7 boostReady → §12.2 obligation-(b) →
now the whole invariant). Not scope-creep: it directly serves the expedition's goal ("her mechanism built
FULLY, faithfully"). It is a **ladder re-architecture** (the recursion's object), NOT a destination/
definition-of-done change — the payoff `rlct=C/2` is character-unchanged; so it proceeds on this ruling +
pnp's check (no operator gate for the direction; the controller may surface it async as a scope event given
its size, non-blocking).

**(2) THE RENDER GATE = pnp's cleared-recursion soundness check (I concur the gate).** pnp's honest flag: the
raw route's FAILURE is verified; the global move's SUCCESS is NOT yet — a naive residual-swap (foldResid→C,
keeping `foldG`/`foldB` raw) fails IDENTICALLY, because `StepInv` needs the cleared `foldG`/`foldB` too. So
`foldG`/`foldB` must re-architect to the cleared object, and the cleared `StepInv` must be verified to CLOSE
on witnesses. pnp constructs the cleared `foldG`/`foldB` + verifies the cleared `StepInv` (GO'd, in flight).
**No render before this ruling + pnp's soundness check both land.**

**(3) SCOPE BOUNDARY (what survives vs re-states):**
- **SURVIVES (data / geometry):** the shear DATA (`canonNormalizationOf` and the F₂ compensators — the
  coordinate-change functions), the tree/oracle structure (`buildTree`, `conOracle`), **termination**
  (`conMeasure`/`conRel_wf`), and the combinatorial exhaustion (`OracleInv`). These are `e`-parametric data
  the cleared fold reuses (applied to the cleared coords).
- **RE-STATES ON `C`:** `foldG`/`foldB`/`foldResid` (→ cleared `sourceCleared*`), `FoldStepInvAt`, the entire
  `StepInv` chain, the cleared transport laws (`sourceClearedResid_extend_delta1/delta0` — the `couplingClear`
  commutations, L4D (ii)), case12's route + δ=0 re-derived on `C` (L4D (iii)), and the Q₁-lift wired from
  `rlctGlobal` down (L4D (iv) — the §7.7/§7.8 `ψ`-bridge, now connecting the payoff to the fully-cleared
  recursion). Plus BLOCKER 1 (the append splits per-case) in every world.
- **CONSUMERS re-point** to the cleared invariant (the census/consumer map updates uniformly).

**(4) §7.8's "recursion untouched" — OWNED SUPERSESSION.** §7.8 Option 2′ ("fold def unchanged on `F`;
read-off on `C`") is SUPERSEDED: pnp's ∃q necessity shows the raw-`F` `StepInv` itself is false at case11, so
there was never a sound raw-`F` recursion to keep "untouched." The fold def MOVES to `C`. Owned: §7.8 was a
partial object-move (read-off only) that under-estimated how deep the E_J obstruction cuts (it hits the
`StepInv` divisibility, not just the boostReady support); the full move is forced. The paper-first
justification makes the supersession a fidelity WIN, not a cost — the render now IS her recursion. (My
successive object-moves — §7 → §12.2 → §8 — were each correct-in-direction and each under-scoped the reach
of the same E_J obstruction by one layer; pnp's exact-Gröbner/∃q instruments caught each under-scope before
render. The convergent endpoint: the cleared representative carries the ENTIRE resolution invariant, exactly
as Aoyagi's paper does.)

**CAPR's STEP-3 induction is UNAFFECTED — and now MORE central:** its `INV` becomes the invariant of the
REAL (cleared) recursion, not a side-object. Everything CAPR builds is already on `C`.

**Gates before ANY render:** this §8 ruling + pnp's cleared-recursion soundness check (cleared
`foldG`/`foldB` constructed; cleared `StepInv` closes on witnesses). Both must land.
