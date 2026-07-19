# Review — o5 §3 envelope-splice arc (FIDELITY)

**Reviewer:** controller-spawned, function = FIDELITY (report-only). Branch `review/o5-s3`,
worktree `.claude/worktrees/aoyagi-engine/rev-s3`, off `origin/expedition/aoyagi-engine` @ `65541573b`.
**Target:** `lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean` (headlines `clearable_of_minimizer`,
`clearable_tStar`) + its `Clearable` surface in `Engine/ClearableReify.lean`.
**Primary sources (fidelity = Lean matches THESE):** `threads/12-realization/cert-o5-realization.md`
§§0–4; `theory/aoyagi-2023-reproduction/verify-realization-gap-defect.md`;
`threads/11-construction/statement-card-o5-s3-clearable.md`; `threads/11-construction/codex/o5-s3-*`.

## Verdict: SURVIVED. No fidelity break; no soundness break. One minor provenance FINDING (item 1).

The §3 arc faithfully formalises cert §3. The Lean `Clearable` predicate is equivalent (under `Adm`)
to the certificate's `Clearable`; the envelope-splice chain is a genuine proof of the cert's four steps
(no weakened seam); the scope is minimizer-only with no `⊇ Adm` overclaim; `hmin` is a real consequence
of the banked minimizer identity, not a smuggled assumption; wording is clean.

---

## Per-item

### 1. Clearable fidelity — PASS (one minor provenance finding)

The Lean predicate (`ClearableReify.lean:48`, 0-indexed `a i = a^{i+1}`):

    Clearable M a := ∀ i j, i.val+1 = j.val → a j < a i → a i = widthMinUpto M j.val →
                       ∀ m, m.val ≤ i.val → a m = widthMinUpto M (m.val+1)

Index map to the cert (paper layer `S`, 1-indexed): a descent `a^S < a^{S-1}` is the Lean pair
`i = S-2`, `j = S-1`; `widthMinUpto M j.val = min(M^1..M^S) = r_S`, so the hypothesis `a i =
widthMinUpto M j.val` is exactly the cert's saturation `a^{S-1} = r_S`; the conclusion `∀ m ≤ i,
a m = widthMinUpto M (m.val+1)` is "prefix `1..S-1` equals the envelope `e_m = r_{m+2}`". This is the
cert §1 **saturation form** ("every strict descent from a coordinate saturating its running min has the
complete running-min envelope as prefix").

**Equivalence to the cert PRIMARY b/clear form** (`Clearable_prim` = ∀ S ∈ (b(a), clear(a)]:
`a^S < a^{S-1} ⟹ a^{S-1} < r_S`) — verified two ways:
- **Hand-proof, both directions, under `a ∈ Adm`.** (⟹) A saturated descent at `S > b` is impossible
  under `Clearable_prim` (it forces `a^{S-1} < r_S`, contradicting saturation), so the Lean implication
  fires only at `S ≤ b`, where the prefix `1..S-1 ⊆ 1..b-1` is the envelope by definition of `b` —
  conclusion holds. (⟸) Given the Lean form and a `Clearable_prim` descent at `S ∈ (b,clear]` with
  `a^{S-1} ≥ r_S`: `Adm` gives `a^{S-1} ≤ r_S` (`adm_le_widthMinUpto`), so `a^{S-1} = r_S`; the Lean
  form then forces the full envelope prefix `1..S-1`, but coord `b ≤ S-1` is strictly below the envelope
  — contradiction, so `a^{S-1} < r_S`. Boundary cases (`b=1`; all-envelope `b=clear` with empty descent
  range; touch-drop-touch; ties) all check.
- **Independent numeric scan** (`/tmp/twoform_clearable_check.py`, decorrelated from the seat's
  scripts — I implemented BOTH forms from scratch): 0 mismatches over **9967** admissible profiles
  across 1292 instances (widths ≤4, L≤5), with **1388 non-clearable** profiles present — so the two
  forms genuinely differ syntactically AND the predicate is **non-vacuous** (not trivially all-true).

**FINDING (minor, provenance — NOT a fidelity break).** The reify commit `e2bacc60b` and journal
tick-174 claim the Clearable predicate was "cross-verified against the b/clear primary form over
**64024** admissible profiles, 0 mismatches." No committed script performs that specific two-form
comparison: the batteries in the repo (`realization-battery.py` B2/B4, `clearable-characterization.py`)
implement only the **primary** form and compare it to the tree's `P(M)`; none implements the Lean
**saturation** form. The equivalence is nonetheless TRUE (hand-proof + my 9967-profile re-derivation),
so the claim's content holds — but the cited "64024-profile cross-verification" is not independently
reproducible from the repo as committed. Recommend either committing a two-form script or restating the
provenance to the actual committed evidence (primary-form battery + the equivalence argument).

### 2. No redefinition — PASS

Only two new local `def`s in the target: `envVal` (`:75`) and `spliceEnv` (`:146`). `Mval`, `Adm`,
`admBound`, `admPred`, `tPrev` (all `Foundations/Lambda.lean`), `widthMinUpto`/`runMinWidth`
(`EngineDefs.lean`), `tStar`/`tStar_mem`/`Mval_tStar_eq_inf'` (`RouteMAchieverPath.lean`) are the single
banked decls, imported — grep confirms exactly one `def` each repo-wide; no shadowing local re-statement.

### 3. The splice chain — PASS (seam is a real proof, not a weakened placeholder)

Each lemma maps to a cert §3 step and is genuinely proved (index alignment `i=S-2, j=S-1` ↔ paper
layer `S`; splice sets Lean coords `≤ i` = paper `1..s-1` to the envelope):
- `spliceEnv_term_zero` (`:200`) = **step 1**: prefix summand `= 0` via
  `widthMinUpto M (k+1) = min(widthMinUpto M k, M k.succ)` killing one factor + `ring`. Real.
- `prefix_forces_env` (`:82`) = **step 2** (contrapositive): a genuine `Nat.strong_induction_on` — the
  factored zero forces `a k = widthMinUpto M (k+1)` in both the `tPrev = a k` and `M k.succ = a k`
  branches, using the IH + `adm_le_widthMinUpto` + `widthMinUpto_succ`. Real.
- `spliceEnv_mem_Adm` (`:162`) = **step 3a**: block bounds via `spliceEnv_le_envVal` +
  `envVal_le_admBound`; the weak-decrease **seam** (t04's ex-placeholder) is the completed calc
  `a q ≤ a j ≤ a i = widthMinUpto M j.val ≤ widthMinUpto M (p+1)`, using `hdesc` and `hsat` — a genuine
  proof of monotonicity across the seam, not a weakened statement. Last coord `0` handled (`i.val < L-1`
  since `j.val ≤ L-1`).
- `spliceEnv_term_eq` (`:229`) = **step 3b**: the boundary term `j=s` AND all suffix terms `j>s` are
  proved EQUAL to `a`'s (a genuine equality of the actual `Mval` summands). At the seam the predecessor
  `spliceEnv i = widthMinUpto M j.val = a i` **by `hsat`** (`:246`, `← hsat`); beyond, predecessor lies
  outside the splice so `= a`. This is exactly cert 3(b)'s "boundary uses `a^{s-1}=r_s=b^{s-1}`,
  UNCHANGED; suffix UNCHANGED" — not a placeholder, not weakened.
- `mval_spliceEnv_lt` (`:259`) = **step 3c**: `Finset.sum_lt_sum` — prefix `0 ≤ a`-summand
  (`mval_term_nonneg`), suffix `=` (`spliceEnv_term_eq`), strict at the bad coord obtained by the
  contrapositive of `prefix_forces_env`. Real.
- `clearable_of_minimizer` (`:287`) / `clearable_tStar` (`:298`) = **step 4**: minimizer ⟹ Clearable
  by contradiction with the strictly-cheaper admissible sibling. `hdesc`/`hsat` threaded correctly.

### 4. Minimizer-only scope — PASS

No theorem states or implies `⊇ Adm` / stratum-completeness. Names honor the pin: `clearable_of_minimizer`,
`clearable_tStar` — no `*_complete` / `*_eq_Adm`. File header (`:9–17`) states MINIMIZER-ONLY and points
the full `⊇ Clearable-Adm` at R7 (`realizedProfiles_eq_clearableAdm`, sorried). The `⊇ Adm` FALSE gap is
cited at the definition site (`ClearableReify.lean` docstrings name defect #4 + the ledger path). The
statement card's composition note correctly records that §3 alone does NOT close `o5_core` (needs §4 +
wiring) — no premature-"done". Minor: the O5Realization header points to R7 but does not repeat the
`verify-realization-gap-defect.md` path (it lives one import away in ClearableReify) — acceptable.

### 5. hmin genuineness — PASS

`clearable_tStar`'s `hmin` (`fun b hb => by rw [Mval_tStar_eq_inf']; exact Finset.inf'_le _ hb`) is a
real consequence of the banked `Mval_tStar_eq_inf'` (`RouteMAchieverPath.lean:92`, proved via
`(exists_tStar M).choose_spec.2`, sorry-free) + `Finset.inf'_le` — not an axiom-shaped hypothesis.
`tStar_mem` likewise proved (`choose_spec.1`). `mval_term_nonneg`'s two-factor nonnegativity uses the
generic-`Adm` bounds `tStar_le_tPrev` / `tStar_le_Msucc` (`RouteMAchieverPath.lean:36,52`) — despite the
`tStar_`-prefixed names these are stated over an arbitrary `T ∈ Adm M` (`T j ≤ tPrev`, `T j ≤ M j.succ`),
so the application to `a` is correct. (Peripheral: the two lemma names are misnomers — generic bounds,
not `tStar`-specific — but they are banked, outside this arc's scope.)

### 6. Wording scrub — PASS

`grep -rniE` of the banned-wording list over `O5Realization.lean` + `ClearableReify.lean`: zero hits.
No `sorry`/`axiom` in `O5Realization.lean`.

---

## Codex decorrelation (highest-risk item = Clearable fidelity)

Consult `codex/clearable-fidelity-{prompt,answer}.md` (gpt-5.x, xhigh, read-only, hypothesis-neutral —
asked to hunt a counterexample to the equivalence). Corroborates and does not break the arc:

- **Q1 (equivalence) — Codex: PROVED, both directions**, via the same contrapositive as my hand-proof
  (`a^{S-1} ≤ r_S` from `Adm` makes `b<S ⟹ a^{S-1}<r_S` and `a^{S-1}=r_S ⟹ b≥S` contrapositives).
  Boundary checks match; Codex adds a touch-drop-touch witness `M=(5,5,3,2,2), a=(5,2,2,0)` (envelope
  `e=(5,3,2,2)`, `b=2`, re-touches at coord 3, descent at `S=4` from `a^3=r_4=2`) — both forms reject.
- **Q2 (saturation hypothesis non-redundant) — Codex: COUNTEREXAMPLE to redundancy** `M=(3,3,3), a=(2,0)`
  (`a^2=0<a^1=2<r_2=3`: strict descent from BELOW the running min, saturation false ⟹ vacuously clearable).
  Confirms the Lean hypothesis `a i = widthMinUpto M j.val` genuinely narrows the triggering descents.
- **Q3 (faithfulness) — Codex: UNSURE**, and raised one concrete potential false positive:
  `M=(3,3,3), a=(3,0)` accepts despite the birth descent `a^1=r_2=3` sitting above the layer-2 reachable
  ceiling `2`; Codex could not tell (no tree code) whether birth is exempt. **Settled against the sim
  ground truth** (`/tmp/codex_q3_check.py`): the recursion DOES realize `(3,0)` at `t̃=0` — a TRUE
  positive. Cert §2's birth-layer exemption ("envelope coords are born directly at head value by Case 2,
  no pull") is the correct reading; the predicate classifies it faithfully. The touch-drop-touch and
  `(2,0)` cases also agree with ground truth (`clearable == realized` on all three). No false positive.

Net: the decorrelated read strengthens item 1 — equivalence PROVED independently, non-vacuity confirmed,
the one raised faithfulness doubt resolves as a true positive against the simulator.

---

## Peripheral (not §3 findings, surfaced)

- `tStar_le_tPrev` / `tStar_le_Msucc` (`RouteMAchieverPath.lean`) are generic-`Adm` bound lemmas with a
  misleading `tStar_`-prefix — naming imprecision in banked code, outside the audit target.
- The two-form Clearable cross-check would be worth a committed script (see item-1 finding) so the
  saturation↔primary equivalence rides in the repo, not just in commit prose.
