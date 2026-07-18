# Cert — (2,2,2,2) chart-atlas closure, the depth-3 R2 leg (pen-and-paper thread 08, SECOND task)

*Seat: `pen-and-paper` (pnp08), commissioned by the controller as the depth-3 leg of the R2 gate
(my own recommended next probe). Same discipline as cert-atlas-probe.md: Aoyagi 2023 **page images**
p.14–22 + exact integer algebra; the Lean engine was **not** read. One fresh decorrelated Codex consult
(`codex/closure-2222-{prompt,answer}.md`, gpt-5.x `xhigh`, hypothesis withheld). Battery
`battery/closure-2222.py`, exit-0, integer-only.*

**Instance.** `M=(2,2,2,2)`, depth `L=3`, four widths all 2; `C^{(1)},C^{(2)},C^{(3)}` each 2×2 at the
origin; ideal `J=⟨entries of P=C^{(1)}C^{(2)}C^{(3)}⟩`. `minAdm(2,2,2,2)=3` (⇒ `λ_core=3/2`,
reproduction ground truth). Register key as in cert-1.

**The node the controller named.** `(S,J,J₁)=(3,0,1)`, selected level `t̃=1`, two competing divisors:
`A=(1,1,1)` (born layer 1, rank level 1, `M=1`) and `B=(2,1,1)` (born layer 2, **Case 2**, head reset
to `M^{(2)}=2`, tail `=J=1`, `M=1`). Distinct, comparable `A<B`, same `t̃=1`. Def 4 (componentwise `≤`)
selects the minimum `A`.

**Two-way decorrelated agreement.** My exact-algebra battery and Codex's independent chart-tree replay
agree on all three deliverables: the terminal atlas `{000,100,110,200,210,220}`, the minimum `3` with
no undershoot, and the incomparability produced by the wrong tie-break pick.

---

## Verdict (a) — COVERAGE / closure (direction: OBSTRUCTION; empty gap-hunt = evidence)

**Computation.** Enumerate the admissible nested profiles (`= the rank strata`); confirm the binding
ones are emitted; hunt for a missing stratum / coverage gap (`closure-2222.py`; Codex chart-tree replay).

**Exact result.** `[CERT]` the admissible nested profiles `t=(t¹≥t²≥t³=0)` are exactly
`{(0,0,0),(1,0,0),(1,1,0),(2,0,0),(2,1,0),(2,2,0)}` (6). `[OBS, Codex]` its independent replay to
termination emits **the same six** `t̃=0` profiles (5 terminal chart types, union = these six), and its
elementary coverage audit is decisive at the stratum level: every zero of `P` has partial-product ranks
`(rank C^{(1)}, rank(C^{(1)}C^{(2)}), 0)`, which is **necessarily one of these six weakly-decreasing
triples** — so **no rank stratum is missing**. `[CERT]` the three binding profiles (min, below) are all
admissible and emitted. `[CERT, non-toric]` the best coordinate-weight bound at `(2,2,2,2)` is `4/2=2 >
3/2` — loose, as at `L=2`; the binding divisor is non-toric at depth 3 too.

**Scoped-claim wording.** `[CERT]` *At `(2,2,2,2)` the emitted `t̃=0` atlas is exactly the six rank
strata, which cover `{P=0}` at the stratum level (partial-product-rank triple), and the three binding
strata are emitted.* `[SCOPE]` the stronger **pointwise proper cover** (every nearby zero has a chart
lift, charts proper) is **not** provable from the page transcription (coordinate maps + pivot subcharts
not supplied) — it remains the R2 obligation, and (cert-1) is genuinely non-toric.

**→ (a): NO coverage gap at the stratum level (six strata, all reached; binding strata emitted). The
proper pointwise cover is the standing R2 hole; non-toric confirmed at depth 3.**

---

## Verdict (b) — the emitted `t̃=0` MINIMUM stays 3, no undershoot

**Computation.** `Mval` over the emitted `t̃=0` profiles (`closure-2222.py`; Codex substitution).

**Exact result.** `[CERT]` (both derivations agree):

| `T` (`t̃=0`) | `000` | `100` | `110` | `200` | `210` | `220` |
|---|---|---|---|---|---|---|
| `Mval` | 4 | **3** | **3** | 4 | **3** | 4 |

min `= 3 = minAdm(2,2,2,2)`, achieved at `(1,0,0),(1,1,0),(2,1,0)` (three minimizers); **no `t̃=0`
divisor has `Mval<3`** — no undershoot. `[CERT, subtle]` the `M=1` divisors `(1,1,1),(2,1,1),(2,2,1)`
that the construction *does* create have `t̃=1`, so by Aoyagi's `t̃=0` restriction (p.22) they do **not**
enter the candidate min — they are red herrings, not undershoots (same mechanism as cert-1 leg 5).
`[OBS, Codex]` every terminal chart already contains `(1,0,0)[3]`, so each chart's own minimum is 3.

**→ (b): min = 3 = minAdm, three minimizers, NO undershoot. The construction's own `M=1` (positive-`t̃`)
divisors are fenced off by the `t̃=0` rule.**

---

## Verdict (c) — the tie-break's choice is LOAD-BEARING (the faithfulness content)

**Computation.** At `(3,0,1)`, apply Case 1(1) (tail `t^{(3)}:=J=0`) under the **correct** pick (`A`)
and the **wrong** pick (`B`); check total-comparability (Def 4) of the resulting divisor set and the
emitted minimum (`closure-2222.py`; Codex Q_C).

**Exact result** (both derivations identical to the component):
- **WRONG (fix non-min `B`):** `B=(2,1,1) → (2,1,0)`; the other divisor `A=(1,1,1)` remains.
  Compare: `(2,1,0)` vs `(1,1,1)` — `2≰1` and `0≱1` ⇒ **INCOMPARABLE** ⇒ the **total-comparability
  invariant (p.15) is VIOLATED**. `Mval(2,1,0)=3`.
- **CORRECT (fix min `A`):** `A=(1,1,1) → (1,1,0)`; `B=(2,1,1)` remains. Compare: `(1,1,0)≤(2,1,1)`
  (`1≤2,1≤1,0≤1`) ⇒ comparability **preserved**. `Mval(1,1,0)=3`.
- **The emitted minimum is `3` under BOTH choices** (both merged divisors are `Mval=3` minimizers).

**Interpretation.** `[CERT]` **The p.15 minimality tie-break protects the total-comparability INVARIANT
— not the numerical minimum.** The numerical candidate min is *choice-independent* (`3` either way), so a
**value-only / finiteness certificate is BLIND to a tie-break faithfulness break**; only the full-`T`
comparability invariant detects it (the wrong pick yields incomparable `T`-vectors). `[SCOPE, Codex flag
preserved]` breaking the invariant *provably* removes the construction from its stated-valid regime; the
step from "invariant broken" to "actual pointwise coverage gap" (vs merely "the coverage/monomialization
**proof** no longer applies") rides on the construction's asserted invariant→principalization link,
which is **not re-derived here**.

**→ (c): the tie-break is LOAD-BEARING for FAITHFULNESS (the comparability invariant ⇒ valid
principalization ⇒ coverage), NOT for the value. Decisive corollary: the finiteness value cannot detect
a wrong tie-break (both give 3) — so maintaining/checking the invariant needs the full `T`, not `t̃`.
This is the depth-3 confirmation of cert-1 verdict 3 + council verdict 3a: full-`T` in the State is
necessary precisely because the value is blind to what it protects.**

---

## Codex decorrelation summary

`[OBS]` Codex (hypothesis withheld) independently: (i) replayed the `(2,2,2,2)` chart tree — five
terminal chart types, union of `t̃=0` profiles = **the same six** as my nested-profile enumeration, and
sharpened Q_A by noting only **two** `S=1` divisors exist (`(0,0,0)` and `(1,1,1)`; rank level `r=2` has
`M=0`, no exceptional divisor); (ii) matched the `Mval` table and `min=3` with the same three minimizers,
and flagged the `t̃=1` `M=1` red herrings; (iii) computed the **same** incomparability under the wrong
pick (`(2,1,0)` vs `(1,1,1)`: `2≰1`, `1≰0`) and the same preserved comparability under the correct pick;
(iv) returned the verdict "the tie-break protects the comparability invariant / valid principalization
(coverage), with the minimum unchanged either way."

`[OBS] Codex "most likely wrong"` (inference flags preserved, NOT promoted): Q_A — pointwise coverage is
inferred from the meaning of "charts" (coordinate maps / pivot subcharts not supplied); Q_B — the
six-profile completeness rests on the inferred `S=1→2` boot + divisor-persistence (the *arithmetic* is
exact); Q_C — incomparability *certainly* breaks the stated invariant, but equating that with an actual
coverage failure (vs loss of the coverage *proof*) uses the asserted invariant→principalization link.
My verdicts (a,b) do not rest on the tree (the profile set is established from the minAdm recursion; the
strata cover by the rank-triple audit); (c) is verified at rule level for the two `T`-vectors + the exact
comparability computation, tree-level only for their live coexistence at `(3,0,1)`.

---

## Close (firmest / most likely to break / next)

- **Firmest:** at `(2,2,2,2)` the emitted atlas is the six rank strata, `min=3=minAdm` with no
  undershoot, and — the sharp depth-3 finding — the tie-break protects the **comparability invariant**,
  not the value: the wrong pick leaves the value at 3 but makes `T`-vectors incomparable. Verified two
  independent ways (exact battery + Codex replay), agreeing to the component.
- **Most likely to break the closure:** the **pointwise proper cover** (R2) — still un-proved by Aoyagi,
  still non-toric at depth 3, and it must include the suppressed pivot subcharts; the stratum-level
  audit does not substitute for it. And the invariant→coverage link (Codex Q_C flag) is asserted, not
  re-derived — worth a bedrock note when R2 is formalised.
- **Next:** the depth-3 tie-break is exercised here; the remaining decorrelated unknown is the pointwise
  cover-image over the *constructed* atlas (coordinate maps), which needs Aoyagi's chart transforms
  (Lemma-2 unipotents) instantiated — the architect's construction lane, gated by this cert's stratum-
  level closure + the invariant-maintenance requirement (full-`T`).
