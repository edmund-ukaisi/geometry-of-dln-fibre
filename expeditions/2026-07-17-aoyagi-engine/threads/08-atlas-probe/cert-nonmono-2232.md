# Cert — (2,2,3,2) truth-value: fork 12(b), GATES the Adm / IsFullMonomialization discharge

*Seat: `pen-and-paper` (pnp08), commissioned for fork 12(b) — the highest-stakes single computation
since the boundedness counterexample; the architect's discharge of `IsFullMonomialization` + the
exponent hooks is GATED on this verdict. Same discipline: Aoyagi 2023 **page images** p.14–22 + exact
integer algebra (the Lean engine was **not** read); one fresh decorrelated Codex consult
(`codex/nonmono-2232-{prompt,answer}.md`, hypothesis withheld). Instrument: `battery/nonmono-2232-sim.py`
— a page-faithful RAW-`T` simulator, VALIDATED on the three known atlases `(2,2,2)`,`(3,3,4)`,`(2,2,2,2)`
(t̃=0 profile-set, min, AND every t̃>0 divisor exponent match) before being trusted at `(2,2,3,2)`.
Register key as in the earlier certs.*

**Instance.** `M=(2,2,3,2)`, `L=3`, the **minimal non-monotone-width** case (`M^{(3)}=3 > M^{(2)}=2`,
a width increase in a live interior head). `minAdm(2,2,3,2)=3` (`λ_core=3/2`). The two questions:
(i) does the p.20 **raw-width** Case-2 head-reset `t^{(i)}:=M^{(i+1)}` reach a leaf with a
non-weakly-decreasing profile? (ii) does every leaf carry ONLY `t̃=0` divisors? KILL: a leaf divisor
`∉ Adm(2,2,3,2)`.

**Page-pin (load-bearing, re-verified p.20).** The Case-2 head-reset is the **raw** width
`t^{(i)}_{S,J+1}=M^{(i+1)}` (superscript-parenthesised — distinct from the running-min `M(S)` used in
the same line's exponent `(M(S)-J)(M^{(S+1)}-J)`). This is the "p.20-faithful raw-width reset" of fork 12(b).

**Two-way decorrelated agreement.** My exact simulator and Codex's independent chart-tree replay agree
to the number on all sharp facts below.

---

## Verdict (i) — YES: a non-weakly-decreasing `t̃=0` profile reaches a leaf. **KILL-CONDITION HIT.**

**Computation.** Run the construction to termination; inspect every leaf divisor's raw `T`, `t̃`, and
accumulated exponent (`nonmono-2232-sim.py`; Codex replay).

**Exact result.** `[CERT]` The raw-width head-reset produces, at node `(S,J)=(3,0)` (Case 2, head
`(M^{(2)},M^{(3)})=(2,3)`), the leaf divisor
> **`T=(2,3,0)`, `t̃=0`, accumulated `M=4`** — **non-weakly-decreasing** (`2<3`), and **`∉ Adm(2,2,3,2)`**
> (violates weak-decrease AND the block bound `t^{(2)}≤min(t^{(1)},M^{(3)})=min(2,3)=2`).

It reaches the leaf at `t̃=0` — the **sharp** case (it enters the LCT candidate set). A second
non-weakly-decreasing divisor `(2,3,1)` [`t̃=1`, `M=1`] is also emitted (positive-`t̃`).

**Root cause (the mechanism).** `[CERT]` `(2,3,0)` is the admissible **`(2,2,0)` stratum, MIS-LABELLED**
by the raw-width reset:
- its accumulated exponent `M=4` equals `Mval(2,2,0)=4` (the Case-2 exponent `(M(S)-J)(M^{(S+1)}-J)`
  uses the running-min `M(S)`, so the exponent is **correct**);
- only the label's `t^{(2)}` is wrong: the reset sets `t^{(2)}:=M^{(3)}=3`, whereas the running-min /
  Adm block-bound is `M(3)=min(M^{(1)},M^{(2)},M^{(3)})=2`. So the divisor is really `(2,2,0)`.
- **Internal inconsistency of the raw reading:** the LABEL uses raw `M^{(i+1)}` while the EXPONENT uses
  running-min `M(S)`. Consequently the p.22 terminal `Mval` formula on the raw label gives `6`, but the
  accumulated exponent is `4` (`Mval(2,3,0)=(2-2)(2-2)+(2-3)(3-3)+(3-0)(2-0)=6 ≠ 4`). For every
  *admissible* profile the two agree (verified); they diverge **only** on the mislabelled non-monotone one.

`[CERT]` Total-comparability is **NOT** violated: `(2,3,0)` never coexists with an incomparable divisor
in a single leaf (checked within every leaf); the anomalous `(2,3,0)` and e.g. `(1,1,1)` live in
different chart branches.

**→ (i): YES — the raw-width head-reset reaches a `t̃=0` leaf with a non-weakly-decreasing profile
`(2,3,0) ∉ Adm`. It is a MIS-LABEL of the `(2,2,0)` stratum (correct exponent 4; corrupt label from
`t^{(2)}:=M^{(3)}=3` instead of the running-min `2`). The corrected per-node **weak-decrease** invariant
and **leaf-Adm** are BOTH FALSE on the raw `T` at non-monotone widths.**

---

## Verdict (ii) — NO: leaves carry `t̃>0` divisors (IsFullMonomialization's `∀k` is stronger than the paper)

**Exact result.** `[CERT]` Every one of the 5 leaves at `(2,2,3,2)` carries `t̃>0` divisors — e.g.
`(1,1,1)`[`t̃=1`,`M=1`], `(2,1,1)`[`t̃=1`,`M=2`], `(2,3,1)`[`t̃=1`,`M=1`]. (Same phenomenon on all
validated instances: `(3,3,4)` leaves carry `(2,2)`,`(3,1)`,`(3,2)`; `(2,2,2,2)` leaves carry
`(1,1,1)`,`(2,1,1)`,`(2,2,1)`.) The paper's read-off (p.22) sums **only** `t̃=0` divisors.

**→ (ii): NO — leaves do NOT carry only `t̃=0` divisors. A predicate `IsFullMonomialization :=
∀ leaf divisor k, t̃_k=0` is FALSE. The correct meaning is "the leaf ideal is monomial" (`⟨diag(b)⟩`,
each `b_i` a monomial — true regardless of `t̃`); the read-off / exponent-hook MUST restrict the min to
`t̃=0` divisors, as the paper does.**

---

## No-undershoot cross-check — SAFE (value), but the Adm-based PROOF is broken

`[CERT]` min over `t̃=0` leaf divisors of the accumulated exponent = **3 = minAdm(2,2,3,2)**, achieved
by `(1,1,0)` [`M=3`]. The mislabelled `(2,3,0)` has accumulated `M=4 ≥ 3`. **No numerical undershoot**
(either the accumulated exponent `4` or the p.22-formula value `6` for `(2,3,0)` is `≥ minAdm`). Codex's
independent enumeration agrees: min `= 3`, achieved by `(1,1,0)`; admissible-reference min independently
`= 3`.

`[CERT]` BUT the exponent-hook no-undershoot **proof strategy** named in fork 12(a) — *"`t̃=0 ⟹ divProfile
∈ Adm ⟹ Mval ≥ minAdm`"* — **FAILS** at non-monotone widths: `(2,3,0)` is a `t̃=0` leaf divisor `∉ Adm`,
so "`Mval ≥ minAdm` on `Adm`" does not cover it. The value is safe; the *argument* is not.

---

## GATE VERDICT for the build (IsFullMonomialization + exponent hooks)

`[CERT]` As currently gated — **(A)** checking `divProfile ∈ Adm` (weak-decrease) on the **raw** `T`, and
**(B)** an `IsFullMonomialization` quantifying `∀k` over ALL leaf divisors — the discharge is **UNSOUND at
non-monotone widths**. Both fork-12(b) sub-questions resolve against the current predicates:
1. a `t̃=0` leaf divisor (`(2,3,0)`) is `∉ Adm` → the weak-decrease per-node invariant and the
   `Mval≥minAdm`-on-`Adm` no-undershoot argument break;
2. leaves carry `t̃>0` divisors → an `∀k, t̃=0` reading of `IsFullMonomialization` is false.

`[SPEC → recommendation, controller/architect owns the Lean route]` Two independent fixes, each
sufficient; FIX-A is the more faithful:
- **FIX-A (transcription fix; recommended).** Cap the Case-2 head-reset at the **running-min**:
  `t^{(i)} := M(i+1) = min(M^{(1)},…,M^{(i+1)})` (equivalently, at the Adm block-bound
  `min(t^{(i-1)}, M^{(i+1)})`) — NOT the raw `M^{(i+1)}`. This relabels `(2,3,0)→(2,2,0) ∈ Adm`, makes the
  label consistent with the accumulated exponent (`Mval(2,2,0)=4=accumulated`) and the geometry
  (rank `≤` running-min), and restores the per-node weak-decrease + leaf-Adm invariants and the
  `Mval≥minAdm`-on-`Adm` no-undershoot argument. The raw `M^{(i+1)}` reading is a **page-20 transcription
  defect** (the LABEL uses the raw width while the EXPONENT already uses the running-min) — add to the
  typo ledger; it is invisible at monotone widths (where `M^{(i+1)}` IS the running-min) and bites only
  at an interior width increase (`L≥3`, `M^{k} >` an earlier running-min), minimal witness `(2,2,3,2)`.
- **FIX-B (label-agnostic predicates).** Do not read the raw `T`-label for no-undershoot: prove it via
  the **accumulated exponent = codim** (geometric), and restrict `IsFullMonomialization` /the exponent
  hook to `t̃=0` divisors (never `∀k`). Sound under either head-reset reading.

Either fix requires the exponent-hook to restrict to `t̃=0` (verdict ii). FIX-A additionally repairs the
label so the Adm-based fork-12(a) argument goes through unchanged.

---

## Codex decorrelation summary + preserved inference flags

`[OBS]` Codex (hypothesis withheld) independently: created `(2,3,0)` at `(3,0)` via Case 2 with
`M_update=4`; flagged it `∉ Adm` (both `2<3` and `t^{(2)}≤min(2,3)=2` violated); independently reported
the **same** `M_update`(4)-vs-`M_term`(6) inconsistency (and `(2,3,1)`: 1 vs 2); confirmed leaves carry
`t̃>0` divisors; and computed min `t̃=0 = 3` achieved by `(1,1,0)`, matching the admissible reference.

`[OBS] Codex "most likely wrong"` (inference flags, preserved): survival of `(2,3,0)` to a leaf uses the
unstated **divisor-persistence** convention (`(2,3,1)` is born directly on the terminal transition, so it
needs no persistence); the full leaf inventory depends on the inferred `S=1→2` **boot**; the minimum is
robust, but the transcription assigns **incompatible `M`-values** to the non-monotone Case-2 vectors
(the `4`-vs-`6` conflict — itself a symptom of the raw-width defect). My verdicts do NOT hinge on the
boot/persistence: the min `=3` and the admissible reference are boot-free; `(2,3,1)` (terminal-step birth)
alone already exhibits a non-weakly-decreasing leaf divisor without persistence; and the `t̃=0` case
`(2,3,0)` is corroborated two ways.

---

## Close (firmest / most likely to break / next)

- **Firmest:** the raw-width head-reset produces a `t̃=0` leaf divisor `(2,3,0) ∉ Adm(2,2,3,2)` — a
  mislabel of the `(2,2,0)` stratum (correct exponent 4, corrupt label from `t^{(2)}:=M^{(3)}=3`), with
  the label/exponent inconsistency (`Mval` 6 vs accumulated 4). Two independent derivations agree to the
  number. The VALUE (min `=3=minAdm`, no undershoot) is safe; the Adm-based proof and the `∀k` predicate
  are not.
- **Most likely to break (build):** shipping `IsFullMonomialization`/exponent-hooks on the raw-`T` Adm
  check or an `∀k, t̃=0` quantifier — unsound at non-monotone widths. Gate correctly holds.
- **Next:** the controller/architect picks FIX-A (running-min head-reset; typo-ledger entry) or FIX-B
  (label-agnostic, `t̃=0`-restricted). A one-line re-run of `nonmono-2232-sim.py` with the running-min
  reset would confirm the whole leaf atlas becomes `Adm`-clean (`(2,3,0)→(2,2,0)`) — the cheapest
  confirmation that FIX-A closes the gate.
