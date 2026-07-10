# Case-2 fidelity certificate — prefix-min vs actual-width, and why Case-2 never binds

**Seat:** pen-and-paper (adjudicate a truth-value + fidelity card). **Charge:** #107. **Date:** 2026-07-10.
**NO Lean.** **Decorrelated:** `local-codex-consult` (xhigh), my conclusion withheld (`case2-codex-*.md`).
**Source, image-pinned:** Aoyagi 2023 `theory/aoyagi-2023-reproduction/pages/p20.png` (Case-2 step),
`p22.png` (terminal exponent + admissibility). **Exact-algebra:** `case2_verify.py`, `case2_verify2.py`.

---

## HEADLINE VERDICT (a reversal of the naive framing — flagged)

> **Case-2 NEVER binds** the finiteness threshold: `minAdm(M) ≤ M(S)·M^{(S+1)} ≤ M^{(S)}·M^{(S+1)}` for
> every width vector and every `S` (**PROVED**, §2b+c, via an admissible prefix-min-pivot branch; cross-checked
> `0` counterexamples to widths ≤ 6, `L ≤ 4`). So BOTH the printed (actual-width) and prefix-min forms of the
> Case-2 exponent are `≥ minAdm`. Therefore the exact Case-2 exponent is
> **NOT load-bearing** for `(□)`: a COARSE bound suffices, and the repo's `minAdm` accounting already
> subsumes Case-2 (since `minAdm ≤` every Case-2 branch's `Mval` by construction).

**This contradicts the naive charge framing** ("the prefix-min form is the corrected/honest one; the
printed form would be wrong"). The exact algebra says: neither is "wrong" for finiteness — both are
`≥ minAdm`. What IS wrong (and is the prior expedition's rabbit hole, `lessons.md` 2026-06-20) is a
*specific buggy* prefix-min "correction": substituting prefix-min into the `Mval` COLUMN widths while
keeping the actual-width pivot vector, which produces **negative** exponents (§4). So the operative
guidance is: **use the printed reading (or don't reproduce Case-2 machinery at all); do NOT build the
prefix-min column-correction.** This matches `lessons.md` exactly, now proven with exact algebra.

---

## 1. The two source formulas (image-pinned, 1-indexed `M^{(1)},…,M^{(L+1)}`)

`M(S) := min{M^{(1)},…,M^{(S)}}` (the **prefix minimum**); `M^{(S)}` = the **actual** width of layer `S`.

**Case-2 step at stage `S`, chart index `J` (p.20, verbatim):**

    pivot vector    t^{(i)}_{S,J+1} = M^{(i+1)}   (i = 1,…,S−1),    t^{(i)} = J   (i = S,…,L)   [ACTUAL widths]
    divisor exp     M'_{S,J+1} = (M(S) − J)(M^{(S+1)} − J)                                        [PREFIX-MIN rows]

**Terminal accumulated exponent / RLCT candidate (p.22, verbatim):**

    rlct_core = ½·min{ M_{s,k} : t̃_{s,k}=0 },
    M_{s,k} = (M^{(1)}−t^{(1)})(M^{(2)}−t^{(1)}) + Σ_{j=2}^{L} (t^{(j−1)}−t^{(j)})(M^{(j+1)}−t^{(j)}),
    admissibility (reindexed):  H_j ≤ H_{j−1},  H_j ≤ M^{(S_{j+1})},  H_ℓ = 0.

**The M(S)-vs-M^{(S)} collapse (the pitfall).** The single-step divisor exponent (p.20) uses the
**prefix-min** `M(S)` for the block ROW count — geometrically correct, because by stage `S` the diag(b)
reduction has compressed the residual block to `M(S)` rows. But the terminal `Mval` (p.22) with the
printed pivot vector `t^{(i)}=M^{(i+1)}` uses the **actual** widths. Plaintext PDF extraction collapses
`M(S)` and `M^{(S)}` (`lessons.md`: "Page images are necessary when a step depends on `M^{(s)}` vs
`M(S)`"), which is the origin of the confusion.

---

## 2. Exact adjudication (all verified, `case2_verify.py` / `case2_verify2.py`)

### (a) The printed pivot vector telescopes — FACT (`0/4992` failures)

Plugging the printed Case-2 vector (`t^{(i)}=M^{(i+1)}` for `i<S`, `t^{(i)}=0` for `i≥S`, `J=0`) into the
`Mval` formula (p.22): every term for `j ≤ S−1` is `(M^{(j)}−M^{(j+1)})(M^{(j+1)}−M^{(j+1)}) = 0`, the
`j=S` term is `(M^{(S)}−0)(M^{(S+1)}−0)`, and `j>S` terms are `0`. Hence

    **Mval(printed Case-2 vector, J=0) = M^{(S)}·M^{(S+1)}**   (a two-width product of ACTUAL widths).

### (b)+(c) Neither form ever binds below `minAdm` — PROVED (clean, not just exhaustive)

**Lemma (never-binds).** For every width vector and every `S`,

    minAdm(M)  ≤  M(S)·M^{(S+1)}  ≤  M^{(S)}·M^{(S+1)}.

*Proof.* The right inequality is `M(S) ≤ M^{(S)}` (prefix-min ≤ actual). For the left, use the admissible
rank profile `t^{(i)} = M(i+1)` (prefix-min) for `i<S`, `t^{(i)}=0` for `i≥S`. It is **admissible**:
prefix-minima are non-increasing (⟹ weakly decreasing) and `M(i+1) ≤ M^{(i+1)}` (⟹ within width bound).
Its `Mval` **telescopes to `M(S)·M^{(S+1)}`**: for each `j<S` the term `(t^{(j−1)}−t^{(j)})(M^{(j+1)}−t^{(j)})`
vanishes — either the prefix-min did not drop at `j+1` (`t^{(j−1)}=t^{(j)}`) or it dropped to `M(j+1)=M^{(j+1)}`
(`M^{(j+1)}−t^{(j)}=0`) — and the surviving `j=S` term is `(M(S)−0)(M^{(S+1)}−0)`. Since `minAdm` is the min
over admissible profiles, `minAdm ≤ Mval = M(S)·M^{(S+1)}`. ∎

**Verified:** `Mval(prefix-min pivot) = M(S)·M^{(S+1)}` and the profile is admissible, `35424/35424`;
`minAdm ≤ M(S)M^{(S+1)} ≤ M^{(S)}M^{(S+1)}`, `0` violations (widths ≤ 6, `L≤4`). Both forms can EQUAL
`minAdm` (bind as an equality — e.g. prefix-min tight at `M=(1,4,4)`, `S=2`: `M(2)M^{(3)}=1·4=4=minAdm`;
printed tight at `M=(3,2,4,4)`, `S=1`: `M^{(1)}M^{(2)}=6=minAdm`), but **never go strictly below**. This is
the trusted-spine `2λ ≤ M^{(i)}M^{(j)}` de-risk — **now PROVED, not just checked.**

### (d) The discrepancy — FACT

    printed exponent − prefix-min codim  =  M^{(S)}M^{(S+1)} − M(S)M^{(S+1)}
      =  (M^{(S)} − M(S))·M^{(S+1)}  =  (n_S − μ_S)(n_{S+1} − J)|_{J=0}    [the captured pitfall formula].

`n_S = M^{(S)}` (actual), `μ_S = M(S)` (prefix-min), `n_{S+1} = M^{(S+1)}`. The printed pivot-vector `Mval`
**overcounts** the true (prefix-min) block codim by exactly this amount when `M(S) < M^{(S)}` — a HARMLESS
overcount (a larger exponent = a larger, non-binding threshold).

---

## 3. Fully-worked binding chain where the divergence BITES: `M = (2,4,4)`

`M^{(1)},M^{(2)},M^{(3)} = 2,4,4`; prefix-mins `M(1)=2`, `M(2)=2 < M^{(2)}=4` — **the divergence bites at `S=2`.**

- `minAdm(2,4,4) = 7`, at the rank-1 branch `t=(1,0)` (`(2−1)(4−1)+minAdm(1,4)=3+4=7`); the other cuts
  give `t=0 → 8`, `t=2 → 8`. **Threshold `λ = 7/2 = 3.5`.**
- **Case-2 at `S=2`** (full block drops):
  - PRINTED terminal `Mval` (pivot `t=(M^{(2)},0)=(4,0)`): `Mval = M^{(2)}M^{(3)} = 16`.
  - PREFIX-MIN single-step codim: `M(2)·M^{(3)} = 2·4 = 8`.
  - **Both `≥ minAdm = 7`** — Case-2 is non-binding; the binder is the rank-1 branch `t=(1,0)` (`Mval=7`),
    NOT a Case-2 branch.
  - Discrepancy `(M^{(2)}−M(2))(M^{(3)}−0) = (4−2)·4 = 8 = 16 − 8`.

**Conclusion for this chain:** whether one reads the Case-2 exponent as `16` (printed/actual) or `8`
(prefix-min), the finiteness threshold is unaffected — it is set by the rank-1 branch at `7/2`, and Case-2
sits strictly above. So the M(S)-vs-M^{(S)} choice is **immaterial to the threshold** here, exactly as the
never-binds theorem predicts. *(Additional bite-and-tight examples in `case2_verify2.py`: `(1,2,2)`,
`(1,3,3)` where the prefix-min form equals `minAdm` — still `≥`, still non-binding-below.)*

---

## 4. The prior expedition's ACTUAL error — the buggy "prefix-min correction" (§g, `case2_verify2.py`)

`lessons.md` (2026-06-20): *"the prefix-minimum 'fix' the prior expedition built can violate admissibility
and produce sub-2λ (even negative) values."* My CLEAN prefix-min substitutions (b)/(c) do **not** reproduce
any negative — so the bug was a *specific* mixed form. I reproduced it exactly:

> **Buggy form:** substitute prefix-min `M(j+1)` into the `Mval` COLUMN widths while keeping the printed
> ACTUAL-width pivot `t^{(i)}=M^{(i+1)}`. Then a column term `(M(j+1) − t^{(j)})` goes **negative** because
> `t^{(j)} = M^{(j+1)} > M(j+1)` when widths increase. E.g. `M=(5,2,1,1)`, `S=3`, pivot `t=(5,2,0)`:
> buggy `Mval = −1`. (`10` such negatives found, widths ≤ 5, `L≤3`.)

The failure is **mixing** an actual-width pivot with prefix-min columns — an internally inconsistent object.
Aoyagi's printed formulas are each internally consistent (actual pivot + actual columns → `M^{(S)}M^{(S+1)}`;
prefix-min rows in the single-step codim → `M(S)M^{(S+1)}`); the danger is a half-applied "correction".

---

## 5. Answer to the charge's three asks

1. **Corrected prefix-min form vs printed form + the divergence.** The single-step divisor exponent (p.20)
   is `(M(S)−J)(M^{(S+1)}−J)` — **prefix-min rows, geometrically the true block codim**; the terminal `Mval`
   via the printed pivot vector (p.22) is `M^{(S)}M^{(S+1)}` — **actual widths, an overcount** by the pitfall
   discrepancy `(n_S−μ_S)(n_{S+1}−J)`. Both are internally consistent readings; the paper uses prefix-min
   for the block rows and actual widths for the pivot bookkeeping. The **honest** geometric divisor exponent
   is the prefix-min one; the printed pivot-vector `Mval` overcounts it but stays safe.

2. **Worked binding chain (§3): `M=(2,4,4)`** — divergence bites (`M(2)=2 < M^{(2)}=4`), printed `16` vs
   prefix-min `8`, both `≥ minAdm=7`, threshold set by the rank-1 branch at `7/2`. **Neither form is "wrong"**
   for the threshold — contra the charge's framing. (What is wrong is the buggy mixed form, §4, which the
   charge should NOT be read as endorsing.)

3. **Coarse vs sharp — the de-risk.** The trusted-spine `2λ ≤ M^{(i)}M^{(j)}` (Case-2 never binds) **HOLDS
   exactly** (b),(c): both Case-2 forms are `≥ minAdm` for all chains (PROVED). Therefore **a COARSE bound
   suffices; the sharp corrected form is NOT load-bearing.** The safe coarse bound to state is the **printed**
   two-width product `M^{(S)}·M^{(S+1)} ≥ minAdm` (the cleaner form; `≥ M(S)·M^{(S+1)} ≥ minAdm`). Since the
   repo proves `(□)` via the `minAdm` recursion (`minAdmRec_eq_minAdm`, banked), **Case-2 is subsumed — no
   separate Case-2 exponent needs to be computed at all** for finiteness.

---

## 6. Recommendation for the carrier / fidelity card (Lean-friendly)

- **DO** state the Case-2 exponent as the coarse `M^{(S)}·M^{(S+1)} ≥ minAdm` (printed reading), or better,
  **subsume it**: the repo's finiteness proof goes through `minAdm` (the min over admissible branches), and
  `minAdm ≤ M^{(S)}M^{(S+1)}` is a one-line branch-instantiation. No sharp Case-2 machinery is needed for
  `(□)`.
- **DO NOT** reproduce the prefix-min column-substitution "correction" (§4) — it is internally inconsistent
  (negative exponents) and was the prior expedition's `+8.7K`-line treadmill (`lessons.md`).
- **Fidelity-card wording (drop-in):** *"Aoyagi's Case-2 divisor exponent is stated with prefix-min block
  rows `(M(S)−J)(M^{(S+1)}−J)` (p.20) and an actual-width pivot vector `t^{(i)}=M^{(i+1)}` whose terminal
  `Mval` telescopes to `M^{(S)}M^{(S+1)}` (p.22); the two differ by `(M^{(S)}−M(S))(M^{(S+1)}−J)` where the
  prefix-min `M(S)` collapses to the actual `M^{(S)}` under plaintext extraction. This is immaterial to our
  result: both forms are `≥ minAdm` (PROVED, §2b+c), so Case-2 never binds and is
  subsumed by the `minAdm` accounting. We do not reproduce the (unsound) prefix-min column-correction."*

---

## 7. Levels / scope / caveats

- **Levels separate.** This is entirely at the COMBINATORIAL exponent level (`minAdm` / `Mval`); it does not
  touch the geometry (the blow-up charts) or the `rlct = ½·codim` interface. It certifies only that the
  Case-2 branch exponents do not lower the finiteness threshold below `½minAdm`.
- **Proof status.** The never-binds lemma `minAdm ≤ M(S)M^{(S+1)} ≤ M^{(S)}M^{(S+1)}` is **PROVED** (§2b+c,
  via the admissible prefix-min-pivot branch, `Mval = M(S)M^{(S+1)}`) — a clean formaliser-ready statement,
  not merely exhaustive. The telescoping (a) and the proof are cross-checked `35424/35424` and `0/4992`.
  *(Note: the pivot for the lemma is `t^{(i)} = M(i+1)` — the prefix-min of the FIRST `i+1` widths, `p_{i+1}`.
  A first draft of this cert used a mis-indexed pivot and wrongly concluded the one-line proof failed; the
  correctly-indexed prefix-min pivot is admissible and telescopes exactly — thanks to the decorrelated Codex
  pass, §8, which supplied the clean argument.)*
- **The one thing that could complicate.** If a downstream construction ever needed the *exact* Case-2
  divisor threshold (not just `≥ minAdm`) — e.g. to compute `θ` (the top-component MULTIPLICITY, which
  counts ties at the min) — then the prefix-min-vs-actual choice WOULD matter (a tie-count is sharp). But
  `(□)` / finiteness only needs `≥ minAdm`, and `θ` is explicitly secondary (standing decision). Flagged,
  not load-bearing here.

---

## 8. Codex (decorrelated, xhigh; my conclusion withheld) — CONCUR + supplied the clean proof

`case2-codex-{prompt2,answer}.md`. Codex independently reproduced ALL of the above and, importantly,
**supplied the clean general proof** of the never-binds lemma that fixed a mis-indexed pivot in my first
draft:

- **(1)** Printed pivot telescopes to `m_S·m_{S+1}` (actual adjacent-width product) — identical to §2a.
- **(2)+(3)** "Stronger fact: for every `S`, `minAdm(M) ≤ p_S·m_{S+1} ≤ m_S·m_{S+1}`" via the admissible
  prefix-min pivot `t_i = p_{i+1}` (i<S), `0` (i≥S) — **the exact proof now in §2b+c**. It notes both can
  bind as equalities (`M=(3,2,4,4)` `S=1` printed `=6=minAdm`; `M=(1,4,4)` `S=2` prefix-min `=4=minAdm`) but
  never go below. Matches my `35424/35424` cross-check term-for-term.
- **(4)** "For proving finiteness for `c < ½minAdm`, the exact Case-2 exponent is **not load-bearing**. A
  coarse lower bound is enough… the `M^{(S)}` vs `M(S)` ambiguity matters for exact branch arithmetic and
  binding claims, but not for the finiteness inequality." — identical to my §5.3.
- **(5)** The buggy prefix-min fix creates negatives: Codex's example `M=(2,5,4,7)`, `S=3`, `t=(5,4,0)`,
  the `j=2` term `(5−4)(p_3−4)=(1)(2−4)=−2` — the same failure mode as my §4 (`case2_verify2.py`).

Full concurrence; the consult strengthened the result (exhaustive → proved).

---

## 9. Closing

- **Firmest.** Case-2 never binds: both the printed (actual, `M^{(S)}M^{(S+1)}`) and prefix-min
  (`M(S)M^{(S+1)}`) exponents are `≥ minAdm` for all chains (PROVED via the prefix-min-pivot branch). The
  finiteness threshold is `½minAdm`, set by rank-drop (Case-1) branches; Case-2 sits above. Coarse suffices;
  the repo's `minAdm` subsumes Case-2. The pitfall discrepancy `(n_S−μ_S)(n_{S+1}−J)` is a harmless overcount.
- **Reversal flagged.** The naive charge framing ("prefix-min corrected / printed wrong") does not survive
  the exact algebra: neither is wrong for finiteness. The genuinely unsound object is the *mixed* buggy
  prefix-min column-correction (negative exponents) — the prior expedition's error, which we must not rebuild.
- **Most likely to matter later.** Only `θ` (multiplicity / tie-counting) would make the sharp form
  load-bearing; `(□)` does not. Flagged for whoever takes `θ`.
- **Next.** None needed for `(□)` (Case-2 is subsumed by the `minAdm` accounting). The general never-binds
  lemma `minAdm M ≤ M(S)·M^{(S+1)} ≤ M^{(S)}·M^{(S+1)}` (∀S) is **PROVED** (§2b+c) and formaliser-ready: the
  prefix-min-pivot profile `t^{(i)}=M(i+1)` is admissible with `Mval = M(S)·M^{(S+1)}`, so `minAdm ≤` it by
  `minAdm ≤ Mval`. Sits banked-adjacent to `minAdmRec_eq_minAdm`.
