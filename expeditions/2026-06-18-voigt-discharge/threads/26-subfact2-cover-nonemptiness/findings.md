# Thread 26 — sub-fact 2 (cover-nonemptiness), the K1 crux (pen-and-paper, 2026-06-19)

**The one question.** Settle the truth-value AND proof-cost of L6.2 sub-fact 2: at the extremal
deficient cell `(i0,j0)` of `g = r − s`, does there exist a covering interval `[a,e]`
(`a ≤ i0`, `e ≥ j0`, `m(r)_{[a,e]} ≥ 1`) whose rectangle `[a,i0]×[j0,e] ⊆ supp(g)`?

## VERDICT — CLOSES ELEMENTARILY. L6.2 is BUILDABLE at 2–3 modules with NO Abeasis–Del Fra cite.

Sub-fact 2 has a **complete elementary proof** by second-difference telescoping over the
rectangle-in-support family `A`. It needs only: the inversion identity (already in Lean as
`diff_cumul`), nonnegativity of `m(s)` and of `g`, and a discrete-Green telescope. **It does NOT
need extremality of `(i0,j0)`, totally-nonnegative structure, or any lace-diagram machinery.**

This **overturns thread 24's verdict** ("sub-fact 2 is NOT elementary; logically equivalent to the
Abeasis–Del Fra rank-cover classification"). Thread 24's equivalence argument (descent ⟺ cover
classification) is correct *as a logical equivalence*, but the conclusion drawn from it — that this
forces heavy machinery — was a **non-sequitur**: the cover-classification subfact is itself
elementary via the telescope below. Thread 24's error was looking only for a *monotone selector*
`(a,e) = f(g)` (which genuinely does not exist — single-row, single-col, and maximal-rect all fail).
The proof is not a selector; it is a **non-constructive existence argument** (a positive sum forces a
positive term).

| Sub-fact | thread-24 verdict | thread-26 verdict |
|---|---|---|
| 1 (linked applicability `m(r)_{[c,b]}≥1`) | ELEMENTARY (2nd-diff collapse at extremal cell) | confirmed elementary |
| 2 (cover-nonemptiness) | NOT elementary = Abeasis–Del Fra | **ELEMENTARY** (telescope; proof below) |

## The proof (sub-fact 2), self-contained

**Conventions.** Vertices `0..n`. `g_{ij} ≥ 0` is the residual on `i ≤ j` (here `g = r − s`, both
cumulants of nonneg arrays with the same diagonal, so `g_{ii} = 0`); extend `g` by `0` for any
out-of-range index (`i < 0`, `j > n`, or `i > j`). `supp(g) = {(i,j) : i < j, g_{ij} > 0}`.

**Inversion identity (Lean: `diff_cumul`).** For `m(r) = diff(r)`, `m(s) = diff(s)`, with
`h_{a,e} := m(r)_{[a,e]} − m(s)_{[a,e]}`, linearity of the second difference gives

> `h_{a,e} = g_{a,e} − g_{a,e+1} − g_{a−1,e} + g_{a−1,e+1}`.

(Verified exact on all 610 covering pairs of `d=(1,2,2,1)`; it is `m = diff∘cumul` applied to `g`.)

**Key lemma (purely about a nonnegative triangular array).** Let `g ≥ 0` be triangular and `(I,J)`
any cell with `I < J` and `g_{I,J} > 0`. Let

> `A := { [a,e] : a ≤ I, e ≥ J, and g_{ij} > 0 for every (i,j) ∈ [a,I]×[J,e] }`.

Then

> **`Σ_{[a,e] ∈ A} ( g_{a,e} − g_{a,e+1} − g_{a−1,e} + g_{a−1,e+1} ) ≥ g_{I,J} > 0`.**   (★)

**Proof of (★).**
- *Staircase shape of `A`.* For row `i`, `z_i := min{ q ≥ J : g_{i,q} = 0 }` (well-defined with
  `g_{i,n+1}=0`). For `a ≤ I`, `q_a := min_{p∈[a,I]} z_p`, `E(a) := q_a − 1`. Then `[a,e] ∈ A` iff
  `a ≥ α` and `J ≤ e ≤ E(a)`, where `α` = least `a ≤ I` with `g_{p,J} > 0` for all `p∈[a,I]` (exists
  since `g_{I,J} > 0`; `g_{α−1,J}=0` by minimality or out-of-range convention). `q_a` is
  **nondecreasing** in `a`. [Verified as a *set equality* `A_tele = A_brute` on 539,898 instances.]
- *Inner telescope (fixed `a`, over `e∈[J,q_a−1]`):*
  `Σ_{e=J}^{q_a−1} h_{a,e} = (g_{a,J} − g_{a,q_a}) − (g_{a−1,J} − g_{a−1,q_a})`.
- *Outer telescope (over `a∈[α,I]`):* the `g_{·,J}` column telescopes to `g_{I,J} − g_{α−1,J} =
  g_{I,J}`; remainder `qterm := Σ_{a=α}^{I}(g_{a−1,q_a} − g_{a,q_a})`. So `Σ_A h = g_{I,J} + qterm`.
- *`qterm ≥ 0` by blocks.* Group `[α,I]` into maximal blocks `[u,v]` where `q_a = q` constant. Block
  contributes `Σ_{a=u}^{v}(g_{a−1,q} − g_{a,q}) = g_{u−1,q} − g_{v,q}`. At top `v`, `g_{v,q}=0`: if
  `v<I`, maximality gives `q_{v+1} > q_v = q` and `q_v = min(z_v, q_{v+1})` forces `z_v = q` so
  `g_{v,q}=0`; if `v=I`, `q_I = z_I` so `g_{I,q}=0`. Each block contributes `g_{u−1,q} ≥ 0`, hence
  `qterm ≥ 0`.

Therefore `Σ_A h ≥ g_{I,J} > 0`. ∎(★)

**From (★) to sub-fact 2.** Substitute `h_{a,e} = m(r)_{[a,e]} − m(s)_{[a,e]}`. If **every** `[a,e]∈A`
had `m(r)_{[a,e]} = 0`, then `h_{a,e} = −m(s)_{[a,e]} ≤ 0` termwise (`m(s) ≥ 0`), giving `Σ_A h ≤ 0` —
contradicting (★). So some `[a,e]∈A` has `m(r)_{[a,e]} ≥ 1`; by definition of `A` its rectangle
`[a,i0]×[j0,e] ⊆ supp(g)`. Apply with `(I,J) = (i0,j0)`. ∎

The proof is **agnostic to which cell `(I,J)`** is chosen (any `g>0` cell works). Extremality of
`(i0,j0)` is used only for sub-fact 1 (the linked `m(r)_{[c,b]}≥1`) and to make `D = [a,i0]×[j0,e]`
the move's drop rectangle with `c=i0+1, b=j0−1`.

## Verification ledger (exact integer arithmetic, no floats)

| Check | scope | result |
|---|---|---|
| Sharpening "(1) is free" (some covering `m(r)≥1` exists) | all covering pairs, 8 dim-vectors | 0 failures |
| sub-fact 2 holds (some valid `(a,e)`) | all covering pairs, 8 dim-vectors | 0 failures |
| `h = ` second-diff(`g`) identity | 610 pairs `d=(1,2,2,1)` | 0 mismatches |
| **Key lemma (★) at ALL `g>0` cells, RANDOM nonneg `g`** | 676,045 instances, n≤6 | **0 failures** |
| **Every intermediate proof step** (α, set-eq `A`, P3/P4/P5/P6) | 539,898 instances, n≤6 | all assertions pass |
| Block telescoping + `qterm = Σ g_{u−1,q}` | 285,289 instances, n≤6 | 0 bad |
| **End-to-end descent** (sf1+sf2 ⟹ box move `s ≤ r' < r`, dim preserved) | 4,851 covering pairs, 8 dim-vectors | 0 bad |

The key lemma holding for *arbitrary* nonnegative triangular `g` (not just cumulant differences) is
the strong tell that it is elementary — it cannot encode quiver-representation content.

## Lean-targetable statement (for the formaliser)

> **L6.2b-key (`sum_secondDiff_coveringRect_ge`).** Let `g` be a nonneg triangular array (out-of-range
> `=0`). Fix `I < J` with `g I J > 0`. Let `A = {(a,e) | a ≤ I ∧ J ≤ e ∧ ∀ i∈[a,I], ∀ j∈[J,e],
> 0 < g i j}`. Then `∑_{(a,e)∈A} (g a e − g a (e+1) − g (a−1) e + g (a−1)(e+1)) ≥ g I J`.

> **L6.2b (`exists_coveringInterval_mr_pos`).** `r,s` achievable (`m(r),m(s) ≥ 0`), same dim vector,
> `s ≤ r`, `g = r − s`, `(i0,j0)` any cell with `g i0 j0 > 0`: `∃ (a,e)`, `a ≤ i0 ∧ e ≥ j0 ∧
> m(r)_{[a,e]} ≥ 1 ∧ (∀ (i,j) ∈ [a,i0]×[j0,e], 0 < g i j)`. Proof: L6.2b-key + `diff_cumul` (giving
> `h = secondDiff g`), by contradiction with `m(s) ≥ 0`.

**Lean cost of L6.2b-key:** self-contained `~150–250` line `Finset.sum` telescope over `ℤ`, no new
imports beyond `Finset` order/sum lemmas. Fiddly parts: the staircase set-equality for `A` and `q_a`
monotonicity (`Fin` index juggling at the `a−1`,`e+1` boundary). The engine glue (`h = secondDiff g`
via `diff_cumul`, then the `m(s) ≥ 0` contradiction) is the light part. The key lemma is **pure
combinatorics on a nonneg triangular array, decoupled from the engine** — formalisable standalone.

## L6.2 size (revised DOWN from thread 24)

| Piece | Size | Status |
|---|---|---|
| L6.1-general (per-move degeneration) | ~1 module (heavy, mechanical) | thread-24 §4; INDEPENDENT of L6.2 |
| L6.2a move + rank-drop `1_D` + dim + `Φ` | ~1 module | exact-certified (thread 24 §2) |
| L6.2b sub-fact 1 (elementary) + **sub-fact 2 (telescope, this thread)** | ~1 module | **both elementary — designed here** |
| L6.2c `Φ`-induction to terminate | ~½ module | clean given L6.2b |

**2–3 modules, all elementary content — no scoped CITE of Thm 3.8 / Abeasis–Del Fra needed for the
poset-combinatorial move-existence.** (The geometric `O_s ⊆ Ō_r` ⟺ rank-order direction is separate,
handled by L6.1-general's degeneration; this thread resolves only the combinatorial move-existence.)

## Codex (decorrelated, xhigh) — CONVERGENT; it produced the proof

I withheld my tentative direction (I was pursuing an `EITHER` two-arm L-shaped selector — CLIMB-E* OR
CLIMB-A*, verified to cover 100% of cases but awkward to prove). Given only the sharpened
reformulation, Codex **independently produced the telescope proof** — a strictly cleaner, global route
that bypasses selection. I did NOT paste its argument; I re-derived (★) and audited every intermediate
step on >500k instances before trusting it. Codex's scratch experiments (`sf2-stdout.log`) found "no
arbitrary bad" — it stress-tested the lemma on random `g` first, matching my sweep. **No divergence.**
The decorrelated consult *was* the unblock: thread 24 and I both circled the selector framing; Codex
broke it with the summation framing.

Artefacts: `codex/sf2-{prompt,answer,stdout.log}.md`; reproducibility scripts in `scripts/`
(`verify_codex.py` = key-lemma sweep, `audit_telescope.py` = full intermediate-step audit,
`endtoend.py` = descent-move composition).

## Firmest / most-likely-to-break / next step

- **Firmest:** key lemma (★) + full proof — verified at *step* level on 539,898 instances, as a
  standalone inequality on 676,045 random `g`, and end-to-end descent on 4,851 pairs.
- **Most likely to break:** a Lean *convention* mismatch in the out-of-range `g = 0` extension or the
  `Fin (n+1)` boundary indexing of the second difference (`a−1`,`e+1`). Math robust; transcription is
  where a slip could hide. Caveat for the formaliser: pin the boundary convention to `diff_cumul`.
- **Next:** hand L6.2b-key to the formaliser as a standalone `Finset.sum` telescope over `ℤ`,
  decoupled from the engine; the engine glue is the light part.
