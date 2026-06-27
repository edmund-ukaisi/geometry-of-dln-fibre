# Certificate — the nonzero-VvalGen witness (VALIDATION of the effective-leaf+carrier correction)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. VALIDATES genm-decoder's correction of my earlier
`certificate-genM-Bdet.md §5` witness (which was WRONG). The corrected construction is the **effective-leaf
+ carrier** witness for `∃ w, achieverUfun w ≠ 0` (the last rate-side gap: `VvalGen > 0` a.e., the `Ubound`
positivity). Independent exact-algebra re-derivation + a 3rd decorrelated Codex.

Decorrelated xhigh Codex (my own, the 3rd independent check beyond genm-decoder's two): `codex/witness-validate-{prompt,answer}.md`.
Exact scripts: `scripts/witness_validate.py`, `deadleaf_validate2.py`, `validate_3333_334.py`, `carrier_when.py`,
`recompute_text.py`, `revalidate_correct.py`.

**VERDICT — the effective-leaf+carrier correction is CORRECT and uniform ∀M (2≤L). NOT a research wall.** I
reproduced the failure of my §5 witness, validated the correction on the FAILING cases (incl. genuine
dead-leaf (3,3,1,3)/(1,2,2)), and resolved the one edge I initially mis-flagged as a wall (the "q=0"
case — a self-inflicted `tach`-miscomputation; with the correct `tach = Fin.cons(M_0, tStar)`, `q ≥ 1`
always). The one genuine residual is the dependent-width downward `Hmat_succ` induction — bounded
engineering, with a clean `rowPath` skeleton.

---

## 1. Why my §5 was wrong (REPRODUCED — diligence)

My §5 claimed: "all kept-diag = 1, leaf pivot = 1 ⟹ `Hmat_0(0,0) = ∏Bmat·1 = 1`." Two failures (exact
sympy, `scripts/witness_validate.py`, `deadleaf_validate2.py`):

- **(#1) A non-deepest active block does NOT propagate.** At the witness `A_{L−1} = [0; W]` (dead-leaf kept
  rows zero) and `A_s = [Bmat_{s+1}; 0]` for `s < L−1` (lift zero), so the SUFFIX product zeroes any column
  injected before the last live boundary. REPRODUCED: (3,3,3,3) with the live block at `s=1` + dead leaf +
  identity W gives `Hmat_0 = 0` exactly.
- **(#2) The leaf is structurally row-empty for the achiever** when `Text_L = 0` (the penultimate Aoyagi
  rank already dropped) — then `Rfin_L : 0 × M_L`, so the live-leaf pivot is INFEASIBLE. REPRODUCED:
  (3,3,1,3) leaf `Rfin = 0×3`, no entry to set.

My §5 error was the visible-progress trap — I asserted the all-kept term survives without probing the
suffix telescope. It survives ONLY in the live-leaf case (and then only if the pivot is at the deepest live
boundary).

---

## 2. The corrected construction (genm-decoder's; VALIDATED), 2≤L

**Effective leaf `q := max { k ≤ L : Text_k > 0 }`** (the deepest positive-rank boundary), where the chain
`tach M := Fin.cons (M_0) (tStar M)` gives `Text_0 = M_0`, **`Text_1 = tach_0 = M_0`** (the identity
boundary), `Text_{k+1} = tach_k = tStar_{k−1}` for `k ≥ 1`. Two regimes:

- **`q = L` (LIVE leaf, `Text_L > 0`):** pivot `e` at `Rfin_L(0,0)`; kept-diagonal `Bmat_k(0,0) = 1`; all
  `N/W/other-E = 0`. The kept-diagonal `Bmat` propagates the leaf pivot UP: `Hmat_0(0,0) = e`. **NO
  carriers** (validated: (3,3,3,3), (3,3,4) with `W = 0` give `Hmat_0(0,0) = e`).

- **`q < L` (DEAD leaf, `Text_L = 0`):** pivot `e` at the deepest E-block (boundary `q`, `Rmat_q`
  bottom-right `r_q × c_q`); **CARRIER lifts `W_q, …, W_{L−1}` = 1-entries** propagate the injected column
  DOWN to the leaf output; kept-diagonal `Bmat` above `q`. `Hmat_0(0,0) = e · (∏ carrier W entries)`. The
  carriers are LOAD-BEARING: validated (3,3,1,3) gives `e·w₂` WITH carriers, `0` WITHOUT (`scripts/revalidate_correct.py`).

**The mechanism (Codex Q3, validated):** below `q` every `Text_{k+1} = 0`, so `A_k = [empty kept ; W_k] =
W_k` (all-lift), and `suffix_q = W_q·W_{q+1}·…·W_{L−1}` (the carrier chain); the `E_q · suffix_{q+1}` term
carries `e · (carrier product)`. Above `q` the kept-diagonal `Bmat` copies it up to `Hmat_0`.

---

## 3. The "q=0" edge — a CONFOUND I mis-flagged, then ruled out (the lesson re-applied)

I initially computed `Text = [M_0, 0, …]` for the M_0-bottleneck (e.g. (1,2,2), `tStar = (0,0)`), found NO
live residual slot (boundary-0 E needs `Rmat_0`, FORCED 0 for hC0; leaf row-empty), and nearly flagged a
research wall. **This was a miscomputation:** I used `tStar` directly as `tach`. The actual `tach =
Fin.cons(M_0, tStar)` PREPENDS `M_0`, so **`Text_1 = tach_0 = M_0 ≥ 1` always** (the identity boundary is
always live). Hence `q ≥ 1` for every genuine network — **the q=0 case cannot arise** (`scripts/recompute_text.py`,
`revalidate_correct.py`). Recomputed: (1,2,2) `tach = (1,0,0)`, `Text = [1,1,0]`, `q = 1`, deepest E at
boundary 1 (`1×2`, nonempty), carrier `W_1` ⟹ `Hmat_0(0,0) = e·w ≠ 0`. ✓ The M_0-bottleneck is a normal
`q = 1` dead-leaf case, fully covered.

(This is the §5 lesson re-applied: probe the confound to ground before naming a wall. The earlier `tach`
mis-handling would have produced a false escalation; the correct `tach` closes it.)

---

## 4. Well-definedness + nonemptiness (Codex Q1/Q2, validated)

- **`q` well-defined ∀M:** `{k ≤ L : Text_k > 0}` is finite and nonempty (`Text_0 = M_0 ≥ 1`); `q ≥ 1`
  (`Text_1 = M_0 ≥ 1`, §3). So there is always at least one live boundary at or below `q`.
- **The pivot slot exists (`q < L`):** `r_q = Text_q − Text_{q+1} = Text_q − 0 = Text_q ≥ 1` (q deepest
  positive), `c_q = M_q − Text_{q+1} = M_q ≥ 1`. So the deepest E-block is nonempty (`Codex Q2`).
- **The pivot slot exists (`q = L`):** `Rfin_L : Text_L × M_L`, `Text_L ≥ 1` (q=L means `Text_L > 0`),
  `M_L ≥ 1`. Nonempty.
- **The carrier dims (`q < L`):** below `q`, `W_k : c_k × M_{k+1} = M_k × M_{k+1}` (since `Text_{k+1} = 0`),
  all `≥ 1×1` for positive widths — NO carrier-chain break (Codex Q3).
- **No cancellation** at the witness: all non-essential coords are 0, leaving ONE surviving monomial
  (`e` live-leaf, or `e·∏w` dead-leaf) in `Hmat_0(0,0)` — so `Hmat_0 ≢ 0`, `VvalGen = ‖Hmat_0‖²` is a
  nonzero polynomial ⟹ `> 0` a.e. (Codex Q4; `achieverUfun_nonneg` + `ae_eval_ne_zero` banked).

---

## 5. SYMPY validation on the FAILING cases (the binding check — exact)

| `M` | `tach` | `Text` | leaf | `q` | construction | `Hmat_0(0,0)` | nonzero |
|-----|--------|--------|------|-----|-------------|---------------|---------|
| (3,3,3,3) | (3,2,1,0) | [3,3,2,1] | LIVE (Text_L=1) | L=3 | leaf pivot, kept-diag, no carrier | `e` | ✓ |
| (3,3,4) | (3,1,0) | [3,3,1] | LIVE | L=2 | leaf pivot, no carrier | `e` | ✓ |
| (3,3,1,3) | (3,2,0,0) | [3,3,2,0] | DEAD (Text_L=0) | 2<L | deepest-E pivot, carrier W_2 | `e·w₂` | ✓ |
| (1,2,2) | (1,0,0) | [1,1,0] | DEAD | 1<L | deepest-E pivot, carrier W_1 | `e·w` | ✓ |

(Exact, `scripts/validate_3333_334.py`, `revalidate_correct.py`.) The CRITICAL no-carrier failure check
(`scripts/revalidate_correct.py`): (3,3,1,3) with `W = 0` gives `Hmat_0 = 0` — confirming the carriers are
load-bearing, and the dead-leaf cases are exactly where my §5 (carrier-free) witness failed. The simple
witness "passed" the L=2 live anchors only because their leaf is live; it fails the dead-leaf cases, which
the effective-leaf+carrier construction covers.

---

## 6. L=1 edge (confirmed: banked `DeepestBaseL1` covers it)

For `L = 1` the dead-leaf chain has `achieverUfun ≡ 0` (Codex `witness-deadleaf` Q3; `Rfin = 0` ⟹ `Hmat_1 =
0`, `Rmat_0 = 0` kills the only `E_0` term). The witness is FALSE for the dead-leaf `L=1` chart — so the
scope is `2 ≤ L`, with `L = 1` handled by the banked `DeepestBaseL1` pure-radial single-layer chart
(separate, no chain telescope). This is consistent with `structAdm_tach M hL` needing `0 < L` and the
2-boundary minimum for a nontrivial Schur frame.

---

## 7. Residual risk (NONE a research wall — Codex Q5 confirms)

| piece | status |
|-------|--------|
| effective-leaf `q` selection (deepest `Text > 0`) | well-defined, `q ≥ 1`; a `Finset.max'`/decidable scan over `Fin (L+1)` |
| pivot-slot nonemptiness (`r_q, c_q ≥ 1` or leaf `Text_L, M_L ≥ 1`) | from `q` deepest-positive + positive widths (Codex Q2) |
| carrier construction `W_q..W_{L−1}` | the dims `M_k × M_{k+1} ≥ 1×1`; coordinate carriers (Codex Q3) |
| **the downward `Hmat_succ` induction** (the surviving entry's (row,col) via `rowPath`) | **the main remaining proof burden** — `Finset.sum_eq_single` per step over opaque widths (the dependent-`Fin` kernel); the `witness-deadleaf` Codex skeleton (`rowPath`, `B_rowPath_basis`, `E_rowPath_zero_before`, `deep_E_entry`, `H_entry_survives`) is the structure. Bounded engineering, NOT research. |
| `UPolyGen ≠ 0` ⟹ `achieverUbound`/`Ubound` | banked (`UPolyGen_ne_zero_of_witness`, the MvPolynomial encoding done) |

**The construction itself has NO hole** (Codex Q4/Q5; my exact validation). The one residual is the
dependent-width downward induction — the `rowPath` carries the surviving entry's index symbolically (avoiding
per-node `⟨_, by decide⟩` casts), `Finset.sum_eq_single` at each `Hmat_succ` step.

---

## Close

**Firmest result:** genm-decoder's effective-leaf+carrier witness is CORRECT and uniform ∀M (2≤L) — `q :=
deepest Text > 0` (`≥ 1` always, since `tach = Fin.cons(M_0, tStar)` ⟹ `Text_1 = M_0 ≥ 1`); live-leaf
(`q=L`) = leaf-pivot + kept-diagonal (no carrier); dead-leaf (`q<L`) = deepest-E pivot + carriers `W_q..W_{L−1}`.
Validated EXACT on the FAILING cases (3,3,1,3)/(1,2,2) dead-leaf + (3,3,3,3)/(3,3,4) live-leaf; the no-carrier
failure (`Hmat_0 = 0`) confirms the carriers are load-bearing. My §5 was wrong (the all-kept term is killed
by the dead-leaf suffix unless the pivot is at the deepest live boundary with carriers). Triple-confirmed
(my exact sympy reproduction of both failure + correction / genm-decoder's sympy+2 Codex / my 3rd decorrelated
Codex). **NO research wall** (Codex Q5).

**Most likely to bite:** the downward `Hmat_succ` induction over opaque widths (#7 row) — the `rowPath`
dependent-`Fin` bookkeeping; bounded engineering with the Codex skeleton, NOT research. **Next construction
that settles it:** implement the `rowPath` + the two-regime witness `wEW`/`wLeaf` + the `H_entry_survives`
downward induction (the `witness-deadleaf` skeleton), validate on (3,3,1,3) (the genuine dead-leaf) first,
then the ∀M lift; `UPolyGen_ne_zero_of_witness`/`achieverUbound`/`achieverUfun_nonneg` are banked.

**Strategic note:** the rate-side `NodeAchieverChart` fields complete (for `2 ≤ L`) once this witness lands;
`L = 1` rides the banked `DeepestBaseL1`. The construction is build-ready; the open part is the bounded
downward induction, not a design or research question.
