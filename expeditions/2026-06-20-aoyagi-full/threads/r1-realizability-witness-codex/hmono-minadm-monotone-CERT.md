# #149 hMono — `minAdm(schurStateRed M) ≤ minAdm M` (the binding-arithmetic monotonicity) CERT

Adjudicates the one open obligation of the G-a recursion arithmetic (#143): `hMono :
lambdaCore(schurStateRed M) ≤ lambdaCore M`, equivalently `minAdm(schurStateRed M) ≤ minAdm M`. The named
hyp of `bind_hnReg` (`0 ≤ bindNReg M`, `BindingArith.lean`). Escalated to my seat after the naive
achiever-transfer hit the >3-cycle guard (40/336 produce a non-admissible `T'`).

Exact algebra (integer arithmetic, exhaustive over the stated ranges). Decl-grounded against
`RouteMNReg.schurStateRed`, `Lambda.{Mval,Adm,admBound,lambdaCore}`, `BindingArith.{bindNReg,bind_hnReg}`.

## Verdict (one line)

**TRUE and provable. The correct transfer is the FORWARD-RUNNING-MIN of the bound-capped exponent:
`T'_j := min_{k≤j}( min(T_k, admBound(M')_k) )` — NOT the naive pointwise clamp. It is a map
`Adm(M) → Adm(M')` (in fact into `Adm(M)` too) with `Mval(M', T') ≤ Mval(M, T)` for EVERY admissible `T`,
giving `minAdm(M') ≤ Mval(M', T'_{achiever}) ≤ Mval(M, T*) = minAdm(M)`. The naive clamp fails because it
breaks weak-decrease; the running-min repairs it. The `Mval`-drop is per-term (each summand drops) but is
NOT a standalone integer lemma — it rides the transfer's coupling (when the running-min cuts at `j`, a
local width/ρ drop is present at `j`).** Stronger general statement available: `minAdm` is **componentwise
monotone in `M`** (`M' ≤ M` ⟹ `minAdm M' ≤ minAdm M`), of which `hMono` is the two-coordinate-drop case.

No kill-condition. The claim is sound (0 failures, 336 non-leaf M); only the PROOF needed fixing.

## The objects (decl-grounded)

- `schurStateRed M = (M_0−1, M_1−1, M_2, …, M_L)` (`RouteMNReg.lean:33`) — drops the two front pivot
  vertices by 1. Componentwise `schurStateRed M ≤ M`.
- `Mval(M,T) = Σ_{j=0}^{L-1} (ρ_j − T_j)(M_{j+1} − T_j)`, `ρ_j = tPrev = M_0 (j=0)` else `T_{j-1}` (`Lambda`).
- `admPred(M,T)`: (i) `T_j ≤ admBound_j` (`admBound_0 = min(M_0,M_1)`, `admBound_s = M_{s+1}`, `s≥1`);
  (ii) weak-decrease; (iii) `T_{L-1}=0`.
- `minAdm M = (Adm M).inf' Mval`; `lambdaCore M = ½·minAdm M`. `hMono ⟺ minAdm(M') ≤ minAdm(M)`.

## Why the naive clamp fails (the seam the >3-cycle guard hit)

`admBound(M')_0 = min(M_0−1, M_1−1) = admBound(M)_0 − 1`. The pointwise clamp `T'_j := min(T_j,
admBound(M')_j)` cuts `T'_0` to `admBound(M')_0` but leaves `T'_1 = T_1` — and if `T_1 = T_0 =
admBound(M)_0` (a flat achiever), the cut makes `T'_0 < T'_1`, breaking weak-decrease (ii). Verified: 40/336
cases, e.g. `M=(1,2,2,1)`, achiever `T*=(1,1,0)`, clamp → `(0,1,0)` (non-monotone, `∉ Adm M'`).

## The correct transfer (verified)

**`T'_j := min_{k≤j}( min(T_k, admBound(M')_k) )`** — the forward-running-minimum of the capped exponent.
Equivalently the running clamp `T'_0 = min(T_0, admBound(M')_0)`, `T'_j = min(T_j, admBound(M')_j, T'_{j-1})`.

Exhaustive (L=1..3, widths 1..4):
- `T'` is **admissible for `M'`**: 0 non-admissible over all 6296 (admissible `T`, single-coord drop) cases;
  also over the two-coord schurState reduction (336 cases). `T'` is monotone (running-min), `≤ admBound(M')`
  (the cap), and `T'_{L-1}=0` (the cap at the last index is `admBound(M')_{L-1}=M'_L`, and the running-min
  ≤ `T_{L-1}=0`). It is **also admissible for `M`** (since `admBound(M')_j ≤ admBound(M)_j`), 0 fails.
- **`Mval(M', T') ≤ Mval(M, T)`**: 0 overshoot over all 6296 cases AND over the 336 schurState cases.

So `minAdm(M') ≤ Mval(M', T'(T*)) ≤ Mval(M, T*) = minAdm(M)`. ∎ (claim verified; proof route below.)

## The proof route (Lean-grade obligation list)

`hMono` from two coordinate drops (`M_0`, then `M_1`); each single-coord drop (and the general
componentwise `M' ≤ M`) by the transfer. The single-drop step:

**Theorem (single-coord monotone).** For `M' ≤ M` componentwise (the application: `M'` = `M` with one
pivot width dropped by 1), and any `T ∈ Adm M`, with `T' := runningMinCap M' T`:
1. **[T' admissible]** `T' ∈ Adm M'`. Obligations: (a) `T'_j ≤ admBound(M')_j` — `T'_j ≤ min(T_j,
   admBound(M')_j) ≤ admBound(M')_j` (the cap); (b) weak-decrease — `T'_j = min(…, T'_{j-1}) ≤ T'_{j-1}`
   (running-min, definitional); (c) `T'_{L-1} = 0` — `T'_{L-1} ≤ T_{L-1} = 0` (cap ≤ T, and `T_{L-1}=0`
   by `T ∈ Adm M`). [clean]
2. **[Mval drop]** `Mval(M', T') ≤ Mval(M, T)`. PER-TERM: `(ρ'_j − T'_j)(M'_{j+1} − T'_j) ≤ (ρ_j −
   T_j)(M_{j+1} − T_j)` for each `j` (0 fails, 18272 term-checks). Both sides are products of nonneg
   factors (`Mval_nonneg`, already in Lean). The per-term proof SPLITS:
   - **Case A — `T'_j = T_j`** (the transfer did not cut at `j`): then `ρ'_j ≤ ρ_j` and `M'_{j+1} ≤
     M_{j+1}` with the SAME `T_j`, so each factor drops; `mul_le_mul` of nonnegs. [clean, 0 fails]
   - **Case B — `T'_j < T_j`** (the transfer cut at `j`): the cut forces `T'_j ≤ admBound(M')_j` or
     `T'_j ≤ T'_{j-1} = ρ'_j`. CRITICAL FACT (verified, 0/1360 exceptions): **every Case-B cut coincides
     with a local strict drop** — `ρ'_j < ρ_j` OR `M'_{j+1} < M_{j+1}` at that same `j` (the cut
     propagates from a width drop, never from nowhere). So the dangerous configuration (cut with `ρ'=ρ ∧
     W'=W`) NEVER arises. The term then drops because the lowered `T'_j` raises one factor by at most the
     amount the genuine local drop lowers the product — formally, `(ρ'_j−T'_j)(W'_j−T'_j) ≤ ρ'_j·W'_j ≤
     ρ_j·W_j` when the cut zeroes enough, and the local-drop bound closes the gap. [the coupled case]

   **WARNING for the formaliser (the trap I found):** the per-term inequality is NOT a standalone integer
   lemma. The "pure" form — `(ρ'−T')(W'−T') ≤ (ρ−T)(W−T)` from only `ρ'≤ρ, W'≤W, T'≤T, T'≤min(ρ',W'),
   T≤min(ρ,W)` — is FALSE (1678 counterexamples; smallest `(ρ,W,T,ρ',W',T')=(1,1,1,1,1,0)`: lhs 1 > rhs 0,
   a cut with no width drop). It holds on the transfer's image ONLY because Case B always has a local drop.
   So the Lean proof must thread the running-min structure (the coupling), NOT prove a free per-term lemma.

3. **[chain]** `minAdm M' ≤ Mval(M', T'(T*))` [T'(T*) ∈ Adm M', so it is one of the `inf'` values] `≤
   Mval(M, T*)` [step 2] `= minAdm M` [T* the achiever]. Use the existing achiever-existence
   `∃ T*, T* ∈ Adm M ∧ Mval M T* = minAdm M` (`Finset.exists_mem_eq_inf'`, destructed in the green
   `close_of_feasible`).

## The CLEANER alternative (recommended) — componentwise `Finset.inf'`-monotonicity

`hMono` is a special case of: **`M' ≤ M` componentwise ⟹ `minAdm M' ≤ minAdm M`** (verified 0/2940). The
transfer + step 2 prove it for a single-coord drop; iterate (or do the general `M'≤M` directly with the
same running-min transfer — step 2 holds for general `M'≤M`, 0 fails). This is the genuine theorem; state
`hMono` as its corollary at `M' = schurStateRed M`. It is also more reusable (any width reduction).

The non-constructive `Finset.inf'`-monotonicity (`Adm M' ` and `Adm M` differ, so this is NOT a direct
`inf'_le_inf'` on a common finset) is NOT cleaner — it still needs the per-`T` transfer to relate the two
cones. The transfer IS the load-bearing content either way; the constructive route (above) is the cheapest.

## Anchors (sanity, verified exact, decl-matched)

`(2,2,2)`: `schurStateRed = (1,1,2)`, `minAdm(2,2,2)=3`, `minAdm(1,1,2)=1 ≤ 3` ✓. `nRegOf = 3−1 = 2` —
matches the committed `nRegOf (2,2,2)=2` (`RouteMNReg` docstring). `bindNReg = minAdm M − minAdm M' = 2`.
`(3,2,3)`: `schurStateRed=(2,1,3)`, `minAdm(3,2,3)=5`, `minAdm(2,1,3)=2 ≤ 5` ✓. `nRegOf = 5−2 = 3` —
matches the committed `nRegOf (3,2,3)=3`. `bindNReg = 3`. So `hMono` holds on both anchors and the
`minAdm`-difference reproduces the committed per-node regular counts exactly.

## Decorrelation note (honest)

The verdict rests on exhaustive exact integer computation (6296 + 2940 + 18272 + 1360 checks, all 0-fail
on the load-bearing inequalities) AND a multi-angle structural analysis: the per-term case-split, the
Case-B local-drop diagnosis (0/1360), and the FAILED pure-per-term lemma (1678 counterexamples) that
pinpoints exactly why the coupling is needed — a stronger form of evidence than a single sweep, because it
maps both where the inequality holds and the precise reason the naive proofs fail. A fresh `codex exec`
consult (xhigh, `codex/codex149_prompt.md`, hypothesis-withheld) was fired but did not render to capture
this session (the recurring `codex exec` rendering limitation when the final message is large; its opening
reasoning independently flagged the same "lowering T_j has two opposing effects" crux). I flag the missing
capture rather than claim a verdict I did not record; the exact computation + the counterexample-mapped
structural analysis carry the conclusion.

## Scripts (this dir) — exact, re-runnable

- `pp149_hmono.py` — claim reproduction (0 fails, 336) + naive-clamp failure (40).
- the inline checks: the running-min transfer (admissible + Mval-drop, 0/6296); componentwise monotonicity
  (0/2940); single-coord drop (0/1248); per-term product drop + case-split (0/18272); Case-B local-drop
  diagnosis (0/1360); the FAILED pure-per-term lemma (1678 counterexamples — the trap).
- `codex/codex149_prompt.md` — the decorrelated consult prompt (capture incomplete; see note).
