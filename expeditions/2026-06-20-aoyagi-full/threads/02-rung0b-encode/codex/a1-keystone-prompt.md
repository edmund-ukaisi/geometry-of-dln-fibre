<task>
I am formalising in Lean 4 + Mathlib (v4.29) a discrete combinatorial-optimization identity (Aoyagi
Lemma 3 for deep linear networks). I need the CLEANEST Lean proof ROUTE (architecture + key
lemmas), not Lean code. All math below is numerically verified exhaustively (0 failures, L<=4,
widths 0..4). The goal: replace ONE `sorry` with a real proof, minimizing the dependent-`Fin`
reindexing that has historically thrashed.

## The objects (exact Lean defs, transcribed faithfully)

- `M : Fin (L+1) -> Nat` is a vector of widths (L >= 1). Write `M_0, ..., M_L`.
- For `T : Fin L -> Nat`, set `tPrev j = M_0 if j=0 else T_{j-1}`, and
  `Mval M T = sum_{j=0}^{L-1} (tPrev j - T_j) * (M_{j+1} - T_j)`   (over the integers Z).
- Admissible cone `Adm M` = the finite set of `T` with: (a) `T_j <= admBound j` where
  `admBound j = min(M_0,M_1) if j=0 else M_{j+1}`; (b) weakly decreasing `T_i >= T_j` for `i<=j`;
  (c) `T_{L-1} = 0`.
- `lambdaCore M = (1/2) * min_{T in Adm M} Mval M T`   (a rational; min over the nonempty finite cone).
- `balancedSplit P l i = (P/l + 1) if i < P%l else P/l`  (nat division; the balanced split of P into l parts).
- `cleanCore c m = (1/4) * ( sum_{i<c} balancedSplit(P,c,i)^2  -  sum_{k<=c} m_k^2 )`,
  where `m : Fin (c+1) -> Nat`, `P = sum_k m_k`. (A rational.)
- `sortedSmallest M c` (for `c <= L`) = the `c+1` smallest entries of `M`, ascending (via Tuple.sort).

## The FROZEN goal (cannot change the statement)

`lambdaCore_eq_clean : exists (c : Nat) (hc : c <= L), 1 <= c AND
                         lambdaCore M = cleanCore c (sortedSmallest M c hc)`

The `exists c` is an ACHIEVER (NOT an extremum: both min-over-c and max-over-c are FALSE).

## What is already PROVEN in the file (usable engines)

1. `balancedSplit_min (P l) (0<l) (q : Fin l -> Nat) (sum q = P) : sum balancedSplit^2 <= sum q^2`.
   (Balanced split minimizes sum of squares at fixed total. Over Z.)
2. `balancedSplit_sq_int (P l) (0<l) : sum_{i<l} balancedSplit(P,l,i)^2 = l*(P/l)^2 + (P%l)*(2*(P/l)+1)`.
3. `cleanCore_perm` : cleanCore depends only on the MULTISET of m (it is sum and sum-of-squares).
4. `Mval_descent` : Mval M T = sum over strict-descent positions only (zero-gap terms drop).
5. `T_le_tPrev`, `T_le_Msucc`, `Mval_nonneg` (sign facts on the cone).

## Key NEW facts I verified numerically (0 failures), choose the route that exploits these

(A) CLEAN ADM REFRAME: `T in Adm M`  IFF  the sequence `u_0=M_0, u_j = T_{j-1} (1<=j<=L)` satisfies
    `M_0 = u_0 >= u_1 >= ... >= u_L = 0`  AND  `u_j <= M_j` for `j=1..L`. (The index-0 `min(M_0,M_1)`
    special case collapses to just `u_1 <= M_1` because `u_1 <= u_0 = M_0` is automatic.)

(B) RECURSION (verified 0 fails): define
    `g(top, tail)` = min over `top = v_0 >= v_1 >= ... >= v_k = 0` with `v_i <= tail_i (i>=1)`
       of `sum_{i} (v_i - v_{i+1})*(tail_{i+1} - v_{i+1})`,  base `g(top,[w]) = top*w`.
    Then `minMval(M) = min_{v_1 <= min(M_0,M_1)} (M_0 - v_1)(M_1 - v_1) + g(v_1, M[2:])`.

(C) TARGET-AS-FORMULA: the whole goal reduces to proving `minMval(M) = Vstar(M)` where
    `Vstar(M) = (1/2)*( c*b^2 + amod*(2b+1) - sum_{i<=c} a_i^2 )`, `a = sort(M) ascending`,
    `c = cstar(M)`, `P = sum_{i<=c} a_i`, `b = P/c`, `amod = P%c`. Because `2*cleanCore(c, sortedSmallest)
    = Vstar` is PURE ARITHMETIC (immediate from balancedSplit_sq_int), and `cleanCore_perm` lets me use
    the sorted/multiset form freely.

(D) THE ACHIEVER `cstar(M)` = largest `c in {1..L}` with the CUMULATIVE predicate
    `good c := forall 1<=i<=c, i*a_i <= S_i + i - 1` (S_i = sum_{k<=i} a_k); `c=1` always good.
    (The single-step `a_c <= ceil(S_c/c)` is NOT enough; needs cumulative.)

## What I need from you

Rank the candidate ROUTES to `minMval(M) = Vstar(M)` (equivalently the two inequalities
`minMval <= Vstar` via an explicit achiever `T*`, and `minMval >= Vstar` for every admissible T),
by Lean-formalization tractability in Mathlib v4.29, MINIMIZING dependent-`Fin` reindexing. Candidates
I see:

R1. Descent reparametrisation: extract (c_T, gaps, breakpoint-widths) from each T; per-T:
    `Mval M T >= 2*cleanCore(c_T, W_T)`; then `>= Vstar` via "smallest widths win on sorted M". This is
    the historically-thrashing route (the descentSet -> (c,gaps,widths) Fin reindex is the killer).
R2. Induction on L via the recursion (B): prove `g(top, tail) = <closed form>` by induction, peeling
    one layer. Avoids reindex but needs a closed form for `g` and a tricky generalized IH.
R3. A direct "exchange/majorization" argument: lower-bound `Mval M T` for arbitrary T by a global
    sum-of-squares + `balancedSplit_min` WITHOUT extracting c_T (keep index set Fin L fixed).
R4. Something else (an Abel-summation identity, an LP-duality certificate, a potential function...).

For the TOP-RANKED route, give:
  - the precise intermediate lemma statements (in math, Lean-shaped) and their dependency order;
  - where `balancedSplit_min` / `balancedSplit_sq_int` / `cleanCore_perm` plug in;
  - the single hardest sub-step and a concrete tactic-level plan for it;
  - the explicit achiever `T*` construction (as a function of sorted M and cstar) for the `<=` direction,
    and a proof sketch that `T*` is admissible (reframe A) and `Mval M T* = Vstar`.
Be concrete about how to AVOID the variable-length `Fin c_T` reindexing.
</task>

<output_contract>
1. ROUTE RANKING: one line per route (R1-R4) with a tractability verdict (best/viable/avoid + why).
2. CHOSEN ROUTE: numbered intermediate lemmas (math statements), dependency order, where the proven
   engines plug in.
3. HARDEST SUB-STEP: name it, give a concrete tactic-level attack.
4. ACHIEVER T*: explicit formula in (sorted M, cstar); admissibility sketch; value = Vstar sketch.
5. REINDEX-AVOIDANCE: the specific trick that keeps the index set fixed / sidesteps Fin c_T.
Keep it tight. Math, not Lean syntax. Flag any step where you are INFERRING vs CERTAIN.
</output_contract>

<grounding_rules>
All numeric claims above are exhaustively verified by me (0 failures); treat (A)-(D) as TRUE.
If you propose a closed form for `g` (route R2) or any new identity, FLAG it as a conjecture I must
verify numerically before formalizing — do not assert it as fact. Distinguish "this will formalize
cleanly" (inference) from "this is mathematically true" (which I will check).
</grounding_rules>
