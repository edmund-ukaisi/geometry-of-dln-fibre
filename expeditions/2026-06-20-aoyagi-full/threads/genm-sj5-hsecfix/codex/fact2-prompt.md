# Combinatorial lemma: the sharp binding-cut corank bound `a★+b★ ≤ tailMinWidth+1`

I am formalising in Lean 4. I need a clean GENERAL (∀ chain M) proof of a Nat inequality about a
recursively-defined optimum. Please adjudicate the cleanest proof and the MINIMAL correct hypotheses.
Do NOT trust my numeric sweeps as proof — I need a real argument.

## Definitions (exact)

A "chain" is a tuple `M = (M0, M1, …, M_last)` of positive naturals, length ≥ 2. Truncated Nat subtraction.

- `minAdm(M)`:
  - length 2: `M0 * M1`.
  - length ≥ 3: `min over t ∈ [0, min(M0,M1)] of  (M0−t)(M1−t) + minAdm( (t, M2, M3, …, M_last) )`.
    (Peel the leading layer at pivot rank t; the reduced chain replaces the first TWO widths (M0,M1) by
    the single pivot width t, keeping M2..M_last. So the reduced chain is one shorter.)
- `redChain(u, M) = (u, M2, M3, …, M_last)`  (length = len(M) − 1).
- `bindingCut(M) = t★` = the LEAST `t ∈ [0, min(M0,M1)]` achieving the min, i.e.
  `minAdm(M) = (M0−t★)(M1−t★) + minAdm(redChain(t★, M))`.
- `a★ = M0 − t★`,  `b★ = M1 − t★`.
- `tailMinWidth(M) = min(M1, M2, …, M_last)`   (min over indices 1..last; INCLUDES M1).
- `deepRank(M)  = min(M2, …, M_last)`           (EXCLUDES M1).   Note tailMinWidth = min(M1, deepRank).
- `G(u) := minAdm(redChain(u, M))`.  (A function of the single pivot width u, with M2..M_last fixed.)

## What I've PROVEN cleanly (unconditional)
By "reuse the minimizer s₀ of G(u) as a valid competitor for G(u+1)" (s₀ ≤ min(u,M2) ≤ min(u+1,M2)):
    G(u+1) − G(u) ≤ M2 − s₀ ≤ M2.
Combined with binding optimality `minAdm M = f(t★) ≤ f(t★+1)` (valid when t★+1 ≤ min(M0,M1), which holds
when a★≥1 and b★≥1), where `f(u)=(M0−u)(M1−u)+G(u)`:
    a★·b★ − (a★−1)(b★−1) = a★+b★−1 ≤ G(t★+1) − G(t★) ≤ M2,
hence the UNCONDITIONAL bound `a★+b★ ≤ M2 + 1` (given a★≥1, b★≥1).

## What I NUMERICALLY OBSERVE (0 counterexamples, arity 3–6, widths 1–7), but cannot yet prove
1. UNCONDITIONAL increment sharpening: `G(u+1) − G(u) ≤ deepRank(M) = min(M2,…,M_last)` for ALL u.
   (Sharper than my ≤ M2; would give `a★+b★ ≤ deepRank+1` unconditionally.)
2. Under the hypothesis `hpiv : G(t★) ≤ t★·tailMinWidth(M)` (plus t★≥1, a★≥1, b★≥1):
   `a★+b★ ≤ tailMinWidth(M) + 1`, and equivalently `G(t★+1) − G(t★) ≤ tailMinWidth(M)`.
   (Note tailMinWidth ≤ deepRank; when M1 < deepRank ("waist at 1") tailMinWidth = M1 < deepRank, and then
   `a★+b★ ≤ deepRank+1` is NOT enough. hpiv is what removes those.)
3. Under FULL goodness `hgood : ∀u, G(u) ≤ u·tailMinWidth(M)` (stronger than hpiv-at-t★ only): the waist
   cases (deepRank > tailMinWidth) are ENTIRELY excluded, i.e. `hgood ⟹ deepRank(M) = tailMinWidth(M)`
   (equivalently deepRank ≤ M1).

## Questions
Q1. Prove (or refute) the unconditional increment sharpening `G(u+1) − G(u) ≤ deepRank(M)`. Give the
    cleanest inductive argument (induction on chain length / arity). If it needs the minimizer to satisfy
    s₀ ≥ M2 − deepRank, prove that.
Q2. Give the cleanest proof of `a★+b★ ≤ tailMinWidth(M) + 1`. Which hypotheses are MINIMAL —
    hpiv-at-t★, or full hgood (∀u)? For each step name whether it is: binding optimality, the increment
    lemma, or hpiv/hgood. I prefer a route that is short to formalise (Nat arithmetic + the minAdm
    recursion `minAdm_le_peelCharge_add_redChain` and the value-fold `LayerSplit_value_eq_minAdm` which I
    have as `minAdm M ≤ (M0−u)(M1−u) + minAdm(redChain u M)` for any u ≤ min(M0,M1), with equality at t★).
Q3. Is `hgood ⟹ deepRank = tailMinWidth` (Q obs 3) provable, and is that a cleaner decomposition than
    proving `a★+b★ ≤ tailMinWidth+1` directly (i.e. prove `a★+b★ ≤ deepRank+1` + `hgood ⟹ deepRank=tailMinWidth`)?
    Which decomposition minimises Lean pain?
Q4. State the single cleanest theorem I should formalise for fact (2), with exact hypotheses.
