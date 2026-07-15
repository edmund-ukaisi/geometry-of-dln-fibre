<task>
Adjudicate an exact-combinatorics genericity fact from a deep-linear-network fibre-RLCT proof.

SETUP (all widths are positive integers). A chain M = (M0, M1, M2, ..., M_last) of layer widths
(arity = number of widths; layers = arity-1 generic real matrices multiplied). Define:
  deepTailMin(M) = min(M2, M3, ..., M_last)   [the minimum over the DEEP tail widths, strictly past M1]
  minAdm: the "admissible codimension" of the chain, given by the recursion
     minAdm(d0, d1) = d0 * d1                                        (arity-2 leaf)
     minAdm(M) = min over t in [0, min(M0,M1)] of
                    [ (M0 - t)*(M1 - t) + minAdm( (t, M2, ..., M_last) ) ]   (arity >= 3)
     where (t, M2, ..., M_last) is the "reduced chain": replace the first two widths (M0,M1) by the
     single width t, keeping the deep tail. (So the recursion peels the front pair into a width-t node.)

A "cut" is a pair (t, j): an outer peel depth t >= 1 and a shell index j with 1 <= j < r,
where r = min(M0 - t, M1 - t). At a cut define u = t + j, a = M0 - u, b = M1 - u.

THE DEEP FACTOR. Z_deep(z) = the product of the deep-tail layers, a generic real matrix product with
widths (M2, M3, ..., M_last), an (M2 x M_last) matrix depending on real parameters z. Standard fact
(you may take it as given): for Lebesgue-a.e. z, rank(Z_deep(z)) = min(M2, ..., M_last) = deepTailMin(M),
and rank(Z_deep(z)) <= deepTailMin(M) for ALL z.

THE FACT TO ADJUDICATE:  ∀ᵐ z,  b <= rank(Z_deep(z)).
Downstream this feeds a corank-survival lemma: for a FIXED Z_deep with b <= rank(Z_deep), a.e. free
b×M2 matrix A_cor has rank(A_cor · Z_deep) = b (full row rank). So the fact is exactly the input
"b <= rank(Z_deep)" for a.e. z.

SCOPE that the proof currently assumes at a cut:
  (S1) GOOD branch: deepTailMin(M) <= M1.
  (S2) strict shell: 1 <= j < r,  r = min(M0-t, M1-t).
  (S3) a + b <= M2.

An important structural fact about the downstream integral: the shell restriction on the outer
variable has ALREADY been dropped (an a-fortiori "integrate over the full box" step) BEFORE the point
where "b <= rank(Z_deep)" is needed. So a discharge that relies on the shell/singular-set restriction
forcing rank(Z_deep) up is NOT available at that integrand; the fact must hold over the full parameter box.

QUESTIONS (use exact reasoning; small explicit chains welcome):
 Q1. Since rank(Z_deep(z)) <= deepTailMin(M) always and = deepTailMin(M) a.e., the fact
     "∀ᵐ z, b <= rank(Z_deep(z))" is equivalent to the Nat inequality  b <= deepTailMin(M).
     Under scope (S1)+(S2)+(S3), is  b <= deepTailMin(M)  GUARANTEED? If not, give the smallest
     explicit chain + cut where it FAILS (i.e. b > deepTailMin(M) while (S1),(S2),(S3) all hold).
     Note arity 3 has deepTailMin = M2, so there (S3) gives b <= a+b <= M2 = deepTailMin; the question
     is whether deeper chains (arity >= 4) can break it.
 Q2. There is a distinguished cut per chain: the "binding cut" u = t* + j, where t* is an argmin of
     the minAdm recursion (t* = argmin_t [ (M0-t)(M1-t) + minAdm((t,M2,...,M_last)) ]). Suppose the
     proof only ever needs the fact at cuts with t = t* (the argmin). At such binding cuts, with
     1 <= j < r, is  b <= deepTailMin(M)  guaranteed? Prove it or give a counterexample. If it holds,
     give the cleanest argument (hint to consider: the optimality inequality f(t*) <= f(t*+1), and the
     marginal behaviour of  g(t) := minAdm((t, M2, ..., M_last))  as a function of t).
 Q3. What is the marginal  g(t+1) - g(t)  bounded by (g as in Q2)? State the tightest clean bound you
     can justify, and use it to complete Q2.
 Q4. Given the shell-drop note above (no shell-determinism available), what is the cleanest route to
     discharge "∀ᵐ z, b <= rank(Z_deep(z))": (a) a pure Nat inequality from the scope, (b) a Nat
     inequality from the binding-cut optimality, or (c) a fresh a.e.-in-z genericity lemma
     ("generic rank of the deep product = min width", i.e. a b×b minor of Z_deep is a nonzero
     polynomial in z)? Which combination is actually required, and is (c) avoidable?
</task>

<output_contract>
Answer Q1..Q4 in order. For each, label every claim [FACT] (proved/computed) or [INFERENCE].
Q1: YES/NO + smallest explicit counterexample chain+cut if NO (give M, t, j, u, a, b, deepTailMin).
Q2: PROVED/COUNTEREXAMPLE + the argument.
Q3: the bound on g(t+1)-g(t) + one-line justification.
Q4: which of (a)/(b)/(c) (or combination) is needed; whether (c) is avoidable. Keep under ~500 words.
</output_contract>

<grounding_rules>
Do not assume the fact is true or false — argue from the definitions. Verify Q1's counterexample (if
any) by explicitly computing deepTailMin and checking (S1),(S2),(S3). For Q2/Q3, if you assert a
marginal bound, justify it from the minAdm recursion (a competitor/peeling argument), don't hand-wave.
Flag any step you cannot fully justify as [INFERENCE].
</grounding_rules>
