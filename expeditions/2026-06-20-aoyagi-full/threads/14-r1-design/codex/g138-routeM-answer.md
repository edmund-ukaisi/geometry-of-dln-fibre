Short answer: **not complete as written**. The taxonomy misses a mixed node unless C1 is broadened beyond its stated “regular squares + reduced chain” form.

**Missed Layer Structure**

Take active prefix ranks, in map notation \(V_0 \to \cdots \to V_5\), with all relevant widths at least 3:

\[
(t_0,t_1,t_2,t_3,t_4,t_5)=(3,3,2,2,2,0).
\]

Layer 2 has a genuine partial rank drop \(3 \to 2\), but the surviving rank-2 block passes through layers 3 and 4 before being killed at layer 5. In local bases:

\[
C_2 \sim
\begin{pmatrix}
I_2 & 0\\
0 & Z
\end{pmatrix},
\]

so

\[
C_5C_4C_3C_2C_1
=
\big[
C_5C_4C_3|_U
\quad
C_5C_4C_3|_W Z
\big].
\]

The first block is a **pass-through/later-drop** problem. The second is a **coupled defect** problem. This node is not C2, because \(C_2\) is not full rank on the active prefix. It is not C4, because the surviving rank is 2, not a width-1 pinch. It is not C3, which is only NC cleanup. And it is not C1 as stated, because C1 claims the Schur step gives “regular squares + reduced chain”; here the surviving block is not regular until later full-rank layers are passed through.

So C1 must be generalized to a **mixed Schur/pass-through node** for \(t_{s-1}>t_s>0\), or the taxonomy is not exhaustive.

**Termination**

The stated lex measure \((L,\sum M_s)\) works for the clean core moves:

- C2: \(L\) drops.
- C1: if genuinely Schur-reducing dimensions, \(\sum M_s\) drops.
- C4: if treated as a Fubini split, each child subproblem has smaller depth.

But it does **not** account for C3. NC-completion blow-ups do not necessarily change \(L\) or \(\sum M_s\). They need a separate well-founded invariant, such as complexity of the non-NC exceptional arrangement. Without that, C3 is a same-measure move.

The mixed node above is also a stuck node under the literal branch logic: neither C1 nor C2 cleanly applies.

**Value Argument**

The lower bound is sound only if the multiplicity-control inequality is proved for **every** divisor created, including mixed-node divisors:

\[
m\,k_E \le h_E+1,\quad m=\minAdm Mval.
\]

For NC intersection blow-ups, this is plausible: new multiplicity and discrepancy add,

\[
k_E=\sum k_i,\qquad h_E+1=\sum(h_i+1),
\]

so the ratio is a weighted average and cannot undershoot. The dangerous gap is not C3 itself; it is unproved control for omitted mixed Schur/pass-through centers.

The equality direction also depends on the taxonomy containing a chart path to every minimizing admissible prefix-rank tuple. The mixed tuple above is admissible, so the current taxonomy does not guarantee the achiever leaf exists.

**Verdict**

As written: **not complete, not fully terminating, and value correctness is conditional**.

Load-bearing fixes:

1. Define “full rank” and “rank defect” relative to the current active prefix image, not global matrix rank.
2. Add a mixed node for \(t_{s-1}>t_s>0\) where a survivor block passes through while a complement is Schur-reduced.
3. Give C3 its own termination invariant.
4. Prove \(m k_E \le h_E+1\) for all C1, mixed, C4, and C3 divisors.
5. Prove the minimising admissible rank tuple selects an actual leaf path.

With those additions, the construction may be salvageable. Without them, the mixed partial-drop plus later-pass-through structure breaks the claimed exhaustiveness.