   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.2
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019efdeb-edef-7b60-9491-c3c04b0653e2
--------
user
<task>
Decorrelated check of ONE block-matrix identity + its germ orders, for a Lean RLCT formalisation. Re-derive
independently. Do NOT rubber-stamp.
</task>

<setting>
Block-(r+M) matrices, L=2 layers: C_s = [[a_s, Y_s],[Z_s, T_s]], s=0,1, where now the PIVOT a_s is an
r×r MATRIX (r≥2), Y_s is r×M, Z_s is M×r, T_s is M×M. At the "deepest point" a_s → I_r, Y_s,Z_s → 0,
T_s → core. Write a_s = I_r + X_s (X_s the r×r deviation → 0).

Two M×M core quantities:
- R = Schur complement of the PRODUCT P = C0·C1 wrt its r×r (1,1) block: R = P22 − P21·P11⁻¹·P12
  (P11 the r×r top-left block of the product, INVERTIBLE near the deepest point).
- ∏S = S0·S1, per-layer Schur S_s = T_s − Z_s·a_s⁻¹·Y_s (M×M).

For a SCALAR pivot (r=1) I proved exactly: R = S0·W·S1, W = I_M − Z1·A⁻¹·Y0, A = a0a1 + Y0·Z1 (the
product's (1,1) block), W → I_M, det-driven; and on a germ (all deviations ~ ε) R−∏S = O(ε⁴) while
∏S = O(ε²), giving the in-sum comparability |∑‖R‖²−∑‖∏S‖²| ≤ C·∑E².

I need the r≥2 (matrix-pivot) confirm:
</setting>

<questions>
1. Block-LDU with a MATRIX pivot: C_s = L_s·diag(a_s, S_s)·U_s where L_s=[[I_r,0],[Z_s a_s⁻¹, I_M]],
   U_s=[[I_r, a_s⁻¹ Y_s],[0, I_M]], S_s = T_s − Z_s a_s⁻¹ Y_s. (All standard for an invertible matrix
   pivot a_s.) Confirm this LDU holds for matrix a_s (it should — it's the standard block-LU with the
   Schur complement; the only requirement is a_s invertible, true near the deepest point).
2. Schur-invariance under the outer unipotents: Schur(L0·X·U1) = Schur(X) for L0 lower-unipotent (r×r
   identity (1,1)), U1 upper-unipotent. Does this hold with MATRIX blocks? (It should — the Schur
   complement is invariant under such block-triangular unipotent congruences. Confirm the block algebra.)
3. So R = Schur(D0·M·D1), D_s = diag(a_s, S_s), M = U0·L1. What is M's block form with matrix pivots,
   and does the (2,2)-Schur of D0 M D1 give R = S0·W·S1 with W = I_M − (some matrix coupling) → I_M?
   Pin the EXACT W (it may be Z1·(a0 a1 + Y0 Z1)⁻¹·Y0 — i.e. the GLOBAL product pivot A = P11 — or a
   per-layer-coupled version; the r=1 case had A = the product (1,1) block). Is A⁻¹ bounded near 0
   (A → I_r)?
4. THE GERM ORDERS (the load-bearing check): with all deviations X_s,Y_s,Z_s,T_s ~ O(ε), is
   S_s = O(ε)?  ∏S = O(ε²)?  R − ∏S = O(ε⁴)? (i.e. the matrix coupling W − I = O(ε²), times S0,S1 each
   O(ε), gives R − ∏S = S0·(W−I)·S1 = O(ε⁴) — strictly higher than ∏S = O(ε²)). Confirm the matrix pivot
   does NOT break this order count (the worry: does a_s⁻¹ = (I+X_s)⁻¹ = I − X_s + … introduce an O(ε)
   term into W − I that would make R − ∏S only O(ε³)?).
5. Net: does the in-sum germ comparability |∑‖R‖²−∑‖∏S‖²| ≤ C·∑E² survive the matrix pivot, with A⁻¹
   bounded (A → I_r) and the order count intact? If a matrix-pivot obstruction appears (A⁻¹ unbounded,
   or the order breaks to O(ε³)), state it precisely.
</questions>

<output_contract>
Per question VERDICT + reasoning, exact block-algebra vs inference marked. The decisive output: does the
matrix-pivot LDU give R = S0·W·S1 with W→I_r-bounded, and does R−∏S = O(ε⁴) (vs ∏S=O(ε²)) survive?
End with: "The r≥2 matrix-pivot S5c is [CONFIRMED germ / OBSTRUCTED because ___]; W = ___, R−∏S = O(ε^?)."
</output_contract>

<grounding_rules>
Re-derive the block-LU with matrix pivots. The crux is whether a_s⁻¹ = (I+X_s)⁻¹ introduces an O(ε)
contamination into W−I that drops the R−∏S order from ε⁴ to ε³. Track the lowest order of W−I carefully.
</grounding_rules>

codex
I’ll derive this from the block multiplications directly and keep track of the multiplication order, since that is exactly where the matrix-pivot case can differ from the scalar case.
codex
**Q1 Verdict: CONFIRMED.**  
Exact block algebra, with no scalar commutativity used:

\[
\begin{pmatrix}I&0\\ Z_sa_s^{-1}&I\end{pmatrix}
\begin{pmatrix}a_s&0\\0&S_s\end{pmatrix}
\begin{pmatrix}I&a_s^{-1}Y_s\\0&I\end{pmatrix}
=
\begin{pmatrix}
a_s & Y_s\\
Z_s & Z_sa_s^{-1}Y_s+S_s
\end{pmatrix}
=
\begin{pmatrix}
a_s & Y_s\\
Z_s & T_s
\end{pmatrix}.
\]

So the LDU factorisation is valid for an invertible matrix pivot \(a_s\).

**Q2 Verdict: CONFIRMED.**  
Let \(X=\begin{pmatrix}A&B\\ C&D\end{pmatrix}\), \(A\) invertible, and

\[
L=\begin{pmatrix}I&0\\K&I\end{pmatrix},
\qquad
U=\begin{pmatrix}I&H\\0&I\end{pmatrix}.
\]

Then

\[
LXU=
\begin{pmatrix}
A & AH+B\\
KA+C & (KA+C)H+KB+D
\end{pmatrix}.
\]

Its Schur complement is

\[
(KA+C)H+KB+D-(KA+C)A^{-1}(AH+B)
= D-CA^{-1}B.
\]

So \(\operatorname{Schur}(LXU)=\operatorname{Schur}(X)\), exactly, for matrix blocks.

**Q3 Verdict: CONFIRMED.**  
Here

\[
M=U_0L_1
=
\begin{pmatrix}
I_r+a_0^{-1}Y_0Z_1a_1^{-1} & a_0^{-1}Y_0\\
Z_1a_1^{-1} & I_M
\end{pmatrix}.
\]

Thus

\[
D_0MD_1
=
\begin{pmatrix}
a_0a_1+Y_0Z_1 & Y_0S_1\\
S_0Z_1 & S_0S_1
\end{pmatrix}.
\]

The top-left block is exactly the global product pivot

\[
A=P_{11}=a_0a_1+Y_0Z_1.
\]

Therefore

\[
R
=
S_0S_1-(S_0Z_1)A^{-1}(Y_0S_1)
=
S_0\bigl(I_M-Z_1A^{-1}Y_0\bigr)S_1.
\]

So the exact coupling is

\[
\boxed{W=I_M-Z_1(a_0a_1+Y_0Z_1)^{-1}Y_0.}
\]

Since \(a_s\to I_r\) and \(Y_0Z_1\to0\), we have \(A\to I_r\), hence \(A^{-1}\) is bounded near the deepest point.

**Q4 Verdict: CONFIRMED.**  
Assuming \(T_s\) denotes the germ/deviation coordinate with \(T_s=O(\epsilon)\),

\[
a_s^{-1}=(I_r+X_s)^{-1}=I_r+O(\epsilon),
\]

so

\[
Z_sa_s^{-1}Y_s=O(\epsilon)\,O(1)\,O(\epsilon)=O(\epsilon^2).
\]

Hence

\[
S_s=T_s-Z_sa_s^{-1}Y_s=O(\epsilon),
\qquad
S_0S_1=O(\epsilon^2).
\]

For \(W\),

\[
A=(I+X_0)(I+X_1)+Y_0Z_1
=I+O(\epsilon),
\]

so

\[
A^{-1}=I+O(\epsilon).
\]

But this is sandwiched between \(Z_1\) and \(Y_0\):

\[
W-I_M=-Z_1A^{-1}Y_0
=-Z_1Y_0+O(\epsilon^3)
=O(\epsilon^2).
\]

Thus there is no \(O(\epsilon)\) contamination from \(a_s^{-1}\) or \(A^{-1}\). Consequently

\[
R-S_0S_1
=
S_0(W-I_M)S_1
=
O(\epsilon)\,O(\epsilon^2)\,O(\epsilon)
=
O(\epsilon^4).
\]

**Q5 Verdict: CONFIRMED.**  
The same in-sum germ comparison survives the matrix pivot. If \(Q=S_0S_1\) and \(\Delta=R-Q\), then

\[
Q=O(\epsilon^2),
\qquad
\Delta=O(\epsilon^4),
\]

so

\[
\left|\|R\|^2-\|Q\|^2\right|
=
\left|\|Q+\Delta\|^2-\|Q\|^2\right|
\le
2\|Q\|\|\Delta\|+\|\Delta\|^2
=
O(\epsilon^6).
\]

For finite sums, the same order estimate holds termwise. Thus the matrix-pivot case introduces no obstruction beyond the scalar case’s existing germ-domination assumptions.

The r≥2 matrix-pivot S5c is **CONFIRMED germ**; \(W = I_M-Z_1(a_0a_1+Y_0Z_1)^{-1}Y_0\), \(R-\prod S = O(\epsilon^4)\).
tokens used
11,036
**Q1 Verdict: CONFIRMED.**  
Exact block algebra, with no scalar commutativity used:

\[
\begin{pmatrix}I&0\\ Z_sa_s^{-1}&I\end{pmatrix}
\begin{pmatrix}a_s&0\\0&S_s\end{pmatrix}
\begin{pmatrix}I&a_s^{-1}Y_s\\0&I\end{pmatrix}
=
\begin{pmatrix}
a_s & Y_s\\
Z_s & Z_sa_s^{-1}Y_s+S_s
\end{pmatrix}
=
\begin{pmatrix}
a_s & Y_s\\
Z_s & T_s
\end{pmatrix}.
\]

So the LDU factorisation is valid for an invertible matrix pivot \(a_s\).

**Q2 Verdict: CONFIRMED.**  
Let \(X=\begin{pmatrix}A&B\\ C&D\end{pmatrix}\), \(A\) invertible, and

\[
L=\begin{pmatrix}I&0\\K&I\end{pmatrix},
\qquad
U=\begin{pmatrix}I&H\\0&I\end{pmatrix}.
\]

Then

\[
LXU=
\begin{pmatrix}
A & AH+B\\
KA+C & (KA+C)H+KB+D
\end{pmatrix}.
\]

Its Schur complement is

\[
(KA+C)H+KB+D-(KA+C)A^{-1}(AH+B)
= D-CA^{-1}B.
\]

So \(\operatorname{Schur}(LXU)=\operatorname{Schur}(X)\), exactly, for matrix blocks.

**Q3 Verdict: CONFIRMED.**  
Here

\[
M=U_0L_1
=
\begin{pmatrix}
I_r+a_0^{-1}Y_0Z_1a_1^{-1} & a_0^{-1}Y_0\\
Z_1a_1^{-1} & I_M
\end{pmatrix}.
\]

Thus

\[
D_0MD_1
=
\begin{pmatrix}
a_0a_1+Y_0Z_1 & Y_0S_1\\
S_0Z_1 & S_0S_1
\end{pmatrix}.
\]

The top-left block is exactly the global product pivot

\[
A=P_{11}=a_0a_1+Y_0Z_1.
\]

Therefore

\[
R
=
S_0S_1-(S_0Z_1)A^{-1}(Y_0S_1)
=
S_0\bigl(I_M-Z_1A^{-1}Y_0\bigr)S_1.
\]

So the exact coupling is

\[
\boxed{W=I_M-Z_1(a_0a_1+Y_0Z_1)^{-1}Y_0.}
\]

Since \(a_s\to I_r\) and \(Y_0Z_1\to0\), we have \(A\to I_r\), hence \(A^{-1}\) is bounded near the deepest point.

**Q4 Verdict: CONFIRMED.**  
Assuming \(T_s\) denotes the germ/deviation coordinate with \(T_s=O(\epsilon)\),

\[
a_s^{-1}=(I_r+X_s)^{-1}=I_r+O(\epsilon),
\]

so

\[
Z_sa_s^{-1}Y_s=O(\epsilon)\,O(1)\,O(\epsilon)=O(\epsilon^2).
\]

Hence

\[
S_s=T_s-Z_sa_s^{-1}Y_s=O(\epsilon),
\qquad
S_0S_1=O(\epsilon^2).
\]

For \(W\),

\[
A=(I+X_0)(I+X_1)+Y_0Z_1
=I+O(\epsilon),
\]

so

\[
A^{-1}=I+O(\epsilon).
\]

But this is sandwiched between \(Z_1\) and \(Y_0\):

\[
W-I_M=-Z_1A^{-1}Y_0
=-Z_1Y_0+O(\epsilon^3)
=O(\epsilon^2).
\]

Thus there is no \(O(\epsilon)\) contamination from \(a_s^{-1}\) or \(A^{-1}\). Consequently

\[
R-S_0S_1
=
S_0(W-I_M)S_1
=
O(\epsilon)\,O(\epsilon^2)\,O(\epsilon)
=
O(\epsilon^4).
\]

**Q5 Verdict: CONFIRMED.**  
The same in-sum germ comparison survives the matrix pivot. If \(Q=S_0S_1\) and \(\Delta=R-Q\), then

\[
Q=O(\epsilon^2),
\qquad
\Delta=O(\epsilon^4),
\]

so

\[
\left|\|R\|^2-\|Q\|^2\right|
=
\left|\|Q+\Delta\|^2-\|Q\|^2\right|
\le
2\|Q\|\|\Delta\|+\|\Delta\|^2
=
O(\epsilon^6).
\]

For finite sums, the same order estimate holds termwise. Thus the matrix-pivot case introduces no obstruction beyond the scalar case’s existing germ-domination assumptions.

The r≥2 matrix-pivot S5c is **CONFIRMED germ**; \(W = I_M-Z_1(a_0a_1+Y_0Z_1)^{-1}Y_0\), \(R-\prod S = O(\epsilon^4)\).
