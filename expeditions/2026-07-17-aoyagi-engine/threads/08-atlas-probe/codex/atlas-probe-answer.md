## Q1

**Boot convention inferred:** the transcription does not specify \(S=0\to1\). I start at \((S,J)=(1,0)\) with no actual divisor coordinates. Thus the \(S=1\) Case-2 steps produce

\[
T=(r,r),\qquad M=(M^{(1)}-r)(M^{(2)}-r).
\]

If the stated initialization denotes an actual initial divisor rather than a sentinel, the atlas is underdetermined from the transcription.

Write \(U=\) Case 1(1) and \(D=\) Case 1(2).

### Instance I: \(M=(2,2,2)\)

The terminal formula is

\[
F(t_1,t_2)=(2-t_1)^2+(t_1-t_2)(2-t_2).
\]

The \(S=1\) divisors are \((0,0)\) and \((1,1)\). At \((S,J,J_1)=(2,0,1)\), the sole parent is \((1,1)\).

| Leaf | Case-1 path | Terminal \(\widetilde t=0\) divisors \(T:M\) | Leaf minimum |
|---|---|---|---:|
| I-U | \(U_{(1,1)}\) | \((0,0):4,\ (1,0):3,\ (2,0):4\) | 3 |
| I-D | \(D_{(1,1)}\) | \((0,0):4,\ (1,0):3\) | 3 |

Arithmetic:

\[
F(0,0)=4,\quad F(1,0)=1+2=3,\quad F(2,0)=0+4=4.
\]

Independently,

\[
\operatorname{minAdm}(2,2,2)
=\min_{t=0,1,2}\bigl((2-t)^2+2t\bigr)
=\min\{4,3,4\}=3.
\]

Hence every combinatorial leaf has minimum \(3\), giving candidate \(\lambda_0=3/2\).

Under the standard inference that every residual \(d_{ij}\) supplies a coordinate chart, I-U represents \(16\) charts and I-D represents \(8\), for \(24\) actual charts.

### Instance II: \(M=(3,3,4)\)

Now

\[
F(t_1,t_2)=(3-t_1)^2+(t_1-t_2)(4-t_2).
\]

The \(S=1\) divisors are

\[
A=(0,0),\qquad B=(1,1),\qquad C=(2,2).
\]

| Leaf | Case-1 path | Terminal \(\widetilde t=0\) divisors \(T:M\) | Leaf minimum |
|---|---|---|---:|
| II-1 | \(U_B,U_C\) | \((0,0):9,(1,0):8,(2,0):9,(3,0):12\) | 8 |
| II-2 | \(U_B,D_C@J=0,U_C@J=1\) | \((0,0):9,(1,0):8,(2,0):9\) | 8 |
| II-3 | \(U_B,D_C@J=0,D_C@J=1\) | \((0,0):9,(1,0):8,(2,0):9\) | 8 |
| II-4 | \(D_B@J=0,U_C@J=1\) | \((0,0):9,(1,0):8\) | 8 |
| II-5 | \(D_B@J=0,D_C@J=1\) | \((0,0):9,(1,0):8\) | 8 |

Arithmetic:

\[
\begin{aligned}
F(0,0)&=9,\\
F(1,0)&=4+4=8,\\
F(2,0)&=1+8=9,\\
F(3,0)&=0+12=12.
\end{aligned}
\]

Also,

\[
\operatorname{minAdm}(3,3,4)
=\min_{t=0,1,2,3}\bigl((3-t)^2+4t\bigr)
=\min\{9,8,9,12\}=8.
\]

Thus every combinatorial leaf has minimum \(8\), giving candidate \(\lambda_0=4\).

With one chart per center generator, the five leaf multiplicities are respectively

\[
5184,\ 3456,\ 1728,\ 1728,\ 864,
\]

totalling \(12960\). This multiplicity expansion is inferred; the transcription specifies only chart types.

### Undershoot and coverage verdict

There is **no eligible undershoot**: every emitted divisor with \(\widetilde t=0\) appears in the tables, and none has \(M<3\) or \(M<8\).

There are literal small \(M\)-values among positive-\(\widetilde t\) divisors:

\[
(2,1)\text{ in I has }F=1,\qquad
(2,2)\text{ in II has }F=1.
\]

These are not LCT ratios. If \(\widetilde t=q>0\), that coordinate first occurs in \(b_{q+1}\), not \(b_1\). Since the terminal ideal is \(\langle b_1\rangle\), its order along that divisor is \(0\); \(M/2\) is therefore inapplicable.

For coverage:

- If Case 1(2) and Case 2 include every residual \(d_{ij}\)-pivot chart, each blow-up is covered by its ordinary generator charts. Inductively the full iterated blow-up is covered, so every nearby point—and hence every point with \(C^{(1)}C^{(2)}=0\)—has a lift. I found no gap under this reading.
- This replication is not forced by the transcription. If “the corner entry” means one fixed entry only, there is an immediate gap: take
  \[
  C^{(1)}=\begin{pmatrix}0&\varepsilon\\0&0\end{pmatrix},\qquad C^{(2)}=0
  \]
  with nonzero rational \(\varepsilon\) arbitrarily small. It is not in the fixed \(c_{11}\)-pivot chart’s image, since \(c_{11}=0\) there forces every \(C^{(1)}\)-entry to vanish.

## Q2

No Case-1 node in either requested instance has competing divisors at its selected level:

- Instance I: \((S,J,J_1)=(2,0,1)\), sole candidate \((1,1)\).
- Instance II: \((2,0,1)\), sole candidate \((1,1)\); and the various \((2,0,2)\) or \((2,1,1)\) nodes each have sole candidate \((2,2)\).

Total comparability does **not** imply equality at common \(\widetilde t\). Instance I already ends with the comparable but different vectors

\[
(1,1)< (2,1),\qquad \widetilde t=1.
\]

They merely never become competing candidates because the layer has ended.

The smallest class producing a genuine tie-break has \(L=3\) and its first three widths at least \(2\). For example, on \(M=(2,2,2,1)\), take \(D\) at \((S,J)=(2,0)\). At the end of layer \(2\) one has

\[
(1,1,1),\qquad (2,1,1),
\]

both at level \(1\). At \((S,J,J_1)=(3,0,1)\), both compete, and full-vector minimality selects \((1,1,1)\). Thus \(\widetilde t\) alone is genuinely insufficient. If width \(1\) is disallowed by an unstated “reduced” convention, use \((2,2,2,2)\).

## Q3

The \(T\)-update is a clean operation on a fixed index set \(\{1,\dots,L\}\):

- Case 1(1): mutate one record by setting \(t^{(S)},\dots,t^{(L)}:=J\).
- Case 1(2): create one record, copying the parent’s head and setting its tail to \(J\).
- Case 2: create one record, resetting its head to the prescribed widths and its tail to \(J\).

There is no re-indexing or vector merging. Divisor records grow in number, but every \(T\) retains length \(L\). The dynamic work belongs to the \(b\)-chain: inserting or moving a divisor between \(\widetilde t\)-levels and maintaining divisibility products.

Tracking full \(T\) is cheap: \(O(L)\) storage and comparison per divisor versus \(O(1)\) for \(\widetilde t\) alone. For fixed depth, this is constant-size bookkeeping.

## MOST LIKELY WRONG

Q1 — The least certain step is the inferred \(S=1,J=0\) boot and all-pivot expansion; neither is explicitly specified.  
Q2 — “Smallest” uses terminal width \(1\); an unstated reduced-width restriction could change the smallest tuple to \((2,2,2,2)\).  
Q3 — I infer that old divisor records persist after Case 1(2); the transcription describes creation but does not explicitly state persistence.