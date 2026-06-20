# Blocked audit - Lemma 5 displayed-family realisation

Status: full source-family realisation is not formalisation-ready.

This audit normalises Aoyagi Lemma 5's displayed vectors on PDF pp. 26-27,
especially equations `(3)` and `(4)`, and records the source guards that must
be made explicit before any theorem can claim terminal variables or pole-order
count.

## Source Context

Aoyagi first counts same-coordinate intervals

```text
I_j = { H : Htilde_j <= H <= Htilde'_j },       j=1,...,ell-1.
```

The paper then says that because `J` is increased by one in Case 1(2), one has
`theta <= a(ell-a)+1`, and displays several vectors `T_{s,k}`.  The final
sentence says that equations `(3)` and `(4)` are used in Case 1(2) to
construct the blow-up process.

## Normalised Equation (3)

Let

```text
L_j = Htilde_j,
U_j = Htilde'_j,
c = ell-a,
B_j = { S : S_j-1 <= S < S_(j+1)-1 }.
```

Equation `(3)` handles the special pair excluded from `(2)`:

```text
s = S_2-1,
k = U_1+1.
```

The displayed vector is:

```text
t^(S) =
  M(S+1)       if S < S_2-1,
  U_(j-1)      if S in B_j, 2 <= j <= c+1,
  U_(c+1)+1    if S = S_(c+2)-1,
  U_(j-1)      if S > S_(c+2)-1 and S in B_j.
```

Guards not supplied as theorems by the displayed source:

- `1 <= a`, so that `S_(c+2)` lies in the printed selected list.
- `a < ell`, so the own coordinate `S=s=S_2-1` is in the second branch and
  gives `t^(s)=U_1=k-1`.
- `U_1+1 <= M(S_2)`, so the source label `k` is legal.
- a terminal/tail convention giving a zero coordinate if this vector is to
  satisfy `tilde t_{s,k}=0`.

The special `U_(c+1)+1` value is outside the same-coordinate interval.  It
looks like the Case 1(2) trigger that increases `J`, not an interval member.

## Normalised Equation (4)

Equation `(4)` has fixed label

```text
s = S_(j0+1)-1,
k = L_j0+1,
```

and the source prints `j0 <= a`.  Writing `p=j0`, the displayed vector is:

```text
t^(S) =
  M(S+1)          if S < S_2-1,
  U_(j-1)-j+1     if S in B_j, 2 <= j <= p+1,
  U_(j-1)-p       if S in B_j, p+1 < j <= p+c+1,
  U_(j-1)-p+1     if S = S_(j+1)-1 and j = p+c+1,
  U_(j-1)         if S > S_(p+c+2)-1 and S in B_j.
```

Extra guards found by reproduction:

- `1 <= p`.
- `p <= a`, printed by the source.
- `p <= ell-a`, needed for the own-coordinate calculation
  `U_p-p=L_p`, so that `t^(s)=k-1`.
- an index-existence guard for `S_(p+c+2)`, for example `p <= a-1` unless a
  source convention supplies an extra terminal `S_(ell+2)`.
- terminal/tail and nonnegativity hypotheses if one wants `tilde t_{s,k}=0`.

## Blockers

- The source does not prove legal label bounds such as `U_1+1 <= M(S_2)` for
  equation `(3)`.
- The printed equation `(4)` range gives only `j0 <= a`; own-coordinate
  consistency also needs `j0 <= ell-a`.
- The source does not explicitly state a terminal/tail convention sufficient
  to prove `tilde t_{s,k}=0` for equations `(3)` and `(4)`.
- The final Case 1(2) sentence does not specify the chart sequence turning the
  one-step-above displayed values into terminal variables.

## 2026-06-20 source audit update

An xhigh source audit reconfirmed that equation `(4)` is not
formalisation-ready as a terminal source-vector theorem.  The paper's final
Lemma 5 sentence says that equations `(3)` and `(4)` are used in Case 1(2),
but it does not give the finite sequence of charts, verify the Case 1 gap
hypothesis at each step, assign the terminal selected endpoint
`S_(ell+1)-1`, or prove `tilde t_{s,k}=0`.

The safe boundary is therefore supplied-data bookkeeping only: if a future
record supplies the terminal endpoint assignment
`T(S_(ell+1)-1)=Htilde'_ell`, then Definition 3's selected-sum identity proves
that endpoint value is zero.  This does not remove the displayed-vector
realisation blocker.

## Safe First Lean Target

The source-faithful finite arithmetic target is only the equation `(4)`
own-coordinate sanity:

```text
U_p - p = L_p
```

under the explicit guards `p <= a` and `p <= ell-a`.

This does not prove equation `(4)` is a legal source vector, does not prove
`tilde t=0`, and does not prove Lemma 5.
