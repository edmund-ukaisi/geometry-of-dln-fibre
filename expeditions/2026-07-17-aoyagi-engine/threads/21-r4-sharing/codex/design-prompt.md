# Design red-team: Aoyagi resolution — the divisor-sharing / support field

You are a decorrelated second opinion on a Lean-formalisation design decision. Re-derive from
scratch; do not defer to any framing. Exact algebra only.

## Setup (Aoyagi 2023, the deep-linear-network / RRR resolution of the multiplication ideal)

A tuple of composable matrices $C^{(1)}\cdots C^{(L)}$; the squared Frobenius loss is
$F=\lVert\prod_s C^{(s)}\rVert^2$. Aoyagi resolves the singularity by iterated blow-ups. The recursion
maintains an inductive invariant (indexed by layer $S$ and cleared-pivot count $J$):

$$\Big\langle\prod_{s=1}^L C^{(s)}\Big\rangle
 =\Big\langle\operatorname{diag}(b_1,\dots,b_{M(S)})\begin{pmatrix}E_J&O\\O&D_J\end{pmatrix}
   \prod_{s=S+1}^L C^{(s)}\Big\rangle,$$

where $M(S)=\min\{M^{(s)}:s\le S\}$, $D_J$ is the $(M(S){-}J)\times(M^{(S+1)}{-}J)$ residual block,
and the $b_i$ are monomials in the exceptional blow-up coordinates $u_{s,k}$:
$$b_0=1,\qquad b_i=\Big(\prod_{\tilde t_{s,k}=i-1}u_{s,k}\Big)\,b_{i-1}.$$

Here $\tilde t_{s,k}=\min T_{s,k}$ is the "clearing level" of the exceptional divisor $u_{s,k}$, a
derived scalar of that divisor's full rank-pattern vector $T_{s,k}=(t^{(1)},\dots,t^{(L)})$. Each
divisor also carries a Jacobian/blow-up exponent $M_{s,k}$ (the change-of-variables power, distinct
from its multiplicity in the $b$-chain). At the terminal leaf ($S=L{+}1$) the block is fully diagonal
and $F=\sum_i b_i^2$ (normal crossings).

At corank $\ge 2$ (a genuine $\ge 2\times2$ residual block $D_J$), two loss generators can SHARE a
blow-up variable, and this sharing changes the RLCT (exact witness:
$\langle\delta x,\delta y\rangle$ has $\mathrm{rlct}=1/2$ vs $\langle\delta_1 x,\delta_2 y\rangle$ has
$\mathrm{rlct}=1$ — identical "threshold-only" summaries, different value). So a Lean carrier that
flattens the sharing to a per-row multiplicity is provably unfaithful. The binding witness is
$M=(3,3,4)$, branch $t=(1,0)$: $\mathrm{Mval}=8$, layer-1 corank $(2,2)$, $\mathrm{rlct}=4$; the clean
(corank $\le 1$) branches give $9,12 > 8$, so the coupled branch binds.

## The current Lean carrier (per-node data of the recursion)

The tree node (`StepData`) already carries, as TYPED fields:
- `divProfile : Fin numDiv → (Fin L → ℕ)` — the full rank-pattern vector $T_{s,k}$ per divisor
  (primitive). `divTilde k := min (divProfile k)` is derived.
- `divExp : Fin numDiv → ℕ` — the Jacobian exponent $M_{s,k}$ per divisor.
- `bExp : Fin numB → (Fin numDiv → ℕ)` with `bChain : Monotone bExp` — the diagonal monomial vector
  ($b_i$'s exponent over the divisor variables), typed monotone (divisibility chain).
- `numGen : ℕ`, `genDivExp : Fin numGen → Fin numDiv → ℕ` — "the exponent of divisor $k$ in
  generator $g$"; `support g := {k | genDivExp g k ≠ 0}`.

The per-step transition `stepUpdate` (cases: case-1(1) exponent-merge, case-1(2) new pivot,
case-2 full-block new pivot, rollover layer-advance) currently propagates `numDiv/divExp/divProfile/
cleared` faithfully but does NOT propagate `genDivExp` (it was deferred — "support propagation across
the per-divisor re-indexing balloons"). The task ("R4") is to design the `genDivExp`/support
propagation and prove it is maintained by every `stepUpdate` case.

## The questions (re-derive independently; give exact reasoning)

1. In the invariant above, express $b_i$ as an explicit product of the $u_{s,k}$ (solve the
   recursion). Which $u_{s,k}$ divide $b_i$? Give the condition in terms of $\tilde t_{s,k}$ and $i$.

2. The loss generators are the entries of $\operatorname{diag}(b)\,[E_J\mid D_J]\prod_{s>S}C^{(s)}$.
   A generator sitting in matrix-row $i$ — what is its divisor content (which $u_{s,k}$ divide it,
   with what multiplicity)? Does it depend on the column, or only on the row $i$?

3. Given the answers to 1–2: is the field `genDivExp` (generator→divisor multiplicity) INDEPENDENT
   data that must be transported across the per-divisor re-indexing, or is it a DERIVED function of
   `divProfile` (via `divTilde`) plus the structural row-index? State precisely what determines the
   full sharing pattern (which divisors are shared across the corank-$\ge2$ block).

4. If it is derived: what is the exact formula for `support` of a residual-block generator, and does
   deriving it (rather than transporting a `Finset`) LOSE any information that the
   $\langle\delta x,\delta y\rangle$ vs $\langle\delta_1 x,\delta_2 y\rangle$ distinction needs? i.e.
   can `divProfile`/`divTilde` distinguish "one divisor shared across two rows" from "two divisors,
   one per row"?

5. Trace $M=(3,3,4)$, branch $t=(1,0)$ (clear one pivot in layer 1, leaving a $2\times2$ residual;
   then resolve). What is the $b$-chain at the terminal leaf, which divisors are shared across the
   $2\times2$ block, and does the sharing pattern follow your formula from 3–4? Confirm $\mathrm{rlct}=4$.

6. KILL-CONDITION: describe a concrete configuration (if any) where the sharing pattern is NOT
   recoverable from `divProfile`/`divTilde` + row-index — i.e. two distinct resolutions with
   identical `divProfile` ledgers but different generator-sharing (hence different RLCT). If none
   exists, argue why `divProfile` is a complete invariant for the sharing.

Give a crisp verdict on Q3 and Q6 specifically: should the Lean build carry `genDivExp` as
independent transported data, or derive support from `divProfile`?
