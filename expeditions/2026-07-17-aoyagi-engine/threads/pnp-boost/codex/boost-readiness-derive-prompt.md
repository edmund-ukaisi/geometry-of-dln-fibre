# Consult: is a "smaller-center degree-1 support" property of Aoyagi's fold residual DERIVABLE from a "full-block degree-1 support" invariant, or does it need the b-chain history?

## Contract
Adjudicate ONE truth-value, in one direction, with a mechanism:

> **Q.** Let `R = (R_ij)` be the generator family of Aoyagi's DLN product-ideal resolution at a node
> that sits at the START of a layer (all pivots of that layer still uncleared, `J = 0`), and is about to
> undergo a **Case-1(1) boost** (reuse of a divisor born at an EARLIER layer). Is the property
>
>   (P) "`R` is degree-1 supported on the SMALL set `Csmall = {pivot} ∪ (partial block)`
>        — every monomial of every `R_ij` carries EXACTLY ONE `Csmall`-factor, and its cofactor is
>        `Csmall`-independent"
>
> DERIVABLE from the property
>
>   (Q) "`R` is degree-1 supported on the LARGER set `Cfull` = the full current-layer residual block
>        (`pivot ∉ Cfull`; `partial block ⊊ Cfull`) — each `R_ij = Σ_{c ∈ Cfull} a_c · c` with `a_c`
>        continuous, plus a per-layer total-degree ≤ 1 grade"
>
> alone (i.e. from the abstract shape of `R` as a `Cfull`-linear form with continuous coefficients)?
> Or does (P) require extra structural information about `R` that (Q) does not encode — and if so, WHAT
> is that information, stated as sharply as you can?

Answer with: VERDICT (derivable-from-(Q) / needs-extra-structure / false-as-stated), the precise
mechanism or the precise obstruction, and — if extra structure is needed — its sharpest statement and
whether it is a genuine feature of Aoyagi's construction or an artefact of the encoding.

## Setup (exact, self-contained)

Aoyagi resolves the ideal `⟨entries of C^(1) C^(2) … C^(N)⟩` (a product of layer matrices, `C^(s)` of
size `d_s × d_{s-1}`) by an (S,J) recursion. At each node the standing invariant is

  `⟨∏ C⟩ = ⟨ diag(b_1, …, b_{M(S)}) · [[E_J, O],[O, D_J]] · ∏_{s>S} C^(s) ⟩`

where:
- `S` = current layer, `J` = number of pivots cleared in it so far.
- `b = (b_1, …, b_{M(S)})` is the **b-chain**: each `b_i` is a MONOMIAL in the exceptional (blow-up)
  coordinates `u_{s,k}`, defined by `b_i = ∏_{ t̃_{s,k} < i } u_{s,k}`. Consequence: `b_1 | b_2 | … |
  b_{M(S)}` (a divisibility chain). `M(S)` is a running-min width.
- `D_J` is the residual block (rows `J+1..M(S)`, cols `J+1..M^(S+1)`), whose entries are treated as
  FRESH degree-1 coordinates; `E_J` is the cleared-pivot head (`J×J` identity block).
- `∏_{s>S} C^(s)` are the untouched deeper-layer matrices (fresh independent coordinates).

The generator family `R` at the node = the entries of the matrix
`G = diag(b) · [[E_J,O],[O,D_J]] · ∏_{s>S} C^(s)` (a `d_N × d_0` matrix; `R_ij = G_ij`).

**The node of interest:** `J = 0`, and the equal-run classifier finds a jump at run-length `J_1` fed by a
divisor `u_p` (born at an EARLIER layer `S' < S`) with `t̃_{u_p} = J_1`. So `b_1 = … = b_{J_1}` and
`b_{J_1+1} = u_p · b_{J_1}` (the pivot coordinate `u_p` first enters the chain at index `J_1+1`).

- `pivot = u_p` (the reused earlier-layer exceptional coordinate; `u_p ∉ D_J`, `u_p ∉` any layer block).
- `partial block` = the residual-block entries in the DOMINANT rows `1..J_1` (b-value `b_1..b_{J_1}`,
  i.e. the rows whose b does NOT yet contain `u_p`).
- `Cfull` = ALL residual-block entries (`D_0`), rows `1..M(S)`.
- `Csmall = {u_p} ∪ (partial block)`.

## The concrete instances (please reason on these, exact algebra)

- `d = (2,2,2,2)`, N=3. Boost node at layer S=2, J=0. b-chain `(b_1,b_2) = (u_{1,1}, u_{1,1}·u_{1,2})`,
  `u_p = u_{1,2}` (born layer 1), `J_1 = 1`. Residual `D_0` = 2×2, deeper layer `C^(3)` = 2×2.
- `d = (3,3,2,2)`, N=3. Two successive boost nodes at layer S=2, J=0 (reuse `u_{1,2}` then `u_{1,3}`),
  b-chain `(u_{1,1}, u_{1,1}u_{1,2}, u_{1,1}u_{1,2}u_{1,3})` with a running-min shrink at the S=2→3
  rollover (`M` drops 3→2). Residual `D_0` = 3×2 (or 2×2 after the shrink); deeper layer `C^(3)`.

## What I have established (facts — build on these, don't re-derive)

- The b-chain divisibility `b_1 | … | b_{M(S)}` holds by construction (`b_i = ∏_{t̃<i} u`).
- The rows `1..J_1` have b-value NOT divisible by `u_p`; rows `>J_1` have b-value divisible by `u_p`
  (since `u_p` enters at index `J_1+1`), with cofactor `b_i / b_{J_1+1}` also a monomial (chain).
- The residual-block coordinates `D_0[i][k]` and deeper-layer coordinates `C^(s>S)[k][j]` are
  independent of the exceptional coordinates `u_{s,k}` (they live in disjoint coordinate axes).
- The abstract invariant (Q) is what a Lean formalisation carries between fold steps: it says `R_ij` is a
  `Cfull`-linear form `Σ_{c∈Cfull} a_c c` with `a_c` continuous, PLUS a per-layer degree ≤ 1 grade. It
  does NOT say anything about the `a_c` beyond continuity + that grade.

## Questions
1. Compute `G_ij` in the two instances and decide whether (P) holds for the ACTUAL `G`. If it holds, by
   what mechanism does each monomial acquire exactly one `Csmall`-factor — separately for (a) the
   dominant rows `1..J_1` and (b) the rows `> J_1`?
2. Does (P) FOLLOW from (Q) for an ARBITRARY `R` satisfying (Q)? If not, exhibit the sharpest witness
   `R` that satisfies (Q) but violates (P), and name exactly the extra structural fact about the ACTUAL
   `G` that (Q) fails to encode.
3. If extra structure is needed, is it a genuine feature of Aoyagi's construction (so a Lean proof must
   CARRY it as an invariant conjunct or pin it via the construction's provenance), or is it recoverable
   from (Q) plus generic facts (continuity, the layer/exceptional axis disjointness) alone?
4. Any subtlety specific to the running-min shrink in `(3,3,2,2)` (the deeper node, reuse of `u_{1,3}`)
   that changes the answer relative to `(2,2,2,2)`?
