# Pen-and-paper reproduction - Lemma 5 equation (4) terminal endpoint boundary

Status: checked conditional endpoint bookkeeping; source realisation remains
blocked.

This note records a narrow endpoint fact around Aoyagi Lemma 5 equation `(4)`.
It does not prove that equation `(4)` constructs a terminal variable.

## Source Audit

Aoyagi Lemma 5 displays equation `(4)` and then says that equations `(3)` and
`(4)` are used in Case 1(2) to construct the blow-up process.  The printed text
does not specify:

- the finite sequence of Case 1(2) charts;
- the proof that the Case 1 gap hypothesis holds at each step;
- the treatment of the terminal selected endpoint `S_(ell+1)-1`;
- the proof that the displayed vector has `tilde t_{s,k}=0`.

Thus full displayed-vector realisation remains a source/API gap.  Any theorem
about the terminal endpoint must keep the endpoint assignment as supplied data.

## Finite Endpoint Facts

The displayed lower and upper `Htilde` chains share the terminal value

```text
Htilde_ell = Htilde'_ell = 0
```

under Definition 3's selected-sum identity

```text
sum_i W_i = ell*(M-1)+a.
```

The existing chain-level theorem is indexed by `Fin.last ell`; the new
Nat-indexed wrappers expose the same fact as

```text
aoyagiHtildeLowerNat ell a M m ell = 0,
aoyagiHtildeUpperNat ell a M m ell = 0.
```

The selected blocks cover only

```text
S_1-1 <= S < S_(ell+1)-1.
```

Therefore the terminal endpoint `S_(ell+1)-1` is not in a selected block.

## Conditional Equation `(4)` Endpoint Boundary

If a future source convention or supplied displayed-vector record gives the
terminal selected endpoint the upper terminal value,

```text
T(S_(ell+1)-1) = Htilde'_ell,
```

then the selected-sum identity implies

```text
T(S_(ell+1)-1) = 0.
```

This is only an endpoint consequence of a supplied assignment.

## Lean Targets

```text
aoyagiHtildeLowerNat_last_eq_zero_of_selectedSum
aoyagiHtildeUpperNat_last_eq_zero_of_selectedSum
AoyagiSelectedCutpoints.not_block_terminalEndpoint
aoyagiLemma5Eq4_prefix_leftEndpoint
aoyagiLemma5Eq4_middle_leftEndpoint
aoyagiLemma5Eq4_tail_leftEndpoint_of_cutoff_lt
aoyagiLemma5Eq4_terminalEndpoint_zero_of_upperNatExtension
```

## Nonclaims

- No construction or existence theorem for equation `(4)`'s displayed vector.
- No proof of terminal `tilde t=0`.
- No vector admissibility or source vector-to-chain correspondence.
- No Case 1(2) chart sequence, chart coverage, Lemma 5 order count, pole
  order, normal crossings, or RLCT extraction.
