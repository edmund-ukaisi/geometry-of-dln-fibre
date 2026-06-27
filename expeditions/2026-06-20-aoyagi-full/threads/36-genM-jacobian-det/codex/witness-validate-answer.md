**Q1:** Yes, `q = max { k <= L : Text_k > 0 }` is well-defined because the set is finite and contains `0`: `Text_0 = M_0 >= 1`.

`q >= 1` does **not** follow from `Text_0 >= 1` alone. It follows only if your admissibility condition `minAdm >= 1` really guarantees `Text_1 >= 1`. If `Text_1` may be `0`, then `q = 0` is possible.

If `q = 0`, the same dead-leaf construction still works algebraically, provided `Rmat_0` is an allowed residual block: inject at boundary `0`, use carriers `W_0 ... W_{L-1}`, and there is no upward `Bmat` propagation step.

**Q2:** Yes. In the `q < L` case, deepest positivity gives `Text_q > 0` and `Text_{q+1} = 0`. Therefore

```text
r_q = Text_q - Text_{q+1} = Text_q >= 1
c_q = M_q - Text_{q+1} = M_q >= 1
```

assuming genuine positive widths. So the deepest E-block exists and has a valid pivot slot.

**Q3:** The carrier mechanism is correct. For every `k >= q` in the dead-leaf case, `Text_{k+1} = 0`, so the “kept” top of

```text
A_k = [ C_{k+1} - N_k W_k ; W_k ]
```

is row-empty, hence

```text
A_k = W_k.
```

Thus

```text
suffix_q = W_q W_{q+1} ... W_{L-1}.
```

If you set one carrier entry in each `W_k`, then the selected suffix entry is exactly the product of those carrier entries. At boundary `q`,

```text
H_q = Rmat_q suffix_q
```

because `Bmat_q H_{q+1}` is zero/empty. Above `q`, the kept diagonal entries of `Bmat_k` copy the live row upward to `Hmat_0`.

No carrier break occurs as long as all widths `M_k >= 1`: in this regime `W_k` has size

```text
c_k x M_{k+1} = M_k x M_{k+1},
```

so each carrier matrix has at least one usable entry.

**Q4:** I see no algebraic hole under the stated positive-width/admissible-rank assumptions. In the live-leaf case, only the leaf pivot survives and the `Bmat` diagonal propagates it upward. In the dead-leaf case, only the deepest `E` pivot times the carrier suffix survives.

There is no cancellation at the witness point because all nonessential coordinates are set to zero. The target entry has a single surviving monomial:

```text
e
```

in the live-leaf case, or

```text
e * w_q * ... * w_{L-1}
```

in the dead-leaf case.

**Q5:** This is **not** a research wall. It is bounded dependent-width engineering: a uniform two-case witness plus a straightforward downward suffix induction. The only real edge condition is bookkeeping: either ensure `q >= 1` from `minAdm >= 1`, or explicitly allow the same construction at `q = 0` using `Rmat_0`.