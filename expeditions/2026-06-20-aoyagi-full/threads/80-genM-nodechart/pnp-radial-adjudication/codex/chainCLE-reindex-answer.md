**Q1**

Verdict: `C_{s+1}` lives in the **kept-row block of layer `s`**, not in a separate “next-boundary” flat slot.

“Built from boundary `s+1`” describes provenance. The flat coordinate that the chain factor reads and overwrites is the first `Text_{s+1}` rows of layer `s`, because

```lean
A_s = [ C_{s+1} - N_s * W_s
      ; W_s ]
```

puts `C_{s+1} - N_s W_s` exactly in layer `s` kept rows.

Let

```lean
B_s   := Wext_s * Wext_{s+1}
off_s := ∑ j < s, Wext_j * Wext_{j+1}
hrow_s : Text_{s+1} + c_s = Wext_s
```

and assume row-major flattening inside each layer:

```lean
lin_s (r : Fin Wext_s) (j : Fin Wext_{s+1}) :
  Fin (Wext_s * Wext_{s+1})
```

with value

```lean
r.val * Wext_{s+1} + j.val
```

Then the C-block coordinate map is:

```lean
rowC_s (i : Fin Text_{s+1}) : Fin Wext_s :=
  Fin.cast hrow_s (Fin.castAdd c_s i)

CIdx_s (i : Fin Text_{s+1}) (j : Fin Wext_{s+1}) : Fin N :=
  flatIdx_s (rowC_s i) j
```

Equivalently, by values:

```lean
CIdx_s i j =
  ⟨ off_s + i.val * Wext_{s+1} + j.val, proof ⟩
```

where the proof is the layer-packing bound into `Fin N`.

For comparison, the lift/W block is:

```lean
rowW_s (a : Fin c_s) : Fin Wext_s :=
  Fin.cast hrow_s (Fin.natAdd Text_{s+1} a)

WIdx_s (a : Fin c_s) (j : Fin Wext_{s+1}) : Fin N :=
  flatIdx_s (rowW_s a) j
```

with value

```lean
off_s + (Text_{s+1} + a.val) * Wext_{s+1} + j.val
```

So for `E_chain_s`:

```lean
(E_chain_s x).W a j = x (WIdx_s a j)
(E_chain_s x).C i j = x (CIdx_s i j)
```

Proof-level: this follows directly from the banked row laws `chainA_apply_castAdd` and `chainA_apply_natAdd`.

**Q2**

Yes: the chain CLE is derived from the **flat layer/output coordinatization**: layer `s`, split by kept rows and lift rows.

That can differ from the per-boundary chart-role coordinatization used by `schur_s` or `ldu_s`. This does **not** by itself break `composeFold`. A `composeFold` over `R^N → R^N` only needs every factor to be a self-map of the same ambient space. Each factor may have its own CLE:

```lean
factor_s = E_s.symm ∘ (factorMap_s × id) ∘ E_s
```

The determinant argument is still sound factorwise: conjugation by each `E_s` cancels inside that factor’s determinant computation, and the global determinant uses the chain rule over the composed self-maps.

Soundness risk: do not silently treat all factors as sharing one product decomposition. If a proof identifies “boundary `s+1` C-slot” with “layer `s` kept rows” merely by name, that is unsafe. The equality must come from the actual recursive construction showing that, at the moment `chain_s` runs, the values produced by deeper boundary data occupy the layer-`s` kept-row coordinates.

**Q3**

Uniform fold. No separate leaf reindex branch is needed.

For `s = L - 1`, the same rule says:

```lean
C_L lives in the kept rows of layer L-1.
```

If `Text_L > 0`, those kept rows contain the live leaf block `u · Rfin`.

If `Text_L = 0`, then

```lean
Fin Text_L = Fin 0
```

so the C-block has no coordinates. The kept-row map is vacuous, `chainA_apply_castAdd` has no cases, and `chainA_apply_natAdd` covers the whole layer as lift rows. This is a degenerate-but-uniform case, not a different indexing regime.

Proof-level: the same `rowC_s := cast hrow_s (castAdd c_s i)` formula applies for all `s`; at `Text_L = 0` it has no inhabitants.