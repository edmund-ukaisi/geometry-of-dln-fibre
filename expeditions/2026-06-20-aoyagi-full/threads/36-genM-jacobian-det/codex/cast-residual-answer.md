`rfl` fails because the pretty-printer hides coercions. One side is applying `P` through an index transported along the `chainA_apply_castAdd` path, essentially a `Fin.cast`/`finCongr` path from `Fin (Wext M222 0)` or `Fin (Wext M222 (0+1))` to `Fin 2`; the other side is the raw matrix application. These transports preserve `.val`, but they are not definitionally the same term, so `rw`’s final reflexivity check misses.

Use this closer first:

```lean
  simpa only [Fin.cast_eq_self]
```

If a hidden `finCongr`/`reindex` is still present, use the repo’s checked pattern:

```lean
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    finCongr_symm, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  rfl
```

I would not use `fin_cases` as the main proof; it works by enumerating `Fin 2`, but it is the wrong abstraction and will get worse in layer 1. For the layer-1 kept/lift rows, do the same thing after `chainA_apply_castAdd` or `chainA_apply_natAdd`: normalize the row transport with the same `simp only [...]`, then close by `rfl`.