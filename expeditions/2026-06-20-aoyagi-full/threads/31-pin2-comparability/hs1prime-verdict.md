# hS1' adjudication — VERDICT: FALSE (pivot-column permutation on the deviation)

`DeepestGaugeConstruction.lean:~1891`, `hS1' : ∀ w, F w (lastLayer hL) = Pf last · (A w) last · Qf last`
where `F w = framedParamsPivot … (split w)`, `A w = (paramsEquivFlat H).symm w`, `split w = deepestSplit w0 w`.

## Verdict
**hS1' is FALSE as stated** (high confidence; exact index algebra + two independent numeric checks +
decorrelated Codex xhigh, all aligned). It is true only when `J` is the front pivot (`J = castLE`,
`pivotThresholdSplit = rThresholdSplit`); the bundle's `J` is `B`'s pivot set and may permute.

## The mechanism
`framedParamsPivot_last` reindexes with the THRESHOLD row split `eR` and the PIVOT column split
`eCpiv = (pivotThresholdSplit r (H last.succ) (pivotJSucc J)).symm`:

    F_last = reindex eR eCpiv (fromBlocks 1 0 0 0)
           + Pf_last · reindex eR eCpiv (fromBlocks readX readY readZ coreRead) · Qf_last.

`reindex eR eCpiv M (i,j) = M (rThr i) (pivotThr J · j)`. The reads are **J-independent threshold-column
decodes** (`reindex_fromBlocks_reads_eq_deviation`, `readY/readT_deepestSplit_raw`): block col `inl q ↦`
deviation col `q`, `inr q ↦` deviation col `r+q`. So the reads term equals the deviation `Mdev :=
(symm(w−w0)) last` with columns permuted by

    π_J(j) := (rThresholdSplit r b).symm ((pivotThresholdSplit r b J) j),   colPerm_J(Mdev) i j = Mdev i (π_J j),

NOT `Mdev` itself. The corner term is calibrated by `hcorner` (last-layer, pivot split) to
`deepest_last · Qf_last` (with `Pf_last = 1`). Hence

    F_last = deepest_last·Qf_last + Pf_last·colPerm_J(Mdev)·Qf_last,
    target = (deepest_last + Mdev)·Qf_last        (since (symm w) last = deepest_last + Mdev).

`F_last = target ⟺ colPerm_J(Mdev) = Mdev ⟺ π_J = id ⟺ J front-pivot`. The non-last normal-form `hNF`
is **explicitly restricted to `s+1 ≠ L`**, so the threshold-corner route used for `hS1` (the non-last
layers) does not cover the last layer — by design the last layer is the pivot one.

## Smallest counterexample
`L=2`, `H=(1,1,2)` → last layer width: `a = H_last.castSucc = 1`, `b = H_last.succ = 2`, `r = 1`,
`J 0 = 1` (pivot column = col 1, not col 0). `π_J = [1,0]` (swap the two columns). With `Pf_last = I`,
`Qf_last = I`, generic deviation `Mdev = [x y]`: `F_last = deepest + [y x]` but `target = deepest + [x y]`;
they differ by `[y−x, x−y] ≠ 0`. (Numeric: `max|F−target| = 2.73`.) Codex's independent counterexample
(`r=1, a=2, b=2, J 0 = 1`, reads term `[[y x],[t z]]` vs target `[[x y],[z t]]`) is identical in structure.

## Correct statement of hS1' (asymmetric — NOT a clean column-permutation of the whole target)
`deepest_last` enters un-permuted (via the corner); only the deviation is permuted:

    F w (lastLayer) = Pf last · (deepestPoint … last) · Qf last
                    + Pf last · colPerm_J ((symm(w−w0)) last) · Qf last

i.e. `F_last ≠ Pf · colPerm_J((symm w) last) · Qf` either (checked: `max|F − cleanperm| = 0.91 ≠ 0`).

## Consequence for the downstream telescope (hframe → hS2 → hS3b)
`hframe`/`hS2` feed `prod H (F w) = P0 · prod H (A w) · QL` to `endpoint_telescoping_eq`. With hS1'
false, `prod H (F w)` is NOT `P0 · prod(symm w) · QL`; the last factor carries the column-permutation π_J.
**hS3b is unaffected** at the deepest point: there `split w0 = 0`, `Mdev = 0`, so `colPerm_J(0) = 0` and
`F w0 = framedParamsRegPivot 0` (the pivot corner) — the verification at the basepoint is exactly the
permuted-deviation-vanishes case, which `reindex_prodAux_framedParamsRegPivot_zero` already lands. The
problem is for `w ≠ w0` (the loss/energy identity `hS2`, conjunct (a)).

## The fix (two options, for the controller/formaliser)
- (A) Carry the permutation explicitly: telescope to `P0 · prod(A' w) · QL` where `A' w` is `A w` with the
  last layer's columns permuted by `π_J`, then absorb `π_J` into `QL`/`B`-normalization (it is an
  orthogonal column permutation `Pπ`, `colPerm_J(M) = M·Pπ`, so `colPerm_J(M)·Qf = M·(Pπ·Qf)` — fold
  `Pπ` into the endpoint `QL` and into the `B`-pivot reindex; the outer `reindex(rThr, pivotThr J)` on
  the loss side `Sreg` may already absorb it, since BOTH `deepestEFull` and the loss use the SAME outer
  `reindex(rThr, pivotThr J)`).
- (B) Make the reads pivot-aware (option β of `framedbody-cert.md`): use a pivot-column variant of the
  `readY/readT` decode whose RHS reads the pivot column `(pivotSupport)ᶜ.orderEmbOfFin q` directly, so the
  reads term reconstructs the un-permuted `Mdev`. This requires `deepestSplit`'s last-layer gauge slots to
  be encoded at pivot role-indices — they are NOT (the gauge reads are J-independent, by construction), so
  (B) means changing `deepestSplit` itself or adding a relabel; heavier than (A).

**Recommendation:** (A). The π_J permutation is an orthogonal `Pπ` that should cancel against the SAME
outer `reindex(rThr, pivotThr J)` already applied on both the energy (`deepestEFull`) and loss (`Sreg`)
sides — verify that cancellation before re-stating hS1'. The cert's option-α premise ("the role index of
a column is split-independent, so the two decoders agree on the per-entry value") is the error: the reads
ARE split-independent (threshold), but `framedParamsPivot_last` PLACES them at pivot columns, so the
per-entry value lands at a permuted column.
