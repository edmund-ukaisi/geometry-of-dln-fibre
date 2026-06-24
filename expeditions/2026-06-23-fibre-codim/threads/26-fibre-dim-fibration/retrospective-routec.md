# Thread 26 (route-c pivot) — retrospective + banked state

The H4 tide pivoted to **route c (the equivariant homogeneous sweep)** after route B (Jacobian) was
certified circular (thread 27) and the original fibration-via-trdeg route's closed-fibre step was
walled (my Step-realization consult). Route c proves `codim(fibre B) = C + δ` for all rank-`r` `B`,
flatness-free, via orbit dimension. This records what landed.

## Banked (committed/pushed, whole library green, sorries 0, axiom-clean `[propext, Classical.choice, Quot.sound]`)

### `Core.EndBaseChangeSweep` — the reachable sweep STRUCTURE `Σ^r = H·F`
- `rank_endpoint_conj` — `rank (P_N · B · P_0⁻¹) = rank B` (endpoint units preserve rank;
  `rank_mul_eq_left/right_of_isUnit_det`).
- `mem_productRankLocus_iff_mem_sweep` / `productRankLocus_eq_iUnion_smul_fibre` — **`Σ^r = ⋃_P (P•·)''
  (fibre E)`**: the exact-rank locus is the `H`-sweep of one fibre (`exists_baseChange_of_rank_eq` +
  `image_smul_fibre`).
- `codimRepCanonical_fibre_translate_eq` — every `H`-translate of `fibre E` has the same codim (G1).

### `Core.RouteCAssembly` — the additive assembly to `codim F = C+δ` (conditional)
`codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep [IsAlgClosed][CharZero]`: for a rank-`r` `B`,
`codimRepCanonical (fibre d B) = (cCodim d r).toNat + r(d_N+d_0−r)`, carrying as **explicit named
hypotheses**:
- **`hSweep`** : `varietyDim Σ^r = δ + varietyDim F` — the one genuinely-hard orbit-dimension rung
  (the `+δ` is isolated to exactly here). Under scout adjudication (build via `OrbitPullbackDim` vs
  name as Cited).
- **`hClosure`** : `varietyDim Σ^r = varietyDim Σ̄^r` — the Cited density bridge (LR 4.4/4.5).
- **`hCatFibre` / `hCatSigma`** : `codimRepCanonical Z + varietyDim Z = card` for `Z = F`, `Σ̄^r` — the
  *soft* reducible-locus catenary (true for any nonempty subset of affine space over an alg-closed
  field; `codim = min`, `dim = max`, dual under the per-prime catenary). Dischargeable as general
  bedrock (`ringKrullDim(R/I) = Order.krullDim(zeroLocus I) = ⨆ coheight` + per-prime catenary +
  min/max) — a multi-lemma sub-build, named here rather than ground out.

The proof is the purely-additive chain `C + δ + dim F = C + dim Σ̄^r = card = codim F + dim F`,
left-cancelling the finite `dim F`. Uses LANDED `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`
(`codim Σ̄^r = C`, Brick A).

## Status of `BundleShiftInterface`
**NOT discharged.** The headline `codim F = C+δ` is conditional on `hSweep` (hard) + `hClosure` (Cited)
+ `hCat*` (soft). When `hSweep` lands (scout greenlight) + the soft catenary is discharged, the
assembly closes unconditionally for all rank-`r` `B` (via G1), and a thin DLN tide discharges
`BundleShiftInterface.cited_bundle_shift`. Nothing is named to overclaim.

## The route map (for the record)
- Route A (flatness/determinantal-presentation): walled (threads 09/14/20).
- Route B (Jacobian rank ≥ C+δ): CIRCULAR (thread 27 — `rank = card − dim` identity at smooth pts;
  `+C` has no independent structural source; uniform `rank ≥ C+δ` false at singular pts).
- Route c (homogeneous sweep): the path. Reachable structure + assembly banked; `+δ` isolated to
  `hSweep`. Scout adjudicating whether `hSweep` builds from `OrbitPullbackDim` or stays Cited.

## Process note (lessons.md item E)
The whole-library build briefly carried 1 sorry from thread 28's (`tide-routec-sweep`, shut down
mid-SPECIFY) untracked `RouteCAssembly.lean`. Detected via `scripts/sorries`; resolved by
**adopting + completing** thread 28's good skeleton (not deleting it) as sole route-c write-tide, and
removing my redundant `FibreCodimSweepAssembly`. Zero work lost; branch clean + green.
