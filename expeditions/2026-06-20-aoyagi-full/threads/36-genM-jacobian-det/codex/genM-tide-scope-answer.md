**Verdict**

Full `nodeChartGeneral M` is not one-tide scope. The one-tide win is to land the rate/unit side plus corrected decoder/factor definitions and anchor-specialization checks. The bridge + `cov` is the multi-tide wall.

**Q1**

Yes: `Ufun := VvalGen (x p) M (tStar M) (B_det M x) hle` is the right way to avoid re-deriving explicit `Hval`/`Uval` for the **rate and leaf-integrand** fields.

Lean route:

```lean
hrate :
  routeMCore M (phiGen (x p) M t (B_det x) hle)
    = (x p)^2 * VvalGen (x p) M t (B_det x) hle

leaf_integrand := leaf_integrand_of_rate ... hrate VvalGen_nonneg
```

That is already architecturally banked in [RouteMGenLeafIntegrand.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:30) and [RouteMGenChartId.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenChartId.lean:136).

But `Ubound` is not free. You still need:

- `Measurable/Continuous` of this `VvalGen` as a function of `x`.
- `0 < VvalGen ...` a.e. on boxes.

The existing anchors do not prove positivity from “full-rank decoder”; they prove a concrete nonzero polynomial unit and apply polynomial zero-set nullity. General `VvalGen` positivity will need the same kind of parametric nonzero-polynomial witness. Full-rank of the chart Jacobian does not by itself imply `HrGen ≠ 0` a.e.

And no: this does not avoid `cov`. The `cov` field in [NodeAchieverChart.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/NodeAchieverChart.lean:92) still needs the genuine Jacobian and injectivity/slice-null bookkeeping.

**Q2**

The bridge is not one-tide tractable for arbitrary `M`.

The anchor bridges are valuable evidence, but they close after fixing concrete widths and explicit matrices. The general bridge has to align:

- the recursive `C_{s+1}` in `chartParamsGen`,
- the factor-prefix output of `T_M`,
- `chainA_apply_castAdd` / `chainA_apply_natAdd`,
- opaque `Text`/`Wext` casts,
- and the Aoyagi active residual blocks, not the old chain `E`-slot count.

The most likely stall is the kept-row layer equality:

```lean
A_s kept row = C_{s+1} - N_s * W_s
```

after transporting the row index through `Fin.cast`, `castAdd`, `natAdd`, and `finCongr`. This exact cast kernel already appeared in the concrete bridges; generalizing it while also matching the recursive `C` prefix is the hard part.

Also, determinant is not the whole `cov`: after `|det Dφ| = ∏ |u_j|^leafH j`, you still need `InjOn` off the full determinant-zero union and null-slice add-back, as in `phi222_cov` and `phi3333_cov`.

**Q3**

Pick option **(a')**, not full (a):

Land definitions and rate-side facts, but do not promise `cov` or full `nodeChartGeneral`.

Best one-tide checkpoint:

- Define the corrected `B_det`/factor-chart data, active set, pivot, `leafH`.
- Prove `active.card = minAdm M` and `leafH p = minAdm M - 1`.
- Prove `hC0_det`, then get the rate by `routeMCore_phiGen`.
- Prove the generic `leaf_integrand` from `VvalGen`.
- Specialize-check against `(2,2,2)` and `(3,3,3,3)` using explicit `tach222`/`tach3333`, not definitional reduction of `tStar M` to those paths.

Do not set the checkpoint as “full-rank off `{x_p = 0}`”. The anchors have extra spectator determinant axes (`x4`, `x1`, `x9`, etc.). The correct target is full-rank/injectivity off the full zero-union, then add null slices back in `cov`.

`B_det M` itself is only a contained sub-tide if scoped as definitions plus `hC0`/rate. A full-rank proof and anchor-reduction proof are not contained. Even defining the right parametric decoder forces the Schur/LDU structure: the anchors’ polynomial entries are not arbitrary tables, but the parametric implementation must generate them via the LDU/Schur factor maps, not by a tiny `Rfin` patch.

**Q4**

Do not make `B_det M` a small edit of `genBlkFlatStruct`.

`genBlkFlatStruct` is rate scaffolding. It has `Rfin := fun _ => 0` in [RouteMGenFlatStruct.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenFlatStruct.lean:150), so it has dead leaf slots and cannot be the determinant chart. Reuse its ideas and `hC0` proof pattern, not the decoder as the target.

A correct live decoder/factor chart must encode:

- one chosen active residual normal as the pivot/fixed-`1` entry;
- the flat coordinate `x_p` is used only as the radial scalar;
- every other active normal is an angular coordinate multiplied by `x_p`;
- active residuals can live in interior `Rmat s` blocks or in terminal `Rfin L`;
- `Bmat 0 = I` and `Rmat 0 = 0` remain unchanged, so `hC0` still holds.

So the live `Rfin` is not “just nonzero”. It must participate in a global one-pivot blow-up of the `minAdm` Aoyagi residual normals. If the chosen active block is terminal, `Rfin L` contains the fixed `1` plus angular entries; if the pivot is interior, the fixed `1` is in the corresponding `Rmat s`, while `Rfin` still must not leave terminal active slots dead.

**Scope Ranking**

1. One tide: `Ufun := VvalGen`, `leaf_integrand`, `hC0_det`, active-card/leafH definitions.
2. Maybe one tide: define a fresh `B_det`/factor API and specialize smoke tests.
3. Not one tide: full parametric bridge `chartParamsGen = pack_M ∘ T_M`.
4. Not one tide: `cov` + `nodeChartGeneral` + `routeMCore_box_diverges_achiever` ∀M.
