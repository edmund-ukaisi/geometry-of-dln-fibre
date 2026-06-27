Based on the settled facts you gave, the build-ready route is **2a**.

**Q1 Route Rank**
1. **2a: lands with least risk.**
   - **FACT:** `routeMCore_phiGen` is decoder-agnostic in `B : GenBlk M t`.
   - **FACT:** therefore the rate does not require `phi_det = phiFlatStructV`.
   - **INFERENCE:** define the determinant chart as `phiGen (x p) M t (B_det x) hle`, where `B_det` is the full-rank decoder matching the determinant factorization. Then rate is just:
     ```lean
     simpa [phi_det] using
       routeMCore_phiGen (u := x p) (M := M) (t := t)
         (B := B_det x) hle (hC0_det x)
     ```
   - This avoids the failed role-slot/raw-Params bridge and avoids a new telescope.

2. **A-revisited: second, only if it collapses into 2a.**
   - **FACT:** modifying `genBlkFlatStruct` and rechecking `hC0` would still let the banked rate theorem apply.
   - **INFERENCE:** a “single decoder edit” is not enough to guarantee the determinant unless the edited decoder is exactly the full-rank factored decoder. If so, it is basically 2a under the old name.
   - Direct Jacobian computation on a patched legacy `phiFlatStructV` is higher risk than defining a fresh `B_det`.

3. **2b: reject.**
   - **FACT:** current `phiFlatStructV` has identically zero Jacobian.
   - **FACT:** the desired chart has determinant generically `|x_p|^(m-1) * spectators`.
   - So `phi_det = phiFlatStructV` is not merely hard; for the current decoder it is false. The historical funext failure just confirms this should not be pursued.

**Q2 Chosen Construction**
Use canonical `FlatIdx` order. Define:
```lean
active : Finset (Fin N)
active := Finset.univ.filter fun q =>
  isAoyagiResidualSlot M t (decodeFlatIdx q)

p : Fin N
p := chosenPivotResidualSlot M t

have hp : p ∈ active := ...
have hcard : active.card = minAdm M := ...
```

Define the chart:
```lean
def phi_det (x : Fin N → R) : Fin N → R :=
  phiGen (x p) M t (B_det x) hle
```

`B_det x` is the full-rank decoder:

- decoded in canonical `FlatIdx` order;
- pivot active residual slot is stored as fixed `1`;
- radial scalar is supplied separately as `u = x p`;
- every other active residual slot stores the corresponding Schur coordinate, so `chartParamsGen` produces `u * β`;
- spectator Schur slots are copied through the `b = aβ` layer-op decoder;
- terminal `Rfin` is nonzero, with the fixed-`1` pivot residual entry, so leaf Schur-slot columns are live.

The rate target is exactly:
```lean
lemma hC0_det (x : Fin N → R) :
  Hc0 M t (B_det x) := by
  ext i j
  -- cases on decoded residual/spectator/pivot slots
  simp [B_det]

theorem route_phi_det (x : Fin N → R) :
  routeMCore M (phi_det x) = (x p)^2 * U_det x := by
  simpa [phi_det] using
    routeMCore_phiGen (u := x p) (M := M) (t := t)
      (B := B_det x) hle (hC0_det x)
```

The determinant target should be coordinate-level, not a bridge to `phiFlatStructV`:
```lean
lemma phi_det_coord (x : Fin N → R) (q : Fin N) :
  phi_det x q =
    Q_linear M t
      (pivotBlowupOn active p (schurOps M t x)) q := by
  obtain idx := decodeFlatIdx q
  -- induction/cases over the boundary/layer index of idx
  -- cases on pivot / active nonpivot / spectator
  simp [phi_det, B_det, chartParamsGen, pivotBlowupOn, schurOps]
```

The induction is over the Schur boundary prefix:
```lean
IH k :
  ∀ idx with idx.layer < k,
    chartParamsGen (x p) M t (B_det x) hle at idx
      =
    factoredSchurPivotParams M t active p x at idx
```

This is not the old `chartIdxEquiv K/X/N/E` archaeology. It is the local decoded-`FlatIdx` statement for the one decoder used by the one chart.

**Q3**
Yes. The route is:

```lean
phi_det x := phiGen (x p) M t (B_det x) hle
```

Rate comes from `routeMCore_phiGen` instantiated at `B := B_det x`.

Det comes from the direct Jacobian/factor computation of that same chart, after unfolding `B_det`. No bridge to `phiFlatStructV`, no new telescope, and no global `composeFold = phiFlatStructV` proof.

**Q4 `(3,3,3,3)`**
For `M = (3,3,3,3)`, the unique minimizer is `T* = (2,1,0)`. The drops occur at all three boundaries. The active residual blocks have total size

```text
|active| = minAdm = 6
```

Choose `p ∈ active`. Then `pivotBlowupOn active p` contributes

```text
|x_p|^(6-1) = |x_p|^5
```

The Schur layer-ops handle all three boundary drops uniformly through the same boundary-prefix induction. Because `B_det` has nonzero terminal `Rfin` and no dead leaf slots, the multi-boundary coupling remains full-rank. The rate is still obtained by the banked theorem:

```text
routeMCore (phi_det x) = (x_p)^2 * U_det x
```

**Q5**
No, all three are not walls.

**2a lands.**  
**2b is a wall/no-go.**  
**A-revisited only lands if rewritten into the same full-rank `B_det` construction as 2a; as a mere patch to the old decoder, it is not the safest build route.**