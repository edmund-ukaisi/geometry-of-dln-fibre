**Recommendation: A.**

**Fact:** your green lemmas certify the Schur node once the loss is literally the two-factor loss `‖Â * A2‖²`.  
**Inference:** state `schur_straighten_squeeze_exists` at the **2-factor matrix node**. This is faithful because it proves exactly the certified per-node math and leaves the L-layer-to-node coordinate contract as an explicit blow-up-lane interface. Option B looks convenient but risks hiding guessed coordinates in an equality hypothesis that belongs upstream.

Sketch:

```lean
theorem schur_straighten_squeeze_exists
    {m k n : Nat}
    -- dimension/nonempty hypotheses as needed for pivot/block indices
    (Â : Matrix (Fin m) (Fin k) ℝ)
    (A2 : Matrix (Fin k) (Fin n) ℝ)
    (hpiv : Â 0 0 = 1)
    -- node split data, preferably already packaged:
    (Snode : ChainDimSplit Mnode)
    (redEmbed : Y → Params Snode.red)
    (flatCore : (Fin n → ℝ) × Y → ℝ)
    (G : Y → ℝ)
    -- definitional/contracts tying coordinates to blocks:
    (hflat :
      ∀ w, flatCore w =
        ‖(AhatOf w) * (A2Of w)‖_F_sq)
    (hE :
      ∀ w j, E w j = β w j + ∑ r, a w r * Γ w r j)
    (hS :
      ∀ w i r, S w i r = D w i r - b w i * a w r)
    (hG :
      ∀ y, G y ^ 2 = dlnLoss Snode.red 0 (redEmbed y))
    -- measurability/nonzero/local-bound contracts not automatic from algebra:
    (hmeasF : Measurable flatCore)
    (hmeasG : Measurable G)
    (hGne : G ≠ 0)
    :
    ∃ c₁ c₂,
      IsSchurStraightenSqueeze Mnode Snode flatCore G redEmbed c₁ c₂
```

Field discharge map:

- `redCore_eq`: by `hG`.
- Schur algebra inside `squeeze`: `schur_row_decomp`.
- loss difference / ideal or measure-drop algebra: `schur_lossDiff_eq_cofactor` and `schur_lossDiff_mem_ideal`.
- two-sided comparability: `squeeze_bounds_abstract`.
- `c₁pos`, `c₂pos`: from the constants produced by `squeeze_bounds_abstract`.
- `Fmeas`, `Gmeas`, `Gne`: pass as hypotheses unless already derivable locally.

Hardest sub-step: proving the local bound hypothesis `hp : ∑ pⱼ² ≤ t² * ∑ Eᵢ²` in the exact coordinate split. That is the analytic bookkeeping bridge between the Schur decomposition and `squeeze_bounds_abstract`.

For coordinates, the clean split is:

```lean
(Fin n → ℝ) × Y
```

with first component exactly `E_row : Fin n → ℝ`, and

```lean
Y ≃ (a,b,D,Γ)   -- all non-regular node coordinates
```

Then define

```lean
β := E_row - a * Γ
Â := [[1,a],[b,D]]
A2 := [[β],[Γ]]
S := D - b * a
G y := ‖S y * Γ y‖_F
```

**Inference:** this avoids making `β` an independent coordinate, so `E_row` is literally the regular generator family required by `IsSchurStraightenSqueeze`.

Temptation to avoid: do not assert `dlnLoss M 0 coords = ‖Â * A2‖²` inside this theorem unless the blow-up lane supplies it. Make it a separate hypothesis/interface, e.g. `h_blowup_loss_eq`, consumed later by the full-node theorem.