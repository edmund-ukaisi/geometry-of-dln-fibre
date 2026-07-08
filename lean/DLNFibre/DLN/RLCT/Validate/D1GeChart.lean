import DLNFibre.DLN.RLCT.Validate.D1GeSchurTelescope

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeChart` — the general-`L` corner-elimination chart (rungs 4+)

Piece (iii), the chart itself. The general-`L` analogue of `schurChartRaw`/`schurChartRawInv`
(`D1L2PhiExpl`), built on the asymmetric Schur telescope (`D1GeSchurTelescope`, rungs 1–3). Operates
on the `ℕ`-indexed `Fin`-core block chain `C` (the natural home of `partProd`/`redFactorGen`); the
`BlockParamsGen`/flat conjugation is a later bridge.

**Rung 4 — the packing** (Codex-settled, DOF-verified; artefact
`threads/genm-geleg1/codex/piece-iii-rung4-packing-{prompt,answer}.md`). `schurChartRawGen C L`
per layer slot `s`:

    slot s = fromBlocks (P_{s+1})₁₁  (P_{s+1})₁₂  Q_s.21  R_s
    Q_s.21 = (P_L)₂₁  (s = 0) | (C_s)₂₁  (s ≥ 1),   R_s = redFactorGen C s,   P_k = partProd C k.

The top row is the PREFIX-product top row `(P_{s+1})₁₁, (P_{s+1})₁₂` (regular); the `(2,2)`
corner is the reduced factor `R_s`; the lower-left holds `(C_s)₂₁` except slot `0`, which holds the
full product's `(P_L)₂₁` (last regular direction). Same type as `C s`, so again a chain. The
`nReg = r·(H₀+Hᴸ−r)` regular directions live in `(P_L)₁₁, (P_L)₁₂, (P_L)₂₁`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

/-! ## Rung 4 — the packed corner-elimination chart map -/

/-- **The general-`L` corner-elimination chart** (raw, chain form). Per slot `s`, packs the prefix
product `(partProd C (s+1))` top row, the lower-left `(C_s)₂₁` (or `(partProd C L)₂₁` at `s=0`),
the reduced factor `redFactorGen C s`. Same type as `C`, so again a chain. The general-`L` analog of
`schurChartRaw`. -/
noncomputable def schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ) :
    (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ :=
  fun s => Matrix.fromBlocks
    (partProd C (s + 1)).toBlocks₁₁
    (partProd C (s + 1)).toBlocks₁₂
    (if h : s = 0 then h.symm ▸ (partProd C L).toBlocks₂₁ else (C s).toBlocks₂₁)
    (redFactorGen C s)

variable {r₀ : ℕ} {n : ℕ → ℕ}
  (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ)

/-- The `(1,1)` corner of slot `s`: the prefix-product pivot `(partProd C (s+1))₁₁`. -/
@[simp] theorem schurChartRawGen_toBlocks₁₁ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₁₁ = (partProd C (s + 1)).toBlocks₁₁ := rfl

/-- The `(1,2)` corner of slot `s`: the prefix-product `(partProd C (s+1))₁₂`. -/
@[simp] theorem schurChartRawGen_toBlocks₁₂ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₁₂ = (partProd C (s + 1)).toBlocks₁₂ := rfl

/-- The `(2,2)` corner of slot `s`: the reduced factor `R_s = redFactorGen C s`. -/
@[simp] theorem schurChartRawGen_toBlocks₂₂ (s : ℕ) :
    (schurChartRawGen C L s).toBlocks₂₂ = redFactorGen C s := rfl

/-- The lower-left of slot `s ≥ 1`: `(C_s)₂₁`. -/
@[simp] theorem schurChartRawGen_toBlocks₂₁_succ (s : ℕ) :
    (schurChartRawGen C L (s + 1)).toBlocks₂₁ = (C (s + 1)).toBlocks₂₁ := rfl

/-- The lower-left of slot `0`: the full product's `(P_L)₂₁ = (partProd C L)₂₁` (the last regular
direction). -/
@[simp] theorem schurChartRawGen_toBlocks₂₁_zero :
    (schurChartRawGen C L 0).toBlocks₂₁ = (partProd C L).toBlocks₂₁ := rfl

/-! ## Rung 5 — recovering the product from the chart output -/

/-- The ordered product of the `(2,2)` corners of a chain `Q`, `(Q 0)₂₂·…·(Q (k−1))₂₂`, of shape
`(Fin (n 0)) × (Fin (n k))` (`= 1` at `k = 0`). At `Q = schurChartRawGen C L` this is `redProd C`
(`blockDiagProd_schurChartRawGen`), i.e. the reduced core `blockSchur (partProd C L)`. -/
noncomputable def blockDiagProd {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) :
    (k : ℕ) → Matrix (Fin (n 0)) (Fin (n k)) ℝ
  | 0 => 1
  | k + 1 => blockDiagProd Q k * (Q k).toBlocks₂₂

/-- **`recoverProductGen`** — rebuild the full product's block form from the chart output over
`last + 1` layers: top row `(P_L)₁₁, (P_L)₁₂` from the last slot, lower-left `(P_L)₂₁` from slot 0,
and the eliminated `(2,2)` corner as `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ + ∏ R_s`. Parametrised by `last`,
last slot index `= L − 1`) so the output width `Fin (n (last+1))` needs no `L−1` cast. General-`L`
analogue of `recoverProduct`. -/
noncomputable def recoverProductGen {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ) :
    Matrix (Fin r₀ ⊕ Fin (n 0)) (Fin r₀ ⊕ Fin (n (last + 1))) ℝ :=
  Matrix.fromBlocks (Q last).toBlocks₁₁ (Q last).toBlocks₁₂ (Q 0).toBlocks₂₁
    ((Q 0).toBlocks₂₁ * (Q last).toBlocks₁₁⁻¹ * (Q last).toBlocks₁₂ + blockDiagProd Q (last + 1))

/-- The `(2,2)`-corner fold of the chart output is the reduced-factor telescope `redProd C`. By
on `k`, reading `(schurChartRawGen C L s)₂₂ = redFactorGen C s`. -/
theorem blockDiagProd_schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L : ℕ) (k : ℕ) :
    blockDiagProd (schurChartRawGen C L) k = redProd C k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [blockDiagProd, redProd, ih, schurChartRawGen_toBlocks₂₂]

/-- **Rung 5 — the chart output rebuilds the product.** `recoverProductGen (schurChartRawGen C
last = partProd C (last+1)` on the prefix-pivot domain: the three regular corners are the packed
`(P_L)₁₁/₁₂/₂₁`, and the eliminated `(2,2)` corner is rebuilt as `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ +
blockSchur (partProd C L)` (the reduced core, `blockDiagProd_schurChartRawGen` + the asymmetric
telescope `blockSchur_partProd_asym_fold`). Validates the packing. General-`L` analogue of
`recoverProduct_schurChartRaw`. -/
theorem recoverProductGen_schurChartRawGen {r₀ : ℕ} {n : ℕ → ℕ}
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ)
    (hPart : ∀ k, k ≤ last + 1 → Invertible (partProd C k).toBlocks₁₁) :
    recoverProductGen (schurChartRawGen C (last + 1)) last = partProd C (last + 1) := by
  letI hpiv : Invertible (partProd C (last + 1)).toBlocks₁₁ := hPart (last + 1) le_rfl
  conv_rhs => rw [← Matrix.fromBlocks_toBlocks (partProd C (last + 1))]
  rw [recoverProductGen, schurChartRawGen_toBlocks₁₁, schurChartRawGen_toBlocks₁₂,
    schurChartRawGen_toBlocks₂₁_zero, blockDiagProd_schurChartRawGen,
    ← blockSchur_partProd_asym_fold C (last + 1) hPart, blockSchur]
  congr 1
  -- `(P_L)₂₁·(P_L)₁₁⁻¹·(P_L)₁₂ + ((P_L)₂₂ − (P_L)₂₁·(Ring.inverse (P_L)₁₁)·(P_L)₁₂) = (P_L)₂₂`.
  rw [Ring.inverse_invertible, Matrix.invOf_eq_nonsing_inv (partProd C (last + 1)).toBlocks₁₁]
  abel

/-! ## Rung 6 — the rational inverse map -/

/-- **Reconstruct the `(t+1)`-th layer** `C_{t+1}` from the chart output, locally (reads slots `t`,
`t+1`). With `p_{t+1}=(Q t)₁₁`, `q_{t+1}=(Q t)₁₂`, `p_{t+2}=(Q (t+1))₁₁`, `q_{t+2}=(Q (t+1))₁₂`,
`D = (Q (t+1))₂₁`, `R = (Q (t+1))₂₂`:
`E = R + D·p_{t+2}⁻¹·q_{t+2}`, `A = p_{t+1}⁻¹(p_{t+2}−q_{t+1}D)`, `B = p_{t+1}⁻¹(q_{t+2}−q_{t+1}E)`,
`C_{t+1} = fromBlocks A B D E`. Rational in the prefix pivots `p_{t+1}, p_{t+2}`. -/
noncomputable def invLayerSucc {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (t : ℕ) :
    Matrix (Fin r₀ ⊕ Fin (n (t + 1))) (Fin r₀ ⊕ Fin (n (t + 2))) ℝ :=
  let pt1 := (Q t).toBlocks₁₁; let qt1 := (Q t).toBlocks₁₂
  let pt2 := (Q (t + 1)).toBlocks₁₁; let qt2 := (Q (t + 1)).toBlocks₁₂
  let D := (Q (t + 1)).toBlocks₂₁; let R := (Q (t + 1)).toBlocks₂₂
  let E := R + D * pt2⁻¹ * qt2
  Matrix.fromBlocks (pt1⁻¹ * (pt2 - qt1 * D)) (pt1⁻¹ * (qt2 - qt1 * E)) D E

/-- **`schurChartRawInvGen`** — the rational inverse of the chart over `last + 1` layers. Layers
`s = t+1 ≥ 1` are reconstructed locally by `invLayerSucc`; layer 0 uses the full-product
`(P_L)₂₁ = (Q 0)₂₁` and the suffix product `γ = (C_1·…·C_last)₂₁` (a `partProd` of the reconstructed
suffix `invLayerSucc Q ·`): `D_0 = ((P_L)₂₁ − R_0·γ)·p_L⁻¹·p_1`, `E_0 = R_0 + D_0·p_1⁻¹·q_1`.
analogue of `schurChartRawInv`; prefix-pivots-only. -/
noncomputable def schurChartRawInvGen {r₀ : ℕ} {n : ℕ → ℕ}
    (Q : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (last : ℕ) :
    (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ
  | 0 =>
      let γ := (partProd (fun t => invLayerSucc Q t) last).toBlocks₂₁
      let R0 := (Q 0).toBlocks₂₂; let pL := (Q last).toBlocks₁₁
      let p1 := (Q 0).toBlocks₁₁; let q1 := (Q 0).toBlocks₁₂; let ellL := (Q 0).toBlocks₂₁
      let D0 := (ellL - R0 * γ) * pL⁻¹ * p1
      Matrix.fromBlocks p1 q1 D0 (R0 + D0 * p1⁻¹ * q1)
  | t + 1 => invLayerSucc Q t

/-! ## Rung 6b — the inverse identities -/

variable {r₀ : ℕ} {n : ℕ → ℕ}

/-- **`partProd` reads only its first `k` layers.** If two chains agree on layers `0,…,k−1`, their
`partProd` at `k` agree. Induction on `k`. -/
theorem partProd_congr {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {m : ℕ → Type*}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {α : Type*} [CommRing α]
    (C C' : (s : ℕ) → Matrix (ρ ⊕ m s) (ρ ⊕ m (s + 1)) α) (k : ℕ) (h : ∀ t, t < k → C t = C' t) :
    partProd C k = partProd C' k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [partProd, partProd, ih (fun t ht => h t (by omega)), h k (by omega)]

/-- **Front-peel of `partProd`.** The left-associated fold peels its FIRST factor:
`partProd C (k+1) = C 0 · partProd (C ∘ succ) k`, where `C ∘ succ = fun t => C (t+1)` is the suffix
chain. Induction on `k` (base `partProd C 1 = C 0`; step by `Matrix.mul_assoc`). Used to relate the
full product to the reconstructed suffix in the `s = 0` inverse case. -/
theorem partProd_front_peel
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (k : ℕ) :
    partProd C (k + 1) = C 0 * partProd (fun t => C (t + 1)) k := by
  induction k with
  | zero => simp only [partProd, Matrix.one_mul, Matrix.mul_one]
  | succ k ih =>
      rw [partProd, ih, partProd, Matrix.mul_assoc]

/-- **Local reconstruction is exact** (the `s ≥ 1` half of `Ψ∘Φ = id`). With the prefix pivots
`(partProd C (t+1))₁₁`, `(partProd C (t+2))₁₁` invertible, `invLayerSucc (schurChartRawGen C L) t
= C (t+1)`. Via the block-mult identities `partProd C (t+2) = partProd C (t+1) · C (t+1)` and the
pivot cancellations (the reduced-factor `R` term cancels in `E`). -/
theorem invLayerSucc_schurChartRawGen
    (C : (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ) (L t : ℕ)
    (hp1 : Invertible (partProd C (t + 1)).toBlocks₁₁)
    (hp2 : Invertible (partProd C (t + 1 + 1)).toBlocks₁₁) :
    invLayerSucc (schurChartRawGen C L) t = C (t + 1) := by
  letI := hp1; letI := hp2
  have hu1 : IsUnit ((partProd C (t + 1)).toBlocks₁₁).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)
  -- block-mult identities for `partProd C (t+1+1) = partProd C (t+1) · C (t+1)`.
  have hblk : partProd C (t + 1 + 1) = Matrix.fromBlocks
      ((partProd C (t + 1)).toBlocks₁₁ * (C (t + 1)).toBlocks₁₁
        + (partProd C (t + 1)).toBlocks₁₂ * (C (t + 1)).toBlocks₂₁)
      ((partProd C (t + 1)).toBlocks₁₁ * (C (t + 1)).toBlocks₁₂
        + (partProd C (t + 1)).toBlocks₁₂ * (C (t + 1)).toBlocks₂₂)
      ((partProd C (t + 1)).toBlocks₂₁ * (C (t + 1)).toBlocks₁₁
        + (partProd C (t + 1)).toBlocks₂₂ * (C (t + 1)).toBlocks₂₁)
      ((partProd C (t + 1)).toBlocks₂₁ * (C (t + 1)).toBlocks₁₂
        + (partProd C (t + 1)).toBlocks₂₂ * (C (t + 1)).toBlocks₂₂) := by
    conv_lhs => rw [show partProd C (t + 1 + 1) = partProd C (t + 1) * C (t + 1) from rfl,
      ← Matrix.fromBlocks_toBlocks (partProd C (t + 1)), ← Matrix.fromBlocks_toBlocks (C (t + 1))]
    rw [Matrix.fromBlocks_multiply]
  have h11 : (partProd C (t + 1 + 1)).toBlocks₁₁
      = (partProd C (t + 1)).toBlocks₁₁ * (C (t + 1)).toBlocks₁₁
        + (partProd C (t + 1)).toBlocks₁₂ * (C (t + 1)).toBlocks₂₁ := by
    rw [hblk, Matrix.toBlocks_fromBlocks₁₁]
  have h12 : (partProd C (t + 1 + 1)).toBlocks₁₂
      = (partProd C (t + 1)).toBlocks₁₁ * (C (t + 1)).toBlocks₁₂
        + (partProd C (t + 1)).toBlocks₁₂ * (C (t + 1)).toBlocks₂₂ := by
    rw [hblk, Matrix.toBlocks_fromBlocks₁₂]
  -- the reduced factor cancels: `E = R + D·p₂⁻¹·q₂ = (C_{t+1})₂₂`.
  have hE : redFactorGen C (t + 1)
      + (C (t + 1)).toBlocks₂₁ * (partProd C (t + 1 + 1)).toBlocks₁₁⁻¹
        * (partProd C (t + 1 + 1)).toBlocks₁₂ = (C (t + 1)).toBlocks₂₂ := by
    rw [redFactorGen, Ring.inverse_invertible,
      Matrix.invOf_eq_nonsing_inv (partProd C (t + 1 + 1)).toBlocks₁₁]
    abel
  -- A-block: `p₁⁻¹·((P_{t+2})₁₁ − q₁·D) = (C_{t+1})₁₁`.
  have hA : (partProd C (t + 1)).toBlocks₁₁⁻¹
      * ((partProd C (t + 1 + 1)).toBlocks₁₁
        - (partProd C (t + 1)).toBlocks₁₂ * (C (t + 1)).toBlocks₂₁) = (C (t + 1)).toBlocks₁₁ := by
    rw [h11, add_sub_cancel_right, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1, Matrix.one_mul]
  -- B-block: simplify `E` by `hE`, then like the A-block via `h12`.
  have hB : (partProd C (t + 1)).toBlocks₁₁⁻¹
      * ((partProd C (t + 1 + 1)).toBlocks₁₂ - (partProd C (t + 1)).toBlocks₁₂
        * (redFactorGen C (t + 1) + (C (t + 1)).toBlocks₂₁ * (partProd C (t + 1 + 1)).toBlocks₁₁⁻¹
          * (partProd C (t + 1 + 1)).toBlocks₁₂)) = (C (t + 1)).toBlocks₁₂ := by
    rw [hE, h12, add_sub_cancel_right, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu1,
      Matrix.one_mul]
  simp only [invLayerSucc, schurChartRawGen_toBlocks₁₁, schurChartRawGen_toBlocks₁₂,
    schurChartRawGen_toBlocks₂₁_succ, schurChartRawGen_toBlocks₂₂]
  rw [hA, hB, hE]
  exact Matrix.fromBlocks_toBlocks (C (t + 1))

end DLNFibre.DLN.RLCT
