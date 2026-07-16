import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedCharge

set_option linter.style.longLine false

/-!
# `RouteMSJDeepGate` — the deep-stratum codim gate (Route B, the Nat part) (module (i-b)/gate)

**Thread `genm-sj5-stepbuild` (aoyagi-full Stage 2), Route B** (the VERIFIED `genm-deepgate/deepgate-cert.md`:
the deep-stratum codim WITH the peeled corank det charge is BOUNDED — the charge never binds). Route B
closes Step 3's deep factor by a DIRECT per-stratum codim gate (no comparator; stepbuild's `r^{−ab}` killed
the bare-comparator route, not the integral).

The gate (cert §6): at a binding cut `u=t★+j`, deep rank-drop `{rank Z_deep = ρ−k}`, the codim WITH charge is
`C_k = min(u·ρ, u·(ρ−k) + κ_k − γ_{ρ−k}) ≥ minAdm(M) − a·b = 2·T1_q`, discharged by the Nat chain
`minAdm(M) ≤ κ_k + minAdm(M₀,M₁,ρ−k)` (I, deep-rank stratification — OWNED BY `crstrat`) and
`minAdm(M₀,M₁,s) ≤ a·b + u·s − γ_s` (II, this file) with `γ_s = max_{max(0,b−s)≤h≤b} h(a+b−s−h)` (`chargeExp`).

This file banks the TRACTABLE part (γ_s + II + the gate assembly), taking **(I) as an explicit hypothesis**
(κ abstract — `crstrat` owns the composite-rank recursion `CR` and discharges `minAdm ≤ CR(deep,ρ−k) + …`).
-/

namespace DLNFibre.DLN.RLCT

open Matrix
open scoped BigOperators

/-! ## The corank Gram det-charge exponent `γ_s` -/

/-- **The corank Gram det-charge exponent** `γ_s = max_{b−s ≤ h ≤ b} h·(a+b−s−h)` (cert §1(B)), the exact
`A_cor`-integral charge exponent at a rank-`s` drop (stratifying `rank(A_cor|surviving) = b−h`; the naive
pointwise value is only the `h=(b−s)₊` term). `max 0 (b−s) = b−s` over ℕ. -/
noncomputable def chargeExp (a b s : ℕ) : ℕ :=
  (Finset.Icc (b - s) b).sup' (Finset.nonempty_Icc.mpr (Nat.sub_le b s))
    (fun h => h * (a + b - s - h))

/-- Each in-range `h·(a+b−s−h)` is ≤ `γ_s`. -/
theorem le_chargeExp (a b s h : ℕ) (hh : h ∈ Finset.Icc (b - s) b) :
    h * (a + b - s - h) ≤ chargeExp a b s :=
  Finset.le_sup' (fun h => h * (a + b - s - h)) hh

/-- **Charge inert at a shallow drop**: `γ_s = 0` when `a+b ≤ s` (cert §5 — the `k=1`/`rank ρ−1` stratum,
`s = ρ−1 ≥ a+b` by rankgen, so `Q_b` keeps full row rank and the det charge is a bounded unit). -/
theorem chargeExp_eq_zero_of_le (a b s : ℕ) (h : a + b ≤ s) : chargeExp a b s = 0 := by
  refine le_antisymm ?_ (Nat.zero_le _)
  refine Finset.sup'_le _ _ (fun x _ => ?_)
  have hz : a + b - s - x = 0 := by omega
  rw [hz, Nat.mul_zero]

/-- **Full collapse**: `γ_0 = a·b` (the `Z_deep → 0` stratum; matches stepbuild's `r^{−ab}` scaling). At
`s=0` the range is the singleton `{b}`, forcing `h=b`, `γ_0 = b·a`. -/
theorem chargeExp_zero (a b : ℕ) : chargeExp a b 0 = a * b := by
  have hval : ∀ h ∈ Finset.Icc (b - 0) b, h * (a + b - 0 - h) = a * b := by
    intro h hh
    rw [Finset.mem_Icc] at hh
    have hb : h = b := by omega
    subst hb
    rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.mul_comm]
  refine le_antisymm (Finset.sup'_le _ _ (fun h hh => le_of_eq (hval h hh))) ?_
  have hbmem : b ∈ Finset.Icc (b - 0) b := by rw [Finset.mem_Icc]; omega
  calc a * b = b * (a + b - 0 - b) := by rw [Nat.sub_zero, Nat.add_sub_cancel, Nat.mul_comm]
    _ ≤ chargeExp a b 0 := le_chargeExp a b 0 b hbmem

/-! ## The arity-3 `minAdm` QIP upper bound -/

/-- **The arity-3 QIP upper bound** `minAdm ![M₀,M₁,s] ≤ (M₀−r)(M₁−r) + r·s` for any `r ≤ min(M₀,M₁)` —
the 3-chain `minAdm` is `inf_r [(M₀−r)(M₁−r)+r·s]`, so any `r` gives an upper bound (banked
`minAdm_le_peelCharge_add_redChain` at `L=0`; the reduced chain `redChain r ![M₀,M₁,s]` is the 2-leaf
`![r,s]`, `minAdm = r·s`). -/
theorem minAdm3_le_qip (M0 M1 s r : ℕ) (hr : r ≤ min M0 M1) :
    minAdm ![M0, M1, s] ≤ (M0 - r) * (M1 - r) + r * s := by
  have hu : r ≤ min ((![M0, M1, s] : Fin 3 → ℕ) 0) ((![M0, M1, s] : Fin 3 → ℕ) 1) := by
    simpa using hr
  have h := minAdm_le_peelCharge_add_redChain ![M0, M1, s] r hu
  have hred : minAdm (redChain r ![M0, M1, s]) = r * s := by
    rw [← minAdmRec_eq_minAdm]; rfl
  rw [peelCharge, hred] at h
  exact h

/-! ## (II) — the 3-chain QIP with the charge exponent -/

/-- **(II) — the 3-chain QIP with the charge exponent** (cert §4): `minAdm ![M₀,M₁,s] + γ_s ≤ a·b + u·s`
(`a = M₀−u`, `b = M₁−u`, `γ_s = chargeExp a b s`), for `u ≤ min(M₀,M₁)`. Per in-range `h`, the QIP index
`r = u+h` (case `h ≤ a`, an exact ℤ identity) or `r = u+a` (case `h > a`, via `h(a+b−s−h) ≤ a(b−s)` from
`(h−(b−s))(h−a) ≥ 0`) bounds `minAdm ![M₀,M₁,s] + h(a+b−s−h) ≤ a·b+u·s`; taking the `sup'` over `h` gives
the charge exponent. The charge-carrying half of the deep-stratum gate; combined with (I)
(`crstrat`) it yields `C_k ≥ minAdm(M) − a·b`. -/
theorem minAdm3_add_chargeExp_le (M0 M1 u s : ℕ) (hu : u ≤ min M0 M1) :
    minAdm ![M0, M1, s] + chargeExp (M0 - u) (M1 - u) s ≤ (M0 - u) * (M1 - u) + u * s := by
  have hmle : minAdm ![M0, M1, s] ≤ (M0 - u) * (M1 - u) + u * s := minAdm3_le_qip M0 M1 s u hu
  set a := M0 - u with ha
  set b := M1 - u with hb
  -- per-`h` bound: `h·(a+b−s−h) + minAdm₃ ≤ a·b + u·s`
  have hper : ∀ h, b - s ≤ h → h ≤ b →
      h * (a + b - s - h) + minAdm ![M0, M1, s] ≤ a * b + u * s := by
    intro h h1 h2
    by_cases htr : a + b ≤ s + h
    · -- charge inert: `a+b−s−h = 0`
      have hz : a + b - s - h = 0 := by omega
      rw [hz, Nat.mul_zero, Nat.zero_add]; exact hmle
    · by_cases hha : h ≤ a
      · -- `h ≤ a`: QIP index `r = u+h`, exact ℤ identity
        have hr : u + h ≤ min M0 M1 := by omega
        have hq := minAdm3_le_qip M0 M1 s (u + h) hr
        have e0 : M0 - (u + h) = a - h := by omega
        have e1 : M1 - (u + h) = b - h := by omega
        rw [e0, e1] at hq
        have hkey : h * (a + b - s - h) + ((a - h) * (b - h) + (u + h) * s) = a * b + u * s := by
          have hsab : s ≤ a + b := by omega
          have hhab : h ≤ a + b - s := by omega
          zify [hsab, hhab, hha, h2]
          ring
        omega
      · -- `h > a` (forces `a < b`): QIP index `r = u+a = M₀`, `h(a+b−s−h) ≤ a(b−s)`
        have hr : u + a ≤ min M0 M1 := by omega
        have hq := minAdm3_le_qip M0 M1 s (u + a) hr
        have e0 : M0 - (u + a) = 0 := by omega
        have e1 : M1 - (u + a) = b - a := by omega
        rw [e0, e1, Nat.zero_mul, Nat.zero_add] at hq
        have hbs : s ≤ b := by omega
        have hg : h * (a + b - s - h) + a * s ≤ a * b := by
          have hsab : s ≤ a + b := by omega
          have hhab : h ≤ a + b - s := by omega
          have hz1 : (0 : ℤ) ≤ (h : ℤ) - ((b : ℤ) - (s : ℤ)) := by
            have hc : ((b - s : ℕ) : ℤ) ≤ (h : ℤ) := by exact_mod_cast h1
            rw [Nat.cast_sub hbs] at hc; linarith
          have hz2 : (0 : ℤ) ≤ (h : ℤ) - (a : ℤ) := by
            have haa : a < h := by omega
            have hc : (a : ℤ) < (h : ℤ) := by exact_mod_cast haa
            linarith
          zify [hsab, hhab, hbs]
          nlinarith [mul_nonneg hz1 hz2]
        have hexp : (u + a) * s = u * s + a * s := by ring
        omega
  -- fold the per-`h` bounds into the `sup'`
  have hsup : chargeExp a b s ≤ (a * b + u * s) - minAdm ![M0, M1, s] := by
    refine Finset.sup'_le _ _ (fun h hh => ?_)
    rw [Finset.mem_Icc] at hh
    exact Nat.le_sub_of_add_le (hper h hh.1 hh.2)
  calc minAdm ![M0, M1, s] + chargeExp a b s
      = chargeExp a b s + minAdm ![M0, M1, s] := Nat.add_comm _ _
    _ ≤ ((a * b + u * s) - minAdm ![M0, M1, s]) + minAdm ![M0, M1, s] :=
        Nat.add_le_add_right hsup _
    _ = a * b + u * s := Nat.sub_add_cancel hmle

/-! ## The deep-stratum gate assembly (κ abstract — `crstrat` owns `CR`/(I)) -/

/-- **Deep-branch gate** (cert §6): given (I) the deep-rank stratification `minAdm(M) ≤ κ_k +
minAdm(M₀,M₁,ρ−k)` (`κ_k = CR((M₂,…,M_last), ρ−k)`, discharged by `crstrat`) and (II)
(`minAdm3_add_chargeExp_le`), the deep branch of `C_k` dominates the target:
`minAdm(M) + γ_{ρ−k} ≤ a·b + u·(ρ−k) + κ_k`, i.e. `minAdm(M) − a·b ≤ u·(ρ−k) + κ_k − γ_{ρ−k}` = the deep
branch of `C_k`. `κ`, `mM` (= `minAdm(M)`) abstract — no `CR` in this file. -/
theorem deepGate_branch (M0 M1 u s κ mM : ℕ) (hu : u ≤ min M0 M1)
    (hI : mM ≤ κ + minAdm ![M0, M1, s]) :
    mM + chargeExp (M0 - u) (M1 - u) s ≤ (M0 - u) * (M1 - u) + u * s + κ := by
  have hII := minAdm3_add_chargeExp_le M0 M1 u s hu
  omega

/-- **`u·ρ`-branch gate**: the generic-front cap. At the top deep rank `s = ρ` the composite-rank codim
`κ_0 = CR(deep, ρ) = 0` (`hκ0`) and the charge is inert (`a+b ≤ ρ`, from rankgen `a+b ≤ ρ−1`, `hρ`),
so (I)+(II) give `minAdm(M) ≤ a·b + u·ρ` — the `u·ρ` branch of `C_k`. -/
theorem deepGate_uρ_branch (M0 M1 u ρ κ0 mM : ℕ) (hu : u ≤ min M0 M1)
    (hI : mM ≤ κ0 + minAdm ![M0, M1, ρ]) (hκ0 : κ0 = 0)
    (hρ : (M0 - u) + (M1 - u) ≤ ρ) :
    mM ≤ (M0 - u) * (M1 - u) + u * ρ := by
  have hII := minAdm3_add_chargeExp_le M0 M1 u ρ hu
  rw [chargeExp_eq_zero_of_le _ _ _ hρ] at hII
  omega

end DLNFibre.DLN.RLCT
