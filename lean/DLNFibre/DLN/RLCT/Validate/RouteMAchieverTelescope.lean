import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# `RouteMAchieverTelescope` — the abstract chained-product telescoping (R1 general achiever)

The reusable algebraic heart of the general-`M` achiever chart identity
`prod M (φ_M u) = u · H` (the chart factorization `routeMCore M (φ_M u) = ‖prod‖² = u²·V`).

The general chart's layer matrices `A^(0), …, A^(L−1)` chain through *compressed transitions* `C_s`
(the cert `threads/26-r1-genM-chart/`'s closed form): each boundary `s` carries a per-level local
identity `C_s · A_s = B_s · C_{s+1} + u · E_s` (the `P_s K_s` part `B_s`, the radial-error part `E_s`),
with the terminal condition `C_L = u · R`. Backward induction then forces every suffix product
`C_s · (A_s · A_{s+1} · ⋯ · A_{L−1})` to be `u`-divisible — in particular `C_0 · (full product) = u · H`.

This module banks that telescoping ABSTRACTLY — over arbitrary `ℕ`-valued width families
`Wwid, Twid : ℕ → ℕ` (the spaces are `Fin (Wwid k)` / `Fin (Twid k)`, so all `Fintype`/`DecidableEq`
are automatic) and a chain length `n` — so the brutal per-`M` block construction need only supply the
*local* identities `C_s · A_s = B_s · C_{s+1} + u · E_s` and `C_n = u · R`; the global telescope is
proven once, here, sorry-free. (The decorrelated-Codex design read, thread 33, ranked this the single
highest-value reusable increment toward the general atom.)

* `Chain.suffix` — the suffix product `A_s · ⋯ · A_{n−1} : Mat (Fin (Wwid s)) (Fin (Wwid n))`.
* `Chain.Hmat` — the telescoped quotient `H_s` (`B_s · H_{s+1} + E_s · suffix_{s+1}`, `H_n := R`).
* `chain_telescope` — `C_s · suffix s = u • Hmat s` for every `s ≤ n` (the keystone). At `s = 0`:
  `C_0 · (full product) = u · Hmat 0` — the `prod = u·H` divisibility the chart identity consumes.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (pure matrix algebra; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators
open Matrix

/-- **An abstract chained-product telescope certificate.** The data the general achiever chart's
layer factorization supplies, per boundary level, decoupled from the block construction. `Wwid k` is
the ambient width at slot `k` (`= M k` in the chart instance), `Twid k` the compressed (kept-rank)
width. The single radial pivot `u` is the scalar that telescopes out.

The coefficient type `𝕜` is an arbitrary `CommRing` (was `ℝ`); the matrix algebra of the telescope
(`Matrix.mul`/`add`/`smul`/`mul_assoc`) needs no more. The ℝ instance is the chart's; the
`MvPolynomial (Fin N) ℝ` instance carries the polynomial-valued `Hmat 0` used for the a.e.-positivity
encoding (`RouteMAchieverVvalPoly`). `𝕜` is IMPLICIT, inferred from `u`, so every ℝ-callsite is
unchanged. -/
structure Chain (n : ℕ) {𝕜 : Type*} [CommRing 𝕜] (u : 𝕜) where
  /-- Ambient widths (the layer-product spaces); `Wwid k = M k` in the chart instance. -/
  Wwid : ℕ → ℕ
  /-- Compressed (kept-rank) widths. -/
  Twid : ℕ → ℕ
  /-- The layer matrices `A_k : Fin (Wwid k) → Fin (Wwid (k+1))` (`k < n`); the DLN factors `A^(k)`. -/
  A : (k : ℕ) → Matrix (Fin (Wwid k)) (Fin (Wwid (k + 1))) 𝕜
  /-- The compressed transitions `C_k : Fin (Twid k) → Fin (Wwid k)`. -/
  C : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid k)) 𝕜
  /-- The `P_k K_k` (kept) part of the local identity, `B_k : Fin (Twid k) → Fin (Twid (k+1))`. -/
  B : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Twid (k + 1))) 𝕜
  /-- The radial-error part of the local identity, `E_k : Fin (Twid k) → Fin (Wwid (k+1))`. -/
  E : (k : ℕ) → Matrix (Fin (Twid k)) (Fin (Wwid (k + 1))) 𝕜
  /-- The terminal residual `R : Fin (Twid n) → Fin (Wwid n)` (`C_n = u • R`). -/
  R : Matrix (Fin (Twid n)) (Fin (Wwid n)) 𝕜
  /-- **The per-level local identity** (the only thing the block construction must prove per layer):
  `C_k · A_k = B_k · C_{k+1} + u • E_k`, for `k < n`. -/
  step : ∀ k, k < n → C k * A k = B k * C (k + 1) + u • E k
  /-- **The terminal condition**: `C_n = u • R`. -/
  base : C n = u • R

namespace Chain

variable {n : ℕ} {𝕜 : Type*} [CommRing 𝕜] {u : 𝕜}

/-- The suffix product `A_s · A_{s+1} · ⋯ · A_{n−1} : Mat (Fin (Wwid s)) (Fin (Wwid n))`. Built by
downward recursion on the remaining length `d = n − s`: `suffixAux d s` (with `s + d = n`) is the
product of `d` factors from slot `s`. -/
def suffixAux (c : Chain n u) :
    (d : ℕ) → (s : ℕ) → s + d = n → Matrix (Fin (c.Wwid s)) (Fin (c.Wwid n)) 𝕜
  | 0, s, h => by
      rw [Nat.add_zero] at h
      subst h
      exact (1 : Matrix (Fin (c.Wwid s)) (Fin (c.Wwid s)) 𝕜)
  | d + 1, s, h =>
      have h' : (s + 1) + d = n := by omega
      (c.A s : Matrix (Fin (c.Wwid s)) (Fin (c.Wwid (s + 1))) 𝕜) * c.suffixAux d (s + 1) h'

/-- The suffix product from slot `s` (`s ≤ n`): `A_s · ⋯ · A_{n−1}`. -/
def suffix (c : Chain n u) (s : ℕ) (h : s ≤ n) : Matrix (Fin (c.Wwid s)) (Fin (c.Wwid n)) 𝕜 :=
  c.suffixAux (n - s) s (by omega)

/-- The telescoped quotient `H_s`: `H_n := R`, `H_s := B_s · H_{s+1} + E_s · suffix_{s+1}`. Built by
downward recursion (the `u`-stripped backward fold the telescope produces). -/
def HmatAux (c : Chain n u) :
    (d : ℕ) → (s : ℕ) → s + d = n → Matrix (Fin (c.Twid s)) (Fin (c.Wwid n)) 𝕜
  | 0, s, h => by
      rw [Nat.add_zero] at h
      subst h
      exact c.R
  | d + 1, s, h =>
      have h' : (s + 1) + d = n := by omega
      have hs1 : s + 1 ≤ n := by omega
      (c.B s : Matrix (Fin (c.Twid s)) (Fin (c.Twid (s + 1))) 𝕜) * c.HmatAux d (s + 1) h'
        + (c.E s : Matrix (Fin (c.Twid s)) (Fin (c.Wwid (s + 1))) 𝕜) * c.suffix (s + 1) hs1

/-- The telescoped quotient from slot `s` (`s ≤ n`). -/
def Hmat (c : Chain n u) (s : ℕ) (h : s ≤ n) : Matrix (Fin (c.Twid s)) (Fin (c.Wwid n)) 𝕜 :=
  c.HmatAux (n - s) s (by omega)

/-! ## The suffix / quotient unfolding lemmas

The recursion runs on the remaining length `d`; the proof index `h : s + d = n` is propositional, so
the auxiliaries depend only on `d` (the `_congr` transports). The `_succ` lemmas are the literal `d+1`
recursion equations; the `_last`/`_succ` wrappers reduce `n - s` to `0` / `(n−(s+1))+1` through the
`_congr` transport (avoiding the dependent-motive `rw` on the in-place index). -/

/-- `suffixAux` depends only on the remaining length `d` (the index proof is propositional);
transports along `d = d'`. -/
theorem suffixAux_congr (c : Chain n u) {d d' s : ℕ} (hdd : d = d') (h : s + d = n)
    (h' : s + d' = n) : c.suffixAux d s h = c.suffixAux d' s h' := by
  subst hdd; rfl

/-- `suffixAux` peels one factor (the literal `d+1` recursion equation). -/
theorem suffixAux_succ (c : Chain n u) (d s : ℕ) (h : s + (d + 1) = n) :
    c.suffixAux (d + 1) s h = c.A s * c.suffixAux d (s + 1) (by omega) := rfl

/-- `HmatAux` depends only on the remaining length `d`; transports along `d = d'`. -/
theorem HmatAux_congr (c : Chain n u) {d d' s : ℕ} (hdd : d = d') (h : s + d = n)
    (h' : s + d' = n) : c.HmatAux d s h = c.HmatAux d' s h' := by
  subst hdd; rfl

/-- `HmatAux` peels one step (the literal `d+1` recursion equation). -/
theorem HmatAux_succ (c : Chain n u) (d s : ℕ) (h : s + (d + 1) = n) :
    c.HmatAux (d + 1) s h
      = c.B s * c.HmatAux d (s + 1) (by omega) + c.E s * c.suffix (s + 1) (by omega) := rfl

/-- The suffix at `s = n` is the identity. -/
theorem suffix_last (c : Chain n u) :
    c.suffix n (le_refl n) = (1 : Matrix (Fin (c.Wwid n)) (Fin (c.Wwid n)) 𝕜) :=
  (suffixAux_congr c (show n - n = 0 by omega) _ (by omega))

/-- The suffix one-step peel: `suffix s = A_s · suffix (s+1)` (for `s < n`). -/
theorem suffix_succ (c : Chain n u) (s : ℕ) (h : s < n) :
    c.suffix s (le_of_lt h) = c.A s * c.suffix (s + 1) h := by
  unfold suffix
  rw [suffixAux_congr c (show n - s = (n - (s + 1)) + 1 by omega) _ (by omega),
    suffixAux_succ]

/-- The quotient at `s = n` is `R`. -/
theorem Hmat_last (c : Chain n u) : c.Hmat n (le_refl n) = c.R :=
  (HmatAux_congr c (show n - n = 0 by omega) _ (by omega))

/-- The quotient one-step peel: `Hmat s = B_s · Hmat (s+1) + E_s · suffix (s+1)` (for `s < n`). -/
theorem Hmat_succ (c : Chain n u) (s : ℕ) (h : s < n) :
    c.Hmat s (le_of_lt h)
      = c.B s * c.Hmat (s + 1) h + c.E s * c.suffix (s + 1) h := by
  unfold Hmat
  rw [HmatAux_congr c (show n - s = (n - (s + 1)) + 1 by omega) _ (by omega), HmatAux_succ]

/-! ## Coefficient `RingHom` naturality (`eval`-pushing for the `MvPolynomial` encoding)

A ring hom `f : 𝕜 →+* 𝕜'` carries a `Chain n u` to a `Chain n (f u)` by mapping every block matrix
(`Matrix.map f`), and `suffix`/`Hmat` commute with `f` (matrix mul/add/smul are ring-hom-natural). This
is the bridge: the polynomial chain (over `MvPolynomial (Fin N) ℝ`) maps under `eval x` to the ℝ chain,
so the polynomial `Hmat 0` evaluates to the ℝ `Hmat 0` — the keystone for the named `UPolyGen`. -/

/-- `(u • M).map f = f u • M.map f` for a ring hom `f` on `𝕜`-entry matrices (the entry smul is `*`). -/
private theorem map_smul_eq {𝕜' : Type*} [CommRing 𝕜'] {p q : ℕ} (f : 𝕜 →+* 𝕜') (a : 𝕜)
    (M : Matrix (Fin p) (Fin q) 𝕜) : (a • M).map f = f a • M.map f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

/-- `(M + N).map f = M.map f + N.map f` for a ring hom `f` (entrywise). -/
private theorem map_add_eq {𝕜' : Type*} [CommRing 𝕜'] {p q : ℕ} (f : 𝕜 →+* 𝕜')
    (M N : Matrix (Fin p) (Fin q) 𝕜) : (M + N).map f = M.map f + N.map f := by
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]

/-- **The `f`-mapped chain** `c.map f : Chain n (f u)` — every block matrix pushed through the ring hom
`f`. Same widths; `step`/`base` transport by `Matrix.map_mul`/`map_add`/`map_smul_eq`. -/
noncomputable def map {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    Chain n (f u) where
  Wwid := c.Wwid
  Twid := c.Twid
  A := fun k => (c.A k).map f
  C := fun k => (c.C k).map f
  B := fun k => (c.B k).map f
  E := fun k => (c.E k).map f
  R := (c.R).map f
  step := by
    intro k hk
    have h2 := congrArg (fun M => M.map f) (c.step k hk)
    simp only at h2
    rw [Matrix.map_mul] at h2
    rw [show (c.B k * c.C (k + 1) + u • c.E k).map f
          = (c.B k).map f * (c.C (k + 1)).map f + f u • (c.E k).map f from by
        rw [map_add_eq f, Matrix.map_mul, map_smul_eq f u (c.E k)]] at h2
    exact h2
  base := by
    have h2 := congrArg (fun M => M.map f) c.base
    simp only at h2
    rw [show (u • c.R).map f = f u • (c.R).map f from map_smul_eq f u c.R] at h2
    exact h2

@[simp] theorem map_Wwid {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    (c.map f).Wwid = c.Wwid := rfl
@[simp] theorem map_Twid {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    (c.map f).Twid = c.Twid := rfl

/-- **`suffix` commutes with `f`**: `(c.map f).suffixAux d s h = (c.suffixAux d s h).map f`. By
downward induction on `d` (`suffixAux_succ` + `Matrix.map_mul`; base `Matrix.map_one`). -/
theorem suffixAux_map {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    ∀ d s (h : s + d = n),
      (c.map f).suffixAux d s h = (c.suffixAux d s h).map f := by
  intro d
  induction d with
  | zero =>
      intro s h
      have hs : n = s := by omega
      subst hs
      -- both `suffixAux 0 n _` reduce to `1 : Matrix (Fin (c.Wwid n)) (Fin (c.Wwid n))`
      rw [show (c.map f).suffixAux 0 n h
            = (1 : Matrix (Fin (c.Wwid n)) (Fin (c.Wwid n)) 𝕜') from by unfold suffixAux; rfl,
          show c.suffixAux 0 n h
            = (1 : Matrix (Fin (c.Wwid n)) (Fin (c.Wwid n)) 𝕜) from by unfold suffixAux; rfl,
          Matrix.map_one f (map_zero f) (map_one f)]
  | succ d ih =>
      intro s h
      rw [suffixAux_succ (c.map f) d s h, suffixAux_succ c d s h, Matrix.map_mul]
      congr 1
      exact ih (s + 1) (by omega)

/-- **`Hmat` commutes with `f`**: `(c.map f).HmatAux d s h = (c.HmatAux d s h).map f`. By downward
induction on `d` (`HmatAux_succ` + `Matrix.map_mul`/`map_add` + `suffixAux_map`; base = `R`). -/
theorem HmatAux_map {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    ∀ d s (h : s + d = n),
      (c.map f).HmatAux d s h = (c.HmatAux d s h).map f := by
  intro d
  induction d with
  | zero =>
      intro s h
      have hs : n = s := by omega
      subst hs
      rw [show (c.map f).HmatAux 0 n h = (c.map f).R from by unfold HmatAux; rfl,
          show c.HmatAux 0 n h = c.R from by unfold HmatAux; rfl]
      rfl
  | succ d ih =>
      intro s h
      rw [HmatAux_succ (c.map f) d s h, HmatAux_succ c d s h, map_add_eq f,
          Matrix.map_mul, Matrix.map_mul]
      congr 1
      · -- B_s · Hmat (s+1) block
        congr 1
        exact ih (s + 1) (by omega)
      · -- E_s · suffix (s+1) block
        congr 1
        unfold suffix
        exact suffixAux_map c f (n - (s + 1)) (s + 1) (by omega)

/-- **`Hmat 0` commutes with `f`**: `(c.map f).Hmat 0 _ = (c.Hmat 0 _).map f`. -/
theorem Hmat_zero_map {𝕜' : Type*} [CommRing 𝕜'] (c : Chain n u) (f : 𝕜 →+* 𝕜') :
    (c.map f).Hmat 0 (Nat.zero_le n) = (c.Hmat 0 (Nat.zero_le n)).map f := by
  unfold Hmat
  exact HmatAux_map c f (n - 0) 0 (by omega)

/-! ## The keystone telescoping -/

/-- **The chained-product telescope (keystone).** `C_s · suffix_s = u • Hmat_s` for every `s ≤ n`.
Proven by downward induction on the remaining length `d = n − s`: the base `s = n` is the terminal
condition `C_n = u • R`; the step rewrites `C_s · A_s` by the local identity `step`, pulls the scalar
through matrix multiplication (`Matrix.add_mul`/`mul_smul`/`smul_mul`/`mul_assoc`), and folds the
inductive hypothesis `C_{s+1} · suffix_{s+1} = u • Hmat_{s+1}`. -/
theorem chain_telescope (c : Chain n u) :
    ∀ d s (_ : s + d = n),
      c.C s * c.suffix s (by omega) = u • c.Hmat s (by omega) := by
  intro d
  induction d with
  | zero =>
      intro s hsd
      have hs : s = n := by omega
      subst hs
      rw [suffix_last, Hmat_last, Matrix.mul_one, c.base]
  | succ d ih =>
      intro s hsd
      have hlt : s < n := by omega
      have hih : c.C (s + 1) * c.suffix (s + 1) (by omega) = u • c.Hmat (s + 1) (by omega) :=
        ih (s + 1) (by omega)
      rw [suffix_succ c s hlt, Hmat_succ c s hlt]
      rw [← Matrix.mul_assoc, c.step s hlt]
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hih]
      rw [Matrix.mul_smul, ← smul_add]

/-- **The full-product divisibility** (the chart identity consumer's form): the product of ALL `n`
layers, premultiplied by `C_0`, is `u • Hmat_0`. The `s = 0` instance of `chain_telescope`. In the
chart instance `C_0 = 1` (the deepest factor is its own compressed transition), so this reads
`prod = u • H`. -/
theorem chain_telescope_zero (c : Chain n u) :
    c.C 0 * c.suffix 0 (Nat.zero_le n) = u • c.Hmat 0 (Nat.zero_le n) :=
  c.chain_telescope n 0 (by omega)

/-! ## Non-vacuity: a length-1 chain telescopes to `u • H`

A concrete `n = 1` chain with the binding shape `C_0 = 1`, `C_1 = u • R`, `B_0 = 0`, `E_0 = R`: the
single local identity `1 · A_0 = 0 · C_1 + u • R` forces `A_0 = u • R` (one radial pivot on the lone
layer — the `L = 1` / RRR achiever). The keystone then yields `suffix_0 = A_0 = u • R = u • Hmat_0`,
confirming the engine fires non-vacuously and reproduces the `prod = u·H` shape at `s = 0`. -/
example (u : ℝ) (R : Matrix (Fin 1) (Fin 1) ℝ) :
    True := by
  let c : Chain 1 u :=
    { Wwid := fun _ => 1, Twid := fun _ => 1
      A := fun _ => u • R
      C := fun k => if k = 0 then 1 else u • R
      B := fun _ => 0
      E := fun _ => R
      R := R
      step := by
        intro k hk
        obtain rfl : k = 0 := by omega
        simp
      base := by simp }
  -- the engine fires: `C_0 · suffix_0 = u • Hmat_0`, i.e. `1 · (u•R) = u • R`
  have : c.C 0 * c.suffix 0 (Nat.zero_le 1) = u • c.Hmat 0 (Nat.zero_le 1) :=
    Chain.chain_telescope_zero c
  trivial

end Chain

end DLNFibre.DLN.RLCT
