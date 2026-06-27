import DLNFibre.DLN.RLCT.Validate.RouteMChartIdxCard
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction

/-!
# `RouteMChartIdx` — Phase B item 1: the chart-coordinate dimension count (`∑ roleDim = flatDim`)

The determinant-ready coordinatization's load-bearing arithmetic (item 1 of the det route, B+b1): the
per-boundary chart-coordinate roles (Schur `K`/`X`/`N`/`E`, chain lift `W`) sum, over the `L` boundaries
plus the radial, to `flatDim M = routeMAmbient M` — the cert's `ninputs = flatDim` (a genuine bijective
coordinatization, not the rate-side modular `flatIdxOf`).

The cardinality is a TELESCOPING identity (`tele_card`): per boundary `s` the Schur roles
`K+X+N+E = (t_s+r_s)(t_s+c_s) = t_{s-1}·M_s` (`roleSquare_eq`, via the `K_s` block's `t²` = LDU
`low/diag/up` from `lduRole_card`), the chain lift `W_s = c_s·M_{s+1}`; the `t_s` middle sums cancel and
`t_0 = M_0` closes it. The `+1` radial and `−1` fixed residual cancel.

* `tele_card` — the abstract telescoping `∑ t_k·M_{k+1} + ∑ c_k·M_{k+2} = ∑ M_k·M_{k+1}` (the spine).
* `roleSquare_eq` — `(t_s+r_s)(t_s+c_s) = t_{s-1}·M_s` (the Schur per-boundary role count).
* `chartDim_eq_flatDim` — `(∑ roleDim) + 1 − 1 = flatDim M` (the coordinate count, range form).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (arithmetic + finite cardinality; no analysis).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The abstract telescoping spine -/

/-- **The telescoping card identity.** For widths `M, t : ℕ → ℕ` with `t 0 = M 0` and `t (k+1) ≤ M (k+1)`,
the boundary Schur-role sum `∑_{k<L} t_k·M_{k+1}` plus the chain-lift sum `∑_{k<L−1} (M_{k+1}−t_{k+1})·M_{k+2}`
equals the layer-product sum `∑_{k<L} M_k·M_{k+1}` (`= flatDim`). The `t_k` middle sums cancel; `t_0 = M_0`
closes the boundary. The spine of `chartDim_eq_flatDim`. -/
theorem tele_card (M t : ℕ → ℕ) (h0 : t 0 = M 0)
    (hc : ∀ k, t (k + 1) ≤ M (k + 1)) :
    ∀ L, 0 < L →
    (∑ k ∈ Finset.range L, t k * M (k + 1))
        + (∑ k ∈ Finset.range (L - 1), (M (k + 1) - t (k + 1)) * M (k + 2))
      = ∑ k ∈ Finset.range L, M k * M (k + 1) := by
  intro L
  induction L with
  | zero => omega
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [h0]
      · have ihn := ih hn
        rw [Finset.sum_range_succ (fun k => t k * M (k + 1)) n,
            show (n + 1) - 1 = (n - 1) + 1 by omega,
            Finset.sum_range_succ (fun k => (M (k + 1) - t (k + 1)) * M (k + 2)) (n - 1),
            Finset.sum_range_succ (fun k => M k * M (k + 1)) n, show n - 1 + 1 = n by omega,
            show n - 1 + 2 = n + 1 by omega]
        have hsplit : t n * M (n + 1) + (M n - t n) * M (n + 1) = M n * M (n + 1) := by
          have hle : t n ≤ M n := by cases n with | zero => omega | succ m => exact hc m
          rw [← Nat.add_mul]; congr 1; omega
        have e1 : (∑ k ∈ Finset.range n, t k * M (k + 1)) + t n * M (n + 1)
              + ((∑ k ∈ Finset.range (n - 1), (M (k + 1) - t (k + 1)) * M (k + 2))
                  + (M n - t n) * M (n + 1))
            = ((∑ k ∈ Finset.range n, t k * M (k + 1))
                + (∑ k ∈ Finset.range (n - 1), (M (k + 1) - t (k + 1)) * M (k + 2)))
              + (t n * M (n + 1) + (M n - t n) * M (n + 1)) := by ring
        rw [e1, ihn, hsplit]

/-! ## The per-boundary Schur-role count -/

/-- **The Schur per-boundary role count** `(t_s + r_s)(t_s + c_s) = t_{s-1}·M_s` where `r_s = t_{s-1} − t_s`,
`c_s = M_s − t_s` (`t_s ≤ t_{s-1}`, `t_s ≤ M_s`). The `K_s`(`t_s²`) + `X_s`(`r_s·t_s`) + `N_s`(`t_s·c_s`)
+ `E_s`(`r_s·c_s`) roles. -/
theorem roleSquare_eq {ts tprev Ms : ℕ} (h1 : ts ≤ tprev) (h2 : ts ≤ Ms) :
    ts * ts + (tprev - ts) * ts + ts * (Ms - ts) + (tprev - ts) * (Ms - ts) = tprev * Ms := by
  have hr : tprev - ts + ts = tprev := by omega
  have hcc : Ms - ts + ts = Ms := by omega
  nlinarith [hr, hcc, Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]

/-! ## The chart-coordinate dimension = flatDim (range form) -/

/-- **The chart-coordinate count = `flatDim M`** (range form, the cert's `ninputs = flatDim`). With the
descent path `t : ℕ → ℕ` (`t 0 = M 0`, weakly decreasing, `t (k+1) ≤ M (k+1)`), the per-boundary
`roleDim k = (t_k+r_k)(t_k+c_k) + (chain-lift W)` sums (with `+1` radial `−1` fixed residual) to
`flatDim M`. Combines `roleSquare_eq` (per-boundary Schur roles) + the `tele_card` telescoping +
`flatDim_eq`. The role count `(t_k+r_k)(t_k+c_k) = t_k·M_{k+1}` IS the `tele_card` summand. -/
theorem chartDim_eq_flatDim (M : Fin (L + 1) → ℕ) (t : ℕ → ℕ)
    (h0 : t 0 = M 0) (hc : ∀ k, t (k + 1) ≤ (Wext M) (k + 1)) (hL : 0 < L) :
    ((∑ k ∈ Finset.range L, t k * (Wext M) (k + 1))
        + (∑ k ∈ Finset.range (L - 1), ((Wext M) (k + 1) - t (k + 1)) * (Wext M) (k + 2)))
      = flatDim M := by
  rw [tele_card (Wext M) t (by rw [h0]; simp [Wext]) hc L hL, flatDim_eq]
  -- `∑_{k<L} (Wext M) k · (Wext M) (k+1) = ∑_{s:Fin L} M_{castSucc}·M_{succ}` (both `M_k·M_{k+1}`).
  rw [Finset.sum_range fun k => (Wext M) k * (Wext M) (k + 1)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Wext_apply M s.val (by omega), Wext_apply M (s.val + 1) (by omega)]
  congr 1 <;> · apply congrArg; apply Fin.ext; simp [Fin.castSucc, Fin.succ]

end DLNFibre.DLN.RLCT
