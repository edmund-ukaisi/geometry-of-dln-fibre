**Q1**
[FACT] Define the extended survivor vector
\[
\rho_{M,T}(0)=M_0,\qquad \rho_{M,T}(j+1)=T_j.
\]
The independent achiever target should be the total rank-pattern function
\[
r^*_{M,T}(i,j)=
\begin{cases}
0,& i>j,\\
M_i,& i=j,\\
T_{j-1},& i<j.
\end{cases}
\]
This uses only `M` and `T`, not `cascadeTuple`.

```lean
def expSurvivor (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Fin (L + 1) → ℕ
  | ⟨0, _⟩ => M 0
  | ⟨n+1, hn⟩ => T ⟨n, Nat.lt_of_succ_lt_succ hn⟩

def achieverRankPattern
    (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) :
    Fin (L + 1) → Fin (L + 1) → ℕ :=
  fun i j =>
    if i < j then expSurvivor M T j
    else if i = j then M i
    else 0
```

[FACT] The prefix row is:
```lean
achieverRankPattern M T 0 0 = M 0
achieverRankPattern M T 0 j.succ = T j
```

[INFERENCE] If by `r*` you mean the generic full rank pattern of all tuples with prefix ranks `T`, then `T` alone is not enough. The definition above is the canonical column-constant completion that the diagonal cascade is meant to realize.

**Q2**
[FACT] The cascade survivor counts are exactly
\[
t^*_s=T^*_s\qquad(s:\mathrm{Fin}\ L).
\]
Do not use `tPrev`; the prepended value `M 0` belongs only to the extended prefix row `ρ`, not to the cascade input.

```lean
def IsAchiever (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) : Prop :=
  T ∈ Adm M ∧
    Mval M T = (Adm M).inf' (Adm_nonempty M) (Mval M)

theorem rankFn_cascadeTuple_eq_achieverRankPattern
    {k : Type u} [Field k]
    (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ)
    (hT : T ∈ Adm M) :
    rankFn (k := k) M (cascadeTuple (k := k) M T) =
      achieverRankPattern M T := by
  -- real proof obligation
  sorry

theorem rankFn_cascadeTuple_eq_rStar_of_achiever
    {k : Type u} [Field k]
    (M : Fin (L + 1) → ℕ) (Tstar : Fin L → ℕ)
    (hAch : IsAchiever M Tstar) :
    rankFn (k := k) M (cascadeTuple (k := k) M Tstar) =
      achieverRankPattern M Tstar :=
  rankFn_cascadeTuple_eq_achieverRankPattern M Tstar hAch.1
```

[FACT] The `Mval = minAdm` part is not used in the cascade equality; admissibility is the needed hypothesis. It is included only to say this admissible `Tstar` is the learning-coefficient achiever.

[FACT] Especially:
```lean
rankFn (k := k) M (cascadeTuple (k := k) M Tstar) 0 j.succ = Tstar j
```
for `j : Fin L`, after rewriting by the equality above.

**Q3**
[FACT] `admPred` forces the extended survivor vector to be weakly decreasing:
`T 0 ≤ min (M 0) (M 1) ≤ M 0`, and `i ≤ j → T j ≤ T i`. Hence
\[
\rho_0 \ge \rho_1 \ge \cdots \ge \rho_L.
\]

[FACT] Therefore every admissible window minimum over `(i,j]` is the right endpoint:
\[
\min_{i<s\le j}\rho_s=\rho_j.
\]
So a witness with a strict interior window minimum below both endpoints cannot exist for an admissible achiever. If you find one, it violates the committed `admPred` convention or uses a cascade input not equal to `T`.

[INFERENCE] A non-degenerate witness should instead stress: `L ≥ 3`, some interior nonzero rank `T (j-1) > 0` with `0 < i < j < L+1`, at least one strict positive drop before the forced final zero, and preferably an increasing width step `M s < M (s+1)` so the proof must derive source-size feasibility from monotonicity, not just from the direct bound.

[FACT] Degenerate cases: `T = 0`, `L ≤ 2`, or only final-zero behavior test almost nothing beyond prefix membership. They can make the false vacuity citation look adequate by coincidence.