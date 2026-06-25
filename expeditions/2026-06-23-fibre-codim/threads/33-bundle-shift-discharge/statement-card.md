# Statement card — G4: discharge `BundleShiftInterface` from Core

The expedition's closing rung. The rank-`r` RLCT payoff carried the geometric bundle shift
`codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` as the **Assumed** field `cited_bundle_shift` of
`BundleShiftInterface`. That codimension identity is in fact PROVED zero-cite in
`Core.FibreCodimFinal`. This thread discharges the interface, so the payoff rests on ONLY the Cited
Aoyagi `RlctInterface`.

---

> **Claim.** The geometric bundle shift is a theorem of `Core`, not a carried hypothesis: there is a
> proved `BundleShiftInterface d K ι` instance. Hence the rank-`r` RLCT payoff
> `rlct(K^DLN_B) = (cCodim d r + r(d_0+d_N−r))/2` holds with the **only** carried dependency being
> `I : RlctInterface` (the Cited Aoyagi `rlct = ½·codim`).
>
> - **Lean:** `DLNFibre.DLN.bundleShift_of_core`, `DLNFibre.DLN.rlct_lossDLN_eq_half_cCodim_add_shift`,
>   `DLNFibre.DLN.Matrix.rank_map_eq_of_injective`, `DLNFibre.DLN.rlct_lossDLN_d222_one_eq_two`
>   (`lean/DLNFibre/DLN/BundleShiftDischarge.lean` @ `b41b305e`)
> - **Gloss.**
>   - `Matrix.rank_map_eq_of_injective B ι hι : (B.map ι).rank = B.rank` — for an injective ring hom
>     `ι : R →+* S` between fields, entrywise `Matrix.map` preserves rank.
>   - `bundleShift_of_core d K ι : BundleShiftInterface d K ι` — a proved instance whose
>     `cited_bundle_shift` field (the geometric shift `codim (fibre (B.map ι)) = codim Σ̄^r + δ`,
>     `δ = r(d_0+d_N−r)`, for rank-`r` `B`, `0 < N`, `∀ k, r ≤ d k`) is derived from
>     `Core.FibreCodimFinal.codimRepCanonical_fibre_eq_cCodim_add_shift`.
>   - `rlct_lossDLN_eq_half_cCodim_add_shift I hN hB hr h : I.rlct (lossDLN d B) = (cCodim d r h + δ)/2`
>     — the rank-`r` payoff carrying ONLY `I : RlctInterface` (no `J`).
>   - `rlct_lossDLN_d222_one_eq_two I hB : I.rlct (lossDLN d222 B) = 2` — the `(2,2,2)`, `r = 1` witness.
> - **Proved (zero-cite).**
>   - Rank-preservation `(B.map ι).rank = B.rank`, via the in-repo determinantal-rank bridge
>     `Core.rank_le_iff_forall_submatrix_det_eq_zero` + `RingHom.map_det` + `map_eq_zero_iff` (ι
>     injective ⟹ `ι x = 0 ↔ x = 0`).
>   - The whole geometric half (`bundleShift_of_core.cited_bundle_shift`): the `N = M+1` index
>     reconciliation (`Fin (N+1)` defeq `Fin (M+2)`), Kostant-nonemptiness
>     (`Core.kostantPartitions_nonempty_of_le`), Brick A (`codim Σ̄^r = cCodim`), and the Core central
>     identity `codim (fibre (B.map ι)) = cCodim + δ`. `#print axioms bundleShift_of_core` =
>     `[propext, Classical.choice, Quot.sound]`.
> - **Assumed.** In the rewired payoff, the lone carried hypothesis is `I : RlctInterface` (see Cited).
>   The bundle shift is no longer assumed.
> - **Cited.** The Aoyagi analytic equality `rlct(K^DLN_B) = ½·codim mult⁻¹(B)` (Aoyagi Thm 1 /
>   LR Thm 8.6), carried as the field `I.cited_aoyagi_dln`. It is a typed hypothesis, **not** an
>   axiom: `#print axioms rlct_lossDLN_eq_half_cCodim_add_shift` =
>   `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `BundleShiftInterface` or
>   `RlctInterface` as an axiom).
> - **Deferred.** none for the geometric half. Scope note: the discharge is at `K : Type` (universe
>   `0`) — the Core codim identity is itself `Type 0` (the Schur-side no-drop fixes the index type at
>   `Type 0`); the RLCT story lands at `ℂ` / `AlgebraicClosure ℚ`, both `Type 0`. LR Lemma 4.6's
>   locally-trivial-bundle / component-count / smoothness content beyond the codimension identity is
>   separate (not in scope here).
> - **Status.** sorry-free; awaiting reviewer fidelity check.

---

## Reconciliations (the three wrinkles the discharge pins)

1. **Indexing.** Payoff/interface use `d : Fin (N+1) → ℕ` under `0 < N`; `Core.FibreCodimFinal` uses
   `d : Fin (M+2) → ℕ`. `obtain ⟨M, rfl⟩ : ∃ M, N = M+1` makes `Fin (N+1)` **defeq** `Fin ((M+1)+1) =
   Fin (M+2)` — no transport cast. `Fin.last N`, `d 0` align definitionally; the shift differs only by
   `Nat.add_comm` inside the subtraction (`d_0 + d_N` vs `d_N + d_0`).
2. **Base-change ℝ→K.** Need `(B.map ι).rank = r` from `B.rank = r`; `Matrix.rank_map_eq_of_injective`
   (the determinantal-minors route — no algebra instance, no tensor base change).
3. **Kostant-nonempty.** `(kostantPartitions d r).Nonempty` from `0 < N` + `∀ k, r ≤ d k` via
   `Core.kostantPartitions_nonempty_of_le`.
