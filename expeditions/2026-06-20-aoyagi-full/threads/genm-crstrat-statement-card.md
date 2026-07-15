# genm-crstrat — statement card: composite-rank codim `CRrec` + the (I) deep gate

Branch `genm-crstrat` (off `origin/genm-sj5-capstone` @`12a7ae38a`). Module
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCompositeRank.lean`, first landed @`9794f441d`.
Discharges the (I) obligation of the Route-B deep gate (deepgate cert §1(A)/§6, codex answer §2).

---

## Card 1 — `CRrec` and its `s = 0` specialization

> **Claim.** The composite-rank codim `CR((v₀,…,v_p), s)` (parameter-space codim of
> `{rank(product) ≤ s}`), defined by peeling a layer, specialises to `minAdm` at `s = 0`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.CRrec` (def) and
>   `DLNFibre.DLN.RLCT.CRrec_zero_eq_minAdm`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCompositeRank.lean` @ `9794f441d`)
> - **Gloss.** `CRrec M s` recurses on chain arity: `Fin 1 ↦ 0`; `Fin 2` leaf ↦
>   `(M₀−s)(M₁−s)` (ℕ-truncated, the determinantal codim of `{rank ≤ s}` of one matrix);
>   `≥ 3` widths ↦ `min_{t ≤ min(M₀,M₁)} [(M₀−t)(M₁−t) + CRrec (redChain t M) s]` (peel the
>   FRONT layer). `CRrec_zero_eq_minAdm M : CRrec M 0 = minAdm M`.
> - **Proved.** Both, unconditionally, for every chain `M : Fin (L+1) → ℕ` and `s : ℕ`.
> - **Assumed.** none.
> - **Cited.** none.
> - **Deferred.** `CRrec` is the canonical CR def (controller decision 2026-07-15). It is the
>   HEAD-peel recursion; the cert states the LAST-peel recursion. The two are numerically
>   equal (65k cases, 0 fails — reversal symmetry of a rank locus), but the equality
>   `CRrec = CR_last` is NOT proved here (not needed: stepbuild's gate is abstract-param and
>   consumes `CRrec` directly). A `CRrec` reversal-symmetry lemma would close it if ever wanted.
> - **Status.** sorry-free + reviewed (crstrat-reviewer PASS; fidelity SURVIVED).

## Card 2 — THE (I) THEOREM

> **Claim.** Deep-rank stratification of the QIP: `minAdm M ≤ κ + minAdm(M₀,M₁,s)` where
> `κ = CR((M₂,…,M_last), s)`, for every `s`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.minAdm_le_compositeRank_add`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCompositeRank.lean` @ `9794f441d`)
> - **Gloss.** For `M : Fin (L+1+1+1+1) → ℕ` (≥ 4 widths) and `s : ℕ`:
>   `minAdm M ≤ CRrec (deepTail M) s + minAdm ![M 0, M 1, s]`, where
>   `deepTail M = fun i ↦ M i.succ.succ` is `(M₂, …, M_last)` and the arity-3 tail is the
>   concrete `![M 0, M 1, s] : Fin 3 → ℕ`.
> - **Proved.** The inequality, unconditionally, for every `M` (≥ 4 widths) and every `s : ℕ`
>   (numerically tight over `s ∈ [0, ρ]`; 72k cases, 0 fails).
> - **Assumed.** `M` has ≥ 4 widths (deep tail ≥ 2 widths). For a 3-width chain the deep tail is
>   a single width and the statement is false — this is the correct domain, not a gap.
> - **Cited.** none.
> - **Deferred.** none for (I). The full deep-gate `C_k ≥ minAdm(M) − ab` also needs the
>   companion (II) `minAdm(M₀,M₁,s) + γ_s ≤ ab + us` (stepbuild's, delivered separately) and the
>   γ_s/charge assembly (stepbuild). (I) is exactly the deep branch.
> - **Structure & ideas observed (deepgate cert + this build).** The bridge is head-peel
>   alignment: appending the peeled head width `t` at the TAIL (`Fin.snoc D t`) means head-peeling
>   the chain reduces the deep tail `D`'s FRONT while leaving `t` untouched — matching `CRrec`'s
>   head-peel step-for-step. The whole (I) reduces to the KEY lemma
>   `minAdm (Fin.snoc D t) ≤ t·s + CRrec D s` (`minAdm_snoc_le`), which is a clean arity
>   induction with a 3-chain base. Banked `minAdm_comp_perm` (permutation-invariance) supplies
>   `minAdm (Fin.cons t D) = minAdm (Fin.snoc D t)` (one cyclic perm, `Fin.snoc_eq_cons_rotate`);
>   banked `minAdmRec_three`/`gCrux` supply the 3-chain form.
> - **Route.** Head-peel CR (reuses `redChain`); KEY via snoc-append + `minAdm_comp_perm`; (I) via
>   head-peel of `minAdm M` + KEY at the 3-chain achiever pivot.
> - **Status.** sorry-free + reviewed (crstrat-reviewer PASS; fidelity SURVIVED).

---

**Consumed for `deepGate_branch` (stepbuild, abstract-param):** wire with κ = `CRrec (deepTail M) (ρ−k)`,
`a = M 0`, `b = M 1`, `s = ρ−k`; the arity-3 term is exactly `minAdm ![M 0, M 1, ρ−k]`. No bridge lemma.

**Axioms (forced `#print axioms`):** `minAdm_le_compositeRank_add`, `CRrec_zero_eq_minAdm`,
`minAdm_snoc_le`, `CRrec` all `[propext, Classical.choice, Quot.sound]`.
