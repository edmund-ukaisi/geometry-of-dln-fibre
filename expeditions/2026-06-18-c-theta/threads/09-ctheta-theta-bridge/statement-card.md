# Statement card — CThetaThetaBridge: `θ` at the Kostant layer (`numTop d 0 = cTheta d`)

Module `lean/DLNFibre/Core/CThetaThetaBridge.lean` (new file, imports `Core.CThetaValue` +
`Core.CThetaQIPConverse`). Closes the layer gap flagged on PR #3: the QIP-layer count
`qipNumMinimisers_eq_cTheta` counts `Gqip`-minimisers `e`, but the paper's `θ` is the **Kostant-side**
component count `numTop d 0` (`Core.CTheta`). This file proves they agree, so the paper's `θ` is the
closed form `cTheta d`. Import appended to `DLNFibre.lean` (single-writer, at end). Sorry-free,
axiom-clean (`propext, Classical.choice, Quot.sound`). Commit `ecef4cc`.

**Scope (name = content).** This is the **combinatorial** `θ`: a minimiser count of a ℤ-quadratic
form over Kostant partitions. The geometric reading (`θ` = number of top-dimensional components of
`Σ⁰`) rides on the deferred Voigt hypothesis (`hVoigt`, `Core.OrbitCodim`), exactly as in
`Core.CTheta` and the QIP tide; nothing here asserts it. The bridge **reuses** the existing C-side
`m ↔ e` correspondence (`mOfE`/`eOfm`, `Core.CThetaQIP`/`Core.CThetaQIPConverse`) — no new heavy
machinery; the only new lemma is the right-inverse `eOfm (mOfE d e) = e` (`eOfm_mOfE`, a one-liner)
plus a nonemptiness bridge.

**Notation.** `mOfE d e` = horizontal-lace multiplicity array of feasible `e` (`Core.CThetaQIP`);
`eOfm m i = m (0, i.castSucc)` (`Core.CThetaQIPConverse`), the inverse on HL partitions; `IsHL m` =
`m` vanishes on every interior interval; `cTheta d = C(qipM d, |qipDelta d|)`.

---

> **Claim (θ Kostant-layer closed form, Thm 7.10 `r=0`).** For `Monotone d`, the Kostant-side
> component count `numTop d 0` equals `θ = C(m, |δ|) = cTheta d`.
>
> - **Lean:** `numTop_zero_eq_cTheta (d) (hd : Monotone d) (hk : (kostantPartitions d 0).Nonempty) :`
>   `numTop d 0 hk = cTheta d`.
> - **Gloss / proof.** `numTop d 0 hk` is the number of Kostant partitions of `d` with corner `0`
>   whose `codimForm` attains the minimum `cCodim d 0 hk`. The proof rewrites it to the QIP-minimiser
>   count (`numTop_zero_card_eq_qipNumMinimisers`) and applies the proved
>   `qipNumMinimisers_eq_cTheta`. The count equality is a `Finset.card_bij'` between the two filtered
>   minimiser sets, forward `m ↦ eOfm m`, inverse `e ↦ mOfE d e`:
>   - a Kostant minimiser `m` is horizontal-lace (`minimiser_isHL`), hence `mOfE d (eOfm m) = m`
>     (`mOfE_surj_of_hl`, whose surjectivity witness *is* `eOfm m`), so `eOfm m` is feasible and
>     `codimForm m = codimForm (mOfE d (eOfm m)) = Gqip d (eOfm m)` (`codimForm_mOfE`);
>   - a QIP minimiser `e` gives `mOfE d e ∈ kostantPartitions d 0` (`mOfE_mem`) with `codimForm = Gqip`;
>   - the two minimiser predicates agree because `cCodim d 0 = qipMin d` (`cCodim_eq_qipMin`);
>   - round trips: `mOfE d (eOfm m) = m` (above), `eOfm (mOfE d e) = e` (`eOfm_mOfE`, the low column of
>     `mOfE` reads `e` back).
> - **Proved.** Full equality `numTop d 0 = cTheta d`, all combinatorial. **Hypothesis:** `Monotone d`
>   (load-bearing — `cCodim_eq_qipMin`, `minimiser_isHL`, `mOfE_surj_of_hl` all need it) + Kostant set
>   nonempty (`hk`). The QIP-side `Nonempty` is supplied by the bridge
>   `kostant_nonempty_iff_qipFeasible_nonempty`.
> - **Assumed / Cited.** none.
> - **Deferred.** The geometric reading `θ = #{top components of Σ⁰}` (rides on `hVoigt`, as upstream).
> - **Status.** sorry-free.

> **Claim (minimiser-count bridge).** For `Monotone d`, the number of Kostant minimisers equals the
> number of QIP minimisers.
>
> - **Lean:** `numTop_zero_card_eq_qipNumMinimisers (d) (hd : Monotone d)`
>   `(hk : (kostantPartitions d 0).Nonempty) (hne : (qipFeasible d).Nonempty) :`
>   `((kostantPartitions d 0).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d 0 hk)).card`
>   `= ((qipFeasible d).filter (fun e ↦ Gqip d e = qipMin d hne)).card`.
> - **Proved.** The value-preserving bijection above (`Finset.card_bij'`). **Deferred / Cited / Assumed.**
>   none beyond `Monotone d` + the two nonemptiness hypotheses.

> **Claim (nonemptiness bridge).** For `Monotone d`, `(kostantPartitions d 0).Nonempty ↔`
> `(qipFeasible d).Nonempty`.
>
> - **Lean:** `kostant_nonempty_iff_qipFeasible_nonempty (d) (hd : Monotone d) :`
>   `(kostantPartitions d 0).Nonempty ↔ (qipFeasible d).Nonempty`.
> - **Proved.** `→` sends `m ↦ eOfm m` (feasible by `kostantAt … 0`, corner-`0` dropping the last
>   term — holds for every Kostant `m`, no HL); `←` sends `e ↦ mOfE d e` (`mOfE_mem`).

---

## Witnesses (in-file, axiom-clean)

- `numTop_zero_eq_cTheta_d222 : numTop d222 0 _ = cTheta d222` and `numTop_zero_d222_eq_one`
  (`= 1`): the paper's Ex 4.3 component count `θ = 1` for `(2,2,2)`, now the closed form.
- `numTop_zero_eq_cTheta_d639 : numTop d639 0 _ = cTheta d639` and `numTop_zero_d639_eq_four`
  (`= 4`): the paper's Ex 6.3 rearrangement `θ = 4`. Kostant-nonemptiness for `d639` comes via
  `qipFeasible_d639_nonempty` (`e = (8,0,…,0)`) + the nonemptiness bridge.

All five delivered theorems print `[propext, Classical.choice, Quot.sound]`.

## What fought back

- The `Finset.card_bij'` goals arrive with the bijection lambda **unreduced**
  (`(fun m _ ↦ eOfm m) m hm`), so `rw`/`mem_filter` did not fire — fixed with a `change` to the
  beta-reduced membership goal in each of the four branches.
- `qipFeasible_d639_nonempty` via the noncomputable `qipWitness` timed out at `whnf`; replaced with an
  explicit feasible `e = ![8,0,…,0]` closed by `decide +kernel`.
- `minimiser_isHL` takes `codimForm = cCodim` directly (not `.symm`); the filter predicate already has
  that orientation.
