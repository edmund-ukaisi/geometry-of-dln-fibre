# Statement card — drop-to-m active-support reduction (the wall)

Module `lean/DLNFibre/Core/CThetaDropM.lean` (new file, imports `Core.CThetaExplicit`). The **wall**
of the explicit-formula tail (Lehalleur–Rimányi Thm 7.10, `r = 0`): a `Φ`-minimiser on the QIP
feasible face is supported on the first `m` coordinates only, where `m` is an explicit antitone
arithmetic threshold. Transcribed from the proven + Codex-audited certificate
`threads/06-drop-to-m/certificate.md`. Import appended to `DLNFibre.lean` (single-writer). Commit
`fa7ca6e`.

**Scope (name = content).** This is the **support reduction** in isolation: minimisers of
`Φ(e) = ∑_i (e_i − s_i)²` on `{∑ e = d_0}` vanish past index `m`. It does **not** assemble the
closed-form `C`, does **not** do the rounding/value-assembly on the `m`-face, and does **not** touch
`cCodim`/`qipMin`. `Φ` is the square-completion target of `Core.CThetaExplicit.two_Gqipℤ_sub_sq`
(`s_i = qipShift d i = d_0 − d_{i+1}`); the link `min Gqip ⇔ min Φ` on the feasible face is the
algebra already in `CThetaExplicit`, not re-proved here. No geometric (Voigt) content.

**Index discipline (load-bearing).** Lean `e i` = paper `e_{i+1}`; paper "`e_i = 0` for `i > m`"
becomes 0-based `e i = 0` for `i ≥ m`. The threshold `m` is 0/1-based the same way as the paper's `l`
(`A_l`, `l ∈ {1,…,N}`); the conclusion's source coordinate `k ≥ m` (0-based) is paper `k+1 > m`.

---

> **Claim (threshold well-definedness, Lemma 1).** For `Monotone d`, `A_l := (∑_{i=0}^l d_i) − l·d_l`
> is non-increasing with `A_1 = d_0 ≥ 0`, so `{l ≤ N : A_l ≥ 0}` is a nonempty prefix and
> `m := max` of it is well-defined with `1 ≤ m ≤ N`.
>
> - **Lean:** `qipA` (`= A_l`, clamped index `min l N`), `qipPred d l := 0 ≤ qipA d l` (with the
>   `DecidablePred` instance), `qipM d := Nat.findGreatest (qipPred d) N`. Facts: `qipA_one`
>   (`A_1 = d_0`), `qipPred_one`, `qipM_ge_one` (`1 ≤ m`), `qipM_le` (`m ≤ N`), `qipPred_qipM`
>   (`Pred m`), `not_qipPred_of_gt_qipM` (`¬Pred l` for `m < l ≤ N`).
> - **Gloss.** `qipM` is `Nat.findGreatest` of the decidable predicate; the prefix structure is read
>   off `Nat.findGreatest`'s `_spec` / `_is_greatest` / `le_findGreatest` API. The antitone identity
>   `A_{l+1} = A_l − l(d_{l+1}−d_l)` of the certificate is **not** separately stated — `findGreatest`
>   gives `Pred m ∧ (∀ m<l≤N, ¬Pred l)` directly, which is all the downstream proof needs (the
>   antitone fact was the certificate's route to *characterise* `m`, not a Lean obligation).
> - **Proved.** Well-definedness via `findGreatest`. `qipA_one`/`qipM_ge_one` need `1 ≤ N`.
> - **Assumed / Cited / Deferred.** none.

> **Claim (separation, Lemma 2).** If `m < N` then `m · d_{m+1} > S` where `S := ∑_{i=0}^m d_i`;
> integer form `S + 1 ≤ m · d_{m+1}` (i.e. `m·d_{m+1} − S ≥ 1`).
>
> - **Lean:** `qip_separation d (hm : qipM d < N) : qipS d + 1 ≤ (qipM d : ℤ) * d ⟨qipM d + 1, _⟩`,
>   via `qipA_succ_qipM` (`A_{m+1} = S − m·d_{m+1}`) and `not_qipPred_of_gt_qipM` (`A_{m+1} < 0`).
>   `qipS d := ∑_{i ∈ range (m+1)} d_i` (clamped).
> - **Proved.** The strict integer inequality, no division. It is exactly the negation of `Pred(m+1)`.
> - **Assumed.** `m < N` (else `m+1 > N`, the bound is vacuous — and there is no drop). **Cited /
>   Deferred.** none.

> **Claim (the wall — strict-decrease transfer).** For `Monotone d` and feasible `e`, if some 0-based
> `k ≥ m` has `e_k ≥ 1`, the explicit unit transfer `k → j` (`j = argmin_{i<m} u_i`,
> `u_i = e_i − d_0 + d_{i+1}`) gives a feasible `e'` with `Φ(e') < Φ(e)`.
>
> - **Lean:** `qip_unit_transfer_decreases d hd e (hfeas) {k} (hk : qipM d ≤ k) (hek : 1 ≤ e k) :`
>   `∃ e' ∈ qipFeasible d, Phi d (↑e') < Phi d (↑e)`. Construction `qipTransfer e j k :=`
>   `update (update e j (e j + 1)) k (e k − 1)`; `j` from `Finset.exists_min_image` over
>   `qipLow d := {i | i < m}` (`qipLow_nonempty`, `qipLow_card = m`).
> - **Gloss / proof (certificate §3, 6 steps).** (1) `m < N` from `k < N`, `m ≤ k`. (2) argmin `j`,
>   `j < m ≤ k` so `j ≠ k`. (3) `e'` feasible (`sum_eq_of_two_point`, ℤ-cast — `e_k ≥ 1` so no ℕ
>   truncation). (4) cost change `Φ(e') − Φ(e) = 2(u_j − u_k + 1)` (`sum_eq_pair_of_zero` + `ring`).
>   (5) gap `u_k − u_j ≥ 2`: min-≤-average `m·u_j ≤ ∑_{qipLow} u` (`card_nsmul_le_sum`, integer, no
>   divide); `∑_{qipLow} u = (∑_{qipLow} e) + (S − d_0) − m·d_0` (`sum_qipLow_dsucc`);
>   `∑_{qipLow} e ≤ d_0` (non-truncated feasibility `∑_all e = d_0`, `e ≥ 0`), giving
>   `m·u_j ≤ S − m·d_0`; `m·u_k ≥ m(1 − d_0 + d_{m+1})` (`e_k ≥ 1`, `d_{k+1} ≥ d_{m+1}`); combine with
>   `qip_separation` to get `m(u_k − u_j) ≥ m+1`, then `m ≥ 1 ⟹ u_k − u_j ≥ 2`. (6) `Φ(e') − Φ(e) ≤
>   −2 < 0`.
> - **Proved.** The strict decrease, exactly the certificate's algebra. All in ℤ.
> - **Assumed / Cited / Deferred.** none.

> **Claim (drop-to-m).** For `Monotone d`, every `Φ`-minimiser `e` on `{∑ e = d_0}` has `e_i = 0` for
> every 0-based `i ≥ m`.
>
> - **Lean:** `qip_minimiser_support_le_m d hd e (hfeas)`
>   `(hmin : ∀ e'' ∈ qipFeasible d, Phi d (↑e) ≤ Phi d (↑e'')) : ∀ i, qipM d ≤ (i:ℕ) → e i = 0`.
> - **Gloss.** `by_contra`: `e i ≠ 0 ⟹ e i ≥ 1 ⟹ qip_unit_transfer_decreases ⟹ ∃ e'` feasible with
>   `Φ(e') < Φ(e)`, contradicting `hmin e'`.
> - **Proved.** The support bound, conditional on `e` being a minimiser. The reduction is to the
>   `m`-face. **Deferred (ordering obligation, recorded next to the rounding lemma):** the rounding /
>   value-assembly closed form must be stated on the `m`-face (`i < m`) only and run AFTER this — the
>   certificate's §4 boundary witnesses `d'=(4,5,8,9,10,10)`, `(2,5,6,7,10)` break a "nonneg ⟹ support"
>   shortcut on all `N` coords.

> **Claim (witnesses, non-vacuity).** `m` fires at concrete data: `(2,2,2)` has `m = N = 2` (no drop);
> Ex 6.3 `(8,8,11,11,11,13,13,13,15)` has `m = 4` (the drop) with strict separation `4·13 = 52 > 49`.
>
> - **Lean:** `qipM_d222_eq_two` (`= 2`, `decide +kernel`), `d639` + `d639_monotone`,
>   `qipM_d639_eq_four` (`= 4`, `decide +kernel`), `qip_separation_d639` (the integer separation at
>   `d639`, from `qip_separation`).
> - **Proved.** All four. The Ex 6.3 separation `qipS d639 + 1 ≤ 4 · d639_5` is the instantiated
>   `qip_separation`.
> - **Assumed / Cited / Deferred.** none.

---

## Audit

- `lean/scripts/sorries` → no sorry in `CThetaDropM` (whole-library gate unchanged).
- `lake build` green (2083 jobs); `lake build DLNFibre.Core.CThetaDropM` green, no linter warnings in
  the file.
- `#print axioms` on `qip_unit_transfer_decreases`, `qip_minimiser_support_le_m`, `qip_separation`,
  `qipM_d222_eq_two`, `qipM_d639_eq_four`: only `propext`, `Classical.choice`, `Quot.sound` (no
  `native_decide`).
- Numerics (certificate §6, exact integer): Ex 6.2 `(2,2,2)` `m=N=2` no drop; Ex 6.3
  `m=4`, separation `52>49`, brute minimisers all drop `e_i (i>4)`; support-drop verified over 3000
  random `d'` (0 violations), unit-transfer decrease over 11336 points (0 failures), gap chain over
  30000 (0 failures).
- Fidelity review (Lean ↔ informal claim): **PASS** (reviewer, 2026-06-18; decorrelated Codex on the
  index discipline Q2 and the `card_nsmul_le_sum` min-≤-average step). All six checks survived: (1)
  `Phi` matches `two_Gqipℤ_sub_sq`'s target with `s_i = d_0 − d_{i+1}` (the committed `Gqip`
  indexing); (2) index discipline correct — `i ≥ m` (0-based) is the unique non-vacuous threshold,
  brute-checked against the Ex 6.3 minimisers (boundary coord `e_4 = 0` dropped, `e_3 ≠ 0` kept); (3)
  `qipM`/`qipA`/`qipPred` faithful, the `min l N` clamp is identity on `l ≤ N` and never alters
  `findGreatest`; (4) `qipS = S`, separation is the correct division-free integer form; (5) `Monotone
  d` + feasibility the exact hypotheses, `m < N` *derived* not assumed, minimiser hypothesis on the
  right domain, gap chain matches line-for-line (Codex confirmed no division/rounding artefact); (6)
  build green, axioms clean, zero sorry. Scoping honest (Φ-minimisers, not `qipMin`/`cCodim`). No
  discrepancies. Codex artefact: `threads/06-drop-to-m/codex/fidelity-review-{prompt,answer}.md`.
- **Status: sorry-free + reviewed.**

## Judgement calls / deviations from the certificate

- **`Φ` as the object, not `Gqip`.** The certificate states §1–§4 for `Φ(e) = ∑(e_i − s_i)²`; I define
  `Phi d e := ∑ (e i − qipShift d i)²` over `e : Fin N → ℤ` (so `ring` works) and state the wall on
  cast ℕ-vectors `Phi d (↑e)`. The `min Gqip ⇔ min Φ` link (`two_Gqipℤ_sub_sq`) lives in
  `CThetaExplicit`; not re-proved here. Downstream value-assembly must compose the two.
- **`m` via `Nat.findGreatest`, antitone fact dropped.** The certificate's `A_{l+1} ≤ A_l`
  monotonicity is its *route* to well-definedness; `Nat.findGreatest` supplies `Pred m` and
  `¬Pred l (m<l≤N)` directly, which is all the separation + wall need, so `qipA_antitone` is not in
  the file (no obligation lost). `qipA` clamps the index (`min l N`) to stay total in `l : ℕ`.
- **Argmin over `qipLow := {i : Fin N | i < m}`** (a filter of `univ`), card `= m` via `attachFin`;
  `Finset.exists_min_image` for `j`. The min-≤-average step is `card_nsmul_le_sum` (`m • u_j ≤ ∑`),
  kept in ℤ — the certificate's flagged most-likely-to-break point; the `∑_{qipLow} e ≤ d_0` bound
  uses the non-truncated `∑_all e = d_0`.
- **Two reusable sum-surgery helpers** (`sum_eq_of_two_point`, `sum_eq_pair_of_zero`) factored for the
  feasibility and cost-change steps; not lifted to shared `Core` API (first use).
