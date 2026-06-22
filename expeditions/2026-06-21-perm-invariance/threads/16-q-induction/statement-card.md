# Statement card — Thm 5.6 (the "fivegon") + the (Q) q-series induction

Thread 16 (perm-invariance expedition). The last open node of the fivegon: `fivegonSum d = Pmult d`,
the corner-free generating identity over **all** Kostant partitions of `d`. Reached via the (Q)
inner-sum q-series induction.

> **Claim (fivegon, Thm 5.6).** Over `ℤ⟦X⟧`, for every dimension vector `d : Fin (N+1) → ℕ`,
> `fivegonSum d = Pmult d`, where
> `fivegonSum d = ∑_{m ∈ kostantAll d} X^{(codimForm N (extendℤ m)).toNat} · Pm N m`
> (the sum over all Kostant partitions of `d`, any corner) and `Pmult d = ∏_i P (d i)`.
>
> - **Lean:** module `DLNFibre.Core.QSeriesFivegon` (`lean/DLNFibre/Core/QSeriesFivegon.lean` @ `31b997c`,
>   branch `expedition/perm-invariance`; SHA pinned by the controller at integration). Headline: `fivegon`.
> - **Proof.** Induction on `N`. Base `N=0` (`fivegon_base`): the single partition contributes `X^0·P(d 0)`.
>   Step `N+1`: `fivegonSum_fiberwise` reorganizes the sum over `kostantAll d` into its `peelPart`-fibres
>   over `kostantAll (d∘castSucc)`; `perfibre_collapse` collapses each fibre to `X^{codim m'}·Pm m'·P(d_last)`;
>   factor out `P(d_last)`, recognize `fivegonSum (d∘castSucc)`, apply the IH, then `Pmult_succ`.
> - **Proved.** Unconditionally, axiom-clean. `#print axioms DLNFibre.Core.fivegon =
>   [propext, Classical.choice, Quot.sound]`.

## The (Q) chain (deliverable 1) and the per-fibre collapse (deliverable 2)

> **(Q) — `innerSum_eq_transferRHS`.** For `m' : Fin (N+1)×Fin (N+1) → ℕ`, `dlast : ℕ`,
> `innerSum m' dlast = transferRHS (List.ofFn (fun i ↦ m' (i, last N))) dlast`.
> The per-fibre inner sum over admissible last columns equals the last-column transfer of the column-`N`
> data. Route (Codex thread-16 `q-answer.md`):
> - `adm b d` (`Finset.Nat.antidiagonalTuple (n+1) d` filtered by `x_{i.castSucc} ≤ b_i`); the bridge
>   `admissibleXs_eq_adm` (corner bound from `∑ x = dlast`).
> - `adm_peel_sum` — the constrained-vector peel (`∑_{x∈adm b d} F x = ∑_{x₀≤min(b 0)d} ∑_{y∈adm(tail b)(d−x₀)} F(cons x₀ y)`),
>   a sigma `Finset.sum_bij'` (`x ↦ ⟨x 0, tail x⟩`).
> - `flatDelta` (recursive ℤ exponent, peels under `cons`); `flatDelta_eq_finsum` (the row/col double sum);
>   `qSum` (general flat q-sum) and `qSum_eq_transferRHS` (the q-series induction: peel + `durfee` deferred to `transferRHS_eq`).
> - `innerSum_exp_eq_flatDelta` — the exponent bridge: `innerSum`'s `Icc`-indexed `extendℤ(rebuild)` pairing
>   = `flatDelta` of the column-`N` data, via the two `extendℤ_rebuild` eval lemmas + an `Icc→Fin` reindex.
>   **Requires** `∀ I', x I'.castSucc ≤ m'(I', last N)` (the admissibility bound: the truncated ℕ-subtraction
>   `rebuild` stores equals the ℤ-subtraction of `flatDelta` only under the bound). Discharged in `innerSum_eq_qSum`
>   from `x ∈ adm`.
>
> **Per-fibre collapse (deliverable 2) — `perfibre_collapse`.** For `m' ∈ kostantAll (d∘castSucc)`,
> `∑_{m : peelPart m = m'} X^{(codimForm (N+1) (extendℤ m)).toNat}·Pm (N+1) m = X^{(codimForm N (extendℤ m')).toNat}·Pm N m'·P(d_last)`.
> `perfibre_reduces` (P, landed) → `X^{codim}·lowerPm·innerSum`; then (Q) + `transferRHS_eq` + `listOfFn_col_prod`
> evaluate `innerSum = P(d_last)·∏ P(m'_{·,N})`; `Pm_eq_colN_mul_lower` reassembles `Pm N m'`.

- **Assumed / Cited.** None new in this thread. `durfee` (M2, the only classical q-series input) and (P)
  `perfibre_reduces` were landed earlier. Everything else from Mathlib `Finset`/`Fin`/`Nat`/`Int` primitives.
- **Status.** sorry-free, green, axiom-clean. **AUDIT (fidelity) pending** — a reviewer must confirm the Lean
  `fivegonSum`/`Pmult`/`kostantAll`/`codimForm` statements match the paper's Thm 5.6.

## Build / hygiene
- `lake build DLNFibre.Core.QSeriesFivegon`: green (3019 jobs), 0 sorry / 0 axiom / 0 native_decide.
- `#print axioms DLNFibre.Core.fivegon = [propext, Classical.choice, Quot.sound]`.
- **Aggregator not yet wired**: `import DLNFibre.Core.QSeriesFivegon` should be appended to `DLNFibre.lean`
  by the controller (single-writer rule). Currently `QSeriesFivegon` is NOT in `DLNFibre.lean`.

## v4.29 gotchas found
- A **stale build cache** can report a broken proof as green. `flatDelta_eq_finsum` first "built green"
  but was genuinely broken (`Fin.sum_univ_succ` matched the wrong inner sum); the fix pins the split sum
  with an explicit `(f := …)`. Re-run `lake build` from a clean state before trusting green.
- `Finset.sum_bij'` (dependent, membership-in-scope `i : ∀ a ∈ s, κ`) is the right tool for an
  `Icc (1:ℤ) n ↔ Fin n` reindex — `sum_nbij'` needs a *total* inverse `ℤ → Fin n`, which forces a junk
  fallback. Beta-reduce the bij-produced redexes (`(fun i hi ↦ …) i hi`) with `simp only` before `omega`/`rw`.
- `not_lt_of_le` is not in scope at this pin — use `not_lt.mpr`.
- Rewriting under an `if c then … else …` condition triggers "motive is not type correct"; convert the
  condition with an `Iff` (`hcond`) and `if_pos (hcond.mpr h)` / `if_neg (fun hc ↦ h (hcond.mp hc))` instead.
