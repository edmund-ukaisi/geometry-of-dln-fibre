# Thread 16 — the q-series inner-sum induction (Q) → fivegon (Thm 5.6)

Formalisation tide. Controller delegates; this is the spec.

**Codex consult status:** the `local-codex-consult` for (Q)'s Lean strategy TIMED OUT (xhigh >10min,
high >7min, no output written). Per policy, NOT substituting a fabricated answer — the formaliser
grinds with the controller-pinned route below + its own exploration.

## Goal
Complete **Thm 5.6 (the 5gon)** in `lean/DLNFibre/Core/QSeriesFivegon.lean`:
`fivegonSum d = Pmult d` (corner-free single sum), for `d : Fin (N+1) → ℕ`, by induction on `N`.

## Remaining pieces (in order)
1. **(Q)** `innerSum m' dlast = transferRHS (List.ofFn (fun i : Fin (N+1) => m' (i, Fin.last N))) dlast`
   — THE hard q-series induction.
2. **per-fibre collapse**: `∑_{m ∈ (kostantAll d).filter (peelPart · = m')} X^{(codimForm (N+1) (extendℤ m)).toNat} · Pm (N+1) m
   = X^{(codimForm N (extendℤ m')).toNat} · Pm N m' · P (d (Fin.last (N+1)))`, from `perfibre_reduces` (P) + (Q)
   + `transferRHS_eq` + `listOfFn_col_prod` + `Pm_eq_colN_mul_lower` (S3a).
3. **S5 / fivegon**: induction on N — base `fivegon_base` (N=0); step `fivegonSum_fiberwise` + per-fibre collapse + IH
   + `Pmult_succ`. Aggregate `QSeriesFivegon` into `DLNFibre.lean` at the end.

## LANDED building blocks (all in QSeriesFivegon.lean unless noted)
- `innerSum m' dlast` (def); `perfibre_reduces` (the (P) reduction to `X^{codim m'}·lowerPm·innerSum`).
- `extendℤ_rebuild_colN m' x a (0≤a) (a≤↑N) : extendℤ (rebuild m' x) a ↑N = ↑(m'(⟨a.toNat⟩, last N) − x ⟨a.toNat⟩.castSucc)`.
- `extendℤ_rebuild_colNp1 m' x u (0≤u) (u≤↑N+1) : extendℤ (rebuild m' x) u (↑N+1) = ↑(x ⟨u.toNat⟩)`.
- `transferRHS` (QSeriesPeel): `[] d = P d`; `(b0::bs) d = ∑ x0 ∈ range (min b0 d + 1), X^((b0-x0)(d-x0))·P(b0-x0)·P x0·transferRHS bs (d-x0)`.
- `transferRHS_eq : transferRHS b d = P d * (b.map P).prod`. `listOfFn_col_prod : ((List.ofFn (m'(·,last N))).map P).prod = ∏ i, P (m'(i,last N))`.
- `durfee` (QSeriesDurfee): `P a * P b = ∑ r ∈ range (min a b + 1), X^((a-r)(b-r))·P(a-r)·P r·P(b-r)` (check exact form in file).
- `Pm_eq_colN_mul_lower : Pm N m' = (∏ I, P (m'(I,last N))) * lowerPm m'`. `lowerPm` (def).
- `Pmult_succ : Pmult d = Pmult (d∘castSucc) * P (d (last (N+1)))`. `fivegonSum_fiberwise`, `fivegon_base`, `kostantAll_zero_eq` (N=0).
- `admissibleXs m' dlast = (piFinset (fun I => range (boundX m' dlast I + 1))).filter (∑ = dlast)`; `boundX I = Fin.lastCases dlast (m'(·,last N)) I`.

## (Q) route (controller-pinned)
Δ in innerSum's exponent (the codimForm `∑_{i∈Icc 1(↑N+1)}∑_{u∈Icc i(↑N+1)} extendℤ(rebuild)(i-1)↑N · extendℤ(rebuild) u(↑N+1)`)
evaluates (via the two entry-eval lemmas, INSIDE a `sum_congr` so the Icc range hyps are available; then `push_cast`/`Int.toNat`)
to a ℕ quantity `natΔ = ∑_{0≤a<u≤N+1} (b_a − x_a)·x_u` (b_a = m'(a,last N)).
- Define a general `qSum (n : ℕ) (c : Fin n → ℕ) (d : ℕ)` (bounded-composition q-sum over `x : Fin (n+1) → ℕ`, `∑x=d`,
  `x_{i.castSucc} ≤ c i`, corner `≤ d`; exponent the peelable Fin natΔ; factors `∏_I P(x I) · ∏_i P(c i − x_{i.castSucc})`).
- `qSum n c d = transferRHS (List.ofFn c) d` by induction on `n`: base `n=0` → `P d`; step peel the first block `x 0`:
  reorganize `∑_{x∈admissibleXs}` into `∑_{x_0}∑_{tail}` — candidate idioms: `Finset.sum_fiberwise_of_maps_to (·0)` + a per-fiber
  `Finset.sum_bij'` (fiber ≅ filtered tail piFinset via `Fin.tail`/`Fin.cons`); OR `Finset.filter_piFinset_eq_map_consEquiv`
  (Mathlib/Data/Fin/Tuple/Finset.lean) + handle the `∑=d` filter by summing over `x_0` (the `∑=d` filter is `x_0 + ∑tail = d`,
  not tail-only, so the consEquiv lemma needs the `x_0`-wrapper); OR `Finset.piAntidiag_cons`. The `x_0>d` fibers are EMPTY
  (drop to match `range (min c_0 d + 1)`). Δ-split: `natΔ = (c_0−x_0)(d−x_0) + natΔ'` using `∑x=d ⟹ ∑_{u>0}x_u = d−x_0`
  (watch ℕ subtraction). P-factor split + `durfee` per step + IH.
- Δ-eval fold: `innerSum m' dlast = qSum (N+1) (fun i => m'(i,last N)) dlast` (rewrite exponent + match bounds/factors).

THE crux is the constrained-vector peel (`∑x=d` couples head+tail). Try the fiberwise route first; if it fights, the consEquiv
or piAntidiag route. Build incrementally, commit each green sorry-free chunk.

## Constraints
- Work in THIS worktree only (`/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/voigt-discharge`); verify `lean/.lake/packages/mathlib` exists before building (do NOT `lake exe cache get` / re-clone). `source ~/.elan/env`; `lake build DLNFibre.Core.QSeriesFivegon` from `lean/`.
- Zero `sorry`/`axiom`/`native_decide`; `decide +kernel` only. Axiom-clean target `[propext, Classical.choice, Quot.sound]`.
- Commit green chunks to the branch with clear messages. Report what landed + any obstruction.
