# rankgen — the deep-factor rank-survival fact `b ≤ rank Z_deep`: FALSE at general cuts, TRUE at the binding cut

**Seat:** pen-and-paper (adjudication — obstruction to the stated scope + witness of the operative scope),
aoyagi-full Stage 2, `genm-rankgen`. **Date:** 2026-07-15. **NO Lean edits, NO build.** Exact Nat/rational
algebra + decorrelated `local-codex-consult` (gpt-5.x, xhigh, my conclusion WITHHELD — prompt framed
"argue from the definitions"): `codex/rankgen-{prompt,answer}.md`, `run.log`. Numerics
(exact, certificate — not MC): `rankgen-binding.py`, `rankgen-mechanism.py`, `rankgen-exact2.py`,
`rankgen-sweep2.py`.

**Consumed / cross-read (verified, not paraphrased) on `genm-sj5-capstone`:**
`RouteMSJIncidenceAssembly.lean` (`deepTailMin` L55, `minAdm_redChain_le_deepTailMin` L83,
`coupledBoxIntegrand` L254, `shellSpine_le_coupledBox` L272, `freedSchurLoss_gammaPeel_le` L329),
`RouteMSJCorankSurvival.lean` (`corank_survival_ae` L88, `ae_matrix_eval_ne_zero` L48),
`RouteMSJDeeperFlagCore.lean` (`deeperFlagZdeep` L466, `shellSpineIntegrand` L444, `tailMinWidth` L458),
`RouteMSJDeeperFlagShell.lean` (mountain doc: "cut `u = t★+j`"), `RouteMSJOffSectorBPos.lean` (the
`Z.rank = M₂` assumption, §5 landmine), `RouteMLayerSplit.lean` (`minAdmRec` L58, leaf `= M₀·M₁`),
`BindingSpine.lean` / `RouteMNReg.lean` (`schurStateRed`); the certs `genm-routeverify/routeverify-cert.md`
§3–§4, `genm-incidencepp/incidence-cert.md` §Verdict-2/§3/§4.

---

## ★ VERDICT

The threaded hypothesis `∀ᵐ z, b ≤ rank(deeperFlagZdeep M u z)` is **exactly equivalent to the Nat
inequality `b ≤ deepTailMin M`** (`deepTailMin M = min(M₂,…,M_last)`), because `rank Z_deep(z) ≤ deepTailMin M`
for ALL z and `= deepTailMin M` for a.e. z (generic rank of a layer product = min width — exact-certified,
§4).

1. **Under the STATED scope `a+b ≤ M₂` (+ GOOD + strict shell), the fact is FALSE for deep chains
   (arity ≥ 4)** — an OBSTRUCTION. Smallest witness (independently found by decorrelated Codex):
   `M = (3,4,3,1)`, `t = 1`, `j = 1`: `u = 2`, `a = 1`, `b = 2`, `deepTailMin = min(3,1) = 1`, and all of
   GOOD (`1 ≤ 4`), strict-shell (`1 ≤ 1 < r = min(2,3) = 2`), `a+b = 3 ≤ M₂ = 3` hold, yet `b = 2 > 1`.
   Here `Z_deep` is a `3×1` matrix (rank ≤ 1), so `b = 2` corank rows **cannot** survive full rank — the
   corank Gram `det(Q_bQ_bᵀ)` is `0` for **all** `(z, A_cor)`. No scope phrased in `{M₂, M₁, M_last}` can
   fix this: the bottleneck sits at an arbitrary deep layer (see `M=(3,4,1,4)`, bottleneck at `M₂=1`).
   `a+b ≤ M₂` gave 1074 fails, the Brick-D scope `a+b ≤ min(M₁,M_last)−j` gave 390 fails (widths 1..6,
   arity 3..5). **`a+b ≤ M₂` is the arity-3 shadow** — at arity 3, `deepTailMin = M₂`, so it happens to work
   (0 fails); it is the *generalisation to deep chains* that broke.

2. **At the BINDING cut `u = t★+j` (`t★ = argmin` of the layer recursion) — which is the only cut the
   mountain (`deeperFlag_shell_le`, "cut `u = t★+j`") invokes — the fact is TRUE with slack `≥ 2`:**
   `a+b ≤ deepTailMin M − 1`, hence `b ≤ deepTailMin M − 2 < rank Z_deep(z)` a.e. **0 fails** across every
   arity/width tested (arity 3..6, widths 1..7 at binding cuts). This is a clean consequence of the
   optimality of `t★` (§3), not a coincidence.

3. **Discharge (§4): route (b′) + route (c), composed — route (a) is UNAVAILABLE.**
   - **(b′) binding-cut Nat lemma** → `b ≤ deepTailMin M` (via `t★`-optimality + the marginal lemma below);
   - **(c) a.e. generic-rank lemma** → `deepTailMin M ≤ rank(deeperFlagZdeep M u z)` a.e., converting the Nat
     bound into the per-`z` fact `corank_survival_ae` consumes. **(c) is logically unavoidable** (rank drops
     on an exceptional — measure-zero — set, so no purely combinatorial bound gives the per-`z` statement),
     but its pieces are largely banked (`exists_submatrix_det_ne_zero_of_le_rank`, `minorPoly`/`eval_minorPoly`,
     `ae_matrix_eval_ne_zero`).
   - **(a) shell-determinism is dead here**: `shellSpine_le_coupledBox` DROPS the shell indicator
     (`lintegral_mono_set Set.inter_subset_left`, a-fortiori) BEFORE the corank charge, landing on the full
     product box. So there is no shell to force `rank Z_deep ≥ b` pointwise; the fact must hold over the full
     `z`-box, which is exactly what (b′)+(c) deliver.

**Outcome class: (ii) — TRUE in the operative scope (binding cut), needs a fresh a.e.-genericity lemma (c)
gated by a Nat binding-cut lemma (b′); (iii) with respect to the *stated* scope `a+b ≤ M₂`, which is
INCORRECT for deep chains and must be replaced by the deep-tail scope `a+b ≤ deepTailMin` (of which
`a+b ≤ M₂` is the arity-3 special case).**

---

## 1. The reduction: the fact ⟺ `b ≤ deepTailMin M`

`deeperFlagZdeep M u z = prod (dropHead (redChain u M)) (paramsHeadSplit … z).2` is the product of the deep
layers of widths `(M₂, M₃, …, M_last)` — an `M₂ × M_last` matrix. `deepTailMin M = min(M₂,…,M_last)`
(`IncidenceAssembly:55`, `= ⨅_{i≥2} Mᵢ`). Two elementary facts about a product of generic matrices:

- **deterministic upper bound:** `rank Z_deep(z) ≤ min(M₂,…,M_last) = deepTailMin M` for **all** `z`
  (rank of a product ≤ each factor width; `Matrix.rank_mul_le`).
- **a.e. lower bound (generic rank):** for a.e. `z`, `rank Z_deep(z) = deepTailMin M` (the generic rank of a
  layer product equals the minimum width — §4).

Hence `∀ᵐ z, b ≤ rank Z_deep(z)` holds **iff** `b ≤ deepTailMin M` (Nat): if `b ≤ deepTailMin` the a.e. set
is full; if `b > deepTailMin` then `rank Z_deep(z) ≤ deepTailMin < b` for **every** `z`, so the fact is false
everywhere (not just a.e.). This is the whole content of the "genericity" — it collapses to one Nat
inequality plus the standard generic-rank lemma.

`corank_survival_ae` (`CorankSurvival:88`) needs precisely `hb : b ≤ Zdeep.rank` for the *fixed* matrix
`Zdeep = Z_deep(z)`, per `z`; the fact supplies it a.e.-`z`, then `corank_survival_ae` supplies
`rank(A_cor·Z_deep) = b` a.e.-`A_cor`. So `b ≤ deepTailMin` is the load-bearing combinatorial input.

## 2. The obstruction: `a+b ≤ M₂` does NOT give `b ≤ deepTailMin` (deep chains)

`rankgen-sweep2.py` (exact Nat, GOOD + strict-shell, arity 3..5 widths 1..6):

| scope | in-scope cuts | `b > deepTailMin` fails |
|---|---|---|
| `a+b ≤ M₂` (stated) | 6344 | **1074** |
| `a+b ≤ min(M₁,M_last)−j` (Brick-D) | 2630 | **390** |
| `a+b ≤ deepTailMin` (correct) | 2848 | **0** |

The failures are genuine geometric divergences, not slack: at `M=(3,4,3,1)`, `u=2`, `Z_deep` is `3×1`
(rank ≤ 1), `Q_b = A_cor·Z_deep` is `2×1` (rank ≤ 1 < 2 = `b`), so `det(Q_bQ_bᵀ) ≡ 0` and the corank charge
`det(Q_bQ_bᵀ)^{−a/2} ≡ +∞`. This is the same divergence as incidence-cert §Verdict-2's out-of-scope witness
`(3,3,3)@u=1` (a+b > M₂) — except here `a+b ≤ M₂` **holds**, so `a+b ≤ M₂` fails to protect it. The correct
scope references the deep-tail minimum: `a+b ≤ deepTailMin M` (0 fails), and at arity 3 `deepTailMin = M₂`,
recovering the known `a+b ≤ M₂`.

## 3. The resolution: the binding cut forces `a+b ≤ deepTailMin − 1`

The mountain peels at the **binding cut** `t★ = argmin_t f(t)`, `f(t) = (M₀−t)(M₁−t) + minAdm(redChain t M)`
(`DeeperFlagShell` doc: LHS is "the cut-`u = t★+j` integrand"; `minAdmRec` = this recursion,
`RouteMLayerSplit:58`, leaf `minAdm(d₀,d₁) = d₀·d₁`). Write `g(t) := minAdm(redChain t M)`,
`ρ := deepTailMin M`, `A := M₀−t★`, `B := M₁−t★`.

**Marginal lemma (exact-certified 0/33600, `rankgen-mechanism.py`):** `g(t+1) − g(t) ≤ ρ`, tight.
*Proof (induction on the deep-tail length; matches decorrelated Codex Q3).* `redChain t M = (t, W)`,
`W = (M₂,…,M_last)`. Base (`W` a single width `w`): `g(t) = minAdm(t,w) = t·w`, so `g(t+1)−g(t) = w = ρ`.
Step (`W = (w₀, W')`): let `s★` optimise `g(t) = min_{s≤min(t,w₀)}[(t−s)(w₀−s)+minAdm(s,W')]`.
If `ρ = w₀`, reuse `s = s★` at `t+1`: `g(t+1) ≤ g(t) + (w₀−s★) ≤ ρ`. If `ρ < w₀` and `s★ < w₀`, use
`s = s★+1`: `g(t+1)−g(t) ≤ −(t−s★) + [minAdm(s★+1,W′)−minAdm(s★,W′)] ≤ −(t−s★) + ρ ≤ ρ` (inner marginal by
IH on the shorter tail). If `s★ = w₀`, reuse `s = w₀`: increment `0 ≤ ρ`. ∎

**Binding-cut bound (exact-certified 0/8425 GOOD, 0/13365 all chains, `rankgen-mechanism.py`).** At a strict
shell `1 ≤ j < r = min(A,B)` we have `min(A,B) ≥ 2`, so `A,B ≥ 2` and `t★+1 ≤ min(M₀,M₁)` is admissible.
Optimality `f(t★) ≤ f(t★+1)` gives, using `AB − (A−1)(B−1) = A+B−1` and the marginal lemma,

    A + B − 1  =  (M₀−t★)(M₁−t★) − (M₀−t★−1)(M₁−t★−1)  ≤  g(t★+1) − g(t★)  ≤  ρ,

so `A + B ≤ ρ + 1`. Therefore at the strict shell (`a = A−j`, `b = B−j`, `j ≥ 1`):

    a + b  =  A + B − 2j  ≤  (ρ+1) − 2  =  ρ − 1  =  deepTailMin M − 1,

hence `b ≤ a+b ≤ deepTailMin M − 1` and (with `A ≥ 2` ⟹ `a ≥ 1`) `b ≤ deepTailMin M − 2`. This is **why** the
binding cut never divergences: `a+b ≤ deepTailMin − 1` puts the corank charge STRICTLY inside the convergent
regime `a+b ≤ deepTailMin` (not even the borderline). The margin-`≥2` histogram (`rankgen-binding.py`) is this
bound. Note the mechanism needs NO GOOD assumption — it is pure optimality of `t★`.

`M=(3,4,3,1)` reconciled: its `t★ = 3` (`f(3)=0+3=3` is the min; `f(1)=6+1=7`), so `r = min(0,1) = 0` and
there are **no strict shells** — the chain is handled entirely by the `j=0`/`j=r` base cases, and the
"counterexample" cut `(t=1,j=1)` is non-binding and is **never invoked** by the mountain.

## 4. The discharge routes

- **(b′) — the Nat lemma [BUILD].** `binding cut t★, strict shell 1≤j<r ⟹ b ≤ deepTailMin M`. Proof = §3:
  the `t★`-optimality inequality `f(t★) ≤ f(t★+1)` + the **marginal lemma** `g(t+1)−g(t) ≤ deepTailMin`. The
  marginal lemma is the one substantive sub-fact (clean induction on tail length; it is a first-difference
  companion to the banked `minAdm_le_head_mul_tailInf` / `minAdm_redChain_le_deepTailMin`, provable by the
  same permutation-invariance + head-bound toolkit). This is the CLEANEST source of `b ≤ deepTailMin` — it
  ties the fact to *why* the mountain's cut is chosen, not to a hoped-for scope.
- **(c) — the a.e. generic-rank lemma [BUILD, pieces banked].**
  `∀ᵐ z, deepTailMin M ≤ rank(deeperFlagZdeep M u z)`. Then `b ≤ deepTailMin ≤ rank Z_deep(z)` a.e.
  Exact-certified sound: the deep product achieves rank = deepTailMin at a generic (random exact-ℚ) point,
  0/90 fails, arity 4..6 (`rankgen-exact2.py`). Lean shape (parallels `corank_survival_ae`'s own structure):
  exhibit a `deepTailMin×deepTailMin` submatrix of `prod (dropHead (redChain u M))` whose determinant is a
  **nonzero** `MvPolynomial` in `z` (a staircase/identity witness point makes the minor `= ±1`), then
  `ae_matrix_eval_ne_zero` (`CorankSurvival:48`, banked) ⟹ a.e. nonvanishing ⟹ `rank ≥ deepTailMin` via
  `rank_le_iff_forall_submatrix_det_eq_zero` / `exists_submatrix_det_ne_zero_of_le_rank`
  (`Core/RankLocusClosed.lean`, banked). The one new content is the **nonzero-minor witness for a *product* of
  layers** (generic rank of a chain product = min width) — `DeepestCoreNonvanishing` only gives a single
  nonzero *entry* (rank ≥ 1); the `deepTailMin`-minor version is the natural strengthening. Feasible, not a
  wall. **(c) cannot be avoided** — it is the only step that converts the combinatorial `b ≤ deepTailMin`
  into the per-`z` `b ≤ rank Z_deep(z)` that `corank_survival_ae` consumes (Codex Q4 concurs).
- **(a) — shell-determinism [UNAVAILABLE].** The Ky-Fan `shell ⊆ goodSet` route would force `rank Z_deep ≥ m`
  pointwise on the shell, but `shellSpine_le_coupledBox` drops the shell a-fortiori before the corank charge
  (`IncidenceAssembly:272`, `lintegral_mono_set Set.inter_subset_left`), so the corank survival is needed over
  the FULL box where no shell floor exists. This is not a defect — at binding cuts (b′)+(c) hold over the full
  box, so dropping the shell is legitimate (off-shell is convergent, `a+b ≤ deepTailMin−1`).

**Cleanest architecture recommendation.** Thread the Nat hypothesis `b ≤ deepTailMin M` on the general-`(t,j)`
`deeperFlag_shell_le` / step-2 lemma (NOT `∀ᵐ z, b ≤ rank`, which is a per-`z` consequence). Prove the bridge
`b ≤ deepTailMin M → ∀ᵐ z, b ≤ rank(deeperFlagZdeep M u z)` once (route c). Discharge `b ≤ deepTailMin M` at
the `t★` call site via the binding-cut Nat lemma (route b′). The general-`(t,j)` lemma then stays honest
(it carries the hypothesis; it is FALSE without it) and the caller supplies it from the binding property.

## 5. Related landmine (flag — beyond the strict remit, same root cause)

`RouteMSJOffSectorBPos.lean` (the older off-sector route) states its scope as **"Fixed full-rank tail:
`Z.rank = M₂`"** and its weight-finiteness `corankWeight_bpos_lt_top` on `a < M₂ − b + 1`, via
`exists_gram_normalizer` (`ZZᵀ = LLᵀ`, `L` invertible `M₂×M₂`). For a deep chain with `deepTailMin < M₂`,
`Z.rank = M₂` is **a.e. FALSE** (rank `= deepTailMin`), so `ZZᵀ` is singular and the `M₂×M₂` Gram
normaliser does not exist — the CoV underlying weight-finiteness breaks, exactly as the survival breaks. The
same fix applies: the **effective column dimension is `deepTailMin`, not `M₂`**, the convergent regime is
`a+b ≤ deepTailMin` (`a < deepTailMin − b + 1`), and the binding cut sits strictly inside it
(`a+b ≤ deepTailMin − 1`). Wherever the corank *weight* finiteness is invoked for a deep chain, it needs a
`deepTailMin`-effective-dimension version (normalise on the `deepTailMin`-dim row space of `Z`), not the
`M₂`-Gram version. (The `(3,3,3)@t=1` borderline `a = M₂−b+1` the cert notes is the arity-3 shadow of the
`a = deepTailMin−b+1` borderline; at genuine binding cuts the strict `a+b ≤ deepTailMin−1` avoids it.) This
is stated for the incidence route too: keep the corank charge over the effective `deepTailMin`-space.

## 6. Certificates (exact — MC not used)

- `rankgen-sweep2.py`: `a+b ≤ M₂` ⟹ `b ≤ deepTailMin` FAILS (1074), `a+b ≤ min(M₁,M_last)−j` FAILS (390),
  `a+b ≤ deepTailMin` HOLDS (0), arity 3..5 widths 1..6. Smallest witness `M=(3,4,3,1)`.
- `rankgen-binding.py`: at binding cuts `u = t★+j` (all argmins), `b ≤ deepTailMin` HOLDS 0/63 (a3), 0/130
  (a4), 0/108 (a5), 0/103 (a3..6 w1..5). Margin `deepTailMin − b ≥ 2` always. `M=(3,4,3,1)` t★=3, r=0 (no
  strict shell).
- `rankgen-mechanism.py`: marginal `g(t+1)−g(t) ≤ deepTailMin` 0/33600 (max excess 0, tight); binding
  consequence `A+B ≤ deepTailMin+1` 0/8425 (GOOD), 0/13365 (all).
- `rankgen-exact2.py`: generic rank of the deep product `= deepTailMin` at an exact-ℚ random point, 0/90
  fails (arity 4..6) — route (c) is sound; `b ≤ deepTailMin` at all 90 binding strict shells.

## Decorrelated Codex (conclusion WITHHELD; prompt "argue from the definitions") — CONCURS on all points

`codex/rankgen-{prompt,answer}.md` (xhigh). Independent, reached the identical results:
- **Q1 [FACT]** NO — smallest counterexample `M=(3,4,3,1)`, `t=1`, `j=1`, `b=2 > deepTailMin=1`, all of
  (S1),(S2),(S3) verified; identical minimality argument (arity 3 cannot fail).
- **Q2 [FACT] PROVED** at binding cuts via `f(t★) ≤ f(t★+1)`: `A+B−1 ≤ g(t★+1)−g(t★) ≤ D`, so
  `b = B−j ≤ B−1 ≤ A+B−1 ≤ D` (identical to §3).
- **Q3 [FACT]** `0 ≤ g(t+1)−g(t) ≤ D` tight, by tail-length induction (identical).
- **Q4 [INFERENCE/FACT]** route **(b)+(c)**: binding optimality ⟹ `b ≤ D`, generic rank ⟹ `rank = D` a.e.;
  route (a) insufficient (per Q1); "some generic-rank input is logically unavoidable"; a fresh (c) is
  avoidable only if a standard generic-rank theorem is already available (identical to §4).

## Close

- **Firmest result.** `∀ᵐ z, b ≤ rank(deeperFlagZdeep M u z)` ⟺ Nat `b ≤ deepTailMin M`. FALSE under the
  stated scope `a+b ≤ M₂` for deep chains (obstruction; smallest witness `M=(3,4,3,1)@(1,1)`, Codex-concurred);
  TRUE with slack `≥ 2` at the binding cut `u = t★+j` the mountain actually invokes (`a+b ≤ deepTailMin−1`,
  by `t★`-optimality + the marginal lemma `g(t+1)−g(t) ≤ deepTailMin`). The correct scope is
  `a+b ≤ deepTailMin M`, whose arity-3 special case (`deepTailMin = M₂`) is the known `a+b ≤ M₂`.
- **Discharge.** (b′) binding-cut Nat lemma → `b ≤ deepTailMin`, then (c) a.e. generic-rank lemma (pieces
  banked: `ae_matrix_eval_ne_zero` + `exists_submatrix_det_ne_zero_of_le_rank`; one new nonzero-minor witness
  for a layer product) → `b ≤ rank Z_deep(z)` a.e. Route (a) shell-determinism is unavailable (shell dropped
  before the corank charge).
- **Most likely to break it.** The verdict RESTS on the mountain invoking the spine only at cuts with
  `b ≤ deepTailMin` (i.e. `t = t★`). If any consumer instantiates the step-2 / `deeperFlag_shell_le` at a
  non-binding `t` with a strict shell and `b > deepTailMin`, the fact is false there and that instance's
  corank charge diverges — so the fact must be discharged at the call site from the binding property, never
  stated as a free `∀(t,j)` lemma. (Controller check: confirm no consumer sums over non-binding `t`.)
- **Next.** (i) Build route (b′) — the marginal lemma is the one substantive Nat step (bank it beside
  `minAdm_le_head_mul_tailInf`). (ii) Build route (c) — the deep-product nonzero-`deepTailMin`-minor witness.
  (iii) Re-scope the whole corank charge (survival + weight) to `deepTailMin`-effective-dimension, not `M₂`
  (§5); confirm the `Z.rank = M₂` assumption is purged from the deep-chain path.

Files (absolute):
- `…/threads/genm-rankgen/rankgen-cert.md` (this cert)
- `…/threads/genm-rankgen/codex/rankgen-{prompt,answer}.md`, `run.log`
- `…/threads/genm-rankgen/rankgen-{binding,mechanism,exact2,sweep2}.py`
