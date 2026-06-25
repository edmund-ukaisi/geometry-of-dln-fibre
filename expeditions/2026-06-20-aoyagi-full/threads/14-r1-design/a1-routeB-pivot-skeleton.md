# Route B (Rado pivot) — the proof skeleton for a114e07e (#84/#46, A1 upper bound)

**From:** pp (design). **To:** a114e07e (resuming route B, building the Rado core). Controller asked for
the **tight-set-Hall pivot-existence** front-and-center (NOT a deterministic rule). Here it is — with
the one load-bearing finding that **collapses the hard piece to a GREEN lemma you already have**. Read
§0 first; it changes how much you build.

## §0 — THE KEY FINDING (read before building): the Rado/tight-set theorem is UNNECESSARY; the real
## content is the BRIDGE `Yvec_lowerfit ⟹ ∃ QFeas perm`, and BG (backward greedy) is the realizer.
The controller is right that the Rado pivot is NOT a deterministic rule (largest-Y→largest-width fails
206/1360; min-tight-set fails 1170/1360 — `/tmp/a1_our_rho_pivot.py`, `/tmp/a1_pivot_rule.py`). The
pivot is an EXISTENCE statement. **What that existence equals (verified):**

> **tight-set pivot-exists-throughout ⟺ ∃ QFeas permutation of `Y` (realizability), 0/2018**
> (`/tmp/a1_achiever_pivot_property.py`); FAILS exactly on non-realizable instances (`M=[0,1,1],
> Y=[0,2]`: Gale/#74 holds, NO valid pivot, `/tmp/a1_pivot_on_cx.py`).

And **`Yvec_lowerfit` ⟺ realizability** (0/1360, `/tmp/a1_lowerfit_is_realizability.py`): the trunk's
green `Yvec_lowerfit` (`smallestK_m(Y) ≤ Sprefix_{m+1}` ∀m, achiever) is EXACTLY equivalent to
"∃ QFeas perm of `Y`". **So a general polymatroid-Hall / Rado–Gale theorem is UNNECESSARY — it would
re-derive `Yvec_lowerfit`.** (Converges with your #84 "no general Rado-Gale biconditional — FALSE",
pp-hall's CX, Codex's caveat.)

> **⚠️ CIRCULARITY WARNING (I caught this — do NOT build a "peel-given-feasible-completion" induction).**
> A peel "feasible `(j,u,rem)` ⟹ ∃ window value with feasible residual" IS true (5008/5008) but is
> **circular as a CONSTRUCTION**: it needs a feasible completion to exist (to peel its head), and
> proving one exists from `Yvec_lowerfit` IS the bridge we must establish. The peel is a tautology, not
> a realizer. **The actual constructive realizer of the bridge is BG** (below) — it builds the QFeas
> perm step-by-step, its window-non-emptiness following from `Yvec_lowerfit` + the dual, with NO oracle
> completion.

**THE REAL CONTENT (one statement):** the bridge
> `bridge : Yvec_lowerfit M (achiever) → ∃ q, (q ~ Yvec M (achiever)) ∧ QFeas M q`.
This is `#84` / `#46`. The realizer is **BG** (§1). Everything else (value chain, #45 LB) is green.

## §1 — What you build: BG (backward min-suffix greedy) realizes the bridge
**BG is the construction** (a114e07e's earlier choice — it is correct, verified `bg` realizes the
bridge 0/19525, `/tmp/a1_bridge_via_bg.py`). It builds `q` directly on `M` (NO transport, NO `ρ`, NO
Hall). State `(j : Fin L counting down, u : ℤ = running level, rem : Multiset ℤ)`; `u₀-anchor` via the
suffix:
- process `j = L−1 … 0`; suffix-sum so far `Tnext`; window `lo_q = max(M⁽ʲ⁺¹⁾, (S_tot−S_j)−Tnext)`,
  `hi_q = (S_tot−S_j + admBound_{j−1}) − Tnext` (`j≥1`; `hi_q = S_tot − Tnext` at `j=0`);
- pick `x =` smallest `rem` element in `[lo_q, hi_q]`; `rem := rem.erase x`; `Tnext += x`.
- `q := the picks`; then `q ~ Yvec` (rem exhausts) and `QFeas M q` (window bounds ⟹ `uTel`
  nonneg/antitone/≤admBound/`=0` at L). Telescoping recovery `Tstar M q ∈ Adm` is GREEN
  (`Tstar_mem_Adm` in your worktree).
**Window non-emptiness** (the one substantial piece — well-founded on `|rem|`): two guards, each
0-fail over 92775 steps (`/tmp/a1_bg_guards_provable.py`):
- **upper-fit** `min(rem) ≤ hi_q` — from conservation (`∑rem = S_tot − Tnext − (placed))` + the
  smallest-of-`|rem|`-positives-≤-mean; this is the `Yvec_lowerfit` / #74 side.
- **lower-fit** `max(rem) ≥ lo_q` — from the **dual** majorization `largestK_k(Yvec) ≥ largestK_k(M[1:])`
  (0/19525, `/tmp/a1_bg_guards_provable.py`); the large `Y`-values survive in `rem` to cover the large
  lower-windows ahead. ⚠️ The per-step reduction from (lower-fit + dual) to the guard is NOT a clean
  order-statistic (BG places non-descending 1126/1360, so `rem ≠ k-smallest of Y`) — it threads the
  achiever-`Y` structure (the same Hall content, positioned concretely). This is BG's irreducible piece.

(Your #84 already has `QFeas`, `Tstar`, `Tstar_mem_Adm`, `uTel`, `Yvec`, `goodAch`, `cAch`,
`Yvec_lowerfit`, `smallestK`, `Yvec_monotone`, `Yvec_prefix` — the scaffolding. BG = a recursion
producing `q` + the two-guard non-emptiness + the value chain.)

### (legacy §1 list — superseded by BG above; the "realizable wrapper" item is the bridge, not free)
1. **realizable** `∃ q, q ~ Y ∧ QFeasible M q` — this IS the bridge (`Yvec_lowerfit ⟹ ∃-perm`), the
   open content #84/#46. `Yvec_lowerfit` (lower-fit majorization, GREEN) ⟺ realizability (0/1360), but
   the ∃-perm WITNESS is what BG constructs. Not a free wrapper — it is the theorem.
2. **peel** (the lemma boxed in §0) — `obtain` the completion, peel its head. ~10 lines.
3. **construction** = well-founded recursion on `|rem|` applying peel; produces `q ~ Y`, `QFeasible M q`.
4. **value** (GREEN chain): `edgeQ(telescope(M,q)) = q` (D1 inverse) ⟹ `∑edgeQ² = ∑q² = ∑Y²` ⟹
   (`2·Mval = ∑edgeQ² − ∑M²`, the #74 factor-2 identity) `2·Mval(T*) = ∑Y² − ∑M² = 4·cleanCore` ⟹
   `Mval(T*) = 2·cleanCore` ⟹ `lambdaCore ≤ cleanCore`. With #45 (LB, GREEN) ⟹ `lambdaCore_eq_clean`.

QFeasible recap (edge-prefix, `S_n = M⁰+⋯+Mⁿ`, `P_n = ∑_{j<n}q_j`, `admBound_0=min(M⁰,M¹)`,
`admBound_j=M⁽ʲ⁺¹⁾`): (L) `q_j≥M⁽ʲ⁺¹⁾` (U) `P_n≤S_n` (Ladm) `P_n≥S_n−admBound_{n−1}` (T) `P_L=S_L`.

## §A — the `ρ`/tight-set framing (FAITHFUL, but the heavy path — build only if §0 peel is rejected)
- **`ρ(A) = ∑_{j∈A}M⁽ʲ⁺¹⁾ + C_{min A}`, `C_i=min{M⁰..Mⁱ}`, `ρ(∅)=0`.** Monotone + submodular via the
  cover decomposition **`C_{min A} = C_L + ∑_{i=0}^{L−1}(C_i−C_{i+1})·𝟙[A∩{0..i}≠∅]`** (⚠️ the `C_L`
  base term is REQUIRED — `C_L=min` of ALL widths, not 0; without it 144336/536025 fail. Verified with
  it 0/536025, `/tmp/a1_cover_fix.py`). `ρ(∅)=0` guard interacts with the nonempty-`C_L`-constant —
  verified submodular 0/1360, but be careful in Lean.
- **Gale condition = #74** (nested ρ ⟹ prefix-only collapse): `∀A sumSmallest(|A|,Y)≤ρ(A)` ⟺
  `∀m smallestK_m(Y)≤S_m` (= green #74). [`ρ({0..m−1})=S_m`; for general `A`, `ρ(A)≥` sum of `|A|+1`
  smallest widths `≥ smallestK(Y)`, 0/536025, `/tmp/a1_ii_proof_check.py`.] ⚠️ This is NECESSARY only —
  Gale/#74 does NOT imply ∃ assignment (the `[0,2]` CX). The Rado induction's pivot-existence is the
  EXTRA content, and (per §0) it = realizability = green. So even on this path the hard piece is §0's
  realizability, not a Hall theorem.
- **Rado induction** (if built): remove `y*=max Y`, pivot `e*` = an element supplied by a tight set
  `A` (`sumSmallest(|A|,Y)=ρ(A)`), contract `ρ'(A):=min(ρ(A), ρ(A∪{e*})−y*)`. ⚠️ pivot-existence
  holds iff realizable (§0) — so discharge it by `Yvec_lowerfit`, do not re-prove via Hall.
- **assignment ⟹ QFeasible** (clause-algebra, 0/1360): (U) prefix `ρ=S_n`; (L) complement
  `ρ(E)−ρ(E∖{j})=M⁽ʲ⁺¹⁾`; (Ladm) suffix `ρ`; (T) total. All `omega`/`Finset`.

## §B — fallbacks (if §0/§A both wall)
- **Route BG** (a114e07e's earlier choice): backward min-suffix greedy DIRECT on `M`, no transport,
  no `ρ`. Window non-emptiness = #74 + dual (`largestK_k(Y)≥largestK_k(M[1:])`, 0/19525) + the
  Y-scoped per-step reduction. 0/19525. (`a1-achiever-design.md §ROUTE BG`.) ≈ same realizability core
  as §0, different construction shell.
- **Route S**: sorted achiever `q=sortY` (0/19525, 4 clean clauses) + bubble-transport sortM→M
  (L²-fiddly, 3-way per-swap witness). (`§ROUTE S`.)

## Net
**Build §0 (peel given green `Yvec_lowerfit`) — it is the minimal route and avoids the polymatroid-Hall
theorem entirely.** The controller's "tight-set-Hall pivot" is faithfully in §A, but the verified
finding is that pivot-existence = realizability = green, so §A's Hall is unnecessary. Confirm the exact
trunk form of `Yvec_lowerfit` (lower-fit majorization vs ∃-perm); the lower-fit ⟹ ∃-perm bridge is the
one realizability step shared by §0/BG/S. Route-back to me with the `Yvec_lowerfit` form and I'll pin
the bridge. Value chain (#74-identity, edgeQ inverse, #45) all GREEN.
