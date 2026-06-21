# Route B (Rado–Gale) — proof skeleton for a114e07e (#84, the A1 upper bound)

> ⛔ **STOP — THE GENERAL RADO–GALE THEOREM IS UNNECESSARY (and its biconditional form is FALSE).
> DO NOT BUILD A POLYMATROID HALL THEOREM.** Full resolution after re-deriving:
>
> 1. **"Gale ⟹ ∃ assignment" is FALSE** for this `ρ`. CX (= pp-hall's, confirmed): `M=[0,1,1]`,
>    `Y=[0,2]` satisfies the Gale condition (#74) yet has NO QFeasible permutation. No clean Gale family
>    characterises existence (mismatches 1209/2018, 73/2018 — `/tmp/a1_gale_direction.py`,
>    `/tmp/a1_correct_rado.py`).
> 2. **The Rado induction IS internally consistent**: pivot-existence (the tight-set/Hall step) FAILS
>    exactly when the instance is non-realizable. Verified: **pivot-exists-throughout ⟺ ∃ QFeasible
>    perm (realizability), 0/2018** (`/tmp/a1_achiever_pivot_property.py`). For `[0,2]` no valid pivot
>    exists (both `e*` give residual-Gale=False) — the induction correctly refuses.
> 3. **THEREFORE the tight-set-Hall pivot existence = realizability = the achiever's `Yvec_lowerfit`,
>    which is ALREADY GREEN in the trunk.** Building a general Rado–Gale / polymatroid-Hall theorem
>    would RE-DERIVE realizability that is already proven — it is **logically unnecessary work**. Given
>    realizability (green), the construction is a trivial "peel a feasible first value" induction; the
>    `ρ`/tight-set machinery adds nothing.
> 4. **USE ROUTE BG** (backward min-suffix greedy, direct on `M`): same green realizability, more direct
>    construction (no `ρ`, no tight-set Hall, no polymatroid). a114e07e already chose it (#84). The
>    `ρ`-algebra below is NOT needed; only the value chain transfers (and it is green).
>
> This converges with a114e07e's #84 note and Codex's caveat. The material below is RETAINED as the
> record of why B's general theorem is both false-as-biconditional AND unnecessary-as-scoped.

**From:** pp (design). **To:** a114e07e (A1 formaliser, @d7b4632). The five pieces the controller listed
are addressed, but (iii) is REFUTED above; (i)/(iv)/(v) and the value chain transfer to BG.

## The target (recap)
The trunk upper bound is `lambdaCore M ≤ cleanCore c (sortedSmallest M c)` for the achiever `c`,
i.e. `minMval M ≤ ∑Y² − ∑M²` (with `Y` the achiever edge-multiset; `2·Mval = ∑edgeQ² − ∑M²`, factor 2).
It suffices to exhibit ONE `q` that is a **permutation of `Y`** and **QFeasible** — then
`T* := telescope(M,q) ∈ Adm M`, `edgeQ(T*)=q` (D1 inverse, green), `∑edgeQ² = ∑Y²`, value closes.
QFeasible (edge-prefix form, `S_n = M⁰+⋯+Mⁿ`, `P_n = ∑_{j<n} q_j`, `admBound_0=min(M⁰,M¹)`,
`admBound_j=M⁽ʲ⁺¹⁾`):
- (L) `q_j ≥ M⁽ʲ⁺¹⁾`  (U) `P_n ≤ S_n`  (Ladm) `P_n ≥ S_n − admBound_{n−1}`  (T) `P_L = S_L`.

---

## (i) The rank `ρ` — monotone + submodular [`omega`/algebra; verified `/tmp/a1_rado_gale.py` 0/1360]
Slots `E = Fin L`. Width `w_j = M⁽ʲ⁺¹⁾`. Define `C : Fin (L+1) → ℤ`, `C_i := min{M⁰,…,Mⁱ}`
(`Finset.min'` over `Finset.range (i+1)` of `M`, or a simple fold; non-increasing in `i`). For
`A : Finset (Fin L)`:
> `ρ(A) := (∑_{j∈A} (M⁽ʲ⁺¹⁾ : ℤ)) + (if A.Nonempty then C_{A.min'} else 0)`,   `ρ(∅) = 0`.

- **Submodular**: the width term is modular; `A ↦ C_{min A}` (on nonempty `A`) is submodular via the
  **cover decomposition** [verified 0/536025, `/tmp/a1_cover_fix.py`]:
  > `C_{min A} = C_L + ∑_{i=0}^{L−1} (C_i − C_{i+1}) · 𝟙[A ∩ {0,…,i} ≠ ∅]`,   `C_L = min{M⁰,…,Mᴸ}`.
  ⚠️ **DO NOT drop the base term `C_L`** (I had this bug — `C_L` is the min of ALL widths, NOT `0`;
  the decomposition without it fails 144336/536025). `C_L` is a constant (independent of `A`), so it
  does not affect submodularity; each `(C_i − C_{i+1}) ≥ 0` (`C` non-increasing) and
  `𝟙[A ∩ {0..i} ≠ ∅]` is a submodular coverage indicator (verified 0 violations), so the sum is
  submodular. (Note the `i ≥ min A` ⟺ `A ∩ {0..i} ≠ ∅` identity is the index bookkeeping.)
- **`ρ(∅)=0` guard**: `ρ` is submodular *with* the `if A.Nonempty` guard (verified 0/1360) — but the
  `C_L`-constant-on-nonempty vs `ρ(∅)=0` interaction is a place to be careful in Lean (the constant is
  added to every nonempty `A` but not to `∅`); the exhaustive check confirms it holds, do not assume it
  away. Monotonicity `A⊆B ⟹ ρ(A)≤ρ(B)` follows from the same decomposition (coverage only grows).

## (ii) Gale condition = green #74 [the BIG simplification; verified `/tmp/a1_nested_assignment.py` 0/1360]
**Because `ρ` is NESTED (`C` depends only on `min A`), the full Gale family over all `2^L` subsets
collapses to the PREFIX sets `A = {0,…,m−1}`** (0 mismatches). And `ρ({0,…,m−1}) = M⁰+M¹+⋯+Mᵐ = S_m`
exactly (since `min A = 0 ⟹ C = C_0 = M⁰`). Therefore:
> **The Gale condition `∀A, sumSmallest(|A|,Y) ≤ ρ(A)` is EXACTLY `∀m, smallestK_m(Y) ≤ S_m` = green #74.**

So (ii) is `lemma gale_of_74 : (∀ m, smallestK m Y ≤ S m) → ∀ A, sumSmallest A.card Y ≤ ρ A`. Proof:
for nonempty `A`, `|A|=k`, `i=min A`: `ρ(A) = C_i + ∑_{j∈A} M⁽ʲ⁺¹⁾` is a sum of `k+1` DISTINCT entries
of the full width vector `M` (the `k` slot-widths in `A`, plus one of `M⁰..Mⁱ` realising `C_i`), hence
`≥ a_0+⋯+a_k` (`a = sortedSmallest`, the `k+1` smallest widths) `≥ smallestK_k(Y)` by #74. ⚠️ **NOTE
the earlier doc-version said the high-end "dual" majorization is also needed — it is NOT for the Gale
CONDITION** (nested ρ collapses it to prefixes = #74). The high-end is absorbed into `ρ`'s
submodularity and re-emerges only in the assignment ⟹ QFeasible step (iv) via complements.

## (iii) Rado–Gale: Gale condition ⟹ ∃ dominated assignment [THE HARD PIECE — Hall, induction on |E|]
> `radoGale : (|Y| = |E|) → (∑Y = ρ E) → (∀A, sumSmallest |A| Y ≤ ρ A) →`
> `  ∃ q : E ≃ (Y as indexed family), ∀ A, ∑_{j∈A} q_j ≤ ρ A`.
This is NOT in Mathlib. ⚠️ **There is NO clean deterministic assignment**: "sorted-Y by slot index"
fails the dominated bound 1029/1360 (`/tmp/a1_nested_construct.py`); "largest-Y → largest-width slot"
fails 206/1360; "min-index of minimal tight set" fails 1170/1360. So it MUST be the
**existence-via-Hall** argument, by **induction on `|E|`**:
- Take `y* = max Y`. **A valid pivot `e*` EXISTS** (verified: 1344/1344 instances have a valid pivot,
  `/tmp/a1_hall_encoding.py`; AND 0/1360 instances with no valid pivot, `/tmp/a1_our_rho_pivot.py`).
  The pivot-existence is the genuine Hall content: by the standard polymatroid-transversal /
  uncrossing argument, some `e*` admits `y*` while keeping the contracted instance Gale-valid.
  `Finset.all_card_le_biUnion_card_iff_exists_injective` is the Hall atom underneath; the existence is
  proven by a tight-set / uncrossing lemma (a tight set `A` with `sumSmallest(|A|,Y)=ρ(A)` exists or
  not; pick `e*` outside the closure of the minimal tight set).
- Contract: `ρ'(A) := min(ρ(A), ρ(A∪{e*}) − y*)` on `E∖{e*}`. This is again monotone-submodular-
  integral, `∑(Y∖y*) = ρ'(E∖e*)`, and the residual Gale condition holds (verified 1344/1344). Recurse.
- **STRATEGY NOTE.** This is the wall. If the general Rado-via-Hall walls in Lean, the controller's
  FALLBACK is Route S (bubble-transport, `a1-achiever-design.md §ROUTE S`, fully explicit, 0/19525, no
  abstract theorem — but L²-fiddly). Do not sink unbounded time into (iii); escalate to the controller
  for the S fallback if Hall resists. (A SECOND fallback worth knowing: Route BG, the backward
  min-suffix greedy on `M` directly, 0/19525, no transport — `§ROUTE BG`; its window-non-emptiness is
  the same Hall content but positioned concretely, may transcribe more easily than abstract Rado.)

## (iv) Assignment ⟹ QFeasible [clause-algebra; verified `/tmp/a1_rado_gale.py` 0/1360]
From `∑_{j∈A} q_j ≤ ρ(A) ∀A` and `∑q = ρ(E) = ∑Y = S_L`:
- **(U)** prefix `A={0,…,n−1}`: `ρ(A) = S_n` (item ii), so `P_n = ∑_{j<n} q_j ≤ S_n`. ✓
- **(L)** complement: `q_j = ∑q − ∑_{A=E∖{j}} q_j ≥ ρ(E) − ρ(E∖{j})`. For `j ≥ 1`, `min(E∖{j}) = 0` so
  `ρ(E) − ρ(E∖{j}) = M⁽ʲ⁺¹⁾`. ✓ (For `j=0`: the stronger `q_0 ≥ M⁰+M¹−min(M⁰,M¹) = max(M⁰,M¹)`.)
- **(Ladm)** suffix `A={n,…,L−1}`: `∑_{j≥n} q_j ≤ ρ(A) = ∑_{j≥n}M⁽ʲ⁺¹⁾ + C_n`, so
  `P_n = S_L − ∑_{j≥n}q_j ≥ S_L − ∑_{j≥n}M⁽ʲ⁺¹⁾ − C_n = S_n − C_n`. Since `C_1 = min(M⁰,M¹) =
  admBound_0` and `C_n ≤ Mⁿ = admBound_{n−1}` for `n≥2`, this gives (Ladm). ✓
- **(T)** `P_L = ∑q = S_L`. ✓
All four are `omega`/`Finset.sum` algebra once the assignment is in hand.

## (v) Perm-invariance reduction `minMval M = minMval (sort M)` [verified `/tmp/a1_perm_invariance.py` 0/3000]
The trunk theorem is on general positional `M`; the achiever `Y` and `∑M²` depend only on `sort M`.
Route B is the ONLY route that does NOT need a transport — it builds the assignment **directly on `M`**
(the rank `ρ` uses `M`'s own positional prefix-mins `C_i`). So **(v) is NOT needed for Route B's upper
bound** — Route B produces `T* ∈ Adm M` directly. (The perm-invariance is only needed if you take
Route S/T, which build on `sort M` and transport back. Listed here for completeness / fallback; for
Route B, skip it.) ⚠️ This is a real advantage of B over S/T flagged in the de-risk: **no transport.**

---

## Net for a114e07e
- (i) `ρ` mono+submodular — cover-decomposition algebra. (ii) Gale = green #74 — nested-ρ prefix
  collapse (the big win; reuses #74 directly, no dual). (iv) assignment ⟹ QFeasible — complement/suffix
  algebra. (v) NOT needed for Route B (no transport — B builds on `M`). **(iii) Rado-via-Hall is THE
  piece** — existence of a dominated assignment by induction on `|E|`, pivot-existence the Hall content
  (no deterministic pivot; uncrossing/tight-set). If (iii) walls, escalate for Route S fallback.
- Value chain after the assignment: `edgeQ(telescope(M,q)) = q` (green D1) ⟹ `∑edgeQ² = ∑Y²` ⟹
  `2·Mval(T*) = ∑Y² − ∑M²` (#74 factor-2 identity, green) ⟹ `lambdaCore ≤ cleanCore`; with #45 (LB,
  green) ⟹ `lambdaCore_eq_clean`, Skeleton sorry 5→4.
- Reproducible: `/tmp/a1_rado_gale.py` (ρ poly + Gale⟺assignment + assignment⟹QFeasible, 0/1360),
  `/tmp/a1_nested_assignment.py` (Gale = #74, 0/1360), `/tmp/a1_hall_encoding.py` +
  `/tmp/a1_our_rho_pivot.py` (pivot existence 1344/1344, no-deterministic-pivot), `/tmp/a1_rado_
  induction.py` (searched-pivot construction 0/1360). Codex prompt/answer: `codex/a1-existence-*.md`,
  `codex/a1-greedy-redteam-*.md`.
