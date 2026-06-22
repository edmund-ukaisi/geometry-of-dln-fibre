# Thread 07 — Thm 5.6 (the 5gon) Lean-proof STRATEGY, pinned over the real CTheta encoding

> Seat: `pen-and-paper`, obstruction-flavoured (pin the exact statement + the proof skeleton; no Lean).
> All load-bearing claims EXACT-integer verified — `scratch/verify_thm56_lean.py`, 699 checks across
> 20 dimension vectors (monotone, non-monotone, with zeros, N=0..3), 0 failures. Decorrelated Codex
> consult under `codex/`. NO Lean written; this is a certificate the controller turns into Lean.

**VERDICT: STRATEGY PINNED, build-ready.** Thm 5.6 = a peeling induction on `N` (peel `Fin.last`),
resting on FOUR exact splits — all verified on the real ℤ-indexed `codimForm`/`extendℤ` — and the
LANDED engine `transferRHS_eq`. The bijection, the codim split, the Pm split, and the inner-sum =
`transferRHS` link are each certified. Honest size: **~2 files (~400–600 lines), 1 substantive grind**
(the bijection's membership/`kostantAt` bookkeeping). The classical q-series content is ALREADY landed
(`durfee`, `transferRHS_eq`); thread 07 adds only the combinatorial peel.

---

## 1. The pinned Thm 5.6 statement (Lean form, against the real defs)

**(a) Indexing "all Kostant partitions of d".** CTheta's `kostantPartitions d r` is corner-graded by
`r = m (0, Fin.last N)`. The corners are disjoint (`m` determines `r`), so the biUnion over a range
covering all corners gives "all Kostant partitions". **Corner-range fact (verified, check A):** for
`N ≥ 1`, `kostantPartitions d r` is nonempty exactly for `r ∈ 0..(min_k d_k)`; for `N = 0`, only at
`r = d 0`. The full interval `[0,N]` covers EVERY vertex, so `m (0,last) ≤ d_k` for all `k` — this is
why the cap is `min_k d_k`, NOT `min (d 0) (d (last))` (the brief's first guess fails on e.g.
`d = (2,1,3,2)`: `min(d0,dN)=2` but max corner `=1`, pinched by `d_1=1`; and on `N=0` `d=(5,)` the
only corner is `5`, not `0`).

BUT for the biUnion any cap `≥ min_k d_k` is CORRECT — extra `r` layers are empty and contribute
nothing (verified, check B/Cp, for all three caps `min(d0,dN)`, `d0`, `min_k d_k`). **Recommended cap:
`Finset.range (d 0 + 1)`** — i.e. `r ∈ 0..d_0`. Reason: `m (0,last)` is one summand of the Kostant
sum at vertex `0` (`d_0 = ∑_j m (0,j)`), so `m (0,last) ≤ d_0` is the most DIRECT bound (no `min`, no
multi-vertex argument), and it covers `min_k d_k ≤ d_0` and the `N=0` case `d_0`. Disjointness for
`Finset.sum_biUnion`: trivial — corner value is a function of `m`.

> **Decision for the controller (statement form).** Prove Thm 5.6 as the **corner-free single sum**
> (the induction's natural target — it does NOT respect the corner grading), then derive the
> `Qseries`-graded form as a one-line corollary via `Finset.sum_biUnion`. Concretely introduce a
> corner-free `kostantAll d` (= `kostantPartitions` minus the `m (0,last) = r` conjunct), or define it
> as the biUnion; both verified equal (check B).

The two equivalent target shapes (both verified = `Pmult d`, checks C / Cp):

```
-- corner-free single sum (INDUCTION TARGET):
Pmult d = ∑ m ∈ kostantAll d, X^(codimForm N (extendℤ m)).toNat * Pm N m
-- corner-graded (the Qseries form, as a corollary):
Pmult d = ∑ r ∈ Finset.range (d 0 + 1), Qseries d r
```
where `kostantAll d = Finset.biUnion (Finset.range (d 0 + 1)) (kostantPartitions d ·)` and
`Qseries d r = ∑ m ∈ kostantPartitions d r, X^(codimForm N (extendℤ m)).toNat * Pm N m` (LANDED).

**(b) LHS / summand confirmed.** `Pmult d = ∏ᵢ P (d i)` (LANDED, `QSeries.Pmult`) and
`Pm N m = ∏_{p ∈ upperPairs N} P (m p)` (LANDED, `QSeries.Pm`, the upper triangle `i ≤ j`) are the
right LHS and summand. The summand exponent is `(codimForm N (extendℤ m)).toNat` (LANDED, matches
`Qseries`). `codimForm` is `≥ 0` on Kostant partitions (sum of products of nonneg multiplicities),
so `.toNat` is honest.

---

## 2. The peeling induction on N (peel `Fin.last N`)

**Induction on `N`**, theorem stated for `d : Fin (N+1) → ℕ`. Codex (decorrelated) independently
recommended the SAME scheme.

### Base `N = 0`  (`d : Fin 1 → ℕ`)
Single interval `(0,0)`; `kostantAt` forces `m (0,0) = d 0`; the unique partition. `codimForm 0 = 0`
(outer sum over `Finset.Icc (1:ℤ) 0 = ∅`). `Pm 0 m = P (m (0,0)) = P (d 0)`. RHS `= X^0 · P (d 0) =
P (d 0) = Pmult d`. Structural; no q-series.

### Step `N → N+1`  (`d : Fin (N+2) → ℕ`)
Residual `d' := d ∘ Fin.castSucc : Fin (N+1) → ℕ` (drop the last vertex). Goal: collapse the RHS to
`P (d (Fin.last (N+1))) · RHS5 d'`, then IH (`RHS5 d' = Pmult d'`) and the trivial multiplicative
`Pmult d = P (d (Fin.last (N+1))) · Pmult d'` (= `Fin.prod_univ_castSucc`).

The collapse is FOUR pieces (1)–(4), glued by ONE summation lemma.

### (1) The bijection  `kostantAll d  ↔  Σ_{m' ∈ kostantAll d'} (last-column data)`
**Forward** `m ↦ (m', x)` (verified, check G, round-trip + coverage + no-collision):
- `m' : Fin (N+1) × Fin (N+1) → ℕ`, **merge old column N+1 into N** (`Fin.lastCases` on the second
  index `J : Fin (N+1)`):
  - `J = Fin.last N`  →  `m' (I, last) = m (castSucc I, castSucc (last N)) + m (castSucc I, last (N+1))`
    (the boundary merge: `m'_{i,N} = m_{i,N} + m_{i,N+1}`);
  - `J = castSucc J₀`  →  `m' (I, castSucc J₀) = m (castSucc I, castSucc (castSucc J₀))` (untouched).
- last-column data `x` = the last column `j = N+1` of `m`: `x i = m (castSucc⁺ i, Fin.last (N+1))`
  for `i ≤ N`, plus `x_{N+1} = m (last, last)`. Constraints `0 ≤ x_i ≤ b_i := m' (i, last)` (`i ≤ N`)
  and `∑ x = d (last (N+1))` (= the Kostant equation at the new vertex).

**Inverse** `(m', x) ↦ m`: keep columns `j ≤ N-1`; split the boundary column
`m (i, N) = b_i − x_i`, `m (i, N+1) = x_i` (with `b_i = m' (i, last)`); `m (last, last) = x_{N+1}`.

**Finset lemma (the carry):** `Finset.sum_bij'` (Codex's pick) over a sigma-finset
`(kostantAll d').sigma (fun m' => admissibleXs m')`, OR `Finset.sum_fiberwise` partitioning
`kostantAll d` by `m ↦ m'` then collapsing each fibre by (3). **Recommendation:** use the
**fiberwise** form (`Finset.sum_fiberwise`/`Finset.sum_biUnion` over `m'`-fibres) — it lets piece (3)
(the per-fibre collapse, the cleanest verified statement) be a standalone lemma, and avoids
constructing the `admissibleXs` finset and a second bijection to the `x`-data. `sum_bij'` is the
fallback if the fibre Finset is awkward.

### (2) The codimForm split (verified exact on the real ℤ-form, check D, 201 cases)
```
codimForm (N+1) (extendℤ m) = codimForm N (extendℤ m') + Δ_b(x)
Δ_b(x) = ∑_{0 ≤ a < u ≤ N+1} (b_a − x_a) · x_u           (b_{N+1} := 0)
```
The two `extendℤ` have different boxes (`0..N+1` vs `0..N`) — the split is on the real ℤ-indexed
nested `Finset.Icc` form, verified literally (not on a dict abstraction). `Δ_b` depends on `m'`
(through `b_i = m' (i, last)`) and `x`.

### (3) The Pm split + per-fibre collapse (verified, check E, 57 fibres)
The clean per-fibre statement (what the fiberwise route consumes directly):
```
∑_{m ∈ fibre(m')} X^(codimForm (N+1) (extendℤ m)).toNat · Pm (N+1) m
  =  X^(codimForm N (extendℤ m')).toNat · Pm N m' · P (d (Fin.last (N+1)))
```
Proof of (3): pull out `X^{c(m')}` and the `j ≤ N-1` factors of `Pm` (common to the fibre), then the
inner sum over `x` of `X^{Δ_b(x)} · (last-column P-factors)` collapses by (4).

### (4) Inner sum = `transferRHS` (LANDED `transferRHS_eq` discharges it; verified, check F, 80 cases)
With `b := List.ofFn (fun i : Fin (N+1) => m' (i, Fin.last N))` (the merged column, Codex's
List bridge):
```
∑_{x : ∑x = d(last), 0≤x_i≤b_i} X^{Δ_b(x)} · P(x_{N+1}) · ∏_{i≤N} (P(b_i−x_i)·P(x_i))
  =  transferRHS b (d (Fin.last (N+1)))
  =  P (d (Fin.last (N+1))) · (b.map P).prod          -- transferRHS_eq, LANDED (axiom-clean)
```
**Key structural finding (verified):** the inner fibre-sum satisfies *exactly* `transferRHS`'s own
recursion (peel `x_0` first → `min b_0 d` range + residual `d − x_0`), so it can be proved equal to
`transferRHS b d` by an induction MIRRORING the `transferRHS` recursion — no detour through a flat
constraint set. The thread-04 exponent split `Δ_b(x) = (b_0−x_0)(d−x_0) + Δ'_{b'}(x')` (pure `ring`)
is the per-step glue. Then `(b.map P).prod = ∏_{i≤N} P (b_i) = ∏_{i≤N} P (m' (i,last))` are exactly
the column-`N` factors of `Pm N m'`, so (3)+(4) give `∑_fibre = X^{c(m')} Pm N m' · P(d last)`.

Summing (3) over `m' ∈ kostantAll d'` via the fiberwise lemma:
`RHS5 d = P(d last) · ∑_{m'} X^{c(m')} Pm N m' = P(d last) · RHS5 d'`. With IH and
`Fin.prod_univ_castSucc`: `RHS5 d = P(d last) · Pmult d' = Pmult d`. ∎

---

## 3. The single most-likely-to-break Lean step

**The bijection's membership obligations — specifically `m' ∈ kostantAll d'` (the `kostantAt` equation
at the new last vertex + the merged-column support `i ≤ j`).** Codex (decorrelated) independently
flagged this same step. It combines: `Fin.castSucc`/`Fin.lastCases` index arithmetic, the
`if p.1 ≤ p.2` support condition at the boundary column, and the merge `b_i = m_{i,N}+m_{i,N+1}`
satisfying `kostantAt d' m' k` for each residual vertex `k`. The `kostantAt` sum at vertex `k < N`
is unchanged (no interval to/through the dropped vertex contributes differently); at the new last
vertex `k = N` (old vertex N) the merged column supplies the count. This is bookkeeping, not deep,
but it is the bulk of the grind — `mem_kostantPartitions` unfolds it into four conjuncts that must
each be re-established for `m'` (and for the inverse `m`).

Secondary risk: the `List.ofFn ↔ Fin.prod` bridge — relating `(b.map P).prod` to
`∏_{i : Fin (N+1)} P (m' (i, last))` (the column-N factors of `Pm N m'`). Routine
(`List.prod_ofFn` / `Finset.prod`), but a named bridge lemma is cleanest. NO q-series risk remains —
`durfee` and `transferRHS_eq` are LANDED and axiom-clean.

---

## 4. Honest size

- **Statement + corner-free `kostantAll` + corner range + biUnion equivalence** (§1): ~1 file,
  ~120 lines. The corner-range/biUnion facts are elementary `Finset` reasoning.
- **The peel induction** (§2): ~1 file, ~300–450 lines. The bijection (1) (forward/inverse +
  membership) is ~half of it; (2) codimForm split is a reindex + `ring`; (3) per-fibre collapse is a
  `Finset` factor-out; (4) is the recursion-matching induction onto LANDED `transferRHS_eq`.

**TOTAL ~2 files, ~400–600 lines, 1 substantive grind (the bijection bookkeeping).** This is
SMALLER than the original thread-03 estimate (~2–3 files for S0) because the q-series engine
(`durfee` M2, `transferRHS_eq` M3a) is already landed — thread 07 is the pure-combinatorial peel.

---

## 5. Next construction / consult to settle the open part

The one place a Lean grind could surprise: the `kostantAt`-at-the-merged-vertex membership proof. If
it balloons, the cheapest de-risk is to FIRST land a standalone lemma
`kostantAll d ≃ Σ_{m'} admissibleXs m'` (the bijection as a `Finset` equiv, NO q-series), test it
compiles, then bolt on the weight identity. Recommend the formaliser build (1) (the bijection +
membership) and verify it green BEFORE attempting the summed weight identity (2)–(4) — that isolates
the single risk. A focused Codex consult on the `kostantAt`-merge proof obligation (with the unfolded
`mem_kostantPartitions` conjuncts in hand) is the natural second consult if it stalls.

## Artifacts
- `scratch/verify_thm56_lean.py` — the consolidated certificate (699 checks, 0 fail; reuses thread-03
  `ctheta.py`/`qseries.py`). Checks A–G map to §1–§2.
- `codex/peel-structure-{prompt,answer}.md` — decorrelated structuring consult (hypothesis withheld;
  Codex converged on the same induction scheme + flagged the same hardest step).
