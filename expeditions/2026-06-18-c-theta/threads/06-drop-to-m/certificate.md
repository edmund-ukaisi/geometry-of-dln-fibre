# Drop-to-m active-support reduction — formaliser-ready certificate

**Thread:** 06-drop-to-m (pen-and-paper, `obstruction` direction — a scoped no-go: a minimiser
*cannot* have support past `m`). **Target:** the wall of the explicit-formula tail (Thm 7.10 r=0).

**Status:** PROVEN (exact algebra, every step closed). Decorrelated Codex (xhigh) audited the proof
line-by-line and found no gap; it supplied the `A_l`-monotonicity derivation folded in below, which
makes the well-definedness and the separation lemma formaliser-clean (no argmax bookkeeping). Codex
artefact: `codex/dropm-prompt.md` + `codex/dropm-answer.md`.

---

## 0. Frame — objects, exactly as committed in Lean

From `lean/DLNFibre/Core/CThetaQIP.lean`:

* `d : Fin (N+1) → ℕ`, hypothesis `hd : Monotone d`. On the reduced rank-0 problem `d` is the
  weakly-increasing rearrangement `d'`; write `d'_i := d i` for `i : Fin (N+1)`, so `d'_0 = d 0`.
  Weak increase: `d'_0 ≤ d'_1 ≤ … ≤ d'_N`. Positivity `d'_0 ≥ 1` is **not** needed for drop-to-m as
  stated here (see §1 note), but the feasible set is empty when `d'_0 = 0`, so the interesting regime
  is `d'_0 ≥ 1`.
* `e : Fin N → ℕ` (paper `e_1 … e_N`; Lean `e i` = paper `e_{i+1}`).
* `qipFeasible d = Finset.finAntidiagonal N (d 0) = { e : Fin N → ℕ | ∑ i, e i = d'_0 }`.
* `Gqip d e = ∑_{j ≤ i} e_i (e_j + d'_{j} − d'_{j−1})` (Lean: `d j.succ − d j.castSucc`).
* `qipMin d hne = (qipFeasible d).inf' hne (Gqip d)`; committed `cCodim d 0 = qipMin d` (Monotone d).

**Square-completion bridge** (symbolic, verified N≤5; re-verified N=4 here). With `s_i := d'_0 − d'_i`
(so `s_i ≤ 0`, `s` weakly decreasing):

> `2·Gqip d e − (∑ e)² = ∑_{i=1}^N (e_i − s_i)² − ∑_{i=1}^N s_i²`.

On the feasible set `∑ e = d'_0` the term `(∑ e)²` is the constant `d'_0²` and `∑ s_i²` is a constant.
Hence **on `qipFeasible`, minimising `Gqip d` ⇔ minimising `Φ(e) := ∑_i (e_i − s_i)²`** over integer
`e ≥ 0` with `∑ e = d'_0`. The minimiser *sets* coincide. All of §1–§4 is stated for `Φ`; the bridge
is a separate small tide (the square-bridge), proved *before* this one is used.

---

## 1. The statement (with `m` pinned by a decidable predicate)

Define, over the weakly-increasing `d'`, the integer
```
A_l := (∑_{i=0}^{l} d'_i) − l · d'_l ,    l ∈ {1, …, N}.
```
The predicate `Pred(l) := A_l ≥ 0`, i.e. `∑_{i=0}^{l} d'_i ≥ l · d'_l`, is **decidable** (a `ℕ`/`ℤ`
inequality). Set
```
m := max { l ∈ {1, …, N} : A_l ≥ 0 }.
```

**Lemma 1 (well-definedness — the qualifying set is an initial interval `{1,…,m}`).**
For `Monotone d`:
* `A_1 = d'_0` (so `A_1 ≥ 0` always: `l = 1` qualifies, the set is nonempty, `m ≥ 1`);
* `A_{l+1} = A_l − l·(d'_{l+1} − d'_l) ≤ A_l` (monotone non-increasing, by weak increase).

Hence `{ l : A_l ≥ 0 }` is a downward-closed prefix `{1, …, m}`; `m` is well-defined, and equivalently
`m = ` the largest `l` with `A_l ≥ 0` `= ` (`A_l ≥ 0` for all `l ≤ m`, `A_l < 0` for all `l > m`).
*(Formaliser: `m` is a threshold of an antitone `Bool`-predicate — no argmax needed. `Nat.findGreatest`
over `Pred`, or `Finset.max'` of the filter with `1 ∈ filter` for nonemptiness. The antitone-prefix
fact lets you characterise `m` by `Pred m ∧ ¬Pred (m+1)` when `m < N`.)*

**Theorem (drop-to-m).** For `Monotone d`, every minimiser `e*` of `Φ` over
`{ e : Fin N → ℕ | ∑ e = d'_0 }` satisfies
```
e*_i = 0   for all i with  m < i ≤ N   (Lean: e* ⟨i⟩ = 0 for i ≥ m, using 0-based index = paper i+1).
```
Stronger form actually proved (used in the contradiction): **any feasible `e` with `e_k ≥ 1` for some
`k > m` is not a minimiser** — there is an explicit single-unit transfer strictly decreasing `Φ`.

*Note on positivity.* `d'_0 ≥ 1` is **not** required for the theorem statement; it is only needed to
make `qipFeasible` nonempty (`∑ e = d'_0`). `A_1 = d'_0 ≥ 0` holds even at `d'_0 = 0`, so `m` is still
well-defined. The drop argument uses only weak increase, integrality, and feasibility.

---

## 2. Strict separation lemma (the load-bearing inequality)

**Lemma 2 (separation).** If `m < N` then
```
m · d'_{m+1}  >  S ,      where   S := ∑_{i=0}^{m} d'_i   (= the brief's S = S_m).
```
*Proof.* `m < N` ⟹ `m+1 ∈ {1,…,N}` and `m+1` is past the prefix, so `A_{m+1} < 0`:
```
A_{m+1} = (∑_{i=0}^{m+1} d'_i) − (m+1)·d'_{m+1} < 0
        ⟺ (∑_{i=0}^{m} d'_i) + d'_{m+1} < (m+1)·d'_{m+1}
        ⟺ S < m·d'_{m+1}.      ∎
```
Integer cross-multiplied form for the formaliser: **`m · d'_{m+1} > S`** (strict `ℕ`/`ℤ` inequality;
no division). The rational reading is `S / m < d'_{m+1}`, but never divide — carry `m · d'_{m+1} > S`.

This is exactly the negation of `Pred(m+1)` from §1; in Lean it is `not_le.mp` applied to the
`¬Pred(m+1)` half of the threshold characterisation, then `omega`/`ring`-rearranged.

**Within-prefix companion (needed in §4, recorded here).** For `1 ≤ i ≤ m`, `Pred(m)` gives
`S ≥ m·d'_m`, hence `d'_m ≤ S/m`, hence (weak increase) `d'_i ≤ d'_m ≤ S/m`. Integer form:
`m · d'_i ≤ m · d'_m ≤ S` for `i ≤ m`.

---

## 3. The unit-transfer construction (strict decrease — exact per-term arithmetic)

Let `e*` be a minimiser with `e*_k ≥ 1` for some `k > m` (so `m < N`, hence Lemma 2 applies).

**Shifted coordinate.** `u_i := e*_i − s_i = e*_i − d'_0 + d'_i ∈ ℤ` (`i = 1,…,N`).

**Target index.** Choose `j ∈ {1,…,m}` minimising `u_j` (well-defined: `m ≥ 1` by Lemma 1; in Lean,
`Finset.exists_min_image` / `Finset.min'` over `Finset.Icc 1 m` or `(Finset.range m)`). Note `j ≠ k`
since `j ≤ m < k`.

**Modified vector.**
```
e'_i := e*_i + 1   if i = j
        e*_i − 1   if i = k
        e*_i       otherwise.
```
* Nonnegativity: `e'_k = e*_k − 1 ≥ 0` (since `e*_k ≥ 1`); all other coords unchanged or increased. ✓
* Feasibility: `∑ e' = ∑ e* + 1 − 1 = d'_0`. ✓  Integrality: preserved. ✓

**Per-term cost change** (only coordinates `j, k` move; `Φ` is a coordinatewise sum of squares):
```
Φ(e') − Φ(e*) = [(e'_j − s_j)² − (e*_j − s_j)²] + [(e'_k − s_k)² − (e*_k − s_k)²]
              = [(u_j + 1)² − u_j²]            + [(u_k − 1)² − u_k²]
              = [2 u_j + 1]                    + [−2 u_k + 1]
              = 2 ( u_j − u_k + 1 ).
```

**The gap `u_k − u_j ≥ 2`** (so `u_j − u_k + 1 ≤ −1 < 0`, strict decrease):

*Lower bound on `u_k`.* `e*_k ≥ 1` and `d'_k ≥ d'_{m+1}` (weak increase, `k ≥ m+1`):
```
u_k = e*_k − d'_0 + d'_k  ≥  1 − d'_0 + d'_{m+1}.
```

*Upper bound on `u_j` (the min ≤ the average — rigorous, no rounding).*
```
u_j = min_{1≤r≤m} u_r  ≤  (1/m) ∑_{r=1}^m u_r
                       =  (1/m) ( ∑_{r=1}^m e*_r + ∑_{r=1}^m d'_r − m d'_0 ).
```
Now `∑_{r=1}^m e*_r ≤ ∑_{r=1}^N e*_r = d'_0` (all `e* ≥ 0`), and `∑_{r=1}^m d'_r = S − d'_0`. So
```
u_j ≤ (1/m)( d'_0 + (S − d'_0) − m d'_0 ) = S/m − d'_0.
```

*Combine.*
```
u_k − u_j ≥ (1 − d'_0 + d'_{m+1}) − (S/m − d'_0) = 1 + d'_{m+1} − S/m.
```
By Lemma 2, `d'_{m+1} − S/m > 0` (i.e. `m·d'_{m+1} > S`), so `u_k − u_j > 1`. Since `u_k − u_j ∈ ℤ`,
`u_k − u_j ≥ 2`. Hence
```
Φ(e') − Φ(e*) = 2(u_j − u_k + 1) ≤ 2(−1) = −2 < 0,
```
contradicting minimality of `e*`. Therefore no minimiser has `e*_k ≥ 1` for `k > m`: `e*_i = 0` for
`i > m`. ∎

**Formaliser note — how to avoid `ℚ`.** Do not divide. Multiply through by `m > 0`:

* min-≤-average in integer form: `m · u_j ≤ ∑_{r=1}^m u_r` (i.e. `m · u_j ≤ ∑_{r=1}^m u_r` because
  `u_j` is the min of `m` terms — `Finset.card_nsmul_le_sum` / `m • min ≤ ∑`). Note `u_r ∈ ℤ`; the sum
  identity `∑_{r=1}^m u_r = ∑_{r=1}^m e*_r + (S − d'_0) − m·d'_0` is a `ℤ` rearrangement.
* So `m · u_j ≤ S − m·d'_0` (using `∑_{r≤m} e*_r ≤ d'_0`).
* `m · u_k ≥ m·(1 − d'_0 + d'_{m+1})`.
* `m·(u_k − u_j) ≥ m·(1 − d'_0 + d'_{m+1}) − (S − m d'_0) = m + (m·d'_{m+1} − S) ≥ m + 1` (Lemma 2:
  `m·d'_{m+1} − S ≥ 1`). Since `m ≥ 1`, `m·(u_k − u_j) ≥ m + 1 > m`, so `u_k − u_j ≥ 2` (divide the
  integer inequality `m·(u_k−u_j) ≥ m+1` by `m`: `u_k − u_j ≥ ⌈(m+1)/m⌉ = 2`). This keeps everything
  in `ℤ`/`ℕ` — `Lemma 2` enters as `m·d'_{m+1} − S ≥ 1`, the integer form of the strict inequality.

The decrease `Φ(e') − Φ(e*) = 2(u_j − u_k + 1) ≤ −2` is then a pure `ring`/`omega` step from
`u_k − u_j ≥ 2`.

---

## 4. The `e ≥ 0` caveat and the ORDERING obligation (drop BEFORE rounding)

After drop-to-m, the problem restricts to the **m-face** `{ e : ∑_{i=1}^m e_i = d'_0, e_i ≥ 0,
e_i = 0 for i > m }`. On the m-face the rounded optimum is
```
a := ⌊ S/m + ½ ⌋ ,   δ := S − m·a ,   e_i = a − d'_i + Δ_i   (i ≤ m),
```
with `Δ ∈ {0, ε}^m`, `ε = sgn δ`, exactly `|δ|` coordinates carrying `ε` (the integer-square lemma,
separate tide).

**In-face nonnegativity (clean).** For `i ≤ m`: `d'_i ≤ d'_m ≤ S/m` (the within-prefix companion of
Lemma 2, from `Pred(m)`), and `a = ⌊S/m + ½⌋ ≥ ⌊S/m⌋ ≥ d'_m ≥ d'_i` (using `S/m ≥ d'_m` integer, so
`⌊S/m⌋ ≥ d'_m`). Hence `e_i = a − d'_i (+Δ_i) ≥ 0` on the m-face. Verified `a ≥ d'_i` for all `i ≤ m`
on the full random battery (0 failures, 40000 cases). *(The `Δ_i ∈ {0, ±1}` correction is dominated:
`a ≥ d'_m` with slack, and the `−1` case only at coords where `e_i ≥ 1`.)*

**Why it FAILS without the drop — the ordering obligation.** The reason in-face nonnegativity is clean
is that `i ≤ m` ⟹ `d'_i ≤ d'_m ≤ a`. For `i > m` this protection is **gone**: `d'_i ≥ d'_{m+1} > S/m`
(Lemma 2), so `a − d'_i` is typically negative and the naive "round on all N coordinates" would either
produce a negative entry (infeasible) or, in the boundary regime, keep spurious positive support.

Concretely (exact witnesses, not a gesture):
* `d' = (4,5,8,9,10,10)`, N=5: `m = 2`, `S = Σ_{0..2} d' = 4+5+8 = 17`, `S/m = 17/2 = 8.5`,
  `a = ⌊8.5+0.5⌋ = 9`. Then `d'_{m+1} = d'_3 = 9 = a`, so `a − d'_3 = 0 ≥ 0`: the naive
  full-coordinate round does **not** flag `e_3` as negative, yet the true minimisers are
  `(3,1,0,0,0)` and `(4,0,0,0,0)` — both drop `e_3 = 0`. The drop is **not** detectable from
  rounding-nonnegativity here; it is a separate optimality fact.
* `d' = (2,5,6,7,10)`, N=4: `m=2`, `S=2+5+6=13`, `a=⌊13/2+½⌋=7`, `d'_3 = 7 = a`, `a−d'_3 = 0`.
  Minimisers `(1,1,0,0)`, `(2,0,0,0)` — drop `e_3`.

So: **the drop-to-m theorem must be proved BEFORE the rounding/assembly step**, and the rounding step
must be stated *on the m-face* (coordinates `1..m` only), not on all `N` coordinates. The minimiser
characterisation is `{ drop to m-face } ∩ { rounded optimum on the m-face }`; the first conjunct is
this certificate, the second is the integer-square lemma + assembly tide. Stating the rounding on all
`N` coordinates and arguing nonnegativity-⟹-support is **wrong** (the witnesses above show the
boundary `d'_{m+1} = a` where rounding alone keeps support that the true minimiser drops).

---

## 5. Lean-shaped targets for the formaliser

Names are suggestions; types are the contract. Everything is over the committed `Gqip`/`qipFeasible`
once the square-bridge (`Phi`) is in place. `S N d` denotes `∑_{i=0}^{m} d'_i` as an `ℤ`/`ℕ` sum.

```
-- §1 predicate and threshold
def qipA (d : Fin (N+1) → ℕ) (l : ℕ) : ℤ :=
  (∑ i in Finset.range (l+1), (d i : ℤ)) - l * (d ⟨l, _⟩ : ℤ)         -- A_l
def qipPred (d) (l : ℕ) : Prop := 0 ≤ qipA d l                          -- decidable
noncomputable def qipM (d : Fin (N+1) → ℕ) : ℕ := Finset.findGreatest (qipPred d) N
                                                                        -- or Nat.findGreatest

theorem qipA_one  (hd : Monotone d) : qipA d 1 = (d 0 : ℤ)              -- A_1 = d'_0  (≥ 0)
theorem qipA_antitone (hd : Monotone d) {l} (hl : l < N) :
    qipA d (l+1) = qipA d l - l * ((d ⟨l+1,_⟩ : ℤ) - d ⟨l,_⟩)          -- A_{l+1} ≤ A_l
theorem qipM_ge_one (hd : Monotone d) : 1 ≤ qipM d
theorem qipPred_of_le_qipM  (hd) {l} (h : 1 ≤ l) (h' : l ≤ qipM d) : qipPred d l   -- prefix ⇒ Pred
theorem not_qipPred_of_gt_qipM (hd) {l} (h : qipM d < l) (h' : l ≤ N) : ¬ qipPred d l

-- §2 separation
theorem qip_separation (hd : Monotone d) (hm : qipM d < N) :
    (S := ∑ i in Finset.range (qipM d + 1), d i)        -- S = Σ_{0..m} d'
    (qipM d) * d ⟨qipM d + 1, _⟩ > S                     -- m · d'_{m+1} > S   (ℕ, strict)
theorem qip_within_prefix (hd : Monotone d) {i} (h1 : 1 ≤ i) (h2 : i ≤ qipM d) :
    (qipM d) * d ⟨i,_⟩ ≤ S                               -- m·d'_i ≤ S   (i ≤ m)

-- §3 the wall: drop-to-m
theorem qip_unit_transfer_decreases
    (hd : Monotone d) (e : Fin N → ℕ) (hfeas : e ∈ qipFeasible d)
    {k : Fin N} (hk : qipM d ≤ (k : ℕ)) (hek : 1 ≤ e k) :
    ∃ e' ∈ qipFeasible d, Phi d e' < Phi d e                -- explicit e' from §3; strict
theorem qip_minimiser_support_le_m
    (hd : Monotone d) (e : Fin N → ℕ) (hfeas : e ∈ qipFeasible d)
    (hmin : ∀ e'' ∈ qipFeasible d, Phi d e ≤ Phi d e'') :
    ∀ i : Fin N, qipM d ≤ (i : ℕ) → e i = 0                -- e_i = 0 for i > m  (0-based ≥ m)
```

**Index discipline.** Lean `e i` = paper `e_{i+1}`. Paper "`e_i = 0` for `i > m`" becomes, in 0-based
`Fin N`, `e ⟨i⟩ = 0` for `i ≥ m` (the coordinate carrying paper-index `i+1 > m` is 0-based `i ≥ m`).
The target index `j ≤ m` (paper) is a 0-based index `< m`; the source `k > m` (paper) is 0-based `≥ m`.

**Proof skeleton for `qip_unit_transfer_decreases`** (the only hard one):
1. `m < N` from `hk` and `k : Fin N` (`(k:ℕ) < N`, `qipM d ≤ k` ⟹ `qipM d < N`).
2. `u i := (e i : ℤ) − d 0 + d ⟨i+1⟩`. Pick `j` = `argmin` of `u` over 0-based `Finset.range (qipM d)`
   (nonempty by `qipM_ge_one`). `j < qipM d ≤ k` so `j ≠ k`.
3. `e' = Function.update (Function.update e j (e j + 1)) k (e k − 1)`; `e' ∈ qipFeasible` by
   `Finset.sum` bookkeeping (`finAntidiagonal` membership ⟺ `∑ = d 0`).
4. `Phi d e' − Phi d e = 2*(u j − u k + 1)` by expanding the two changed squares (`ring`).
5. `u k − u j ≥ 2` via the integer chain in §3 "Formaliser note": `m·u_j ≤ S − m·d'_0`,
   `m·u_k ≥ m·(1 − d'_0 + d'_{m+1})`, `qip_separation` as `m·d'_{m+1} − S ≥ 1`, then
   `m·(u_k − u_j) ≥ m+1`, divide by `m ≥ 1` (`Int`/`Nat` `le_div`) ⟹ `u_k − u_j ≥ 2`.
6. Conclude `Phi d e' < Phi d e`. `qip_minimiser_support_le_m` is then `by_contra` + this lemma.

**Ordering obligation for the assembly tide (record next to the rounding lemma):** prove
`qip_minimiser_support_le_m` first; state the rounding/closed-form `e_i = a − d'_i + Δ_i` **on the
m-face** (`i < m`), with in-face nonnegativity from `qip_within_prefix`. Do NOT state rounding on all
`N` coordinates (the boundary witnesses `d'=(4,5,8,9,10,10)`, `(2,5,6,7,10)` break the
"nonneg ⟹ support" shortcut).

---

## 6. Numerical certificates (exact integer, reproduced this thread)

| `d'` | N | A-sequence `(A_1,…,A_N)` | m | S=Σ₀..ₘ | sep `m·d'_{m+1}>S` | a=⌊S/m+½⌋ | δ | C | θ=C(m,|δ|) |
|---|---|---|---|---|---|---|---|---|---|
| (2,2,2) | 2 | (2, 2) | 2 (=N) | 6 | — (m=N) | 3 | 0 | 3 | 1 |
| (8,8,11,11,11,13,13,13,15) | 8 | (8,5,5,5,−3,−3,−3,−17) | 4 | 49 | 52 > 49 ✓ | 12 | 1 | 55 | 4 |

* Ex6.2 `d=(2,2,2)` → (C,θ) = (3,1): paper ✓. No drop (m=N); support is all of `{1,2}`.
* Ex6.3 `d'=(8,8,11,11,11,13,13,13,15)` → (C,θ) = (55,4): paper ✓. Drop at m=4; brute-force
  minimisers `(4,1,1,2,0,0,0,0),(4,1,2,1,0,0,0,0),(4,2,1,1,0,0,0,0),(5,1,1,1,0,0,0,0)` — all have
  `e_i = 0` for `i > 4`. Separation `52 > 49` strict, A-sequence non-increasing as Lemma 1 predicts.
* Support-drop verified exhaustively (brute minimisers) over 3000 random weakly-increasing positive
  `d'`: 0 violations. Unit-transfer `Φ`-decrease verified over 11336 arbitrary feasible high-support
  points: 0 failures. Bound chain (`u_k ≥ …`, `u_j ≤ S/m − d'_0`, gap ≥ 2) verified over 30000: 0
  failures. In-face `a ≥ d'_i (i≤m)` over 40000: 0 failures. All exact rational/integer.

---

## 7. Close

**Firmest result.** Drop-to-m is PROVEN with exact algebra, every step closed and Codex-audited:
Lemma 1 (`A_l` antitone ⟹ qualifying set is the prefix `{1,…,m}`, `m` well-defined) → Lemma 2
(separation `m·d'_{m+1} > S`, the integer negation of `Pred(m+1)`) → §3 unit-transfer
(`Φ(e')−Φ(e) = 2(u_j−u_k+1) ≤ −2`, with the integer gap `u_k−u_j ≥ 2` from the min-≤-average bound +
separation). The reduction is to the m-face; rounding/assembly is a separate downstream tide that must
run AFTER this and be stated on the m-face only.

**Most likely thing to break it (for the formaliser).** The integer min-≤-average step
(`m·u_j ≤ ∑_{r<m} u_r`): keep it in `ℤ` via `Finset.card • (min) ≤ ∑` rather than dividing; the
`∑_{r≤m} e*_r ≤ d'_0` bound needs the *non-truncated* feasibility `∑_{all} e* = d'_0` with `e* ≥ 0`.
And the index translation (paper `i > m` ⟺ 0-based `i ≥ m`) — get the off-by-one wrong and the wall
lemma will be vacuous or false at the boundary coordinate.

**Next construction/consult to settle the open part.** The two clean downstream pieces are (a) the
integer-square lemma `min{∑ t_i² : t∈ℤ^m, ∑t=δ} = |δ|` for `|δ|≤m` (exchange `t_i ≥ t_j+2` ⟹ swap drops
`∑t²` by `2(t_i−t_j−1) > 0`) — same exchange flavour, independently small; and (b) value assembly
`C = ½(d'_0² − ∑_{i=1}^m(d'_i−d'_0)² + m(a−d'_0)² + 2(a−d'_0)δ + |δ|)` (verified 4000/4000, always
integer) + `θ = Nat.choose m |δ|`. Neither needs new ideas; both stand on this certificate's m-face
restriction.
