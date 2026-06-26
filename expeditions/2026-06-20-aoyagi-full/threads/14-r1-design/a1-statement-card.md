# A1 statement card — genuine `lambdaCore_eq_clean` (Aoyagi Lemma 3)

- **Seat:** `pp` (design). **Read-only on repo; /tmp scratch; no Lean.** Task #19.
- **Purpose:** replace the WEAK existential (fm closed by free choice ℓ=1, m=`![1,(min Mval).toNat]`,
  proving nothing about M) with the GENUINE faithful Lemma-3 statement binding the witnesses to M.

## The genuine statement (recommended — candidate (d), verified total + genuine)

```text
theorem lambdaCore_eq_clean (M : Fin (L + 1) → ℕ) :
    ∃ ℓ : Fin L,          -- ℓ ranges over {1,…,L} (use ℓ.succ or a 1..L index)
      lambdaCore M = cleanCore (ℓ+1-as-nat) (fun k : Fin (ℓ+2) => sortedSmallest M k)
```
i.e. **`∃ ℓ ∈ {1,…,L}, lambdaCore M = cleanCore ℓ (the ℓ+1 smallest entries of M)`**, where the `m`
argument of `cleanCore` is **pinned** to `sortedSmallest M ℓ` = the `ℓ+1` smallest reduced widths
(a function of `M`, NOT a free variable). One small Lean helper: `sortedSmallest M ℓ : Fin (ℓ+1) → ℕ`
= the first `ℓ+1` entries of `M` sorted ascending (`Finset`/`MonotoneOn` sort, or
`(Finset.univ.sort … ).take`).

### Why this is GENUINE (not the weak existential)

The discriminator (synthesis): `∃ x, LHS(data) = f(x)` is weak iff `f` free-covers a concrete LHS
with `x` chosen independent of the data. In the **weak** form both `ℓ` AND `m` were free, so
`cleanCore` could be tuned (m=`![1,(min Mval)]`) to hit `lambdaCore` for ANY `M` — no Aoyagi content.
In **(d)**, once `M` and `ℓ` are fixed, `m` is FORCED to be the `ℓ+1` smallest widths of `M`. The RHS
ranges over only the finite, `M`-determined set `{ cleanCore ℓ (sortedSmallest M ℓ) : ℓ ∈ Fin L }`
(at most `L` values). `cleanCore` cannot free-cover — the witness must encode `M` (via `m`). The
existential `ℓ` over the finite definable `{1,…,L}` is NOT a loophole (non-uniqueness of the achiever
is harmless). **Codex consult independently confirms (d) GENUINE** (`/tmp/codex-a1-answer.md`).

### Verified TOTAL

Exhaustive exact-rational check (`/tmp/a1_candidate_d.py`): for **every** `M` (widths ≥ 1,
`L = 1..4`, 1360 cases) there IS an `ℓ ∈ {1,…,L}` with `lambdaCore M = cleanCore ℓ (ℓ+1 smallest)`.
**1360/1360.** No Def-3 dependence — totality is carried by `lambdaCore`'s own min-definition.

### CRITICAL: it is NOT min/max over ℓ (both refuted — do not "simplify" to an extremum)

Codex's first instinct (candidate (c), `lambdaCore = min_ℓ cleanCore ℓ (ℓ+1 smallest)`) is **FALSE**
— refuted exactly (`/tmp/a1_refute_c.py`): `M=[1,1,4]`, `lambdaCore = 1/2`, but `ℓ=2` gives
`cleanCore(2,[1,1,4]) = 0 < 1/2` (the large width `4` swept into the balanced split `q=[3,3]`
over-counts ⇒ the "wrong" ℓ undercuts). `max_ℓ` also fails (`[2,2,2]`: `max = 2 ≠ 3/2`). So the
statement is genuinely **`∃ ℓ` (the achiever)** — neither min nor max. The achiever ℓ* is the one
where the balanced split on the ℓ+1 smallest is *admissible* (realizable as a `T ∈ Adm`); for other ℓ
`cleanCore(ℓ, smallest)` is not even a valid lower bound. **Do not collapse the `∃` to an extremum.**

## Proof route (Aoyagi Lemma 3; Codex route-3, corrected to per-ℓ)

1. **Balanced-split lemma** (the arithmetic core): among integer vectors of fixed length `ℓ` and
   fixed sum `P`, the balanced split (`P mod ℓ` copies of `⌈P/ℓ⌉`, rest `⌊P/ℓ⌋`) **minimises `Σqᵢ²`**.
   Standard exchange: if two parts differ by ≥ 2, moving one unit from larger to smaller strictly
   decreases `Σqᵢ²`. (Mathlib: likely `Finset`/`inner_le`-style or a direct induction; small lemma.)
2. **Reparametrise** admissible `T ∈ Adm(M)` to the H-block/gap form (design-spec §4.1, Aoyagi p.22):
   `T`'s distinct nonzero values `H₁ > … > H_{ℓ_T} = 0` at breakpoint positions `S₁<…<S_{ℓ_T+1}`, so
   `Mval(M,T) = (M^{S₁}−H₁)(M^{S₂}−H₁) + Σ_{j≥2}(H_{j−1}−H_j)(M^{S_{j+1}}−H_j)` — which the
   completed-square identity (design-spec §4.3) turns into a `Σ(F_j − P/ℓ)²`-form at the breakpoint
   widths `m = M^{S_j}`.
3. **Lower bound (per-ℓ, NOT global min):** every `T` has its breakpoint widths `≥` the `ℓ_T+1`
   smallest widths; balanced-split-minimises-`Σq²` (step 1) + the smallest-widths choice ⇒
   `Mval(M,T) ≥ 2·cleanCore(ℓ_T, ℓ_T+1 smallest)` for `T`'s own `ℓ_T`. Hence `lambdaCore M` is `≥`
   the cleanCore at the achiever ℓ* (the ℓ whose balanced split is admissible and minimal).
4. **Upper bound (construct the achiever):** build `T* ∈ Adm(M)` from the balanced split on the
   `ℓ*+1` smallest widths; `Mval(M,T*) = 2·cleanCore(ℓ*, smallest)` ⇒ `lambdaCore M ≤` it.
5. Together: `lambdaCore M = cleanCore ℓ* (ℓ*+1 smallest)`, witnessing the `∃ ℓ` of (d).
6. **Def-3 ill-definedness SIDESTEPPED** (the known trap, lessons.md): Def-3 is used NOWHERE — not to
   define `lambdaCore` (it's the min), not to choose ℓ (the achiever exists by the min). Verified:
   Def-3 fails to select on ~80% of M (1082/1360, `/tmp/a1_def3.py`), but (d) is total regardless.

## Complementary scoped theorem (optional, genuine where it applies)

If a Def-3-keyed auxiliary is wanted (e.g. to connect to the printed Theorem-2 form): the SCOPED
`∀ M ℓ, Def3Selects M ℓ → lambdaCore M = cleanCore ℓ (ℓ+1 smallest)` is GENUINE (m pinned, ℓ bound by
the predicate) and verified (278/278 where Def-3 selects, unique, `/tmp/a1_def3.py`). It is partial
(covers the Def-3 regime only) — fine as an *auxiliary*, NOT as the total Lemma 3. The achiever ℓ of
(d) coincides with the Def-3 ℓ where Def-3 selects.

## Sequencing / status

OFF the headline critical path (the headline uses `aoyagiLambda` = `reg + lambdaCore` directly, with
`lambdaCore` the min-definition — it does NOT consume the clean form). So this strengthening is
sequenced after L1; the weak proof can stay as a flagged honest interim. The ~200-line balanced-split
exchange is the formaliser's lift; this card pins the genuine STATEMENT + route. **Use (d).** Verified
total (1360/1360), genuine (m pinned, Codex-confirmed), NOT an extremum (min/max refuted).
