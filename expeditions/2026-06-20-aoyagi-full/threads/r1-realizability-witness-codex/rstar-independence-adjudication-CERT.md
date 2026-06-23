# #121 — the genuine realizability tie: independence adjudication CERT

Pen-and-paper adjudication (witness + obstruction) of the proposed genuine equality

> `rankFn (cascadeTuple M T) = achieverRankPattern M T`,  given `T ∈ Adm M`.

All algebra below is **exact** (sympy `.rank()` over ℚ; no float ranks). Scripts live next to this
file; the decorrelated codex prompt + answer are under `codex/`.

## One-line verdicts

- **(1) INDEPENDENCE — ACCEPT.** `achieverRankPattern M T` is built from `M, T` alone (via `expSurvivor`),
  with no `cascadeTuple`/matrix input. The equality is a genuine equality of two independently-defined
  ℕ-valued functions, not `⟨cascadeTuple, rfl⟩`.
- **(2) THE SUBTLETY — ACCEPT, with a sharpened proof-route and a corrected cap.** `achieverRankPattern`
  IS the genuine cascade rank pattern *on admissible `T`*: exact rank `= achieverRankPattern = committed
  survivors formula` on all 10820 admissible cases (L=2..4, widths 1..4). The coincidence rides on
  `admPred ⟹ ρ weakly-decreasing` plus two width-caps; the load-bearing clauses are exactly **(i)+(ii)**
  — clause (iii) is NOT needed. One correction to the codex's stated rank formula is folded in below.
- **(3) PROPERTY-BREAKER — ACCEPT.** An admissible witness with all four required properties exists
  (`M=(1,1,1,2,1), T=(1,1,1,0)`; a rank-2 interior variant `M=(3,3,3,2,2), T=(3,3,2,0)`), computed both
  ways with matrices/ranks shown; a non-monotone per-block perturbation breaks the equality — so the
  agreement is content, not identity.

No kill-condition for the (i)+(ii)-scoped statement. One scope correction (drop clause (iii) from the
needed hypotheses; the committed endpoint-only cap is correct only because admissibility also kills the
intermediate-width pinch) — detailed below.

---

## Committed ground truth (origin/fm3/routem — decl-grounded)

- `partialId k r c t : Matrix (Fin r)(Fin c)` — entry `(a,b)=1` iff `a=b (as ℕ) ∧ a<t`, else 0.
  (`Core/CascadeRank.lean:27`)
- `survivors r c t := min t (min r c)`; `rank_partialId : (partialId k r c t).rank = survivors r c t`.
  (`CascadeRank.lean:31`, proved.)
- `cascadeTuple d t s := partialId k (d s.succ) (d s.castSucc) (t s)` — block `A_s : (d_{s+1})×(d_s)`.
  (`Core/CascadeRealizable.lean:28`)
- `submult d A i j (i≤j) = A_{j-1} ⋯ A_i : Matrix (Fin d_j)(Fin d_i)` — **LEFT-multiplied** product;
  empty (`i=j`) is `1`. (`Core/Submult.lean:51`)
- `rankPattern d A i j := (submult d A i j).rank`; `rankFn d A i j := if i≤j then rankPattern else 0`
  (total, 0 off the `i≤j` triangle). (`Submult.lean:95`, `OrbitKostant.lean:64`)
- **Cascade rank (proved in Core, `rankPattern_cascade`, `CascadeRealizable.lean`):**
  `rankPattern (cascadeTuple) i j = survivors (d_j)(d_i)(cascadeWindow i j)
     = min( cascadeWindow i j , min(d_j, d_i) )`,
  where `cascadeWindow i j = (⨅_{i≤p<j} t_p)` capped at the base width `d_i` (`= d_i` at `j=i`).
- **Admissibility (`admPred`, `DLN/RLCT/Foundations/Lambda.lean:51`):** with
  `admBound 0 = min(M_0,M_1)`, `admBound s = M_{s+1}` for `s≥1`,
  - (i) `∀ j, T_j ≤ admBound j`;
  - (ii) `∀ i≤j, T_j ≤ T_i` (weak decrease);
  - (iii) `∀ j, j = L-1 → T_j = 0`.

  `Adm M := piFinset(range(admBound+1)).filter admPred`.

The proposed independent target (banked codex `rstar-genuine-equality-answer.md`), as a Lean def:

```
expSurvivor M T : Fin (L+1) → ℕ          -- ρ, the running ranks
  ⟨0,_⟩   := M 0
  ⟨n+1,_⟩ := T ⟨n,_⟩                      -- ρ_0 = M_0 ,  ρ_{j} = T_{j-1}

achieverRankPattern M T i j :=
  if i < j then expSurvivor M T j          -- COLUMN-CONSTANT in i: value ρ_j, NOT capped
  else if i = j then M i
  else 0
```

---

## (1) Independence — ACCEPT

`achieverRankPattern M T` references only `expSurvivor M T` and `M`, both functions of `(M,T)`; it never
takes a tuple or a matrix. So `rankFn (cascadeTuple M T) = achieverRankPattern M T` is an equality
between two functions defined on disjoint data pipelines: the LHS is `(submult …).rank` of explicit
matrices; the RHS is a combinatorial `if`-formula in `M,T`. No hidden cascade dependence. This is the
opposite of the `cascadeTuple_rankFn_mem_range = ⟨cascadeTuple, rfl⟩` tautology that the Core docstring
(`CascadeRealizable.lean:90`) explicitly flags as vacuous.

**Verdict: ACCEPT.** Genuine equality of independently-defined objects.

---

## (2) The subtlety — ACCEPT (with the monotonicity chain + a corrected cap)

### 2a. `admPred ⟹ ρ weakly-decreasing` (decl-grounded against the committed `admPred`)

ρ (= `expSurvivor`) is `ρ_0 = M_0`, `ρ_{j+1} = T_j`. Weak-decrease `ρ_0 ≥ ρ_1 ≥ … ≥ ρ_L` means:

- `ρ_0 ≥ ρ_1`: `M_0 ≥ T_0`. From (i) at `j=0`: `T_0 ≤ admBound 0 = min(M_0,M_1) ≤ M_0`. ✓
  (this is the codex's `T_0 ≤ min(M_0,M_1) ≤ M_0` chain — verified against the committed `admBound 0`.)
- `ρ_{j} ≥ ρ_{j+1}` for `j≥1`: `T_{j-1} ≥ T_j`. This is (ii) at `(i,j)=(j-1,j)`. ✓

So **(i)-at-0 + (ii) ⟹ ρ weakly decreasing.** Clause (iii) is unused here. Exhaustively confirmed: 0
running-rank-increase violations over all admissible `T` (L=2..4, widths 1..5) — `pp_which_clause.py`,
and the dedicated `monotone_check.py`.

### 2b. The rank formula and the intermediate-width correction

The cascade interval product `submult i j = A_{j-1}⋯A_i` is itself a partial-identity. Its EXACT rank
(re-derived independently, sympy over ℚ) is

> **`rank(submult i j) = min( ⨅_{i≤p<j} T_p , ⨅_{i≤r≤j} M_r )`** — the window-min of the truncations
> `T_p`, capped by the minimum over **all** widths `M_i,…,M_j` (not only the endpoints).

The endpoint-only cap `min(⨅T_p, min(M_i,M_j))` is **WRONG in general**: an intermediate width `M_s`
(`i<s<j`) smaller than the window-min pinches the rank. Re-derivation found 158/3360 random mismatches;
the smallest is

    M=(5,1,3,1), T=(3,3,3), cell (0,2):  endpoint-cap = min(3,min(5,3)) = 3   but   true rank = 1.
    submult(0,2) = [[1,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0]]   (the intermediate M_1=1 binds.)

My decorrelated codex caught the **same** pinch independently (`codex/codex_answer.md`, Q2):
`M=(2,1,2),T=(2,2)`, cell (0,2): endpoint-cap 2, true rank 1, "misses the intermediate width `M_1=1`".

The **committed Lean** `survivors(d_j)(d_i)(cascadeWindow i j)` is the endpoint form (caps at `d_i` then
`min(d_i,d_j)`). It is therefore correct **only when no intermediate width binds**. CONFIRMED EXACT: on
all **101200** admissible 2-index cells (L=2..4, widths 1..4) the committed endpoint form equals the
corrected all-widths form — **0 mismatches**. Reason: admissibility forces `ρ` weakly decreasing and
`ρ_j ≤ M_r` for all `i≤r≤j` (sub-fact below), so the window-min of `T` is already `≤` every intermediate
width; the intermediate cap never bites. So the committed cascade lemma `rankPattern_cascade` is sound on
its admissible use-site — no kill-condition — but the "endpoint cap suffices" fact is itself an
admissibility consequence, worth a one-line note at the use-site.

### 2c. `ρ weakly-decreasing (+ width caps) ⟹ window-min over (i,j] = ρ_j = achieverRankPattern`

Decompose `achieverRankPattern i j = ρ_j = T_{j-1}` (`i<j`) vs the true rank. Need three sub-facts, all
verified with **0 violations** under (i)+(ii) (`pp_which_clause.py`):

- **F1 (window-min = ρ_j):** for weakly-decreasing `T`, `⨅_{i≤p<j} T_p = T_{j-1} = ρ_j` (the min of a
  decreasing list is its last entry; index `j-1` is the largest `p<j`). Pure consequence of (ii).
- **F2a (left width cap):** `ρ_j ≤ M_i` for `i<j`. The tight cell is `i=j-1` with `j-1≥1`, where
  (i) gives only `T_{j-1} ≤ admBound(j-1)=M_j` — **not** `≤ M_{j-1}`. The bound comes from the monotone
  chain `T_{j-1} ≤ T_{j-2} ≤ admBound(j-2)=M_{j-1}`, i.e. **(i)+(ii) combine**. Per-block ALONE fails F2a
  165446 times in the sweep; under (i)+(ii): 0.
- **F2b (right width cap):** `ρ_j ≤ M_j` for `i<j`. From (i) at `j-1` (`T_{j-1} ≤ admBound(j-1)`, which
  is `≤ M_j` for `j-1≥1`, and `= min(M_0,M_1) ≤ M_1 = M_j` at `j-1=0`). 0 violations.

Then for `i<j`: `rank = min(⨅T_p, ⨅_{i≤r≤j} M_r) = min(ρ_j, …) = ρ_j` (F1 collapses the T-window to
`ρ_j`; F2a+F2b+2b push every width `≥ ρ_j`). Hence `rank = ρ_j = achieverRankPattern i j`. The diagonal
`i=j` is `M_i = d_i` (`rankPattern_self`); off-triangle both are 0.

### 2d. Which clauses bite (the minimal scope)

Exhaustive clause isolation (`pp_which_clause.py`, all `T`, L=2..4, widths 1..4):

| hypotheses                | codex≠core count |
|---------------------------|------------------|
| none                      | 556456           |
| (i) per-block only        | 119928           |
| (ii) monotone only        | 54938            |
| **(i)+(ii)**              | **0**            |
| (ii)+(iii)                | 24701            |
| (i)+(ii)+(iii) = admPred  | 0                |

**The load-bearing hypotheses are exactly (i)+(ii). Clause (iii) (last-zero) is NOT needed** for the
equality. My decorrelated codex independently reached the same minimal subset and gave its own
counterexamples for "(i) alone" (`M=(5,5,5),T=(1,3)`) and "(ii) alone" (`M=(1,5,5),T=(3,0)`).

> **Note for the formaliser:** the genuine-equality theorem can be stated with hypothesis `(i)∧(ii)`
> (strictly weaker than `T ∈ Adm M`). Stating it at `T ∈ Adm M` is fine and convenient (it is what
> downstream consumes), but the docstring should say the proof uses only (i)+(ii) — naming the theorem by
> its true scope (CLAUDE.md precision discipline). Do NOT cite (iii) in the proof.

**Verdict: ACCEPT.** `achieverRankPattern` is the genuine cascade orbit rank-pattern on admissible `T`
(it is NOT merely a "column-constant completion" that coincides by luck — the coincidence is forced, and
exactly by the weak-decrease + width-cap chain). One correction folded in: the endpoint cap is sound only
because admissibility also kills the intermediate-width pinch.

---

## (3) Property-breaker witness — ACCEPT

### Primary witness (all four required properties), `pp_strong_witness.py`

    M = (1,1,1,2,1)      T = (1,1,1,0)        admissible: YES
    running ranks ρ = (1,1,1,1,0)             weakly decreasing: YES

- (P1) L = 4 ≥ 3. ✓
- (P2) interior nonzero cell `(i,j)=(1,3)`, `0<1<3<5`, `achieverRankPattern 1 3 = ρ_3 = T_2 = 1 > 0`. ✓
- (P3) strict positive drop before the forced final zero: `T_2=1 > T_3=0`. ✓
- (P4) increasing width step `M_2=1 < M_3=2`. ✓

**Both sides, exact.** Full cascade rank pattern (sympy `.rank()` over ℚ):

    i\j  0 1 2 3 4
     0 : 1 1 1 1 0
     1 : 0 1 1 1 0
     2 : 0 0 1 1 0
     3 : 0 0 0 2 0
     4 : 0 0 0 0 1

`exact rankFn == achieverRankPattern == committed survivors`: **TRUE** at every cell. The load-bearing
interior cell `(1,3)`: actual `submult = A_2·A_1 = [[1],[0]]` (shape 2×1), exact rank 1 = `ρ_3 = T_2`.
The LOCAL block bound `admBound(2)=M_3=2 > M_1=1`, so `T_2 ≤ admBound(2)` does **not** bound `ρ_3` below
`M_1`; the monotone descent `T_2≤T_1≤T_0≤min(M_0,M_1)=1` delivers `ρ_3 ≤ M_1`. **The source-size
feasibility rides on monotonicity, as required.**

### Rank-≥2 interior variant (a substantive matrix, not 1×1)

    M = (3,3,3,2,2)      T = (3,3,2,0)        admissible: YES
    interior cell (1,3): window T[1:3]=(3,2) — STRICT drop inside the window; window-min = T_2 = 2 = ρ_3
    submult = A_2·A_1 = [[1,0,0],[0,1,0]]   (shape 2×3),  EXACT rank 2  =  achieverRankPattern 1 3 = ρ_3 = 2.

### The agreement RIDES monotonicity (non-identity)

Non-monotone, still per-block-feasible perturbation of the primary witness:

    T' = (0,0,0,1)   running ranks (1,0,0,0,1) — INCREASES at the last step (non-admissible)
    exact rankFn(cascade T') ≠ achieverRankPattern(T') at cells (0,4),(1,4),(2,4):
        exact = 0   but   achieverRankPattern = ρ'_4 = T'_3 = 1.

`achieverRankPattern` **overshoots** the true rank once monotonicity is dropped (the column-constant
value reads only the right-endpoint `T_3`, ignoring that the earlier zeros killed the rank). So the
equality is genuine content carried by admissibility, not a definitional identity. (Codex Q4 reached the
identical conclusion with `M=(5,5,5),T=(1,3)`.)

**Verdict: ACCEPT.** A principled admissible witness with all four properties exists and agrees on both
sides; the agreement provably rides the weak-decrease.

---

## Decorrelated codex — independent take (`codex/`)

Prompt withheld my conclusions (frame in, facts in, hypothesis out). Codex independently:

- **Caught the intermediate-width pinch** (the endpoint-only cap is wrong; `M=(2,1,2),T=(2,2)`) — a bug
  the BANKED codex answer (`rstar-genuine-equality-answer.md`) did NOT surface. Agrees with my 2b.
- Stated the exact coincidence condition: rank `= t_j` iff `T_{j-1} ≤ T_p (i≤p<j)` and `T_{j-1} ≤ M_r`
  for **all** `i≤r≤j`. Matches my F1/F2 decomposition.
- **Minimal subset = (i)+(ii); (iii) irrelevant** — identical to my clause-isolation, with its own
  decorrelated counterexamples for each dropped clause.
- `P` is content not identity; non-admissible `T` overshoots. Matches (3).

Where it differs from the BANKED answer: the banked answer asserted the endpoint survivors formula and
the achieverRankPattern coincide for admissible `T` (true) but did not flag that the endpoint cap is
itself an admissibility artifact (intermediate widths). Both my re-derivation and my fresh codex flag it.
No disagreement on the load-bearing conclusion.

---

## CLEAN final statement for the formaliser

**Theorem (genuine realizability tie, true scope (i)+(ii); stated at `Adm` for the consumer).**

```
theorem rankFn_cascadeTuple_eq_achieverRankPattern
    {k : Type u} [Field k] {L : ℕ}
    (M : Fin (L + 1) → ℕ) (T : Fin L → ℕ) (hT : T ∈ Adm M) :
    rankFn (k := k) M (cascadeTuple (k := k) M T) = achieverRankPattern M T
```

with `achieverRankPattern`/`expSurvivor` as defined above. Conclusion is a plain `funext` equality of
`Fin (L+1) → Fin (L+1) → ℕ`.

### Lean-grade obligation list (proof route — uses only clauses (i)+(ii) of `hT`)

Let `ρ = expSurvivor M T` (so `ρ_0 = M_0`, `ρ_{j+1} = T_j`). Off the triangle (`i>j`) and on the diagonal
(`i=j`, value `M_i` via `rankPattern_self`) are immediate. For `i<j`:

0. **Reuse the proved cascade rank** `rankPattern_cascade` (already in Core): it needs the side condition
   `ht : ∀ p, T_p ≤ M (p.castSucc)` (the cascade middle-dimension bound). DISCHARGE `ht` from `hT`:
   `T_p ≤ admBound p` and (the monotone chain) `≤ M_p`. [obligation H0]
   This gives `rankFn (cascade) i j = survivors (M_j)(M_i)(cascadeWindow i j)
       = min( min(⨅_{i≤p<j} T_p, M_i) , min(M_i, M_j) )`.
1. **H1 (ρ weakly decreasing):** from `hT.1` at 0 (`T_0 ≤ min(M_0,M_1) ≤ M_0`) and `hT.2.1`
   (`T_{j-1} ≥ T_j`). ⟹ `ρ_0 ≥ … ≥ ρ_L`. [clause (i)-at-0 + (ii)]
2. **H2 (F1, window-min = ρ_j):** `⨅_{i≤p<j} T_p = T_{j-1} = ρ_j`. From H1: min of a weakly-decreasing
   finite family over `[i,j)` is the last entry `p=j-1`. [clause (ii)]
3. **H3a (F2a, `ρ_j ≤ M_i`):** monotone chain `ρ_j = T_{j-1} ≤ T_{i-1 or 0} ≤ admBound(<region>) ≤ M_i`.
   Spell the worst case `i=j-1≥1`: `T_{j-1} ≤ T_{j-2} ≤ admBound(j-2) = M_{j-1} = M_i`. [clauses (i)+(ii)]
4. **H3b (F2b, `ρ_j ≤ M_j`):** `T_{j-1} ≤ admBound(j-1) ≤ M_j` (`= M_j` for `j-1≥1`;
   `= min(M_0,M_1) ≤ M_1 = M_j` for `j=1`). [clause (i)]
5. **Collapse:** substitute H2 into step 0; `survivors = min(min(ρ_j, M_i), min(M_i,M_j)) = ρ_j` by
   H3a+H3b (all caps `≥ ρ_j`). Equals `achieverRankPattern i j = ρ_j`. ∎

Notes for the formaliser:
- Do **not** use `hT.2.2` (clause (iii), last-zero) in the proof; the theorem holds without it. Name the
  scope accordingly (precision discipline).
- The `survivors` endpoint cap is what `rankPattern_cascade` proves; the intermediate-width pinch is
  invisible here precisely because H2+H3 force the window-min below every width — no extra obligation, but
  worth a one-line docstring so a future reader does not mistake the endpoint cap for the general rank.
- A non-vacuity `#eval`/`example` at `M=(3,3,3,2,2), T=(3,3,2,0)` (interior cell (1,3) rank 2) is a good
  regression guard; the `(1,1,1,2,1)/(1,1,1,0)` witness guards the increasing-width corner.

## Scripts (this dir) — all exact, re-runnable

- `pp_exact_rstar.py` — exact rank vs codex-column-constant vs committed-survivors; CHECK A/B/C.
- `pp_which_clause.py` — clause-isolation table + F1/F2a/F2b sub-fact sweep.
- `pp_property_breaker.py` — primary 4-property witness + non-monotone break.
- `pp_strong_witness.py` — interior monotone-feasibility witness (+ rank-2 variant inline above).
- `codex/codex_prompt.md`, `codex/codex_answer.md` — decorrelated consult.
