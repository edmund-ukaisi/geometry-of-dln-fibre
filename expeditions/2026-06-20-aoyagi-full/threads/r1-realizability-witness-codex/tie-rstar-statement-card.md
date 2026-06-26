# Statement card — #121-(ii) the genuine realizability tie

> **Claim.** For an admissible exponent vector `T ∈ Adm M` (the §4 cone), the diagonal cascade's full
> 2-index rank pattern equals the orbit-stratum pattern `r*` of the achiever, where `r*` is defined from
> `(M, T)` ALONE (no `cascadeTuple`, no matrix): `rankFn M (cascadeTuple M T) = achieverRankPattern M T`.

- **Lean:** `DLNFibre.DLN.RLCT.rankFn_cascadeTuple_eq_achieverRankPattern`
  (`lean/DLNFibre/DLN/RLCT/Validate/CascadeAchiever.lean` @ `0211927`). The two defs `expSurvivor` /
  `achieverRankPattern` are hoisted to **`DLNFibre.Core.CascadeAchiever`** (network-free, `Fin`/`ℕ` only) so
  fm3's `RouteMBranchRead.realizes_ach` lock + the geometric-codim identification import the SAME decl; the
  H-lemmas and the tie theorem stay DLN-side (they need `Adm`/`admPred`/`adm_le_width`).
- **Gloss.** `rankFn M A i j` is the total `ℕ`-valued rank pattern of a tuple `A` (`(submult A i j).rank`
  on the `i ≤ j` triangle, `0` below). `achieverRankPattern M T i j` is the combinatorial `if`-formula
  `if i < j then expSurvivor M T j else if i = j then M i else 0`, with `expSurvivor M T` the running rank
  `ρ` (`ρ_0 = M_0`, `ρ_{k+1} = T_k`). The theorem: the rank pattern of the explicit partial-identity cascade
  `cascadeTuple M T` (matrices) coincides, cell by cell, with this formula in `(M, T)`. The two are defined
  on disjoint data pipelines (`Matrix.rank` vs an `if`-formula), so this is a genuine equality, NOT the
  `⟨cascadeTuple, rfl⟩` tautology (which `Core.cascadeTuple_rankFn_mem_range` flags as vacuous).
- **Proved.** The full function equality `rankFn M (cascadeTuple M T) = achieverRankPattern M T`, for any
  field `k`, by the obligation chain (CERT §2c/2d):
  - `expSurvivor_antitone` (H1) — `ρ` weakly decreasing, from clause (i)-at-0 and clause (ii).
  - `cascadeWindow_eq_expSurvivor` (H2) — the `i`-relative window-min of the cascade equals `ρ_j` for
    `i < j`, under H1.
  - `expSurvivor_le_width` (H3) — `ρ_i ≤ M_i` for every `i`, from clause (i); subsumes both endpoint width
    caps (`ρ_j ≤ M_i` via H1 antitone + this at `i`; `ρ_j ≤ M_j` via this at `j`).
  - Collapse: substitute H2 + H3 into `survivors (M_j)(M_i)(cascadeWindow i j) = min(ρ_j, min(M_j, M_i)) =
    ρ_j`. Off-triangle `0`; diagonal `M_i` (`rankPattern_self`).
- **Assumed.** `T ∈ Adm M` (stated at `Adm` for the downstream consumer). **The proof uses only clauses
  (i)+(ii)** of `admPred` (per-block bound + weak-decrease); clause (iii) (last-zero, `admPred.2.2`) is
  **unused** — confirmed in the proof (it destructures the third clause as `_`). The theorem holds on the
  strictly weaker hypothesis `(i)∧(ii)`; the docstring names the true scope.
- **Cited.** `Core.rankPattern_cascade` (#122, committed) for the cascade's interval-product rank
  `survivors (d_j)(d_i)(cascadeWindow i j)`; its side-condition `ht : ∀ p, T_p ≤ M_p` is discharged from
  admissibility by `adm_le_width` (gate-1, committed). Both are reproved upstream on the branch, not external.
- **Deferred.** none. (The downstream `T* ∈ RealizableRank` membership and the `r* = orbit-stratum` reading
  for the §4 achiever consume this equality; they are separate obligations, not this card.)
- **Status.** sorry-free + **reviewed** (independent fidelity review, 2026-06-23: all five gates PASS —
  independence, proven-not-assumed, (i)+(ii)-only scope re-verified by re-proving the tie from an
  (i)+(ii)-only hypothesis, non-vacuity on the 4-property witness, name=content; decorrelated Codex consult
  concurred). Axioms = clean-three `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no
  `monomial_rlct`, no `native_decide`).

## Non-vacuity (in-file, CERT §3)

`rankFn` is `noncomputable` (`Matrix.rank`), so the in-file checks split:

- `decide`: the property-breaker `M=(1,1,1,2,1), T=(1,1,1,0)` and the interior rank-2 variant
  `M=(3,3,3,2,2), T=(3,3,2,0)` are genuinely in `Adm M` — the theorem applies non-vacuously, on a witness
  with the increasing-width corner (`M_2 < M_3`) and a strict pre-final drop.
- `#guard` / `example` (`by decide`): the achiever's interior nonzero cell `(1,3)` is `1` on the first
  witness and `2` on the second — content at a genuine interior stratum, a substantive (non-`1×1`) matrix
  rank. The cert verified (sympy, exact ℚ) that `rankFn` agrees with these; this theorem is the Lean proof.

## Cap-check verdict (controller note)

`Core.rankPattern_cascade` is **SOUND as a general statement** (NOT admissible-only, NOT unsound): it carries
the hypothesis `ht : ∀ p, T_p ≤ M_p` (`= M p.castSucc`), which is exactly the per-fold middle-dimension bound
`partialId_mul` requires. Under `ht`, the committed endpoint-cap form `min(cascadeWindow i j, min(M_i, M_j))`
equals the true all-widths rank at **0 / 12 412 300** cells (decorrelated combinatorial re-derivation, then
cross-checked against sympy `.rank()` on 800 375 cells with no `ht` — the `true_rank` formula itself is
exact). The CERT §2b intermediate-width counterexample `M=(5,1,3,1), T=(3,3,3)` violates `ht` (`T_1=3 >
M_1=1`), so it is outside the lemma's scope and is not a counterexample to it. Name = content holds; safe to
consume at the admissible use-site.
