import DLNFibre.DLN.RLCT.Engine.EngineConstruction

/-!
# `DLNFibre.DLN.RLCT.Engine.ClearableReify` — the honest realized-stratum surface (reify-now)

The library's TYPED honest name for the stratum set the built tree's `t̃ = 0` read-off realizes
(elder-gate7 REIFY-NOW, compass 13(o5-IN)). The paper's implicit stratum-completeness "the `t̃ = 0`
profile-set is ALL of `Adm(M)`" is **FALSE** — a verified read-off defect (#4,
`theory/aoyagi-2023-reproduction/verify-realization-gap-defect.md`): at an interior-bottleneck width
vector (`∃ 3 ≤ S ≤ L, r_S < r_2`) an admissible profile whose level equals the dropped running-min
corank `r_S` is stranded above the shrunken chain and is NEVER pulled to `t̃ = 0` (chooser- and
branch-independent — `occ_above` tops out at `r_S − 1`, so a level-`r_S` divisor is invisible to
case-1 under any pick). Witness `M = (3,3,4,2,3)`: `(2,2,2,0)`, `(3,2,2,0) ∈ Adm` strand at `t̃ = 2`.

The TRUE characterization (pnp-o5 cert §1, two independent derivations — my exact recursion + a
decorrelated Codex leg — 0 counterexamples over 847 exact-recursion instances) is

    realizedProfiles M = { a ∈ Adm M : Clearable a }.

This module REIFIES that as a SEPARATE, sorried library-surface theorem — a TYPE, not a defeasible
docstring — so the honest realization boundary rides in the library. It is DELIBERATELY **NOT** a
conjunct of `IsFullMonomialization` (which would re-inflate the false `⊇ Adm` promise; the spine
proves only the SAFE `⊆ Adm` direction, `leaf_mem_Adm`). The load-bearing MINIMIZER fact
`minAdm ∈ terminalExponents` — the value the payoff needs — is `o5_realization` (cert §3,
envelope-splice: every non-clearable profile has a strictly cheaper admissible sibling, so every
`Mval`-minimizer is clearable, hence realized), SEPARATE and safe. This SET equality is the honest
FULL realization surface, whose PROOF is **R7** (the descent invariant, cert §4, for `⊇`; the strand
obstruction, cert §2, plus `leaf_mem_Adm`, for `⊆`). Reify-now lands the STATEMENT only — it must not
pull the descent-invariant proof onto the spine. AxCheck: `+sorryAx` until R7.
-/

namespace DLNFibre.DLN.RLCT.Engine

open DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The `Clearable` predicate** (pnp-o5 cert §1, the self-contained "running-min saturation
freezing" form; Codex-corroborated). A rank profile `a : Fin L → ℕ` (0-indexed: `a i = a^{i+1}` in
the paper's 1-indexing) is *clearable* iff every SATURATED strict descent has the complete running-min
envelope as its prefix: for adjacent coords `i, j` (`i + 1 = j`), IF `a` drops strictly at `j`
(`a j < a i`) FROM a coordinate saturating the running-min corank
(`a i = widthMinUpto M j.val = r_{j.val+1}`, the running min `min(M⁰ … M^{j.val})`), THEN every
earlier coord `m ≤ i` equals the envelope value `widthMinUpto M (m.val + 1) = r_{m.val+2}`. Equivalent
(cert §1) to the primary form "every POST-BIRTH strict descent (`b(a) < S`) starts strictly below the
running min (`a^{S-1} < r_S`)". A non-clearable profile is STRANDED at `t̃ > 0` (cert §2) — realizable
only above the shrunken chain, fenced by the paper's `t̃ = 0` read-off. -/
def Clearable (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) : Prop :=
  ∀ i j : Fin L, i.val + 1 = j.val → a j < a i → a i = widthMinUpto M j.val →
    ∀ m : Fin L, m.val ≤ i.val → a m = widthMinUpto M (m.val + 1)

/-- **`realizedProfiles M`** — the set of `t̃ = 0` leaf-divisor rank profiles the built tree realizes:
the ANALYTIC `divProfile`s of its leaves, which ARE the `t̃ = 0` divisors by construction
(`leafOfState` enumerates the `t̃ = 0` sublist via `t0Indices`; the `t̃ > 0` stranded divisors fold
into the residual). This is the cert's `P(M)`. -/
def realizedProfiles (M : Fin (L + 1) → ℕ) : Set (Fin L → ℕ) :=
  { a | ∃ l ∈ ResolutionTree.leaves (buildTree M (conOracle M) (conRoot : ConState L)),
      ∃ k : Fin l.numDiv, l.divProfile k = a }

/-- **The realized `t̃ = 0` stratum set equals the CLEARABLE admissible cone** (pnp-o5 cert §1;
elder-gate7 REIFY-NOW). NOT `= Adm` — the paper's implicit stratum-completeness is FALSE (read-off
defect #4): `realizedProfiles M ⊊ Adm M` exactly at interior-bottleneck widths, where a stranded
level-`r_S` divisor never reaches `t̃ = 0`. The safe minimizer fact `minAdm ∈ terminalExponents`
(the value the payoff needs) is `o5_realization`, SEPARATE and PROVED (cert §3); this SET equality is
the honest full realization surface. `0 < L` is REQUIRED (at `L = 0` the built tree is a single leaf
with no divisors, so `realizedProfiles = ∅`, while the clearable cone is `{()}` — the statement is
genuinely false at `L = 0`). **POSITIVE WIDTHS ALSO REQUIRED** (`hMpos : ∀ i, 0 < M i`; caveat next to
the claim, rev-s4 escalation): `Clearable` is width-free, but REALIZATION is not — at a zero width the
`⊇` direction fails. Witness `M = ![2,2,0]`: `tStar M = (2,0)` is `Clearable` but never realized (the
zero last-width forces immediate rollover, `realizedProfiles = {(0,0)}`), so `Clearable-Adm ⊄
realizedProfiles`. Same mechanism as `tStar_realized`/`o5_realization`'s `hMpos`. **Proof is R7**: `⊇`
via the descent invariant (cert §4), `⊆` via the strand obstruction (cert §2) + `leaf_mem_Adm`;
reify-now lands the STATEMENT only (a type is not defeasible; a docstring is). AxCheck: `+sorryAx`
until R7. -/
theorem realizedProfiles_eq_clearableAdm (M : Fin (L + 1) → ℕ) (_hL : 0 < L)
    (_hMpos : ∀ i, 0 < M i) :
    realizedProfiles M = { a | a ∈ Adm M ∧ Clearable M a } := by
  sorry

end DLNFibre.DLN.RLCT.Engine
