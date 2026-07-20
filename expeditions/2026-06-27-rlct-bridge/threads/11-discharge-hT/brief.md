# Thread 11 — Phase 2 CAPSTONE: prove + discharge `hT`

**Type:** lean-formaliser (tide). **Base:** branch `expedition/rlct-bridge-discharge` from
`origin/expedition/rlct-bridge` (after the L7+L8 integration — the fibre-codim headline
`codimRepCanonical_fibre_eq_cCodim_add_shift` is now `[CharZero][Infinite]`, holds over ℝ, and the
base-change finrank machinery `DeformationBaseChange` is landed).

## The capstone (makes the whole expedition's headline land)

`hT` (`RlctPayoff.lean:410`) is the cited transfer `codimRepCanonical(fibre ℝ B) =
codimRepCanonical(fibre K (B.map ι))`, threaded as a hypothesis through the 7 payoff consumers. **PROVE it
and DISCHARGE it** — then the payoff `rlct = ½·C` rests on only the two analytic citations (Watanabe `≤`,
Aoyagi `≥`); the real↔complex transfer becomes a THEOREM.

The L7+L8 tide found the DIRECT route (no `T′`/varietyDim-transfer needed): with the relaxed fibre-codim
headline, **both sides equal the same field-independent `C+δ`**:
- LHS `codimRepCanonical(fibre ℝ B) = (cCodim d r).toNat + r·(d_N+d_0−r)` — the headline over ℝ
  (`[CharZero][Infinite]` ✓), `r = B.rank`.
- RHS `codimRepCanonical(fibre K (B.map ι)) = (cCodim d r').toNat + r'·(d_N+d_0−r')` — the headline over K
  (alg-closed char-0 ✓), `r' = (B.map ι).rank`.
- Equal once **`r' = r`**, i.e. the micro-gap **`(B.map ι).rank = B.rank`** (`Matrix.rank` preserved under
  the injective field hom `ι`) — `DeformationBaseChange`/`MatrixKaehler` territory; should be a short
  base-change lemma.

## Rungs

1. **`(B.map ι).rank = B.rank`** — rank base-change under `ι : ℝ →+* K` (ring hom, injective). Short.
2. **`hT` as a NAMED THEOREM** (e.g. `codimRealFibre_eq_codimRepCanonical_baseChange` /
   `transfer_codim_real_complex`): apply `codimRepCanonical_fibre_eq_cCodim_add_shift` on both sides +
   rung 1. Honest name (it's now PROVED, not assumed).
3. **DISCHARGE** across the consumers (`DLN/RlctPayoff` + `RlctPayoffGeneral` + `BundleShiftDischarge`):
   remove the `hT` hypothesis from the 7 payoff theorems — apply the rung-2 theorem instead. The payoff
   now rests on only `{cited_watanabe_upper, cited_aoyagi_lower}`. Update the `rlctRealInterfaceWitness`
   if it referenced `hT`. (The banked `codimRealFibre_eq_codimRepCanonical_of_dimTransfer` reduction lemma
   may now be redundant — leave or deprecate, your call; the direct route supersedes it.)
4. **L3 SWEEP (critical, name=content):** every docstring/comment that says `hT`/the transfer is **cited /
   to-be-proved / assumed / a named hypothesis** is now stale → **PROVED**. Sweep the semantic class across
   ALL of `lean/DLNFibre/` (RlctPayoff/RlctPayoffGeneral/BundleShiftDischarge + the aggregator
   `DLNFibre.lean` import comments + `codimRealFibre`'s docstring "T bridges to K") + the statement card +
   `synthesis.md`/`brief.md` framing. **Re-grep the class to EMPTY.** The cited boundary is now exactly
   `{Watanabe ≤, Aoyagi ≥}` — make every mention say so.

## Gates / discipline (MANDATE)

- **Full-aggregator green-gate** (`scripts/lb DLNFibre`, foreground — box may be loaded; `.lake` persists
  across kills). Sorry-free; **`#print axioms` on the headline payoffs MUST stay `[propext,
  Classical.choice, Quot.sound]`** (hT is now a proved theorem, NOT a hypothesis or axiom — confirm no new
  axiom crept in). name=content; in-file ℚ/ℝ witnesses where load-bearing.
- This is the CAPSTONE — after it lands the controller convenes a **decorrelated fidelity + hardener
  re-review** (the cited boundary shrank from 3 → 2; verify the discharge is genuine, hT's proof is sound,
  and no `rlct_…` now silently over/underclaims). Commit + push; controller integrates (single-writer
  aggregator) + re-green-gates. Stay **BLIND** to the aoyagi `RLCT/*`. IN-REPO memory only.

## NOT in this tide (roadmap)
The fibre-component/smoothness/θ-count-AT-fibre layer (~10 files `FibreComponentOrbit*`/`FibreThetaCount*`/
`FibreSmoothBlock*`/`TopDimMinPrimes*` still `[IsAlgClosed]` — the LR Lemma 4.6 bundle content) is NOT
needed for `hT` (the codim identity suffices); a separate "full-relaxation" tide if the operator wants it.
