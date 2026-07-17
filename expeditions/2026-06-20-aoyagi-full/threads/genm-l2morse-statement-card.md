# Statement card — `corankSVD_chartFamily_lt_top` (Lane 2 §H hole #1, the fixed-S Morse corank family)

**Claim.** For a fixed `b×q` matrix `S` of rank `r`, `min(a,b) ≥ 2`, and `2c' < a·r`, the integral over any
**bounded** box of `(‖Γ·S‖_F²)^{−c'}` is finite (a Morse / smooth-linear-center singularity).

- **Lean.** `DLNFibre.DLN.RLCT.corankSVD_chartFamily_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankMorse.lean`, on `origin/genm-l2morse` @`918a74ffb`;
  merged + wired into the engine on `genm-l2engine` @`176c27aea`).

      theorem corankSVD_chartFamily_lt_top {a b q : ℕ} (hab : 2 ≤ min a b)
          (S : Matrix (Fin b) (Fin q) ℝ) (c' : NNReal)
          (hthr : 2 * (c' : ℝ) < (a : ℝ) * (S.rank : ℝ))
          (box : Set (Fin a → Fin b → ℝ)) (hbox : Bornology.IsBounded box) :
          ∫⁻ Γ in box, ENNReal.ofReal ((frobSq (Matrix.of Γ * S)) ^ (-(c' : ℝ))) < ⊤

- **Gloss.** `frobSq(Γ·S)` is a PSD quadratic form in `Γ` of rank exactly `a·rank(S)`, zero-locus the linear
  subspace `{ΓS=0}`; below the tight threshold `c' < a·rank(S)/2` the `(−c')`-power is box-integrable.

- **Proved.** Finiteness, unconditional given the hypotheses. Route (l2svd cert §§1–4): spectral rewrite
  `frobSq(Γ·S)=∑λⱼ∑ᵢ((ΓQ)ᵢⱼ)²` → eigenframe CoV `Γ↦Γ·Q` (unit-Jacobian, over a Q-invariant Frobenius ball)
  → anisotropic floor to the `a·rank(S)` active columns (`weighted_rpow_le`) → active/free Tonelli split
  (`sumSqSubset_morseBox_lt_top`) + the banked radial engine (`sumSqND_box_lt_top`). `measurableEigendecomp`
  NOT needed (S fixed). 9 sorry-free theorems; the tight `a·rank(S)` count via `card_pos_eigenvalues_eq_rank`
  (`rank_eq_card_non_zero_eigs` + `rank_self_mul_transpose`).

- **Assumed.** `S` fixed; `2c' < a·rank(S)`; `box` bounded (`Bornology.IsBounded` — the l2svd §5 spec
  correction; the `volume box < ⊤` form is FALSE, counterexample reproduced). `min(a,b) ≥ 2` carried for
  byte-identical socket fit but UNUSED (the result is d-agnostic — Morse for any a,b, strictly more general).

- **Cited.** none (STAGE-2-free; no `cited_aoyagi_dln`). Consumes only banked measure-theory / linear-algebra
  bricks.

- **Deferred.** Does NOT close §H by itself. The outer per-stratum measure descent (`corankStratum_lt_top`)
  needs a QUANTITATIVE inner bound (`∫_Γ ≤ C(S)`, `C(S)` outer-integrable — a stronger, different lemma), and
  that outer integrability IS obligation 2 (`nonsubmersive_Ar_principalization`, the held wall). This fixed-S
  finiteness statement structurally cannot carry the quantitative bound (l2svd §7 scope caveat).

- **Status.** sorry-free; axiom footprint **clean-three** `[propext, Classical.choice, Quot.sound]` (forced
  `#print axioms` via deleted-olean re-elaboration). **TRIPLE-confirmed:** morserev (decorrelated own-worktree
  build + forced axioms + Codex xhigh, conclusion withheld) CONFIRMED CLEAN; morsefill (independent forced
  re-verify) CONFIRMED; l2morse (author, forced check). Clear to wire (l2engine merged).
