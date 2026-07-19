# Statement card — o5_core §3: every Mval-minimizer is Clearable

**Status:** sorry-free (awaiting reviewer fidelity check).
**Pinned commit:** `ca09d2d5b` (branch `expedition/aoyagi-engine--t01-r2`).
**File:** `lean/DLNFibre/DLN/RLCT/Engine/O5Realization.lean`.
**Axioms:** `clearable_of_minimizer`, `clearable_tStar` both `[propext, Classical.choice, Quot.sound]`
(forced `#print axioms`, clean-three, no `sorryAx`).

## Claim (cert-o5-realization.md §3)

Every `Mval`-minimizer of the admissible cone `Adm M` is `Clearable`. Concretely, the banked minimizer
`tStar M` is `Clearable M (tStar M)`. This is the envelope-splice: a non-clearable admissible profile
has a strictly cheaper admissible sibling (replace its pre-saturation prefix by the running-min
envelope, which contributes `0` to `Mval` while the differing prefix contributes `> 0`), so it cannot
be a minimizer.

## Lean signatures

```lean
theorem clearable_of_minimizer (M : Fin (L + 1) → ℕ) (a : Fin L → ℕ) (ha : a ∈ Adm M)
    (hmin : ∀ b ∈ Adm M, Mval M a ≤ Mval M b) : Clearable M a

theorem clearable_tStar (M : Fin (L + 1) → ℕ) : Clearable M (tStar M)
```

## English gloss

- `clearable_of_minimizer`: if `a` is admissible and `Mval M a ≤ Mval M b` for every admissible `b`
  (i.e. `a` attains the minimum of `Mval` over `Adm M`), then `a` satisfies `Clearable` (ClearableReify:
  every saturated strict descent has the complete running-min envelope as its prefix).
- `clearable_tStar`: the banked achiever `tStar M` (which attains `(Adm M).inf' Mval`, via
  `Mval_tStar_eq_inf'`) is `Clearable`. This is the load-bearing instance: §4 (pnp-o5) then realizes a
  clearable minimizer as a `t̃ = 0` leaf divisor, giving `minAdm ∈ terminalExponents` (o5_core).

## Hypotheses / scope

- `a ∈ Adm M` (admissible: weak-decrease, per-coord block bounds `admBound`, last coord `0`).
- `hmin`: `a` minimizes `Mval` over `Adm M` (for `clearable_of_minimizer`; discharged for `tStar` via
  `Mval_tStar_eq_inf'` + `Finset.inf'_le`).
- No `0 < L` needed (`L = 0` is vacuously clearable).
- MINIMIZER-ONLY (naming pin honored: `clearable_*`, never `*_complete` / `*_eq_Adm` — the full
  `⊇ Adm` is FALSE, R7 territory). Does NOT claim the realized set equals `Adm` or the clearable cone;
  claims only that a minimizer is clearable.

## Supporting lemmas (all sorry-free, same file)

`adm_le_widthMinUpto`, `mval_term_nonneg`, `prefix_forces_env` (cert step 2), `envVal`,
`envVal_le_admBound`, `spliceEnv`, `spliceEnv_le_envVal`, `spliceEnv_mem_Adm` (step 3a),
`spliceEnv_term_zero` (step 1: envelope summand = 0), `spliceEnv_term_eq` (step 3b: boundary/suffix
unchanged), `mval_spliceEnv_lt` (step 3c: strictly cheaper sibling).

## Fidelity check for the reviewer

1. `Clearable` (ClearableReify:48) matches cert §1's "running-min saturation freezing" — verify the
   Lean `Clearable` predicate is the intended one (not a weaker/stronger variant).
2. `Mval`/`Adm`/`tStar`/`admBound`/`widthMinUpto` are the banked defs (Lambda.lean / RouteMAchieverPath /
   EngineConstruction) — verify no redefinition.
3. The claim is MINIMIZER-ONLY (cert §3, the value the payoff needs), NOT stratum-completeness — verify
   the statement does not overclaim (`⊇ Adm` is false).
4. `clearable_tStar`'s `hmin` discharge (`Mval_tStar_eq_inf'` + `Finset.inf'_le`) genuinely gives
   `tStar` attains the min — verify.

## Composition note (surfaced, not part of §3)

o5_core (`EngineConstruction`, upstream) cannot consume `clearable_tStar` (`O5Realization`, downstream)
directly; discharging o5_core needs §4 (pnp-o5: clearable ⟹ realized) + a wiring/dependency-order
resolution (o5_core moves downstream, or a downstream theorem is wired into the assembly).
