# `adm` soundness audit — verdict (reviewer, genm-admfix)

**Target.** `adm` (`RouteMSJAdm.lean:192`), the admissibility predicate the `DecoratedDescent`
spine (`RouteMSJDecoratedRec`) quantifies over.
**Function.** Claim-soundness (adversarial counterexample hunt against the `(□)` discharge foundation).
**Verdict.** **BROKEN.** `adm` is unsound: it admits divergent decorations, so `DecoratedStepHyp adm`
is **false as stated** and can carry no sorry-free proof.
**Minimal sound fix.** Candidate (a) — drop the corank disjunct: `adm := genuineCarrier D ∧ FaithfulSJAt D`.
**Ripple.** Bounded / mechanical (3 proof-term edits + 1 base-proof simplification); no *sound* banked
result re-opens; drivers + Mint are `adm`-abstract and untouched.

All arithmetic and the witness's admissibility were checked in Lean against the built
`expedition/aoyagi-full` library (read-only, `/tmp` scratch); decorrelated with a full Codex read.
Every headline number below is `native_decide`/`#eval`-confirmed and Codex-confirmed.

---

## 1. The bug (confirmed)

```
adm n M D := genuineCarrier D ∧ (admCorankA M = 0 ∨ admCorankB M = 0 ∨ FaithfulSJAt D)
```

The corank disjuncts are properties of the **chain `M`** (`admCorankA M = M 0 − bindingCut M`,
`admCorankB M = M 1 − bindingCut M`), not of the **decoration `D`**. `genuineCarrier D`
(`RouteMSJAdm.lean:60`) constrains only `D.ζ = Unit`, `D.ν`, the measure-equiv `e : D.Z ≃ᵐ Params M`,
`D.dom`, and `D.ctx`'s second component (= the layer product). It does **not** constrain `D.d`,
`D.jac`, or `D.carrier.supp`. So whenever `M` has a degenerate binding-cut corank, *every*
genuine-carrier decoration is admitted regardless of its exceptional-divisor / Jacobian structure —
in particular bypassing `FaithfulSJAt`'s β threshold (`RouteMSJAdm.lean:170`), the very gate that
bounds the monomial box integral.

Confirmed there is **no** `SJLinGenState` / `SJDecoration` invariant that rescues it: the structure
fields `d`, `jac`, `carrier.supp` are free, and `radialAttach` copies exactly the `genuineCarrier`-read
fields while raising `d` and prepending to `jac` — so `genuineCarrier (radialAttach D j) = genuineCarrier D`
definitionally (proved: `witness_genuine := genuineCarrier_trivial M521`, no `sorry`).

## 2. The decide-checkable witness — `M = (5,2,1)`

Arithmetic (Lean `native_decide`, matching the `Mval` fold `Mval(t,0)=(5−t)(2−t)+t → [10,5,2]`):

| quantity | value |
|---|---|
| `minAdm ![5,2,1]` | `2` |
| `bindingCut ![5,2,1]` (least `u` with the peel-fold equality; achieved only at `u=2`) | `2` |
| `admCorankA` `= 5 − 2` | `3` |
| `admCorankB` `= 2 − 2` | **`0`** ← fires |
| `carrierThreshold = minAdm/2` | `1` |

Witness decoration `D* := (SJDecoration.trivial ![5,2,1]).radialAttach 0`:
`d = 1`, `jac = ![0]` (both `rfl`), and `decLoss (u₀ ::: u) A = u₀² · frobSq (prod M A)`
(proved: `witness_decLoss`, axiom-clean). It is `adm`:

```
theorem witness_adm : adm 2 ![5,2,1] D* := ⟨witness_genuine, Or.inr (Or.inl (by native_decide))⟩
```

`#print axioms witness_adm = [propext, Classical.choice, Quot.sound, <native_decide numeric fact>]`
— no `sorryAx`. So the divergent decoration is a **genuine in-Lean adm witness**.

## 3. The divergence (⟹ `DecoratedStepHyp adm` false)

With `unitBox 1 = univ.pi (fun _ => Icc 0 1)` (confirmed, `Skeleton.lean:84`) and `jac ≡ 0`, Tonelli
factors the decorated integral (both factors nonnegative):

```
D*.integral c' = (∫₀¹ u₀^(−2c') du₀) · (∫_{paramsBoxM} frobSq(prod M A)^(−c') dA)
```

`∫₀¹ u₀^(−2c') du₀ = ⊤` for `2c' ≥ 1`, i.e. `c' ≥ ½`; and `∫ frobSq(prod M A)^(−c') dA > 0`
(`frobSq(prod M A)` is a nonzero polynomial in `A`, positive on a positive-measure set). Hence
`D*.integral c' = ⊤` for every `c' ∈ [½, 1)`. Since `carrierThreshold M = 1`, such `c'` satisfy
`c' < carrierThreshold M`, so

```
¬ DecoratedBoxThresholdFinite D*.
```

The driver `decoratedBoxThresholdFinite_of_decoratedStep` (`RouteMSJDecoratedRec:161`) at `n = 2 = k+2`
(`k=0`) calls `hstep 0 M (IH) D* witness_adm`, whose conclusion is `DecoratedBoxThresholdFinite D*`.
That conclusion is false, so **`DecoratedStepHyp adm` is false as stated** — no sorry-free proof of it
can exist in consistent Lean. (The parameterised driver theorem itself stays logically sound; the
un-fillable object is the hypothesis `hstep`.)

**Why the base #4 masks it, the step un-masks it.** At width-2 (`DecoratedBaseHyp`) `bindingCut = 0`
(`bindingCut_two`), so `admCorankA = M 0`, `admCorankB = M 1`; a corank being `0` forces `M i = 0`,
hence `minAdm = M₀·M₁ = 0` (`minAdm_eq_zero_of_corankZero`), hence `carrierThreshold = 0` — vacuously
finite (`decoratedBase_corankZero`). At the interior the binding cut is positive (`bindingCut = 2` here),
which **decouples** corank-`0` from `minAdm = 0` (`minAdm = 2 > 0`, threshold `= 1 > 0`), so the corank
disjunct becomes non-vacuous and admits the divergent `D*`. (Precise correction to the dispatch framing:
corank-`0` ⟹ `minAdm = 0` holds only at width-2, where `bindingCut = 0` — not in general.)

## 4. `FaithfulSJAt` correctly rejects `D*` (the fix's crux)

`D*` has `d = 1` (so the `d = 0` observable disjunct fails), uniform support `≡ 1`
(`sharedDivisorExp = 1`), `jac = 0`. Then `monomialThreshold 1 ![1] ![0] = ½`, and β requires
`½·minAdm M = 1 ≤ ½` — **false**. So `¬ FaithfulSJAt D*`: the β threshold is exactly the guard the
corank disjunct bypasses. This is what makes candidate (a) remove the counterexample.

## 5. The minimal sound fix (candidate (a)) — exact Lean

```lean
def adm (n : ℕ) (M : Fin (n + 1) → ℕ) (D : SJDecoration M) : Prop :=
  genuineCarrier D ∧ FaithfulSJAt D
```

Rationale for dropping (not strengthening) the corank disjunct: **it is never *produced* as a tool.**
Every downstream proof of `adm` goes through the `FaithfulSJAt` disjunct — `adm_trivial`
(`Or.inr (Or.inr (Or.inl …))` = FaithfulSJAt d=0) and `cornerComparator_adm`
(`Or.inr (Or.inr faithful)`); nothing proves `adm` via `admCorankA/B = 0`. The disjunct only *widens*
the predicate (the bug) and is *consumed* only at the vacuous width-2 base. Dropping it makes
`DecoratedStepHyp adm` a **sound (provable) target** rather than a false one, and — at a corank-`0`
parent chain — the step now must prove finiteness only for `FaithfulSJAt` decorations (the intended
analytic goal), instead of for all genuine decorations (impossible).

Verified in Lean (`admFix := genuineCarrier ∧ FaithfulSJAt`, axiom-clean `[propext, Classical.choice, Quot.sound]`):
* `admFix_trivial` — `trivial` admissible via the `d = 0` observable disjunct (`Or.inl`).
* `admFix_cornerComparator` — the reduced comparator admissible via `cornerComparator_faithful` (same
  `hd`, `i₀`, `hbeta` hypotheses; only the disjunction-constructor boilerplate changes).

Codex's alternative (more conservative) repair, if the team prefers to keep the degenerate corank
branch literally:
`genuineCarrier D ∧ (FaithfulSJAt D ∨ ((admCorankA M = 0 ∨ admCorankB M = 0) ∧ minAdm M = 0))`.
The added `minAdm M = 0` guard makes the extra branch genuinely vacuous (threshold `0`). It is sound
but strictly redundant — a `minAdm = 0` chain is vacuously finite for *any* `D`, and no arising
decoration needs corank-admission (§6). Candidate (a) is cleaner and *simplifies* the base rather than
preserving dead cases; recommend (a).

## 6. Ripple (what re-opens, re-proof size)

| consumer | effect of fix (a) | size |
|---|---|---|
| `adm` def (`RouteMSJAdm.lean:192`) | drop corank disjunct | 1 line |
| `adm_trivial` (`:209`) | `Or.inr (Or.inr (Or.inl …))` → `Or.inl …` | 1 token |
| `cornerComparator_adm` (`RouteMSJCornerComparator.lean:205`) | `Or.inr (Or.inr faithful)` → `faithful` | 1 token |
| `decoratedBaseHyp_faithful` (`RouteMSJBaseHyp.lean:395`) | drop the two `decoratedBase_corankZero` `rcases` arms; keep the `FaithfulSJAt` (ii)/(iii) dispatch verbatim | ~4 lines |
| `decoratedBase_corankZero`, `minAdm_eq_zero_of_corankZero`, `bindingCut_two` (`RouteMSJBaseHyp.lean:47–74`) | become unused (keep as dead code or delete) | 0 (or delete) |
| `deeperFlag_shell_le` (`RouteMSJDeeperFlagCore.lean:770`) | **transparent** — consumes `cornerComparator_adm`'s result type `adm (…) (comparator)`, whose meaning changes but whose provision (via `cornerComparator_adm`) is unchanged | 0 |
| `DecoratedStepHyp` / `DecoratedBaseHyp` / `DecoratedDescent` / drivers (`RouteMSJDecoratedRec`) | `adm`-abstract — definition-independent | 0 |
| `RouteMSJMint` (`:42`, consumes `∃`-packaged `DecoratedDescent`) | `adm`-abstract | 0 |

**No sound banked result re-opens.** `decoratedBaseHyp_faithful` (currently green, sorry-free) re-proves
mechanically: its `FaithfulSJAt` arms (`decoratedBase_d0_of_lossEq`, `decoratedBase_routeA_of_leafForm`)
are unchanged; only the outer 3-way `rcases` collapses to the 2-way `FaithfulSJAt` split. The base's
non-vacuity witness `witnessDecoration222` (d≥1) is unaffected. `DecoratedStepHyp adm` was never proved
(it is the open analytic target — the `deeperFlag` bricks F, D remain `sorry` at
`RouteMSJDeeperFlagCore.lean:501,544`); the fix turns it from *false-as-stated* into a *sound target*.

**Assessment: BOUNDED (mechanical).** No substantial re-proof. The fix removes a hole; it does not move
any staked boundary.

## 7. Scope of the certification

Confirmed in-scope: the corank disjunct admits the concrete divergent `D*`, `DecoratedStepHyp adm` is
false, candidate (a) excludes `D*` (β rejects it) and preserves the trivial + comparator legs with only
boilerplate edits. **Out of scope** (unchanged by this audit): the *positive* soundness of `FaithfulSJAt`
itself — i.e. whether `∀ (genuineCarrier ∧ FaithfulSJAt) D, DecoratedBoxThresholdFinite D` holds — which
depends on the α/δ/γ' clauses and the still-`sorry`'d `deeperFlag` analytic bricks. From the definitions
one can certify that (a) removes *this* counterexample, not that it proves the whole `(□)` positive
theorem. Codex concurs.

---

### Reproduction

Read-only against the built `expedition/aoyagi-full` library:

    cd <repo>/lean && lake env lean /tmp/adm_witness_final.lean   # witness_adm, witness_decLoss (axiom-clean)
    cd <repo>/lean && lake env lean /tmp/adm_fix_check.lean       # admFix_trivial, admFix_cornerComparator (axiom-clean)

Key `native_decide` facts: `minAdm ![5,2,1] = 2`, `bindingCut = 2`, `admCorankA = 3`, `admCorankB = 0`.
