# Decorrelated fidelity red-team: the `IsFullMonomialization` Lean predicate

You are an independent reviewer. Do NOT trust my framing; reason from the definitions.
Read-only; no code to build. Give an inference-vs-fact split at the end.

## Background (a resolution-tree monomialization, Aoyagi 2023 pp.14–22)

A resolution tree's leaf carries TWO ledgers of "exceptional divisors":

- a FULL ledger of `fullNumDiv` divisors, each with an exponent `fullDivExp j : ℕ` and a
  rank-pattern vector `fullDivProfile j : Fin L → ℕ`. Its clearing level is `tildeOf(profile) = min
  over the vector's coordinates`.
- an ANALYTIC ledger of `numDiv` divisors (exponent `divExp k`, profile `divProfile k`), which is
  meant to be EXACTLY the sublist of FULL divisors whose clearing level `tildeOf = 0`.

Two established facts from pen-and-paper certificates (exact integer batteries, 847 instances, +
decorrelated proofs), which the Lean must respect:

1. **t̃=0 restriction (defect #4).** A leaf CARRIES `t̃ > 0` "stranded" divisors whose exponents
   can be BELOW the minimum. The paper's read-off (p.22) restricts to `t̃ = 0` divisors. So any
   predicate quantifying over ALL full leaf divisors (an unrestricted `∀ k` with `∈ Adm` or
   `divExp = Mval`) is STRICTLY STRONGER THAN the paper and FALSE.

2. **No ⊇ Adm.** `Adm(M)` is a finite "admissible cone" of profiles. The set `P(M)` of realized
   `t̃=0` leaf profiles is a PROPER SUBSET of `Adm(M)` at "interior-bottleneck" widths (e.g.
   `M=(3,3,4,2,3)` realizes 17 of 19 admissible profiles). So NO statement may assert
   `Adm ⊆ P` / `P == Adm` / "the leaf profiles enumerate Adm". The SAFE, true direction is
   `P ⊆ Adm` (every realized `t̃=0` profile is admissible).

`Mval M (T : Fin L → ℕ) : ℤ` is a fixed closed-form integer functional of the profile. `Adm M :
Finset (Fin L → ℕ)` is a fixed finite set. `.toNat` is ℤ→ℕ truncation.

## The Lean predicate under audit

```lean
def IsFullMonomialization {M : Fin (L + 1) → ℕ} (t : ResolutionTree M) : Prop :=
  ∀ l ∈ ResolutionTree.leaves t,
    -- (C1) analytic side: exponent = Mval of profile, and profile is admissible
    (∀ k : Fin l.numDiv, l.divExp k = (Mval M (l.divProfile k)).toNat ∧ l.divProfile k ∈ Adm M) ∧
    -- (C2) each analytic divisor matches a t̃=0 full divisor
    (∀ k : Fin l.numDiv, ∃ j : Fin l.fullNumDiv,
        l.divExp k = l.fullDivExp j ∧ l.divProfile k = l.fullDivProfile j ∧
          tildeOf (l.fullDivProfile j) = 0) ∧
    -- (C3) every t̃=0 full divisor is matched by an analytic divisor
    (∀ j : Fin l.fullNumDiv, tildeOf (l.fullDivProfile j) = 0 →
        ∃ k : Fin l.numDiv, l.divExp k = l.fullDivExp j ∧ l.divProfile k = l.fullDivProfile j)
```

## Questions (answer each sharply, with a concrete case where possible)

Q1. Does C1's `∀ k : Fin l.numDiv, l.divProfile k ∈ Adm M` assert the SAFE `P ⊆ Adm` direction, or
    does it (alone or combined with C2/C3) SMUGGLE the forbidden `Adm ⊆ P` / `== Adm` completeness?
    Be precise about quantifier direction.

Q2. Do C2 + C3 together faithfully pin "the analytic side is EXACTLY the `t̃=0` sublist of the full
    ledger"? They are VALUE-level `∃`-covers (matching on `(divExp, divProfile)` values), not an
    index bijection. Identify what they DO and DO NOT guarantee — e.g. multiplicity/cardinality: if
    two analytic divisors share a value, or two full `t̃=0` divisors share a value, is anything
    lost? Does the intended downstream use (reading off the SET/MIN of `t̃=0` exponents) survive the
    value-level, non-multiplicity form?

Q3. Is the predicate at risk of being HOLLOW/vacuous — e.g. is there a reading under which it is
    trivially true and carries no constraint on the accumulated exponents `divExp`? Consider both
    the case of leaves with `numDiv = 0` and the case where `divExp` might be a definitional alias
    of `Mval` rather than an independently-accumulated quantity. (For context: in the actual
    construction `divExp` is accumulated by per-step `+= runLen·resCols` bumps and `resRows·resCols`
    appends, and `divExp = Mval(divProfile)` is PROVEN via a maintained invariant, not defined.)

Q4. Any OTHER way this predicate could be weaker than "every leaf is a faithful full
    monomialization" while looking correct, or stronger than the paper (re-admitting the stranded
    `t̃>0` strata)?
