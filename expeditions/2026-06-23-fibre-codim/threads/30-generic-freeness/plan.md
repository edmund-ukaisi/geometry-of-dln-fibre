# Thread 30 — generic freeness (b-build rung 1)

*Seat: formalisation tide. Target: the standalone general generic-freeness theorem that lets the
non-circular fibre-codimension `+δ` route close (thread 29 ROUTE-C: generic freeness → relative
fibre-dim → homogeneity transport ⟹ `hSweep`).*

## VERDICT (one line)

**LANDED, and far cheaper than the scout's ~3-5 module estimate.** Generic freeness (module case) is
NOT a from-scratch sub-library: the Mathlib v4.29 substrate
`Module.FinitePresentation.exists_free_localizedModule_powers` + "every module over a field is free"
collapses it to a **one-shot application at the fraction field**. One module, four theorems, green,
sorry-free, axiom-clean.

## What landed

`lean/DLNFibre/Core/GenericFreeness.lean` (≈115 LoC):
- `Module.FinitePresentation.exists_free_localizedModule_of_isDomain` — primitive core (`[IsDomain]`
  + `[FinitePresentation]`, no Noetherian).
- `Module.exists_free_localizedModule_of_isDomain` — Noetherian + finite corollary.
- `Module.exists_flat_localizedModule_of_isDomain` — flat form (rung-2 going-down interface).
- `Module.exists_basicOpen_subset_freeLocus_of_isDomain` — freeLocus density (the missing genericity).
- Non-vacuity witness (`ℚ[X]`) shown in-file.

Statement cards: `statement-cards.md`. Codex consult (high effort):
`codex/genfree-strategy-{prompt,answer}.md` — confirms the fraction-field reduction is sound and
minimal; flags the module-vs-algebra-finite-type scope (caveat 5, recorded in the module docstring +
cards).

## The proof (no dévissage)

Domain `R`, f.g. `M`. Localize at `nonZeroDivisors R`. `FractionRing R` is a FIELD ⟹
`LocalizedModule (nonZeroDivisors R) M` is `Module.Free` (Mathlib instance). The descent lemma
`exists_free_localizedModule_powers` (which `isOpen_freeLocus` itself uses) hands back a single
`r ∈ nonZeroDivisors R` with `M[1/r]` free over `R[1/r]`; `r ≠ 0` in a domain. The textbook prime
filtration / dévissage is bypassed — Mathlib's lemma already contains the spreading-out argument.

## Scope (honest boundary)

Finite-MODULE case only. Full Grothendieck for finite-type ALGEBRAS (relative dim > 0) is strictly
stronger (EGA IV 6.9.1), Mathlib-absent, a separate larger build — NOT done here. Rung 2 must check
whether the chart map `R → S` is module-finite (then this suffices) or only algebra-finite-type (then
it needs the roadmapped extension). The dévissage substrate IS present in Mathlib
(`IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`,
`exists_relSeries_isQuotientEquivQuotientPrime`) for whoever builds the algebra version — but that
induction is over modules and would re-prove the (cheaper) module case; the algebra case additionally
needs Noether normalization, the genuinely new work.

## Reproduction

Probe scripts elaborated all three output forms sorry-free before writing the module (`/tmp` probes;
the final module is the durable artefact). Whole-library build green (3716 jobs).
