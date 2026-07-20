# R2 crux review — `Core.Dimension.Catenary` (independent decorrelated reviewer)

Reviewer: independent (read-only, no full aggregator rebuild — controller re-gating in parallel).
Target: `lean/DLNFibre/Core/Dimension/Catenary.lean` @ commit `574a9056` (`expedition/dimension-stack`).
Method: byte-level diff of the copied substitution against Mathlib source; soundness trace of the
"any field" chain through every called lemma; Stacks-tag content check; one decorrelated Codex consult
on the fidelity question.

## Overall verdict: PASS-with-notes

The crux holds. The copied `private`-Mathlib substitution is a **faithful, minimal** copy (one
declaration de-privatised, all proof bodies byte-identical), and the "any field" generality is
**sound, not overstated** — no `[IsAlgClosed]`, characteristic, or cardinality hypothesis enters
anywhere in the `≥`-induction chain. The only findings are cosmetic: three stale `§`-section
cross-references in the top docstring and a statement-card-vs-code drift on which Stacks tags are
machine attributes vs prose. None blocks.

---

## (1) Fidelity of the verbatim re-exposed Mathlib `private` substitution — PASS

Mathlib source: `Mathlib/RingTheory/NoetherNormalization.lean`, `namespace NoetherNormalization`,
`section equivT` (lines 62–169). Repo copy: `Catenary.lean` `namespace MonicPositioning` (lines
125–231).

A direct `diff` of the two sections returns **only** the following differences:

- `section equivT` → `namespace MonicPositioning` (and the matching `end`).
- Docstring/comment wording: `X_0`→`X₀` notation in prose, `/- … -/` plain comments upgraded to
  `/-- … -/` docstrings. No code.
- **Exactly one** visibility change: `private noncomputable abbrev T` → `noncomputable abbrev T`.
  Every other declaration keeps its exact Mathlib visibility: `lt_up`, `t1_comp_t1_neg`,
  `sum_r_mul_ne`, `degreeOf_zero_t`, `degreeOf_t_ne_of_ne`, `leadingCoeff_finSuccEquiv_t`,
  `T_leadingcoeff_isUnit` all stay `private`; `T1` was already public in Mathlib.

Every proof body is **byte-for-byte identical**. The preceding `variable` block is identical
(`{k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)` + `(v w : Fin (n + 1) →₀ ℕ)`),
so `up`, `r`, `T1`, `T` and every lemma elaborate against the same context; the `local notation3`
`up`/`r` re-pin to the same `f`. The `open` set is the same Mathlib set plus `Order PrimeSpectrum`,
which does not shadow any symbol used in the substitution (`X`, `C`, `degreeOf`, `finSuccEquiv`, …
resolve identically — and a green build with byte-identical bodies is itself evidence no
meaning-changing shadowing occurred).

The de-privatising is in fact **more conservative than the statement card describes**: the card says
"the only change is visibility (`private` → in-namespace)" for the whole construction, but only `T`
needed exposing (it appears in the public consequence's term
`⟨MonicPositioning.T f, MonicPositioning.T_leadingcoeff_isUnit f fne⟩`, line 241); the helper lemmas
remain `private`, reachable only because the consequence sits in the same file/module. The public
consequence `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit` (lines 238–241) is a thin packaging of
`T` + `T_leadingcoeff_isUnit`, faithful to what Mathlib proves internally.

The Provenance docstring (`§ Provenance of the monic-positioning substitution`, lines 109–120)
accurately describes what was copied and why (no public route): I independently confirmed the public
Noether-normalization API in this file is `exists_integral_inj_algHom_of_quotient` /
`exists_integral_inj_algHom_of_fg`, which normalize the **quotient** and do not hand back the
one-variable positioning automorphism the catenary `≥`-induction needs. Decorrelated Codex (gpt-5.1,
high effort) reached the same verdict on all three sub-points: no meaningful elaboration difference,
visibility-only change to `T`, "any field" not overstated.

## (2) Soundness of the "any field" generality — PASS

I traced every lemma in the `≥`-induction and the `≤` half. None re-introduces a field-strength
hypothesis:

- `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit` — the substitution `Xᵢ ↦ Xᵢ + X₀^(N^i)` chooses
  no `k`-point and no generic scalar (only `±1` and ℕ-exponents); characteristic- and
  cardinality-free. Confirmed by the byte-identical copy + Codex.
- `height_eq_height_under_add_height_map_quotient` (tower brick) → Mathlib
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (`KrullsHeightTheorem.lean:446`), which
  needs only `[IsNoetherianRing S]` + `[Algebra.HasGoingDown R S]`. No field. The `HasGoingDown A A[X]`
  instance comes from free ⟹ flat, field-independent.
- `ringKrullDim_quotient_eq_under_of_monic` → `ringKrullDim_eq_of_integral_injective`
  (`Integral.lean:107`), hypotheses just `[CommRing A] [CommRing S]`. No field.
- `one_le_height_map_quotient_of_monic` — only `[CommRing A]` + primality/monicity. No field.
- `ringKrullDim_mvPolynomial_fin_field` / `_field` (`Basic.lean:31,36`) → Mathlib
  `MvPolynomial.ringKrullDim_of_isNoetherianRing` (any Noetherian + `[Finite ι]`) +
  `ringKrullDim_eq_zero_of_field` (any `[Field F]`). No algebraic closure / characteristic / cardinality.
- `ringKrullDim_quotient_eq_coheight` (`Basic.lean:54`) — `[CommRing R]` only.
- `≤` half (`height_add_coheight_le`) — `ringKrullDim_mvPolynomial_fin_field` (field-only) +
  `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` (order-theoretic). No field.

A sweep of the whole module for `IsAlgClosed|CharZero|PerfectField|[Infinite|Fintype k|Finite k|
DecidableEq k` returns **zero hits in any signature or instance** — the only occurrences are
docstring lines stating these are *not* needed. Every field hypothesis in the file is the bare
`[Field k]`. The docstrings' char-/cardinality-free claim is accurate.

Assembly correctness spot-checked: the induction (`nat_le_height_add_coheight`, lines 333–405) peels
variable 0 via `Φ = phi.trans (finSuccEquiv k d)`, transports height and quotient-dim across the
cross-ring `k`-algebra equiv (`height_map_algEquiv`/`ringKrullDim_quotient_map_algEquiv` both handle
`R ≃ₐ[k] S` with `R ≠ S`), combines `hadd` + `hfib` into `q.height + 1 ≤ P.height`, and closes with
the IH. The `le_antisymm` of the two halves (line 422) is sound.

## (3) name = content (Stacks tags + docstrings) — PASS-with-notes

Actual machine `@[stacks …]` attributes in the file: **`00OS` only**, on the three equality forms
(`height_add_coheight_eq`, `height_add_ringKrullDim_quotient_eq`, `primeHeight_…_eq`). `00OX`, `00ON`,
`00OW` appear **only in prose** (`[Stacks, Tag …]` / parenthetical), not as attributes.

Tag content checked against the Stacks project:
- `00ON` (tower brick) — Mathlib itself tags the underlying
  `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` `@[stacks 00ON]`; the repo brick is a
  direct application. **Correct.**
- `00OX` (Lemma 10.115.3) — monic-after-coordinate-change so the leading coefficient in one variable
  is a unit/nonzero element of `k`. Exactly the positioning consequence. **Correct.**
- `00OW` — the Noether-normalization section/umbrella (Brasca–Su–Lin–Su); Mathlib tags
  `exists_integral_inj_algHom_of_fg` `@[stacks 00OW]`. Correct as a **provenance** attribution for the
  copied substitution.
- `00OS` (Lemma 10.114.4) — strictly, "a finite-type **domain** over a field is equidimensional";
  its *proof* uses precisely that maximal chains in `k[x₁..xₙ]/p` have length `n − height(p)`, i.e.
  the height+coheight=n computation the repo proves directly. So `00OS` is a **defensible** tag (the
  docstring is honest: "its proof *is* the height+coheight=n computation"), but it is not a verbatim
  statement match — the repo proves the polynomial-ring identity, `00OS` states the equidimensionality
  corollary. PASS-with-note: not overstated, but a reader chasing `00OS` lands on the corollary, not
  the identity. Acceptable as documented.

Note (statement-card drift, low stakes): the card asserts the positioning theorem is `@[stacks 00OX]`
and the tower brick `@[stacks 00ON]`; in the code these are prose mentions, not attributes. The code
is the more conservative of the two — flag only so the card is reconciled.

## (4) Organizational — PASS-with-notes

The `A`-general tower brick `height_eq_height_under_add_height_map_quotient` living in `Catenary` is
fine: it is exactly the catenary infrastructure the `≥`-peel consumes, and both the brief and Codex
endorse keeping it here rather than spinning a separate module. No action needed.

Cosmetic nit (stale docstring cross-references): the top-of-file roadmap (lines 26–51) cites
`§ Monic positioning` (line 28) and `§ Polynomial tower` (line 39), but **neither section title
exists** — the positioning machinery is in the `MonicPositioning` namespace under the
`§ The catenary ≤ direction and the one-variable polynomial tower` section, which is also where the
tower brick lives. (The third reference, `§ Provenance of the monic-positioning substitution`, line
37, does match the real section at line 109.) Two dangling `§` references; a one-line docstring fix.

---

## Suggested (non-blocking) fixes
1. Reconcile the statement card's `@[stacks 00OX]` / `@[stacks 00ON]` claims with the code (they are
   prose mentions, not attributes) — or add the attributes if machine-tagging is wanted.
2. Fix the two stale `§ Monic positioning` / `§ Polynomial tower` cross-references in the top docstring
   to point at the actual section title(s).
