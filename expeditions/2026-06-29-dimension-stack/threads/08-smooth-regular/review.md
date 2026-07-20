# Review — E2 capstone (08-smooth-regular): smooth point ⟹ regular local ring

**Reviewer:** independent decorrelated audit. **Target commit:** `b9affa4a` (`expedition/dimension-stack`).
**Method:** read-only (no full build — controller re-gated green at 3819); per-lemma trace +
git rename-diff + Mathlib lemma-signature checks + one decorrelated Codex (xhigh) consult.
**Files audited:** `lean/DLNFibre/Core/Dimension/Regular.lean`, its E1 dependency
`Core/Dimension/Smooth.lean`, convention cross-check `Core/Dimension/{Catenary,AffineDomain}.lean`.

---

## Item 1 — `[PerfectField]` soundness (headline generality): **PASS**

The chain is genuinely `[PerfectField k]`-only; no step silently re-pulls `[IsAlgClosed]`.

**Import-surface evidence.** `Regular.lean` does NOT import `Mathlib.FieldTheory.IsAlgClosed.Basic`
(confirmed absent — the vestigial import was dropped as claimed). Its sole `DLNFibre` import is
`Core.Dimension.Smooth` (line 18), whose own `DLNFibre` imports are only `Integral` + `Catenary`. No
`IsAlgClosed`/`algClosure`/`AlgClosed` symbol appears in the body of either file — the single string hit
is a prose mention in a `Smooth.lean:50` docstring. `#print axioms` (card) is the clean
`[propext, Classical.choice, Quot.sound]` for both headlines.

**Per-lemma trace (verified against the actual proof body).** The only field-theoretic input is at
`Regular.lean:121-124` inside `finrank_cotangentSpace_le_of_isSmoothAt`:
- `EssFiniteType k (ResidueField R)` is built by `.comp _ R _` from `EssFiniteType R (ResidueField R)`
  (`inferInstance`) — pure CA, no field condition;
- `Algebra.FormallySmooth k (ResidueField R) := inferInstance` resolves via
  `Algebra.FormallySmooth.of_perfectField`, whose Mathlib signature I confirmed at
  `Mathlib/RingTheory/Smooth/Field.lean:55` is `[PerfectField K] [Algebra.EssFiniteType K L]` — **no
  `[IsAlgClosed]`**.
- The smoothness hypothesis itself, `IsSmoothAt k m` (`Regular.lean:108`,
  `haveI : Algebra.FormallySmooth k R := ‹IsSmoothAt k m›`), is `Algebra.FormallySmooth R (AtPrime m)`
  by definition (`Smooth/Locus.lean:46`, `@[stacks 00TB]`, no field hypothesis) — **consumed, not
  produced**. So the smooth-locus density `dense_smoothLocus_of_perfectField` (which callers use to
  *establish* `[IsSmoothAt]`) never enters this chain. Confirmed: the card's claim on this point holds.
- The dimension input `hdim` comes from E1's `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`
  (`Smooth.lean:218`), whose signature is `[Field k]`-only (verified: variable block `[Field k]` at
  `Smooth.lean:148`, no `PerfectField`/`IsAlgClosed`). Closed-point maximality there goes through
  `IsLocalization.isMaximal_of_isMaximal_disjoint` (Zariski-lemma route), not a residue-field-is-`k`
  Nullstellensatz. Non-circular: the dimension is an input from the étale-over-affine route, never the
  cotangent space.

The final hypothesis on `smooth_point_isRegularLocalRing` (`Regular.lean:197`) and
`finrank_cotangentSpace_eq_of_isSmoothAt` (`Regular.lean:228`) is genuinely `[PerfectField k]`
(alongside `[Field k]`, `[Algebra.FiniteType k A]`).

**Decorrelated Codex (xhigh) consult** (artefact: `codex/perfectfield-{prompt,answer}.md`) independently
confirms: (a) κ(m) of a finite-type algebra at a maximal ideal is finite over k (Zariski), and perfect ⟹
finite ⟹ separable ⟹ formally smooth ⟹ H1 vanishes; (b) the cotangent count is over κ(m), not k — no
hidden κ(m)=k assumption, so no algebraic-closure shortcut; (c) the regular-local conclusion is
field-input-free.

**Note (precision nuance, not a defect).** Codex's point (d): `[PerfectField k]` is *not* the
information-theoretic minimum for the **theorem** — the pointwise requirement is only that *this*
κ(m)/k be separable. The card's phrase "the weakest that compiles" (line 57) reads as a claim about
*this proof route's clean global instance*, not the theorem's absolute minimum, and is honest under that
reading: a per-residue-field-separability hypothesis would be a different, bespoke statement, not a clean
typeclass. The card does NOT overclaim a global minimum — it claims `[PerfectField]` is "exactly
sufficient" and `[IsAlgClosed]` "NOT re-needed," both confirmed. Recording the nuance for completeness;
it does not move the verdict.

---

## Item 2 — `@[stacks 00TV]` tag honesty + convention: **PASS**

Stacks Tag 00TV (Lemma 10.140.5) is a **biconditional**: for a finite-type k-algebra S and prime q with
κ(q) separable over k, "S smooth at q over k" ⟺ "S_q regular" (verified against the Stacks source). The
theorem proves the **forward direction only** (smooth ⟹ regular).

The tag string is honest about this: `@[stacks 00TV "the smooth ⟹ regular direction (perfect base field
gives separable residue fields)"]` (`Regular.lean:196`). It (i) names the exact direction proved and
(ii) records that perfectness supplies the separability hypothesis the iff requires. The docstring
(`Regular.lean:191`, `:25`) repeats "the smooth ⟹ regular direction." No overstatement: nothing claims
the converse.

**Convention match — confirmed by in-repo precedent.** This harness routinely tags a one-directional /
restatement / corollary form of a Stacks result with the parent tag plus a clarifying string:
- `Integral.lean` tags a one-directional **inequality** `dim S ≤ dim R` with note "the dimension
  inequality `dim S ≤ dim R`";
- `AffineDomain.lean` tags **three** distinct restatements/corollaries of the equidimensionality result
  all under `@[stacks 00OS]`, each with its own clarifying string (a restatement, a maximal-ideal
  corollary, the `dim A = dim Aₘ` form) — and the docstring there explicitly discusses that none displays
  the arbitrary-prime form verbatim, calling the tag "true and on-point";
- `Catenary.lean` tags the order-form of 00OS with "the order form: ...".

Tagging a one-direction theorem with an iff-tag plus a directional string is squarely within the
established `00OS`/`Integral` pattern, and Mathlib itself does this routinely. PASS.

---

## Item 3 — Re-home fidelity + name=content: **PASS**

Git records `b9affa4a` as a **rename** (`{.../SmoothPointRegular.lean => .../Regular.lean}` path notation
in `--stat`). The full rename-diff (`git diff --find-renames b9affa4a~1 b9affa4a`) is 125 lines, and every
changed line is confined to:
- docstrings / module comment / copyright header,
- import set,
- `namespace DLNFibre.Core` → `namespace DLNFibre.Core.Dimension` (+ matching `end`),
- dropping the now-redundant `open DLNFibre.Core.Dimension` (the old file needed it to reach the E1 bridge
  unqualified; the new file *is* in that namespace, so the call at `Regular.lean:205` resolves
  within-namespace — verified E1's `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` lives in
  `namespace DLNFibre.Core.Dimension`, `Smooth.lean:68`),
- the newly added `@[stacks 00TV "..."]` attribute line,
- one cosmetic docstring word ("a map" → "a map cast", `injective_cotangent_cast` doc).

**Zero changes to any theorem signature, hypothesis list, type, or proof body.** All six declarations
(`injective_cotangent_cast`, `finrank_kaehler_chart_eq`, `finrank_cotangentSpace_le_of_isSmoothAt`,
`finrank_kaehler_localizationAtPrime_eq`, `smooth_point_isRegularLocalRing`,
`finrank_cotangentSpace_eq_of_isSmoothAt`) carry identical statements pre/post; the old file already
carried `[PerfectField k]` on the three flagged decls — confirming the card's "benign surprise" (the
weakening was landed upstream in a prior thread, not in E2). `open Algebra IsLocalRing TensorProduct` is
identical in both.

**name=content** on the supporting lemmas: `injective_cotangent_cast` (injectivity transport along ideal
equality — body is `subst h; exact hf`), `finrank_kaehler_chart_eq` (chart Kähler finrank = n),
`finrank_cotangentSpace_le_of_isSmoothAt` (the `≤`, content matches), `finrank_kaehler_localizationAtPrime_eq`
(chart→local transport), `finrank_cotangentSpace_eq_of_isSmoothAt` (the companion equality). Names denote
exactly what is proved; the capstone is `…isRegularLocalRing`, not an over-reaching `rlct…`/`…smooth_iff`.
PASS.

---

## Overall verdict: **PASS** (all three items), survived all cases checked.

No mathematical hole, no statement drift, no silent `[IsAlgClosed]` re-pull, honest tag. The single
recorded nuance (Item 1 note) is a precision footnote on "weakest", not a defect — `[PerfectField]` is the
right clean field hypothesis for this proof route and the build/axioms/trace are consistent. The E2
deliverable is faithful to its statement card.

### Caveats co-located (for the synthesis)
- `[PerfectField]` is sound and `[IsAlgClosed]`-free; it is a *clean sufficient* field hypothesis, not the
  theorem's absolute minimum (per-residue-field separability is the true pointwise requirement). State it
  as "perfect base field" — do not upgrade to "weakest possible for the theorem."
- `@[stacks 00TV]` is the **forward** direction of an iff; the tag string says so. Any downstream prose
  must not cite it as the full iff.
- `[IsAlgClosed]` in `FibreSmoothBlock.lean` consumers is out of scope (genuine Nullstellensatz use, RF
  territory), correctly flagged by the card as not-a-hole.
