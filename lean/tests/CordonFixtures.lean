import Meta.Cordon
import Meta.CordonAudit
import FixtureCited

/-!
# `CordonFixtures` — adversarial fixtures for the citation cordon (the SPEC, built first)

These decls have **known-expected verdicts**; they are the proof the cordon actually catches
violations (a cordon unproven to catch (c)/(d)/(h) is worthless). They live in a **separate namespace**
`CordonFixtures` / `CordonLeak` / `CordonClean` (bare, NOT `DLNFibre`) and in modules whose names have
no `DLNFibre` prefix, so the real gate — which audits module provenance `DLNFibre` — never sees the
*intentional* violations here. The test harness (`scripts/cordon-test`) runs
`cordon-audit --import CordonFixtures --ns CordonFixtures --ns FixtureCited` and asserts the verdicts
below, including that (c)/(d)/(f)/(h) FAIL the gate (nonzero exit).

Cited-cordon verdict map (asserted by the harness):
* `(a)` `fullyProved` — FORMALISED (UNACCOUNTED = ∅, CITED = ∅);
* `(b)` `usesCite` — CITED[src] (UNACCOUNTED = ∅, CITED = {citedFixtureAxiom});
* `(c)` `usesUntagged` — UNACCOUNTED = {untaggedFixtureAxiom}, gate FAILS;
* `(d)` `misplacedCitedAxiom` — a `@[cited]` axiom NOT in a located cite file → LOCATION violation;
* `(e)` `transitiveCite` — CITED (kernel transitivity: it uses `usesCite` which uses the cite);
* `(f)` `opaqueHider`/`usesOpaque` — an axiom hidden in an `opaque`'s value → still UNACCOUNTED (the
  batch traverses `opaqueInfo.value`).

Blueprint-leak verdict map:
* `(g)` `blueprintForecast` — a `@[blueprint]` *def* (a forecast on a non-axiom);
* `(h)` `bankedUsesBlueprint` — a banked theorem resting on `blueprintForecast` → BLUEPRINT-LEAK, FAILS;
* `(i)` `blueprintInternal` — a `@[blueprint]` theorem resting on `blueprintForecast` → NOT a leak
  (blueprint-internal consumption is permitted; a forecast may rest on a forecast).

The whole namespace is a violating set (it deliberately contains (c), (d), (f), (h)); running the gate
over it must exit nonzero with `UNACCOUNTED=5 CITED=2 LOCATION=3 LEAKS=1`. UNACCOUNTED (5): the two
untagged axioms (`untaggedFixtureAxiom`, `hiddenFixtureAxiom`) + the three decls resting on them
(`usesUntagged`, `opaqueHider`, `usesOpaque`). CITED (2): the located cite + the misplaced cite.
LOCATION (3): the two untagged axioms + the misplaced cited axiom (the located cite in `FixtureCited`
is in scope and passes). LEAKS (1): `bankedUsesBlueprint` resting on the forecast `blueprintForecast`.
-/

open Meta.Cordon

namespace CordonFixtures

/-! ### (a) A fully-proved declaration → FORMALISED -/

/-- (a) A theorem resting only on the foundational allowlist (in fact on nothing). -/
theorem fullyProved : 1 + 1 = 2 := rfl

/-! ### (b) A declaration using a properly tagged+located cite → CITED[src]

The cited axiom itself is declared in the located file `tests/FixtureCited.lean` (in the
allowlisted module `FixtureCited`), tagged `@[cited "Fixture Source B"]`. -/

/-- (b) A theorem depending on the located, tagged cite axiom `citedFixtureAxiom`. -/
theorem usesCite : True := citedFixtureAxiom.elim (fun _ => trivial) (fun _ => trivial)

/-! ### (e) A TRANSITIVE cite: `transitiveCite` uses `usesCite`, which uses the cite → CITED -/

/-- (e) A theorem that uses `usesCite` (transitively the cite) → still CITED by kernel transitivity. -/
theorem transitiveCite : True ∧ True := ⟨usesCite, usesCite⟩

/-! ### (c) A declaration using an UNTAGGED axiom → UNACCOUNTED (gate FAILS)

`untaggedFixtureAxiom` is a bare `axiom` — no `@[cited]` tag — declared *here* (not in a located cite
file). Any decl using it lands in UNACCOUNTED; the axiom itself is a LOCATION (untagged) violation. -/

/-- (c) An UNTAGGED axiom — the forget-proofness case (a forgotten cite). -/
axiom untaggedFixtureAxiom : ∀ n : Nat, n + 0 = n

/-- (c) A theorem depending on the untagged axiom → UNACCOUNTED. -/
theorem usesUntagged : 7 + 0 = 7 := untaggedFixtureAxiom 7

/-! ### (d) A `@[cited]` axiom OUTSIDE a located cite file → LOCATION violation

Tagged correctly but declared in this non-located module: the location half of the invariant fails. -/

/-- (d) A `@[cited]` axiom in the WRONG file (this is `CordonFixtures`, not a located cite file). -/
@[cited "Fixture Source D (misplaced)"]
axiom misplacedCitedAxiom : ∀ n : Nat, 0 + n = n

/-- (d) A theorem using the misplaced-but-tagged axiom → CITED for accounting, but the axiom triggers
a LOCATION violation. -/
theorem usesMisplaced : 0 + 5 = 5 := misplacedCitedAxiom 5

/-! ### (f) An axiom hidden behind an `opaque` value → STILL UNACCOUNTED

The completeness of the custom `collectAxiomsBatch` is the load-bearing claim (a missed traversal case
= a false green). `opaque` is the subtle case: its value is stored but the constant is irreducible.
The batch reads `opaqueInfo.value`'s used constants, so an axiom in that value is NOT concealed. -/

/-- (f) An untagged axiom (a proof), hidden inside an `opaque` value's erased Prop component. -/
axiom hiddenFixtureAxiom : True

/-- (f) An `opaque` definition carrying the hidden axiom in its (proof) component. Code generation
erases the Prop proof, but `collectAxioms` / `collectAxiomsBatch` read the *kernel* term of
`opaqueInfo.value`, so the opacity does not conceal the axiom. -/
opaque opaqueHider : {_n : Nat // True} := ⟨3, hiddenFixtureAxiom⟩

/-- (f) A theorem using the opaque → transitively UNACCOUNTED (the hidden axiom surfaces through the
opaque's value; the opacity does not hide it). -/
theorem usesOpaque : opaqueHider.val = opaqueHider.val := rfl

/-! ### (g)–(i) Blueprint fixtures: a forecast, a banked leak, and a permitted internal consumer -/

/-- (g) A `@[blueprint]` forecast — a not-yet-banked stub, on a `def` (blueprint tags any decl). -/
@[blueprint] def blueprintForecast : Nat := 42

/-- (h) A BANKED theorem resting on the forecast → BLUEPRINT-LEAK (banked consumes a forecast). -/
theorem bankedUsesBlueprint : blueprintForecast = 42 := rfl

/-- (i) A `@[blueprint]` theorem resting on the forecast → NOT a leak (blueprint-internal is fine). -/
@[blueprint] theorem blueprintInternal : blueprintForecast = 42 := rfl

end CordonFixtures
