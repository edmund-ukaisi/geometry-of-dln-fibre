import DLNFibre.Core.Meta.Cited
import DLNFibre.Core.Meta.CordonAudit
import FixtureCited

/-!
# `CordonFixtures` — adversarial fixtures for the citation cordon (the SPEC, built first)

These decls have **known-expected verdicts**; they are the proof the cordon actually catches
violations (a cordon unproven to catch (c)/(d) is worthless). They live in a **separate namespace**
`CordonFixtures` (bare, NOT `DLNFibre`) so the real gate — which audits the `DLNFibre` namespace —
never sees the *intentional* violations here. The test harness (`scripts/cited-test`) runs
`cited-audit --import CordonFixtures --ns CordonFixtures` and asserts the verdicts below, including
that (c)/(d) FAIL the gate (nonzero exit).

Verdict map (asserted by the harness):
* `(a)` `fullyProved` — FORMALISED (UNACCOUNTED = ∅, CITED = ∅);
* `(b)` `usesCite` — CITED[src] (UNACCOUNTED = ∅, CITED = {citedFixtureAxiom});
* `(c)` `usesUntagged` — UNACCOUNTED = {untaggedFixtureAxiom}, gate FAILS;
* `(d)` `misplacedCitedAxiom` — a `@[cited]` axiom NOT in a `…Cited.lean` file → LOCATION violation;
* `(e)` `transitiveCite` — CITED (kernel transitivity: it uses `usesCite` which uses the cite);
* `(f)` `opaqueHider`/`usesOpaque` — an axiom hidden in an `opaque`'s value → still UNACCOUNTED (the
  batch traverses `opaqueInfo.value`; the regression guard for the load-bearing completeness case).

The whole namespace is a violating set (it deliberately contains (c), (d), (f)); running the gate over
it must exit nonzero with `UNACCOUNTED=5 CITED=2 LOCATION=3`. UNACCOUNTED (5): the two untagged axioms
(`untaggedFixtureAxiom`, `hiddenFixtureAxiom`) + the three decls resting on them (`usesUntagged`,
`opaqueHider`, `usesOpaque`). CITED (2): the located cite + the misplaced cite. LOCATION (3): the two
untagged axioms + the misplaced cited axiom.
-/

open DLNFibre.Meta.Cited

namespace CordonFixtures

/-! ### (a) A fully-proved declaration → FORMALISED -/

/-- (a) A theorem resting only on the foundational allowlist (in fact on nothing). -/
theorem fullyProved : 1 + 1 = 2 := rfl

/-! ### (b) A declaration using a properly tagged+located cite → CITED[src]

The cited axiom itself is declared in the located file `tests/FixtureCited.lean` (module ending in
`Cited`), tagged `@[cited "Fixture Source B"]`. -/

/-- (b) A theorem depending on the located, tagged cite axiom `citedFixtureAxiom`. -/
theorem usesCite : True := citedFixtureAxiom.elim (fun _ => trivial) (fun _ => trivial)

/-! ### (e) A TRANSITIVE cite: `transitiveCite` uses `usesCite`, which uses the cite → CITED -/

/-- (e) A theorem that uses `usesCite` (transitively the cite) → still CITED by kernel transitivity. -/
theorem transitiveCite : True ∧ True := ⟨usesCite, usesCite⟩

/-! ### (c) A declaration using an UNTAGGED axiom → UNACCOUNTED (gate FAILS)

`untaggedFixtureAxiom` is a bare `axiom` — no `@[cited]` tag — declared *here* (not in a `…Cited`
file). Any decl using it lands in UNACCOUNTED; the axiom itself is a LOCATION (untagged) violation. -/

/-- (c) An UNTAGGED axiom — the forget-proofness case (a forgotten cite). -/
axiom untaggedFixtureAxiom : ∀ n : Nat, n + 0 = n

/-- (c) A theorem depending on the untagged axiom → UNACCOUNTED. -/
theorem usesUntagged : 7 + 0 = 7 := untaggedFixtureAxiom 7

/-! ### (d) A `@[cited]` axiom OUTSIDE a `…Cited.lean` file → LOCATION violation

Tagged correctly but declared in this non-`Cited` module: the location half of the invariant fails. -/

/-- (d) A `@[cited]` axiom in the WRONG file (this is `CordonFixtures`, not a `…Cited` file). -/
@[cited "Fixture Source D (misplaced)"]
axiom misplacedCitedAxiom : ∀ n : Nat, 0 + n = n

/-- (d) A theorem using the misplaced-but-tagged axiom → CITED for accounting, but the axiom triggers
a LOCATION violation. -/
theorem usesMisplaced : 0 + 5 = 5 := misplacedCitedAxiom 5

/-! ### (f) An axiom hidden behind an `opaque` value → STILL UNACCOUNTED

The completeness of the custom `collectAxiomsBatch` is the load-bearing claim (a missed traversal case
= a false green). `opaque` is the subtle case: its value is stored but the constant is irreducible.
The batch reads `opaqueInfo.value`'s used constants, so an axiom in that value is NOT concealed —
this fixture is the regression guard for that traversal case. -/

/-- (f) An untagged axiom (a proof), hidden inside an `opaque` value's erased Prop component. -/
axiom hiddenFixtureAxiom : True

/-- (f) An `opaque` definition carrying the hidden axiom in its (proof) component. Code generation
erases the Prop proof, but `collectAxioms` / `collectAxiomsBatch` read the *kernel* term of
`opaqueInfo.value`, so the opacity does not conceal the axiom. -/
opaque opaqueHider : {n : Nat // True} := ⟨3, hiddenFixtureAxiom⟩

/-- (f) A theorem using the opaque → transitively UNACCOUNTED (the hidden axiom surfaces through the
opaque's value; the opacity does not hide it). -/
theorem usesOpaque : opaqueHider.val = opaqueHider.val := rfl

end CordonFixtures
