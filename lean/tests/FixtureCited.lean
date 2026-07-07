import DLNFibre.Core.Meta.Cited

/-!
# `FixtureCited` — the *located* cite file for the cordon fixtures

A `…Cited`-suffixed module (the located-cite invariant), holding the one **properly declared** cite
axiom the fixture (b) uses: `@[cited]`-tagged AND in a `…Cited` file. Contrast the *misplaced* cited
axiom in `CordonFixtures` (case (d)), which is tagged but in the wrong file. This is the positive
control: an axiom here must NOT trigger a LOCATION violation.
-/

open DLNFibre.Meta.Cited

namespace CordonFixtures

/-- (b) A correctly located + tagged cite axiom. -/
@[cited "Fixture Source B"]
axiom citedFixtureAxiom : True ∨ True

end CordonFixtures
