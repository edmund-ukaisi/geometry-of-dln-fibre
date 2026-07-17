import Meta.Cordon

/-!
# `FixtureCited` — the *located* cite file for the cordon fixtures

A `…Cited`-named module (the located-cite invariant), holding the one **properly declared** cite axiom
that fixture (b) uses: `@[cited]`-tagged AND in a located cite file. Contrast the *misplaced* cited
axiom in `CordonFixtures` (case (d)), which is tagged but in the wrong file. This is the positive
control: an axiom here must NOT trigger a LOCATION violation. (The module name `FixtureCited` is in
`Meta.Cordon.citedFileAllowlist`, so it counts as located even though its last name-component is not
literally `Cited`.)
-/

open Meta.Cordon

namespace CordonFixtures

/-- (b) A correctly located + tagged cite axiom. -/
@[cited "Fixture Source B"]
axiom citedFixtureAxiom : True ∨ True

end CordonFixtures
