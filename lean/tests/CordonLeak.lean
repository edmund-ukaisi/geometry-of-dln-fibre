import Meta.Cordon

/-!
# `CordonLeak` — the ISOLATED blueprint-leak fixture

A minimal scope whose *only* violation is a blueprint leak — no unaccounted axioms, no cites, no
location issues — so it isolates the blueprint (GATE 2) dimension of the soundness gate:

* `#assert_banked_clean CordonLeak.bankedLeak` (and the batch `#assert_banked_clean_batch
  [CordonLeak.bankedLeak]`) → FAILS, exit **1**, naming the leaked forecast (the *banked* `bankedLeak`
  transitively rests on the `@[blueprint]` forecast `forecast`).
* Contrast a *forecast* consumer (`CordonFixtures.blueprintInternal`): a `@[blueprint]` decl may rest on
  a forecast, so the gate skips GATE 2 for it — blueprint-internal consumption is permitted.

(The old whole-environment `cordon-audit` executable and its `--import` / `--ns` / `--allow-blueprint`
flags were deleted 2026-07-20; the gate is now the in-build `#assert_banked_clean[_batch]` + the
`scripts/cordon` grep.)
-/

open Meta.Cordon

namespace CordonLeak

/-- A `@[blueprint]` forecast. -/
@[blueprint] def forecast : Nat := 1

/-- A BANKED theorem resting on the forecast → the sole (blueprint) violation in this scope. -/
theorem bankedLeak : forecast = 1 := rfl

end CordonLeak
