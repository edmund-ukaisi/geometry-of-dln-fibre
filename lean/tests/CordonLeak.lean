import Meta.Cordon

/-!
# `CordonLeak` — the ISOLATED blueprint-leak fixture (the `--allow-blueprint` control)

A minimal scope whose *only* violation is a blueprint leak — no unaccounted axioms, no cites, no
location issues — so it isolates the blueprint dimension of the gate and the `--allow-blueprint` flag:

* `cordon-audit --import CordonLeak --ns CordonLeak` → `UNACCOUNTED=0 CITED=0 LOCATION=0 LEAKS=1`, exit
  **1** (the banked `bankedLeak` rests on the forecast `forecast`);
* `cordon-audit --import CordonLeak --ns CordonLeak --allow-blueprint` → same summary, but exit **0**
  (the scope is declared blueprint-internal: the leak is reported, not gated).
-/

open Meta.Cordon

namespace CordonLeak

/-- A `@[blueprint]` forecast. -/
@[blueprint] def forecast : Nat := 1

/-- A BANKED theorem resting on the forecast → the sole (blueprint) violation in this scope. -/
theorem bankedLeak : forecast = 1 := rfl

end CordonLeak
