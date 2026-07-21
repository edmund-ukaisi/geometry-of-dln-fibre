import Meta.Cordon
import FixtureCited

/-!
# `CordonClean` — the GREEN control (DLNFibre's actual definition of done)

The positive control for the *repo's* bar: **proved modulo declared citations**, NOT zero-cite. A scope
that (i) rests on no unaccounted axiom, (ii) uses a properly located+tagged cite, and (iii) has no
banked decl resting on a forecast is **green** — even with a cite present (`CITED=1`). This is the key
difference from the sibling `qs` harness, whose green requires `CITED=0`.

The harness (`scripts/cordon-test`) runs the soundness gate `#assert_banked_clean_batch
[CordonClean.cleanUsesCite]` (and per-root `#assert_banked_clean`) from a scratch module and asserts it
PASSES (exit 0) with the union summary — the batch also names the cited-source set in use here
(`Fixture Source B`). (The old whole-environment `cordon-audit` executable and its `--import` / `--ns` flags were deleted
2026-07-20; the gate is now the in-build `#assert_banked_clean[_batch]` + the `scripts/cordon` grep.)
* `cleanProved` — FORMALISED (UNACCOUNTED = ∅, no cite);
* `cleanUsesCite` — uses the located cite `citedFixtureAxiom` → CITED (one cite), still green (the DoD
  permits declared cites, mirroring the legitimate Aoyagi RLCT interface);
* `cleanForecast` / `cleanForecastInternal` — a forecast and a blueprint-internal consumer → no LEAK
  (the consumer is itself `@[blueprint]`, and nothing *banked* rests on the forecast).
-/

open Meta.Cordon

namespace CordonClean

/-- A fully-proved (foundational-only) theorem. -/
theorem cleanProved : 1 + 1 = 2 := rfl

/-- A theorem resting on the located, tagged cite `citedFixtureAxiom` → green with `CITED=1`. -/
theorem cleanUsesCite : True :=
  CordonFixtures.citedFixtureAxiom.elim (fun _ => trivial) (fun _ => trivial)

/-- A `@[blueprint]` forecast that nothing *banked* consumes. -/
@[blueprint] def cleanForecast : Nat := 7

/-- A `@[blueprint]` consumer of the forecast → blueprint-internal, permitted (not a leak). -/
@[blueprint] theorem cleanForecastInternal : cleanForecast = 7 := rfl

end CordonClean
