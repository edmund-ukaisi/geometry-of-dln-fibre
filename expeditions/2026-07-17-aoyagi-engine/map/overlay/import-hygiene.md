# Overlay — import-hygiene (cartographer, curated layer) — PROPOSED, controller ratification

*NEW pass #2 (2026-07-18). A narrow-interface rule for the new Aoyagi-engine library against the
inherited ~490-module predecessor bulk. **Status: PROPOSED — awaiting controller ratification.**
Provenance: engine/glue modules importing the predecessor's heavy cones drag ~15-min builds (journal
tick 49 COST); three near-rebuild incidents this run traced to poor visibility of what is banked
vs half-built. Measured import weights below are transitive DLNFibre-internal counts (build-cost
proxy), 2026-07-18.*

## The core rule (one line)

**Engine modules import banked substrate ONLY from the indexed whitelist below; any heavy-cone
import (> 150 transitive) needs a re-home or an explicit controller note in the module docstring.**

## Why it bites here

The construction cone is already clean and CHEAP — the rungs that grind (R1/R2, the long pole)
build fast:

| Engine module | transitive imports | weight |
|---|---|---|
| `Engine.ResolutionTree` | 4 | VERY LIGHT |
| `Engine.EngineObligations` | 31 | LIGHT |
| `Engine.EngineConstruction` | 32 | LIGHT |
| `Engine.CanonicalWitness224` / `CoRank2Spike` | 31 | LIGHT |
| `Engine.RegionGluePerLeaf` | 40 | LIGHT |
| `Engine.RegionGlueGlobalize` | **304** | **HEAVY** |
| `Engine.EngineDriver` | **359** | **HEAVY** |

Only two engine modules are heavy, and the distinction matters:
- `EngineDriver` (359) is heavy because it consumes `Validate.HeadlineGenAssembly` (356 = the whole
  value lane). This is UNAVOIDABLE — the driver's job is to wire the engine into `_gen`, so it must
  see it. Acceptable: the driver builds rarely (R5 wiring), not on the R1/R2 grind loop.
- `RegionGlueGlobalize` (304) is heavy because it consumes `Validate.D1L2ExplicitCoreProducer` (302).
  This is AVOIDABLE and is the worked example below.

## The whitelist (banked substrate the engine may import directly)

*Light/medium banked modules, safe to import. Grouped by the rung that consumes them
([[banked-families]] has the decl-level pins).*

- **Combinatorial budget (LIGHT):** `Validate.RouteMLayerSplit` (21 — `minAdm`/`minAdmRec`),
  `Foundations.Lambda` (`Adm`/`admBound`/`Mval`/`lambdaCore`/`aoyagiLambda`), `Validate.RouteMState`
  (`minAdm_le_Mval_toNat` + the `ℕ ×ₗ ℕ ×ₗ ℕ` μ-lex WF idiom).
- **Carrier base (VERY LIGHT):** `Foundations.ParamsFlatLinear` (normed/findim/CLE instances —
  import this FIRST for any `Params`-fderiv design; the false "Params not normed" probe skipped it).
- **hbox interface (LIGHT):** `Validate.RouteMBoxReduction` (28 — `RouteMBoxThresholdFinite` verbatim).
- **Per-leaf reads (LIGHT):** `Validate.RegionGlueModelRead` (27 — `model_read_lt_top`),
  `Foundations.S1ScalingBridge` (the globalization bridge), `Foundations.S1Cover`/`S1BoxAdditive`
  (covers/null).
- **Value lane (HEAVY — R5 wiring ONLY):** `Validate.HeadlineGenAssembly` (356). Whitelisted for
  `EngineDriver` alone with the docstring note already present ("consumed verbatim, anchor-pin").

## Heavy cones — name + cost + disposition

- `Validate.D1L2ExplicitCoreProducer` (302) — the DLN homogeneity smul lemmas + the explicit-core
  producer. **RE-HOME candidate** (see worked example). Consumers: `RegionGlueGlobalize`.
- `Validate.HeadlineGenAssembly` (356) — the value lane. Keep (R5-only, unavoidable).
- `Validate.RouteMSJResolution` (56) — MEDIUM; carries the `instBorelSpaceParams` `RegionGluePerLeaf`
  deliberately AVOIDED by re-exposing the instance locally (`instBorelSpaceParamsGlue`) — a good
  worked instance of the narrow-interface rule already in the tree.

## Worked example — the D1L2 re-home (tick 49 deferred; proposed here)

`Engine.RegionGlueGlobalize` needs only the degree-2L homogeneity facts `flatNodeLoss_smul` /
`dlnLoss_zero_smul` / `prod_smul` — but imports `Validate.D1L2ExplicitCoreProducer`, which drags 302
files. D1L2's weight comes from `DeepestMinRlct` / `DeepestFrontGauge` / `R1ResolutionInterfaceL2` /
`D1L2ExplChartClose2` — the explicit-core PRODUCER machinery, entirely unrelated to the smul lemmas.
The smul lemmas themselves depend only on `Foundations.S1NodeFlatHomog` + `Validate.LossHomogeneity`
+ `Foundations.ParamsFlatLinear` (all LIGHT).

**Proposal:** extract `flatNodeLoss_smul`/`dlnLoss_zero_smul`/`prod_smul` (+ the DLN scaling bridge
`lintegral_flatNodeLoss_smul_bridge`) into a light `Foundations` homogeneity module (e.g.
`Foundations.DLNHomogeneity`). `RegionGlueGlobalize` would drop from 304 → ~small, moving the glue
lane off the 15-min build. This is post-hbox-safe (a pure relocation of banked, sorry-free content;
D1L2 keeps re-exporting for its existing consumers). Cross-ref: journal tick 48 already DELETED the
duplicate `S1ScalingBridgeDLN` — the smul family has ONE home (D1L2); this re-home gives it a LIGHT
home the engine can reach without the producer cone.

## Guardrails (fold into the seat briefs if ratified)

1. Before importing any `Validate.*` module, check its weight (or its place on the whitelist). If
   > 150 and you need one decl, prefer re-exposing that decl locally (the `instBorelSpaceParamsGlue`
   pattern) or requesting a re-home.
2. Survey banked state before commissioning (compass standing counsel — 3 redundant commissions the
   predecessor run; the false "Params not normed" probe; the duplicate `S1ScalingBridgeDLN`; the
   `abs_rpow_lintegral_Icc_lt_top` re-declaration in glue-t06's draft). The name-clash class is real.
3. Namespace discipline: new engine modules declare `namespace DLNFibre.DLN.RLCT.Engine` — two glue
   modules currently violate this (see [[naming]]); fold the fix into the D1L2 re-home commit if
   ratified.

---
**RATIFIED (controller, 2026-07-18).** The whitelist rule binds all engine/glue seats from now:
engine modules import banked substrate only from the indexed whitelist above; any heavy-cone
import (>100 files) outside it needs a controller note BEFORE it lands. The D1L2 re-home
(flatNodeLoss_smul / dlnLoss_zero_smul / prod_smul_pow + measurability into a light Foundations
module consuming only S1NodeFlatHomog + LossHomogeneity + ParamsFlatLinear; D1L2 imports it back)
is COMMISSIONED to the glue lane with the Engine-namespace fix (RegionGlueGlobalize +
RegionGluePerLeaf declare the parent namespace) folded in.
