# Dead-branch registry — SHAs recorded before deletion (prep house-cleaning, 2026-07-24)

Every seat branch's tip SHA is recorded here so deletion loses NOTHING (recover with
`git branch <name> <sha>` / `git fetch origin <sha>`). Classification drives the deletion plan.

## MERGED into `expedition/aoyagi-engine` (work is in-trunk history → DELETED this pass; SHA redundant but recorded)
| branch | tip |
|---|---|
| --carto2 | 347c34a62 |
| --nav | a99b92394 |
| --recon07 | 8243c56a1 |
| --t01-skeleton | 2888cebf7 |
| --t02-covdesign | d688441b8 |
| --t03-hunt | 8a57e39b0 |
| --t04-bridge | bb469c568 |
| --t12-pnp-o5 | 8067ca0de |
| --thread37-paper-mining | 9e804c4fc |
| -BAKE | f4f73fc8e |
| -E | a1029b5b1 |
| -Ecore | b24fa1bdb |
| -Eswap | bed8a639e |
| -L4D-wall | 89d34dd54 |
| -L6 | 582ab8226 |
| -M4B | b41c7c659 |
| -M7B | 0aa991c41 |
| -Q | f4c3bd31c |
| -REBAKE2 | e2b466976 |
| -api | 76427f7bf |
| -core | 549a1c01a |
| -core2 | 311745da7 |
| -elab | 209a0f0ca |
| -rung-c | 99a1eb5b0 |
| -w0l3 | fe9dbbaee |
| -w0l3-gens | a11cae2e5 |
| -w0l3-l3 | 0ab32e5e1 |
| -w0l3-o9 | a67da440d |

## UNMERGED (unique commits) — SHAs recorded; deletion DEFERRED to post-scout-code reuse/retire map
**RETIRED (geometric-fold, superseded by the re-architect — deletable once scout-code confirms):**
-CAP c845e97be · -CAPF 025693eac · -CAPR bbb3f924d · -CFF c4380af55 · -CX ff1bb2804 · -GM 3ed42a3d4 ·
-INV f8ccab333 · -KILL caaa53150 · -KILLFIN f7d485cef · -KILLSTEP 2324f0c00 · -L3T 1751c0710 ·
-L3T2 7c47467d8 · -L3T3 65e14acf2 · -L4 a22b76ccc · -L4B df2299e60 · -L4C 29a18e5c2 · -L4D 5bdc3d9f1 ·
-L4wire 2a9e14aa1 · -LL dadf4716b · -REBAKE 55a5d258f (dead pre-freeze render) · -p2 577b418e4

**KEEP (not deleted):**
- **-L7cover 646bcdcdb** — the L7 cover engine (`LeafCoverTiling`), KEPT/reused per the render (L7 shared).
  Preserve; likely merge into trunk during the build.
- **-PROTO 05c35eb8a** — the corank-2 cast-tax prototype (`Corank2Proto.lean`); reference for the builders'
  corank-2 Lean shape. Keep as reference.
- **report/aoyagi-engine-landscape d7aa1c46b** — a report branch; keep.

## Disposition (COMPLETE, 2026-07-24)
- MERGED (28): DELETED (safe; in-trunk).
- UNMERGED-RETIRED (21): DELETED after scout-code confirmed CapDescent/etc. absent + the on-branch fold
  retire orphans them; SHAs above are the recovery record.
- KEEP: `expedition/aoyagi-engine` (integration), `-L7cover` (kept L7 engine, 646bcdcdb — likely merge in
  the build), `-PROTO` (corank-2 reference, 05c35eb8a), `report/aoyagi-engine-landscape`.
- Result: 52 seat branches → 3. Branch house-cleaning DONE.

## Fossil-quarantine plan (sorry-bearing off-cone modules; scout-code list — PLAN, action deferred)
- **RouteM* / Deepest* / D1* / Case222* (~400 files, aoyagi-full chart route):** AxCheck-imported for the
  aoyagi-full L1/L2/(2,2,2) payoff roots (a SEPARATE deliverable). DO NOT bulk-delete. Quarantine =
  keep, mark off-this-expedition's-cone; prune only when the aoyagi-full deliverable is retired.
- **`DLN/RLCT/Skeleton.lean` (literal-name Skeleton root):** OPERATOR-GATED (#94 — does "done" require the
  literal-name clean-three?). Surface, do NOT act.
- **Retired `DLN/RLCT/Engine/*` (ClearableReify/GeoAlphaGauge/GeoAtlasTransfer/CanonicalWitness224):**
  off-cone; prune at build-close (after the fold retire), not now.
- **The on-branch geometric fold (MonumentAtlas/MonumentAssembly/GeometricAtlasD12/Wire cluster):** retire
  (banner superseded, delete imports+modules) ONLY AFTER N2 lands green — a stale sorry misdirects the
  gradient (P6). Sequenced in the build, not the prep.
