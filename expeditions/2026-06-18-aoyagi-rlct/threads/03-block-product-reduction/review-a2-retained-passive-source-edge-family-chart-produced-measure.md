# Review - A2 retained-passive source-edge-family chart-produced measure

Reviewer: xhigh read-only checker `Hegel`.

Verdict: PASS after documentation correction.

The Lean theorem is well-scoped.  It fixes `EdgeFamily`, `base`,
`sourceChart`, and `DetData` internally, assumes the needed measurable and
open-measurable structure for `DetData`, and takes the load-bearing
`hretainedData` hypothesis as the a.e.-measurable determinant-subtype data
path.  The proof derives `hsourceChart` by composing `hretainedData` with the
continuous fixed-base p.13 source chart, derives `hchart_mem` and `hfactor`
from `hdet` and `hdataFactor` via the source-edge-family helper, and then calls
the existing chart-produced handoff with `Cedge := fun E => E`.

The reviewer found no Lean correction.  The requested documentation correction
was to list the retained-data inputs explicitly in the statement card:
`hdet`, `residualCoordEquiv`, `hdataFactor`, and
`hretainedData : AEMeasurable (fun y => <retainedData y, hdet y>) signedBox`.
That correction is incorporated.

Nonclaims remain correct: no endpoint-equivalence construction, no
label-preserving endpoint provenance, no original prior or external source
measure identification, no Jacobian comparison for such a prior, no
source-rank coverage, no normal crossings, no pole order, and no RLCT.
