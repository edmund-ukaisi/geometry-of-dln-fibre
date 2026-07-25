# Statement card — admissible leaf region (terminal-shrink ⋈ cover), (2,2,2)

**Claim.** At a (2,2,2) terminal resolution leaf, the terminal non-vanishing region and the cover tiling box
conjoin on ONE chart (terminal-shrink ⋈ cover), under the real-leaf collapse `unit ≡ 1`.

**Lean.** `admissible_leaf_region_222` (+ 4 supporting lemmas), `DLNFibre/DLN/Aoyagi/Corank2AdmissibleLeaf222.lean`,
@ `1bb3f96fe` on `expedition/aoyagi-engine-reroute`. Clean-three; full `scripts/lb DLNFibre` = 9035 jobs, 0 errors.
Supporting: `exists_cover_ball_of_open`, `terminal_bezout_cover_ball`, `terminal_region_eq_of_collapse`,
`terminal_bezout_collapse` (API-clean: `unit ≡ 1 ⇒ PrincipalInv` on FULL `V`, no opaque `V'` — the variant the
deep build should consume).

**Hypotheses.**
- `unit ≡ 1` on `V` (the real-leaf collapse; a DESIGN GUARANTEE — `chart_of_collapse` sets `unit := 1`, the
  `pathMap` shears are Jacobian-exactly-1, `cert_334` verified the (3,3,4) pivot strict-transform ≡ 1 —
  **evidenced, but NOT re-derived by this gate**; discharging it at the built leaf = R4's `hjac` / the `hcollapse` obligation).
- `closedBall 0 R ⊆ V` (the chart region contains the inflated cover box).

**Gloss.** `unit ≡ 1` makes `terminal_bezout`'s shrink `V' = V ∩ {unit≠0} = V` VACUOUS, so the cover's
`≥ 1`-radius box (the block-blow-up argmax lift needs source radius `max R 1 ≥ 1` — a genuine floor) fits
inside `V'`. The exact compatibility condition: `unit` non-vanishing on `closedBall 0 1` (radius 1, NOT merely
near 0); `unit ≡ 1` gives it with room, a merely-continuous `unit 0 ≠ 0` would not clear the `≥ 1` floor.

**Residuals (NOT discharged by this gate — routed to the elder + downstream rungs).**
- Derive `unit ≡ 1` at the BUILT (2,2,2)/(3,3,4) leaf (discharge `hcollapse`) — R4 `hjac` (the (★) telescoping), detail-at-scale.
- COUPLED admissible-leaf: this gate is UNCOUPLED (2,2,2); the coupled concern is *reframed* (`unit ≡ 1` dominant-pivot
  strict transform holds coupled too, cert_334) but not exercised as a coupled Lean lemma — elder judges sufficiency.
- FAMILY-UNION-COVER: single-leaf shrink ⊇ its own box does NOT test the union of shrunken leaf-domains tiling the
  parent box — owed into R2's marriage-fold.
