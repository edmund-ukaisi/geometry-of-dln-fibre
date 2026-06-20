# threads.md — voigt-discharge thread index

status ∈ open / in-progress / blocked / review-pending / closed / abandoned

| NN | slug | type | status | subject / outcome |
|----|------|------|--------|-------------------|
| 01 | mathlib-recon | scout | closed | Mathlib coverage map + build ladder + `[IsAlgClosed k]` verdict; route A confirmed |
| 02 | dimension-formula-sizing | pen-and-paper | closed | Sized L5: bounded 2–3 module sub-library, integral-extension route (catenary avoided); sub-ladder L5.0–L5.8 |
| 03 | L5-dim-foundations | formaliser | closed (AUDIT survived) | First build tide — L5.4 (integral-ext `ringKrullDim` invariance) + L5.1 (`dim(R/p)=coheight p`) |
| 04 | L5-poly-dim-formula | formaliser | closed | L5.5 + L5.7-≤ + additive height brick; ≥ gap (monic-positioning) reported |
| 05 | L5-noether-monic | formaliser | closed | Monic-coordinate positioning (Noether normalization) → close L5.7 ≥ → full `height + dim = n` |
| 06 | L0-nullstellensatz | formaliser | closed (AUDIT survived) | L0 codim↔dim bridge `height (vanishingIdeal) + varietyDim = Nat.card` over alg-closed `k` |
| 07 | L1-geometry-recon | scout | closed | Phase B architecture — Route A (concrete affine) decided; L1–L4 ladder; kill-condition L4(a)/(d) |
| 08 | L4-regular-local | scout | closed | De-risk: smooth ⟹ `IsRegularLocalRing` (L4a) + local↔global dim (L4d) sized as 3-module sub-ladder |
| 09 | L4d-affine-domain-dim | formaliser | closed | Affine-domain equidimensionality `height m + dim(R/m) = dim A`; local↔global feed-in for L4a; fidelity PASS |
| 10 | L4a-recon | pen-and-paper | closed | L4a sub-ladder — bounded ~3 modules via étale route; load-bearing `height_eq_under_of_flat_quasiFiniteAt` |
| 11 | L4a-M1-flat-qf-height | formaliser | closed (AUDIT survived) | M1 — flat + quasi-finite ⟹ prime height = contraction height (general CA, de-risks route) |
| 12 | L4a-M2-dim-bridge | formaliser | closed (AUDIT survived) | M2 — `ringKrullDim (AtPrime m) = n = rank Ω` non-circularly (étale route, any field); reviewer FAITHFUL |
| 13 | L4a-M3-cotangent-regular | formaliser | closed (AUDIT survived) | M3 — smooth ⟹ regular via cotangent comparison `finrank (m/m²) = n`; L4★ COMPLETE; reviewer FAITHFUL |
| 14 | geometry-recon | pen-and-paper | closed | Orbit geometry sized — L6 (3–4 module degeneration sub-library), L2/L3 bounded via pivot chart |
| 15 | L6.0-limit-lemma | formaliser | closed (AUDIT survived) | Polynomial-curve limit ⟹ in `V(vanishingIdeal)`; first geometry tide, independent |
| 16 | orbit-variety | formaliser | closed | L1 — `O_M` irreducible (vanishingIdeal prime), orbit map, `𝒪(G_d)` domain via `Localization.Away`; FAITHFUL |
| 17 | chart-design | pen-and-paper | closed | L3 pivot-chart design + (2,2,2) Gröbner-certified `AlgEquiv`; general scale flagged for thread 18 |
| 18 | geom-route-general | pen-and-paper | closed | Geometry route DECIDED — HYBRID (homogeneity L3 + uniform L2 cotangent↔Jacobian), superseding per-orbit charts |
| 19 | L2a-cotangent-jacobian | formaliser | closed (AUDIT survived) | Zariski cotangent = Jacobian kernel `finrank_cotangentSpace_eq_finrank_ker_jacobian` (general CA, unconditional) |
| 20 | L2b-tangent-design | pen-and-paper | closed | L2b circularity confirmed; determinantal (KMS) & orbit-stabiliser routes both need sub-libraries |
| 21 | route-sizing | pen-and-paper | closed | Route (a) smooth-point assembly chosen over (b) orbit-stabiliser; KMS avoided via re-scoped L2b |
| 22 | L6-degeneration-design | pen-and-paper | closed | L6.1 family certified (3 instances); L6.2 box-move generation = cover-classification lace sub-library |
| 23 | L6.1-box-move | formaliser | closed (AUDIT survived) | Degeneration engine + (1,2,1) witness; general box-move = named gap; reviewer PASS |
| 24 | L6.2-cover-classification | pen-and-paper | closed | K1 fires (scoped): generation clean given move-existence; sub-fact 2 framed as irreducible AD content |
| 25 | L6.3-rank-locus-closed | formaliser | closed (AUDIT survived) | `orbitRankLocus` Zariski-closed + `O_M ⊆ it` + minor-vanishing brick; reviewer PASS |
| 26 | subfact2-cover-nonemptiness | pen-and-paper | closed | Overturns 24 — sub-fact 2 closes ELEMENTARILY (discrete-Green telescope); L6.2 buildable, no Abeasis–Del Fra cite |
| 27 | L6.1-general | formaliser | closed | L6.1-general — common-summand lemma + split box-move; non-split move handled (sorry-free) |
| 28 | L6.2-generation | formaliser | closed | L6.2 box-move-chain generation: achievable `s ≤ r` connected by finite moves via measure descent (sorry-free) |
| 29 | geometry-assembly-ladder | pen-and-paper | closed | Geometry L3/L2b/A assembly plan; hard nugget = `finrank (range δ⁰) = dim Z_M` (char-0 submersion) |
| 30 | L2b-submersion-derisk | pen-and-paper | closed | L2b submersion de-risk → route-c trdeg chain; pinned MISSING Mathlib bricks (affine image dim from differential rank) |
| 31 | L6.4-orbit-closure | formaliser | closed | L6.4 + L1★ — `vanishingIdeal_orbitRankLocus_eq_orbitSet` (Thm 3.8, `Ō_M = orbitRankLocus`) + ideal prime (sorry-free) |
| 32 | A0-orbit-pullback-dim | formaliser | closed (AUDIT survived) | A0 — `varietyDim Z_M = ringKrullDim (image μ_M^*)` (f.g. domain) via first-iso + L6.4 (sorry-free) |
| 33 | A1-kahler-trdeg-api | scout | closed | Mathlib v4.29 API map for the route-c discharge (Kähler/trdeg); honest module count + hardest must-build lemma |
| 34 | A2-l3-smoothness-api | scout | closed | Mathlib v4.29 API map for L3 smoothness via homogeneity; crux = `vanishingIdeal {orbit closed pts} = ⊥` (cheap from L6) |
| 35 | A3-orbit-smooth | formaliser | closed (AUDIT survived) | A3 (L3) — `Z_M` smooth at `M` via generic smoothness + dense orbit + transport; `κ(m_M) = k` (sorry-free) |
| 36 | A4.2-jacobian-criterion | pen-and-paper | closed | char-0 Jacobian criterion certificate for `trdeg (image μ_M^*) ≤ finrank (range δ⁰)`; Mathlib-targetable decomposition |
| 37 | A4-orbit-image-dim | formaliser | closed | A4 route-c submersion — `ringKrullDim (image) ≤ finrank (range δ⁰)` via trdeg + generic-diff-rank (char-0), unconditional |
| 38 | A6-assembly-design | pen-and-paper | closed | A6 design — reverse inequality via intrinsic cotangent (drops A5/L2a minors); squeeze + L7 arithmetic |
| 39 | hA-codex | reviewer | closed | Codex tactic-block discharge of `D_orbit_conj_termA` (conjugation identity), compiled in-repo |
| 40 | A6-voigt-discharge | formaliser | closed (AUDIT survived) | A6 capstone — `hVoigt` discharged (`codimRep_orbitRankLocus_eq_orbitLinearCodim`, `[IsAlgClosed][CharZero]`); Cor 3.5 headline unconditional |
| 41 | fidelity-audit | reviewer | closed | Decorrelated Codex fidelity audit of the Voigt chain — SOUND across Q1–Q4, non-vacuous; `CharZero`/`IsAlgClosed` honest |
| 42 | bedrock-audit | hardener | closed | Bedrock/precision audit — no RLCT overclaim, hypotheses minimal; one mild note on the word "UNCONDITIONAL" |
| 43 | ctheta-geometric | formaliser | closed | Geometric reading of `C` — `codimRepCanonical_orbitRankLocus_eq_codimForm` + `cCodim_eq_inf_geomCodim` (per-orbit, unconditional) |
