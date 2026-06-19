# threads.md — voigt-discharge thread index

status ∈ open / in-progress / blocked / review-pending / closed / abandoned

| NN | slug | type | status | subject |
|----|------|------|--------|---------|
| 01 | mathlib-recon | scout | closed | Mathlib coverage map + build ladder + `[IsAlgClosed k]` verdict + route confirmation |
| 02 | dimension-formula-sizing | pen-and-paper | closed | Sized L5: bounded 2–3 module sub-library, integral-extension route (catenary avoided); sub-ladder L5.0–L5.8 |
| 03 | L5-dim-foundations | formaliser | closed (AUDIT survived) | First build tide — L5.4 (integral-ext `ringKrullDim` invariance) + L5.1 (`dim(R/p)=coheight p`) |

| 04 | L5-poly-dim-formula | formaliser | closed | L5.5 + L5.7-≤ + additive height brick; ≥ gap (monic-positioning) reported |
| 05 | L5-noether-monic | formaliser | closed | Build monic-coordinate-positioning (Noether normalization) → close L5.7 ≥ → full `height+dim=n` |

| 07 | L1-geometry-recon | scout | closed | Phase B architecture — **Route A (concrete affine)** decided; L1–L4 ladder; kill-condition L4(a)/(d) |
| 08 | L4-regular-local | formaliser | closed (sizing: L4a = sub-library) | De-risk kill-condition — smooth ⟹ IsRegularLocalRing (L4a) + local↔global dim (L4d), standalone CA |

| 09 | L4d-affine-domain-dim | formaliser | closed | Affine-domain equidimensionality (one module, fidelity PASS); local↔global feed-in for L4a |

| 10 | L4a-recon | pen-and-paper | closed | L4a sub-ladder — **BOUNDED ~3 modules via étale route**; load-bearing lemma `height_eq_under_of_flat_quasiFiniteAt` |
| 11 | L4a-M1-flat-qf-height | formaliser | closed (kill-cond did NOT fire) | M1 — flat + quasi-finite ⟹ prime height = contraction height (general CA, de-risks route) |

| 12 | L4a-M2-dim-bridge | formaliser | closed | Non-circular dimension bridge ringKrullDim(AtPrime m)=n=rank Ω (étale route, any field); reviewer FAITHFUL |

| 13 | L4a-M3-cotangent-regular | formaliser | closed | smooth⟹regular (cotangent comparison bounded); **L4★ COMPLETE**; reviewer FAITHFUL |

| 14 | geometry-recon | pen-and-paper | closed | Orbit geometry sized — L6 (3–4 mod sub-library, paper-cited degeneration), L1/L2/L3 bounded via pivot chart |
| 15 | L6.0-limit-lemma | formaliser | closed | Polynomial-curve limit ⟹ in V(vanishingIdeal) — free/independent; first geometry tide |

| 16 | orbit-variety | formaliser | closed | O_M irreducible (vanishingIdeal prime), orbit map, 𝒪(G_d) domain — 402 LoC, FAITHFUL |

| 17 | chart-design | pen-and-paper | closed | chart>descent; (2,2,2) pivot chart certified (Gröbner); general scale unsized |
| 18 | geom-route-general | pen-and-paper | open | Size chart-GENERAL vs homogeneity for general-M L3/L2; recommend (resolve before building) |

| 19 | L2a-cotangent-jacobian | formaliser | closed | Zariski tangent = Jacobian kernel (general CA, unconditional); AUDIT SURVIVED |

| 23 | L6.1-box-move | formaliser | closed | degeneration engine + (1,2,1) witness; general box-move = named gap; reviewer PASS |

Planned (created as they open):
- 0N — L0 Nullstellensatz/PrimeSpectrum bridge (formaliser tide)
- 0N — L1 GL/orbit/irreducibility (scout recon → formaliser)
- 0N — L2 affine tangent space + `T_M = im δ⁰` (pen-and-paper certificate → formaliser)
- 0N — L3 smoothness via homogeneity (formaliser)
- 0N — L4 regularity bridge (formaliser)
- 0N — L5 dimension formula build (formaliser; scope from thread 02)
- 0N — L6 Thm 3.8 orbitRankLocus = Ō_M (pen-and-paper → formaliser)
- 0N — L7 Voigt assembly (formaliser)
