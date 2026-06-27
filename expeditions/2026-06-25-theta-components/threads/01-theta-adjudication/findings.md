# Thread 01 — θ adjudication (pen-and-paper, decorrelated) — certificate

**Persisted by the controller** (the harness blocks subagent report files). Decorrelated, Codex-concurred.

## Verdict (the truth-value) — CANDIDATE, controller flags H1-vs-H2 (see synthesis)

The two θ's are claimed the **same invariant** (pole multiplicity = #top-dim components via the SLT
dictionary), but the **two closed forms are not equal**: **θ_LR = C(m,|δ|) is the correct count; Aoyagi's
θ = a(ℓ−a)+1 *undercounts* whenever |δ| ≥ 2.** Equal exactly **iff |δ| ≤ 1**.

Smallest witness **(2,2,2,2,2), r=0**: true count **6 = C(4,2)**; Aoyagi's formula gives **5**. The agent
reads this as a **published error in Aoyagi (2023) Theorem 2's order formula** for deep (ℓ≥3) nets (the
formula plotted in her Fig 1) — not a transcription artifact, not a legitimately-different invariant.

## The crux — (2,2,2,2,2), r=0 (exact)

| quantity | value | source |
|---|---|---|
| m=ℓ, S, δ, a | 4, 10, −2 (\|δ\|=2), 2 | LR Def d1 = Aoyagi active set |
| λ_LR = codim/2 | 3/2 | LR thm:main-codim |
| λ_Aoyagi | 3/2 | Aoyagi Thm-2 Example |
| θ_LR = C(4,2) | **6** | LR eqn:number_top_comp (main.tex:1665) |
| θ_Aoyagi = a(ℓ−a)+1 | **5** | Aoyagi Thm 2 (p.9) |
| direct exhaustive QIP optimum count | **6** | full enumeration, min 3 |
| direct Kostant-partition component count | **6** | minimal-codim orbits, 109 partitions |

λ agrees exactly (3/2); θ does not (6 vs 5). Three independent ground truths (QIP brute force, LR closed
form, Kostant stratification) all give 6 for the **component count**.

## Agent's argument for "error, not different invariant"

λ (the RLCT) agrees exactly on all 7 differing-θ cases. The pole order is a germ-invariant of (variety,
function), independent of resolution; both papers compute the same threshold, so the order is well-defined
and cannot be two numbers ⟹ a(ℓ−a)+1=5 is wrong; true order = #components = C(m,|δ|) = 6.

**Controller caveat:** this argument shows the *order is well-defined*; it does not by itself show
*#components = order*. The 3 ground truths confirm #components = 6, via the dictionary, not the pole
multiplicity independently. See synthesis H1-vs-H2 — under verification (thread 03).

## Mechanism (structure, as data)

`a(ℓ−a)+1` = the **first-order (single-transposition) neighborhood** of the rounding vertex (identity +
the a·(ℓ−a) one-swap-reachable vertices). `C(m,|δ|)` = the **full closest-lattice-point set** (all |δ|
simultaneous ±1 corrections — type-A_m Voronoi cell, Conway–Sloane). They coincide through first order:
|δ|=0→1, |δ|=1→m. Agreement region exactly `|δ|≤1 ⟺ S mod m ∈ {0,1,m−1}`. Codex (xhigh, decorrelated)
converged independently.

## Consequences (data)

- Lean `cTheta = C(m,|δ|)` is the correct top-component count; do NOT wire Aoyagi's `a(ℓ−a)+1` as an
  alternate θ form.
- The `rlct = ½·codim` (λ) story is unaffected; Aoyagi-λ results stand.
- Exposition: any mention of Aoyagi's θ must be flagged correct only for |δ|≤1.
- Separate confirmed typo: Aoyagi Def 3 inactive bound `≤(ℓ−1)M^(s)` should be `≤ℓ·M^(s)` (independent).

## Artifacts
- `threads/01-theta-adjudication/scripts/theta_adjudication.py` (crux + sweep + (m,b) table; assertions pass).
- `threads/01-theta-adjudication/codex/{consult-prompt.md,consult-answer.md}`.
- Sources: LR main.tex (QIP :1155, main-codim :1735, number_top_comp :1665, Def d1 :1469, irred_comp :806);
  Aoyagi PDF Thm 1 p.6, Def 3 p.8, Thm 2 p.9, Fig 1 p.10.
