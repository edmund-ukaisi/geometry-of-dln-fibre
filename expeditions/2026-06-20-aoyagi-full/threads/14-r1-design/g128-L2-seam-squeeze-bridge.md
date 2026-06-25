# L2 step-2→3 seam — the SQUEEZE bridge (green-tools-only) (pp-hall, 2026-06-22, #128)

**a114e07e's route-before-lines catch (sharp, real).** S1.5 (smooth-block additivity) needs the LITERAL
`Σ Eᵢ² + G²` (nReg regular squares + a core square). But the #125 deepest χ gives GENERATOR-equivalence,
NOT the literal form. What is the exact `F∘χ` form, and what is the sound bridge to the S1.5 input?

**Verdict: the literal `F∘χ = ΣEᵢ²+G²` is FALSE; the sound green-tool bridge is the SQUEEZE
`c₁·Φ ≤ F ≤ c₂·Φ` + `rlctAt_mono` both ways + unit invariance, then S1.5 on Φ.** No change of variables,
no measure Jacobian, no ideal-invariance lemma, no constant-rank. Two decorrelated legs converged
(pp-hall exact (2,2,2) r=1 + Codex xhigh).

## The exact F∘χ form (a114e07e's catch CONFIRMED)
For (2,2,2) r=1 deepest, `F = g00²+g01²+g10²+g11²` (literally a sum of 4 squares, NO overall unit factor).
The naive χ (rename the 3 regular generators g00,g01,g10 to coords E1,E2,E3 via their unit pivots
w4,w5,w2) gives `F∘χ⁻¹ = E1²+E2²+E3²+(g11∘χ⁻¹)²` where **`g11∘χ⁻¹ = G + E·h` has nonzero E-dependence**
(`∂(g11∘χ⁻¹)/∂E ≠ 0`, computed exact). So `F∘χ` is NOT `ΣEᵢ²+G²` — there are cross terms `2G·E·h`.
**a114e07e is right: the literal form is not reached by the source χ.** (Also confirmed against the
(2,2,2) Lean anchor: its `resolvedForm = E²+F0²+(qE+δG)²+(qF0+δH)²` is likewise COUPLED, not `ΣEᵢ²+G²` —
the anchor never produces the clean SoS form either; it blows up the coupled vertex instead.)

## The sound bridge: the SQUEEZE (green-tools-only)
Define `Φ = g00²+g01²+g10²+G²`, `G` = the Schur core (`g11` on the regular-zero locus; `G = −w3w7/(w1w6−1)`
for (2,2,2) r=1, E-free, vars w3,w7). Then:

**The squeeze `c₁·Φ ≤ F ≤ c₂·Φ` near 0 (c₁,c₂>0), structural (NOT just numerical):**
`F − Φ = g11² − G² = (g11−G)(g11+G)`, and **`g11 − G ∈ the regular ideal (g00,g01,g10)`** (verified:
`g11−G` vanishes on `{g00=g01=g10=0}`). So `g11 = G + Σ gᵢ hᵢ` (`gᵢ ∈ {g00,g01,g10}`, `hᵢ` bounded near 0),
and `F = Σgᵢ² + (G + h·g)²` is uniformly comparable to `Σgᵢ² + G² = Φ` (bounded-linear-perturbation
estimate: the bounded perturbation `h·g` cannot make `F` vanish faster than `Φ`, or conversely). Numerics
confirm: `F/Φ → 1` as scale→0 (min 0.9995, max 1.0007 at scale 0.01).

**`rlctAt_mono` both directions** (F, Φ ≥ 0, SAME zero-set `{prod=B}`):
- `c₁·Φ ≤ F` ⟹ `Φ ≤ c₁⁻¹·F`, with `Φ=0 ⟹ F=0` ⟹ `rlctAt(Φ) ≤ rlctAt(c₁⁻¹·F) = rlctAt(F)` (unit `c₁⁻¹`).
- `F ≤ c₂·Φ`, with `F=0 ⟹ Φ=0` ⟹ `rlctAt(F) ≤ rlctAt(c₂·Φ) = rlctAt(Φ)` (unit `c₂`).
- ⟹ **`rlctAt(F) = rlctAt(Φ)`.** The constant multiples are units, stripped by `rlctAtOn_unit_invariant_aux`.

**S1.5 on Φ:** Φ's 3 regular generators (pivots w4,w5,w2) are DISJOINT in leading vars from `G` (w3,w7),
so `Φ = (3 nondeg regular squares) + G²` splits via `smoothBlockND_rlct` + Fubini ⟹
`rlctAt(Φ) = nReg/2 + rlctAt(G²)`. For (2,2,2) r=1: `3/2 + 1/2 = 2 = aoyagiLambda(2,2,2) 1`. ✓

## The two answers to a114e07e's three questions
1. **Exact F∘χ form:** NOT `u·(ΣEᵢ²+G²)`, NOT literal `ΣEᵢ²+G²` — it is `ΣEᵢ²+(G+E·h)²` (cross terms).
   The literal form is NOT reachable by a source c-o-v. Use the SQUEEZE instead.
2. **The bridge:** the two-sided squeeze `c₁·Φ ≤ F ≤ c₂·Φ` + `rlctAt_mono` ×2 + unit-strip, NOT an
   integrand-unit-strip of `F∘χ`. CRUCIAL: the squeeze compares `F` and `Φ` at the SAME point — **NO
   change of variables, NO measure Jacobian `|det χ'|`**. The "two units" concern (integrand `u` AND
   measure `|det χ'|`) is **MOOT** — neither appears; only the positive constants `c₁⁻¹, c₂` (units).
3. **`G²` = the reduced core** (`G` = `g11` on the regular-zero locus = the Schur complement, vars w3,w7)
   = the reduced `(1,1,1)`-chain core whose rlct (1/2) R1 resolves. ✓

## The build chain for a114e07e (L2 half-(a), green-tools-only)
    rlctAt(F) deepest
      = rlctAt(Φ)               -- squeeze c₁Φ≤F≤c₂Φ + rlctAt_mono ×2 + unit-strip (rlctAtOn_unit_invariant_aux)
      = nReg/2 + rlctAt(G²)     -- S1.5 (smoothBlockND_rlct + Fubini), regular pivots ⊥ core vars
    G² = the reduced core → R1.
No constant-rank, no Morse normal form, no ideal-invariance lemma, no c-o-v / measure Jacobian. The ONLY
new obligation: the squeeze inequality `c₁·Φ ≤ F ≤ c₂·Φ` near 0, which rests on `g11 − G ∈ (g00,g01,g10)`
(the bounded-linear-perturbation estimate) — elementary, the regular gens are a regular sequence.

## Honest scope note (the L2 "elementary, no constant-rank" verdict, refined)
This REFINES #125/#122: the deepest split is NOT a clean source-coordinate `ΣEᵢ²+G²` (which would have
needed a Morse normal form). It is the SQUEEZE to `Φ` (rlct-level, not coordinate-level) + S1.5. Still
constant-rank-FREE — but the route is the two-sided `rlctAt_mono` squeeze, NOT a literal coordinate split.
a114e07e's catch correctly forced this refinement before the body went down a false-literal-form path.

Decorrelation: pp-hall exact (8 scripts `g128-scripts/`: the F∘χ E-dependence, the Schur core G, the
(2,2,2)-anchor-isn't-clean-either, the squeeze numerics, the structural g11−G∈ideal) + Codex xhigh
(independent: SOUND, the two-sided rlctAt_mono spelled, the bounded-linear-perturbation estimate, the
measure-Jacobian-moot point). Converged. Consult `codex/g128-L2-seam-{prompt,answer}.md`. Builds on #125.
