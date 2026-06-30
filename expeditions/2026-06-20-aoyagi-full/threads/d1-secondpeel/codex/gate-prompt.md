<task>
Lean 4 + Mathlib formalisation of Aoyagi's DLN-fibre RLCT result, L=2. I need a DECISIVE
verdict on whether one analytic obligation is "bounded at L=2" or "L>=3-wall-entangled".

## The architecture (verified by reading the canonical Lean modules)

The D1 (>=)-leg per-point claim is `rlctAt deepest <= rlctAt v` for a fibre optimal point v.
At L=2 it is a TWO-PEEL reduction, with the assembly already sorry-free:

- `deepest_le_of_optimal_of_iftResidual` (the two-peel producer) reduces ALL chart data to TWO
  C^1 residual vectors q (first peel) and q2 (second peel), each fed to a network-free engine
  `rlctAtOn_quasiSplit_ge_of_contDiff_residual` that, from a C^1 residual q : (Fin k -> R) x Y ->
  EuclideanSpace R (Fin n), produces the bound  k/2 + rlctAtOn(slice-residual R_slice) t0 <=
  rlctAtOn(sum s^2 + sum q^2)(0,t0).  R_slice(t) = sum_i (q (0,t) i)^2.

- The FIRST-peel chart producer `dln_hchart_residual` is BANKED sorry-free. It does NOT use any
  "gauge chart". Its technique: a selected invertible Jacobian MINOR (er, ec) of the flat-loss
  Jacobian at v -> a concrete chart Phi = chartFDerivEquiv (an explicit linear iso of the flat
  coords) -> the inverse-function-theorem right inverse Psi (C^2 near 0) via
  `rlctAtOn_eq_of_contDiff_chart_rinv` -> the selected m loss entries become the m regular squared
  coords (germ split `germA`), the rest are the residual vector `rawResidVec` -> bump-globalise the
  residual to a GLOBAL C^1 map q -> measure-preserving split homeomorph reindexes flat R^N ~=
  R^m x R^(N-m).  Net: rlctAt(loss) v = rlctAtOn(sum s^2 + sum q^2)(0,t0).

## The target (the SECOND peel)

The second-peel chart `hchart2` has the SAME SHAPE, applied to the first-peel SLICE RESIDUAL
R : Y -> R (where Y = Fin (flatDim H - nReg) -> R, R(t) = sum_i (q (0,t) i)^2):

   hchart2 : rlctAtOn R t0  =  rlctAtOn (fun p : (Fin extra -> R) x Y2 => sum p.1^2 + sum q2 p^2)(0,t02)

with extra = extraCount = m*(a+b) - a*b, charting R into the "degraded core" M'=(m-a, m-a-b, m-b).
Here, at a MIDDLE-STRATUM optimal v, nReg_v - nReg = extra extra Morse directions appear in R; the
second peel must peel those `extra` regular squares and land on the degraded reduced core.

## The concern to adjudicate

A stale code comment hints the second-peel construction "connects to DeepestGaugeChart" — a
DIFFERENT module which is the DEEPEST-POINT gauge-slice normal form and carries an OPEN sorry
(`deepest_gauge_squeeze_exists`), the L>=3 grouped-diffeo research wall #120. That gauge chart rides
the rank-r-EXACT pivot structure AT THE DEEPEST POINT. It is consumed by gate #44 (the `hDeepest`
deepest-side equality), a SEPARATE deliverable from my target.

Two candidate routes for the D1 >=-leg are documented:
(A) `GeneralVChartL2`: a SINGLE chart at general v doing nReg regular squares + reduced core in ONE
    peel; its docstring says the analytic heart is a "constant-rank quadratic split / Morse-Bott /
    Gromoll-Meyer" normal form, "strictly harder than the still-open deepest analog", Mathlib-lacking.
(B) the TWO-PEEL route (my route): first peel = selected-minor IFT (banked), second peel = ANOTHER
    selected-minor IFT applied to R (peeling `extra` Morse squares), landing the degraded core.

## The decisive question

Is the SECOND peel (route B) implementable with the SAME bounded selected-minor IFT technique the
FIRST peel proved works (a selected invertible Jacobian minor of R's own gradient at the slice
basepoint -> IFT right-inverse -> germ split -> bump-globalise -> MP split homeomorph), WITHOUT
routing through the DeepestGaugeChart #120 gauge-slice wall?

Key sub-questions:
1. R is itself a finite sum of squares of smooth (real-analytic, polynomial-in-network-entries)
   functions on Y (it is a residual loss). Does that mean a selected-minor IFT peeling `extra`
   of those squares is structurally the SAME as the first peel — i.e. nothing new beyond heavier
   reindexing/casework?
2. Is there any reason the SECOND peel would REQUIRE the gauge-slice (rank-r-exact pivot, grouped
   inter-layer diffeo) machinery that the deepest gauge chart needs and the first peel sidestepped?
   In particular: does peeling `extra` Morse directions out of a residual-loss germ at a NON-deepest
   point need a grouped/parametrised normal form that is genuinely L>=3-wall content, or is it a
   bounded single-block selected-minor IFT?
3. The first peel chose its minor at v from the FULL flat-loss Jacobian. The second peel chooses its
   minor from R's gradient at the slice basepoint t02. Is there a subtlety (e.g. R's gradient may
   VANISH at the slice basepoint because R is a residual that is itself O(quadratic) there) that
   would BREAK the selected-minor IFT for the second peel — making it genuinely need a different
   (Morse/Hessian-rank, not Jacobian-rank) construction?
</task>

<output_contract>
1. VERDICT (one line): is the second peel BOUNDED (same selected-minor IFT technique, route B) or
   WALL-ENTANGLED (genuinely needs the DeepestGaugeChart #120 gauge-slice)?
2. The single most load-bearing reason for the verdict.
3. Answer sub-question 3 specifically: at the slice basepoint, is the relevant non-degeneracy a
   JACOBIAN-rank condition (first-derivative, selected-minor-IFT-compatible) or a HESSIAN-rank /
   Morse condition (second-derivative, needs a quadratic split)? This is the crux: the `extra`
   directions are MORSE (quadratic, the loss is O(2) there), not first-order graph directions.
4. If WALL-ENTANGLED or if there is a genuine new-idea obstruction beyond reindexing: name the
   precise obstruction in 2-3 sentences.
5. If BOUNDED: name the one technical risk in the Lean build to watch.
</output_contract>

<grounding_rules>
Distinguish what you can INFER from the architecture I described vs what you would need to SEE in
the actual Lean source to confirm. Flag any assumption you are making about how the second-peel
residual q2 / the IFT minor is intended to be constructed. The crux is sub-question 3 / point 3:
the `extra` directions being MORSE (Hessian, second-order) rather than first-order regular graph
coordinates is the thing that could force a quadratic-split (Morse-Bott) rather than a plain
selected-Jacobian-minor IFT. Reason carefully about whether a residual loss's MORSE directions can
be peeled by a selected-minor IFT on its GRADIENT, or whether that genuinely requires a
second-derivative (Hessian) normal form Mathlib lacks.
</grounding_rules>
