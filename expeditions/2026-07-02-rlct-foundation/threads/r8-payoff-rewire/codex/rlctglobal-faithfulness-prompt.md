<task>
Faithfulness review of a Lean 4 definition against a paper definition — no repo access needed, judge on the math.

PAPER (Lehalleur–Rimányi 2024, "Geometry of the fibers of the multiplication map of deep linear networks"):
- Def 8.1(i): for a real-analytic F : X → ℝ, rlct(F) := sup { s ∈ ℝ | |F|^{-s} is locally integrable } ∈ ℝ ∪ {∞}.
- Def 8.1(ii): rlct_x(F) := sup { s ∈ ℝ | |F|^{-s} is locally integrable AT x } (the LOCAL version).
- Prop 8.3(i): 0 < rlct_x(F) < ∞ ⟺ F(x)=0; and rlct(F) < ∞ ⟺ F^{-1}(0) ≠ ∅.
- Prop 8.3(iii): rlct(F) = inf_{x ∈ X} rlct_x(F). This inf is over ALL of X; it is "not always attained because of potential issues at infinity", but IS attained when X is compact or when X,F are algebraic.

MY LEAN (cite-free), over any [MeasureSpace X] [TopologicalSpace X], K : X → ℝ:
  rlctGlobal K := sSup { c : ℝ | 0 ≤ c ∧ ∀ x, IntegrableAtFilter (fun y ↦ (K y)^(-c)) (𝓝 x) }
  rlctAt K x   := sSup { c : ℝ | 0 ≤ c ∧ IntegrableAtFilter (fun y ↦ (K y)^(-c)) (𝓝 x) }
where ^ is Real.rpow (of the signed value K y), IntegrableAtFilter f (𝓝 x) = "f integrable on some nbhd of x", sSup is the ℝ (conditionally-complete) supremum (so sSup of an unbounded-above or empty set is the junk value 0).

QUESTIONS (answer each; flag any GENUINE fidelity gap vs harmless-but-noteworthy):
(1) I restrict the sup to 0 ≤ c, whereas the paper sups over all s ∈ ℝ. For a loss F = K ≥ 0 (the DLN square-Frobenius loss), is this faithful/harmless? (Note rlct is always ≥ 0; is there any case where a negative s is "admissible" and would change the sup?)
(2) I use K^(-c) = Real.rpow (K y) (-c) of the SIGNED value, not |F|^{-s}. Faithful when K ≥ 0 everywhere (the DLN loss)? Any pitfall from Real.rpow's convention on negatives / at 0 (Real.rpow 0 (neg) = 0)?
(3) The ℝ-valued sSup returns junk 0 (not +∞) when the admissible set is unbounded above (e.g. at a regular point where every c is locally admissible, or when there is no zero at all). I document this as out-of-scope, and I characterize rlctGlobal = sInf (rlctAt '' {x | K x = 0}) — the inf over the ZERO LOCUS — rather than a bare inf over ALL x (which would be identically 0 because of the junk). Given the junk-0, is the inf-over-zero-locus the correct HONEST reading of Prop 8.3(iii)? (Paper's inf is over all X, but regular points contribute rlct_x = +∞ by Prop 8.3(i), so the inf is really over {F=0}.)
(4) Any subtlety in equating my "∀ x, IntegrableAtFilter (𝓝 x)" ("globally locally integrable") with the paper's "locally integrable" (Def 8.1(i))? In particular: is "loc-integrable at every point" the same as "locally integrable" as a global property, or is there a compactness / paracompactness gap on a non-compact X?
</task>

<output_contract>
Four short numbered answers (2–5 sentences each). For each: VERDICT = {faithful | harmless-caveat | GENUINE GAP}, then the reason. End with a one-line overall verdict: is rlctGlobal a faithful rendering of Def 8.1(i) for the F ≥ 0 / DLN use-case?
</output_contract>

<grounding_rules>
Judge purely on the mathematics of the definitions as stated. Distinguish "faithful for F ≥ 0" from "faithful in general". Flag any case where the Lean value would DIFFER from the paper value (not just be junk-out-of-scope).
</grounding_rules>
