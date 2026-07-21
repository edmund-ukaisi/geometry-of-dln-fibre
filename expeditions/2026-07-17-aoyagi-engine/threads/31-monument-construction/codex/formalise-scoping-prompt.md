<task>
I am a Lean 4 + Mathlib formaliser. My task: discharge ONE `sorry`, the theorem
`exists_coreResolution`, which is the geometric heart ("monument") of an Aoyagi
resolution-of-singularities formalisation. I need a decorrelated opinion on HOW TO SCOPE
one work-session and on the cleanest Lean ENCODING. I am NOT asking you to write Lean; I
want a diagnosis of the decomposition and the encoding traps.

## The exact target (statement-locked, I cannot change it)

```
theorem exists_coreResolution (d : Fin (N + 1) → ℕ) (hd : Monotone d) (hN : 0 < N)
    (hpos : ∀ k, 0 < d k) (hne : (qipFeasible d).Nonempty)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple d) (he0 : e 0 = 0)
    (he_lin : IsLinearMap ℝ (⇑e)) :
    ∃ res : Resolution (coreGen d e) 0,
      (∀ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
        qipMin d hne ≤ ((res.charts c).jac a + 1 : ℤ)) ∧
      (∃ (c : Fin res.numCharts) (a : Fin (flatDim d)),
        a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) ∧
        ((res.charts c).jac a + 1 : ℤ) = qipMin d hne)
```

Here `coreGen d e k u = (∏_{s=1}^N C^{(s)})_{ij}(e u)` is the concrete POLYNOMIAL family
(entries of the product of N composable matrices, in flat coordinates u; e is a LINEAR
measure-preserving origin-fixing homeomorphism), `flatDim d = Σ d_{i+1} d_i`.

## The `Resolution` / `Chart` record each chart must FULLY inhabit (paraphrased fields)

`Resolution F 0` = { numCharts, charts : Fin numCharts → Chart F 0, hne, U ∈ 𝓝 0,
  hcover : volume (U \ ⋃ c, (charts c).g '' (charts c).dom) = 0 }.

`Chart F 0` requires (all as propositional fields, holding on the whole open `nbhd`, NOT
just germ at 0):
- g : (Fin D→ℝ)→(Fin D→ℝ), with g 0 = 0, Continuous g, AnalyticOnNhd ℝ g univ
- compact `dom ∋ 0`, open `nbhd ⊇ dom`, null `excep` with `InjOn g (nbhd\excep)`
- M' : ℕ, bexp : Fin M' → Fin D → ℕ (monomial exponents of the diagonal b_i), k₀ : Fin M'
- hchain : ∀ k d, bexp k₀ d ≤ bexp k d      (b_{k₀} | b_k divisibility chain)
- hbind : (bindingAxes (bexp k₀)).Nonempty
- hunit_mult : ∀ d ∈ bindingAxes (bexp k₀), bexp k₀ d = 1     (b_{k₀} squarefree on binders)
- jac : Fin D → ℕ, unit : (Fin D→ℝ)→ℝ, hunit_cont (ContinuousOn unit nbhd), hunit_ne
- hjac : ∀ u ∈ nbhd, |det (fderiv ℝ g u)| = jacWeight jac u * |unit u|   (jacWeight = ∏|u_d|^jac d)
- hideal_fwd : RegionRepresents (fun i ↦ F i ∘ g) (monomialFam bexp) nbhd   (∃ cofactors ContinuousOn nbhd, (F i∘g) = Σ_j a_ij · b_j on nbhd)
- hideal_bwd : RegionRepresents (monomialFam bexp) (fun i ↦ F i ∘ g) nbhd   (the reverse inclusion)

Downstream, ALREADY PROVED (I do not need to touch these): a per-chart value lemma
`2·wrlctAt |detDg| (∑(F∘g)²) 0 = inf' binding (jac a + 1)` (consumes hchain/hbind/
hunit_mult/hjac/hideal_fwd/hideal_bwd), an Object-D bridge `divisorMin = cCodim` (consumes
exactly the hlb/hattain conjuncts above), and a min-over-charts change-of-variables leaf
(a SEPARATE sorry, not mine). So the whole payoff is wired IF I produce this `res` + the
two conjuncts.

## The pen-and-paper certificate I was handed (verdict: YES-with-gaps)

The construction is Aoyagi's Cases-1&2 iterated blow-up. Key gifts (all verified pen+paper,
decorrelated):
- CLOSED FORM for the diagonal monomials: b_i = ∏_{s,k : t̃_{s,k} < i} u_{s,k} (b_0=1). The
  threshold sets {t̃<i} are nested increasing ⟹ b_1 | b_2 | … | b_M (divisibility chain).
- b_1 = ∏_{t̃=0} u is a nontrivial SQUAREFREE monomial (each u occurs ≤ once per b_i).
- jac(u_{s,k}) = M_{s,k} − 1 (accumulated Jacobian exponent); on the terminal (t̃=0) divisors,
  jac + 1 = M_{s,k} = Mval(t) = codim S(t) = a per-branch full-codimension exponent, where
  Mval(t) = (M¹−t¹)(M²−t¹) + Σ_{j=2}^L (t^{j-1}−t^j)(M^{j+1}−t^j) for a weakly-decreasing
  running-min profile t. The atlas-min over these = qipMin = cCodim (Object D, banked).
- hlb: every terminal exponent = Mval(admissible profile) ≥ min_admissible Mval = qipMin.
- hattain: every QIP minimiser is "envelope-clearable" hence realised by some leaf (residual II).
- hcover: Hironaka properness ⟹ the finitely many max-pivot-sector compact doms a.e.-cover a
  ball (residual I; may need a Hironaka-properness interface Mathlib lacks — a cite-or-build call).
- The IDEAL identity (hideal_fwd/bwd) comes from the composed monomial substitutions PLUS the
  "regular Q,P" unimodular transforms as ideal-cofactor changes; cofactors only need ContinuousOn
  (they may vanish), NOT nonvanishing. This is the coupled corank≥2 matrix algebra — the frontier
  this project has repeatedly dodged.

## What I have assessed

Fully building this at ∀-general L, ∀-general width is a multi-file, multi-session monument:
the g-analyticity + Jacobian-determinant computation, the two-sided polynomial-cofactor ideal
identity from the recursion (dependent-dimension matrix algebra — brutal in Lean), the a.e.-cover,
and the min-attainment combinatorics. I cannot honestly finish it in one session.

The conjuncts hlb/hattain are quantified over the ACTUAL charts of the ACTUAL `res`, so I cannot
discharge "part of" the leaf without producing real charts — the combinatorial data (bexp/jac) is
entangled with the geometric fields.

## My candidate plan for THIS session (want your adjudication)

Build a standalone reusable Core module developing the RECURSION'S COMBINATORIAL LAYER as general
lemmas NOT yet plugged into Chart/Resolution:
(1) define bexp / jac / k₀ via the certificate's threshold CLOSED FORMS (indexed by the recursion
    tree OR directly by profiles);
(2) prove the invariants: divisibility chain (hchain), b_1 nontrivial+squarefree (hbind/hunit_mult),
    terminal exponent = Mval(profile);
(3) prove the combinatorial hlb (Mval ≥ qipMin, riding banked cCodim_eq_qipMin) and attempt the
    hattain envelope-clearability;
(4) instance sanity checks reproducing the certificate table: (3,3,4)→8, (4,4,4)→12,
    (3,3,3,2,2)→4, (3,3,2,2)→4.
Then STOP and hand the geometric layer (analytic g + ideal identity + cover) to the controller
with a precise decomposition + a build-vs-cite flag on the cover.
</task>

<output_contract>
Answer in these sections, terse:
1. SCOPING VERDICT. Is my one-session scope (combinatorial layer only, no Chart inhabitation)
   the right honest increment, or is there a LEANER path to a genuinely-non-vacuous partial that
   touches the leaf itself? If you see a way to inhabit the FULL record for a restricted-but-honest
   subclass (e.g. width ≤ 2 "clean" telescoping case, or N=1) that discharges the leaf for that
   subclass as a real theorem, say so and rank it against my plan.
2. ENCODING. For the combinatorial layer: model the recursion tree operationally, OR define chart
   data directly by the closed forms (bexp = threshold-indicator, jac = Mval), OR index by profiles?
   Name the single biggest Lean-tractability trap in each and pick one. Dependent dimensions over
   varying D/M are a known pain here.
3. FIDELITY TRAP. If I DEFINE bexp/jac by closed form rather than derive them from a modelled
   recursion, what is the risk that my definitions are "convenient but not what Aoyagi's recursion
   produces" (a subtly-wrong spike), and what is the cheapest check that closes that risk beyond the
   4 instance sanity checks?
4. THE ENTANGLEMENT. Given hlb/hattain quantify over the actual res.charts, is there ANY way to bank
   a real fragment of `exists_coreResolution` this session, or is a standalone Core module (proving
   the same facts about a not-yet-wired data layer) strictly the best bankable unit? Be concrete.
5. BIGGEST RISK to my plan. One paragraph.
</output_contract>

<grounding_rules>
Flag inference vs. fact. You have only my paraphrase of the Lean records — if a claim depends on
a Lean detail you cannot see, say which. Do not invent Mathlib lemma names; if you name one, mark it
"verify". Prefer "I don't know" over confident fabrication.
</grounding_rules>
