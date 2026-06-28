<task>
Lean 4 / Mathlib formalisation. I am lifting an already-proven (at output-width p=4) "cap-A carve"
finiteness lemma to general output-width p. The contract I must close:

  theorem schurCoreP_capA (p r : ℕ) (hIH : SchurLowerIH p (schurLambdaP p) r)
    (c' : ℝ) (hc0 : 0 < c') (hc' : c' < schurLambdaP p r) (T : ℝ) (hT : 0 < T) :
    SchurCore p r c' T

where:
- `SchurCore p r c' T` := `∫_{Δ∈[-T,T]^{r×r}} ∫_{S∈[-T,T]^{r×p}} frobSq(Δ·S)^{-c'} < ⊤`  (frobSq = sum of squared entries).
- `schurLambdaP p r := minAdm(![r,r,p])/2`. By an `inf'` over rank-drops t∈{0..r}:
    minAdm(![r,r,p]) = inf_{t} [ (r-t)² + t·p ].
    So schurLambdaP p 1 = min(1, p)/2 = 1/2 (p≥1).
       schurLambdaP p 2 = min(4, 1+p, 2p)/2.   (p=4 ⟹ min(4,5,8)/2 = 2.)
- `SchurLowerIH p (schurLambdaP p) r` gives: for all 1≤j≤r and 0<c''<schurLambdaP p (r-j), SchurCore p (r-j) c'' T''.

The dispatch routes to schurCoreP_capA:  (a) r≥3 ∧ schurLambdaP p r > p/2 (the interior carve), AND
(b) r∈{0,1,2} (always). r=0 is vacuous (lam 0 = 0, contradicts c'>0).

THE p=4 TEMPLATE (proven sorry-free):
- The interior carve `schurCoreGen_firing` handles r≥3 by an r²-chart radial cover; per chart, an a-axis
  radial divisor (finite for c' < r²/2, which holds since schurLambdaP p r ≤ r²/2) × an angular ratio
  residual. The ratio residual is the heart: pivot-normalise the angular matrix R (pivot=1, |entries|≤1),
  apply an N2b j=1 minor-pivot Schur split which DISJOINTLY decomposes frobSq(R·S) ≳ frobSq(top row of R·S)
  + frobSq(Sc·S_bot), peel the top "Morse" block of width p (threshold p/2, needs c' > p/2), leaving the
  residual at exponent c'' = c' - p/2, which is < schurLambdaP p (r-1) (via the peel inequality
  schurLambdaP p r ≤ p/2 + schurLambdaP p (r-1)). The residual is the SHIFTED corank-(r-1) core
  (Sc = M22 - rank1 shift), translation-dominated into a free (r-1)×(r-1) box and closed by the IH at r-1.
  The carve lemma `innerSGenCarve_le` and assembly `schurRatioResidGen_mid` carry `hr : 3 ≤ r`.
- For r∈{1,2}: SEPARATE bases (`schurCore4_one` for c'<1/2; `schurCore4_two` = `core_schur2_lt_top` for c'<2).
  These are Fin-4-specific. The r=2 base is a 4-chart radial cover (NOT a recursion).

THE QUESTION (scoping the r=1,2 leaves for general p):
1. The r=1 leaf: frobSq(Δ·S) = Δ₀₀²·∑_q S₀q². A 1-D radial divisor (c'<1/2 ⟹ 2c'<1) × a width-p Morse
   block (∑_{q:Fin p} S₀q²)^{-c'} finite for c' < p/2. Since schurLambdaP p 1 = 1/2 ≤ p/2, this is a clean
   p-general lift of schurCore4_one (swap Fin 4 → Fin p, threshold 2 → p/2). Confirm: any obstruction?
2. The r=2 leaf for general p: c' < schurLambdaP p 2 = min(4,1+p,2p)/2. The p=4 base core_schur2_lt_top
   needs c'<2 and is a bespoke 4-chart cover. QUESTION: can I instead AVOID a bespoke r=2 base by RELAXING
   the interior carve to fire at r≥2 (i.e. weaken `hr : 3 ≤ r` to `hr : 2 ≤ r`)? At r=2 the N2b j=1 split
   gives Sc : Fin 1 × Fin 1, residual core at r-1=1, IH at SchurCore p 1, residual exponent
   c' - p/2 < schurLambdaP p 1 = 1/2 (since c' < schurLambdaP p 2 ≤ p/2 + 1/2). The index bounds ⟨1+a⟩ with
   a<r-1=1 give 1+0=1<2=r ✓. Is there a STRUCTURAL reason the carve needs r≥3 and not r≥2? Specifically:
   (i) does the N2b minor-pivot Schur split / the pivot-normalisation / the r²-chart cover degenerate at r=2?
   (ii) does the radial cap c' < r²/2 = 2 still cover c' < schurLambdaP p 2 (need schurLambdaP p 2 ≤ 2,
        i.e. min(4,1+p,2p) ≤ 4 — TRUE always)? (iii) Is the carve's IH-at-(r-1)=1 well-formed given the
        IH supplies SchurCore p 1 for c''<schurLambdaP p 1=1/2 and we need c''=c'-p/2<1/2? 
   If r≥2 works, I get the r=2 leaf for FREE from the carve and only need a bespoke r=1 base.
3. Alternatively, if the carve genuinely needs r≥3, what is the cheapest p-general r=2 base? Is it a direct
   2-chart/Morse argument, or must I reproduce a 4-chart radial cover at width p?
</task>

<output_contract>
Three sections, terse:
A. r=1 leaf — confirm clean lift or name the obstruction (1-3 sentences).
B. r=2 via relaxed carve (hr:2≤r) — VERDICT (works / does-not-work), and if does-not-work, the SINGLE
   structural reason it degenerates at r=2 (point to (i)/(ii)/(iii)). If works, flag any cast/index subtlety
   that differs from r≥3.
C. If B fails: the cheapest p-general r=2 base recipe (sketch, ≤6 lines). If B works: say "skip".
Rank confidence on B (high/med/low). Flag inference vs. what you can verify from the structure I described.
</output_contract>

<grounding_rules>
You cannot see the Lean source; reason from the mathematical structure I described. Explicitly mark any
claim that depends on a detail of the N2b split you cannot verify from my description as INFERENCE.
</grounding_rules>
