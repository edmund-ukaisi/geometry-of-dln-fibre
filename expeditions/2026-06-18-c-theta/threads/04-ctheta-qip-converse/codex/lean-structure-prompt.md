<task>
Lean 4 + Mathlib v4.29. Formalising the CONVERSE of the QIP (Lehalleur–Rimányi Thm 6.1 / Lemma 6.4):
every codimForm-minimiser over the Kostant partitions of a weakly-increasing dimension vector (corner 0)
is "horizontal-lace", hence in the e-image, hence ≥ the QIP minimum. The easy half (≤) is DONE and committed.
I need the cleanest LEAN PROOF STRUCTURE for the two hard sub-steps; I will write/build the code.

EXISTING (committed, in `DLNFibre.Core`):
- `kostantPartitions d r : Finset (Fin (N+1) × Fin (N+1) → ℕ)` — functions m (interval-mult arrays)
  vanishing off i≤j, with d_k = ∑_{i≤k≤j} m(i,j) at every vertex k, and corner m(0,last)=r.
- `codimForm N (M : ℤ→ℤ→ℤ) := ∑_{1≤i≤u≤j≤v≤N} M(i-1)(j-1)·M(u)(v)`. Evaluated on `extendℤ m`.
- `extendℤ m` : the ℤ-extension (m on the box 0≤a≤b≤N, else 0).
- `cCodim d 0 h := (kostantPartitions d 0).inf' h (fun m ↦ codimForm N (extendℤ m))` (the combinatorial C).
- `codimForm_update_corner`: codimForm is BLIND to the corner entry m(0,N) (proven).
- `mOfE d e : Fin(N+1)²→ℕ` (the substitution, e:Fin N→ℕ), `codimForm_mOfE (Monotone d): codimForm(extendℤ(mOfE d e))=Gqip d e`,
  `mOfE_mem (Monotone d)(∑e=d0): mOfE d e ∈ kostantPartitions d 0`,
  `cCodim_le_qipMin (Monotone d): cCodim d 0 ≤ qipMin d`  (the EASY ≤).

MATH (numerically verified exact, sympy, all N≤4 unless noted):
- "Horizontal-lace" (HL): m(a,b)=0 whenever 1≤a AND b≤N-1 (every supported interval touches an endpoint 0 or N).
- HL corner-0 KPs = EXACTLY the mOfE-image {mOfE d e : ∑e=d0} (bijection, verified N≤4).
- Two MOVES (Function.update-style edits on the array m, each a valid corner-0 KP of the SAME d):
  (A) UNCROSS, strict crossing a<c≤b<d: m(a,b)−=1, m(c,d)−=1, m(a,d)+=1, m(c,b)+=1.
      Exact: ΔcodimForm = 1 − m(a,b) − m(c,d)  (verified symbolic; CLEAN iff a<c≤b<d strictly).
  (B) CONCAT [a,b]+[b+1,d]→[a,d]: m(a,b)−=1, m(b+1,d)−=1, m(a,d)+=1.
      Exact: ΔcodimForm = 1 − (∑ of several source-region coeffs, all the involved m's), e.g.
      N=5 [1,1]+[2,4]: Δ = 1 − m(1,1) − m(1,2) − m(1,3) − m(2,2) − m(2,3) − m(2,4).
      Both moves: ΔcodimForm ≤ −1 when both sources present (≥1).  Moves must FORBID creating (0,N) (corner stays 0; codimForm-blind to it anyway).
- EXHAUSTIVENESS (verified exhaustive over ALL weakly-incr d, d0≥1, N≤4; 20942 KPs):
  every NON-HL corner-0 KP admits SOME strictly-decreasing valid corner-0 move (an A-strict-cross or a B-concat).
  CAVEAT (load-bearing): needs weakly-increasing AND d0≥1 — FALSE otherwise (an interior interval can be
  "walled" with no partner). The mechanism: an interior interval [a,b] (1≤a≤b≤N-1, m≥1) forces a partner
  because column a-1 is covered (d_{a-1} ≥ d_0 ≥ 1), but the partner can be on the LEFT (concat [a',a-1]+[a,b]
  or uncross [a',b']+[a,b] with a'<a≤b'<b) OR the RIGHT ([a,b]+[b+1,d'] concat, or [a,b]+[c,d'] uncross with
  a<c≤b<d'). It is NOT a single fixed constructive rule — the searcher tries all A/B configs.

THE PLAN (single-step contradiction, NOT a descent measure — a measure was FALSIFIED in prototyping):
1. Move-Δ lemmas (mechanical Finset.sum). 
2. Each move lands back in kostantPartitions d 0 (Kostant constraint preserved; corner stays 0).
3. Exhaustiveness: non-HL ⟹ ∃ valid corner-0 m' with codimForm m' < codimForm m.
4. minimiser ⟹ HL: if m minimises and is non-HL, (3) gives m' with smaller codimForm, contra inf'_le.
5. HL ⟹ ∃ e feasible, m = mOfE d e (surjectivity onto HL).  ⟹ codimForm m = Gqip d e ≥ qipMin.
6. So qipMin ≤ codimForm m for the minimiser m, i.e. qipMin ≤ cCodim. Combine with committed ≤ for `=`.

<output_contract>
1. SUB-STEP 5 (HL ⟹ mOfE-image): is the cleanest Lean route (a) a constructive inverse
   `eOfm m := fun i ↦ m(0, i)` (read e off the low-column multiplicities) + prove `mOfE d (eOfm m) = m`
   for HL m by the Kostant constraints, or (b) a Finset bijection / image argument? Give the exact
   read-off formula for e_i from an HL KP m, and the key Kostant identities that force `mOfE d (eOfm m)=m`.
   Name the single hardest obstruction.
2. SUB-STEP 3 (exhaustiveness): I must prove `∃ move`. The partner is not a single fixed rule. Propose the
   cleanest case split that COVERS every non-HL m and in each branch exhibits ONE concrete decreasing move.
   Candidate split: pick the interior interval [a,b] with a minimal (then b minimal). Column a-1 is covered:
   ∃ interval [a',b'] with a'≤a-1≤b', m(a',b')≥1. Sub-case on b' vs b (b'<b ⟹ uncross [a',b']+[a,b];
   b'≥b ⟹ ? ; b'=a-1 ⟹ concat). Does picking a minimal kill the b'≥b nested case (would [a',b'] itself be
   a smaller interior interval, or touch an endpoint)? Work out the FULL branch logic so every non-HL m is
   covered, and tell me which branch is the genuine hard one.
3. Is `Function.update` (twice/thrice) the right encoding for the moves, or should I define the moved array
   by an explicit `fun p ↦ ...` piecewise? Which makes the Kostant-preservation + Δ-lemma cleanest?
4. Flag the SINGLE hardest Lean obstruction across (1)–(3), and estimate it as a line-count + sub-task list
   (NO wall-clock).
</output_contract>

<grounding_rules>
- Mark each Mathlib lemma name [SURE] (seen at v4.29) or [GUESS]. Don't invent lemmas.
- Distinguish THEOREM (cite the mechanism) from your INFERENCE. The orbit-closure proof ("add an edge back,
  contradict maximality") is exactly what I must AVOID — I need a form-level (codimForm) argument only.
- If you believe sub-step 3's exhaustiveness needs a genuinely global argument (not a local case split),
  say so plainly and propose the alternative (e.g. a potential/measure after all, or induction on N).
</grounding_rules>
