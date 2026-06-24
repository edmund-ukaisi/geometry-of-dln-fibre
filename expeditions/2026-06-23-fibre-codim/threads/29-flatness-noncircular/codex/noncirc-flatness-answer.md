   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019efa85-b170-77f1-ad26-84c8c558c385
--------
user
<task>
Adjudicate whether there is a NON-CIRCULAR route, in commutative-algebra / affine algebraic geometry, to the dimension identity

    dim Σ^r = δ + dim F          (*)

where, for a "deep linear network" / quiver product setup:
- d = (d_0, d_1, ..., d_N) a dimension vector, N >= 1, fixed field k alg-closed char 0.
- Rep_d = ∏_{i=1}^N Mat(d_i × d_{i-1}, k), with the multiplication map mult : Rep_d → Mat(d_N × d_0, k), (A_N,...,A_1) ↦ A_N···A_1.
- E = diag(I_r, 0), a fixed rank-r target. F = mult⁻¹(E) the fibre (REDUCIBLE in general).
- Mat^{=r} = {rank exactly r matrices}, a single GL_{d_N}×GL_{d_0}-orbit, dim δ = r(d_N + d_0 − r).
- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.

The goal (*) is equivalent to dim F = (card − C) − δ, i.e. codim_{Rep_d} F = C + δ.

THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:

  WALL 1 (reducedness circularity). Building a scheme isomorphism e : O(Σ^r ∩ chart) ≅ O(base ∩ chart) ⊗_k F_E (a product trivialization) is circular: such an iso would FORCE F_E reduced (since O(Σ^r) is reduced), and "F_E reduced" is itself the hard thing — so e cannot be a strategy to PROVE properties, it's equivalent to them.

  WALL 2 (product-trdeg absent). A "sweep" route dim Σ^r = dim(GL×GL · F) via an orbit-dimension count needs trdeg(O(H) ⊗_k O(F)) = trdeg O(H) + trdeg O(F) (product/tensor transcendence-degree additivity), which is absent from the formalisation library, and O(F) is not a domain (F reducible).

THE PROPOSED DODGE (assess it). On the pivot chart U = {top-left r×r minor of mult is invertible}, consider the comorphism of mult restricted to the chart:
    schurToSred : R := O(Mat^{≤r} ∩ U)  →  S := O(Σ^r ∩ U) = O(Σ̄^r ∩ U).
R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
IF schurToSred is FLAT, then it satisfies going-down, and the going-down height-additivity theorem (Matsumura 13.B / Stacks 00ON: for P lying over p, ht P = ht p + ht(P/pS)) gives, applied to a minimal prime P of the chart fibre over the closed point E's maximal ideal m_E ⊂ R:
    ht_S(P) = ht_R(m_E) + ht(P / m_E S) = (dim R) + 0 = δ,
since m_E is maximal in the regular base R (ht = dim R = δ) and P is minimal over m_E S (relative height 0). This yields codim_{Σ̄^r}(F) = δ, hence (with codim Σ̄^r = C, catenary) codim_{Rep_d} F = C + δ. NO RADICALITY of F_E is used (height is radical-insensitive); NO product-trdeg; NO scheme iso e.

So the WHOLE question reduces to: **is schurToSred FLAT, by a NON-CIRCULAR argument** — i.e. an argument that does NOT secretly assert the product decomposition e (Wall 1) and does NOT need product-trdeg (Wall 2)?

Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).

CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
</task>

<output_contract>
1. A VERDICT: does a non-circular route to (*) EXIST? (yes/no, and which of A/B/C/the-homogeneity-sidestep is the cleanest).
2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
4. If EVERY route re-hits Wall 1 (the iso e) or Wall 2 (product-trdeg) or needs a genuinely-absent theorem, say which and what the smallest missing piece is.
5. The single sharpest thing most likely to break the proposed flatness/height route.
</output_contract>

<grounding_rules>
- Reason as a commutative algebraist. Distinguish FACTS (theorems with names) from INFERENCES (your assessment).
- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.
</grounding_rules>

codex
I’ll treat this as a commutative algebra geometry question rather than a code change. I’m going to pin down which statements are genuine theorems and which would smuggle in the product decomposition or the desired dimension count.
codex
A key point is already emerging: the fibre over `E` is still the full fibre when we work on the rank chart, since `E` lies in that chart. So any argument that needs the chart fibre to be equidimensional is exposed directly to the known non-equidimensional examples.
exec
/bin/bash -lc 'rg --files' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
exec
/bin/bash -lc 'rg -n "Cohen|flat|equidim|Hochster|determinantal|quiver" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
 succeeded in 0ms:
noncirc-flatness-answer.md
noncirc-flatness-prompt.md

 succeeded in 0ms:
./noncirc-flatness-answer.md:5:workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
./noncirc-flatness-answer.md:20:where, for a "deep linear network" / quiver product setup:
./noncirc-flatness-answer.md:25:- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.
./noncirc-flatness-answer.md:29:THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:
./noncirc-flatness-answer.md:37:R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
./noncirc-flatness-answer.md:44:Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
./noncirc-flatness-answer.md:45:  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
./noncirc-flatness-answer.md:46:      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
./noncirc-flatness-answer.md:47:      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
./noncirc-flatness-answer.md:48:  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
./noncirc-flatness-answer.md:49:  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).
./noncirc-flatness-answer.md:51:CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
./noncirc-flatness-answer.md:56:2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
./noncirc-flatness-answer.md:57:3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
./noncirc-flatness-answer.md:59:5. The single sharpest thing most likely to break the proposed flatness/height route.
./noncirc-flatness-answer.md:64:- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
./noncirc-flatness-answer.md:65:- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
./noncirc-flatness-answer.md:66:- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
./noncirc-flatness-answer.md:67:- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.
./noncirc-flatness-answer.md:73:A key point is already emerging: the fibre over `E` is still the full fibre when we work on the rank chart, since `E` lies in that chart. So any argument that needs the chart fibre to be equidimensional is exposed directly to the known non-equidimensional examples.
./noncirc-flatness-prompt.md:6:where, for a "deep linear network" / quiver product setup:
./noncirc-flatness-prompt.md:11:- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.
./noncirc-flatness-prompt.md:15:THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:
./noncirc-flatness-prompt.md:23:R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
./noncirc-flatness-prompt.md:30:Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
./noncirc-flatness-prompt.md:31:  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
./noncirc-flatness-prompt.md:32:      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
./noncirc-flatness-prompt.md:33:      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
./noncirc-flatness-prompt.md:34:  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
./noncirc-flatness-prompt.md:35:  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).
./noncirc-flatness-prompt.md:37:CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
./noncirc-flatness-prompt.md:42:2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
./noncirc-flatness-prompt.md:43:3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
./noncirc-flatness-prompt.md:45:5. The single sharpest thing most likely to break the proposed flatness/height route.
./noncirc-flatness-prompt.md:50:- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
./noncirc-flatness-prompt.md:51:- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
./noncirc-flatness-prompt.md:52:- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
./noncirc-flatness-prompt.md:53:- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.

codex
I found a local `noncirc-flatness-answer.md`, but it appears to be just the prompt plus my running notes rather than an existing settled answer. I’ll continue from the algebra, not treat that file as authoritative.
exec
/bin/bash -lc "sed -n '1,220p' noncirc-flatness-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019efa85-b170-77f1-ad26-84c8c558c385
--------
user
<task>
Adjudicate whether there is a NON-CIRCULAR route, in commutative-algebra / affine algebraic geometry, to the dimension identity

    dim Σ^r = δ + dim F          (*)

where, for a "deep linear network" / quiver product setup:
- d = (d_0, d_1, ..., d_N) a dimension vector, N >= 1, fixed field k alg-closed char 0.
- Rep_d = ∏_{i=1}^N Mat(d_i × d_{i-1}, k), with the multiplication map mult : Rep_d → Mat(d_N × d_0, k), (A_N,...,A_1) ↦ A_N···A_1.
- E = diag(I_r, 0), a fixed rank-r target. F = mult⁻¹(E) the fibre (REDUCIBLE in general).
- Mat^{=r} = {rank exactly r matrices}, a single GL_{d_N}×GL_{d_0}-orbit, dim δ = r(d_N + d_0 − r).
- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.

The goal (*) is equivalent to dim F = (card − C) − δ, i.e. codim_{Rep_d} F = C + δ.

THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:

  WALL 1 (reducedness circularity). Building a scheme isomorphism e : O(Σ^r ∩ chart) ≅ O(base ∩ chart) ⊗_k F_E (a product trivialization) is circular: such an iso would FORCE F_E reduced (since O(Σ^r) is reduced), and "F_E reduced" is itself the hard thing — so e cannot be a strategy to PROVE properties, it's equivalent to them.

  WALL 2 (product-trdeg absent). A "sweep" route dim Σ^r = dim(GL×GL · F) via an orbit-dimension count needs trdeg(O(H) ⊗_k O(F)) = trdeg O(H) + trdeg O(F) (product/tensor transcendence-degree additivity), which is absent from the formalisation library, and O(F) is not a domain (F reducible).

THE PROPOSED DODGE (assess it). On the pivot chart U = {top-left r×r minor of mult is invertible}, consider the comorphism of mult restricted to the chart:
    schurToSred : R := O(Mat^{≤r} ∩ U)  →  S := O(Σ^r ∩ U) = O(Σ̄^r ∩ U).
R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
IF schurToSred is FLAT, then it satisfies going-down, and the going-down height-additivity theorem (Matsumura 13.B / Stacks 00ON: for P lying over p, ht P = ht p + ht(P/pS)) gives, applied to a minimal prime P of the chart fibre over the closed point E's maximal ideal m_E ⊂ R:
    ht_S(P) = ht_R(m_E) + ht(P / m_E S) = (dim R) + 0 = δ,
since m_E is maximal in the regular base R (ht = dim R = δ) and P is minimal over m_E S (relative height 0). This yields codim_{Σ̄^r}(F) = δ, hence (with codim Σ̄^r = C, catenary) codim_{Rep_d} F = C + δ. NO RADICALITY of F_E is used (height is radical-insensitive); NO product-trdeg; NO scheme iso e.

So the WHOLE question reduces to: **is schurToSred FLAT, by a NON-CIRCULAR argument** — i.e. an argument that does NOT secretly assert the product decomposition e (Wall 1) and does NOT need product-trdeg (Wall 2)?

Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).

CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
</task>

<output_contract>
1. A VERDICT: does a non-circular route to (*) EXIST? (yes/no, and which of A/B/C/the-homogeneity-sidestep is the cleanest).
2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
4. If EVERY route re-hits Wall 1 (the iso e) or Wall 2 (product-trdeg) or needs a genuinely-absent theorem, say which and what the smallest missing piece is.
5. The single sharpest thing most likely to break the proposed flatness/height route.
</output_contract>

<grounding_rules>
- Reason as a commutative algebraist. Distinguish FACTS (theorems with names) from INFERENCES (your assessment).
- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.
</grounding_rules>

codex
I’ll treat this as a commutative algebra geometry question rather than a code change. I’m going to pin down which statements are genuine theorems and which would smuggle in the product decomposition or the desired dimension count.
codex
A key point is already emerging: the fibre over `E` is still the full fibre when we work on the rank chart, since `E` lies in that chart. So any argument that needs the chart fibre to be equidimensional is exposed directly to the known non-equidimensional examples.
exec
/bin/bash -lc 'rg --files' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
exec
/bin/bash -lc 'rg -n "Cohen|flat|equidim|Hochster|determinantal|quiver" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
 succeeded in 0ms:
noncirc-flatness-answer.md
noncirc-flatness-prompt.md

 succeeded in 0ms:
./noncirc-flatness-answer.md:5:workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
./noncirc-flatness-answer.md:20:where, for a "deep linear network" / quiver product setup:
./noncirc-flatness-answer.md:25:- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.
./noncirc-flatness-answer.md:29:THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:
./noncirc-flatness-answer.md:37:R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
./noncirc-flatness-answer.md:44:Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
./noncirc-flatness-answer.md:45:  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
./noncirc-flatness-answer.md:46:      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
./noncirc-flatness-answer.md:47:      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
./noncirc-flatness-answer.md:48:  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
./noncirc-flatness-answer.md:49:  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).
./noncirc-flatness-answer.md:51:CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
./noncirc-flatness-answer.md:56:2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
./noncirc-flatness-answer.md:57:3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
./noncirc-flatness-answer.md:59:5. The single sharpest thing most likely to break the proposed flatness/height route.
./noncirc-flatness-answer.md:64:- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
./noncirc-flatness-answer.md:65:- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
./noncirc-flatness-answer.md:66:- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
./noncirc-flatness-answer.md:67:- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.
./noncirc-flatness-answer.md:73:A key point is already emerging: the fibre over `E` is still the full fibre when we work on the rank chart, since `E` lies in that chart. So any argument that needs the chart fibre to be equidimensional is exposed directly to the known non-equidimensional examples.
./noncirc-flatness-prompt.md:6:where, for a "deep linear network" / quiver product setup:
./noncirc-flatness-prompt.md:11:- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.
./noncirc-flatness-prompt.md:15:THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:
./noncirc-flatness-prompt.md:23:R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
./noncirc-flatness-prompt.md:30:Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
./noncirc-flatness-prompt.md:31:  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
./noncirc-flatness-prompt.md:32:      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
./noncirc-flatness-prompt.md:33:      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
./noncirc-flatness-prompt.md:34:  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
./noncirc-flatness-prompt.md:35:  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).
./noncirc-flatness-prompt.md:37:CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
./noncirc-flatness-prompt.md:42:2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
./noncirc-flatness-prompt.md:43:3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
./noncirc-flatness-prompt.md:45:5. The single sharpest thing most likely to break the proposed flatness/height route.
./noncirc-flatness-prompt.md:50:- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
./noncirc-flatness-prompt.md:51:- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
./noncirc-flatness-prompt.md:52:- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
./noncirc-flatness-prompt.md:53:- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.

codex
I found a local `noncirc-flatness-answer.md`, but it appears to be just the prompt plus my running notes rather than an existing settled answer. I’ll continue from the algebra, not treat that file as authoritative.

exec
/bin/bash -lc "sed -n '1,140p' noncirc-flatness-prompt.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/29-flatness-noncircular/codex
 succeeded in 0ms:
<task>
Adjudicate whether there is a NON-CIRCULAR route, in commutative-algebra / affine algebraic geometry, to the dimension identity

    dim Σ^r = δ + dim F          (*)

where, for a "deep linear network" / quiver product setup:
- d = (d_0, d_1, ..., d_N) a dimension vector, N >= 1, fixed field k alg-closed char 0.
- Rep_d = ∏_{i=1}^N Mat(d_i × d_{i-1}, k), with the multiplication map mult : Rep_d → Mat(d_N × d_0, k), (A_N,...,A_1) ↦ A_N···A_1.
- E = diag(I_r, 0), a fixed rank-r target. F = mult⁻¹(E) the fibre (REDUCIBLE in general).
- Mat^{=r} = {rank exactly r matrices}, a single GL_{d_N}×GL_{d_0}-orbit, dim δ = r(d_N + d_0 − r).
- Σ^r = mult⁻¹(Mat^{=r}) (exact rank); Σ̄^r = mult⁻¹(Mat^{≤r}) its closure, dim = card − C where C = the quiver/Ext codimension (a known combinatorial number), card = dim Rep_d.

The goal (*) is equivalent to dim F = (card − C) − δ, i.e. codim_{Rep_d} F = C + δ.

THE CONSTRAINT THAT MATTERS. Prior attempts in a Lean formalisation hit two distinct circularities/walls and I need you to assess whether a flatness/height-additivity route DODGES them, because DIMENSION/HEIGHT IS RADICAL-INSENSITIVE:

  WALL 1 (reducedness circularity). Building a scheme isomorphism e : O(Σ^r ∩ chart) ≅ O(base ∩ chart) ⊗_k F_E (a product trivialization) is circular: such an iso would FORCE F_E reduced (since O(Σ^r) is reduced), and "F_E reduced" is itself the hard thing — so e cannot be a strategy to PROVE properties, it's equivalent to them.

  WALL 2 (product-trdeg absent). A "sweep" route dim Σ^r = dim(GL×GL · F) via an orbit-dimension count needs trdeg(O(H) ⊗_k O(F)) = trdeg O(H) + trdeg O(F) (product/tensor transcendence-degree additivity), which is absent from the formalisation library, and O(F) is not a domain (F reducible).

THE PROPOSED DODGE (assess it). On the pivot chart U = {top-left r×r minor of mult is invertible}, consider the comorphism of mult restricted to the chart:
    schurToSred : R := O(Mat^{≤r} ∩ U)  →  S := O(Σ^r ∩ U) = O(Σ̄^r ∩ U).
R is REGULAR (a localized polynomial ring in the Schur coordinates, dim δ). S is reduced, dim = card − C, equidimensional? (unknown — assess). 
IF schurToSred is FLAT, then it satisfies going-down, and the going-down height-additivity theorem (Matsumura 13.B / Stacks 00ON: for P lying over p, ht P = ht p + ht(P/pS)) gives, applied to a minimal prime P of the chart fibre over the closed point E's maximal ideal m_E ⊂ R:
    ht_S(P) = ht_R(m_E) + ht(P / m_E S) = (dim R) + 0 = δ,
since m_E is maximal in the regular base R (ht = dim R = δ) and P is minimal over m_E S (relative height 0). This yields codim_{Σ̄^r}(F) = δ, hence (with codim Σ̄^r = C, catenary) codim_{Rep_d} F = C + δ. NO RADICALITY of F_E is used (height is radical-insensitive); NO product-trdeg; NO scheme iso e.

So the WHOLE question reduces to: **is schurToSred FLAT, by a NON-CIRCULAR argument** — i.e. an argument that does NOT secretly assert the product decomposition e (Wall 1) and does NOT need product-trdeg (Wall 2)?

Candidate non-circular flatness arguments to evaluate, RANKED, for buildability in a Lean+Mathlib-style affine-AG library:
  (A) MIRACLE / LOCAL FLATNESS CRITERION: R regular + S Cohen-Macaulay + all fibres equidimensional of dim = dim S − dim R ⟹ S flat over R. 
      Sub-question A1: is "all chart fibres equidimensional of constant dim δ-codim" CIRCULAR here (it IS basically the conclusion dim F = ...)? Or is it independently obtainable (e.g. from GL_{d_N}×GL_{d_0}-homogeneity: all rank-r fibres are isomorphic as schemes, hence literally constant fibre dimension — is THAT non-circular and does it suffice for miracle flatness which needs the value, not just constancy)?
      Sub-question A2: is S Cohen-Macaulay (the total exact-rank chart ring of a quiver product locus)? Is THAT provable non-circularly / known (determinantal-variety CM theory, Hochster–Eagon)?
  (B) DIRECT free resolution / explicit presentation: present S = R[Ã]/(mult(Ã) − E_univ) on the chart (endpoint-normalized: the relation ideal becomes the constant fibre equations independent of the base), and show the relation generators form an R-REGULAR SEQUENCE (relative complete intersection over R) ⟹ S flat over R (a relative CI / Koszul-flat argument, NO equidim-fibre hypothesis). Does the endpoint-normalized relation ideal (mult(Ã)=E) form a regular sequence over R? (mult(Ã)−E has d_N·d_0 entries; the fibre has codim... assess whether it's a genuine regular sequence or has excess/syzygies.)
  (C) Any OTHER non-circular route to (*) you see (e.g. generic flatness / Grothendieck — but that gives flatness only on a dense open of the BASE, which may miss the closed point E; assess whether the closed-vs-generic-fibre gap can be closed by homogeneity WITHOUT flatness at the closed point).

CLOSED-VS-GENERIC FIBRE SUBTLETY (assess explicitly). Going-down/height-additivity at the closed point E needs flatness AT E (or at the relevant minimal prime over m_E S). Generic flatness only gives a dense-open-in-base locus. The homogeneity (all rank-r fibres isomorphic) transports the fibre dimension to E. Does that transport close the gap WITHOUT establishing flatness at the closed point — i.e. can one prove dim F_E = δ-codim purely by "F_E ≅ F_{generic}" + "generic fibre has dim δ-codim by generic flatness over the base", entirely SIDESTEPPING flatness at E and the going-down lemma? If so, that may be the cleanest non-circular route of all.
</task>

<output_contract>
1. A VERDICT: does a non-circular route to (*) EXIST? (yes/no, and which of A/B/C/the-homogeneity-sidestep is the cleanest).
2. For each of A, B, C, and the homogeneity-sidestep: is it non-circular (dodges Walls 1 and 2)? Where exactly does each one bite or fail? Be specific about whether "equidim fibres" (A1) and "CM" (A2) are circular or independently available.
3. If a non-circular route exists, name the precise theorems it rests on (miracle flatness, Hochster-Eagon CM of determinantal/quiver loci, relative regular sequence, generic flatness + homogeneity transport) and flag which are standard vs which would be a from-scratch build.
4. If EVERY route re-hits Wall 1 (the iso e) or Wall 2 (product-trdeg) or needs a genuinely-absent theorem, say which and what the smallest missing piece is.
5. The single sharpest thing most likely to break the proposed flatness/height route.
</output_contract>

<grounding_rules>
- Reason as a commutative algebraist. Distinguish FACTS (theorems with names) from INFERENCES (your assessment).
- The fibre F is reducible with components of DIFFERENT dimension (e.g. (3,3,3) r=1: dims 10,9,9). The exact-rank CHART restricts to where the product has rank EXACTLY r; assess whether the chart fibre is irreducible/equidimensional even when the full fibre is not.
- mult is NOT globally flat (fibre dim jumps as rank drops). Flatness is claimed only on the exact-rank chart. Do not conflate.
- The going-down height-additivity theorem ht P = ht p + ht(P/pS) (Stacks 00ON) and "flat ⟹ going-down" (Stacks 00HV) ARE available. Miracle flatness, Hochster-Eagon CM, generic flatness — assess availability/cost.
- Be decisive. If flatness at the closed point E is the genuine wall and is circular, say so plainly.
</grounding_rules>

web search: 
web search: Stacks Project generic flatness tag finite type algebra flat over dense open
web search: 
web search: https://stacks.math.columbia.edu/tag/00ON
web search: 
web search: https://stacks.math.columbia.edu/tag/00HT
web search: 
web search: '10.39.19' in https://stacks.math.columbia.edu/tag/00ON
web search: 
web search: https://stacks.math.columbia.edu/tag/00I1
web search: 
web search: Stacks Project dimension of fibres flat morphism finite type irreducible dimension formula generic fibre dim X dim Y
web search: 
web search: site:stacks.math.columbia.edu/tag dimension fibres morphism finite type irreducible generic fibre dimension
web search: 
web search: Stacks Project Morphisms dimension of fibres theorem tag
web search: 
web search: https://stacks.math.columbia.edu/tag/02G4
web search: 
web search: quiver determinantal varieties Cohen-Macaulay Lakshmibai Magyar
web search: 
web search: Zelevinsky map quiver orbit closures Cohen-Macaulay normal type A
codex
**Verdict**

Yes, a non-circular route to `dim Σ^r = δ + dim F` exists. The cleanest is the **generic-flatness + homogeneity sidestep**, not the proposed miracle-flatness or regular-sequence proof of flatness at `E`.

Use `X = (Σ^r)_red`, `Y = Mat^{=r}` or the pivot chart. The endpoint `GL_{d_N} × GL_{d_0}` action is transitive on `Y` and sends fibres isomorphically to fibres, so all closed rank-`r` fibres have the same dimension. Apply generic flatness on a dense open of `Y`, choose a closed `k`-point in that open, compute its fibre dimension as `dim X - dim Y`, then transport that dimension to `E` by homogeneity. This proves
`dim F = (card - C) - δ`
without flatness at `E`, without product-trdeg, and without an unreduced product trivialization. Generic flatness is standard; Stacks gives the dense flat open, and the flat fibre dimension equality is the usual dimension formula. ([stacks.math.columbia.edu](https://stacks.math.columbia.edu/tag/052B))

**A. Miracle Flatness**

This is not the clean route.

A1: “All chart fibres are equidimensional of expected dimension” is the wrong hypothesis here. The chart fibre over `E` is the full fibre `F`, because `E` has the pivot minor invertible. In examples like `(3,3,3), r=1`, `F` has components of dimensions `10,9,9`, so the chart fibre is not equidimensional. If “equidimensional” is weakened to “same maximum dimension”, homogeneity gives constancy non-circularly, but not the expected value; that value is essentially the target identity unless supplied by the generic-flatness sidestep.

A2: CM is independent in principle, but not cheaply available here. Ordinary determinantal CM does not automatically apply to the pullback under the product map. Type-A quiver orbit closures/quiver loci have standard CM results via Zelevinsky/Lakshmibai-Magyar/Kinser-Rajchgot, but invoking the right theorem for this exact union/chart is a serious imported result, not a small Hochster-Eagon lemma. ([arxiv.org](https://arxiv.org/abs/1307.6261?utm_source=openai)) Also, miracle flatness still requires the local dimension equality; Stacks’ local miracle flatness hypothesis is exactly `dim S = dim R + dim(S/mS)`. ([stacks.math.columbia.edu](https://stacks.math.columbia.edu/tag/00R4))

**B. Regular Sequence / Relative CI**

This fails generally. The entries of `mult(A)-E` do not form a regular sequence in the fibre algebra. There are `d_N d_0` equations, but the actual top codimension of `F` can be smaller; in `(3,3,3), r=1`, there are `9` endpoint equations while the top fibre component has codimension `18-10=8`. Different-dimensional components also rule out the ideal being a clean complete intersection/unmixed regular-sequence quotient.

Endpoint normalization does give a base-independent ideal, but that is not the same as a regular sequence.

**C. Other Route / Generic Flatness**

Generic flatness alone does not prove flatness at `E`, so it cannot justify going-down at `m_E`. Flatness at the closed point remains a genuine extra statement. But homogeneity closes the gap for **dimension**: choose a closed point `y` in the dense flat open, compute `dim X_y`, then use the fibre isomorphism `X_y ≅ X_E`.

Do not formulate this as literally `F_E ≅ F_generic`; the generic fibre lives over `k(Y)`. The safer formal route is through a closed `k`-point in the generic-flatness open.

**About `schurToSred` Flatness**

If you allow reductions, there is a likely direct flatness proof by **reduced endpoint normalization**:
`T_chart ≅ R ⊗_k T_E` for the unreduced fibre product, hence after reduction
`S ≅ R ⊗_k (T_E)_red`
because `R` is smooth/geometrically reduced over `k` in char `0`. Then `S` is flat over `R`. This dodges reducedness circularity only if the fibre factor is explicitly `(F_E)_red`, not `F_E`. If your rule forbids any product decomposition, then A and B do not replace it.

**Smallest Missing Formal Piece**

For the homogeneity sidestep: generic flatness/generic freeness plus the flat fibre dimension formula for finite-type affine schemes. That is standard mathematics, but likely a from-scratch Lean build.

For the flatness route: the smallest viable piece is not miracle flatness; it is the reduced endpoint-normalization lemma plus `R ⊗_k A` flat over `R`.

**Sharpest Break**

The sharpest break in the proposed flatness/height route is the non-equidimensional closed chart fibre. Since the fibre over `E` is exactly `F`, any proof depending on equidimensional fibres or a regular sequence is exposed immediately by examples like `(3,3,3), r=1`. Generic flatness plus homogeneity proves the dimension identity, but it does not prove flatness at `E` or justify going-down there.
tokens used
98,744
**Verdict**

Yes, a non-circular route to `dim Σ^r = δ + dim F` exists. The cleanest is the **generic-flatness + homogeneity sidestep**, not the proposed miracle-flatness or regular-sequence proof of flatness at `E`.

Use `X = (Σ^r)_red`, `Y = Mat^{=r}` or the pivot chart. The endpoint `GL_{d_N} × GL_{d_0}` action is transitive on `Y` and sends fibres isomorphically to fibres, so all closed rank-`r` fibres have the same dimension. Apply generic flatness on a dense open of `Y`, choose a closed `k`-point in that open, compute its fibre dimension as `dim X - dim Y`, then transport that dimension to `E` by homogeneity. This proves
`dim F = (card - C) - δ`
without flatness at `E`, without product-trdeg, and without an unreduced product trivialization. Generic flatness is standard; Stacks gives the dense flat open, and the flat fibre dimension equality is the usual dimension formula. ([stacks.math.columbia.edu](https://stacks.math.columbia.edu/tag/052B))

**A. Miracle Flatness**

This is not the clean route.

A1: “All chart fibres are equidimensional of expected dimension” is the wrong hypothesis here. The chart fibre over `E` is the full fibre `F`, because `E` has the pivot minor invertible. In examples like `(3,3,3), r=1`, `F` has components of dimensions `10,9,9`, so the chart fibre is not equidimensional. If “equidimensional” is weakened to “same maximum dimension”, homogeneity gives constancy non-circularly, but not the expected value; that value is essentially the target identity unless supplied by the generic-flatness sidestep.

A2: CM is independent in principle, but not cheaply available here. Ordinary determinantal CM does not automatically apply to the pullback under the product map. Type-A quiver orbit closures/quiver loci have standard CM results via Zelevinsky/Lakshmibai-Magyar/Kinser-Rajchgot, but invoking the right theorem for this exact union/chart is a serious imported result, not a small Hochster-Eagon lemma. ([arxiv.org](https://arxiv.org/abs/1307.6261?utm_source=openai)) Also, miracle flatness still requires the local dimension equality; Stacks’ local miracle flatness hypothesis is exactly `dim S = dim R + dim(S/mS)`. ([stacks.math.columbia.edu](https://stacks.math.columbia.edu/tag/00R4))

**B. Regular Sequence / Relative CI**

This fails generally. The entries of `mult(A)-E` do not form a regular sequence in the fibre algebra. There are `d_N d_0` equations, but the actual top codimension of `F` can be smaller; in `(3,3,3), r=1`, there are `9` endpoint equations while the top fibre component has codimension `18-10=8`. Different-dimensional components also rule out the ideal being a clean complete intersection/unmixed regular-sequence quotient.

Endpoint normalization does give a base-independent ideal, but that is not the same as a regular sequence.

**C. Other Route / Generic Flatness**

Generic flatness alone does not prove flatness at `E`, so it cannot justify going-down at `m_E`. Flatness at the closed point remains a genuine extra statement. But homogeneity closes the gap for **dimension**: choose a closed point `y` in the dense flat open, compute `dim X_y`, then use the fibre isomorphism `X_y ≅ X_E`.

Do not formulate this as literally `F_E ≅ F_generic`; the generic fibre lives over `k(Y)`. The safer formal route is through a closed `k`-point in the generic-flatness open.

**About `schurToSred` Flatness**

If you allow reductions, there is a likely direct flatness proof by **reduced endpoint normalization**:
`T_chart ≅ R ⊗_k T_E` for the unreduced fibre product, hence after reduction
`S ≅ R ⊗_k (T_E)_red`
because `R` is smooth/geometrically reduced over `k` in char `0`. Then `S` is flat over `R`. This dodges reducedness circularity only if the fibre factor is explicitly `(F_E)_red`, not `F_E`. If your rule forbids any product decomposition, then A and B do not replace it.

**Smallest Missing Formal Piece**

For the homogeneity sidestep: generic flatness/generic freeness plus the flat fibre dimension formula for finite-type affine schemes. That is standard mathematics, but likely a from-scratch Lean build.

For the flatness route: the smallest viable piece is not miracle flatness; it is the reduced endpoint-normalization lemma plus `R ⊗_k A` flat over `R`.

**Sharpest Break**

The sharpest break in the proposed flatness/height route is the non-equidimensional closed chart fibre. Since the fibre over `E` is exactly `F`, any proof depending on equidimensional fibres or a regular sequence is exposed immediately by examples like `(3,3,3), r=1`. Generic flatness plus homogeneity proves the dimension identity, but it does not prove flatness at `E` or justify going-down there.
