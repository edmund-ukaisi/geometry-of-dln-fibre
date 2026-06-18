# Thread 02 — Ext-design certificate (recon-ext-design, pen-and-paper)

No Lean. Exact algebra (sympy / integer arithmetic). Decorrelated Codex consult (xhigh, hypothesis withheld) independently reproduced every formula and tripwire — artefacts in codex/standardness-{prompt,answer}.md. Reconciles with recon-mathlib's Ringel-cokernel route. (Recorded by the controller; the harness blocks subagent Write to report files.)

**Convention.** M_{ij} = interval module on [i,j] ⊆ {0,…,N}, 0≤i≤j≤N, identity arrows inside (= Core.intervalModule i j). Distinct from the rank-pattern containment indicator 1[i≤i' ∧ j'≤j] in IntervalModule.lean — a third indicator; keep all three apart.

## 1. Ext / Hom interval indicators
Indecomposable projective P_p = M_{p,N} (tail). With P_{N+1}:=0, resolution: 0 → P_{j+1} → P_i → M_{ij} → 0. kQ hereditary (gl.dim ≤ 1). Applying Hom(−,M_{uv}) with Hom(P_p,X)=X_p:
- dim Ext¹(M_{ij},M_{uv}) = 1 iff i+1≤u≤j+1≤v, else 0 (vacuous at j=N). — paper eqn 3.4
- dim Hom(M_{ij},M_{uv}) = 1 iff u≤i≤v≤j, else 0. (NOT containment.)
Derived two ways (resolution; Codex deformation complex); checked all interval pairs N≤4.

## 2. The Cor 3.5 match (substitution)
Ext biadditive: dim Ext¹(M,M) = Σ_{(i,j),(u,v)} m_{ij} m_{uv}·1[i+1≤u≤j+1≤v]. Set source interval = (i−1,j−1), target = (u,v); the Ext constraint becomes i≤u≤j≤v, giving
dim Ext¹(M,M) = Σ_{1≤i≤u≤j≤v≤N} m_{(i-1)(j-1)} m_{uv} — Cor 3.5 verbatim.
Bijection of index sets; symbolic polynomial identity verified N=1..4 (simplify(lhs−rhs)=0).

## 3. Euler form and Hom route
⟨a,b⟩ = Σ_{t=0}^{N} a_t b_t − Σ_{t=0}^{N-1} a_t b_{t+1}  (arrow term a_t b_{t+1}, orientation-sensitive).
Hereditary: dim Hom − dim Ext¹ = ⟨dim,dim⟩. So dim Ext¹(M,M) = dim Hom(M,M) − ⟨d,d⟩; ⟨d,d⟩ depends only on ambient d (constant across orbits of that d). Recommend formalising codim via the direct Ext sum (§2, one indicator); keep Hom−Euler as the Phase-B bridge.

## 4. (2,2,2) sympy table — six Σ⁰ orbits, three concurring routes
d=(2,2,2), N=2, m_02=0. ⟨d,d⟩=4, dim Rep=8, dim G=12.

| (r01,r12) | normal form | Ext(M,M) | Cor3.5 | Hom−⟨d,d⟩ | dim O |
|:---:|:---|:---:|:---:|:---:|:---:|
| (0,0) | M00²⊕M11²⊕M22² | 8 | 8 | 8 | 0 |
| (0,1) | M00²⊕M11⊕M12⊕M22 | 5 | 5 | 5 | 3 |
| (0,2) A=0 | M00²⊕M12² | 4 | 4 | 4 | 4 |
| (1,0) | M00⊕M01⊕M11⊕M22² | 5 | 5 | 5 | 3 |
| (1,1) | M00⊕M01⊕M12⊕M22 | 3 | 3 | 3 | 5 |
| (2,0) B=0 | M01²⊕M22² | 4 | 4 | 4 | 4 |

(1,1) (im A=ker B) → codim 3; {A=0}=(0,2), {B=0}=(2,0) → codim 4. Three maximal corners (1,1),(0,2),(2,0) are the components; C=3, θ=1. Origin (0,0): dim O=0, codim 8 = dim Rep.

## 5. Phase-B Voigt requirement list
Target codim_Rep O_M = dim Ext¹(M,M). Deformation-complex chain (Codex-confirmed):
1. Rep = ∏_t Hom_k(V_t,V_{t+1}) smooth ⇒ T_M Rep = C¹(M,M) = ∏_t Hom_k(M_t,M_{t+1}).
2. G=∏_i GL(V_i), (g·M)_t = g_{t+1}M_t g_t^{-1}; Lie alg C⁰(M,M)=∏_i End_k(M_i).
3. δ_M:C⁰→C¹, (ξ_i)↦(ξ_{t+1}M_t − M_t ξ_t)_t; im δ_M = B¹ = T_M(G·M).
4. Orbit smooth: dim O = dim B¹ = dim G − dim Stab; Stab=Aut_{kQ}(M) open in End_{kQ}(M) ⇒ dim Stab = dim End(M) = dim Hom(M,M).
5. No relations ⇒ Z¹=C¹ (load-bearing hereditary fact); Ext¹(M,M) ≅ C¹/im δ_M = Z¹/B¹. (Bound quiver: Z¹⊊C¹, diverges.)
6. codim O = dim C¹ − dim im δ_M = dim Ext¹(M,M).
Glue: ⟨d,d⟩ = dim G − dim Rep, so codim O = dim Rep − dim G + dim Hom = dim Hom − ⟨d,d⟩ = dim Ext¹. The Hom−Euler identity IS the Voigt computation. Two Lean routes: (a) deformation complex (1–6); (b) shorter dim O = dim G − dim Aut(M) + hereditary identity (needs only dim End(M) and ⟨d,d⟩, Phase-A objects — likely the realistic path). Subtleties: needs Rep smooth + Stab open in End; state AG facts over k̄ (codim base-change-invariant); no non-reducedness issue.

## 6. Standardness verdict — textbook
Codex-confirmed (same resolution, indicators, Euler form, Voigt chain from scratch). Refs: ASS, Gabriel–Roiter, Crawley-Boevey (Ext); Ringel, ASS (Euler identity); standard module-variety geometry (Voigt). Paper cites FRduke Lemma 4.4. No bespoke construction. Cited analytic rlct ≤ ½·codim (Aoyagi/Watanabe) out of scope.
Tripwires: (1) Hom 1[u≤i≤v≤j] ≠ containment ≠ rank-pattern; (2) Ext shift j+1, vacuous at j=N; (3) Euler term a_t b_{t+1}; (4) codim=dim Ext rests on Rep-smooth + Z¹=C¹; (5) tail convention P_p=M_{p,N} matches intervalModule.

## Close
Firmest: Ext indicator (two derivations); exact Cor-3.5 reindex (symbolic N≤4, bijective); (2,2,2) table (C=3,θ=1). Most likely to break it: index/convention swap (Hom vs Ext vs rank-pattern), or j+1=N+1 boundary. Next: Voigt step-4 Mathlib coverage, else route (b).
Artefacts: codex/standardness-{prompt,answer}.md; scripts /tmp/ext_*.py, /tmp/hom_route.py, /tmp/voigt_dim.py.
