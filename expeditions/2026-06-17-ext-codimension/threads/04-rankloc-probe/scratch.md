# Thread 04 — rankloc-probe scratch (exact sympy, Rep_(2,2,2))

CAS available: sympy 1.14 only (no Sage/M2/Singular). Krull dim computed via maximal-independent-set
on the grevlex Gröbner leading-term ideal (`/tmp/dim_util.py`, sanity-checked on xy, (x,y), x in k^3).

## Ambient
Rep_(2,2,2): quiver 2 ->A 2 ->B 2, tuple (A,B), 8 coords. submult over [0,2] = B·A = mult.
rankPattern: r01=rank A, r12=rank B, r02=rank(BA).

## Ideal-height table (EXACT)
| locus | rank pattern | generators | dim V | codim | dim Ext¹ (predicted) |
|---|---|---|---|---|---|
| (1,1) orbit closure | r01=1,r12=1,r02=0 | detA, detB, 4 entries of BA | 5 | **3** | 3 ✓ |
| {A=0} | r01=0,r12=2,r02=0 | a11,a12,a21,a22 | 4 | **4** | 4 ✓ |
| {B=0} | r01=2,r12=0,r02=0 | b11,b12,b21,b22 | 4 | **4** | 4 ✓ |
| origin | all 0 | all 8 vars | 0 | **8** | 8 ✓ |

All match dim Ext¹ and the synthesis dim-O column (dim O_(1,1)=5, origin dim O=0).

Cross-checks (other dimension vectors), codim = dim Ext¹ holds:
- N=1 d=(2,2): {rank A ≤ 1} codim 1 (generic determinantal (2-1)²=1).
- N=2 d=(1,2,1): {BA=0} = {b1a1+b2a2=0} codim 1 = dim Ext¹(M01⊕M12). Clean hypersurface (a CI here).

## Structural findings (the crux for the Lean verdict)

1. **NOT a complete intersection.** (1,1) ideal: 6 generators, codim 3.

2. **Excess intersection — codim is NOT a sum of independent determinantal heights.**
   If the three rank conditions were independent: rank A≤1 → codim 1, rank B≤1 → codim 1,
   rank(BA)≤0 (generic 2×2 = 0) → codim (2-0)(2-0)=4. Sum = 6 ≠ actual 3.
   The reason: BA is a *product* of two matrices, not a generic matrix; its entries are dependent.
   {BA=0} ALONE has codim **3**, not 4 (the product-zero / zero-composite locus).
   Adding detA=0, detB=0 does NOT raise codim past 3 (they isolate the right component of {BA=0}).

3. **{BA=0} is REDUCIBLE** (codim 3): top component = the (1,1) orbit closure (codim 3);
   plus {A=0} and {B=0} (codim 4) as separate components (A or B full rank → not in (1,1) closure).
   So the orbit-closure ideal genuinely needs detA, detB AND the BA entries to single out Ō_M.

4. **NOT a set-theoretic complete intersection on the natural generators.** Rabinowitsch radical-
   membership test: for EVERY codim-3 triple of the 6 generators, at least one other generator is
   NOT in the triple's radical → V(triple) ⊋ V(I_11). No length-3 regular sequence among the
   generators cuts out Ō_M even set-theoretically. ⇒ The "regular sequence ⟹ height = #gens" shortcut
   is unavailable; codim 3 < (essential equation count).

5. **Irreducible, generically smooth/reduced of codim 3.** Rational parametrization A=uαᵀ, B=wβᵀ
   with β⊥u (so BA=0) covers a dense dim-5 piece; Jacobian of the 6 gens has rank 3 at generic points
   → smooth (hence reduced) there, codim 3. Image of irreducible param space, dim 5 = dim V, no larger
   component ⇒ V irreducible = the orbit closure. Full radicality of the ideal = Bobinski–Zwara
   normality/CM for type-A quiver loci (asserted, not CAS-proved).

## Verdict (pre-Codex)
The codim IS a genuine, exact, classical-CA-computable invariant (Krull dim of an explicit ideal),
BUT it is NOT the easy regular-sequence/Eagon–Northcott height. It is a quiver rank locus (product-zero
+ rank): excess intersection, non-CI, codim = Krull-dim drop of a determinantal-type ideal. Certifying
it in Lean needs the catenary equality `dim R/I = n − height I` + quiver-locus codim/CM theory (absent
in Mathlib), NOT just Krull's height theorem.

## Codex consult (xhigh, decorrelated) — corroborates + names the theory

Codex (codex/rankloc-{prompt,answer}.md) independently re-derived `{BA=0} → codim 3 not 4` (same
number, called it "my calculation, not a cited theorem") and resolved the standard theory:

- **(1) orbit closure = rank locus, IDEAL-level:** theorem in equioriented type A. Set equality AND
  the product-minor ideal is **prime, radical, reduced, normal, Cohen–Macaulay** (Lakshmibai–Magyar
  Thm 2.2; Knutson–Miller–Shimozono Thm 1.14 via Zelevinsky map; degeneration order Abeasis–Del Fra
  1985). Over arbitrary field / char (KMS schemes over ℤ). My CAS smoothness check (generically
  reduced) is the local shadow of this.
- **(2) codimension = Buch–Fulton / KMS rectangle sum:**
  `codim Ō_r = Σ_{0≤i<j≤N} (r_{i,j-1} − r_{ij})(r_{i+1,j} − r_{ij})`  (KMS Cor 1.16).
  VERIFIED against my sympy ideal heights: (1,1)→3, {A=0}→4, origin→8. All match. **NOT** a sum of
  independent determinantal heights; the conditions are highly dependent (excess intersection), as my
  regular-sequence test already showed.
- **NOT a complete intersection** in general (Codex concurs); height = the rectangle sum, not #minors.
- **codim = dim Ext¹** is "usually proved by the orbit-dimension route" (dim O = dim GL_d − dim End M
  + hereditary Euler), which "genuinely uses algebraic-group/orbit-dimension ideas." The KMS/LM
  codimension proof is a SEPARATE Schubert/quiver-determinantal package; matching it to dim Ext¹ is a
  combinatorial homological comparison, "not a generic determinantal-height or regular-sequence proof."

### Lean-sizing verdict (Codex, concurring with my structural findings)
"A from-scratch Lean proof via determinantal CA is the **larger** build" — needs polynomial rings,
minors, determinantal/Schubert ideals, radical/prime/height, standard-monomial or Gröbner theory, AND
dimension–height infrastructure (catenary `dim R/I = n − ht I`) absent from Mathlib. "If the goal is a
Lean formalization, I would not start with quiver determinantal CA." The algebraic-group/orbit-dimension
route is "still substantial, but smaller and more self-contained" — mostly finite-dim linear algebra
(End, Ext¹ via the explicit complex = Phase A already done), rank-nullity, plus a comparatively small
affine orbit-dimension input.

## FINAL VERDICT
The rank-locus codimension IS a genuine, exact invariant (Krull codim of an explicit, prime,
Cohen–Macaulay determinantal ideal; = Buch–Fulton rectangle sum = dim Ext¹). It is NOT computable by the
cheap regular-sequence/Eagon–Northcott route — it is an excess/non-CI quiver-determinantal height. As a
Lean build it is LARGER than the algebraic-group orbit-dimension route, not smaller. The determinantal-CA
route does NOT shrink Layer 2; it relocates the ocean (from AG to Schubert/quiver determinantal CA +
catenary dimension theory). RECOMMENDATION: Layer 2 stays the algebraic-group orbit-dimension route
(route (b): dim O = dim G − dim Aut(M), reusing Phase-A δ); the rank-locus picture is best kept as the
single cleanest CITED bridge (engine-verifiable via RankPattern), not a from-scratch Proved shortcut.
