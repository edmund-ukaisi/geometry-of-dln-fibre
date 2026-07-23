# Corank-2 minimiser certificate — (3,3,4) t=(1,0), matrix-ideal Schur-clearing route

**Purpose.** Render contract for the Lean corank-2 **prototype** (the gate before the re-architect
swap). Turns pnp-ideal's structural inference ("no cofactor degeneration at corank≥2") into a
fully-run, exact witness on the *genuine corank-2 minimiser* — the width that broke Route A's cap.
Re-runnable: `python3 cert_334_corank2.py` (exit 0 iff every direction is exact; Gröbner-verified).

**Instance.** Reduced widths `M=(3,3,4)`, `L=2`: `C1=C^(1)` is 3×3, `C2=C^(2)` is 3×4, product
`P=C1·C2` is 3×4 (12 generators). Branch `t=(1,0)`: `Mval=(3−1)(3−1)+(1−0)(4−0)=8`, `rlct=4`. This is
the coupled-only minimiser (no clean/disjoint peel reaches it). Matches the banked
`theory/aoyagi-2023-reproduction/g-coupled-334-diagb.py`.

**Headline.** Every step is unipotent-**polynomial** with the pivot strict-transform ≡ 1 (a unit,
nonvanishing incl. at the exceptional origin). No `c11⁻¹`/unit inversion in the interior; the coupling
lives entirely in the residual **matrix** `Δ` (never a support predicate). Both ideal directions hold
with **explicit polynomial cofactors**; `⟨P⟩=⟨peeled⟩` confirmed as an exact Gröbner ideal-equality.

---

## The six render-contract items (all PASS, exact)

### [g] blow-up chart map (fixed-ambient)
`g : ℝ²¹ → ℝ²¹` stays fixed-ambient (`flatDim(3,3,4)=3·3+3·4=21`). The step map is
`σ = sh ∘ blockBlowupMap center pivot`: the pivot `c11` (the (0,0) entry of `C1`) is the exceptional
coordinate; the block-center is the corank-2 block; `sh` is the unipotent shear from `Q1,Q2`. Only the
**residual block** `Δ` (2×2, then shrinking) is carried as a dependent-dim matrix — see [ML].

### [QP] unipotent-polynomial Schur cofactors (pivot normalized to 1)
```
Q1 = [[1,0,0],[-c21a,1,0],[-c21b,0,1]]      Q2 = [[1,-c12a,-c12b],[0,1,0],[0,0,1]]
Q1⁻¹=[[1,0,0],[ c21a,1,0],[ c21b,0,1]]      Q2⁻¹=[[1, c12a, c12b],[0,1,0],[0,0,1]]
```
`det Q1 = det Q2 = 1`; all four matrices polynomial. `Q1·C1·Q2 = diag(1, Δ)`,
`Δ = C22 − C21·C12` (the **coupled** Schur complement, 2×2):
`Δ = [[m11−c12a·c21a, m12−c12b·c21a],[m21−c12a·c21b, m22−c12b·c21b]]`.
Reconstruction `Q1⁻¹·diag(1,Δ)·Q2⁻¹ = C1` holds exactly.

### [D] diag(b) + residual matrix after the step
Blow up the coupled `Δ`-block: `Δ∘blowup = u·Dstrict`, `Dstrict=[[1,d01],[d10,d11]]` (pivot ≡ 1,
nonvanishing incl. `u=0`); exceptional order **exactly one** (`u | all entries`, `u² ∤ pivot`). Clear
with the unipotent-poly `R1,R2` ⇒ `diag(1, D_next)`, `D_next = d11 − d01·d10` (**polynomial**, the next
residual — feeds the next layer). Accumulated divisibility chain `b1 | b2 | b3` =
`(E, E·α·v, E·α·v·δ·w)`; terminal `⟨b1,b2,b3⟩ = ⟨b1⟩` principal, `loss = b1²·unit`, `unit(0)=1`;
join Jacobian `E⁷` ⇒ `rlct = (7+1)/(2·1) = 4 = Mval/2`.

### [I⇒] forward  ⟨P⟩ ⊆ ⟨peeled⟩  — explicit polynomial cofactors
`P = Q1⁻¹ · peeled` (entries of `Q1⁻¹` are the cofactors), where
`peeled = diag(1,Δ)·(Q2⁻¹·C2)`. Verified entrywise-exact.

### [I⇐] backward  ⟨peeled⟩ ⊆ ⟨P⟩  — explicit polynomial cofactors
`peeled = Q1 · P` (entries of `Q1` are the cofactors). Verified entrywise-exact.
Together: `⟨P⟩ = ⟨peeled⟩` — **also confirmed as an exact Gröbner ideal-equality** (grevlex), not just
coefficient matching. This is the literal both-ways `RegionRepresents` for the step, cofactors
polynomial (hence continuous on any nbhd — no unit degeneration).

### [ML] the multi-layer reassociation flag (the cast-tax to measure)
The load-bearing products are `peeled = diag(1,Δ)·(Q2⁻¹·C2)` and, one level down,
`D_next · C^(S+1)` — `Matrix.mul` on blocks whose widths `(M(S)−J)×(M^(S+1)−J)` **change per (S,J)**
(3×3→2×2→1×1→3×4→2×3→1×2). This is the documented dependent-dim HMul-synthesis / reassociation /
opaque-width pain (`lean/CLAUDE.md`). **Mitigation baked into the contract:** keep `g:ℝ²¹→ℝ²¹`
fixed-ambient; carry ONLY the residual block as the dependent-dim matrix; do `(A·B)·C = A·(B·C)` with a
fully-applied `Matrix.mul_assoc a b c` term (NOT `rw`/`simp`), per the banked `mul_three_reassoc`
idiom. **This is exactly the cast-tax the Lean prototype must measure** — the math is settled; the open
question is only the plumbing cost.

---

## Lean prototype contract (what the formaliser renders + measures)
For this one corank-2 step, produce — on the fixed ambient `ℝ²¹`, at the pivot chart / blow-up:
1. `g` (composed `sh ∘ blockBlowupMap`), analytic, `g 0 = 0`;
2. `Q1,Q2,Q1⁻¹,Q2⁻¹` (the matrices above) and `Q1·C1·Q2 = diag(1,Δ)` by `decide`/`Matrix.mul` over ℤ
   then cast (the `lean/CLAUDE.md` ℤ-matrix idiom);
3. both `RegionRepresents` directions using the explicit `Q1`/`Q1⁻¹` cofactors (target = `diag(b)`
   monomial family); the residual block `Δ`/`D_next` carried as a dependent-dim matrix;
4. **report the LoC + the number of dependent-dim cast/reassoc frictions hit** — that number is the
   decision datum for re-architect-vs-grind.

## What this does NOT yet cover (honest scope)
- The radial resolutions of `‖T‖²`, `‖ΔS‖²` and the JOIN (`q=E`, `u=E·α`) that carry `diag(b)` to the
  single terminal divisor are the R1 depth-recursion mechanism (banked exact at `L=3,4` incl. non-square
  inner widths, `verify-r1-shortcut`); they are route-independent (same for clean/coupled) and reused
  unchanged. This certificate isolates the **corank-2-specific** block-elim + coupled-Δ blow-up.
- The certificate is on the c11=1 normalized chart (pivot strict-transform ≡ 1). The equivalent
  pre-normalization `{c11 ≠ 0}` chart has cofactors with `c11⁻¹` (continuous, nonvanishing there) — the
  Lean prototype should use the normalized form (polynomial, cheapest).
