<task>
You are an expert Lean 4 + Mathlib (pin v4.29) formaliser. Close ONE isolated `sorry` with a concrete
tactic block. The goal is a finite-`Finset.sum` reindexing identity over a commutative field `K`
(`K = FractionRing (groupRing k d)`) acting on a `K`-Kähler-differential module `Ω = Ω[K⁄k]` (a
`K`-module). All `•` below are `K`-scalar multiplications on `Ω`. No inverse/collapse is needed for THIS
goal — it is a pure reindex + scalar-commute (this is the key difference from the proved mirror `hB`,
which DID collapse via an inverse identity).

== ABBREVIATIONS (to read the goal; these are the actual Lean names) ==
- `Dk x` := `KaehlerDifferential.D k (FractionRing (groupRing (k := k) d)) x`  (the universal
  k-derivation into Ω; it is `K`-linear-additive, NOT `K`-linear on scalars — it is a derivation).
  Its OUTPUT `Dk (...)` is an element of the `K`-module `Ω`.
- `V₂ := genUnitK M i.succ`            : `Matrix (Fin (d i.succ)) (Fin (d i.succ)) K`
- `J  := genUnitInvK M i.castSucc`     : `Matrix (Fin (d i.castSucc)) (Fin (d i.castSucc)) K`  (this is V₁⁻¹)
- `V₁ := genUnitK M i.castSucc`        : `Matrix (Fin (d i.castSucc)) (Fin (d i.castSucc)) K`
- `F  := genFactorK M i`               : `Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) K`
- `(V₂ * F)` is genuine `K`-matrix product; `(V₂ * F) s w = ∑ a, V₂ s a * F a w` by `Matrix.mul_apply`.

== THE GOAL (the `sorry` body of private theorem `D_orbit_conj_termA`) ==
With `M : Tuple (k := k) d`, `i : Fin N`, `s : Fin (d i.succ)`, `t : Fin (d i.castSucc)`:

    (∑ w, (genUnitK M i.succ * genFactorK M i) s w •
        (- ∑ c, ∑ e, (genUnitInvK M i.castSucc) w c • (genUnitInvK M i.castSucc) e t •
          Dk ((genUnitK M i.castSucc) c e)))
      = - ∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i a u) • mcΘ M i.castSucc u b)

where `(M i a u)` on the RHS is a `k`-scalar (element of `k`) acting on `Ω` via `algebraMap k K` (the
`•` there is the `k`-module structure on Ω, lifted from `K`); and

    mcΘ M (i.castSucc) u b  :=  ∑ c, (genUnitInvK M i.castSucc) u c • Dk ((genUnitK M i.castSucc) c b)

(definition `mcΘ M v p q := ∑ c, (genUnitInvK M v) p c • Dk ((genUnitK M v) c q)`).

== HAND-COMPUTED NORMAL FORM (both sides equal this, up to reindexing + collapsing nested `•`) ==
Expand `(V₂*F) s w = ∑ a, V₂ s a * F a w` and `F a w = M_{a w}` (lemma `genFactorK_apply` below). Then:

  LHS = - ∑ a, ∑ w, ∑ c, ∑ e,  (V₂ s a * F a w * J w c * J e t) • Dk (V₁ c e)
  RHS = - ∑ a, ∑ b, ∑ u, ∑ c,  (V₂ s a * J b t * (algebraMap k K (M_{a u})) * J u c) • Dk (V₁ c b)

These match under the relabel  RHS:(b ↦ e, u ↦ w)  and the commutativity of the `K`-ring product
(`F a w = algebraMap k K (M_{a w})`, so `F a w` and `algebraMap k K (M_{a u})` are the SAME object once
`u=w`). The four `•` collapse to a single `•` of the product scalar via `smul_smul` / `mul_smul`.
There is NO sum-collapse: M is not invertible, `∑_u M_{a u} J u c` stays as-is.

== HELPER LEMMAS AVAILABLE (exact signatures) ==
- `genFactorK_apply M i a w : (genFactorK M i) a w = algebraMap k (FractionRing (groupRing (k:=k) d)) (M i a w)`
- `Matrix.mul_apply : (P * Q) r c = ∑ j, P r j * Q j c`
- `Finset.sum_comm : (∑ x, ∑ y, f x y) = ∑ y, ∑ x, f x y`
- `Finset.smul_sum : a • ∑ i, f i = ∑ i, a • f i`
- `Finset.sum_smul : (∑ i, f i) • a = ∑ i, (f i) • a`
- `Finset.sum_neg_distrib : - ∑ i, f i = ∑ i, - f i`  (and `Finset.neg_sum`)
- `smul_smul : a • b • x = (a * b) • x`   ;  `mul_smul : (a*b) • x = a • b • x`
- `smul_comm : a • b • x = b • a • x`
- `smul_neg`, `neg_smul`, `Finset.sum_congr rfl fun .. => ..`
- `algebraMap_smul (K) (c : k) (x) : algebraMap k K c • x = c • x`  (relate the `k`-action and the
  `K`-action of `algebraMap k K c`; used in `hB`).
- Note the proved mirror `hB` uses exactly: `Finset.sum_comm`, `Finset.smul_sum`, `smul_comm`,
  `smul_smul`, `mul_comm`, `genUnitK_smul_mcΘ`, `genFactorK_apply`, `algebraMap_smul`.

== THE PROVED MIRROR `hB` (template — same file, fully builds; the DIRECT/`D(V₂)` side) ==
Goal of hB:
    (∑ w, (genUnitInvK M i.castSucc) w t •
        (∑ a, (genFactorK M i) a w • Dk ((genUnitK M i.succ) s a)))
      = ∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i u b) • mcΘ M i.succ a u)
Proof of hB:
    rw [show (∑ a, ∑ b, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
          (∑ u, (M i u b) • mcΘ M i.succ a u))
        = ∑ b, ∑ u, (genUnitInvK M i.castSucc) b t • (M i u b) •
            (∑ a, (genUnitK M i.succ) s a • mcΘ M i.succ a u) from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [show (∑ a, ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
            (∑ u, (M i u b) • mcΘ M i.succ a u))
          = ∑ a, ∑ u, (M i u b) • ((genUnitK M i.succ) s a * (genUnitInvK M i.castSucc) b t) •
              mcΘ M i.succ a u from
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun u _ => by rw [smul_comm]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_comm ((genUnitInvK M i.castSucc) b t) (M i u b), smul_smul, mul_comm]]
    simp only [genUnitK_smul_mcΘ]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [genFactorK_apply, ← algebraMap_smul (FractionRing (groupRing (k := k) d)) (M i u w), smul_comm]
NOTE: hB ENDS by invoking `genUnitK_smul_mcΘ` (the inverse-collapse `∑ a V₂ s a • mcΘ a u = D(V₂ s u)`).
The hA goal has NO such collapse — do not look for one.

<output_contract>
Return, in this order:
1. A single fenced ```lean block giving the EXACT tactic script to replace the `sorry` (the body after
   `:= by` of `D_orbit_conj_termA`). It must be self-contained (assume the goal is exactly as stated).
2. A 4-8 line "why this closes" walkthrough naming each reindex step and where the sign / the nested-`•`
   collapse / the `genFactorK_apply` rewrite happen.
3. A "risks" list: any step you are UNSURE Lean will accept as written (e.g. whether `Dk` being a
   derivation vs `K`-linear matters here — it should NOT, since `Dk(V₁ c e)` is an opaque `Ω` element
   never re-differentiated in this goal; the `•` are all `K`-on-Ω), and the single most likely failure
   point + a fallback tactic for it.
Prefer an explicit `rw [show LHS = NORMALFORM from by ...]` on BOTH sides into the same explicit
(a,w,c,e)-quadruple-sum normal form, then `Finset.sum_comm`/`rfl` — mirroring hB's structure — over a
fragile `simp`-only attempt. Keep it as close to hB's idiom as the math allows.
</output_contract>

<grounding_rules>
- Do not invent lemma names. Use only the lemmas listed above or standard Mathlib v4.29 names you are
  confident exist; flag any name you are not sure of.
- The identity IS true (hand-verified above). If you think it is false, STOP and say exactly which term
  fails to match — do not paper over it.
- Distinguish "this tactic will compile" (claim) from "this is the right shape, modulo Lean accepting the
  exact lemma forms" (inference). Mark inferences.
</grounding_rules>
</task>
