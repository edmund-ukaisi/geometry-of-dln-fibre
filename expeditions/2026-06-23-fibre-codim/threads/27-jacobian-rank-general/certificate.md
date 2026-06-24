# Thread 27 — the GENERAL argument for the hard direction `codim F ≥ C+δ` (pen-and-paper, 2026-06-24)

*Seat: `pen-and-paper`. Direction: obstruction (the scoped no-go that makes the bound tight) + a
witness-level structural certificate. Exact algebra only; no Lean.*

## Headline (no hedge)

The brief's literal target — *"the general argument for `rank(d mult_A) ≥ C+δ` at a generic point of
every irreducible component of `mult⁻¹(E)`"* — is **NOT a usable proof of the hard direction**: at a
generic *smooth* point of a component `F_α`, `rank(d mult_A) = card − dim F_α` is an *identity* (not an
inequality), so "`rank ≥ C+δ` on every component" is **logically equivalent to** the conclusion
"`dim F_α ≤ card−C−δ` for every `α`". There is **no independent structural proof** of the `+C` part of
the rank (the `δ`-part is uniform and clean; the `+C` part *is* the hard direction in Jacobian
disguise). The exact rank formula `rank(d mult_A) = δ + codim Ō_M(A)` that would have closed it is
**FALSE** (refuted exactly). So **route B (generic-smoothness + Jacobian rank) is circular**, and it
additionally carries a scheme-theoretic generic-reducedness burden.

**The clean general argument exists — it is the equivariant homogeneous SWEEP (route c), not the
Jacobian.** It proves *both* directions at once via an orbit-dimension identity that reuses landed
engine machinery and never touches Jacobians, generic smoothness, flatness, or component
classification:

> **(SWEEP)**  `dim Σ^r = δ + dim F`, hence `dim F = dim Σ̄^r − δ = (card − C) − δ`, i.e.
> **`codim_{Rep_d} F = C + δ`** (both directions).

Here `Σ^r = mult⁻¹(Mat^{=r})` (exact rank), `Σ̄^r = mult⁻¹(Mat^{≤r}) = productRankLocusLE d r`,
`F = mult⁻¹(E)`, `δ = r(d_N+d_0−r) = dim Mat^{=r}`, `C = cCodim d r = codim Σ̄^r`.

Two decorrelated `gpt-5.5`-xhigh Codex consults converged on this independently; every numeric input
is exact (Singular primary decomposition + exact-`ℚ` sympy + closed-form orbit-dimension).

---

## 1. What was actually verified (exact, ground-truth)

### 1.1 The fibre is reducible with components of DIFFERENT dimension (Singular `primdecGTZ` over `ℚ`)

- `(2,2,2) r=1`: `dim F = 4`, `codim = 4 = C+δ` (`C=1, δ=3`). **2 components, both dim 4** (both
  TOP). Ideal `(mult−E)` is **radical** (`reduce(radical I, std I) = 0`).
- `(3,3,3) r=1`: `dim F = 10`, `codim = 8 = C+δ` (`C=3, δ=5`, `card=18`). **3 components, dims
  `10, 9, 9`**. The TOP component (dim 10, codim 8 = C+δ) is the *middle-rank* locus (both `3×3`
  factors rank 2 generically, product rank 1); the two dim-9 components are the *endpoint-invertible*
  branches (one factor in `GL_3`). At a generic point of the top component `rank(d mult) = 8 = C+δ`;
  at a generic point of each dim-9 component `rank(d mult) = 9 > C+δ`.

So `codim F = min over components = C+δ`; the lower components carry **higher** Jacobian rank — the
thread-25 observation, now with the exact component dims behind it.

### 1.2 The CONFOUND that kills the naive Jacobian framing (load-bearing — do not repeat it)

The factor-rank strata `S_ρ = {A ∈ F : rank A_i = ρ_i}` are **NOT** the irreducible components. At a
generic point of the *singular* stratum `ρ=(1,1)` of `(3,3,3) r=1` (both factors rank 1, product rank
1), exact sympy gives `rank(d mult) = 5`, so `card − rank = 13` — but `13 > 10 = dim(top component)`,
which is **impossible** for a subset. The `(1,1)`-stratum is a **singular sub-locus inside the closure
of the dim-10 top component**; `rank(d mult)=5` is the (inflated) tangent dim at a *singular* point,
and `card − rank` is meaningless there. Likewise `(2,2,2) r=1` profile `(1,1)` gives `rank=3 < 4 =
C+δ`. **Hence the bound `rank(d mult_A) ≥ C+δ` FAILS at non-generic (singular) points** — it is *not*
uniform over `F`. It holds only at *generic smooth points of genuine components*, where it is the
tautology above. (Refutes the thread-26 retrospective's hopeful "uniform `rank ≥ C+δ` over the whole
fibre — potentially clean component-free claim": that claim is **false**.)

### 1.3 The structural lower bound `rank ≥ δ` IS clean and uniform (the half that survives)

**THEOREM (exact, char-free, every `A ∈ F`).** `image(d mult_A) ⊇ T_E Mat^{≤r}`, so
`rank(d mult_A) ≥ δ`. *Proof:* the endpoint `H = GL_{d_N}×GL_{d_0}` acts with
`mult((P,Q)·A) = P·mult(A)·Q^{-1}`; differentiating the curve `(P_t,Q_t) = (1+tX, 1+tY)` gives
`d mult_A(δ⁰_A(X,Y)) = X E − E Y` (the engine's `OrbitDifferential.orbitAction_eps_eq_deformationδ`
specialised to the two end vertices). As `X,Y` vary this sweeps `{XE − EY} = T_E Mat^{≤r}`, dim `δ`
(`verify_sweep.py`: `rank(X,Y ↦ XE−EY) = δ` exactly, all cases). ∎

**The `+C` does NOT split off cleanly.** The exact formula `rank(d mult_A) = δ + codim Ō_M(A)` (the
orbit `Ō_M` through `A`) is **FALSE**: at a generic gauge-translate of a low orbit it under-shoots
badly (e.g. `(3,3,3) r=1` orbit-profile `[1,1]`: predicted `δ+codim = 5+8 = 13`, actual `rank = 3`).
The naive "orbit-normal complement injects into `Mat/T_E`" is a heuristic, not a theorem (Codex
concurred, both consults). So the Jacobian route has **no independent handle on the `+C`**.

---

## 2. The clean general argument (route c — the homogeneous sweep)

This is the certificate to hand the formaliser. It is a **theorem** (each step provable), validated
exactly on 9 dimension vectors.

**Objects.** `H = GL_{d_N} × GL_{d_0}` acting on `Rep_d` through the two end vertices (the engine's
`BaseChange.baseChange` with inner units `= 1`); `mult` is `H`-equivariant
(`FibreNormalForm.mult_smul`: `mult(P•A) = P_N · mult(A) · (P_0)⁻¹`). `Mat^{=r} = H·E` is a single
`H`-orbit (any two rank-`r` matrices are `GL×GL`-equivalent — `FibreNormalForm.exists_baseChange_of_
rank_eq`), so `Σ^r = mult⁻¹(Mat^{=r}) = H·F`.

**Step A (orbit dimension of the base).** `dim(H·E) = dim H − dim Stab_H(E) = δ`. Exact:
`dim H = d_N² + d_0²`, and `Stab_H(E) = {(P,Q) : PE = EQ}` has the closed-form dimension
`d_N² + d_0² − δ` (block computation: `PE=EQ ⟺ P_{11}=Q_{11}, P_{21}=0, Q_{12}=0`). Linearised:
`rank(X,Y ↦ XE−EY) = δ` (`verify_sweep.py`, all cases OK). This is exactly the thermometer
`DeterminantalStratumDim.varietyDim_productRankLocusLE_stratum` (`dim Mat^{≤r} = δ`), already LANDED.

**Step B (the sweep dimension identity).** The action map `α : H × F → Σ^r`, `(h,A) ↦ h·A`, is
surjective, and its fibre over `h_0·A_0` is the coset `{(h_0 k, k⁻¹·A_0) : k ∈ Stab_H(E)}` (because
`h·A ∈ F` with `mult(A_0)=E` forces `mult(h·A_0)=h·E`, and `h·A_0 ∈ F ⟺ h ∈ Stab_H(E)`). So every
fibre of `α` has dimension `dim Stab_H(E) = dim K`, giving
$$\dim \Sigma^r = \dim H + \dim F - \dim K = (\dim H - \dim K) + \dim F = \delta + \dim F.$$
Exact (`verify_fibration_identity.py`): `dim Σ̄^r − dim F = δ` on all 9 cases. (Equivalently: the
fibres of `mult|_{Σ^r} : Σ^r → Mat^{=r}` over distinct rank-`r` targets are literally `H`-translates,
hence isomorphic, of `F`; `Mat^{=r}` is homogeneous so no general fibre-dimension theorem is needed —
just orbit dimension.)

**Step C (closure / density).** `Σ̄^r = \overline{Σ^r}` (LR Cor 4.4 / Lemma 4.5 — cited; the engine's
`cCodim` docstring already records `Σ̄^r` is the Zariski closure of the exact-rank `Σ^r` and
`codim Σ̄^r = codim Σ^r`), so `dim Σ^r = dim Σ̄^r`. Exact: Singular `dim Σ̄^r` matches `δ + dim F` on
all cases. **Codex's flagged subtlety (correct): the sweep is for `Σ^r` (exact rank), NOT `Σ̄^r`** —
`H·E` reaches only rank exactly `r`, so the zero-product point of `Σ̄^1` is not in `H·F`. Use Step C to
transfer the dimension.

**Step D (assembly).** `dim Σ̄^r = card − C` (LANDED `SigmaCodim` + catenary). Therefore
$$\dim F = \dim \Sigma^r - \delta = \dim \overline{\Sigma}^r - \delta = (card - C) - \delta
\;\Longrightarrow\; \operatorname{codim}_{Rep_d} F = C + \delta.$$

This is **both directions** (`≤` and `≥`) — it subsumes the separately-built easy direction.

---

## 3. Generic smoothness (the brief's Q3), stated precisely — and why it is NOT needed for route c

For completeness (route B needs it; route c does not): over a char-0 field, the reduced variety
`(F_α)_red` of each component is **generically smooth** — a dense open `U ⊆ F_α` with regular reduced
local rings, where `dim_k T_A (F_α)_red = dim F_α`. **BUT** the tangent identity the Jacobian route
needs is `dim_k ker(d mult_A) = dim F_α`, i.e. the tangent space *of the scheme* `V(mult−E)` (=
`ker(d mult_A)`, the engine's `FibreJacobian.finrank_cotangentSpace_fibre_eq_finrank_ker`) must equal
the *reduced* tangent. That requires the scheme to be **generically reduced along `F_α`** (then scheme
tangent = reduced tangent at a generic smooth point). `(mult−E)` is radical on the checked cases
(thread-16 + §1.1 here), so generic-reducedness holds — but it is an *extra* hypothesis, and the rank
identity it yields (`rank = card − dim F_α`) is still circular for the hard direction (§1). **Route c
sidesteps all of this**: it never reads a tangent space.

---

## 4. Formaliser-facing statements

**Recommended (route c — the homogeneous sweep).** Hand the formaliser the orbit-dimension
identity, NOT a Jacobian-rank lemma:

```
-- the load-bearing new lemma (the sweep):
theorem varietyDim_productRankLocusEQ_eq_delta_add_fibre  [IsAlgClosed k] [CharZero k]
    (d : Fin (N+1) → ℕ) (r : ℕ) (hN : (0:Fin (N+1)) ≠ Fin.last N) (hr : r ≤ min_i d_i) :
  varietyDim (Σ^r d r) = r*(d_N + d_0 - r) + varietyDim (fibre d (E d r))
-- via:  Σ^r = H · F  (mult-equivariance: FibreNormalForm.mult_smul + exists_baseChange_of_rank_eq);
--       dim(H·E) = δ  (= the LANDED thermometer DeterminantalStratumDim, or orbit-dim of E);
--       the action-map fibres are Stab_H(E)-cosets ⟹ dim Σ^r = dim H + dim F − dim K = δ + dim F.

-- closure transfer (Cited LR 4.4/4.5):  varietyDim (Σ^r d r) = varietyDim (Σ̄^r d r)
-- assembly:  varietyDim (Σ̄^r) = card − C  (LANDED SigmaCodim) ⟹
--   codimRepCanonical (fibre d (E d r)) = cCodim d r + r*(d_N+d_0−r).
```

The engine carries: `mult_smul`, `exists_baseChange_of_rank_eq`, `codimRepCanonical_fibre_eq_of_rank_eq`
(G1 — reduce any rank-`r` `B` to `E`), `DeterminantalStratumDim` (`dim Mat^{≤r}=δ`), `SigmaCodim`
(`dim Σ̄^r = card−C`), the catenary bridge, and the `G_d`/orbit-dimension machinery
(`OrbitImageDim`, `JacobianTrdeg`, `varietyDim_eq_ringKrullDim_range_orbitPullback`). The **one genuinely
new** rung is the homogeneous-sweep dimension identity (Step B) for the `H`-action on the *fibre slices*
— an orbit-dimension count on the engine's substrate, **not** a general fibre-dimension theorem and
**not** the determinantal-presentation/flatness wall that stalled threads 09/14/20.

**NOT recommended (route B — Jacobian).** If the controller insists on the Jacobian formulation, the
*only* honest lemma is the tautology, and it does not advance the proof:
```
-- at a generic smooth point A of component F_α, IF the fibre scheme is generically reduced along F_α:
--   rank (fibreJacobianMatrix d E A) = card − varietyDim F_α   [= the dim we are trying to bound]
```
i.e. `rank ≥ C+δ ⟺ dim F_α ≤ card−C−δ` — circular. Do not build route B for the hard direction.

---

## 5. Route assembly for `codim F ≥ C+δ` (and `≤`)

Route c gives the full identity `codim F = C+δ` directly (Steps A–D), so the hard direction
`codim F ≥ C+δ` is a corollary (`dim F ≤ card−C−δ`). It pairs with the LANDED one-sided bound
`FibreCodim` (`codim F ≥ C` from `F ⊆ Σ̄^r`) and the in-flight easy direction `codim F ≤ C+δ` (H4-E),
but **subsumes** the easy direction (route c proves `=`). Discharging the sweep identity (Step B)
closes `BundleShiftInterface.cited_bundle_shift` via G1 + G4, exactly as the prior ladders intended —
but on orbit dimension, not flatness.

---

## 6. Kill-conditions / scope / what is most likely to break it

- **Hypotheses:** `[IsAlgClosed k] [CharZero k]` (engine `cCodim = codim` needs alg-closed; char 0 for
  the Voigt/orbit-dim chain), `N ≥ 1` (`hN : 0 ≠ last N` — for `N=0`, `mult` is constant and the claim
  is false), `r ≤ min_i d_i` (`E` realizable / `Mat^{=r}` non-empty and hit; the dominance/sweep
  hypothesis). All three are already the engine's standing hypotheses.
- **The one thing most likely to break it (both Codices' top risk, concurred):** conflating `Σ^r`
  (exact rank, what `H·F` is) with `Σ̄^r` (rank `≤ r`, what `codim = C` is about). The sweep identity
  is for `Σ^r`; the `= card − C` is for `Σ̄^r`. **Step C (`dim Σ^r = dim Σ̄^r`, density / LR 4.4–4.5)
  is the bridge and is load-bearing** — it is *Cited*, not yet Lean-proved in the engine (the `cCodim`
  docstring asserts it). The cheapest exact test (passed): Singular `dim Σ̄^r` equals `δ + dim F` on
  all 9 cases (so the closure does not raise the dimension). If a formaliser cannot get
  `dim Σ^r = dim Σ̄^r` cheaply, that becomes the residual rung — but it is a *density/closure*
  statement (standard, `varietyDim` is closure-dimension), far smaller than the flatness wall.
- **Generic reducedness of `(mult−E)`** is NOT needed for route c (only for the abandoned route B). It
  was certified true separately (thread-16) but route c does not consume it.

## 7. Reproduction (exact artefacts, this thread)

- `validate_rank.py` — refutes `rank = δ + codim Ō_M` at orbit-generic points (the FALSE formula).
- `validate_fibre_components.py` — the factor-rank-stratum confound (why "uniform `rank ≥ C+δ`" is false).
- `ccodim.py` — ground-truth `C = cCodim(d,r)` from the engine's combinatorial definition.
- `fibre222.sing`, `fibre333.sing` — Singular `primdecGTZ`: exact `dim F`, component dims, radicality.
- `middle333.py`, `confirm222.py`, `topcomp_rank.py` — `rank(d mult) = C+δ` at a generic point of the
  genuine TOP component; `> C+δ` on lower components.
- `verify_fibration_identity.py` — `dim Σ̄^r − dim F = δ` and `codim Σ̄^r = C` (9 cases, all OK).
- `verify_sweep.py` — `dim H − dim K = δ` (closed form + linearised stabilizer rank, all OK).
- `codex/general-rank-{prompt,answer}.md`, `codex/reframed-{prompt,answer}.md` — two decorrelated
  xhigh consults; both rank route c first, route B last (circular), and flag the `Σ^r` vs `Σ̄^r`
  subtlety.
