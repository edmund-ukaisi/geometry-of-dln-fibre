# P0 γ'-clause cert — the FINAL carried `FaithfulSJAt` d≥1 clause set (units DROPPED)

**Seat:** pen-and-paper WITNESS (genm-sj4-recon P0, PRE-tide). **Date:** 2026-07-12. **NO Lean, NO build.**
**Charge:** close the ONE load-bearing design gap the self-recon flagged (recon-map §5.1/§7/§8-P0) —
the units-bound clause status of the z-dependent `FaithfulSJAt` γ' rebuild — BEFORE the #4 base tide
commits. Adjudicate: DROP or CARRY. **Verdict: DROP** (units is the unique z-DEPENDENT clause; carrying
it re-creates the fixed-Z unsatisfiability at intermediate arity). Decorrelated Codex CONCURS (below).

**Read:** recon-map (this thread); `joint-corner-cert.md §4`; `stephyp-buildplan.md §5′/§6″`; the fixed-Z
`FaithfulSJAt` def + base leg on `origin/wip/genm-sj4-base-fixedz` (`RouteMSJAdm.lean:136-159`,
`RouteMSJBaseHyp.lean:129-321`). Exact-algebra: `minAdm` recursion (`RouteMLayerSplit.lean:58`),
`axisRatio (h k) = (h+1)/(2k)` (`Skeleton.lean:47`).

---

## 1. THE FINAL CARRIED γ' CLAUSE SET (units DROPPED)

The d≥1 disjunct of `FaithfulSJAt D` (for `D : SJDecoration M`, `M : Fin (L+1) → ℕ`) is
`1 ≤ D.d ∧ ∃ i₀ : D.ι,` with clauses **α, β, δ≡0, γ'**; the carried invariant is
`adm = genuineCarrier D ∧ (admCorankA M = 0 ∨ admCorankB M = 0 ∨ FaithfulSJAt D)`. Carried set:

| clause | statement | z-indep? | status |
|---|---|---|---|
| `genuineCarrier` | `ζ=Unit`, `ν = Fin(M 0)×Fin(M last)`, `e : Z ≃ᵐ Params M` MP, `dom = e⁻¹'(paramsBoxM M 1)`, `ctx z .2 = prod M (e z)` | yes (structural) | **KEEP** |
| **(α)** pSimultaneous | `∀ j ℓ, supp i₀ ℓ ≤ supp j ℓ` | yes (support) | **KEEP** |
| **(β)** threshold | `(minAdm M : ℝ≥0∞)/2 ≤ monomialThreshold D.d (sharedDivisorExp supp) jac` | yes (arith) | **KEEP** |
| **(δ≡0)** uniform support | `∀ i ℓ, supp i ℓ = sharedDivisorExp supp ℓ` | yes (support) | **KEEP** |
| **(γ') dims** | `minAdm M ≤ a * n` | yes (dims) | **KEEP** |
| **(γ') provenance** | `∀ z i, residual (ctx z) i = rmatMul (Γ z) (Z_tail r) (ρ i).1 (ρ i).2`, `(Γ z, r) = eΓ z` | yes (∀-identity on dom) | **KEEP** |
| **(γ') split iso** | `eΓ : Z ≃ᵐ (Fin a → Fin n → ℝ) × R`, `MeasurePreserving eΓ`, `dom = eΓ⁻¹'(matBox a n 1 ×ˢ Rbox)`, `ρ : ι ≃ Fin a × Fin Dt`, `Z_tail : R → Matrix (Fin n)(Fin Dt)` tied to `tailProd` | yes (structural) | **KEEP** |
| **(γ') UNITS** | `0 < c ∧ (Z_tail(r)·Z_tail(r)ᵀ − c•1).PosSemidef` | **NO (z-dep)** | **★ DROP** |

**Exact final γ' (Lean shape, units-free):**
```
(letI := D.mZ; letI := D.fν; letI := D.fι; letI : Nonempty D.ι := ⟨i₀⟩;
  ∃ (a n Dt : ℕ) (R : Type) (_ : MeasureSpace R)
    (Z_tail : R → Matrix (Fin n) (Fin Dt) ℝ)
    (eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ) × R) (ρ : D.ι ≃ (Fin a × Fin Dt)),
    MeasurePreserving eΓ ∧ D.dom = eΓ ⁻¹' (matBox a n 1 ×ˢ Rbox) ∧ minAdm M ≤ a * n ∧
    ∀ (z : D.Z) (i : D.ι),
      D.carrier.residual (D.ctx z).1 (D.ctx z).2 i
        = rmatMul (eΓ z).1 (Z_tail (eΓ z).2) (ρ i).1 (ρ i).2)
```
with the **R-tie** (`Z_tail` from the `tailProd` suffix product, P1) forcing `R = Unit` / `Z_tail () = I`
(`Dt = n`) at width-2. The `0 < c ∧ PosSemidef` conjuncts of the fixed-Z form (`RouteMSJAdm.lean:156`)
are **removed**. This is the `WeightedLeafForm` shape (`RouteMSJBaseHyp.lean:262`) upgraded with the
measure-split (`eΓ`, MP, dom) + `ρ` an `≃`.

### Why DROP (the load-bearing argument, exact)
The carriability criterion (`joint-corner-cert §4`, UPDATE-955): **a clause is carriable IFF z-INDEPENDENT
(holds on all of `dom`)** — `adm` is a domain-wide invariant. Every retained clause is a property of
`supp`/`jac`/dims/the fixed iso, holding on all of `dom`. The units bound
`(Z_tail(r)·Z_tail(r)ᵀ − c•1).PosSemidef` is a **pointwise fact in `r`**: at intermediate arity `Z_tail`
is a genuine z-dependent family, and the box `Rbox` (centred at 0) **contains `r = 0`**, where
`Z_tail(0) = 0`, so `(0 − c•1) = −c•1` is PosSemidef only for `c ≤ 0`, contradicting `0 < c`. So **no
`c > 0` makes the units bound hold `∀ r ∈ Rbox`** — the units-∀r clause is UNSATISFIABLE inside `dom` at
every intermediate arity (rank-deficient tail sublocus `⊂ dom`). Carrying it re-creates the fixed-Z
unsatisfiability (recon §6 dead-route) in a subtler form. Hence DROP.

### #4 DERIVES the units bound at the width-2 base (exact)
Width-2 (`M : Fin (1+1)`): the tail is empty ⟹ `tailProd = I`, `R = Unit`, `Z_tail () = (1 : Matrix (Fin n)(Fin n))`,
`Dt = n`. Provenance collapses: `rmatMul (Γ z) (1) = Γ z` (right-`I`), so `res_i = (Γ z)_{ρ i}`, matching
genuineCarrier's single-matrix `Params M` (= the single free block, `R=Unit`). `#4`'s
`decoratedBase_routeA_of_leafForm` (`RouteMSJBaseHyp.lean:129`) takes the units bound as EXPLICIT args
`(cpos : ℝ)(hcpos : 0 < cpos)(hZ : (Z·Zᵀ − cpos•1).PosSemidef)`; #4 supplies them from `Z := 1`:
- `cpos := 1`, `hcpos := one_pos`;
- `hZ`: `(1·1ᵀ − 1•1) = (1 − 1) = 0` (via `Matrix.transpose_one`, `Matrix.mul_one`, `one_smul`), and
  `(0 : Matrix).PosSemidef = Matrix.PosSemidef.zero` (Mathlib). **Trivial, 3 lines** — no carried units needed.

So #4 re-points `decoratedBaseHyp_faithful` case (iii) (`RouteMSJBaseHyp.lean:307-321`): `obtain` the
units-free γ', specialize `R := Unit`, `Z_tail () := 1`, then feed `decoratedBase_routeA_of_leafForm`
with `Z := 1, cpos := 1, hcpos, hZ` derived in-line. The corankLeaf core + `decLoss_clean_of_
uniformResidualSupport` (δ≡0) + `Equiv.sum_comp ρ` reindex are UNCHANGED.

### #5 RE-SUPPLIES the units bound per-peel (NOT carried) — sector mechanism
`joint-corner-cert §3-§5` + `stephyp-buildplan §6″`: each peel restricts to the **units sector**
`{σ_min(Z_tail) ≥ ε}` (equiv. `{Z_tail·Z_tailᵀ ≽ c(ε)·1}`), where route B fires: integrate-Γ-first
(freed Morse) with the Rayleigh bound `c·frobSq Γ ≤ frobSq (Γ·Z_tail)` (banked `frobSq_mul_ge`), the
`c > 0` supplied by the **banked units bridge** `exists_gram_sub_smul_one_posSemidef_of_rank_eq`
(`RouteMSJUnitsBridge`, #147 — a universally-true IMPLICATION `full-row-rank ⟹ ∃c>0, Z_tail Z_tailᵀ ≽ c·1`,
eigenvalue-free / sphere-min). The complement `{σ_min < ε}` (rank-drop, incl. `r=0`) **RECURSES** as a
deeper stratum (arity descent, §6″/§7). So the bound holds **on the sector, per-peel, z-restricted** —
never on all of `dom`, which is exactly why it is NOT a carried `adm` clause. (Codex refinement: the
carriable object is the CONDITIONAL "full-row-rank ⟹ ∃c" — already the banked `#147` lemma, not an adm clause.)

---

## 2. THE WIDTH-3 NON-VACUITY WITNESS (exact — the anti-vacuity guard)

`M = ![2,2,2] : Fin 3 → ℕ` (width-3, `L=2`, intermediate arity). `minAdm(2,2,2) = 3` (recursion: `t★=1`
gives `(2−1)(2−1) + minAdm(1,2) = 1 + 2 = 3`, vs 4 at `t∈{0,2}`). Binding cut `t★ = 1` ⟹
`admCorankA = admCorankB = 1` (both **> 0**), so the `a=0 ∨ b=0` escape does NOT fire — the **d≥1 γ'
disjunct is genuinely REQUIRED**. `minAdm(3,3,2,2) = 4 = 1 + minAdm(2,2,2)`, so this `(2,2,2)` is the
exact reduced image of the `(3,3,2,2) →_{t=2} (2,2,2)` rank-1 regression (`RouteMSJAdm.lean:198-236`).

**Decoration `D`** (`SJDecoration ![2,2,2]`): `d = 1`; `ζ = Unit`; `ν = ι = Fin 2 × Fin 2`;
`carrier.supp i 0 = 1 ∀ i`; `carrier.coeff () i v = if v = i then 1 else 0`; `jac = ![3]`;
`Z = Params(2,2,2) = Matrix(Fin 2)(Fin 2) × Matrix(Fin 2)(Fin 2)` (layers `A₁ = z 0`, `A₂ = z 1`);
`e = id`; `dom = paramsBoxM ![2,2,2] 1`; `ctx z = ((), fun ik ↦ prod ![2,2,2] z ik.1 ik.2)`
(so `(ctx z).2 ik = (A₁·A₂)_{ik}`, since `prod = A₁·A₂`).

**γ' data (units-free):** `a = n = Dt = 2`; `R = Matrix(Fin 2)(Fin 2) ℝ`;
`eΓ (A₁,A₂) = ((fun i j ↦ A₁ i j), A₂)` (coordinate reassociation + matrix↔pi, MP);
`Z_tail r = r`; `ρ = (Equiv.refl (Fin 2 × Fin 2))`.

**Per-clause check (exact):**

| clause | PASS/FAIL | exact reason |
|---|---|---|
| genuineCarrier | PASS | `ζ=Unit`; `ν = Fin(M 0)×Fin(M last) = Fin 2×Fin 2`; `e=id` MP; `dom=paramsBoxM`; `ctx.2 = prod`. |
| split iso + dom | PASS | `eΓ` is measure-preserving relabel; `paramsBoxM = matBox 2 2 1 ×ˢ matBox 2 2 1` under `eΓ` (`Rbox = matBox 2 2 1`). |
| provenance | PASS | `res_i(z) = ∑_v [v=i]·(A₁A₂)_v = (A₁A₂)_i`; `rmatMul (Γ z)(Z_tail r)(i.1)(i.2) = ∑_k A₁(i.1,k)A₂(k,i.2) = (A₁A₂)_{i.1,i.2}`. EQUAL. |
| dims `minAdm ≤ a·n` | PASS | `3 ≤ 2·2 = 4` (margin 1). |
| (α) pSimultaneous | PASS | uniform `supp≡1` ⟹ any `i₀` (e.g. `(0,0)`): `1 ≤ 1 ∀ j,ℓ`. Non-vacuous (`|ι|=4`). |
| (δ≡0) uniform | PASS | `supp i 0 = 1 = sharedDivisorExp supp 0` (inf of constant) `∀ i`. |
| (β) threshold | PASS | `minAdm/2 = 3/2`; `monomialThreshold 1 k jac = axisRatio (jac 0)(k 0) = axisRatio 3 1 = (3+1)/2 = 2 ≥ 3/2`. |
| **UNITS ∀r** | **FAIL** | `Rbox ∋ r=0` ⟹ `Z_tail(0)Z_tail(0)ᵀ − c•1 = −c•1`, not PSD for any `c>0`. **Confirms DROP.** |

**Verdict: INHABITED.** The units-dropped γ' is satisfied by a concrete intermediate-arity decoration;
the d≥1 clause is NON-VACUOUS mid-recursion (the fixed-Z single-`Z` / single-block form was vacuous
there). The lone FAIL is the units-∀r clause — which is precisely the clause being dropped, and its
failure at `r=0` is the same rank-deficient-tail witness that forces the drop. **The witness doubles as
the refutation of carrying units.** This is the P4 non-vacuity target for the tide: an in-file
`example`/`theorem` on this data.

---

## 3. #5-PRESERVABILITY + CO-INCONSISTENCY CHECK

**The finalized units-dropped carried set is the shape #5's Route B preserves** (`joint-corner-cert §4`,
`stephyp-buildplan §5′-N5′/§6″`): same Γ×R split, `res = (Γ·Z_tail)_ρ`, `Z_tail = tailProd(redChain)`,
`ρ` an `≃`, units per-peel-supplied. Clause-by-clause preservation (all banked/banked-adjacent):
- (α) — `sharedDivisorExp_prependColumn_one_zero`/`_succ` (fresh `u₀` shared by all; old preserved). BANKED #144.
- (β) — `carrierThreshold_shift` + `minAdm M = peelCharge + minAdm(redChain)`. BANKED.
- (δ≡0) — peelOp prepends a uniform column ⟹ uniformity preserved.
- dims — `minAdm_redChain_succ_ge` convexity (`RouteMSJTransversality`). BANKED-ADJ.
- provenance/split — route-B peel is a measure-preserving chart producing `D'` with `res' = (Γ'·Z_tail')_{ρ'}`;
  the ρ-Equiv PRODUCTION obligation (`§6″` pt 6) is #5's fidelity target. CO-CONSISTENT.
- units — NOT an invariant to preserve; re-derived per-peel on the sector. **Dropping it is what MAKES #5
  possible** — carrying it would obligate #5 to preserve a clause false on the rank-drop sublocus (impossible).

**Co-inconsistency flag (resolved, HARMLESS):** `recon-map §8-P2` lists the carried γ' WITH the measure-split
(`eΓ` MP + dom); `joint-corner-cert §4` lists `{genuineCarrier, provenance, α, β, minAdm≤a·n, δ≡0}` and
folds the split into "provenance". These are the SAME set at different granularity — both units-free, both
#5-preservable. **RECOMMEND the `§8-P2` measure-split form** (carry `eΓ` MP + dom): least-rebuild from the
fixed-Z code (which already passes `eΓ, hmpΓ, hdomΓ` to `decoratedBase_routeA_of_leafForm`), so #4 need
not re-derive the split from genuineCarrier. No soundness gap either way. **The ONLY genuine change vs the
fixed-Z γ' is: single-block `eΓ` → Γ×R split, fixed `Z` → `Z_tail : R → Matrix`, and DROP `0<c ∧ PosSemidef`.**

---

## 4. DECORRELATED CODEX VERDICT (conclusion withheld in the prompt; frame+facts in)

`codex/units-drop-{prompt,answer}.md` (xhigh; carriability criterion + rank-deficiency facts + witness
data supplied, my "DROP" conclusion WITHHELD). **Codex CONCURS on both:**
- **(a) DROP** — "forced by Facts 1 and 4"; a fixed `c>0` fails at `r=0` (`−cI` not PSD); even `∀r ∃c_r`
  fails at `r=0`; #4 derives at base (`c=1`); #5 re-supplies on the sector (`c=ε²`), complement recurses.
  **Subtlety it raised** (fold into the tide): the units argument must be invoked ONLY after restricting
  to the sector — any theorem extracting the bound from GLOBAL `adm` is unsound. It notes one CAN carry the
  CONDITIONAL "full-row-rank ⟹ ∃c" (= our banked `#147` bridge) but never the unconditional bound — which
  matches the design (the conditional is a lemma, not an adm clause).
- **(b) INHABITED** — independently reproduced every PASS (provenance `=(A₁A₂)_{ij}`, `minAdm=3≤4`,
  `axisRatio 3 1 = 2 ≥ 3/2`, α/δ0), and the single FAIL (units-∀r at `r=0`). "Neither vacuous nor
  ill-formed." (One caveat it flagged — "assuming standard coordinate/product measures" — holds:
  `eΓ` is a relabel of the Lebesgue product, MP by construction.)

No inference of mine was fed to Codex; the concurrence is decorrelated.

---

## Close

- **Firmest result.** DROP the units bound from the carried γ'; it is the unique z-DEPENDENT clause and is
  UNSATISFIABLE `∀r ∈ dom` at every intermediate arity (`r=0 ⟹ Z_tail=0`, `−c•1` not PSD). The width-3
  `(2,2,2)` witness INHABITS the units-dropped γ' (all 7 retained clauses PASS, exact algebra), so the
  d≥1 clause is non-vacuous mid-recursion. #4 derives units at base (`Z=1, c=1, hZ=(0).PosSemidef`); #5
  re-supplies per-peel on the units sector (`#147` bridge). Exact minAdm/axisRatio verified two ways
  (Lean-def recursion + Codex). Decorrelated Codex concurs on both faces.
- **Most likely to break it.** The measure-split domain clause `dom = eΓ⁻¹'(matBox a n 1 ×ˢ Rbox)` must be
  proven CONSISTENT with genuineCarrier's `dom = e⁻¹'(paramsBoxM M 1)` (the full box must factor as
  front-box ×ˢ tail-box under `eΓ`) — true when `Γ` is a coordinate SUB-block (front corank rows), NOT a
  linear combination. If a peel's freed block is ever a non-coordinate combination, the box-factorization
  clause needs restating (unlikely — corank blocks are sub-blocks — but the tide should green-gate the
  domain clause on P4). Second: the ρ-Equiv PRODUCTION obligation is #5's (not #4's) — #4 only consumes it.
- **Next.** Hand to the #4 tide: P2 rewires `FaithfulSJAt` γ' to the §1 units-free split shape; P4 commits
  the §2 witness as an in-file non-vacuity `example`. No further pen-and-paper needed — the mechanism is
  decorrelated-confirmed and the arithmetic is exact. STOP-flag for the tide (recon §7 escape hatch
  DISCHARGED): units bound DROPPED, derived at base (`Z_tail=I, c=1`), P4 built against the units-dropped form.
