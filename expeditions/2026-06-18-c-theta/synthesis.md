# synthesis.md — controller's integrative read (c-theta)

## OPEN (2026-06-18)
Compute (C,θ) = (min, #minimisers) of the proven quadratic form Σ m_{i-1,j-1} m_{uv} over Kostant
partitions of d with m_{0N}=r (LR §§5–7). Pure ℕ-combinatorics on ext-codimension's output; no AG. Ladder:
define C,θ (L1) → QIP Thm 6.1 (L2) → explicit formula Thm 7.10 (L3) → permutation invariance Cor 5.10 (L4).
Design recon (01) + Layer-1 formaliser (02) dispatched. Geometric "C = codim Σ^r" rides on hVoigt; the
combinatorial C,θ do not.

## DESIGN RECON VERDICT + LAYER 1 (2026-06-18)

**Numerics (3 routes agree, sympy):** direct KP-min = QIP = explicit (via rank-0 reduction) on (2,2,2)→(3,1),
(2,2,3)→(4,2) [Ex6.2], Ex6.3 (8,8,11,11,11,13,13,13,15)→(55,4). Permutation invariance confirmed:
(2,2,3)/(2,3,2)/(3,2,2) all →(4,2) despite differing #KP / total component counts.

**PRECISION FINDING — Thm 7.10 printed rank-r form is CONDITIONALLY correct.** Fails 107/400 random cases,
exactly when m(d') ≠ m((d−r)') (rank shift changes the truncated simplex prefix). Honest Lean target: reduce
rank-r → rank-0 on d−r FIRST (Lemma 4.5), recompute, apply the r=0 closed form — formalise THROUGH the
reduction, NOT the literal S̃ = S−(m+1)r substitution. Codex concurred independently. (Name what's true.)

**QIP (Thm 6.1):** substitution e↦m(e) gives codim(m(e)) = G_d(e) EXACTLY and a valid m_{0N}=0 KP [easy
half]; but e-image ⊊ all KP. Load-bearing converse = **every minimiser is a horizontal-lace module**
(Lemma 6.4/6.7) — the single hardest step in the ladder.

**Mathlib:** PRESENT — Finset.min'/argmin, piAntidiag/finAntidiagonal (the QIP feasible set {e:Σe=d'_0}),
Multiset.sort, Int.fract/floor, Rearrangement. ABSENT — Conway–Sloane closest-vector ⇒ replace with a
direct integer rounding-exchange lemma (NOT a black box; Codex concurs).

**Target ladder:**
- L1 — define KP-Finset, codimForm, C:=min', θ:=#minimisers. **DONE** (Core.CTheta, reviewed; witness
  (2,2,2)→(3,1)). Tightening the brute-force decide witness (3^9→3^6) before commit.
- L2 — rank-shift C(d,r)=C(d−r,0), same θ (add/remove r copies of M_{0N}; proj-inj, Thm 3.7). Reachable.
- L3 — QIP sorted r=0: e-image+identity [easy] + minimisers∈e-image [HARD, Lemma 6.4 = the wall].
- L4 — explicit closed form via rounding/exchange lemmas (own tide; conceptually easier than L3, long).
- L5 — θ = Nat.choose m |δ| on sorted d−r.
- L6 — permutation invariance LAST: falls out of L4+L5 (no KP-only route; avoid the Poincaré series).

Geometric "C = codim Σ^r" rides on hVoigt (deferred); the combinatorial C,θ do not.

## QIP CONVERSE PROTOTYPE (ctheta-qip, 2026-06-18) — crossable, SINGLE-STEP

The converse (every codimForm-minimiser is in the e-image) is formalisable as a single-step contradiction,
NOT a descent measure.
- **HL (horizontal-lace)** = every supported interval touches an endpoint (m_{a,b}=0 for 1≤a ∧ b≤N−1).
  For weakly-incr d, corner 0: e-image = exactly the HL KPs (bijection m(e)↦e); codimForm(m(e))=G_d(e) exact.
- **Two moves, exact Δ≤−1** (proven symbolic, all N≤7): (A) uncross [a,b]+[c,d]→[a,d]+[c,b] (a≤c≤b≤d);
  (B) concat [a,b]+[b+1,d]→[a,d]. Each source-multiplicity coeff = −1, constant +1, all other coeffs ≤0 ⇒
  both sources present ⇒ ΔF ≤ −1 strict.
- **Exhaustiveness** (exhaustive N≤4): every non-HL corner-0 KP admits a strictly-decreasing valid corner-0
  move. CAVEAT (load-bearing, must sit by the statement): needs weakly-increasing **with d_0≥1** (no interior
  zero column — else an interior interval is walled with no partner: d=(1,0,1,0)); and moves must forbid
  creating [0,N].
- **Theorem (converse):** weakly-incr d, d_0≥1, corner 0 ⟹ every codimForm-minimiser is HL. Proof =
  exhaustiveness + per-move Δ≤−1 + min'_le. **No descent measure** — Codex's proposed M=Σ m·min(a,N−b) was
  FALSIFIED by the prototype (uncross creates interior mass); the single-step contradiction sidesteps it.
- **Formaliser:** hardest sub-step = the exhaustiveness lemma (interior interval ⇒ partner, via d_{a−1}≥1
  from weakly-incr). Δ lemmas = mechanical Finset.sum on the proven kernel (corner-blindness already proved).
- **θ = #minimisers + the constructive HL bijection** need a terminating normal form — SEPARATE, harder
  layer; do NOT bundle with the converse.
- Numerics: minimisers all-HL on (2,2,2)→(3,1) … (2,3,4)→(6,2), Ex6.2, and Ex6.3 (8,8,11,11,11,13,13,13,15)
  → min G=55, 4 minimisers, matching the paper's printed e-tuples.

## QIP CLOSED (Thm 6.1) — Layers 3a+3b landed (2026-06-18)
`Core.CThetaQIP` (easy ≤) + `Core.CThetaQIPConverse` (≥) ⟹ `cCodim_eq_qipMin (Monotone d) : cCodim d 0 =
qipMin d`. The combinatorial codimension of the zero-product locus = the QIP minimum, both directions,
green/sorry-free/axiom-clean, reviewed. Hypothesis strengthened to Monotone-d-only (d_0≥1 dropped). Geometric
reading stays modulo hVoigt. **Remaining (C,θ): L4 explicit closed form (Thm 7.10) via rounding/exchange;
θ = minimiser count (binomial, needs the HL normal-form/lattice count); permutation invariance (Cor 5.10,
falls out of L4). The design flagged L4/θ as the harder tail.**

## EXPLICIT-FORMULA TAIL — charted (ctheta-explicit, 2026-06-18); BOUNDED, not a grind

Thm 7.10 closed-form C, θ, minimiser set, perm-invariance, rank-r — all exact-verified vs direct QIP
(Ex6.2/6.3 + batteries). r=0 on weakly-incr positive d'; rank-r reduces to r=0 on sort(d−r).
- **Square completion:** 2 G_d(e) − (Σe)² = Σ_i(e_i−s_i)² − Σ s_i², s_i = d'_0−d'_i (symbolic N≤5). So on
  Σe=d'_0, min G_d ⇔ min ‖e−s‖² (integer, e≥0). Bridges into the committed cCodim=qipMin.
- **Drop-to-m:** m = max{l∈1..N : Σ_{0..l} d'_i ≥ l d'_l}; every minimiser has e_i=0 for i>m (m<N ⟹ S/m <
  d'_{m+1} strict, S=Σ_{0..m} d'). **THE WALL** (Codex concurs) — argmax m + rational strict inequality +
  unit-transfer-strictly-decreases construction. e≥0 is automatic AFTER drop-to-m (a≥d'_m), FALSE before —
  caveat: drop-to-m must precede rounding.
- **Round:** on the m-face e_i = a − d'_i + Δ_i, a=⌊S/m+½⌋, δ=S−m·a, Δ∈{0,ε}^m with |δ| coords =ε=sgn δ.
  This IS the full minimiser set.
- **Integer-square lemma (optimality core):** min{Σt_i² : t∈ℤ^m, Σt=δ} = |δ| for |δ|≤m, attained exactly at
  0/ε-valued t; exchange t_i≥t_j+2 ⟹ swap drops Σt² by 2(t_i−t_j−1)>0. Replaces Conway–Sloane (Codex same).
- **Closed-form C (pure ℤ, a,δ form):** C = ½(d'_0² − Σ_{i=1}^m(d'_i−d'_0)² + m(a−d'_0)² + 2(a−d'_0)δ + |δ|);
  = direct QIP 4000/4000, always integer.
- **θ = Nat.choose m |δ|** via bijection {A⊆Fin m : |A|=|δ|} ↦ e(A) onto the minimiser Finset (card_powersetCard).
- **Perm-invariance (Cor 5.10):** the closed form reads only sort(d) ⟹ trivial corollary (one def-unfold),
  no Poincaré, no KP-bijection.

**Tides:** square-bridge [small] ‖ integer-square-lemma [small, self-contained] → **drop-to-m [HARD, the wall]**
→ value assembly [medium] → θ-count [bounded] → perm-invariance [free]. Recommended order: square-bridge +
integer-square-lemma first (independent), then drop-to-m, then assembly + θ + perm-invariance.

## WALL CLEARED — drop-to-m active-support reduction PROVEN on paper (ctheta-dropm, 2026-06-18)

Certificate `threads/06-drop-to-m/certificate.md` (+ Codex xhigh line-by-line audit, no gap). Exact algebra.
THEOREM (Monotone d): with Φ(e)=Σ(e_i−s_i)², every minimiser on Σe=d'_0, e≥0 has e_i=0 for i>m. Stronger:
any feasible e with e_k≥1 (k>m) is beaten by an explicit unit transfer.
- **m via Nat.findGreatest** of antitone decidable Pred(l): A_l := Σ_{0..l}d'_i − l·d'_l, A_1=d'_0≥0,
  A_{l+1}=A_l − l(d'_{l+1}−d'_l) ≤ A_l. Qualifying set = initial interval {1..m}. (Codex's derivation —
  cleaner than the argmax form; supersedes the brief's max-formulation.)
- **Separation (load-bearing), integer form:** m<N ⟹ m·d'_{m+1} − S ≥ 1, S=Σ_{0..m}d'_i. = integer negation
  of Pred(m+1).
- **Unit transfer:** u_i=e_i−d'_0+d'_i, move k→j, j=argmin_{≤m}u; ΔΦ=2(u_j−u_k+1)≤−2. Gap u_k−u_j≥2 from
  u_k≥1+d'_{m+1}−d'_0, u_j≤S/m−d'_0 (min≤average via Σ_{≤m}e≤d'_0). **All in ℤ — multiply by m, never divide.**
- **ORDERING OBLIGATION (sharpened, load-bearing for soundness):** a≥d'_i for i≤m ALWAYS (in-face nonneg
  clean). BUT d'_{m+1}>a is NOT always true — 3549/30161 boundary cases d'_{m+1}=a (witnesses d'=(4,5,8,9,10,10),
  (2,5,6,7,10), both m=2) where naive full-coordinate rounding keeps spurious support but the true minimiser
  drops it. ⟹ drop-to-m is a SEPARATE optimality fact proved BEFORE rounding; **rounding/assembly stated on the
  m-face only (i≤m), never on all N coords.** Get the i>m ⟺ 0-based Fin index ≥ m off-by-one wrong → wall lemma
  vacuous/false at the boundary.
- Numerics: Ex6.2 (2,2,2)→m=N=2 no drop; Ex6.3 →m=4, sep 52>49, A-seq (8,5,5,5,−3,−3,−3,−17) non-incr.
  Batteries 0 failures across support-drop/transfer/bound-chain/in-face-nonneg (124k cases).
- Lean targets (cert §5): `qip_unit_transfer_decreases` (6-step skeleton) → `qip_minimiser_support_le_m`
  (by_contra). Square-bridge (Gqip↔Φ) is the prerequisite small tide. Most-likely-to-break: integer
  min≤average (keep m·min≤Σ, no division) + the index off-by-one.
