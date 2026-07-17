# dispatch-spec — the d≤1 NATIVE dispatch + the cited-atom dim-match for `innerCorankDescent_lt_top`

**Seat:** pen-and-paper (design), `genm-satred`, the LAST native content of the (□) programme. **Date:**
2026-07-17. **NO Lean.** The endgame is RESOLVED (controller + decstep): min-corank-≥2 = Aoyagi's
product-corank WALL → CITED; the cite makes the decoration unnecessary → (□) closes on the PLAIN route +
per-cut dispatch. This pins the spec a formaliser builds into `innerCorankDescent_lt_top`'s `by_cases 2≤min`
branch. Verified: exact-ℕ (`scripts/{c2_atom_selfsim,decstep_c2,waist_reach,edge_twochain}.py`); my
saturated/corank machinery (satred/D/waist/hBackbone certs).

---

## 0. The target (verbatim) + the dispatch

`innerCorankDescent_lt_top M t ρ κ c' hc' hIH` (`RouteMSJDecoratedPeelStep`), `a := M 0 − t`, `b := M 1 − t`,
`hc' : (c':ℝ) < minAdm M / 2`, `hIH : ∀ M' : Fin(L+1+1)→ℕ, RouteMBoxThresholdFinite M'` (the PLAIN one-shorter
strong IH), concludes the freed-Γ triple integral `∫_{A'∈paramsBoxM(tailChain M)1} ∫_{x∈outerDom t a b 1}
∫_Γ (freedSchurLoss x Γ Q)^{−c'} < ⊤`, `Q = (prod(tailChain M) A').submatrix (blockSplitEquiv κ) id`.

**THE DISPATCH (`by_cases hd : 2 ≤ min a b`):**
- **`hd` (d = min(a,b) ≥ 2) → CITED** `cited_aoyagi_product_corank` (§1).
- **`¬hd` (d ≤ 1) → NATIVE** (§2): the generic dominant-minor chart + the d=1 corank-one atom + the d=0 wings.

## 1. The d≥2 CITED branch — dim-match `cited_aoyagi_product_corank`

arch1build defines the axiom from decstep §1 (Aoyagi's product-corank theorem, `prodcorank`); **I supply the
width/charge consistency so the cited branch type-matches `innerCorankDescent_lt_top`'s conclusion.** The
axiom's signature must produce EXACTLY the freed-Γ triple integral `< ⊤` at `2 ≤ min a b`, consuming `hIH`:

    cited_aoyagi_product_corank (M : Fin (L+1+1+1)→ℕ) (t : ℕ) (ρ : Fin t ↪ Fin (M 0)) (κ : Fin t ↪ Fin (M 1))
      (c' : NNReal) (hc' : (c':ℝ) < minAdm M / 2) (ht : 1 ≤ t) (ht2 : t ≤ min (M 0) (M 1))
      (hd : 2 ≤ min (M 0 - t) (M 1 - t))
      (hIH : ∀ M' : Fin (L+1+1)→ℕ, RouteMBoxThresholdFinite M') :
      (∫⁻ A' in paramsBoxM (tailChain M) 1, ∫⁻ x in outerDom t (M 0-t) (M 1-t) 1, ∫⁻ Γ in {Γ | …},
        ENNReal.ofReal ((freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id))^(-(c':ℝ)))) < ⊤

— IDENTICAL conclusion to `innerCorankDescent_lt_top` + the `hd` guard. **Width/charge consistency I certify
(so the cite is sound + the exponent threshold matches):** the product-corank codim is
`C_m = m² − ⌊m²/4⌋` (`m` the min-corank drop; the NON-submersive joint incidence — NOT the naive `m²`; this
is exactly the wall Aoyagi resolves), and the min-over-strata reaches `½minAdm M` — the cited theorem asserts
the freed integral finite for `c' < ½minAdm M`, consistent with `hc'`. The cite discharges the whole d≥2
branch (no native descent); the decoration is unnecessary here.

## 2. The d≤1 NATIVE dispatch (`¬hd`, min(a,b) ≤ 1)

**★ CONSISTENT CHARGE (round-5 kill-condition):** every per-cut charge is `peelCharge M u' = (M 0−u')(M 1−u')
= (corank at the deepened cut)²` — NOT the mislabeled `(b−r)²`. The reduced-chain reduction is to
`redChain u' M` at exponent `c' − peelCharge/2`, closing via the PLAIN `hIH (redChain u' M)` + cut-soundness
`minAdm M ≤ peelCharge(u') + minAdm(redChain u' M)` (`minAdm_le_peelCharge_add_redChain`, 0/22932).

**(2a) The generic dominant-minor chart (decstep's watch-item) — the BULK, via plain hIH.** Cover the outer
`x`-domain by the `t` dominant `t×t` minors of `[P|B₁₂]`; on the chart where minor `σ` is nonsingular
(`|det P_σ| ≥` the others), the CoV `z̃₀ = P_σ⁻¹·(front)` has BOUNDED pushforward density (the `|det P_σ|`
Jacobian is dominated on its own chart), so the chart integral `≤ K · routeMLayerBoxIntegral(redChain t M)
(c') 1 < ⊤` by `hIH (redChain t M)`. Lean-friendly: a FINITE `Finset`-cover (the `t×t` minors, `Nat.choose`
many) + the per-chart dominant-minor bound + `ENNReal.sum_lt_top`. **No corank singularity on this chart**
(the pivot is nonsingular). This is the dominant part of ALL cuts; the corank strata (2b/2c) are the |det|→0
complement.

**(2b) d=1 (min(a,b)=1) — the corank-one atom, PINNED (§3 of D-cert).** On the corank-one singular stratum:
the C-transversality (`C ↦ C·Q̃ₚ·η` surjective for `Q̃ₚη≠0`) + the `RouteMSJFreeBilinear` b=1 leaf
(`γ⊗z` outer product, `sumSqND_box_lt_top`) + the δ-fold (`one_add_log_inv_le_rpow`, the tie-log) → reduces
to `redChain u' M` at `c' − peelCharge(u')/2` via the PLAIN `hIH`. Exact statement (the D-cert §3 / §3bis
a<u leaf): `∫ |v'_{j₀}|^{−a}·scaledRadialEuclid·frobSq(P·Q̃ₚ)^{−(c'−a/2)}` with `∫_ω ‖Q̃ₚω‖^{−a} < ⊤ ⟺ a<u`
(`corner_block_lintegral_lt_top`), then `hIH`. Charge `= peelCharge(u')`. [edgefub feeds the edge cells.]

**(2c) d=0 (a=0 or b=0, `t = min(M₀,M₁)`) — the WINGS, single-factor submersive.**
- **a=0** (M₀≤M₁, u=M₀): the WIDE X·Y pushforward-DENSITY wing (`waist-pin §★★` (a)+(b) atom for u≤2; the
  density `ρ` bounded/log/power) → `hIH (redChain M₀ M)`. [The u≥3 square/deep is d≥2-at-a-shallower-cut →
  CITED; here d=0 at the wing is the single-factor submersive part.]
- **b=0** (M₁≤M₀, u=M₁): the TALL `[P;C]` Wishart/qbox `det(PᵀP+CᵀC)^{−M₂/2}` (`waist-pin §5`, banked
  `qbox_lintegral_lt_top`, b=M₁,q=M₀,α=M₂, conv⟺M₂≤a; M₂>a recurses per-level) → `hIH (redChain M₁ M)`.
Both single-factor SUBMERSIVE (injective/surjective front) — plain hIH, no decoration, no product-corank.

## 3. Levels kept apart / what each seat feeds

- The dispatch is the FINITENESS/(□) fill of `innerCorankDescent_lt_top`; it does not touch the codim/`rlct`
  levels. `hIH` is the PLAIN `RouteMBoxThresholdFinite` (the decoration is discharged inside each native case;
  never carried into `hIH` — route-safe).
- **intub (interior)** feeds the 2a generic dominant-minor chart + interior cells; **edgefub (edge)** feeds
  the 2b corank-one edge cells (via the `hFrontReduce` interface, `hBackbone-edge-pin §★`). The 2c wings +
  the 2a chart are my native content; the d≥2 cite is arch1build's axiom (I dim-matched §1).

## Close

- **Firmest.** The (□) endgame closes on the PLAIN route + per-cut dispatch: `by_cases 2≤min(a,b)` — d≥2
  CITED (`cited_aoyagi_product_corank`, dim-matched to the freed-Γ triple + `hIH`, §1), d≤1 NATIVE (2a
  generic dominant-minor chart + 2b corank-one §3 + 2c a=0/b=0 wings), all via the PLAIN `hIH` at the
  CONSISTENT charge `peelCharge M u' = (corank-at-cut)²`. My saturated/corank machinery IS the d≤1 native
  dispatch. No wall in d≤1 (the wall is d≥2, cited).
- **Most likely to break the BUILD.** (i) The mislabeled `(b−r)²` charge (round-5 kill) — use `peelCharge M
  u'`. (ii) The cited-atom conclusion not IDENTICAL to `innerCorankDescent_lt_top`'s (must be the same
  freed-Γ triple + `hd` guard + `hIH`) — §1. (iii) The 2a dominant-minor cover form (decstep's watch-item) —
  the finite minor `Finset`-cover + the per-chart bounded density, not a single chart. (iv) Carrying the
  decoration into `hIH` (never — it's discharged inside each case).
- **Next.** A formaliser builds the `by_cases` branch: §1 cite (arch1build's axiom, my dim-match) + §2a/2b/2c
  native (my machinery). intub/edgefub feed 2a/2b cells. I'm on-call for per-chart detail (the 2a
  dominant-minor bound, the 2b/2c exact instantiations at the formaliser's widths). Then (□) → mint.

Files (absolute): `…/threads/genm-satred/dispatch-spec.md` (this); `D-cert.md` (§3 corank-one), `waist-pin.md`
(§★★ a=0 density, §5 b=0 Wishart), `hBackbone-edge-pin.md` (edge hFrontReduce), `c2-atom-supply.md`
(the d≥2 product-corank = the cited wall); `scripts/{c2_atom_selfsim,decstep_c2,waist_reach,edge_twochain}.py`.
