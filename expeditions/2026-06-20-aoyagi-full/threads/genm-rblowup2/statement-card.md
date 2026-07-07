# Statement card — the integral-level corank-block morse peel (R-BLOWUP sub-tide 1)

Thread `genm-rblowup2` (branch `genm-rblowup2`, off `genm-rblowup` @ `dfd0caea`). Continues the R-BLOWUP
route: on top of the banked corank-step crux (`RouteMSJCorankStep.lean`: `corankStep`,
`corankStep_prefactor`, `corankStep_sequential`) and the banked anisotropic Γ-atom
(`RouteMSJGammaAtom.lean`: `gammaAtom_aniso_shifted_eq`), this tide banks the **integral-level weld** — the
per-step charge produced by integrating the freed corank block — and reports the precise remaining
`(S,J)` gap (decorrelated-Codex-confirmed SAME WALL, artifact
`threads/genm-rblowup2/codex/step2-wall-{prompt,answer}.md`).

> **Claim.** After the Schur block split `‖A₀·Q‖² = ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²`
> (`frobSq_schur_block_split`), integrating the single freed corank block `Γ : Fin p → Fin q → ℝ` against
> the residual-power engine — for coupling `Q_b` of full row rank (`Q_b Q_bᵀ` positive definite) and `c'`
> above the block Morse threshold `pq/2` — yields the exact per-step charge (Aoyagi's exponent shift
> `c' ↦ c' − pq/2` at block dimension `a = pq = (M₀−t)(M₁−t)`):
>
>     ∫_{Γ ∈ ℝ^{p×q}} (w + ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'} dΓ
>       = det(Q_b Q_bᵀ)^{−p/2} · Cresid(pq) c' · (w + ‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P)‖²)^{−(c'−pq/2)},
>     P = Q_bᵀ (Q_b Q_bᵀ)⁻¹ Q_b.
>
> The held pivot energy `‖A·Q̃_p‖²` rides in the additive core (`Γ`-free, strictly positive when `w > 0`);
> the block peels contributing the Gram Jacobian `det(Q_b Q_bᵀ)^{−p/2}` and dropping the deeper core to
> the shifted exponent. Over any sub-domain the integral is `≤` this value, hence `< ⊤`.

- **Lean:** `DLNFibre.DLN.RLCT.corankBlock_morsePeel_eq`, `…corankBlock_morsePeel_setLE`,
  `…corankBlock_morsePeel_lt_top`
  (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJCorankPeel.lean`, +76 net LoC).
- **Gloss.**
  - `corankBlock_morsePeel_eq (Apiv Ccross Qb) (hG : (Qb Qbᵀ).PosDef) (hc' : pq/2 < c') (hw : 0 < w)` —
    the EXACT full-space corank-block integral: `∫_Γ (w + ‖Apiv‖² + ‖Ccross + Γ·Qb‖²)^{−c'} =
    det(Qb Qbᵀ)^{−p/2} · Cresid(pq) c' · (w + ‖Apiv‖² + ‖Ccross·(I−P)‖²)^{−(c'−pq/2)}`. This is
    `gammaAtom_aniso_shifted_eq` (`R := Qb`, `S := Ccross`) with the pivot energy `‖Apiv‖²` folded into the
    additive core. The Schur-split specialisation (the tie to `corankStep`) is this lemma at
    `Apiv = A·Q̃_p`, `Ccross = C·Q̃_p`, `Qb = Q.submatrix Sum.inr id`.
  - `corankBlock_morsePeel_setLE (… s : Set _)` — over ANY sub-domain `s` (in particular the shear-image
    box `{Γ | Γ + C A⁻¹ B ∈ box}` the peel integrates), the integral is `≤` the exact full-space charge
    value (`lintegral_mono_set` + `setLIntegral_univ` + `…_eq`).
  - `corankBlock_morsePeel_lt_top (… s : Set _)` — the same box integral is `< ⊤` (the charge value is a
    real `ENNReal.ofReal`). This is the per-step INNER-integral finiteness the outer recursion consumes.
- **Proved.** All three, sorry-free. `#print axioms = [propext, Classical.choice, Quot.sound]` (forced,
  fresh-olean scratch) — **S2-FREE** (no `sorryAx`, no `monomial_rlct`, no `native_decide`): the
  integral weld is clean, as required.
- **Assumed.** `(Qb Qbᵀ).PosDef` (full row rank of the coupling `Qb`); `c' > pq/2` (above the block
  Morse threshold); `w > 0` (strictly-positive deeper core). No other hypotheses.
- **Cited.** none. Builds only on the banked `gammaAtom_aniso_shifted_eq` (axiom-clean, S2-free) and
  Mathlib (`lintegral_mono_set`, `setLIntegral_univ`, `ENNReal.ofReal_lt_top`).
- **Role.** The **inner per-chart `Γ`-integral** of `sjJointResolution` (`RouteMSJResolution.lean:803`,
  the deferred analytic core of the general-`L` `(S,J)` peel). It produces the per-step charge exactly and
  its `< ⊤` form is the inner finiteness; `sjJointResolution`'s sorry is UNTOUCHED (not laundered).

## The remaining `(S,J)` gap (SAME WALL — decorrelated-Codex-confirmed, not laundered)

The mission's steps (2)–(4) sit on top of the OUTER tail-parameter `A'`-integral, which this weld does
NOT discharge:

    gammaPeelIntegral M t ρ κ c'  ≤  ∫_{A' ∈ box(tail)}
        det(Q_b Q_bᵀ)^{−p/2} · (‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P)‖²)^{−(c'−pq/2)} dA',

where `Q_b, Q̃_p, C·Q̃_p` all depend on `A'` through `Q = prod(tailChain M) A'`.

- **The `corankStep` sequential-independence invariant (`corankStep_prefactor`: residual is `u`-free AND
  `pref`-free) does NOT close this** — it acts on the INNER radial coordinates `u`, not on the OUTER `A'`
  integral. The Gram Jacobian `det(Q_b Q_bᵀ)^{−p/2}` is a function of `A'`, not of any peeled radial, so
  it is not pulled out as a monomial prefix; it couples to the reduced-core divisor through the shared
  deeper product `Z = A₂···A_{L−1}` at `L ≥ 3`. The shorter-chain IH (`hIH` on `redChain t M` /
  `tailChain M`) controls the reduced-core exponent alone, with zero spare integrability budget for the
  Gram Jacobian at the binding cut. (Codex xhigh, decorrelated: **SAME WALL**; its budget-saturation
  claim flagged as inference from the outer-integral structure, corroborating the prior 3-hands + Codex
  `0/4000` numeric verdict on the alternative gammaAtom route.)
- **The single remaining sub-problem** (verbatim, Codex): build the **simultaneous `(S,J)` monomial
  resolution / double induction** that tracks BOTH the reduced-core divisor AND the Gram minors of `Q_b`
  over the shared tail product. The full-row-rank-`Q_b` restriction is not a final restriction — the
  rank-deficient strata (positive measure at `L ≥ 3`, `M₁−t` exceeding a deeper width) must be handled by
  recursive deeper-boundary charts, not ignored.
- **Also unbuilt (bounded plumbing, not attempted this tide):** the block-reindex from
  `gammaPeelIntegral`'s box integrand `‖A₀·Q‖^{−2c'}` on `pivotChart(ρ,κ)` to the block-split form
  (arbitrary `(ρ,κ)` minor → `Fin t ⊕ Fin(M₀−t)` sum-type blocks, measure-preservingly) + the box→full-
  space enlarge before the `measurePreserving_shearSub` `D ↦ Γ` shear. NEW-but-bounded multi-hundred-line
  work; it feeds the inner weld above but leaves the outer `(S,J)` induction untouched, so it was not
  banked for a partial that does not close.

- **Status.** sorry-free; axiom-clean (S2-free); isolated module green + full-aggregate green-gate (see
  thread report for the name-clash gate result). The `(S,J)` outer double induction is the standing
  mountain; `sjJointResolution` left as its named sorry.
