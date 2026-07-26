import DLNFibre.Core.Aoyagi.ProductResolution

/-!
# `Core.Aoyagi.SandwichCover` — the R3 V-lower WIRE (abstract), `hideal_bwd`-FREE

The reroute V-lower cover assembly, `hideal_bwd`-FREE (the honest F10/(A) bypass). It is a bounded
adaptation of `Resolution.mem_localAdmissible_of_lt`: that lower-bound leg consumes the family-level
`hideal_bwd` at EXACTLY ONE line — the per-chart `IntegrableOn` of the pulled-back weighted loss
(via `Chart.integrableAtFilter_of_lt` → `wLocalAdmissible_swap`). Here that one input is supplied
by the SUM-level SANDWICH `c·∑ (monomialₖ)² ≤ ∑ (Fᵢ∘g)²` (R2 survivor + `#172`), fed through the
banked one-directional `wLocalAdmissibleExponents_subset_of_eventually_le`. Everything else — the
area formula push-down, the `integrableOn_finite_iUnion` subadditivity, and the `hcover` transfer
onto a neighbourhood of `x₀` — is ideal-free and reused verbatim.

Per-chart data is taken as LOOSE hypotheses (a `Chart` minus `hideal_fwd`/`hideal_bwd`, plus the
sandwich); the concrete `(3,3,4)` discharge supplies them from the flatCube geometry + R2 survivor,
NEVER from the retired α-atlas (`chartBridgeFaithful_buildTree`, `sorryAx`). `hunit1` (squarefree
binding, k = 1) is a per-leaf hypothesis here, HEADLINE-load-bearing — it makes each per-chart value
`chartMin = ⨅ (jac_d + 1)`; the concrete discharge PROVES it via the `#172`/G1 kept-survivor result
(a genuine `e ≥ 2` binding axis would drop the headline below `½·C`).

## Scope
- IN: the abstract cover-assembly lower bound `⨅_c threshold_c ≤ rlctAt (∑Fᵢ²) x₀`, per-leaf
  obligations as hypotheses, `hideal_bwd`-free.
- OUT: the concrete `(3,3,4)` discharge of the per-leaf hypotheses (flatCube charts + survivor
  sandwich + `#172` + squarefree `hunit1`); Object D's `⨅ threshold = ½·minAdm` (`neq_cCodim`); the
  V-upper `≤`-half (`#110`).

## Main result
- `rlctAt_ge_iInf_threshold_of_sandwich_cover` — TRACKED-OPEN (`-- map: R3-wire`): the
  cover-assembly lower bound. The one hole is the adaptation of `mem_localAdmissible_of_lt`.
-/

open MeasureTheory Set Filter Topology RLCT

namespace DLNFibre.Core.Aoyagi

variable {D Mn : ℕ}

/-- **R3 V-lower wire (abstract, `hideal_bwd`-free).** Given a finite family of resolution charts
`g c` over compact domains `dom c` whose images a.e.-cover a neighbourhood `U` of `x₀` (`hcover`),
each carrying the area-formula data (`g c` differentiable, `dom c ⊆ nbhd c` open, a.e.-injective off
a null `excep c`, Jacobian `|det Dg| = jacWeight (jac c) · unit c` with `unit c` continuous/nonzero
on `nbhd c`), the divisibility chain + squarefree binding (`hchain`/`hbind`/`hunit1`), and the
SUM-level SANDWICH `cst c · ∑ₖ (monomialₖ)² ≤ ∑ᵢ (Fᵢ∘g c)²` near each point of `dom c` — the local
RLCT of the loss `∑ Fᵢ²` at `x₀` is at least the `min` over charts of the boxed threshold
`monomialThreshold (bexp c (k₀ c)) (jac c)`. NO `hideal_bwd`: the sandwich alone drives the
lower-bound `⊇`-direction (`wLocalAdmissibleExponents_subset_of_eventually_le`). -/
theorem rlctAt_ge_iInf_threshold_of_sandwich_cover
    {F : Fin Mn → (Fin D → ℝ) → ℝ} {x₀ : Fin D → ℝ}
    {numCharts : ℕ} (hne : (Finset.univ : Finset (Fin numCharts)).Nonempty)
    (g : Fin numCharts → (Fin D → ℝ) → (Fin D → ℝ))
    (dom nbhd excep : Fin numCharts → Set (Fin D → ℝ))
    (bexp : Fin numCharts → Fin Mn → Fin D → ℕ) (k₀ : Fin numCharts → Fin Mn)
    (jac : Fin numCharts → Fin D → ℕ) (unit : Fin numCharts → (Fin D → ℝ) → ℝ)
    (cst : Fin numCharts → ℝ) (U : Set (Fin D → ℝ))
    (hbind : ∀ c, (bindingAxes (bexp c (k₀ c))).Nonempty)
    (hFmeas : ∀ i, Measurable (F i))
    (hgdiff : ∀ c, Differentiable ℝ (g c))
    (hdomcpt : ∀ c, IsCompact (dom c))
    (hnbhd_open : ∀ c, IsOpen (nbhd c)) (hdom_sub : ∀ c, dom c ⊆ nbhd c)
    (hexcep_meas : ∀ c, MeasurableSet (excep c)) (hexcep_null : ∀ c, volume (excep c) = 0)
    (hg_inj : ∀ c, Set.InjOn (g c) (nbhd c \ excep c))
    (hchain : ∀ c k d, bexp c (k₀ c) d ≤ bexp c k d)
    (hunit1 : ∀ c, ∀ d ∈ bindingAxes (bexp c (k₀ c)), bexp c (k₀ c) d = 1)
    (hunit_cont : ∀ c, ContinuousOn (unit c) (nbhd c))
    (hunit_ne : ∀ c, ∀ u ∈ nbhd c, unit c u ≠ 0)
    (hjac : ∀ c, ∀ u ∈ nbhd c, |jacDet (g c) u| = jacWeight (jac c) u * |unit c u|)
    (hcst : ∀ c, 0 < cst c)
    (hsandwich : ∀ c, ∀ p ∈ dom c, ∀ᶠ w in 𝓝 p,
      0 ≤ cst c * sumSqFam (monomialFam (bexp c)) w ∧
        cst c * sumSqFam (monomialFam (bexp c)) w ≤ sumSqFam (fun i ↦ F i ∘ g c) w)
    (hU : U ∈ 𝓝 x₀)
    (hcover : volume (U \ ⋃ c, (g c) '' (dom c)) = 0) :
    Finset.univ.inf' hne (fun c ↦ monomialThreshold (bexp c (k₀ c)) (jac c) (hbind c))
      ≤ rlctAt (sumSqFam F) x₀ := by
  sorry -- map: R3-wire — cover-assembly adaptation of `Resolution.mem_localAdmissible_of_lt`:
        -- per-chart `IntegrableOn` from the sandwich (via `subset_of_eventually_le`) replacing the
        -- one `hideal_bwd` line, then area formula + `integrableOn_finite_iUnion` + `hcover`.

-- TRACKED-OPEN (#187, `-- map: R3-wire`): `#print axioms` carries `sorryAx` (the one cover-assembly
-- hole above). NOT registered in `AxCheck`'s `#assert_banked_clean_batch` while the hole is live;
-- the statement is LOCKED (typechecks against the h0-free interface). Fill = the bounded adaptation
-- of `Resolution.mem_localAdmissible_of_lt` noted at the hole.

end DLNFibre.Core.Aoyagi
