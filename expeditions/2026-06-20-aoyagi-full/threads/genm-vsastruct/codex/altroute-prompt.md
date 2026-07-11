<task>
Decide between two routes to prove finiteness of a per-chart matrix integral: a "casting" route that
introduces a determinant-inverse Jacobian, vs a "native" route that integrates the actual chart loss
directly. Exact reasoning; I withhold my lean.
</task>

<setup>
The per-chart integral (one peel of the (3,3,3,4) deep linear network at pivot cut t=1) has the good-chart
loss g_cc(Γ,v) = frobSq(P·v·A₂) + frobSq((C·v + Γ·W)·A₂), with Γ the a×b=2×2 corank block, v the t×h=1×3
boundary rows, A₂ the h×o=3×4 deep factor, P (1×1 pivot), C, W (q×h). The good chart assumes P
left-invertible, W and A₂ right-invertible (the resolved front is non-degenerate).

ROUTE 1 (casting): fix A₂, integrate (Γ,v) to get a "corner slice" in the units
U₀=‖w₁A₂‖²+δ²‖w₂A₂‖², U₁=a_piv²‖v̄A₂‖²; then CAST A₂ ↦ (X,Z) via M=[w₁;w₂;v̄] to clean coords ‖X‖²,‖Z‖².
The casting Jacobian is |det M|^{−4} (a DET-INVERSE), nonintegrable over the front near {det M=0}, forcing a
sector restriction {|det M|≥η} + a deeper complement, and a coercive (non-Frobenius-preserving) unit-clear.
~7 new pieces + the det-inverse artifact.

ROUTE 2 (native): integrate g_cc DIRECTLY over the (Γ,v) block. A BANKED lemma proves: flatten (Γ,v) to
ℝ^{a·b+t·h} (measure-preserving linear), g_cc becomes degree-2-homogeneous, continuous, sphere-positive
(given the good-chart invertibility), so the ISOTROPIC corner lemma (∫_{cube}(deg-2 pos)^{−c'}, threshold
dim/2) closes it at c' < (a·b + t·h)/2 = (4+3)/2 = 7/2. NO casting, NO A₂-reparametrization, NO det-inverse.
The chart→g_cc equality and the v-exposure CoV are also banked.
</setup>

<questions>
Q1 (does the native route avoid the det-inverse AND the sector-restriction, landing the same 7/2?). The
   native inner integral is over (Γ,v) at FIXED A₂; the det-inverse in Route 1 came from reparametrizing
   A₂. Does Route 2 avoid |det M|^{−4} entirely (it never casts A₂)? Confirm the threshold (a·b+t·h)/2 = 7/2
   equals ½·minAdm(3,3,3,4), and that it is the SAME "codims add" value Route 1 targets. Is the isotropic
   corner (dim a·b+t·h = 7) the SAME 7/2 as Route 1's weighted-AM-GM corner (h₀+h₁+2)/2?
Q2 (what does the native route still owe, and is a det-inverse hiding there?). Route 2's inner slice needs
   the good-chart invertibility (P,W,A₂). The OUTER integral over the deep data / tail is where the
   invertibility degenerates. Is the outer degeneration a det-inverse (like Route 1's front |det M|^{−4}),
   or a smallest-singular-value / sphere-min weight (∫ a(A₂)^{−s}, a = sphere-min of the loss) handled by a
   codim/good-chart cover? I.e. does Route 2 relocate the det-inverse to the outer integral, or genuinely
   eliminate it?
Q3 (which route is cleaner / fewer new pieces?). Route 1 = ~7-piece chart + casting + det-inverse sector.
   Route 2 = the inner slice is a single banked lemma (chart-equality + v-exposure + isotropic-corner
   endpoint, all banked); the only remainder is the outer tail integration + the good-chart cover (which
   BOTH routes owe as the deeper (S,J) rung). Decide: which route is the cleaner primitive, and is Route 2's
   remainder strictly a subset of Route 1's?
</questions>

<output_contract>
For Q1–Q3: direct answer + "FACT" vs "INFERENCE". End: which route wins (native vs casting), does the
native route genuinely eliminate the det-inverse (not relocate it), and is its only remainder the
deeper (S,J) rung that both routes share?
</output_contract>

<grounding_rules>
Distinguish "eliminates the det-inverse" from "relocates it". The isotropic corner threshold is dim/2 for a
degree-2 sphere-positive form. Check the outer degeneration is a σ_min/sphere-min (not a det).
