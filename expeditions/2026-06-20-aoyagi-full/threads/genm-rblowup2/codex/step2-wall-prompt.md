<task>
Formalisation-strategy red-team. I am formalising (in Lean 4 / Mathlib) the RLCT finiteness of
deep-linear-network square-Frobenius loss, following Aoyagi's per-boundary radial blow-up. I need a
decorrelated verdict on ONE question: does a specific "sequential-independence" invariant give a NEW
handle on the last open step, or does it hit the same wall as prior routes?

SETUP (all matrices real; ‖·‖² = squared Frobenius norm = frobSq).

The target finiteness is: for a width vector M : Fin (L+3) → ℕ and c' < (minAdm M)/2,
  routeMLayerBoxIntegral M c' := ∫_{A ∈ box} ‖prod M A‖^{-2c'}  <  ∞,
where prod M A = A_L · A_{L-1} · … · A_0 is the layer product (each A_s a matrix of the given widths),
box = the unit cube in all entries. This is proved by strong induction on the chain arity L (I HAVE a
sorry-free wrapper reducing it to the inductive step + base), so I may ASSUME the strong IH:
  hIH : the analogous finiteness holds for every strictly-shorter chain (arity L+2), in particular for
        the reduced chain redChain t M and the tail chain tailChain M.

The inductive step reduces (via a measure-preserving front-split + a finite pivot-chart cover, both
sorry-free/banked) to showing, for each rank t (1 ≤ t ≤ min(M₀,M₁)) and each t×t pivot minor selection
(ρ,κ), the PER-CHART peeled integral is finite:
  gammaPeelIntegral = ∫_{A' ∈ box(tail)}  ∫_{A₀ ∈ box ∩ pivotChart(ρ,κ)}  ‖A₀ · Q‖^{-2c'}  <  ∞,
  where Q = prod(tailChain M) A'  (the tail product, depends on the outer variable A').

BANKED pointwise identity (frobSq_schur_block_split): on pivotChart the front factor A₀ block-splits
(A the invertible t×t pivot; B,C,D the other blocks; Γ = D − C A⁻¹ B the corank block, p×q with
p=M₀−t, q=M₁−t), and with Q split by rows into pivot rows Q_p and non-pivot rows Q_b, Q̃_p = Q_p + A⁻¹B Q_b:
  ‖A₀ · Q‖² = ‖A · Q̃_p‖²  +  ‖C · Q̃_p + Γ · Q_b‖².
The measure-preserving shear D ↦ Γ exposes Γ as a free p×q variable.

BANKED anisotropic corank atom (gammaAtom_aniso_shifted_eq) — and this tide I banked the INNER-integral
weld on top of it (corankBlock_morsePeel_eq / _lt_top): for Q_b of FULL ROW RANK (Q_b Q_bᵀ posdef) and
c' > pq/2, and any core w ≥ 0 with w+‖A·Q̃_p‖² > 0,
  ∫_{Γ ∈ ℝ^{p×q}} (w + ‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{-c'} dΓ
    = det(Q_b Q_bᵀ)^{-p/2} · C · (w + ‖A·Q̃_p‖² + ‖C·Q̃_p·(I − P)‖²)^{-(c' − pq/2)},  P = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b.
So the inner Γ-integral is EXACTLY the per-step charge: exponent shift c' ↦ c' − pq/2, times the Gram
Jacobian det(Q_b Q_bᵀ)^{-p/2}, on the deeper core.

After the inner Γ-integral, gammaPeelIntegral is bounded (a.e. in A', on the locus where Q_b is full row
rank) by the OUTER integral
  ∫_{A' ∈ box(tail)} det(Q_b Q_bᵀ)^{-p/2} · (‖A·Q̃_p‖² + ‖C·Q̃_p·(I−P)‖²)^{-(c'−pq/2)} dA'.
Here Q_b, Q̃_p, C·Q̃_p all depend on A' through Q = prod(tailChain M) A'.

THE CLAIMED NEW HANDLE (the reason for this route): the single-radial blow-up factorization has a proven
"sequential-independence invariant" — pref · ‖(u•Δ)·Q‖² = (pref·u²) · residual, where the residual is BOTH
u-free AND pref-free. Interpretation offered: "old exceptional coordinates are passive monomial prefixes
on the active residual; each later downstream resolution is pulled back under a monomial prefix,
φ*(u²·G) = u²·φ*(G) — so the resolution is SEQUENTIAL, not simultaneous; recursion is well-founded arity."

PRIOR VERDICT (3 hands + a decorrelated Codex, via the ALTERNATIVE gammaAtom route) on the OUTER integral:
"at the binding cut the residual exponent EXACTLY saturates the reduced-chain IH threshold (0/4000 numeric
cert), zero budget for the Gram coupling det(Q_b Q_bᵀ)^{-p/2}; the Gram divisor and the reduced-core divisor
share the deeper product Z = A₂···A_{L−1} at L ≥ 3; NOT closable by any black-box shorter-chain / Hölder
call — it is the unbuilt (S,J) monomial double induction." Also: on a positive-measure stratum Q_b is
rank-DEFICIENT (M₁−t exceeds a deeper width), so the atom's full-row-rank hypothesis fails and the inner
peel recurses to a deeper boundary.

MY QUESTION: Does the sequential-independence invariant (residual u-free AND pref-free) give a genuinely
NEW handle on the OUTER A'-integral above — i.e. does "monomial prefix pulls out" let the outer integral
be closed by the shorter-chain IH (hIH on redChain/tailChain) WITHOUT a new simultaneous (S,J) monomial
resolution — or is it the SAME wall (the invariant is about the RADIAL coordinates u, and says nothing
about the tail-parameter A' Gram coupling det(Q_b Q_bᵀ)^{-p/2} vs the shifted reduced-core divisor)?
</task>

<output_contract>
1. VERDICT (one line): NEW HANDLE that closes the outer integral via IH, or SAME WALL. Pick one.
2. The decisive reason (≤6 sentences): does φ*(u²·G)=u²·φ*(G) sequential-independence act on the OUTER
   tail-parameter A' integral, or only on the inner radial coordinates? Does the Gram Jacobian
   det(Q_b Q_bᵀ)^{-p/2} (a function of A') get "pulled out as a monomial prefix", or does it couple to
   the reduced-core divisor through the shared deeper product?
3. If SAME WALL: state the single precise remaining sub-problem in one sentence (the thing that must be
   built), and whether the full-row-rank-Q_b restriction is essential or removable.
4. If NEW HANDLE: give the single cheapest concrete check (a specific chain M and c' near the threshold)
   that would confirm the outer integral is IH-closable, and what exact inequality to verify.
</output_contract>

<grounding_rules>
Distinguish clearly what you can DERIVE from the stated identities (fact) from what is an INFERENCE about
the analytic behaviour. If you assert the outer integral diverges/converges, say whether that is a proven
consequence of the stated formulas or a plausibility judgement. Do not invent Mathlib lemma names.
</grounding_rules>
