<task>
I am adjudicating the integrability (real log-canonical threshold, RLCT) of a family of matrix
integrals that arise as the "corner" of a change-of-variables peel in a deep-linear-network zeta
function. I want your INDEPENDENT analysis of a specific local integral, its threshold, and whether a
proposed reduction route is sound. Do NOT assume my framing is correct; derive the thresholds yourself.

## The concrete objects

Fix integers a,b,q,t ≥ 0 with b ≥ 1. All matrices real. Variables (all integrated over a fixed
BOUNDED box, e.g. the unit ball, around the origin — NO integration to infinity):

- B₀ : a t×q matrix — think of it as the product of a shorter matrix chain ("reduced chain"); for the
  base case treat B₀ as a single FREE t×q matrix (t·q real entries).
- C' : an a×t matrix (free, bounded box).
- Γ  : an a×b matrix (free, bounded box).
- Q_b : a b×q matrix. In the base case Q_b is a FREE b×q matrix (b·q real entries). (In the general
  case Q_b = Y·A is itself a product, but treat it as free for now.)

The integrand is  f^(−c')  where

    f  =  ‖B₀‖²_F  +  ‖ C'·B₀ + Γ·Q_b ‖²_F        (Frobenius norms squared),

and c' > 0 is a real exponent. The integral is
    I(c') = ∫ f^(−c') d(B₀) d(C') d(Γ) d(Q_b)   over the bounded box.

## Questions (derive each independently, exact where possible)

Q1. For the BASE case (B₀, Q_b both free matrices), for which c' is I(c') finite? Give the exact
    threshold c'* (the RLCT), with the reasoning (resolution / blow-up / direct-sum-of-RLCTs /
    explicit radial integration). In particular: is the threshold ½·(codim of the zero locus of f)?
    Compute the codim of {f=0} and compare.

Q2. A proposed route claims: "split Γ = (Γ_∥ , γ) where γ is the a×1 block that multiplies the
    rank-deficient direction of Q_b; peel the Γ_∥ directions as free Morse/translation directions
    (they add freely to output coordinates), then the residual is governed by the bilinear
    ‖γ·z‖² where z ∈ ℝ^D is a single row of Q_b, i.e. a 2-layer chain (a,1,D)."
    (i) For the standalone bilinear model g = ‖B₀‖² + ‖C'·B₀ + γ·z‖² with γ∈ℝ^a, z∈ℝ^D free (bounded
        box), for which c' is ∫ g^(−c') finite? Derive the exact threshold. Is it ½·(t·q + min(a,D))?
    (ii) Does the coupling term C'·B₀ (C' a free matrix) change the threshold vs the decoupled model
         ‖B₀‖² + ‖γ·z‖²? Explain why or why not.

Q3. Contrast with a DIFFERENT route ("Regime A"): instead of the above, integrate Γ over ALL of ℝ^{ab}
    (the whole plane, NOT the bounded box). A standard Morse/Gaussian-type computation gives
        ∫_{ℝ^{ab}} f^(−c') dΓ  =  K · det(Q_b Q_bᵀ)^(−a/2) · ‖B₀‖^(−(2c'−ab))     (for c' > ab/2).
    The emitted weight det(Q_b Q_bᵀ)^(−a/2) must then be integrated over Q_b. For which a,b,q is
        ∫_{box} det(Q_b Q_bᵀ)^(−a/2) d(Q_b)  finite?  Derive the exact condition (in terms of a,b,q),
    including the behaviour near the rank-drop locus {rank Q_b < b}. Where does this DIVERGE?

Q4. The key comparison: when the Regime-A route of Q3 DIVERGES (the det weight is non-integrable),
    does the bounded-box route of Q2 nonetheless give a FINITE integral with the SAME zero locus, at
    the SAME threshold as the true integral I(c') of Q1? I.e. is the bounded-box route a legitimate
    way to certify finiteness that AVOIDS the divergent det-weight, or does the singularity resurface
    somewhere in the bounded-box route? Concrete instance to check: a=2, b=1, q=2 (so D=q=2), t=1.

Q5. Now suppose Q_b = Y·A is a PRODUCT (Y a b×m free matrix, A a fixed-or-free m×q matrix, general
    case). Does the bilinear-leaf reduction of Q2 still deliver the threshold, or does the product
    structure (the "twist") LOWER the threshold below the base-case value? Give the mechanism and, if
    it lowers, the exact regime (in terms of a,b,q,m) where it does.
</task>

<output_contract>
- For each Q, give: the exact threshold/condition, the derivation method, and an explicit small
  worked instance. Distinguish PROVEN (exact integration / resolution) from HEURISTIC (MC / scaling).
- Flag any place where a codim count does NOT equal ½·(the RLCT) — I care about the x⁴+y⁶ trap
  (codim 2 but RLCT 5/12), i.e. do not infer RLCT = ½·codim from a codim bound.
- If a threshold depends on a regime split, name the regimes and the boundary exactly.
</output_contract>

<grounding_rules>
- Real log-canonical threshold convention: λ(f) = sup{ c : f^(−c) locally integrable near {f=0} }.
- For a sum h = f(x)+g(y) in DISJOINT variables, use the direct-sum rule λ(f⊕g) = λ(f)+λ(g) where
  applicable; justify its use.
- For a product h = f(x)·g(y) in disjoint variables, λ = min(λ(f), λ(g)); justify.
- Bounded box everywhere (no divergence at infinity); the only singularity is at {f=0}.
- Show the radial/Mellin integral explicitly for at least the base case.
</grounding_rules>
