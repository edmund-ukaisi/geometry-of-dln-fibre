<task>
Two published papers study the same statistical model — deep linear networks (DLN): a tuple of
composable matrices, parameter space Rep_d, loss = squared Frobenius norm of (product − B),
B a fixed rank-r target. We are auditing a claim about an integer invariant "theta".

THREE distinct integer quantities are in play for a fixed dimension vector (after the standard
reduction to a relevant index set of size m = ell, with residue data S, a, delta):

(A) Lehalleur–Rimanyi (LR) 2024 define theta := number of TOP-DIMENSIONAL irreducible components
    of the loss zero-locus (the multiplication fibre mult^{-1}(B)). Their closed form is
        theta_LR = C(m, |delta|)   (a binomial coefficient),  |delta| = S - m*round(S/m).

(B) LR also compute the "real log-canonical multiplicity" (rlcm), which they DEFINE as the order
    of the largest pole of the archimedean zeta function ∫ |loss|^s dvol — i.e. the SLT pole
    multiplicity / Watanabe multiplicity. Their closed form is
        rlcm_LR = m^2 * frac(S/m) * (1 - frac(S/m)).
    Numerically across a sweep this equals  a(ell - a)  exactly (a = residue in 1..m as Aoyagi
    defines it; ell = m).

(C) Aoyagi 2023 computes, for the SAME model, "lambda and its order theta", where she defines
    (her Definition 1 / her resolution) theta := the ORDER of the largest pole of the same
    zeta function (the order achieved in the recursive blow-up resolution:
        theta = max_u Card{ j : (h_j+1)/(2k_j) = lambda } ).
    Her closed form (Theorem 1 for 3-layer reduced-rank regression, and Theorem 2 for deep nets,
    and her equal-width Example) is, in EVERY case stated identically,
        theta_Aoyagi = a(ell - a) + 1.

FACTS established by exact computation (sympy/Fraction, no floats):
- For the dimension vector (2,2,2,2,2), r=0:  m = ell = 4, S = 10, |delta| = 2, a = 2.
    * lambda (the RLCT) computed by BOTH papers agrees exactly = 3/2.
    * theta_LR = C(4,2) = 6.
    * rlcm_LR = m^2 frac(S/m)(1-frac(S/m)) = 16 * (1/2)(1/2) = 4.
    * theta_Aoyagi = a(ell-a)+1 = 2*2+1 = 5.
    * Direct exhaustive count of optimal solutions of LR's quadratic integer program = 6
      (confirms theta_LR = 6 = #top components).
- Across a full sweep of (m, S mod m):  rlcm_LR = a(ell-a)  and  theta_Aoyagi = a(ell-a)+1
  ALWAYS, i.e. they differ by EXACTLY 1 in every case (including |delta| <= 1).
- C(m,|delta|) = a(ell-a)+1 only when |delta| <= 1; for |delta| >= 2 it is strictly larger.
- LR include a Remark (their paper): "there is no simple relationship between
  rlcm = m^2 frac(S/m)(1-frac(S/m)) and the number k = C(m, |delta|) of irreducible components."

QUESTIONS (this is the audit):
1. In standard singular learning theory (Watanabe), the free energy / stochastic complexity
   asymptotic is  F_n = n L(w0) + lambda log n - (theta - 1) log log n + o(...),
   where lambda = RLCT and theta = "the order/multiplicity". Is the integer "theta" that enters
   this asymptotic equal to the ORDER (multiplicity m_p) of the largest pole of the zeta function,
   or to (order - 1), or (order + 1)? Be precise about the standard convention and cite the
   relation between pole order and the log-log coefficient.
2. Aoyagi DEFINES her theta as "the order of the largest pole" (her Def 1). LR DEFINE their rlcm
   as "the order of that pole" (identical words). If both are computing the order of the largest
   pole of the SAME zeta function for the SAME model, can the two closed forms legitimately differ
   by exactly 1 (a(ell-a)+1 vs a(ell-a))? List the possible explanations and rank them by
   likelihood: (i) one of the two has an off-by-one (which, and is "+1" or no-"+1" the natural
   convention for an order/cardinality of a max-set?); (ii) they are silently using different
   conventions for "order" (e.g. order of pole vs the log-log coefficient theta-1, vs counting
   from 0 vs 1); (iii) a genuine math discrepancy.
3. Independently of any component-counting: is there ANY standard SLT mechanism by which the ORDER
   of the largest pole of the zeta function of this loss could equal C(m,|delta|) (= 6 here),
   i.e. the number of irreducible components of the zero-locus? In general algebraic geometry /
   SLT, is "#top-dimensional irreducible components of V(F)" equal to "the multiplicity of the
   largest pole of zeta_F"? Give the general relationship (or non-relationship) and any standard
   counterexample.
4. For the 3-layer reduced-rank regression case (Aoyagi Theorem 1, originally from her ref [12]),
   the RLCT and its multiplicity are classically known (Aoyagi–Watanabe 2005). For r=0,
   H = (H1, H2, H3) with the generic ("non-degenerate") inequalities, what is the KNOWN
   multiplicity (order of the largest pole) of the largest pole — is it a(ell-a)+1 or a(ell-a)
   in the equal-rank/balanced sub-case? This pins the convention against an independent classical
   result.
</task>

<output_contract>
Answer the four numbered questions in order, each a short tight paragraph.
- Q1: state the standard Watanabe convention with the exact relation (order m_p <-> log-log
  coefficient). One sentence of justification.
- Q2: ranked list of explanations (most to least likely), each with a one-line reason; explicitly
  say which of "a(ell-a)" vs "a(ell-a)+1" is the more natural value for "order of largest pole"
  and why.
- Q3: state the general relationship between #irreducible-components and pole-order; YES/NO whether
  they coincide in general; one standard example.
- Q4: state the classical reduced-rank-regression multiplicity result and whether it matches
  a(ell-a) or a(ell-a)+1; if you are unsure of the exact classical value, say so and give your
  best-supported answer.
End with one line: which single quantity — C(m,|delta|), a(ell-a), or a(ell-a)+1 — is the
"order of the largest pole / SLT multiplicity", flagged as INFERENCE vs ESTABLISHED.
</output_contract>

<grounding_rules>
- Distinguish ESTABLISHED (standard SLT theorem / classical computation you are confident of) from
  INFERENCE (your reasoning about these specific papers).
- Do NOT assume #components = pole order; that identity is exactly what is under audit.
- If a classical value (Q4) is something you cannot recall exactly, say "uncertain" rather than
  guessing a specific formula.
- Conventions matter: be explicit about whether "order/multiplicity theta" counts the pole order
  or the log-log exponent (theta - 1).
</grounding_rules>
