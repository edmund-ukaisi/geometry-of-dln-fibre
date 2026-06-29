<task>
A real-log-canonical-threshold (RLCT) reduction question from a Lean formalisation of
deep-linear-network loss geometry. I need an independent adjudication of whether a specific
right-equivalence (smooth reparametrization) exists, or whether it provably cannot.

SETUP (all germs at the origin w*=0 in R^n; rlctAtOn is the local RLCT functional, invariant
under (i) precomposition by a measure-preserving homeomorphism, and (ii) precomposition by a
C^infinity local diffeomorphism with invertible derivative fixing w*).

Coordinates split as q = (reg, core, spec) (three blocks of real coordinates).
- E(q) := a SMOOTH (polynomial) R^{reg}-valued "reg residual". Concretely for a 2x2x2 instance,
  E reads off-diagonal/top-left blocks of a matrix product M = P0 * (A0 A1) * QL where
  A_s = [[1+x_s, y_s],[z_s, T_s]] (x,y,z are reg/spec coords, T_s are the CORE coords),
  and P0,QL are fixed invertible endpoint frames. So E DEPENDS ON THE CORE coords T_s,
  but only bilinearly: e.g. one component of E is  (d*p)*y0*T1 + (smooth in reg only),
  another is (a*w)*z1*T0 + (smooth in reg only), with d,p,a,w nonzero frame constants and
  y0,z1 reg coords. (The core enters the reg residual only multiplied by a reg coord.)
- C(q) := a fixed scalar "core energy", the SAME on both sides below.
- Theta: q -> (reg, core + delta(reg,spec), spec) is a measure-preserving homeomorphism
  (a det-1 fibre translation of the core block by an additive shift delta(reg,spec)).
  CRUCIAL: delta is CONTINUOUS but NOT C^1 (it is a Schur-correction difference that is
  continuous-only by construction; proving it C^infinity is exactly the heavy thing we want
  to AVOID). delta(0,0)=0, delta is continuous, Theta(0)=0.

THE EXACT QUESTION. Is there a CORE-AND-SPEC-FIXING, C^infinity local diffeomorphism rho
(rho(0)=0, invertible derivative at 0, rho touches only the reg block, leaves core+spec
pointwise fixed), whose ContDiffness uses ONLY the reg-block structure (NOT delta), such that

    rlctAtOn( sum_i E(Theta q)_i^2 + C(q) ) at 0   =   rlctAtOn( sum_i E(q)_i^2 + C(q) ) at 0

is closed by precomposing the LHS integrand with rho via mechanism (ii)?
I.e. does  (sum E(Theta .)^2 + C) o rho  =germ=  sum E(.)^2 + C  hold for some such smooth rho?

Note E(Theta q) = E(q) with T_s replaced by T_s + delta_s(reg,spec). Because E reads the core
bilinearly, E(Theta q)_i = E(q)_i + (reg-coord)*delta_s + ... , i.e. E(Theta q) picks up terms
that are (smooth reg coord) * (continuous-only delta). Squaring keeps cross terms
2*E(q)_i*(reg-coord)*delta_s.
</task>

<output_contract>
1. A yes/no (or "conditionally"): does such a reg-block-only C^infinity rho exist?
2. If NO: the precise reason it cannot, as a certificate (what invariant obstructs it).
   Specifically address: can a core+spec-FIXING smooth rho ever cancel a term of the form
   (smooth reg coord) * (continuous-only delta(reg,spec)) appearing inside the squared reg
   residual, given rho cannot read delta and cannot move core/spec?
3. If YES: the mechanism (and whether it secretly needs delta to be C^1).
4. Separately: is rlctAtOn even SENSITIVE to such a (smooth)*(continuous-only) cross term,
   or could the RLCT be unchanged for a DIFFERENT reason (e.g. the term is higher-order /
   dominated)? Distinguish "rho exists" from "the two RLCTs are equal anyway".
</output_contract>

<grounding_rules>
- Reason from the germ structure and the stated invariance properties only.
- Keep "the diffeo rho exists" (the asked mechanism) DISTINCT from "the RLCTs happen to be equal".
- Flag any inference vs. fact. Do not assume delta is C^1; that is the forbidden hypothesis.
- Do not write Lean. A short, sharp certificate is what is wanted.
</grounding_rules>
