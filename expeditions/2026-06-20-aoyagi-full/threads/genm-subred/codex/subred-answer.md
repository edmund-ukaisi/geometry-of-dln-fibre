   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (a7a172fe2776d600a7d10bed2bb6163e70433404)
npm warn exec The following package was not found and will be installed: @openai/codex@0.144.1
Reading prompt from stdin...
OpenAI Codex v0.144.1
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre
model: gpt-5.6-sol
provider: openai-aisi
approval: never
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f4e14-a62e-7053-bb94-f3faaf7d991b
--------
user
<task>
Analytic change-of-variables question about a determinantal (Gram) integral arising in
a resolution-of-singularities computation for deep linear networks. Adjudicate exactly.

Fix positive integers b, m, q. Let Y be a real b x m matrix and let Atail be a real m x q
matrix. Set Q := Y * Atail (a b x q matrix), and G := Q Q^T (b x b). Consider

    I(a) = ∫_{box} det(G)^{-a/2} d(Y, Atail)

integrated over a bounded box around a generic point, for a real exponent a>0. There is an
"abstract free-matrix core": if instead Q were a FREE b x q matrix (no product structure)
ranging over a box, then ∫ det(QQ^T)^{-a/2} dQ < ∞ iff a < q - b + 1.

The proposed reduction is: for fixed Atail (of rank >= b), change variables Q = Y*Atail in
the inner ∫_Y, producing a Jacobian J(Atail), so that
    I(a) = ∫_{Atail} J(Atail) * [free-core over the image] dAtail.

Answer these, with exact algebra (worked small instances encouraged):

Q1. Compute J(Atail) exactly for the map Y |-> Y*Atail (at fixed Atail). Handle three
    regimes separately: m = q (square), m > q, m < q. Express J via determinants/Gram
    matrices/singular values of Atail. Is J bounded, or singular somewhere?

Q2. Is the outer integral ∫_{Atail} J(Atail) * [free-core] dAtail a clean product of the
    free-core with a benign (bounded) factor, OR does J(Atail) constitute a new
    determinantal integral in its own right? If Atail = A2*A3*...*AL is itself a PRODUCT
    of matrices (so J is a function of that product), does the J-integral reduce to a
    strictly smaller/shorter problem of the SAME type (a recursion), and if so what is the
    shorter problem?

Q3. What is the exact convergence threshold on a for the ORIGINAL product integral I(a)
    (Q = Y*Atail), as a function of b, m, q? Compare it to the free-core value q - b + 1.
    Are they equal, or does the product structure change the threshold? Work the smallest
    non-trivial instances explicitly (e.g. b=1,m=1,q=2 ; b=1,m=2,q=3 ; b=2,m=2,q=3),
    computing det(QQ^T) as an explicit polynomial and finding the exact threshold.

Q4. The locus {rank Atail < min(m,q)} has measure zero but J may blow up there. Is this
    locus genuinely negligible for I(a), or does its contribution matter (and if so, how)?
    Distinguish m>=q from m<q.
</task>

<output_contract>
For each Q1-Q4: a PROVEN/DERIVED exact statement (mark any inference vs fact). J(Atail)
in closed form per regime. The exact threshold on a for I(a) as a formula in (b,m,q), with
at least one fully-worked explicit polynomial instance. A clear yes/no on whether the
reduction to the free-core is clean or hides extra content, with the mechanism.
</output_contract>

<grounding_rules>
Use exact algebra (sympy/by-hand). MC only to guide, never as proof. If you introduce a
local normal form / blow-up, state it and verify the exponent by explicit integration.
Do not assume the answer; if the threshold differs from q-b+1, show the smallest witness.
</grounding_rules>

codex
I’ll separate the linear-map Jacobian from the convergence problem; they are not the same calculation when the map is non-injective or non-surjective. I’ll first load the repository’s research instructions, then derive the threshold using singular-value/rank-stratum coordinates and verify the requested small polynomials directly.
  → Read repository instructions and locate any relevant existing analysis
  • Derive the fixed-tail coarea/Jacobian formulas in all dimension regimes
  • Derive and prove the original product-integral convergence threshold
  • Work explicit small polynomial instances and synthesize Q1–Q4
exec
/bin/bash -lc "sed -n '1,260p' CLAUDE.md && rg -n \"Gram|det\\(QQ|determinantal|change.of.variables|Jacobian|deep linear|RLCT\" README.md docs paper-sources -g '*.md' -g '*.tex' | head -n 240" in /home/ubuntu/workspace/geometry-of-dln-fibre
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited Aoyagi equality.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them, localise context; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md). This may be a good meta-cognitive skill to have when you are thinking precisely as well. 

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the Aoyagi `rlct = ½·codim` **equality** is
  **Cited** (Watanabe's universal `rlct ≤ ½·codim` + Aoyagi's exact DLN computation — the formal
  `RlctInterface.cited_aoyagi_dln` is the equality, which the payoff needs).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.
README.md:24:and concludes that the real log-canonical threshold of the square-Frobenius loss is $C/2$, so deep linear
README.md:54:codimension engine (reusable on its own), and `DLNFibre.DLN.*` is the DLN fibre + loss + RLCT application
docs/decorrelated-records/link2-fork/codex_epsbound_prompt.md:1:You are a decorrelated second opinion on a Lean 4 / Mathlib formalisation sub-problem (RLCT / singular learning theory, Watanabe). I need the CLEANEST proof STRUCTURE (not full Lean code) for a two-sided comparability ε-bound, and a realistic difficulty assessment.
docs/expositions/core-machinery/01-tuples-and-the-multiplication-map.md:23:deep linear networks — appear in later chapters and are not used here.
docs/expositions/paper-digest/high-level-overview.md:15:The question is motivated by deep linear networks: their parameters are such
docs/expositions/paper-digest/high-level-overview.md:33:   associated deep linear network loss.
docs/expositions/paper-digest/high-level-overview.md:469:condition $BA=0$ is not just a determinantal condition on one matrix; it is a
docs/expositions/paper-digest/high-level-overview.md:639:## 9. The RLCT Payoff
docs/expositions/paper-digest/high-level-overview.md:667:equality for deep linear networks:
docs/expositions/paper-digest/high-level-overview.md:669:!!! theorem "Theorem 8.6 of the paper (RLCT formula)"
docs/expositions/paper-digest/high-level-overview.md:686:    $\operatorname{mult}^{-1}(B)$. The general inequality says that the RLCT
docs/expositions/paper-digest/high-level-overview.md:704:- Section 8: real log-canonical threshold of deep linear networks.
docs/expositions/core-machinery/README.md:14:deep linear neural networks* (Lehalleur–Rimányi 2024). It treats Sections 2–3 of
docs/expositions/core-machinery/README.md:21:This is the **network-free engine**. It mentions deep linear networks only as
docs/expositions/core-machinery/README.md:76:of $(C,\theta)$ (Sections 6–7), and the RLCT identity (Theorem 8.6), whose
docs/expositions/core-machinery/05-the-classification-orbits-and-kostant-partitions.md:243:$(C, \theta)$ and the real-log-canonical-threshold payoff for deep linear
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:94:\title[Geometry of linear neural networks]{Geometry of the fibers of the multiplication map \\ of deep linear neural networks}
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:109:tools from the theory of quiver representations. In particular, we determine its codimension $\codimnot$ and the number $\theta$ of its top-dimensional irreducible components. Our solution is presented in three forms: a Poincar\'e series in equivariant cohomology, a quadratic integer program, and an explicit formula. In the course of the proof, we establish a surprising property: $\codimnot$ and $\theta$ are invariant under arbitrary permutations of the dimension vector. We also show that the real log-canonical threshold of the function taking a tuple to the square Frobenius norm of its product is $\codimnot/2$. These results are motivated by the study of deep linear neural networks in machine learning and Bayesian statistics (singular learning theory) and show that deep linear networks are in a certain sense ``mildly singular".
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:119:In this paper we study the possible ways for a tuple of matrices to multiply to zero (or more generally a fixed matrix). This elementary linear algebra problem leads to some rich geometry and combinatorics, and has applications to deep linear neural networks in statistics and machine learning.
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:156:One motivation for studying the geometry of composable tuples of matrices is \emph{deep linear (neural) networks} and specifically their statistical properties in Bayesian statistics. We give a quick overview here and refer to the introduction of Section \ref{sec:RLCT} for more context.
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:168:The \emph{exact, theoretical} computation of $\rlct(K)$ in realistic machine learning scenarios is generally impossible. However, for deep linear networks, $\rlct(K)$ has been calculated by M.~Aoyagi \cite{aoyagi} and this was used in \cite{lau2024locallearningcoefficientsingularityaware} to calibrate the accuracy of the local learning coefficient. The original formula of Aoyagi is complicated, and we started this project in order to understand it better. Combined with our results, it takes a rather simple form (Theorem \ref{thm:aoyagi-rlct}):
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:174:This shows that the singularities of $K$ are in some sense quite mild. Statistically speaking, this means that deep linear networks are  ``mildly singular".
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:774:     \item $\cSigma^r_{a,b}$ is a \emph{determinantal variety}.
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1778:    Informally we see in both cases that the magnitude of $\codim \Sigma_{\ud}^0$ is not too sensitive to $N$ (``the depth''), only to $d$ (``the width'') of the quiver (``network''), cf. Section \ref{sec:RLCT}.
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1782:\section{Real-log canonical threshold of deep linear networks} %\\and Aoyagi's formula}
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1783:\label{sec:RLCT}
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1790:        \item The \emph{real log canonical threshold} (RLCT) of $F$ is
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1874:In \cite{aoyagi}, Aoyagi computes the real log-canonical threshold of the relative entropy function of \emph{deep linear neural networks}. Deep linear networks are obtained from standard (feedforward, fully-connected) deep linear networks by replacing their non-linear activation functions by linear maps. Despite their simplicity, they are a useful ``toy model" in modern deep learning theory, as we discussed in Section \ref{sec:related}. By definition, the weights of a deep linear networks are a tuple of composable matrices, and the function computed by the network is their product, so the parameter space of the model is $\Rep_{\ud}$ where $\ud\in \N^{N+1}$ records the widths of the layers and $N$ is the depth of the network. We also need a ``true distribution" generating the data, or rather in this context a ``true function". Aoyagi makes the assumption that this true function is linear and given by some $B\in \Mat_{d_N,d_0}^{\rk=r}$ with $0\leq r\leq \min{\ud}$. This condition on the rank emsures that $B\in \mathrm{Im}(\mult)$; in statistical terminology, we are in the \emph{realisable} or \emph{well-specified} case.
paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1876:We now define directly the function $K=K^{\DLN}_B$ for our deep linear model, referring to \cite{aoyagi} for a derivation of how it arises as a relative entropy. As it turns out, in this case, $K^{\DLN}_B$ is algebraic:
docs/policies/precision.md:38:> `rlct_mult_fiber_eq_half_codim` asserts a learning coefficient (RLCT) — which additionally needs the
docs/policies/precision.md:40:> Watanabe, not reprove. The honest name is `multFiber_codim_eq` (or `…_hasCodim`); "RLCT = C/2" is a
docs/expositions/core-machinery/the-type-a-quiver-classification.md:23:Already the two-step case is not determinantal. For scalars $a_1, a_2$ the
docs/expositions/core-machinery/the-type-a-quiver-classification.md:426:map of deep linear neural networks* (2024); source at
docs/policies/bedrock.md:27:here: we do not assault the RLCT directly. We build the quiver-orbit translation, the rank-pattern
docs/policies/writing-style-graduate-math-textbook.md:7:and deep linear networks.
docs/policies/draft-policy-semantic-auditing.md:94:The RLCT-vs-codimension boundary is the model example. One can prove `codim mult⁻¹(B) = C` and name
docs/policies/draft-policy-semantic-auditing.md:102:Consequence: "RLCT = C/2" holds only via the cited rlct ≤ ½·codim bound, not proved here.
docs/policies/draft-policy-semantic-auditing.md:134:- the RLCT of the square-Frobenius loss should equal `C/2` (via the cited analytic bound).

codex
The key structural fact is already visible: the proposed “Jacobian times a fixed free core” is not a valid global factorization. For \(m<q\) the image is only a moving \(bm\)-dimensional subspace; for \(m>q\) coarea introduces a fiber-section volume depending on both \(A_{\rm tail}\) and \(Q\). I’m now checking the exact threshold against an independent Gaussian/Wishart factorization and the requested low-dimensional polynomials.
exec
/bin/bash -lc "python - <<'PY'
import sympy as s
x,y,z,w,a,b,c,d,e,f=s.symbols('x y z w a b c d e f', real=True)
Y=s.Matrix([[x,y],[z,w]])
A=s.Matrix([[a,b,c],[d,e,f]])
Q=Y*A
G=s.factor((Q*Q.T).det())
rhs=s.factor(Y.det()**2*(A*A.T).det())
print('Q =')
s.print_latex(Q)
print('det(QQ"'^T) factored ='"')
print(G)
print('difference =',s.expand(G-rhs))
print('det(AA"'^T) ='"',s.expand((A*A.T).det()))

u,v=s.symbols('u v', real=True)
Y1=s.Matrix([[x,y]])
A1=s.Matrix([[a,b,c],[d,e,f]])
q1=Y1*A1
print('b1m2q3 =',s.expand((q1*q1.T)[0]))
PY" in /home/ubuntu/workspace/geometry-of-dln-fibre
Repository guidance is loaded; the algebra and Gaussian/Wishart cross-check agree on the threshold. Proceeding to formalize the coarea cases and domain caveat.
  ✓ Read repository instructions and locate any relevant existing analysis
  → Derive the fixed-tail coarea/Jacobian formulas in all dimension regimes
  • Derive and prove the original product-integral convergence threshold
  • Work explicit small polynomial instances and synthesize Q1–Q4
 succeeded in 738ms:
Q =
\left[\begin{matrix}a x + d y & b x + e y & c x + f y\\a z + d w & b z + e w & c z + f w\end{matrix}\right]
det(QQ^T) factored =
(w*x - y*z)**2*(a**2*e**2 + a**2*f**2 - 2*a*b*d*e - 2*a*c*d*f + b**2*d**2 + b**2*f**2 - 2*b*c*e*f + c**2*d**2 + c**2*e**2)
difference = 0
det(AA^T) = a**2*e**2 + a**2*f**2 - 2*a*b*d*e - 2*a*c*d*f + b**2*d**2 + b**2*f**2 - 2*b*c*e*f + c**2*d**2 + c**2*e**2
b1m2q3 = a**2*x**2 + 2*a*d*x*y + b**2*x**2 + 2*b*e*x*y + c**2*x**2 + 2*c*f*x*y + d**2*y**2 + e**2*y**2 + f**2*y**2

codex
The checks agree exactly. For a standard singularity-containing box (in particular, one with the origin in its interior), the two-factor threshold is
\[
a_c=\min(m,q)-b+1
\]
when \(b\le \min(m,q)\). Thus it equals the free \(b\times q\) value only for \(m\ge q\); \(b=1,m=1,q=2\) is the smallest counterexample. I’m assembling the proof with the necessary caveat that a sufficiently small box around a full-rank product has no singularity and hence no finite threshold at all.
The coarea formulas, Wishart factorization, local witnesses, and explicit polynomial checks are complete.
  ✓ Read repository instructions and locate any relevant existing analysis
  ✓ Derive the fixed-tail coarea/Jacobian formulas in all dimension regimes
  ✓ Derive and prove the original product-integral convergence threshold
  ✓ Work explicit small polynomial instances and synthesize Q1–Q4
codex
Let \(A=A_{\mathrm{tail}}\), and let \(L_A(Y)=YA\).

First, a necessary domain qualification: there is no threshold depending only on \((b,m,q)\) for an arbitrary translated box. If the box is sufficiently small around a pair with \(\operatorname{rank}(YA)=b\), then \(\det(YAA^{T}Y^{T})\) is bounded below and \(I(a)<\infty\) for every \(a\). The stated free-core threshold likewise assumes that the \(Q\)-box meets the rank-\((b-1)\) locus.

Below, “the threshold” means the standard singular local problem: the box contains the origin, or more generally contains a generic point of the rank-deficient locus described below.

## Q1. Exact Jacobian

Let \(r=\operatorname{rank}A\), with nonzero singular values
\(\sigma _1,\dots,\sigma _r\). The linear map \(Y\mapsto YA\) is the direct sum of \(b\) copies of \(\mathbb R^m\to\mathbb R^q,\ y\mapsto yA\). Its forward \(br\)-dimensional Jacobian is

\[
D_r(A)=\left(\prod_{i=1}^r \sigma_i\right)^b
       =\det\nolimits^{+}(AA^T)^{b/2}
       =\det\nolimits^{+}(A^TA)^{b/2},
\]

where \(\det^{+}\) is the product of the nonzero eigenvalues. Thus the inverse Jacobian appearing in the proposed formula is

\[
J_r(A)=D_r(A)^{-1}=\prod_{i=1}^r\sigma_i^{-b}.
\]

The exact coarea identity is

\[
\int_{B_Y} h(YA)\,dY
=
J_r(A)
\int_{(\operatorname{row}A)^b}
h(Q)\,
\mathcal H^{b(m-r)}
\bigl(B_Y\cap L_A^{-1}(Q)\bigr)
\,d\mathcal H^{br}(Q).
\]

This already shows that, except in the injective case, \(J(A)\) is not the entire transformed density.

### \(m=q\): square

For invertible \(A\),

\[
dQ=|\det A|^b\,dY,
\qquad
\boxed{J(A)=|\det A|^{-b}}.
\]

Hence

\[
\int_{B_Y}h(YA)\,dY
=
|\det A|^{-b}\int_{L_A(B_Y)}h(Q)\,dQ.
\]

The transformed domain depends on \(A\). The Jacobian blows up on \(\det A=0\).

### \(m<q\): injective

For full row-rank \(A\),

\[
d\mathcal H^{bm}(Q)=\det(AA^T)^{b/2}\,dY,
\]

so

\[
\boxed{J(A)=\det(AA^T)^{-b/2}}.
\]

Here \(Q\) ranges only over \((\operatorname{row}A)^b\), a \(bm\)-dimensional subspace of \(\mathbb R^{bq}\). After identifying this subspace isometrically with \(\mathbb R^{b\times m}\), the fixed-\(A\) core is a free \(b\times m\) core, not a free \(b\times q\) core.

The Jacobian blows up as \(A\) approaches rank \(<m\).

### \(m>q\): surjective

For full column-rank \(A\),

\[
\boxed{J(A)=\det(A^TA)^{-b/2}}.
\]

But the exact formula is

\[
\int_{B_Y}h(YA)\,dY
=
\det(A^TA)^{-b/2}
\int_{\mathbb R^{b\times q}}
h(Q)\,V_{A,B_Y}(Q)\,dQ,
\]

where

\[
V_{A,B_Y}(Q)
=
\mathcal H^{b(m-q)}
\bigl(B_Y\cap L_A^{-1}(Q)\bigr).
\]

Thus there is an additional fiber-section volume depending on both \(A\) and \(Q\). Again \(J\) blows up at rank \(<q\).

On any compact set separated from the rank-deficient locus, all these Jacobians are bounded. Across that locus they behave as \(\prod\sigma_i^{-b}\) and are unbounded.

## Q2. Is this a benign factor?

No.

There are three obstructions:

- For \(m<q\), the “free core” has effective column dimension \(m\), and its image subspace and scale depend on \(A\).
- For \(m>q\), the coarea formula contains the nonconstant fiber volume \(V_{A,B_Y}(Q)\).
- Even for \(m=q\), the transformed domain \(L_A(B_Y)\) shrinks as \(A\) degenerates.

As a standalone function of a free \(m\times q\) matrix,

\[
J(A)=
\begin{cases}
\det(AA^T)^{-b/2},&m\le q,\\[2mm]
\det(A^TA)^{-b/2},&m\ge q,
\end{cases}
\]

is itself a determinantal integral. Over a singularity-containing box,

\[
\int J(A)\,dA<\infty
\quad\Longleftrightarrow\quad
b<|m-q|+1.
\]

In particular, for \(m=q\), \(J=|\det A|^{-b}\) is never locally integrable for a positive integer \(b\). Nevertheless, the original integral can be finite because the transformed \(Q\)-domain shrinks.

For example, when \(b=m=q=1\), \(A=t\) and \(Y\in[-1,1]\),

\[
|t|^{-1}\int_{-|t|}^{|t|}|Q|^{-a}\,dQ
=
\frac{2}{1-a}|t|^{-a},
\qquad a<1.
\]

The factor \(|t|^{-1}\) is cancelled by the shrinking interval. Replacing that interval with a fixed “free core” would give the wrong answer even at \(a=0\).

### If \(A_{\mathrm{tail}}\) is itself a product

Let \(A_{\mathrm{tail}}=A_2\cdots A_L\).

- If \(m\le q\), then

  \[
  J(A_{\mathrm{tail}})
  =
  \det(A_{\mathrm{tail}}A_{\mathrm{tail}}^T)^{-b/2},
  \]

  which is the same problem for the shorter product \(A_2\cdots A_L\), with new row size \(m\) and new exponent \(a'=b\).

- If \(m\ge q\), then

  \[
  J(A_{\mathrm{tail}})
  =
  \det(A_{\mathrm{tail}}^TA_{\mathrm{tail}})^{-b/2},
  \]

  which is the same problem for the reversed transposed product
  \(A_L^T\cdots A_2^T\), with row size \(q\) and exponent \(a'=b\).

This is an exact algebraic recursion for the standalone \(J\)-integral. It is not by itself a recursion for \(I(a)\), because the image/fiber factors must be retained.

There is, however, a clean recursion for Gaussian-weighted integrals. If

\[
P=A_1\cdots A_L,\qquad
A_1\in\mathbb R^{b\times d_1},\quad
A_j\in\mathbb R^{d_{j-1}\times d_j},
\]

have independent standard Gaussian entries, then

\[
\mathbb E\det(PP^T)^{-a/2}
=
\prod_{j=1}^L M_{b,d_j}(a),
\]

where

\[
M_{b,n}(a)
=
2^{-ab/2}
\prod_{i=1}^b
\frac{\Gamma((n-i+1-a)/2)}
     {\Gamma((n-i+1)/2)}.
\]

Consequently the deep-product threshold is

\[
a<\min_j(d_j-b+1),
\]

provided every \(d_j\ge b\).

## Q3. Exact threshold for the original two-factor integral

Assume \(b\le\min(m,q)\). For any standard singularity-containing box,

\[
\boxed{
I(a)<\infty
\quad\Longleftrightarrow\quad
a<\min(m,q)-b+1.
}
\]

At equality there is divergence. If \(b>\min(m,q)\), then \(YA\) has rank \(<b\) identically, so \(I(a)=\infty\) for every \(a>0\).

Thus

\[
a_c=
\begin{cases}
q-b+1,&m\ge q,\\
m-b+1,&m<q.
\end{cases}
\]

The free \(b\times q\) threshold survives exactly when \(m\ge q\). A narrower intermediate dimension lowers it.

### Proof of sufficiency

Give \(Y\) and \(A\) independent standard Gaussian entries. Almost surely \(Y\) has full row rank. Write

\[
H=(YY^T)^{1/2},
\qquad
R=H^{-1}Y,
\qquad
RR^T=I_b.
\]

Conditionally on \(Y\), the matrix

\[
Z=RA
\]

is a standard Gaussian \(b\times q\) matrix, and its conditional law does not depend on \(Y\); hence \(Z\) is independent of \(Y\). Since \(YA=HZ\),

\[
\det(YAA^TY^T)
=
\det(YY^T)\det(ZZ^T).
\]

Therefore

\[
\mathbb E\det(YAA^TY^T)^{-a/2}
=
M_{b,m}(a)M_{b,q}(a).
\]

Bartlett decomposition gives

\[
\det(XX^T)\overset{d}{=}
\prod_{i=1}^b\chi^2_{n-i+1}
\]

for a Gaussian \(b\times n\) matrix \(X\). Its negative \(a/2\)-moment is finite exactly when

\[
a<n-b+1.
\]

This proves Gaussian integrability exactly for
\(a<\min(m,q)-b+1\). Since a Gaussian density is bounded below on every bounded box, it also proves local integrability on every bounded box below this threshold.

### Proof of necessity and local exponent

Near a generic rank-\((b-1)\) matrix \(X_0\in\mathbb R^{b\times n}\), analytic row and column coordinates give

\[
\det(XX^T)=u(X)\,\|z\|^2,
\]

where \(u(X_0)>0\) and \(z\in\mathbb R^{n-b+1}\) are normal coordinates. Hence the singular integral contains

\[
\int_0^\varepsilon r^{-a}r^{n-b}\,dr,
\]

which converges exactly when \(a<n-b+1\).

- If \(m<q\), take \(A\) full row rank. Then \(AA^T\) is positive definite and

  \[
  \det(YAA^TY^T)\asymp\det(YY^T).
  \]

  The normal dimension is \(m-b+1\).

- If \(m\ge q\), take \(A\) full column rank. Splitting \(Y\) into coordinates along \(\operatorname{col}A\) and its orthogonal complement reduces the singular part to a free \(b\times q\) matrix. The normal dimension is \(q-b+1\).

These witnesses may be scaled into any box having the origin in its interior.

### Explicit instances

#### \(b=1,m=1,q=2\)

Let \(Y=[y]\) and \(A=[u\ v]\). Then

\[
\det(QQ^T)=y^2(u^2+v^2).
\]

Thus

\[
\det(QQ^T)^{-a/2}
=
|y|^{-a}(u^2+v^2)^{-a/2}.
\]

The \(y\)-integral requires \(a<1\); polar coordinates in \((u,v)\) require \(a<2\). Therefore

\[
\boxed{a_c=1},
\]

whereas the free \(1\times2\) threshold is \(2\). This is the smallest counterexample.

#### \(b=1,m=2,q=3\)

Write

\[
Y=[x\ y],
\qquad
A=
\begin{pmatrix}
a&b&c\\
d&e&f
\end{pmatrix}.
\]

Then

\[
\det(QQ^T)
=
(ax+dy)^2+(bx+ey)^2+(cx+fy)^2
\]

or explicitly

\[
x^2(a^2+b^2+c^2)
+2xy(ad+be+cf)
+y^2(d^2+e^2+f^2).
\]

Near any full-row-rank \(A_0\), this quadratic form is comparable to \(x^2+y^2\). Hence

\[
\int_{\mathbb R^2}(x^2+y^2)^{-a/2}\,dx\,dy
\]

has threshold \(a=2\). The general sufficiency proof handles neighborhoods where \(A\) degenerates. Therefore

\[
\boxed{a_c=2},
\]

versus the free \(1\times3\) value \(3\).

#### \(b=2,m=2,q=3\)

Let

\[
Y=
\begin{pmatrix}x&y\\z&w\end{pmatrix},
\qquad
A=
\begin{pmatrix}a&b&c\\d&e&f\end{pmatrix}.
\]

Cauchy–Binet gives the exact factorization

\[
\det(QQ^T)
=
(xw-yz)^2
\left[(ae-bd)^2+(af-cd)^2+(bf-ce)^2\right].
\]

Equivalently,

\[
\det(QQ^T)=\det(Y)^2\det(AA^T).
\]

Thus the integral factors into

\[
\int |\det Y|^{-a}\,dY
\quad\text{and}\quad
\int \det(AA^T)^{-a/2}\,dA.
\]

The first has threshold \(1\), because \(\det Y=0\) is a smooth hypersurface at generic rank-one matrices. The second is the free \(2\times3\) core and has threshold \(2\). Therefore

\[
\boxed{a_c=1},
\]

again below the free value \(2\).

## Q4. Does the rank-deficient tail locus matter?

As a set, it is Lebesgue-null, so changing the integrand on that exact locus does not change \(I(a)\). It is possible for the fixed-\(A\) inner integral to equal \(+\infty\) on this null set while the full double integral remains finite.

Its neighborhoods cannot, however, be discarded when using the change of variables: \(J(A)\) blows up there, while the transformed image or fiber volume simultaneously shrinks. Only their product has analytic meaning.

- For \(m\ge q\), the generic map \(Y\mapsto YA\) is surjective. The exact threshold is \(q-b+1\), equal to the free core. Divergence at and above this threshold already occurs for \(A\) in an open set bounded away from rank deficiency. The rank-deficient locus imposes no additional restriction.

- For \(m<q\), the generic map is injective into a moving \(m\)-plane. The threshold is \(m-b+1\), smaller than \(q-b+1\). This loss also occurs for \(A\) bounded away from rank deficiency; it is caused by the effective \(b\times m\) core, not by the null rank-drop locus. Near rank drop, the blow-up of \(J\) must be paired with the shrinking image.

If \(A_{\mathrm{tail}}\) is a deeper product with an internal width below \(\min(m,q)\), then \(\operatorname{rank}A_{\mathrm{tail}}<\min(m,q)\) is generic rather than null. In that case the full-rank Jacobian formulas are inapplicable, and the narrower internal width enters the deep threshold \(\min_j(d_j-b+1)\).
tokens used
63,884
Let \(A=A_{\mathrm{tail}}\), and let \(L_A(Y)=YA\).

First, a necessary domain qualification: there is no threshold depending only on \((b,m,q)\) for an arbitrary translated box. If the box is sufficiently small around a pair with \(\operatorname{rank}(YA)=b\), then \(\det(YAA^{T}Y^{T})\) is bounded below and \(I(a)<\infty\) for every \(a\). The stated free-core threshold likewise assumes that the \(Q\)-box meets the rank-\((b-1)\) locus.

Below, “the threshold” means the standard singular local problem: the box contains the origin, or more generally contains a generic point of the rank-deficient locus described below.

## Q1. Exact Jacobian

Let \(r=\operatorname{rank}A\), with nonzero singular values
\(\sigma _1,\dots,\sigma _r\). The linear map \(Y\mapsto YA\) is the direct sum of \(b\) copies of \(\mathbb R^m\to\mathbb R^q,\ y\mapsto yA\). Its forward \(br\)-dimensional Jacobian is

\[
D_r(A)=\left(\prod_{i=1}^r \sigma_i\right)^b
       =\det\nolimits^{+}(AA^T)^{b/2}
       =\det\nolimits^{+}(A^TA)^{b/2},
\]

where \(\det^{+}\) is the product of the nonzero eigenvalues. Thus the inverse Jacobian appearing in the proposed formula is

\[
J_r(A)=D_r(A)^{-1}=\prod_{i=1}^r\sigma_i^{-b}.
\]

The exact coarea identity is

\[
\int_{B_Y} h(YA)\,dY
=
J_r(A)
\int_{(\operatorname{row}A)^b}
h(Q)\,
\mathcal H^{b(m-r)}
\bigl(B_Y\cap L_A^{-1}(Q)\bigr)
\,d\mathcal H^{br}(Q).
\]

This already shows that, except in the injective case, \(J(A)\) is not the entire transformed density.

### \(m=q\): square

For invertible \(A\),

\[
dQ=|\det A|^b\,dY,
\qquad
\boxed{J(A)=|\det A|^{-b}}.
\]

Hence

\[
\int_{B_Y}h(YA)\,dY
=
|\det A|^{-b}\int_{L_A(B_Y)}h(Q)\,dQ.
\]

The transformed domain depends on \(A\). The Jacobian blows up on \(\det A=0\).

### \(m<q\): injective

For full row-rank \(A\),

\[
d\mathcal H^{bm}(Q)=\det(AA^T)^{b/2}\,dY,
\]

so

\[
\boxed{J(A)=\det(AA^T)^{-b/2}}.
\]

Here \(Q\) ranges only over \((\operatorname{row}A)^b\), a \(bm\)-dimensional subspace of \(\mathbb R^{bq}\). After identifying this subspace isometrically with \(\mathbb R^{b\times m}\), the fixed-\(A\) core is a free \(b\times m\) core, not a free \(b\times q\) core.

The Jacobian blows up as \(A\) approaches rank \(<m\).

### \(m>q\): surjective

For full column-rank \(A\),

\[
\boxed{J(A)=\det(A^TA)^{-b/2}}.
\]

But the exact formula is

\[
\int_{B_Y}h(YA)\,dY
=
\det(A^TA)^{-b/2}
\int_{\mathbb R^{b\times q}}
h(Q)\,V_{A,B_Y}(Q)\,dQ,
\]

where

\[
V_{A,B_Y}(Q)
=
\mathcal H^{b(m-q)}
\bigl(B_Y\cap L_A^{-1}(Q)\bigr).
\]

Thus there is an additional fiber-section volume depending on both \(A\) and \(Q\). Again \(J\) blows up at rank \(<q\).

On any compact set separated from the rank-deficient locus, all these Jacobians are bounded. Across that locus they behave as \(\prod\sigma_i^{-b}\) and are unbounded.

## Q2. Is this a benign factor?

No.

There are three obstructions:

- For \(m<q\), the “free core” has effective column dimension \(m\), and its image subspace and scale depend on \(A\).
- For \(m>q\), the coarea formula contains the nonconstant fiber volume \(V_{A,B_Y}(Q)\).
- Even for \(m=q\), the transformed domain \(L_A(B_Y)\) shrinks as \(A\) degenerates.

As a standalone function of a free \(m\times q\) matrix,

\[
J(A)=
\begin{cases}
\det(AA^T)^{-b/2},&m\le q,\\[2mm]
\det(A^TA)^{-b/2},&m\ge q,
\end{cases}
\]

is itself a determinantal integral. Over a singularity-containing box,

\[
\int J(A)\,dA<\infty
\quad\Longleftrightarrow\quad
b<|m-q|+1.
\]

In particular, for \(m=q\), \(J=|\det A|^{-b}\) is never locally integrable for a positive integer \(b\). Nevertheless, the original integral can be finite because the transformed \(Q\)-domain shrinks.

For example, when \(b=m=q=1\), \(A=t\) and \(Y\in[-1,1]\),

\[
|t|^{-1}\int_{-|t|}^{|t|}|Q|^{-a}\,dQ
=
\frac{2}{1-a}|t|^{-a},
\qquad a<1.
\]

The factor \(|t|^{-1}\) is cancelled by the shrinking interval. Replacing that interval with a fixed “free core” would give the wrong answer even at \(a=0\).

### If \(A_{\mathrm{tail}}\) is itself a product

Let \(A_{\mathrm{tail}}=A_2\cdots A_L\).

- If \(m\le q\), then

  \[
  J(A_{\mathrm{tail}})
  =
  \det(A_{\mathrm{tail}}A_{\mathrm{tail}}^T)^{-b/2},
  \]

  which is the same problem for the shorter product \(A_2\cdots A_L\), with new row size \(m\) and new exponent \(a'=b\).

- If \(m\ge q\), then

  \[
  J(A_{\mathrm{tail}})
  =
  \det(A_{\mathrm{tail}}^TA_{\mathrm{tail}})^{-b/2},
  \]

  which is the same problem for the reversed transposed product
  \(A_L^T\cdots A_2^T\), with row size \(q\) and exponent \(a'=b\).

This is an exact algebraic recursion for the standalone \(J\)-integral. It is not by itself a recursion for \(I(a)\), because the image/fiber factors must be retained.

There is, however, a clean recursion for Gaussian-weighted integrals. If

\[
P=A_1\cdots A_L,\qquad
A_1\in\mathbb R^{b\times d_1},\quad
A_j\in\mathbb R^{d_{j-1}\times d_j},
\]

have independent standard Gaussian entries, then

\[
\mathbb E\det(PP^T)^{-a/2}
=
\prod_{j=1}^L M_{b,d_j}(a),
\]

where

\[
M_{b,n}(a)
=
2^{-ab/2}
\prod_{i=1}^b
\frac{\Gamma((n-i+1-a)/2)}
     {\Gamma((n-i+1)/2)}.
\]

Consequently the deep-product threshold is

\[
a<\min_j(d_j-b+1),
\]

provided every \(d_j\ge b\).

## Q3. Exact threshold for the original two-factor integral

Assume \(b\le\min(m,q)\). For any standard singularity-containing box,

\[
\boxed{
I(a)<\infty
\quad\Longleftrightarrow\quad
a<\min(m,q)-b+1.
}
\]

At equality there is divergence. If \(b>\min(m,q)\), then \(YA\) has rank \(<b\) identically, so \(I(a)=\infty\) for every \(a>0\).

Thus

\[
a_c=
\begin{cases}
q-b+1,&m\ge q,\\
m-b+1,&m<q.
\end{cases}
\]

The free \(b\times q\) threshold survives exactly when \(m\ge q\). A narrower intermediate dimension lowers it.

### Proof of sufficiency

Give \(Y\) and \(A\) independent standard Gaussian entries. Almost surely \(Y\) has full row rank. Write

\[
H=(YY^T)^{1/2},
\qquad
R=H^{-1}Y,
\qquad
RR^T=I_b.
\]

Conditionally on \(Y\), the matrix

\[
Z=RA
\]

is a standard Gaussian \(b\times q\) matrix, and its conditional law does not depend on \(Y\); hence \(Z\) is independent of \(Y\). Since \(YA=HZ\),

\[
\det(YAA^TY^T)
=
\det(YY^T)\det(ZZ^T).
\]

Therefore

\[
\mathbb E\det(YAA^TY^T)^{-a/2}
=
M_{b,m}(a)M_{b,q}(a).
\]

Bartlett decomposition gives

\[
\det(XX^T)\overset{d}{=}
\prod_{i=1}^b\chi^2_{n-i+1}
\]

for a Gaussian \(b\times n\) matrix \(X\). Its negative \(a/2\)-moment is finite exactly when

\[
a<n-b+1.
\]

This proves Gaussian integrability exactly for
\(a<\min(m,q)-b+1\). Since a Gaussian density is bounded below on every bounded box, it also proves local integrability on every bounded box below this threshold.

### Proof of necessity and local exponent

Near a generic rank-\((b-1)\) matrix \(X_0\in\mathbb R^{b\times n}\), analytic row and column coordinates give

\[
\det(XX^T)=u(X)\,\|z\|^2,
\]

where \(u(X_0)>0\) and \(z\in\mathbb R^{n-b+1}\) are normal coordinates. Hence the singular integral contains

\[
\int_0^\varepsilon r^{-a}r^{n-b}\,dr,
\]

which converges exactly when \(a<n-b+1\).

- If \(m<q\), take \(A\) full row rank. Then \(AA^T\) is positive definite and

  \[
  \det(YAA^TY^T)\asymp\det(YY^T).
  \]

  The normal dimension is \(m-b+1\).

- If \(m\ge q\), take \(A\) full column rank. Splitting \(Y\) into coordinates along \(\operatorname{col}A\) and its orthogonal complement reduces the singular part to a free \(b\times q\) matrix. The normal dimension is \(q-b+1\).

These witnesses may be scaled into any box having the origin in its interior.

### Explicit instances

#### \(b=1,m=1,q=2\)

Let \(Y=[y]\) and \(A=[u\ v]\). Then

\[
\det(QQ^T)=y^2(u^2+v^2).
\]

Thus

\[
\det(QQ^T)^{-a/2}
=
|y|^{-a}(u^2+v^2)^{-a/2}.
\]

The \(y\)-integral requires \(a<1\); polar coordinates in \((u,v)\) require \(a<2\). Therefore

\[
\boxed{a_c=1},
\]

whereas the free \(1\times2\) threshold is \(2\). This is the smallest counterexample.

#### \(b=1,m=2,q=3\)

Write

\[
Y=[x\ y],
\qquad
A=
\begin{pmatrix}
a&b&c\\
d&e&f
\end{pmatrix}.
\]

Then

\[
\det(QQ^T)
=
(ax+dy)^2+(bx+ey)^2+(cx+fy)^2
\]

or explicitly

\[
x^2(a^2+b^2+c^2)
+2xy(ad+be+cf)
+y^2(d^2+e^2+f^2).
\]

Near any full-row-rank \(A_0\), this quadratic form is comparable to \(x^2+y^2\). Hence

\[
\int_{\mathbb R^2}(x^2+y^2)^{-a/2}\,dx\,dy
\]

has threshold \(a=2\). The general sufficiency proof handles neighborhoods where \(A\) degenerates. Therefore

\[
\boxed{a_c=2},
\]

versus the free \(1\times3\) value \(3\).

#### \(b=2,m=2,q=3\)

Let

\[
Y=
\begin{pmatrix}x&y\\z&w\end{pmatrix},
\qquad
A=
\begin{pmatrix}a&b&c\\d&e&f\end{pmatrix}.
\]

Cauchy–Binet gives the exact factorization

\[
\det(QQ^T)
=
(xw-yz)^2
\left[(ae-bd)^2+(af-cd)^2+(bf-ce)^2\right].
\]

Equivalently,

\[
\det(QQ^T)=\det(Y)^2\det(AA^T).
\]

Thus the integral factors into

\[
\int |\det Y|^{-a}\,dY
\quad\text{and}\quad
\int \det(AA^T)^{-a/2}\,dA.
\]

The first has threshold \(1\), because \(\det Y=0\) is a smooth hypersurface at generic rank-one matrices. The second is the free \(2\times3\) core and has threshold \(2\). Therefore

\[
\boxed{a_c=1},
\]

again below the free value \(2\).

## Q4. Does the rank-deficient tail locus matter?

As a set, it is Lebesgue-null, so changing the integrand on that exact locus does not change \(I(a)\). It is possible for the fixed-\(A\) inner integral to equal \(+\infty\) on this null set while the full double integral remains finite.

Its neighborhoods cannot, however, be discarded when using the change of variables: \(J(A)\) blows up there, while the transformed image or fiber volume simultaneously shrinks. Only their product has analytic meaning.

- For \(m\ge q\), the generic map \(Y\mapsto YA\) is surjective. The exact threshold is \(q-b+1\), equal to the free core. Divergence at and above this threshold already occurs for \(A\) in an open set bounded away from rank deficiency. The rank-deficient locus imposes no additional restriction.

- For \(m<q\), the generic map is injective into a moving \(m\)-plane. The threshold is \(m-b+1\), smaller than \(q-b+1\). This loss also occurs for \(A\) bounded away from rank deficiency; it is caused by the effective \(b\times m\) core, not by the null rank-drop locus. Near rank drop, the blow-up of \(J\) must be paired with the shrinking image.

If \(A_{\mathrm{tail}}\) is a deeper product with an internal width below \(\min(m,q)\), then \(\operatorname{rank}A_{\mathrm{tail}}<\min(m,q)\) is generic rather than null. In that case the full-rank Jacobian formulas are inapplicable, and the narrower internal width enters the deep threshold \(\min_j(d_j-b+1)\).
