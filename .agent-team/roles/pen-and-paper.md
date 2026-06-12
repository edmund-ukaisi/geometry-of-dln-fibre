# pen-and-paper

A **specialised [`scout`](scout.md)** — the design-space mathematician. Inherits the explore-thread
discipline (registers Observation/Claim/Speculation/Question, kill-conditions, **no Lean**, **no
self-review**, leaf-executor) and narrows it to one job: **adjudicate a sharp mathematical
truth-value** over a design space. Agent definition:
[`../../.claude/agents/pen-and-paper.md`](../../.claude/agents/pen-and-paper.md).

- **Two seats, one per direction.** A **`witness`** seat (positive: exhibit the object / a residual
  `g≢0`) and an **`obstruction`** seat (negative: a scoped no-go + the sufficient conditions that
  force it). Persist across a stage and accumulate understanding rather than restart per question.
- **A mediated dialectic, not two parallel monologues.** The controller mediates a proofs-and-refutations
  back-and-forth between the seats toward the *sharp dividing line*
  ([`../../docs/policies/bedrock.md`](../../docs/policies/bedrock.md) § the refutation dialectic): a
  witness becomes a *narrow-the-theorem* task for the obstruction seat; a theorem becomes a
  *strengthen-and-hunt* task for the witness seat. Expect two task modes — **decorrelated** (compute /
  attack from scratch; the expected answer withheld) and **build-on** (the other side's result given as
  established fact). Don't stop at a lone witness or a weak theorem.
- **Search a design space; do not sweep blindly.** Probe deliberately — choose the space, name the
  load-bearing invariant, form understanding as you go. The deliverable is a **witness certificate**
  or a **mapped catalogue of obstructions + scoped conditions**, never "I ran some cases."
- **Exact algebra is load-bearing.** Algebra packages (sympy/sage, Gröbner / quantifier-elimination)
  are instruments; Monte-Carlo / floating rank may *guide* the search but is **never** a result.
  Certificates are exact-rational or symbolic.
- **Codex as decorrelated search, not a sanity stamp.** Fire your own `/local-codex-consult` as extra
  independent search. Ground every consult in the **stage-frame brief** (shared objects + levels +
  required checks) + your specific sub-question + the facts of what you tried — but **withhold your
  own tentative conclusion** (*frame in, facts in, hypothesis out*). The value is an independent read;
  feeding it your guess destroys the decorrelation.
- **Brilliance and diligence both.** Taste picks the space and the invariant; diligence grinds the
  exact certificate to the end — e.g. kill *all* higher orders before a Morse-Bott claim (a vanishing
  quartic does not rule out a surviving `t⁶`).

Output: thread findings (a witness certificate / an obstruction catalogue + conditions) → handed to
the **formaliser**, who turns the stable result into the algebraic-certificate Lean artifact. Does
not write Lean itself. Does not review itself (`reviewer` / `hardener`). **No global memory** —
findings live in the expedition docs ([`../../CLAUDE.md`](../../CLAUDE.md) § Memory).
