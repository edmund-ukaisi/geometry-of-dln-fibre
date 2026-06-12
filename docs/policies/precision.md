# Mathematical precision

How we name and state results. The rule is one sentence: **a result's name and statement denote
exactly what is proven — no more.**

## Precision, not (just) honesty

This is a discipline of **precision**, and of resisting a specific tendency — not a matter of
sincerity. The failure mode is the gravitational pull toward framing that makes work look more
finished, more general, or more impressive than it is: a better-sounding name (`rlct_…` for a
volume fact), the word "done" while the hard step is assumed, a hypothesis quietly carried in the
proof but absent from the headline. Each step feels like progress. None is a lie. All are
imprecision, and they compound — a chain built on an overstated link is not stackable. This is the
**visible-progress instinct** ([`../../CLAUDE.md`](../../CLAUDE.md)) applied to naming and scope.

## The four statuses, co-located

State every result by separating, in the same place, what is:

- **Proved** — established unconditionally, by us, in Lean (or by a complete argument we give).
- **Assumed** — hypotheses the statement carries (the things that must hold for it to apply).
- **Cited** — used from an external source, not reproved here (name the source).
- **Deferred** — the reduction or step that would make the impressive reading true, but is *not*
  done. Name it; do not omit it.

A reader must be able to tell these apart without reading the proof. The statement card
([`statement-cards.md`](statement-cards.md)) carries these as explicit lines.

## Naming rule

Names denote content, not aspiration. Lean theorem / def / file names, claim titles, exposition
titles, and statement-card headlines all name **what is proved**. If a result `X` holds only under
hypothesis `H`, or only after a reduction `R` that is not formalised, the name does not assert `X` —
it names the actual content, or names `H`/`R`.

> **Worked example.** A lemma computing the codimension `codim mult⁻¹(B) = C` of a multiplication
> fibre is a *codimension* fact about the quiver-orbit geometry. Naming it
> `rlct_mult_fiber_eq_half_codim` asserts a learning coefficient (RLCT) — which additionally needs the
> general bound `rlct ≤ ½·codim` to be an *equality* here, an analytic step we **Cite** to Aoyagi /
> Watanabe, not reprove. The honest name is `multFiber_codim_eq` (or `…_hasCodim`); "RLCT = C/2" is a
> **Cited** reading, stated as such. (See `docs/expositions/paper-digest/high-level-overview.md` §9.)

## Completeness corollary

Do not call a result — or an expedition — **done** while its **load-bearing** step is merely
**Assumed** or **Deferred**. The load-bearing step is the one that makes the stated result mean what
it says (e.g. proving `codim mult⁻¹(B) = C` from the quiver-orbit codimension formula, rather than assuming it). When the
load-bearing step is open, you have two honest moves: **rename/restate** to the scope actually
proved, or **reopen** and prove it. "Park it as a successor and declare victory" is the failure mode.

Distinguish:
- **load-bearing** gap — must be *attempted*, not deferred (the controller pushes for it; see
  [`expedition.md`](expedition.md) § Supervising the formaliser);
- **genuinely-separate** extension — a different result that the current claim does not pretend to
  cover; legitimately future, and bounding it is good scope discipline, not over-selling.

The line between them is exactly: *does the stated result already claim it?* If yes, it is
load-bearing; if no, it is separate.

## Scope is content; "chore" is unprobed difficulty

A statement promises a *scope*, and the scope is part of what the name asserts. Proving `X` for
one instance — one architecture, one worked example — while the name or framing reads as `X` in
general is the same overclaim as the `rlct_…` case above: the instance is a *worked example* and
must be named as one (the name carries the instance — the special case, the particular
architecture — not the general claim). The honest moves are the corollary's — **fill it** (prove
the general `X`; and if it sits *inside* a boundary the claim already stakes, that is hardening
within reach, to be done rather than deferred — [`bedrock.md`](bedrock.md), *the sea rises … not
in spikes*), or **restate** to the instance proved *and contemplate whether the general case is
within reach*.

And **"chore" is an unprobed difficulty claim, not a license to defer.** "A mechanical chore"
asserts a gap is cheap — a claim earned by *probing*, exactly as "the frontier" asserts it is hard.
An unprobed "chore" pre-judges the cost *and*, if the broad name stands, leaves a hole behind the
boundary. Probe first: a genuinely-cheap in-boundary completion is to be *done*; a gap that hides
content is the frontier, named as such.

**The symmetric twin.** "A trivial chore" guesses a gap is *cheap*; "out of scope — it would need
the sealed base reopened" guesses it is *beyond reach*. Both are feasibility guesses — earned by
*trying*, not by reading the code. Reading shows what depends on what; it does not show whether the
gap is within reach — whether you can sidestep the obstacle by adding new code *beside* the locked
code instead of changing it. So before you put a gap beyond the boundary, attempt it, even as a
rough sketch: a within-reach extension shows itself, and only a real attempt earns "the frontier."

## Cross-references
- Disposition: [`../../CLAUDE.md`](../../CLAUDE.md) (the visible-progress instinct).
- Review function that enforces it: [`review.md`](review.md) (*Mathematical precision*).
- Where the four statuses live on a formalised result: [`statement-cards.md`](statement-cards.md).
- Claims: [`claims.md`](claims.md).
