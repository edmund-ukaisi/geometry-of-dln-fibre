# Bedrock

*The standard, beyond "it compiles" — sorry-free, axiom-clean, and the rest — by which a formalised result
becomes foundation rather than fill, and the taste by which we judge it.*

## Two kinds of slop

> "there is technical slop and conceptual slop (= technically correct but subtly wrong) and
> we'll discover the latter is a big problem once we sidestep the former."

"It compiles" is itself layered: no `sorry`, no smuggled axiom (`#print axioms` clean), no `native_decide`
standing in for a proof. Pass every one of those and you have defeated *technical* slop entirely — and still
done nothing about *conceptual* slop: the theorem that is technically correct and subtly wrong, that compiles
and misleads. Its plainest form needs no exotic check at all — a theorem whose hypotheses are never met is
sorry-free, axiom-clean, and says nothing. Conceptual slop survives every mechanical check, because the
mechanical checks are exactly what it satisfies. Bedrock is the standard for the rest.

## The rising sea

> "the sea advances insensibly in silence, nothing seems to happen, nothing moves, the water is so far off
> you hardly hear it … yet it finally surrounds the resistant substance."
> — Grothendieck, on coming to understand (*Récoltes et Semailles*; via McLarty, *The Rising Sea*)

Ours is the [rising-sea school](https://therisingsea.org/). One does not, in this tradition, go directly at
the hard theorem; one raises the surrounding theory — patiently, "you do have something you want to do, but
you're patient about it" — until the problem is *submerged, and falls away*. That is the shape of the work
here: we do not assault the RLCT directly. We build the quiver-orbit translation, the rank-pattern
combinatorics, and the `Ext`-codimension layer, and let the sea rise toward the `rlct = ½·codim` payoff.

But a rising sea is only as good as what it is made of. **Bedrock is the rock the sea rises over.** A result
that is not bedrock is just water — it raises the level without bearing weight. The discipline of bedrock is
the discipline of building a sea you can stand in.

**The sea rises inexorably, but not in spikes.** Inexorably: the patient pace still *arrives* — one does not
stop short. But *level* — the water comes up over the whole rock at once, never a thin spike racing far ahead
with holes behind it. Racing the boundary outward for a headline while the interior stays unfilled is the
move-fast-and-break-things instinct, the antithesis of bedrock: the spike bears no weight, and whatever stacks
on it inherits the holes. So **fill the layer before you climb** — within a boundary already staked, close the
holes (the generality the statement promised, the cases it already claims, fidelity to the definition and the
underlying spirit it invokes); a hole left behind a broad-named result *is* a spike. For us this is also where
comparative advantage lies: such hardening and completion are high-value, and our bottleneck is scoping, taste,
and direction — not the patient completion of well-scoped work, which is abundant and must not be treated as if
it were scarce. It is the work to **do**, not defer (a "chore" deferred is usually an unprobed cost and a hole
left behind). Moving the boundary into new territory is the different act — and the one that needs direction.

## The refutation dialectic — don't stop at a monster or a weak theorem

The frontier between a counterexample and a no-go is itself a layer to fill. A lone counterexample (an
unexplained "monster") and a hypothesis-padded weak theorem (one monster-barred just enough to be true) are
*both* spikes — they leave the dividing line unmapped. Bedrock here is the **sharp characterization**: the
weakest hypotheses under which the theorem holds, with the counterexample lying exactly the other side of
them.

Reach it by the proofs-and-refutations loop (Lakatos), **mediated by the controller**:
- a **counterexample** found ⟹ examine the obstruction and **narrow the theorem** to the weakest hypothesis
  that excludes *exactly* it — the *right* hypothesis, not a blunt extra assumption;
- a **theorem** in hand ⟹ hypothesise a **reasonable strengthening** (relax or drop a hypothesis) that might
  re-admit a counterexample, and hunt it;
- iterate until the positive and negative sides **meet at the same boundary** and it is stable.

A counterexample is not the end of the negative program, nor a theorem the end of the positive one. The
deliverable is the converged statement — named at its true scope ([`precision.md`](precision.md)), its beauty
(the *exact* hypothesis that suffices) the signal that the line is right.

**The hunt precedes trust; an empty hunt is not a proof.** Bedrock for a universal, negative, or
exhaustiveness claim ("holds for all", "no counterexample exists", "the case-split is complete") is the
**proof** — the converged characterization above. Until that proof is in hand the claim is **not
established**: at most a *scoped negative result* ("searched these architectures / configs / gate patterns,
found no counterexample"), named as such and carrying its search scope (a full deliverable — the
negative-results disposition in [`../../CLAUDE.md`](../../CLAUDE.md) — never dressed as "locked" or proved).
The **decorrelated adversarial search** (a counterexample hunt, run independently of whoever built the claim)
is the *instrument*, not the certificate: a **review** reads the proof you have and confirms the cases shown;
a **hunt** attacks the claim you do *not yet* have a proof of and surfaces the case *missed* — and
completeness/exhaustiveness failures are exactly what review structurally passes over (a hardener PASS on
"the split is exhaustive" certifies the branches written, not the stratum forgotten). So a decorrelated hunt
is **mandatory before such a claim is trusted** — it refutes the false ones early — and when it comes up
empty it yields the scoped evidence, never the theorem.

**The instrument is part of the claim — verify it measures the right object.** A hunt, a check, a verdict
is only as good as the object it actually computes; a flawless search of the *wrong* object certifies
nothing, and the failure hides because every mechanical step passes. So the discipline that holds the claim
holds the *instrument* first: before trusting an empty hunt or a green check, confirm the quantity measured
is the quantity claimed. The failure recurs across layers — a `float` rank at a tolerance read as the exact
rank; a straight-ray leading order read as the Morse–Bott residual order (the rank-`ρ` elimination not
performed); a byte offset read as a display column; a stale working-tree snapshot read as the live file —
each a *correct* computation of the *wrong* object. The guard mirrors the claim: exact arithmetic where the
claim is exact, the post-elimination invariant where it concerns the residual, the convention's unit where it
concerns a limit, the current artifact where it concerns the code. This binds the reviewer's own tooling
before anything under review — a false positive from a mis-measured instrument is the same conceptual slop,
one level in.

The mechanism for running such a pair lives in [`expedition.md`](expedition.md) § mediating a positive/negative pair.

## Beauty is the instrument

When the work goes "substantially outside the borders of the known, or grappling with things deep enough that
short feedback loops are not available" — which is most of formalised research — there is no oracle to check
against. Then:

> "one of the most objectively reliable signals to follow is a sense of beauty, which is a kind of distilled
> indicator of generalisation obtained from shorter trips into the unknown or from grappling with slightly
> less deep things, compounded over time."

Beauty is not decoration. A vacuous theorem, a mis-scoped definition, a name that promises more than it
proves — these are *ugly*, and the ugliness is information. The exact statement, the weakest hypothesis that
suffices, the clean characterization — these are *beautiful*, and the beauty is a signal of generalisation.
We feel our way "towards the deep end of the pool by having a good sense of taste and seeing where it leads."

## The base is audited hardest

A foundational result is what everything else *tags to* — the bottom of a vertical slice. It inherits its
flaws upward: a base that is subtly wrong silently corrupts all that stands on it. So the base is held to the
highest standard — *"a clean pass validates the bedrock,"* while a wrong definition at the bottom *"would
undermine all of them."* Find the base of each piece of work, and audit it hardest.

## The taste, provisionally crystallized

Taste is not a checklist, and the operational signs of bedrock shift with the mathematics. But some recur
often enough to enumerate — a **working list, necessary but not exhaustive**, revised as new modes of
conceptual slop surface. A result built to bedrock should, *at least and without limitation*:

1. **Statement & naming** —
   1. name the result for its content, not its aspiration (a membership fact is `…_mem_ker`, not `…_gen`);
   2. separate Proved / Assumed / Cited / Deferred in statement and docstring ([`precision.md`](precision.md));
   3. carry the *weakest* hypotheses that suffice — drop unused ones rather than leave them decorative (an
      unused hypothesis that looks load-bearing lies about the content).
2. **Non-vacuity** —
   1. commit an in-file witness (an `example`) that each new predicate is inhabited and each load-bearing
      antecedent is satisfiable — not merely an external check;
   2. where two mechanisms might coincide, witness their *independence* (each fires without the other);
   3. for **computational evidence** (a script / numerical certificate cited for a claim), commit it to
      **reproduce its stated headline on a clean re-run** — a script whose re-run contradicts its own printed
      verdict is conceptual slop (it computes and misleads, the runtime analogue of a vacuous theorem); re-run
      cited scripts, never promote a *relayed* headline.
3. **Form & usability** —
   1. state the result as a later result would apply it (usable API), not as it was easiest to prove;
   2. prefer a characterization (`iff`) to a one-directional or incidence-only predicate, where it holds;
   3. do not dress a definitional unfolding as a theorem (`rfl`-packaging).
4. **Interfaces** —
   1. tag every *cited* (external, not reproved) and *assumed* (carried, not discharged) step; never let a
      name assert an interface that is not proved (no `…rlct…`-style theorem for an unproved analytic step);
   2. carry an assumption as a named hypothesis in the statement, not silently in the ambient context.
5. **Verification** —
   1. clear the sorry-gate and `#print axioms` on each gate theorem — only the expected axioms;
   2. audit the dependency-base hardest, with a decorrelated second model and an adversarial in-Lean witness;
   3. for a **universal / negative / exhaustiveness** claim, the gate is a **proof**; absent it the claim is a
      *scoped negative result*, never "established" — and a **decorrelated counterexample hunt** must have
      attacked it and failed before it is trusted (review confirms the cases shown; the hunt surfaces the case
      missed — § the refutation dialectic).

And, deepest and least reducible to any clause: *is this even **the right object**?* — which no enumeration
captures, and which lives in judgement and the sense of beauty.

These are crystallizations of the taste, not the taste itself.

## Lineage

The rising sea is Grothendieck's image (via McLarty, *The Rising Sea: Grothendieck on Simplicity and
Generality*); the refutation dialectic is Lakatos's *method of proofs and refutations* (Imre Lakatos,
*Proofs and Refutations: The Logic of Mathematical Discovery*, ed. Worrall & Zahar, Cambridge University
Press, 1976). The rest are our own, collaboratively-generated principles — phrasing borrowed freely and held
as ours, no inline citation intended. **Who holds this taste, and the cadence for applying it, live in
[`expedition.md`](expedition.md)** (the controller judges formalised work against it; a green build is
necessary, never sufficient; the judgement takes precedence). An independent **hardener**
([`../../.agent-team/roles/hardener.md`](../../.agent-team/roles/hardener.md)) applies this taste as a
standing, decorrelated review function — surfacing overclaims, holes, *and the right extensions* — which the
controller integrates and holds precedence over. Working summaries are in
[`../../CLAUDE.md`](../../CLAUDE.md) and [`../../lean/CLAUDE.md`](../../lean/CLAUDE.md). In-repo kin:
[`precision.md`](precision.md) · [`review.md`](review.md) · [`expedition.md`](expedition.md) ·
[`library-building.md`](library-building.md).
