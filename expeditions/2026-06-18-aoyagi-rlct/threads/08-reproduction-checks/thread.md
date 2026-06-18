# Thread 08 - reproduction checks

Type: pen-and-paper/review. Status: pending.

## Task

For each substantial Aoyagi calculation, produce or check a pen-and-paper
reproduction before the controller treats the corresponding claim as
formalisation-ready.

## Output contract

For each source cluster, record a reproduction artifact with:

- exact source hypotheses and notation;
- a step-by-step re-derivation, not a summary;
- boundary and degenerate cases checked explicitly;
- the precise place where the cited analytic interface is used, if any;
- kill-conditions and any unresolved ambiguity.

Then record a separate checker verdict:

- source fidelity against Aoyagi's PDF;
- mathematical correctness of the reproduced derivation;
- whether the result is ready for Lean, needs more reproduction, or should be
  moved to Cited/Deferred.

## Controller notes

This is a standing gate, not a single final audit. It applies to block/product
reduction, deepest-singular-point probe, blow-up recursion, arithmetic tail,
notation translation, and final assembly.
