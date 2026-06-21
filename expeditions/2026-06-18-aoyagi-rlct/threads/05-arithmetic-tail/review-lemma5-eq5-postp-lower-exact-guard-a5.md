# Review - Lemma 5 Eq5 post-p lower exact guard

Status: reviewed and formalised.

## Scope

This slice identifies the exact local lower-bound condition for a supplied
equation `(5)` post-`p` branch value to lie in the same-coordinate Htilde
interval.  It also records a sufficient terminal-room condition and a concrete
counterexample showing that the strict alpha domain plus post-`p` range is not
enough.

## Verdict

Survived.  No fidelity or claim-soundness findings.  The theorem names only
local finite arithmetic and keeps source construction and source-derived guard
production explicit.

## Checks

Focused Lean checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5DisplayedVector.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5DisplayedVector
lake build DLNFibre
lake env lean DLNFibre.lean
scripts/sorries
git diff --check
```

xhigh pen-and-paper scout `Bohr` independently derived the exact iff, the
terminal-room sufficient condition, and the all-widths-four counterexample
mechanism.

Independent xhigh reviewer `Darwin` confirmed that the iff follows from the
post-`p` branch formula and the Htilde interval/gap API, that the terminal-room
theorem is named only as sufficient, and that the counterexample is finite and
source-free.

## Nonclaims

This theorem does not construct Eq5 vectors, prove source-label legality,
prove the lower guard from source hypotheses, prove cutoff coverage, terminal
`tilde t=0`, selected-span coverage, classifier/injection/back-to-label
coverage, Lemma 5 order count, pole order, normal crossings, or RLCT
extraction.
