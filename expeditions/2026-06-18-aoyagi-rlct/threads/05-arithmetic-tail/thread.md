# Thread 05 - arithmetic tail

Type: formalisation. Status: blocked.

## Task

Formalise Aoyagi's finite minimisation and pole-order arithmetic once the
exponent vectors are stable.

## Output contract

- Lean definitions for the relevant finite candidate set and exponent ratios.
- Proofs of the minimisation and order-count lemmas.
- Boundary-case tests/examples for small dimension vectors.

## Controller notes

This should be mostly finite arithmetic. If a proof becomes a long brittle
calculation, consider a small exact certificate generator, but Lean remains the
final authority.

## 2026-06-18 check result

Draft reproduction: `reproduction-draft.md`. Independent checker: `Planck`,
saved at `reproduction-check.md`.

Status: not formalisation-ready. The next arithmetic reproduction must split
Lemma 3 endpoint cases, preserve Aoyagi's `\tilde t_{s,k}=0` restriction, prove
feasibility of the floor/ceil minimisers, and reproduce Lemma 5's
chart-family/order-count construction.
