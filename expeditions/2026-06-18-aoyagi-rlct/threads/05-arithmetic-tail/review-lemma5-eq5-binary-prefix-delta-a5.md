# Review - Lemma 5 Eq5 binary prefix delta

Status: reviewed/formalised; low documentation finding fixed.

## Scope

This slice proves the binary adjacent-difference calculation for the Lemma 4
increment-prefix sequence attached to a supplied equation `(5)` endpoint chain
under terminal room.

## Checks

Focused Lean checks passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Lemma5Eq5EndpointProfile.lean
lake build DLNFibre.DLN.Aoyagi.Lemma5Eq5EndpointProfile
```

## Review Focus

The independent review should check:

- endpoint cases `D_0=0` and `D_ell=a`;
- `alpha=1`, `p=alpha+1`, and `alpha=a`;
- the successor-terminal case `b+1=ell`;
- terminal-room use in the profile and binary split;
- that source construction, terminality, order count, pole order, normal
  crossings, and RLCT remain nonclaims.

## Findings

Low, fixed: the module header still described this file as not proving binary
prefix deltas.  That was accurate for the previous slice but stale after this
conditional binary-delta theorem.  The header now says binary deltas are proved
only for supplied terminal-room endpoint chains, while construction,
two-value increments, pole order, normal crossings, and RLCT remain nonclaims.

No formal arithmetic findings.  Independent xhigh reviewer `Ohm` checked the
edge cases `alpha=1`, `p=alpha+1`, `alpha=a`, and the terminal successor
case `b+1=ell`; the reviewer also confirmed that source and terminal endpoint
hypotheses remain explicit.
