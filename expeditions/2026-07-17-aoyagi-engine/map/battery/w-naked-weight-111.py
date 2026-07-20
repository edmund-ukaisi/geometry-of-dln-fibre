#!/usr/bin/env python3
# kills: naked-weight-route
# config: M=(1,1,1), t=0, a=M0-t=1; integrand |y|^{-1} over [-1,1]
# provenance: threads/00-genesis/architecture-cert.md (obligation-2 refutation, 2026-07-17)
"""The one-variable falsity witness for naked Jacobian-weight obligations.

At M=(1,1,1), t=0 the tail product is a single scalar y and the naked weight is
det(QQ^T)^{-a/2} = |y|^{-1}. Exact dyadic shells: on 2^{-k-1} < |y| <= 2^{-k}
the integrand exceeds 2^k and the shell has measure 2^{-k} exactly, so each shell
contributes > 1/2 — the sum over k diverges. Exit 1 (killed) iff divergence is
confirmed by exact rational arithmetic. Any obligation of this shape is FALSE."""
import sys
from fractions import Fraction

# shell k contribution lower bound: measure(2^{-k-1},2^{-k}] * inf integrand = 2^{-k-1}*2^k = 1/2
per_shell_lb = [Fraction(2) ** (-k - 1) * Fraction(2) ** k for k in range(50)]
diverges = all(c == Fraction(1, 2) for c in per_shell_lb)  # constant positive terms => sum = inf
print(f"per-shell lower bound constant at {per_shell_lb[0]} over 50 shells -> integral = inf: {diverges}")
sys.exit(1 if diverges else 0)
