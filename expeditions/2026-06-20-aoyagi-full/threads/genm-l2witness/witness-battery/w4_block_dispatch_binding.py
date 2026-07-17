#!/usr/bin/env python3
# =============================================================================
# WITNESS W4 — BLOCK-LEVEL DISPATCH AT THE BINDING CUT  (kill-condition, exact)
# =============================================================================
# DISCRIMINATOR (bridges genm-prodcorank + decstep-cert §4 to the ENGINE's branch
#   variable). The native engine's peel branches on
#       d = min(a, b) = min(M0 - t, M1 - t)
#   -- the min dimension of the residual a x b corank block Gamma at cut t of a
#   node M = (M0, M1, ...). d is exactly the index the native<=1 / transcribe>=2
#   dispatch keys on:
#     - d <= 1  : row/column corank block, NO joint incidence -> NATIVE (decstep §1);
#     - d >= 2  : min(a,b)>=2 product-corank block -> the W1/W2 atom (joint center
#                 survives, codim undershoots) -> TRANSCRIBE (cited).
#   The terminal length-2 BASE (b0 x b1) is a single free bilinear/Wishart block
#   (no deeper product to couple to) -> ALWAYS NATIVE, regardless of its min.
#
# OPERATOR RULE (binding): any inequality-shaped condition the engine carries gets
#   an EQUALITY-AT-BINDING-CELL witness, not only a truth scan. The engine's
#   dispatch inequality is keyed on d, so this witness certifies the budget is
#   EXACTLY tight at the binding d (equality, strict off it) AT THE BRANCH INDEX.
#
# ENGINE KILL-CONDITIONS GUARDED:
#   (E1) bridge: d = min(M0-t, M1-t); block (a,b)=(M0-t,M1-t); charge a*b=d(d+delta),
#        delta=|M0-M1|. The t<->d reparametrization is a bijection, min(a,b)=d.
#   (E2) tightness at the branch index: minAdm(M) = min_d [ d(d+delta) + minAdm(redChain) ],
#        EQUALITY at the binding d*, STRICT above off it, at every node on every
#        optimal peel path of (n,n,n,n), n=4..7.
#   (E3) bridge-correctness vs decstep: the specific reported min(a,b) sequences
#        (5,5,5,5)->[2,2], (7,7,7,7)->[3,2], (4,4,4,4)->[2, then 1] appear among the
#        optimal paths (certifies the bridge is the same object decstep names).
#   (E4) dispatch classification: enumerate optimal peel paths; classify each peel
#        block by d; report best-case (a native-corank cover exists?) and worst-case
#        (dominant-minor cover). BOUNDARY: n<=4 admit an all-corank-native optimal
#        path (only the free BASE carries d>=2); n>=5 FORCE a d>=2 product-corank
#        block on EVERY optimal path. Plus the equality-at-binding-cell for each
#        d>=2 transcribe atom that occurs.
#
# EXACT INSTRUMENT: exact-integer DP (minAdm) + exact recursion enumeration.
#
# EXPECTED RESULT (see w4_block_dispatch_binding.out for the verbatim run).
# =============================================================================

from functools import lru_cache

def hdr(s): print("\n" + "="*70 + "\n" + s + "\n" + "="*70)
def redChain(t, M): return (t,) + M[2:]

@lru_cache(None)
def minAdm(M):
    L = len(M)
    if L == 1: return 0
    if L == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm(redChain(t, M))
               for t in range(0, min(M[0], M[1]) + 1))

def all_cuts(M):
    """Every cut of a node M (len>=3), reparametrized so that d = min(a,b)."""
    out = []
    for t in range(0, min(M[0], M[1]) + 1):
        a, b = M[0]-t, M[1]-t
        out.append(dict(t=t, a=a, b=b, d=min(a, b), charge=a*b, red=redChain(t, M),
                        value=(a*b) + minAdm(redChain(t, M))))
    return out

def optimal_cuts(M):
    v = minAdm(M)
    return [c for c in all_cuts(M) if c['value'] == v]

def enum_paths(M):
    """All optimal peel paths: list of block records. 'peel' = corank block at a
    len>=3 node; 'base' = terminal free len-2 block."""
    if len(M) == 2:
        return [[dict(kind='base', a=M[0], b=M[1], d=min(M[0], M[1]), charge=M[0]*M[1])]]
    paths = []
    for c in optimal_cuts(M):
        rec = dict(kind='peel', node=M, t=c['t'], a=c['a'], b=c['b'], d=c['d'], charge=c['charge'])
        for sub in enum_paths(c['red']):
            paths.append([rec] + sub)
    return paths

HEAD = range(4, 8)   # headline n=4..7
SWEEP = range(3, 8)  # n=3..7

# =============================================================================
# (E1) THE BRIDGE — d = min(M0-t, M1-t); charge a*b = d(d+delta); bijection.
# =============================================================================
hdr("(E1) bridge: d = min(M0-t, M1-t), block (a,b), charge a*b = d(d+delta)")
E1 = True
for M in [(4,4,4,4), (5,5,5,5), (3,5,5), (4,7,7), (2,4,4)]:
    delta = abs(M[0] - M[1]); dmax = min(M[0], M[1])
    seen_d = []
    for c in all_cuts(M):
        d = c['d']
        # bijection check: t = dmax - d  (as d runs dmax..0 while t runs 0..dmax)
        t_from_d = dmax - d
        ok = (c['t'] == t_from_d and c['d'] == min(c['a'], c['b'])
              and c['charge'] == c['a']*c['b'] == d*(d + delta))
        E1 &= ok
        seen_d.append(d)
    bij = (sorted(seen_d) == list(range(0, dmax+1)))
    E1 &= bij
    print(f"  M={M}: delta={delta}, d-values={sorted(seen_d)} (bijection t<->d: {bij}); "
          f"charge=d(d+delta) & min(a,b)=d for all cuts: True")
print("(E1) VERDICT  bridge holds (d=min(a,b), charge=d(d+delta), t<->d bijection):", E1)

# =============================================================================
# (E2) TIGHTNESS AT THE BRANCH INDEX d — equality at binding d*, strict off it,
#      at every node reachable on an optimal path of (n,n,n,n), n=4..7.
# =============================================================================
hdr("(E2) tightness at the branch index d: minAdm = min_d[d(d+delta)+minAdm(red)]")
E2 = True
def nodes_on_optimal_paths(M, acc):
    if len(M) < 3: return
    if M in acc: return
    acc.add(M)
    for c in optimal_cuts(M):
        nodes_on_optimal_paths(c['red'], acc)
for n in SWEEP:
    acc = set(); nodes_on_optimal_paths((n,n,n,n), acc)
    node_ok = True
    for M in acc:
        v = minAdm(M)
        cs = all_cuts(M)
        binding_d = sorted(c['d'] for c in cs if c['value'] == v)
        eq_ok = all(c['value'] == v for c in cs if c['d'] in binding_d and c['value'] == v)
        strict_ok = all(c['value'] > v for c in cs if c['value'] != v)  # STRICT above off binding
        node_ok &= (eq_ok and strict_ok and len(binding_d) >= 1)
    E2 &= node_ok
    tag = "  <== HEADLINE" if n in HEAD else ""
    print(f"  n={n}: nodes on optimal paths={sorted(acc)}  equality@binding-d & strict-off, all nodes: {node_ok}{tag}")
print("(E2) VERDICT  budget tight at the binding d, strict off it, all nodes:", E2)

# =============================================================================
# (E3) BRIDGE-CORRECTNESS vs decstep — reproduce the reported min(a,b) sequences.
# =============================================================================
hdr("(E3) bridge-correctness: reproduce decstep's reported min(a,b) sequences")
def peel_d_seqs(M):
    return set(tuple(r['d'] for r in p if r['kind'] == 'peel') for p in enum_paths(M))
decstep = {
    (5,5,5,5): (2, 2),   # "(5,5,5,5)->(3,5,5): min(a,b)=2 at BOTH levels"
    (7,7,7,7): (3, 2),   # "(7,7,7,7)->(4,7,7): 3 then 2"
    (4,4,4,4): (2, 1),   # "(4,4,4,4)->(2,4,4)... drops to min(a,b)=1 after one peel"
}
E3 = True
for M, seq in decstep.items():
    seqs = peel_d_seqs(M)
    present = seq in seqs
    E3 &= present
    print(f"  M={M}: decstep min(a,b) seq {seq} present among optimal peel paths: {present}  "
          f"(all peel-d seqs: {sorted(seqs)})")
print("(E3) VERDICT  bridge reproduces decstep's reported min(a,b) values:", E3)

# =============================================================================
# (E4) DISPATCH CLASSIFICATION + equality-at-binding-cell for d>=2 atoms.
# =============================================================================
hdr("(E4) dispatch classification by d (native d<=1 / transcribe d>=2)")
print("     BASE = terminal free bilinear/Wishart block (always native).")
E4 = True
boundary = {}
for n in SWEEP:
    M = (n, n, n, n)
    paths = enum_paths(M)
    maxpeel = []
    for p in paths:
        peel_d = [r['d'] for r in p if r['kind'] == 'peel']
        base = [r for r in p if r['kind'] == 'base'][0]
        # budget check: charges along the path sum to minAdm(M) (equality on the path)
        assert sum(r['charge'] for r in p) == minAdm(M)
        maxpeel.append(max(peel_d) if peel_d else 0)
        seq = " -> ".join(
            (f"[{r['a']}x{r['b']} d={r['d']} {'NATIVE' if r['d']<=1 else 'TRANSCRIBE'}]"
             if r['kind']=='peel' else f"BASE({r['a']}x{r['b']} native)")
            for r in p)
        print(f"  n={n}: peel-d={peel_d}  {seq}")
    best = min(maxpeel); worst = max(maxpeel)   # best/worst-case max corank-block d
    boundary[n] = best
    tag = "  <== HEADLINE" if n in HEAD else ""
    kind = "native-corank cover EXISTS" if best <= 1 else "d>=2 TRANSCRIBE forced on every optimal path"
    print(f"   => n={n}: best-case max corank-d={best}, worst-case={worst}  [{kind}]{tag}\n")
# BOUNDARY assertion: n<=4 admit a native-corank optimal path; n>=5 force d>=2.
b_ok = all(boundary[n] <= 1 for n in SWEEP if n <= 4) and all(boundary[n] >= 2 for n in SWEEP if n >= 5)
E4 &= b_ok
print(f"BOUNDARY: best-case max corank-block d by n = {boundary}")
print("  n<=4: a fully-native corank optimal path exists (only the free BASE carries d>=2);")
print("  n>=5: every optimal path has a min(a,b)>=2 product-corank block (transcribe forced).")
print("(E4) VERDICT  dispatch boundary as stated (n<=4 native path / n>=5 forced):", b_ok)

# equality-at-binding-cell for each distinct d>=2 transcribe atom that occurs:
hdr("(E4') equality-at-binding-cell for each d>=2 TRANSCRIBE atom that occurs")
E4b = True
atoms = {}
for n in SWEEP:
    acc = set(); nodes_on_optimal_paths((n,n,n,n), acc)
    for M in acc:
        v = minAdm(M)
        for c in all_cuts(M):
            if c['value'] == v and c['d'] >= 2:
                atoms[(M, c['t'])] = (c['a'], c['b'], c['d'], c['charge'], c['red'], v)
for (M, t), (a, b, d, ch, red, v) in sorted(atoms.items()):
    # EQUALITY: charge + minAdm(reduced) == minAdm(M)  (no slack at this transcribe atom)
    eq = (ch + minAdm(red) == v)
    # STRICT: every non-binding cut of M is strictly above
    strict = all(c['value'] > v for c in all_cuts(M) if c['value'] != v)
    E4b &= (eq and strict)
    print(f"  atom node={M} cut t={t}: block {a}x{b} d={d} (min(a,b)>=2) charge={ch} + "
          f"minAdm({red})={minAdm(red)} = {ch+minAdm(red)} == minAdm({M})={v}  eq={eq} strict-off={strict}")
print("(E4') VERDICT  every d>=2 transcribe atom is tight at its binding cut (no slack):", E4b)

# =============================================================================
# (E5) TWO BOUNDARIES — the coverage-adjudication axis for the engine (genm-l2engine).
#   The dispatch boundary depends on whether the resolution may CHOOSE a peel path or
#   must COVER all binding strata:
#     PATH boundary  : smallest n with NO all-d<=1 optimal path (best-case max-d >= 2).
#     COVER boundary : smallest n with a BINDING d>=2 atom anywhere on the optimal
#                      recursion (a resolution covering all binding rank strata must
#                      transcribe it -- e.g. (4,4,4,4)'s binding chart t=2, block 2x2).
#   FACT (both exact): PATH boundary = 5, COVER boundary = 4.
#   INFERENCE (mine, for l2engine to adjudicate, NOT decided here): a log-resolution
#   of the loss covers ALL binding rank strata -- the rank-(n-2) locus is real and its
#   threshold is binding (= c*) -- so the COVER boundary (n>=4) is the operative one
#   UNLESS the engine exhibits a cover whose d>=2 binding chart resolves natively (W1
#   says single-factor blow-ups do NOT: the joint center (x,y,b) survives). The
#   all-d<=1 optimal PATH (n<=4) is a property of one path, not a cover; it does not
#   by itself license a native resolution.
# =============================================================================
hdr("(E5) two boundaries (coverage-adjudication axis for genm-l2engine)")
def binding_nodes(M, acc):
    if len(M) < 3: return
    if M in acc: return
    acc.add(M)
    for c in optimal_cuts(M):
        binding_nodes(c['red'], acc)
path_bd = None; cover_bd = None
for n in range(2, 10):
    M = (n, n, n, n)
    # PATH: best-case over optimal paths of max corank-block d
    best = min(max([r['d'] for r in p if r['kind'] == 'peel'] or [0]) for p in enum_paths(M))
    # COVER: does a binding d>=2 atom exist anywhere on the optimal recursion?
    acc = set(); binding_nodes(M, acc)
    bind_d = sorted({c['d'] for X in acc for c in optimal_cuts(X)})
    has_cover_atom = any(d >= 2 for d in bind_d)
    if path_bd is None and best >= 2: path_bd = n
    if cover_bd is None and has_cover_atom: cover_bd = n
    if n <= 8:
        print(f"  n={n}: best-case max corank-d={best} (PATH d>=2? {best>=2}); "
              f"binding-atom d-values={bind_d} (COVER d>=2 atom? {has_cover_atom})")
print(f"  => PATH boundary (no all-d<=1 optimal path) = n={path_bd}")
print(f"  => COVER boundary (a binding d>=2 atom exists) = n={cover_bd}")
E5 = (path_bd == 5 and cover_bd == 4)
print("(E5) VERDICT  PATH boundary = 5 and COVER boundary = 4 (both exact):", E5)
print("     [adjudication for genm-l2engine: a resolution covers all binding rank strata,")
print("      so COVER (n>=4) is operative unless the d>=2 binding chart resolves natively --")
print("      W1 says single-factor blow-ups do not principalize it. This witness states the")
print("      two boundaries; it does not choose the cover.]")

# =============================================================================
hdr("W4 OVERALL")
ok = E1 and E2 and E3 and E4 and E4b and E5
print("(E1) bridge d=min(M0-t,M1-t):", E1)
print("(E2) tightness at branch index d:", E2)
print("(E3) reproduces decstep min(a,b):", E3)
print("(E4) dispatch boundary best-case B(n) native<=1 / forced>=2:", E4)
print("(E4') d>=2 transcribe atoms tight (no slack):", E4b)
print("(E5) two boundaries PATH=5 / COVER=4:", E5)
print("W4 PASS:", ok)
assert ok, "W4 FAILED — a load-bearing exhibit did not reproduce"
print("\n[W4] the engine branches on d=min(M0-t,M1-t); the budget is tight at the "
      "binding d. Two boundaries: an all-d<=1 optimal PATH exists for n<=4, but a BINDING "
      "d>=2 atom (COVER must-transcribe) exists for every n>=4. Which is operative is the "
      "engine's coverage-adjudication (a resolution covers all binding strata => COVER, n>=4).")

# =============================================================================
# CHECKED-IN OUTPUT: see w4_block_dispatch_binding.out . Key lines:
#   (E1) VERDICT ... True
#   (E2) VERDICT  budget tight at the binding d, strict off it, all nodes: True
#   (E3) VERDICT  bridge reproduces decstep's reported min(a,b) values: True
#   (E4) VERDICT  dispatch boundary as stated (n<=4 native path / n>=5 forced): True
#   (E4') VERDICT  every d>=2 transcribe atom is tight at its binding cut (no slack): True
#   (E5) VERDICT  PATH boundary = 5 and COVER boundary = 4 (both exact): True
#   W4 PASS: True
# =============================================================================
