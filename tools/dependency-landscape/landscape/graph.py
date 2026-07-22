"""Per-snapshot declaration-graph computation.

Direction convention throughout: an edge (dep, consumer) runs from prerequisite
to the declaration that uses it. Height 0 = top-level consumers/unused roots;
larger height = deeper shared foundations (drawn lower). Same-height cycles
(mutual or resolution-induced) are SCC-condensed so heights are well-defined
and every cross-group edge strictly decreases height toward the consumer.
"""
from __future__ import annotations

from collections import Counter, defaultdict


class StateGraph:
    """The resolved declaration DAG of one code state."""

    def __init__(self, decls, module_of, profile):
        # decls: list[leanparse.Decl]; module_of: decl index → module name
        self.decls = decls
        self.module_of = module_of
        self.profile = profile
        self.n = len(decls)
        self.name_to_index = {}
        for i, d in enumerate(decls):
            # first definition wins; duplicates (rare, e.g. scoped re-declares)
            self.name_to_index.setdefault(d.name, i)
        self.area = [profile.area_index(module_of[i]) for i in range(self.n)]
        self.kind = [d.kind_index for d in decls]
        self.role = [
            profile.role_index(decls[i].name, module_of[i]) for i in range(self.n)
        ]
        self._resolve()
        self._condense()
        self._heights()
        self._goal_cone()

    # -- name resolution ---------------------------------------------------

    def _resolve(self):
        names = self.name_to_index
        by_last = defaultdict(list)
        for name in names:
            by_last[name.rsplit(".", 1)[-1]].append(name)

        consumers = [[] for _ in range(self.n)]   # dep → consumers
        dependencies = [[] for _ in range(self.n)]
        edge_count = 0
        memo = {}  # (prefixes, token) → tuple of decl indices
        for ci, decl in enumerate(self.decls):
            ns = decl.namespaces
            prefixes = tuple(
                ".".join(ns[:cut]) for cut in range(len(ns), 0, -1)
            ) + decl.opens
            resolved = set()
            for token in decl.tokens:
                key = (prefixes, token)
                hits = memo.get(key)
                if hits is None:
                    hit = names.get(token)
                    if hit is None:
                        for p in prefixes:
                            hit = names.get(f"{p}.{token}")
                            if hit is not None:
                                break
                    if hit is not None:
                        hits = (hit,)
                    elif "." in token and token[0].isupper():
                        # partial qualification (`RouteM.foo` from elsewhere);
                        # never suffix-match bare identifiers or hypothesis
                        # dot-notation (`h.symm`) — those are the noise makers
                        suffix = "." + token
                        matches = [names[c] for c in by_last.get(token.rsplit(".", 1)[-1], ())
                                   if c.endswith(suffix)]
                        hits = tuple(matches) if 1 <= len(matches) <= 2 else ()
                    else:
                        hits = ()
                    memo[key] = hits
                for h in hits:
                    if h != ci:
                        resolved.add(h)
            for di in resolved:
                consumers[di].append(ci)
                dependencies[ci].append(di)
            edge_count += len(resolved)
        self.consumers = consumers
        self.dependencies = dependencies
        self.edge_count = edge_count

    # -- SCC condensation (iterative Tarjan) --------------------------------

    def _condense(self):
        n = self.n
        adj = self.consumers
        index = [0] * n
        low = [0] * n
        on_stack = bytearray(n)
        comp = [-1] * n
        stack, call = [], []
        counter = 1
        ncomp = 0
        for root in range(n):
            if index[root]:
                continue
            call.append((root, 0))
            while call:
                v, pi = call[-1]
                if pi == 0:
                    index[v] = low[v] = counter
                    counter += 1
                    stack.append(v)
                    on_stack[v] = 1
                recurse = False
                neighbors = adj[v]
                while pi < len(neighbors):
                    w = neighbors[pi]
                    pi += 1
                    if not index[w]:
                        call[-1] = (v, pi)
                        call.append((w, 0))
                        recurse = True
                        break
                    if on_stack[w]:
                        low[v] = min(low[v], index[w])
                if recurse:
                    continue
                call.pop()
                if low[v] == index[v]:
                    while True:
                        w = stack.pop()
                        on_stack[w] = 0
                        comp[w] = ncomp
                        if w == v:
                            break
                    ncomp += 1
                if call:
                    parent = call[-1][0]
                    low[parent] = min(low[parent], low[v])
        self.scc = comp
        self.scc_count = ncomp
        same_height = 0
        goal_placeholder = 0  # filled after cone
        for di in range(n):
            for ci in self.consumers[di]:
                if comp[di] == comp[ci]:
                    same_height += 1
        self.same_height_edges = same_height

    # -- dependency heights --------------------------------------------------

    def _heights(self):
        # Height on the condensation: 0 for SCCs with no external consumers,
        # else 1 + max over consumer SCCs. Kahn order over consumer→dep edges.
        ncomp = self.scc_count
        comp = self.scc
        cons_out = [set() for _ in range(ncomp)]   # SCC dep → consumer SCCs
        for di in range(self.n):
            cd = comp[di]
            for ci in self.consumers[di]:
                cc = comp[ci]
                if cc != cd:
                    cons_out[cd].add(cc)
        pending = [len(cons_out[c]) for c in range(ncomp)]
        cheight = [0] * ncomp
        dep_in = [[] for _ in range(ncomp)]        # consumer SCC → dep SCCs
        for cd in range(ncomp):
            for cc in cons_out[cd]:
                dep_in[cc].append(cd)
        queue = [c for c in range(ncomp) if pending[c] == 0]
        head = 0
        while head < len(queue):
            cc = queue[head]
            head += 1
            for cd in dep_in[cc]:
                if cheight[cd] < cheight[cc] + 1:
                    cheight[cd] = cheight[cc] + 1
                pending[cd] -= 1
                if pending[cd] == 0:
                    queue.append(cd)
        self.height = [cheight[comp[i]] for i in range(self.n)]
        self.max_height = max(self.height, default=0)
        ordered = sorted(self.height)
        self.median_height = ordered[len(ordered) // 2] if ordered else 0
        self.root_count = sum(1 for i in range(self.n) if not self.consumers[i])

    # -- goal cone -----------------------------------------------------------

    def _goal_cone(self):
        self.goal_index = None
        self.goal_target = None
        for candidate in self.profile.goal_candidates:
            for name, idx in self.name_to_index.items():
                if name == candidate or name.endswith("." + candidate):
                    self.goal_index = idx
                    self.goal_target = name
                    break
            if self.goal_index is not None:
                break
        in_cone = bytearray(self.n)
        if self.goal_index is not None:
            queue = [self.goal_index]
            in_cone[self.goal_index] = 1
            head = 0
            while head < len(queue):
                v = queue[head]
                head += 1
                for d in self.dependencies[v]:
                    if not in_cone[d]:
                        in_cone[d] = 1
                        queue.append(d)
        self.in_goal_cone = in_cone
        self.goal_decl_count = sum(in_cone)
        goal_edges = goal_same = 0
        comp = self.scc
        for di in range(self.n):
            if not in_cone[di]:
                continue
            for ci in self.consumers[di]:
                if in_cone[ci]:
                    goal_edges += 1
                    if comp[di] == comp[ci]:
                        goal_same += 1
        self.goal_edge_count = goal_edges
        self.goal_same_height_edges = goal_same
        self.sorry_total = sum(d.sorry_count for d in self.decls)
        self.goal_sorry = sum(
            d.sorry_count for i, d in enumerate(self.decls) if in_cone[i]
        )

    # -- summaries for the history player -------------------------------------

    def facet_counts(self):
        n_areas = len(self.profile.areas)
        n_kinds = 6
        n_roles = len(self.profile.roles)
        area = [0] * n_areas
        kind = [0] * n_kinds
        role = [0] * n_roles
        g_area = [0] * n_areas
        g_kind = [0] * n_kinds
        g_role = [0] * n_roles
        for i in range(self.n):
            area[self.area[i]] += 1
            kind[self.kind[i]] += 1
            role[self.role[i]] += 1
            if self.in_goal_cone[i]:
                g_area[self.area[i]] += 1
                g_kind[self.kind[i]] += 1
                g_role[self.role[i]] += 1
        return area, kind, role, g_area, g_kind, g_role

    def top_hubs(self, limit: int = 8):
        ranked = sorted(
            range(self.n), key=lambda i: -len(self.consumers[i])
        )[:limit]
        return [
            [
                self.decls[i].name,
                self.module_of[i],
                len(self.consumers[i]),
                bool(self.in_goal_cone[i]),
            ]
            for i in ranked
            if self.consumers[i]
        ]

    def quotient(self):
        """Atomic groups by (height, area, kind, role) and aggregated edges.

        Group tuple: [height, area, kind, role, count, internalEdges,
                      goalCount, goalInternalEdges, sorry, goalSorry]
        Edge tuple:  [depGroup, consumerGroup, weight, goalWeight]
        """
        key_of = {}
        groups = []
        member_group = [0] * self.n
        for i in range(self.n):
            key = (self.height[i], self.area[i], self.kind[i], self.role[i])
            gi = key_of.get(key)
            if gi is None:
                gi = len(groups)
                key_of[key] = gi
                groups.append([key[0], key[1], key[2], key[3], 0, 0, 0, 0, 0, 0])
            g = groups[gi]
            g[4] += 1
            g[8] += self.decls[i].sorry_count
            if self.in_goal_cone[i]:
                g[6] += 1
                g[9] += self.decls[i].sorry_count
            member_group[i] = gi
        edge_acc = Counter()
        goal_acc = Counter()
        scc = self.scc
        for di in range(self.n):
            gd = member_group[di]
            d_goal = self.in_goal_cone[di]
            for ci in self.consumers[di]:
                gc = member_group[ci]
                in_goal = d_goal and self.in_goal_cone[ci]
                # Same-SCC edges (condensed cycles) stay internal even across
                # facet groups, so every emitted ribbon is strictly upward.
                if gd == gc or scc[di] == scc[ci]:
                    groups[gd][5] += 1
                    if in_goal:
                        groups[gd][7] += 1
                else:
                    edge_acc[(gd, gc)] += 1
                    if in_goal:
                        goal_acc[(gd, gc)] += 1
        edges = [
            [dep, cons, weight, goal_acc.get((dep, cons), 0)]
            for (dep, cons), weight in edge_acc.items()
        ]
        edges.sort(key=lambda e: (e[0], e[1]))
        return groups, edges
