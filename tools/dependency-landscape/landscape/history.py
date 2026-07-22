"""Assemble the hourly-playback history: first-parent lineage, hourly frames,
deduplicated code states, per-state quotient DAGs, and the timing audit."""
from __future__ import annotations

import datetime as dt
import sys
from .graph import StateGraph
from .leanparse import parse_lean_source, module_name_from_path


def _iso(ts: int) -> str:
    return dt.datetime.fromtimestamp(ts, dt.timezone.utc).isoformat()


class BlobCache:
    def __init__(self, repo):
        self.repo = repo
        self.cache = {}

    def parsed(self, blob_sha: str):
        hit = self.cache.get(blob_sha)
        if hit is None:
            text = self.repo.blob(blob_sha).decode("utf-8", errors="replace")
            hit = parse_lean_source(text)
            self.cache[blob_sha] = hit
        return hit


def _state_payload(repo, blobs, commit_sha, profile, tree_cache):
    """Computed graph fields + module/decl name sets for the lean tree at a
    commit, cached by the lean tree object id (docs-only commits share the
    previous computation). The StateGraph itself is not retained."""
    tree_sha = repo.rev_parse(f"{commit_sha}:{profile.lean_root}")
    hit = tree_cache.get(tree_sha)
    if hit is not None:
        return hit
    files = repo.lean_tree(commit_sha, profile.lean_root)
    decls, module_of, modules = [], [], []
    for path, blob_sha in files:
        parsed = blobs.parsed(blob_sha)
        module = module_name_from_path(path, profile.lean_root)
        modules.append(module)
        for decl in parsed.decls:
            decls.append(decl)
            module_of.append(module)
    graph = StateGraph(decls, module_of, profile)
    area, kind, role, g_area, g_kind, g_role = graph.facet_counts()
    groups, edges = graph.quotient()
    fields = {
        "moduleCount": len(modules),
        "declarationCount": graph.n,
        "edgeCount": graph.edge_count,
        "rootCount": graph.root_count,
        "sameHeightEdgeCount": graph.same_height_edges,
        "goalSameHeightEdgeCount": graph.goal_same_height_edges,
        "maxHeight": graph.max_height,
        "medianHeight": graph.median_height,
        "sorryCount": graph.sorry_total,
        "goalTarget": graph.goal_target,
        "goalDeclarationCount": graph.goal_decl_count,
        "goalEdgeCount": graph.goal_edge_count,
        "goalSorryCount": graph.goal_sorry,
        "areaCounts": area, "kindCounts": kind, "roleCounts": role,
        "goalAreaCounts": g_area, "goalKindCounts": g_kind,
        "goalRoleCounts": g_role,
        "topHubs": graph.top_hubs(),
        "groups": groups,
        "edges": edges,
    }
    result = (fields, frozenset(modules), frozenset(d.name for d in decls))
    tree_cache[tree_sha] = result
    return result


def _relative(path: str, profile) -> str:
    rel = path
    if rel.startswith(profile.lean_root + "/"):
        rel = rel[len(profile.lean_root) + 1:]
    if profile.project_prefix and rel.startswith(profile.project_prefix + "/"):
        rel = rel[len(profile.project_prefix) + 1:]
    return rel


def build_history(repo, base, tip, profile, progress=lambda s: None,
                  max_states=None):
    lineage = repo.first_parent_lineage(base, tip)
    if not lineage:
        raise SystemExit("empty lineage — nothing to play back")

    # timing audit
    mismatches = [abs(c.committer_time - c.author_time) for c in lineage
                  if c.committer_time != c.author_time]
    backsteps = ties = 0
    for prev, cur in zip(lineage, lineage[1:]):
        if cur.committer_time < prev.committer_time:
            backsteps += 1
        elif cur.committer_time == prev.committer_time:
            ties += 1
    author_backsteps = sum(
        1 for prev, cur in zip(lineage, lineage[1:])
        if cur.author_time < prev.author_time
    )
    reachable = repo.count(f"{base}..{tip}")
    audit = {
        "basis": "committer / first-parent integration time",
        "firstParentCommitCount": len(lineage),
        "reachableCommitCount": reachable,
        "mergeCommitCount": sum(1 for c in lineage if len(c.parents) > 1),
        "authorCommitterMismatchCount": len(mismatches),
        "maxAbsAuthorCommitterDeltaSeconds": max(mismatches, default=0),
        "authorTimestampBackstepCount": author_backsteps,
        "committerTimestampBackstepCount": backsteps,
        "adjacentCommitterTimestampTieCount": ties,
        "sideBranchCommitCount": reachable - len(lineage),
    }

    numstat = repo.numstat_first_parent(base, tip)
    blobs = BlobCache(repo)
    tree_cache = {}

    bucket = profile.bucket_hours * 3600
    start = lineage[0].committer_time // bucket * bucket
    end = lineage[-1].committer_time
    timeline, states = [], []
    state_index_of = {}          # commit sha → index into states
    lineage_pos = 0
    prev_summary = None          # (graph, modules, declnames) of previous state
    prev_state_record = None
    n_buckets = (end - start) // bucket + 1

    for bi in range(n_buckets):
        bucket_end = start + (bi + 1) * bucket
        commits_in_bucket = []
        while lineage_pos < len(lineage) and lineage[lineage_pos].committer_time < bucket_end:
            commits_in_bucket.append(lineage[lineage_pos])
            lineage_pos += 1
        tail = commits_in_bucket[-1] if commits_in_bucket else (
            lineage[lineage_pos - 1] if lineage_pos else None)
        if tail is None:
            continue  # before the first commit

        if tail.sha not in state_index_of:
            if max_states is not None and len(states) >= max_states:
                break
            progress(f"state {len(states) + 1} @ {_iso(tail.committer_time)[:16]} "
                     f"({bi + 1}/{n_buckets} buckets)")
            fields, modules, declnames = _state_payload(
                repo, blobs, tail.sha, profile, tree_cache)
            record = {
                "commit": tail.sha,
                "timestamp": tail.committer_time,
                "iso": _iso(tail.committer_time),
                "authorTimestamp": tail.author_time,
                "authorIso": _iso(tail.author_time),
                "parentCount": len(tail.parents),
                "subject": tail.subject,
                **fields,
            }
            if prev_summary is None:
                change = {k: 0 for k in (
                    "moduleAdded", "moduleRemoved", "declarationAdded",
                    "declarationRemoved", "edgeDelta", "rootDelta",
                    "heightDelta", "sorryDelta", "goalDelta")}
                change["moduleAdded"] = len(modules)
                change["declarationAdded"] = record["declarationCount"]
            else:
                pmods, pdecls = prev_summary
                pr = prev_state_record
                change = {
                    "moduleAdded": len(modules - pmods),
                    "moduleRemoved": len(pmods - modules),
                    "declarationAdded": len(declnames - pdecls),
                    "declarationRemoved": len(pdecls - declnames),
                    "edgeDelta": record["edgeCount"] - pr["edgeCount"],
                    "rootDelta": record["rootCount"] - pr["rootCount"],
                    "heightDelta": record["maxHeight"] - pr["maxHeight"],
                    "sorryDelta": record["sorryCount"] - pr["sorryCount"],
                    "goalDelta": record["goalDeclarationCount"] - pr["goalDeclarationCount"],
                }
            record["change"] = change
            state_index_of[tail.sha] = len(states)
            states.append(record)
            prev_summary = (modules, declnames)
            prev_state_record = record
            fresh_state = True
        else:
            fresh_state = False

        state_idx = state_index_of[tail.sha]
        lean_files = {}
        insertions = deletions = lean_commits = 0
        for c in commits_in_bucket:
            for path, adds, dels in numstat.get(c.sha, []):
                if path.startswith(profile.lean_root + "/") and path.endswith(".lean"):
                    rel = _relative(path, profile)
                    cur = lean_files.setdefault(rel, [0, 0])
                    cur[0] += adds
                    cur[1] += dels
                    insertions += adds
                    deletions += dels
        for c in commits_in_bucket:
            if any(p.startswith(profile.lean_root + "/") and p.endswith(".lean")
                   for p, _a, _d in numstat.get(c.sha, [])):
                lean_commits += 1
        top_files = sorted(
            ([path, adds, dels] for path, (adds, dels) in lean_files.items()),
            key=lambda row: -(row[1] + row[2]))[:5]
        zero_change = {k: 0 for k in states[state_idx]["change"]}
        timeline.append({
            "time": bucket_end - bucket,
            "iso": _iso(bucket_end - bucket),
            "state": state_idx,
            "isHead": tail.sha == lineage[-1].sha,
            "change": states[state_idx]["change"] if fresh_state else zero_change,
            "activity": {
                "filesChanged": len(lean_files),
                "insertions": insertions,
                "deletions": deletions,
                "topFiles": top_files,
                "commitCount": len(commits_in_bucket),
                "leanCommitCount": lean_commits,
                "authorCount": len({c.author for c in commits_in_bucket}),
                "recentCommits": [[c.sha[:10], c.subject] for c in commits_in_bucket[-4:]],
                "tags": profile.tag_labels([c.subject for c in commits_in_bucket]),
            },
        })

    meta = {
        "generatedAt": dt.datetime.now(dt.timezone.utc).isoformat(),
        "repo": repo.root,
        "branch": None,   # filled by the caller
        "head": lineage[-1].sha,
        "base": base,
        "bucketHours": profile.bucket_hours,
        "lineage": "first-parent",
        "timeBasis": "committer / first-parent integration time",
        "timingAudit": audit,
        "areas": profile.areas,
        "kinds": ["theorem", "definition", "type declaration", "instance",
                  "opaque", "other"],
        "roles": profile.roles,
        "laneMeta": profile.lane_meta(),
        "goalLabel": profile.goal_label,
        "goalCandidates": profile.goal_candidates,
        "timelineFrameCount": len(timeline),
        "uniqueStateCount": len(states),
        "uniqueParsedBlobCount": len(blobs.cache),
        "approximate": True,
        "method": "Explicit source declaration commands and name-resolved "
                  "project references; no checkout or Lean build.",
    }
    return {"meta": meta, "timeline": timeline, "states": states}
