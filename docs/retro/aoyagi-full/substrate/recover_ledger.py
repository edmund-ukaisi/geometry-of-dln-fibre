#!/usr/bin/env python3
"""Longitudinal ledger recovery + sha-ref classification  (gaps 1+2).

1. Samples synthesis.md at historical commits (stride over commits touching it,
   plus tip), parses UPDATE blocks with parse_ledger's regexes, unions by
   update_n keeping the FULLEST version. Recovered (non-tip) blocks carry
   anchor_ref = the sampled commit sha, so drill-ins read the right blob.
2. Re-resolves every sha-ref against the full object DB and classifies:
   in_canonical / exists_unmerged / unknown.

Rewrites events.json (superset schema of parse_ledger's) → rerun join.py after.
"""
from __future__ import annotations
import json, re, subprocess
from pathlib import Path
import parse_ledger as P

D = Path(__file__).resolve().parent
REPO, BRANCH, LEDGER = P.REPO, P.BRANCH, P.LEDGER
STRIDE = 20


def git(*args, ok_fail=False):
    r = subprocess.run(["git", *args], cwd=REPO, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    if r.returncode != 0 and not ok_fail:
        raise RuntimeError(args)
    return r.stdout if r.returncode == 0 else None


def parse_blocks(text, anchor_ref):
    lines = text.splitlines()
    heads = [(i, m) for i, ln in enumerate(lines) if (m := P.HEADER_RE.match(ln))]
    out = []
    for k, (i, m) in enumerate(heads):
        end = heads[k + 1][0] if k + 1 < len(heads) else len(lines)
        body = "\n".join(lines[i:end])
        out.append({
            "update_n": int(m.group(1)), "date": m.group(2),
            "anchor_ref": anchor_ref, "line_start": i + 1, "line_end": end,
            "header": lines[i][:400], "n_lines": end - i,
            "thread_slugs": sorted(set(P.SLUG_RE.findall(body)))[:12],
            "sha_refs": sorted(set(P.SHAREF_RE.findall(body)))[:12],
            "item_refs": sorted({int(n) for n in P.ITEM_RE.findall(body)})[:12],
            "flags": sorted(f for f, rx, honly in P.FLAGS
                            if rx.search(lines[i] if honly else body)),
            "agent_ids": sorted(set(P.AGENT_RE.findall(body)))[:8],
        })
    return out


def main():
    # --- 1. sample history
    touching = git("log", "--format=%H", f"{P.__dict__.get('FORK','413566b3')}..{BRANCH}",
                   "--", LEDGER).split()
    touching.reverse()  # oldest first
    samples = touching[::STRIDE] + [touching[-1]]
    best: dict[int, dict] = {}
    for sha in samples:
        text = git("show", f"{sha}:{LEDGER}", ok_fail=True)
        if not text:
            continue
        for ev in parse_blocks(text, sha[:8]):
            cur = best.get(ev["update_n"])
            if cur is None or ev["n_lines"] > cur["n_lines"]:
                best[ev["update_n"]] = ev
    # tip versions win ties and mark liveness
    tip_text = git("show", f"{BRANCH}:{LEDGER}")
    tip_ns = set()
    for ev in parse_blocks(tip_text, "tip"):
        tip_ns.add(ev["update_n"])
        cur = best.get(ev["update_n"])
        if cur is None or ev["n_lines"] >= cur["n_lines"]:
            best[ev["update_n"]] = ev
    for n, ev in best.items():
        ev["at_tip"] = n in tip_ns
    ns0 = sorted(best)
    missing0 = [n for n in range(ns0[0], ns0[-1] + 1) if n not in best]
    # pickaxe-recover blocks that lived between samples
    for n in missing0:
        hit = git("log", "-S", f"UPDATE-{n} (", "--format=%H",
                  f"413566b3..{BRANCH}", "--", LEDGER, ok_fail=True)
        if hit and hit.strip():
            sha = hit.strip().splitlines()[-1]  # oldest = introduction commit
            text = git("show", f"{sha}:{LEDGER}", ok_fail=True)
            if text:
                for ev in parse_blocks(text, sha[:8]):
                    if ev["update_n"] == n:
                        best[n] = ev
                        break
                if n not in best:  # live-tick bracket format: **[UPDATE-N ...]**
                    lines = text.splitlines()
                    pat = re.compile(rf"^\*\*\[?UPDATE-{n}\b")
                    anyhead = re.compile(r"^\*?\*?\[?[⚙]? ?\[?UPDATE-\d+\b|^\*\*⚙")
                    for i, ln in enumerate(lines):
                        if pat.match(ln):
                            end = next((k for k in range(i + 1, len(lines))
                                        if anyhead.match(lines[k])), min(i + 40, len(lines)))
                            body = "\n".join(lines[i:end])
                            dm = re.search(r"(2026-\d\d-\d\d)", body)
                            best[n] = {
                                "update_n": n, "date": dm.group(1) if dm else None,
                                "anchor_ref": sha[:8], "line_start": i + 1, "line_end": end,
                                "header": ln[:400], "n_lines": end - i, "format": "live-tick",
                                "thread_slugs": sorted(set(P.SLUG_RE.findall(body)))[:12],
                                "sha_refs": sorted(set(P.SHAREF_RE.findall(body)))[:12],
                                "item_refs": sorted({int(x) for x in P.ITEM_RE.findall(body)})[:12],
                                "agent_ids": sorted(set(P.AGENT_RE.findall(body)))[:8],
                                "flags": sorted(f for f, rx, _h in P.FLAGS if rx.search(body)),
                            }
                            break
    events = [best[n] for n in sorted(best)]
    ns = sorted(best)
    missing = [n for n in range(ns[0], ns[-1] + 1) if n not in best]

    # --- 2. sha classification
    canonical = set(git("rev-list", f"413566b3..{BRANCH}").split())
    cls_count = {"in_canonical": 0, "exists_unmerged": 0, "agent_id_like": 0, "unknown": 0}
    cache: dict[str, str] = {}
    for ev in events:
        res = []
        for pref in ev["sha_refs"]:
            if pref not in cache:
                full = git("rev-parse", "--verify", "--quiet", f"{pref}^{{commit}}", ok_fail=True)
                if full and full.strip() in canonical:
                    cache[pref] = "in_canonical"
                elif full:
                    cache[pref] = "exists_unmerged"
                elif pref.startswith("a") and not full:
                    cache[pref] = "agent_id_like"
                else:
                    cache[pref] = "unknown"
            res.append({"ref": pref, "cls": cache[pref]})
            cls_count[cache[pref]] += 1
        ev["sha_refs_classified"] = res

    (D / "events.json").write_text(json.dumps(
        {"_meta": {"branch": BRANCH, "ledger": LEDGER, "n": len(events),
                   "n_unique": len(events), "recovered": len(events) - len(tip_ns),
                   "samples": len(samples), "missing_ns": missing},
         "events": events}, indent=1))
    print(f"[recover] {len(events)} unique blocks ({len(events)-len(tip_ns)} recovered, "
          f"{len(tip_ns)} at tip); range {ns[0]}..{ns[-1]}; missing {len(missing)}: {missing[:20]}")
    print(f"[sha-cls] {cls_count} over {sum(cls_count.values())} refs "
          f"({len(cache)} unique prefixes)")


if __name__ == "__main__":
    main()
