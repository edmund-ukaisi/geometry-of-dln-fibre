"""The battery: refutations as executable scripts.

Each ``battery/<name>.py`` is self-contained (stdlib/sympy-class) and exits by
convention: ``0`` = the guarded claim survives, ``1`` = killed (the refuting
witness fires), anything else = error. A frontmatter comment header declares
which node(s) it kills or guards, plus config and provenance:

    # kills: route-shellspine-bridge
    # guards: box-threshold
    # config: M=(3,3,3), t=1, c'=4
    # provenance: threads/genm-routeverify/routeverify-cert.md

``kills``/``guards`` values may be comma-separated to affect several nodes.
"""

from __future__ import annotations

import sys
import subprocess
from pathlib import Path

VERDICT = {0: "survives", 1: "killed"}


def parse_header(path):
    """Read the leading ``# key: value`` comment block of a battery script."""
    hdr = {"kills": [], "guards": [], "config": "", "provenance": ""}
    for line in Path(path).read_text().splitlines():
        s = line.strip()
        if not s:
            continue
        if not s.startswith("#"):
            break  # header ends at first non-comment line
        body = s.lstrip("#").strip()
        if ":" not in body:
            continue
        key, _, val = body.partition(":")
        key, val = key.strip().lower(), val.strip()
        if key in ("kills", "guards"):
            hdr[key].extend(x.strip() for x in val.split(",") if x.strip())
        elif key in ("config", "provenance"):
            hdr[key] = val
    return hdr


def affected_nodes(hdr):
    return sorted(set(hdr["kills"]) | set(hdr["guards"]))


def run_script(path, timeout=60):
    """Execute one battery script; return a result dict with the verdict."""
    hdr = parse_header(path)
    try:
        proc = subprocess.run(
            [sys.executable, str(path)],
            capture_output=True, text=True, timeout=timeout,
        )
        code = proc.returncode
        tail = (proc.stdout + proc.stderr).strip().splitlines()
        tail = tail[-3:] if tail else []
    except subprocess.TimeoutExpired:
        code, tail = -1, ["<timeout>"]
    except Exception as exc:  # pragma: no cover - defensive
        code, tail = -2, [str(exc)]
    verdict = VERDICT.get(code, "error")
    return {
        "script": Path(path).name,
        "path": str(path),
        "exit": code,
        "verdict": verdict,
        "kills": hdr["kills"],
        "guards": hdr["guards"],
        "config": hdr["config"],
        "provenance": hdr["provenance"],
        "output_tail": tail,
    }


def collect_scripts(map_dir):
    d = Path(map_dir) / "battery"
    if not d.is_dir():
        return []
    return sorted(p for p in d.glob("*.py") if not p.name.startswith("_"))


def run_battery(m, node=None, run_all=False, timeout=60):
    """Run battery scripts, optionally filtered to those affecting ``node``.

    Returns (results, skipped_count). With neither ``node`` nor ``run_all``,
    runs everything (the sensible default).
    """
    scripts = collect_scripts(m["map_dir"])
    results, skipped = [], 0
    for path in scripts:
        hdr = parse_header(path)
        if node and node not in affected_nodes(hdr):
            skipped += 1
            continue
        results.append(run_script(path, timeout=timeout))
    return results, skipped
