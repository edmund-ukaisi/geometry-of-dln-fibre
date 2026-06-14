#!/usr/bin/env python3
"""Semantic audit dashboard runner for the DLNFibre Lean library."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import html
import json
import re
import shutil
import shlex
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any


PROJECT_PREFIX = "DLNFibre"
AGGREGATOR_MODULE = "DLNFibre"
AGGREGATOR_FILE = Path("lean/DLNFibre.lean")
LEAN_ROOT = Path("lean")
DEFAULT_OUT = Path(".semantic-audit")
DEFAULT_WORK = DEFAULT_OUT / "work"
CONFIG_PATH = Path("tools/semantic-audit/audit-config.json")
RECORDS_DIR = Path("tools/semantic-audit/records")
RECORD_FILE_NAMES = {
    "lean_reconstructions": "lean-reconstructions.jsonl",
    "source_intentions": "source-intentions.jsonl",
    "comparisons": "comparisons.jsonl",
    "api_boundaries": "api-boundaries.jsonl",
}
SCHEMA_VERSION = "0.1.0"
BUNDLE_ARTIFACT = "semantic-audit-packet-bundle"


@dataclass
class ModuleRecord:
    module: str
    path: str
    imports: list[str]
    imported_by: list[str] = field(default_factory=list)
    public_direct: bool = False
    public_transitive: bool = False
    declaration_count: int = 0
    tracked: bool = True


@dataclass
class Finding:
    finding_id: str
    kind: str
    severity: str
    target: str
    message: str
    recommended_action: str = ""
    evidence: dict[str, Any] = field(default_factory=dict)
    lifecycle: str = "new"


def repo_root_from_script() -> Path:
    return Path(__file__).resolve().parents[2]


def run_cmd(
    args: list[str],
    cwd: Path,
    *,
    check: bool = False,
    timeout: int | None = None,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=check,
        timeout=timeout,
    )


def run_bash(command: str, cwd: Path, *, timeout: int | None = None) -> subprocess.CompletedProcess[str]:
    return run_cmd(["bash", "-lc", command], cwd, timeout=timeout)


def now_utc() -> str:
    return dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    if not path.exists():
        return records
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.strip():
            records.append(json.loads(line))
    return records


def read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_jsonl(path: Path, records: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in records),
        encoding="utf-8",
    )


def load_audit_config(repo: Path) -> dict[str, Any]:
    config = read_json(repo / CONFIG_PATH)
    config.setdefault("schema_version", SCHEMA_VERSION)
    config.setdefault("declarations", [])
    config.setdefault("source_targets", [])
    config.setdefault("comparisons", [])
    config.setdefault("api_boundary_targets", [])
    return config


def load_record_inputs(repo: Path) -> dict[str, list[dict[str, Any]]]:
    record_dir = repo / RECORDS_DIR
    return {
        key: read_jsonl(record_dir / filename)
        for key, filename in RECORD_FILE_NAMES.items()
    }


def declaration_config_by_name(config: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        entry["name"]: entry
        for entry in config.get("declarations", [])
        if entry.get("name")
    }


def answered_by(records: list[dict[str, Any]], field: str) -> dict[str, dict[str, Any]]:
    return {
        record[field]: record
        for record in records
        if record.get(field) and record.get("status") == "answered"
    }


def comparison_records_by_id(records: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        record["comparison_id"]: record
        for record in records
        if record.get("comparison_id")
    }


def technical_gate_failed(attestation: dict[str, Any]) -> bool:
    return any(
        attestation.get(key, {}).get("ok") is False
        for key in ("lake_build", "sorries")
    )


def annotate_declarations(
    declarations: list[dict[str, Any]],
    config: dict[str, Any],
) -> list[dict[str, Any]]:
    configured = declaration_config_by_name(config)
    annotated: list[dict[str, Any]] = []
    for decl in declarations:
        copied = dict(decl)
        entry = configured.get(copied.get("name", ""))
        copied["audit_tier"] = entry.get("tier", "unassigned") if entry else "unassigned"
        copied["audit_reason"] = entry.get("reason", "") if entry else ""
        annotated.append(copied)
    return annotated


def packet_id(kind: str, target: str) -> str:
    safe_target = re.sub(r"[^A-Za-z0-9_.-]+", "-", target).strip("-")
    return f"{kind}.{safe_target}"


def packet_priority(tier: str) -> str:
    if tier == "T0":
        return "high"
    if tier == "T1":
        return "medium"
    return "low"


def comparison_status(
    comparison: dict[str, Any],
    record: dict[str, Any] | None,
    lean_answered: dict[str, dict[str, Any]],
    source_answered: dict[str, dict[str, Any]],
    *,
    semantic_blocked: bool = False,
) -> str:
    if semantic_blocked:
        return "blocked"

    lean_record = lean_answered.get(comparison.get("lean_declaration", ""))
    source_record = source_answered.get(comparison.get("source_id", ""))
    if not record:
        return "blocked" if not lean_record or not source_record else "open"
    if record.get("status") != "answered":
        return "open"
    if not lean_record or not source_record:
        return "stale"
    if record.get("lean_record_id") != lean_record.get("record_id"):
        return "stale"
    if record.get("source_record_id") != source_record.get("record_id"):
        return "stale"
    return "answered"


def module_name_for_file(repo: Path, file: Path) -> str:
    rel = file.relative_to(repo / LEAN_ROOT).with_suffix("")
    return ".".join(rel.parts)


def module_path_for_name(module: str) -> Path:
    return LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?P<module>[A-Za-z0-9_'.]+)\s*$")


def parse_imports(path: Path) -> list[str]:
    imports: list[str] = []
    if not path.exists():
        return imports
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            imports.append(match.group("module"))
    return imports


def lean_files(repo: Path) -> list[Path]:
    return sorted(
        file
        for file in (repo / LEAN_ROOT).rglob("*.lean")
        if ".lake" not in file.parts
    )


def git_tracked_files(repo: Path) -> set[str]:
    result = run_cmd(["git", "ls-files"], repo)
    return set(result.stdout.splitlines())


def git_status(repo: Path) -> list[str]:
    result = run_cmd(["git", "status", "--porcelain"], repo)
    return result.stdout.splitlines()


def build_modules(repo: Path, declarations: list[dict[str, Any]]) -> list[ModuleRecord]:
    tracked = git_tracked_files(repo)
    modules: dict[str, ModuleRecord] = {}
    for file in lean_files(repo):
        module = module_name_for_file(repo, file)
        rel = file.relative_to(repo).as_posix()
        modules[module] = ModuleRecord(
            module=module,
            path=rel,
            imports=parse_imports(file),
            tracked=rel in tracked,
        )

    for module, record in modules.items():
        for imported in record.imports:
            if imported in modules:
                modules[imported].imported_by.append(module)

    for record in modules.values():
        record.imported_by.sort()

    for decl in declarations:
        module = decl.get("module", "")
        if module in modules:
            modules[module].declaration_count += 1

    root = modules.get(AGGREGATOR_MODULE)
    if root:
        direct = [module for module in root.imports if module in modules]
        for module in direct:
            modules[module].public_direct = True
        seen = {AGGREGATOR_MODULE}
        queue = list(direct)
        while queue:
            module = queue.pop(0)
            if module in seen:
                continue
            seen.add(module)
            modules[module].public_transitive = True
            queue.extend(imported for imported in modules[module].imports if imported in modules)
        root.public_transitive = True

    return [modules[name] for name in sorted(modules)]


def command_record(result: subprocess.CompletedProcess[str]) -> dict[str, Any]:
    return {
        "ok": result.returncode == 0,
        "returncode": result.returncode,
        "stdout_tail": "\n".join(result.stdout.splitlines()[-30:]),
        "stderr_tail": "\n".join(result.stderr.splitlines()[-30:]),
    }


def technical_attestation(repo: Path, *, skip_build: bool) -> dict[str, Any]:
    commit = run_cmd(["git", "rev-parse", "HEAD"], repo)
    branch = run_cmd(["git", "branch", "--show-current"], repo)
    status = git_status(repo)

    attestation: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "checked_at": now_utc(),
        "commit": commit.stdout.strip() if commit.returncode == 0 else "",
        "branch": branch.stdout.strip() if branch.returncode == 0 else "",
        "git_status": status,
        "lake_build": {"ok": None, "skipped": skip_build},
        "sorries": {"ok": None, "skipped": skip_build},
    }
    if skip_build:
        return attestation

    build = run_bash("source ~/.elan/env && lake build", repo / LEAN_ROOT, timeout=900)
    if build.returncode != 0:
        retry = run_bash("source ~/.elan/env && lake build", repo / LEAN_ROOT, timeout=900)
        if retry.returncode == 0:
            build = subprocess.CompletedProcess(
                args=retry.args,
                returncode=retry.returncode,
                stdout=(
                    "First build attempt failed; retry succeeded.\n\n"
                    "First stderr tail:\n"
                    + "\n".join(build.stderr.splitlines()[-20:])
                    + "\n\nRetry stdout:\n"
                    + retry.stdout
                ),
                stderr=retry.stderr,
            )
    attestation["lake_build"] = command_record(build)

    sorries = run_bash("source ~/.elan/env && scripts/sorries", repo / LEAN_ROOT, timeout=300)
    attestation["sorries"] = command_record(sorries)
    return attestation


def run_lean_extractor(repo: Path, run_dir: Path) -> Path:
    output = run_dir / "declarations.jsonl"
    script = repo / "tools" / "semantic-audit" / "LeanExtract.lean"
    output.parent.mkdir(parents=True, exist_ok=True)
    result = run_bash(
        f"source ~/.elan/env && lake env lean --run {script} {output}",
        repo / LEAN_ROOT,
        timeout=900,
    )
    if result.returncode != 0:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(f"Lean extractor failed with exit code {result.returncode}")
    return output


def reverse_dependencies(declarations: list[dict[str, Any]]) -> dict[str, list[str]]:
    reverse: dict[str, set[str]] = {}
    names = {decl["name"] for decl in declarations}
    for decl in declarations:
        source = decl["name"]
        for dep in set(decl.get("deps_type", [])) | set(decl.get("deps_value", [])):
            if dep in names:
                reverse.setdefault(dep, set()).add(source)
    return {name: sorted(values) for name, values in sorted(reverse.items())}


def semantic_graph(
    modules: list[ModuleRecord],
    declarations: list[dict[str, Any]],
) -> dict[str, Any]:
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []

    for module in modules:
        nodes.append({
            "id": f"module:{module.module}",
            "kind": "module",
            "label": module.module,
            "properties": asdict(module),
        })
        for imported in module.imports:
            edges.append({
                "source": f"module:{module.module}",
                "target": f"module:{imported}",
                "kind": "IMPORTS",
                "properties": {"internal": imported.startswith(PROJECT_PREFIX)},
            })

    module_names = {module.module for module in modules}
    external_modules = sorted({
        imported
        for module in modules
        for imported in module.imports
        if imported not in module_names
    })
    for module in external_modules:
        nodes.append({
            "id": f"module:{module}",
            "kind": "module",
            "label": module,
            "properties": {
                "module": module,
                "internal": module.startswith(PROJECT_PREFIX),
                "external": True,
                "declaration_count": 0,
            },
        })

    for decl in declarations:
        nodes.append({
            "id": f"decl:{decl['name']}",
            "kind": "declaration",
            "label": decl["name"].split(".")[-1],
            "properties": {
                "name": decl["name"],
                "kind": decl.get("kind"),
                "module": decl.get("module"),
                "audit_tier": decl.get("audit_tier", "unassigned"),
            },
        })
        edges.append({
            "source": f"module:{decl.get('module', '')}",
            "target": f"decl:{decl['name']}",
            "kind": "DECLARES",
            "properties": {},
        })
        for dep in decl.get("deps_type", []):
            edges.append({
                "source": f"decl:{decl['name']}",
                "target": f"decl:{dep}",
                "kind": "USES_CONSTANT_TYPE",
                "properties": {"precision": "lean-environment"},
            })
        for dep in decl.get("deps_value", []):
            edges.append({
                "source": f"decl:{decl['name']}",
                "target": f"decl:{dep}",
                "kind": "USES_CONSTANT_VALUE",
                "properties": {"precision": "lean-environment"},
            })

    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": "semantic-graph",
        "nodes": nodes,
        "edges": edges,
        "reverseDeps": reverse_dependencies(declarations),
    }


def make_packet(
    *,
    kind: str,
    target: str,
    title: str,
    tier: str = "unassigned",
    status: str,
    priority: str | None = None,
    record_id: str = "",
    instructions: str = "",
    inputs: dict[str, Any] | None = None,
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "packet_id": packet_id(kind, target),
        "packet_kind": kind,
        "target": target,
        "title": title,
        "tier": tier,
        "status": status,
        "priority": priority or packet_priority(tier),
        "record_id": record_id,
        "instructions": instructions,
        "inputs": inputs or {},
    }


def generate_work_packets(
    config: dict[str, Any],
    records: dict[str, list[dict[str, Any]]],
    declarations: list[dict[str, Any]],
    *,
    semantic_blocked: bool = False,
) -> list[dict[str, Any]]:
    packets: list[dict[str, Any]] = []
    declaration_names = {decl.get("name", "") for decl in declarations}
    lean_answered = answered_by(records.get("lean_reconstructions", []), "declaration")
    source_answered = answered_by(records.get("source_intentions", []), "source_id")
    comparisons_by_id = comparison_records_by_id(records.get("comparisons", []))
    api_answered = answered_by(records.get("api_boundaries", []), "target_id")

    for entry in config.get("declarations", []):
        name = entry.get("name", "")
        if not name:
            continue
        record = lean_answered.get(name)
        status = "answered" if record and name in declaration_names else "open"
        if semantic_blocked:
            status = "blocked"
        elif record and name not in declaration_names:
            status = "stale"
        packets.append(make_packet(
            kind="lean_reconstruction",
            target=name,
            title=f"Reconstruct Lean declaration {name}",
            tier=entry.get("tier", "unassigned"),
            status=status,
            record_id=record.get("record_id", "") if record else "",
            instructions=(
                "Reconstruct the mathematical content of this Lean declaration from the Lean "
                "signature, local definitions, docstring, and dependencies. Do not use the "
                "paper-intention card as ground truth."
            ),
            inputs={
                "declaration": name,
                "reason": entry.get("reason", ""),
            },
        ))

    for target in config.get("source_targets", []):
        source_id = target.get("source_id", "")
        if not source_id:
            continue
        record = source_answered.get(source_id)
        status = "blocked" if semantic_blocked else ("answered" if record else "open")
        packets.append(make_packet(
            kind="source_intention",
            target=source_id,
            title=f"Reconstruct paper/source intention {source_id}",
            status=status,
            record_id=record.get("record_id", "") if record else "",
            instructions=(
                "Read the indicated source passage and state the intended mathematical claim "
                "without using the current Lean declaration as ground truth."
            ),
            inputs=target,
        ))

    for comparison in config.get("comparisons", []):
        comparison_id = comparison.get("comparison_id", "")
        if not comparison_id:
            continue
        record = comparisons_by_id.get(comparison_id)
        lean_record = lean_answered.get(comparison.get("lean_declaration", ""))
        source_record = source_answered.get(comparison.get("source_id", ""))
        status = comparison_status(
            comparison,
            record,
            lean_answered,
            source_answered,
            semantic_blocked=semantic_blocked,
        )
        packets.append(make_packet(
            kind="comparison",
            target=comparison_id,
            title=f"Compare {comparison.get('lean_declaration', '')} with {comparison.get('source_id', '')}",
            status=status,
            record_id=record.get("comparison_id", "") if record else "",
            instructions=(
                "Compare the independently reconstructed Lean content with the independently "
                "reconstructed source intention. Record exact matches, strict weakenings, "
                "overclaims, convention mismatches, and missing bridge hypotheses."
            ),
            inputs={
                **comparison,
                "lean_reconstruction_record_id": lean_record.get("record_id", "") if lean_record else "",
                "source_intention_record_id": source_record.get("record_id", "") if source_record else "",
            },
        ))

    for boundary in config.get("api_boundary_targets", []):
        target_id = boundary.get("target_id", "")
        if not target_id:
            continue
        record = api_answered.get(target_id)
        status = "blocked" if semantic_blocked else ("answered" if record else "open")
        packets.append(make_packet(
            kind="api_boundary",
            target=target_id,
            title=f"Audit API boundary {target_id}",
            status=status,
            record_id=record.get("record_id", "") if record else "",
            instructions=(
                "Compare the public Lean API's admitted objects and hypotheses with the "
                "paper's mathematical domain. Flag intentional generalizations separately "
                "from accidental overbreadth."
            ),
            inputs=boundary,
        ))

    return packets


def coverage_summary(
    config: dict[str, Any],
    declarations: list[dict[str, Any]],
    records: dict[str, list[dict[str, Any]]],
    packets: list[dict[str, Any]],
    *,
    semantic_blocked: bool = False,
) -> dict[str, Any]:
    configured_decls = declaration_config_by_name(config)
    decl_names = {decl.get("name", "") for decl in declarations}
    t0_names = [name for name, entry in configured_decls.items() if entry.get("tier") == "T0"]
    lean_packet_status = packet_status_map(packets, kind="lean_reconstruction")
    source_packet_status = packet_status_map(packets, kind="source_intention")
    api_packet_status = packet_status_map(packets, kind="api_boundary")

    comparison_answered = {
        packet["target"]
        for packet in packets
        if packet.get("packet_kind") == "comparison" and packet.get("status") == "answered"
    }

    packet_status: dict[str, int] = {}
    packet_kind: dict[str, int] = {}
    for packet in packets:
        packet_status[packet["status"]] = packet_status.get(packet["status"], 0) + 1
        packet_kind[packet["packet_kind"]] = packet_kind.get(packet["packet_kind"], 0) + 1

    return {
        "schema_version": SCHEMA_VERSION,
        "semantic_status": "blocked" if semantic_blocked else "ready",
        "configured_declarations": len(configured_decls),
        "configured_declarations_present": sum(1 for name in configured_decls if name in decl_names),
        "t0_total": len(t0_names),
        "t0_lean_reconstructions_answered": sum(1 for name in t0_names if lean_packet_status.get(name) == "answered" and name in decl_names),
        "source_intentions_total": len(config.get("source_targets", [])),
        "source_intentions_answered": sum(
            1
            for target in config.get("source_targets", [])
            if source_packet_status.get(target.get("source_id", "")) == "answered" and not semantic_blocked
        ),
        "comparisons_total": len(config.get("comparisons", [])),
        "comparisons_answered": sum(
            1
            for comparison in config.get("comparisons", [])
            if comparison.get("comparison_id") in comparison_answered
        ),
        "api_boundaries_total": len(config.get("api_boundary_targets", [])),
        "api_boundaries_answered": sum(
            1
            for target in config.get("api_boundary_targets", [])
            if api_packet_status.get(target.get("target_id", "")) == "answered" and not semantic_blocked
        ),
        "packets_total": len(packets),
        "packets_open": sum(1 for packet in packets if packet.get("status") == "open"),
        "packets_unanswered": sum(1 for packet in packets if packet.get("status") != "answered"),
        "packet_status": packet_status,
        "packet_kind": packet_kind,
    }


STRONG_DOC_WORDS = {
    "complete",
    "classification",
    "classifies",
    "equiv",
    "equivalence",
    "bijection",
    "iff",
    "closure",
    "minimal",
    "maximal",
}
STALE_DOC_WORDS = {"deferred", "remaining", "future", "todo"}


def new_finding(counter: int, **kwargs: Any) -> Finding:
    return Finding(finding_id=f"semantic-audit-{counter:05d}", **kwargs)


def deterministic_findings(
    repo: Path,
    modules: list[ModuleRecord],
    declarations: list[dict[str, Any]],
    attestation: dict[str, Any],
    config: dict[str, Any],
    records: dict[str, list[dict[str, Any]]],
    packets: list[dict[str, Any]],
) -> list[Finding]:
    findings: list[Finding] = []
    counter = 1

    def add(**kwargs: Any) -> None:
        nonlocal counter
        findings.append(new_finding(counter, **kwargs))
        counter += 1

    if attestation.get("lake_build", {}).get("ok") is False:
        add(
            kind="technical_attestation_failed",
            severity="blocker",
            target="lake build",
            message="The semantic audit snapshot did not pass `lake build`.",
            recommended_action="Fix the technical Lean build before trusting semantic audit output.",
            evidence=attestation.get("lake_build", {}),
        )

    if attestation.get("sorries", {}).get("ok") is False:
        add(
            kind="technical_attestation_failed",
            severity="blocker",
            target="scripts/sorries",
            message="The semantic audit snapshot did not pass the sorry/axiom hygiene script.",
            recommended_action="Clear sorry/axiom/native_decide/#exit policy failures before semantic review.",
            evidence=attestation.get("sorries", {}),
        )

    semantic_blocked = technical_gate_failed(attestation)

    for module in modules:
        if module.module.startswith(PROJECT_PREFIX) and not module.tracked:
            add(
                kind="untracked_lean_file",
                severity="high",
                target=module.module,
                message="A Lean module exists in the working tree but is not tracked by git.",
                recommended_action="Track the file or remove it from the audited artifact.",
                evidence={"path": module.path},
            )
        if (
            module.module != AGGREGATOR_MODULE
            and module.module.startswith(PROJECT_PREFIX)
            and not module.public_transitive
        ):
            add(
                kind="module_not_publicly_imported",
                severity="medium",
                target=module.module,
                message="A project Lean module is not reachable from the public aggregator.",
                recommended_action=f"Import it from {AGGREGATOR_FILE.as_posix()} or document why it is private.",
                evidence={"path": module.path},
            )

    decl_names = {decl.get("name", "") for decl in declarations}
    lean_answered = answered_by(records.get("lean_reconstructions", []), "declaration")
    source_answered = answered_by(records.get("source_intentions", []), "source_id")
    comparisons_by_id = comparison_records_by_id(records.get("comparisons", []))
    lean_packet_status = packet_status_map(packets, kind="lean_reconstruction")
    source_packet_status = packet_status_map(packets, kind="source_intention")
    comparison_packet_status = packet_status_map(packets, kind="comparison")

    if not semantic_blocked:
        for entry in config.get("declarations", []):
            name = entry.get("name", "")
            if not name:
                continue
            if name not in decl_names:
                add(
                    kind="configured_declaration_missing",
                    severity="high",
                    target=name,
                    message="Audit config names a declaration that was not found in the extracted Lean snapshot.",
                    recommended_action="Update the audit config or restore/export the expected declaration.",
                    evidence={"tier": entry.get("tier", "unassigned"), "reason": entry.get("reason", "")},
                )
            if entry.get("tier") == "T0" and name in decl_names and lean_packet_status.get(name) != "answered":
                add(
                    kind="stale_lean_reconstruction" if lean_packet_status.get(name) == "stale" else "missing_lean_reconstruction",
                    severity="high",
                    target=name,
                    message=(
                        "A T0 declaration's independent Lean reconstruction is stale relative to the current context."
                        if lean_packet_status.get(name) == "stale"
                        else "A T0 declaration has no current answered independent Lean reconstruction record."
                    ),
                    recommended_action=(
                        "Regenerate a worker bundle and replace the stale Lean reconstruction record."
                        if lean_packet_status.get(name) == "stale"
                        else "Complete the generated lean_reconstruction packet for this declaration."
                    ),
                    evidence={"tier": "T0", "reason": entry.get("reason", ""), "packet_status": lean_packet_status.get(name, "")},
                )

        for target in config.get("source_targets", []):
            source_id = target.get("source_id", "")
            if source_id and source_packet_status.get(source_id) != "answered":
                add(
                    kind="stale_source_intention" if source_packet_status.get(source_id) == "stale" else "missing_source_intention",
                    severity="medium",
                    target=source_id,
                    message=(
                        "A configured paper/source target has a stale source-intention record."
                        if source_packet_status.get(source_id) == "stale"
                        else "A configured paper/source target has no current answered source-intention record."
                    ),
                    recommended_action=(
                        "Regenerate a worker bundle and replace the stale source-intention record."
                        if source_packet_status.get(source_id) == "stale"
                        else "Complete the generated source_intention packet for this target."
                    ),
                    evidence={"paper_label": target.get("paper_label", ""), "path": target.get("path", ""), "packet_status": source_packet_status.get(source_id, "")},
                )

        for comparison in config.get("comparisons", []):
            comparison_id = comparison.get("comparison_id", "")
            if not comparison_id:
                continue
            status = comparison_packet_status.get(comparison_id) or comparison_status(
                comparison,
                comparisons_by_id.get(comparison_id),
                lean_answered,
                source_answered,
            )
            if status == "answered":
                continue
            add(
                kind="stale_comparison" if status == "stale" else "missing_comparison",
                severity="medium",
                target=comparison_id,
                message=(
                    "A configured Lean/source alignment record is stale relative to its prerequisite cards."
                    if status == "stale"
                    else "A configured Lean/source alignment has no answered comparison record."
                ),
                recommended_action=(
                    "Regenerate the comparison against the current Lean reconstruction and source-intention records."
                    if status == "stale"
                    else "Complete the generated comparison packet after its prerequisite cards exist."
                ),
                evidence={**comparison, "comparison_status": status},
            )

        for packet in packets:
            if packet.get("status") == "answered":
                continue
            severity = "high" if packet.get("tier") == "T0" and packet.get("packet_kind") == "lean_reconstruction" else "low"
            stale = packet.get("status") == "stale"
            blocked = packet.get("status") == "blocked"
            add(
                kind="stale_work_packet" if stale else ("blocked_work_packet" if blocked else "open_work_packet"),
                severity=severity,
                target=packet.get("packet_id", ""),
                message=(
                    "A generated semantic-audit work packet has a stale durable record."
                    if stale
                    else (
                        "A generated semantic-audit work packet is blocked on prerequisite records."
                        if blocked
                        else "A generated semantic-audit work packet is not answered yet."
                    )
                ),
                recommended_action=(
                    "Regenerate its worker bundle and replace the durable record with a current answer."
                    if stale
                    else (
                        "Complete the prerequisite Lean/source packets before assigning this packet."
                        if blocked
                        else "Assign the packet to a human or subagent and add the returned structured record."
                    )
                ),
                evidence={
                    "packet_kind": packet.get("packet_kind", ""),
                    "packet_status": packet.get("status", ""),
                    "packet_target": packet.get("target", ""),
                    "stale_reasons": packet.get("stale_reasons", []),
                },
            )

    for decl in declarations:
        name = decl["name"]
        doc = (decl.get("doc") or "").lower()
        words = {word for word in STRONG_DOC_WORDS if word in doc}
        if words:
            has_shape = any(token in name.lower() for token in ("iff", "equiv", "closure", "minimal", "maximal"))
            severity = "low" if has_shape else "medium"
            add(
                kind="strong_docstring_word",
                severity=severity,
                target=name,
                message="Docstring uses strong mathematical wording that may need semantic alignment.",
                recommended_action="Check that the Lean statement supports the docstring wording or add an explicit waiver/comparison.",
                evidence={"words": sorted(words), "module": decl.get("module")},
            )
        stale = {word for word in STALE_DOC_WORDS if word in doc}
        if stale:
            add(
                kind="stale_docstring_word",
                severity="low",
                target=name,
                message="Docstring contains wording that often becomes stale after formalisation progresses.",
                recommended_action="Check whether the prose still matches the current Lean artifact.",
                evidence={"words": sorted(stale), "module": decl.get("module")},
            )

    reverse = reverse_dependencies(declarations)
    for decl in declarations:
        rev_count = len(reverse.get(decl["name"], []))
        if (
            rev_count >= 15
            and decl.get("kind") in {"def", "inductive", "theorem"}
            and decl.get("audit_tier", "unassigned") == "unassigned"
        ):
            add(
                kind="high_reverse_dependency_surface",
                severity="low",
                target=decl["name"],
                message="Declaration has many project reverse dependencies and should be considered for T0/T1 semantic coverage.",
                recommended_action="Assign an audit tier or confirm that this is proof plumbing.",
                evidence={"reverse_dependency_count": rev_count, "module": decl.get("module")},
            )

    return findings


def dashboard_payload(
    run: dict[str, Any],
    attestation: dict[str, Any],
    modules: list[ModuleRecord],
    declarations: list[dict[str, Any]],
    graph: dict[str, Any],
    findings: list[Finding],
    config: dict[str, Any],
    records: dict[str, list[dict[str, Any]]],
    packets: list[dict[str, Any]],
    coverage: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "run": run,
        "attestation": attestation,
        "config": config,
        "modules": [asdict(module) for module in modules],
        "declarations": declarations,
        "graph": graph,
        "records": records,
        "work_packets": packets,
        "coverage": coverage,
        "findings": [asdict(finding) for finding in findings],
    }


def h(value: Any) -> str:
    return html.escape(str(value if value is not None else ""), quote=True)


def html_chip(text: Any, cls: str = "") -> str:
    cls_attr = f" {h(cls)}" if cls else ""
    return f'<span class="chip{cls_attr}">{h(text)}</span>'


def css_class(value: Any) -> str:
    return re.sub(r"[^A-Za-z0-9_-]+", "-", str(value or "").strip()).strip("-")


def status_class(status: str) -> str:
    if status == "answered":
        return "pass"
    if status == "blocked":
        return "fail"
    return "warn"


def packet_status_map(
    packets: list[dict[str, Any]],
    *,
    kind: str | None = None,
) -> dict[str, str]:
    return {
        expected_record_target(packet): packet.get("status", "")
        for packet in packets
        if kind is None or packet.get("packet_kind") == kind
    }


def tier_class(tier: str) -> str:
    return f"tier-{css_class(str(tier).lower())}" if tier else "tier-unassigned"


def attestation_status(record: dict[str, Any]) -> tuple[str, str]:
    if record.get("skipped"):
        return "skipped", "warn"
    if record.get("ok") is True:
        return "pass", "pass"
    if record.get("ok") is False:
        return "fail", "fail"
    return "unknown", "warn"


def dashboard_source_label(module_by_name: dict[str, ModuleRecord], decl: dict[str, Any]) -> str:
    module = module_by_name.get(decl.get("module", ""))
    source_range = decl.get("source_range") or {}
    range_info = source_range.get("range") or {}
    start = range_info.get("start") or {}
    if not module or not start.get("line"):
        return ""
    return f"{module.path}:{start['line']}"


def initial_run_meta(run: dict[str, Any], attestation: dict[str, Any]) -> str:
    dirty = len(attestation.get("git_status", []))
    build_status, build_class = attestation_status(attestation.get("lake_build", {}))
    sorries_status, sorries_class = attestation_status(attestation.get("sorries", {}))
    return "".join([
        html_chip(f"run {run.get('run_id', 'unknown')}"),
        html_chip(f"commit {str(run.get('commit', ''))[:12] or 'unknown'}"),
        html_chip(f"lake build {build_status}", build_class),
        html_chip(f"sorries {sorries_status}", sorries_class),
        html_chip(f"{dirty} git status entries", "pass" if dirty == 0 else "warn"),
    ])


def initial_stats(
    declarations: list[dict[str, Any]],
    modules: list[ModuleRecord],
    findings: list[Finding],
    coverage: dict[str, Any],
) -> str:
    high_plus = sum(1 for finding in findings if finding.severity in {"blocker", "high"})
    semantic_blocked = coverage.get("semantic_status") == "blocked"

    def ratio(answered_key: str, total_key: str) -> str:
        if semantic_blocked:
            return "blocked"
        return f"{coverage.get(answered_key, 0)}/{coverage.get(total_key, 0)}"

    values = [
        ("Declarations", len(declarations)),
        ("Modules", len(modules)),
        ("T0 Lean cards", ratio("t0_lean_reconstructions_answered", "t0_total")),
        ("Source cards", ratio("source_intentions_answered", "source_intentions_total")),
        ("Comparisons", ratio("comparisons_answered", "comparisons_total")),
        ("API boundary", ratio("api_boundaries_answered", "api_boundaries_total")),
        ("Unanswered packets", coverage.get("packets_unanswered", coverage.get("packets_open", 0))),
        ("Findings", len(findings)),
        ("High+", high_plus),
    ]
    return "".join(
        f'<div class="stat"><strong>{h(value)}</strong><span>{h(label)}</span></div>'
        for label, value in values
    )


def initial_decl_rows(
    declarations: list[dict[str, Any]],
    module_by_name: dict[str, ModuleRecord],
    selected_name: str | None,
) -> str:
    if not declarations:
        return '<tr><td colspan="6" class="muted">No declarations found.</td></tr>'
    rows: list[str] = []
    for decl in declarations[:1000]:
        selected = " selected" if decl.get("name") == selected_name else ""
        tier = decl.get("audit_tier", "unassigned")
        rows.append(
            f'<tr class="{selected.strip()}" data-name="{h(decl.get("name", ""))}">'
            f'<td><code>{h(decl.get("name", ""))}</code>'
            f'<div class="muted">{h(dashboard_source_label(module_by_name, decl))}</div></td>'
            f'<td>{h(decl.get("kind", ""))}</td>'
            f'<td>{html_chip(tier, tier_class(tier))}</td>'
            f'<td>{h(decl.get("module", ""))}</td>'
            f'<td>{h(len(decl.get("deps_type", [])))}</td>'
            f'<td>{h(len(decl.get("deps_value", [])))}</td>'
            "</tr>"
        )
    return "".join(rows)


def initial_finding_cards(findings: list[Finding]) -> str:
    if not findings:
        return '<div class="muted">No findings.</div>'
    cards: list[str] = []
    for finding in findings:
        cards.append(
            f'<div class="finding {h(finding.severity)}">'
            '<div class="finding-title">'
            f'<span>{h(finding.kind)}</span>'
            f'<span class="muted">{h(finding.severity)}</span>'
            '</div>'
            f'<div><code>{h(finding.target)}</code></div>'
            f'<div>{h(finding.message)}</div>'
            + (
                f'<div class="muted">Action: {h(finding.recommended_action)}</div>'
                if finding.recommended_action else ""
            )
            + '</div>'
        )
    return "".join(cards)


def initial_packet_rows(packets: list[dict[str, Any]]) -> str:
    if not packets:
        return '<tr><td colspan="6" class="muted">No work packets generated.</td></tr>'
    rows: list[str] = []
    for packet in packets:
        status = packet.get("status", "")
        tier = packet.get("tier", "unassigned")
        rows.append(
            '<tr>'
            f'<td><code>{h(packet.get("packet_id", ""))}</code>'
            f'<div class="muted">{h(packet.get("title", ""))}</div></td>'
            f'<td>{h(packet.get("packet_kind", ""))}</td>'
            f'<td><code>{h(packet.get("target", ""))}</code></td>'
            f'<td>{html_chip(tier, tier_class(tier))}</td>'
            f'<td>{html_chip(status, status_class(status))}</td>'
            f'<td>{h(packet.get("priority", ""))}</td>'
            '</tr>'
        )
    return "".join(rows)


def initial_source_rows(config: dict[str, Any], records: dict[str, list[dict[str, Any]]]) -> str:
    targets = config.get("source_targets", [])
    if not targets:
        return '<tr><td colspan="4" class="muted">No source targets configured.</td></tr>'
    source_answered = answered_by(records.get("source_intentions", []), "source_id")
    rows: list[str] = []
    for target in targets:
        source_id = target.get("source_id", "")
        status = "answered" if source_id in source_answered else "open"
        rows.append(
            '<tr>'
            f'<td><code>{h(source_id)}</code><div class="muted">{h(target.get("summary", ""))}</div></td>'
            f'<td>{h(target.get("paper_label", ""))}</td>'
            f'<td>{html_chip(status, status_class(status))}</td>'
            f'<td>{h(target.get("line_hint", ""))}</td>'
            '</tr>'
        )
    return "".join(rows)


def initial_module_rows(modules: list[ModuleRecord]) -> str:
    return "".join(
        '<tr>'
        f'<td><code>{h(module.module)}</code><div class="muted">{h(module.path)}</div></td>'
        f'<td>{h(module.declaration_count)}</td>'
        f'<td>{h(len(module.imports))}</td>'
        f'<td>{h(len(module.imported_by))}</td>'
        '</tr>'
        for module in modules
    )


def initial_decl_detail(
    declarations: list[dict[str, Any]],
    module_by_name: dict[str, ModuleRecord],
    graph: dict[str, Any],
    findings: list[Finding],
    records: dict[str, list[dict[str, Any]]],
    packets: list[dict[str, Any]],
    selected_name: str | None,
) -> str:
    decl = next((item for item in declarations if item.get("name") == selected_name), None)
    if not decl:
        return "Select a declaration."
    reverse = graph.get("reverseDeps", {}).get(decl.get("name"), [])
    local_findings = [f for f in findings if f.target == decl.get("name")]
    finding_chips = " ".join(html_chip(f"{f.severity}: {f.kind}", f.severity) for f in local_findings) or "none"
    lean_record = answered_by(records.get("lean_reconstructions", []), "declaration").get(decl.get("name"))
    valid_comparison_ids = {
        packet.get("target")
        for packet in packets
        if packet.get("packet_kind") == "comparison" and packet.get("status") == "answered"
    }
    comparison_records = [
        record
        for record in records.get("comparisons", [])
        if record.get("lean_declaration") == decl.get("name")
        and record.get("comparison_id") in valid_comparison_ids
    ]
    local_packets = [
        packet
        for packet in packets
        if packet.get("target") == decl.get("name")
        or packet.get("inputs", {}).get("lean_declaration") == decl.get("name")
    ]
    record_summary = h(lean_record.get("summary", "")) if lean_record else "none"
    comparison_summary = (
        " ".join(html_chip(record.get("alignment", record.get("status", "")), status_class(record.get("status", ""))) for record in comparison_records)
        or "none"
    )
    packet_summary = (
        " ".join(html_chip(packet.get("status", ""), status_class(packet.get("status", ""))) for packet in local_packets)
        or "none"
    )
    tier = decl.get("audit_tier", "unassigned")
    return (
        f'<div class="kv"><div class="key">Name</div><div><code>{h(decl.get("name", ""))}</code></div></div>'
        f'<div class="kv"><div class="key">Kind</div><div>{h(decl.get("kind", ""))}</div></div>'
        f'<div class="kv"><div class="key">Tier</div><div>{html_chip(tier, tier_class(tier))} {h(decl.get("audit_reason", ""))}</div></div>'
        f'<div class="kv"><div class="key">Module</div><div>{h(decl.get("module", ""))}</div></div>'
        f'<div class="kv"><div class="key">Source</div><div>{h(dashboard_source_label(module_by_name, decl) or "unknown")}</div></div>'
        f'<div class="kv"><div class="key">Type</div><div><pre>{h(decl.get("type", ""))}</pre></div></div>'
        f'<div class="kv"><div class="key">Doc</div><div><pre>{h(decl.get("doc") or "(none)")}</pre></div></div>'
        f'<div class="kv"><div class="key">Deps</div><div>{html_chip(str(len(decl.get("deps_type", []))) + " type")} '
        f'{html_chip(str(len(decl.get("deps_value", []))) + " value/proof")}</div></div>'
        f'<div class="kv"><div class="key">Reverse</div><div>{html_chip(str(len(reverse)) + " dependents")}</div></div>'
        f'<div class="kv"><div class="key">Lean card</div><div>{record_summary}</div></div>'
        f'<div class="kv"><div class="key">Comparisons</div><div>{comparison_summary}</div></div>'
        f'<div class="kv"><div class="key">Packets</div><div>{packet_summary}</div></div>'
        f'<div class="kv"><div class="key">Findings</div><div>{finding_chips}</div></div>'
    )


PREFERRED_DASHBOARD_FOCUS = [
    "DLNFibre.Core.rankPattern_eq_iff_orbit",
    "DLNFibre.Core.orbit_of_rankPattern_eq",
    "DLNFibre.Core.rankPattern_eq_cumul_barMult",
    "DLNFibre.Core.exists_barcode_rankPattern",
    "DLNFibre.Core.rankPattern",
]


def preferred_dashboard_focus(declarations: list[dict[str, Any]]) -> str | None:
    names = {decl.get("name", "") for decl in declarations}
    for name in PREFERRED_DASHBOARD_FOCUS:
        if name in names:
            return name
    for decl in declarations:
        if decl.get("audit_tier") == "T0":
            return decl.get("name")
    return declarations[0]["name"] if declarations else None


def safe_json_for_script(value: Any) -> str:
    return (
        json.dumps(value, separators=(",", ":"))
        .replace("<", "\\u003c")
        .replace(">", "\\u003e")
        .replace("&", "\\u0026")
    )


def render_dashboard(repo: Path, run_dir: Path, payload: dict[str, Any]) -> Path:
    template = (repo / "tools" / "semantic-audit" / "dashboard" / "template.html").read_text(encoding="utf-8")
    declarations = payload["declarations"]
    modules = [ModuleRecord(**module) for module in payload["modules"]]
    findings = [Finding(**finding) for finding in payload["findings"]]
    module_by_name = {module.module: module for module in modules}
    selected_name = preferred_dashboard_focus(declarations)
    html_text = (
        template
        .replace("__RUN_META__", initial_run_meta(payload["run"], payload["attestation"]))
        .replace("__STATS__", initial_stats(declarations, modules, findings, payload["coverage"]))
        .replace("__DECL_ROWS__", initial_decl_rows(declarations, module_by_name, selected_name))
        .replace("__FINDING_CARDS__", initial_finding_cards(findings))
        .replace("__PACKET_ROWS__", initial_packet_rows(payload["work_packets"]))
        .replace("__SOURCE_ROWS__", initial_source_rows(payload["config"], payload["records"]))
        .replace("__MODULE_ROWS__", initial_module_rows(modules))
        .replace("__DECL_DETAIL__", initial_decl_detail(
            declarations,
            module_by_name,
            payload["graph"],
            findings,
            payload["records"],
            payload["work_packets"],
            selected_name,
        ))
        .replace("__AUDIT_DATA__", safe_json_for_script(payload))
    )
    out = run_dir / "dashboard" / "index.html"
    out.parent.mkdir(parents=True, exist_ok=True)
    vendor_src = repo / "tools" / "semantic-audit" / "dashboard" / "vendor"
    if vendor_src.exists():
        shutil.copytree(vendor_src, out.parent / "vendor", dirs_exist_ok=True)
    out.write_text(html_text, encoding="utf-8")
    return out


def current_commit(repo: Path) -> str:
    result = run_cmd(["git", "rev-parse", "HEAD"], repo)
    return result.stdout.strip() if result.returncode == 0 else ""


def run_audit(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    out_root = (repo / args.out).resolve()
    config = load_audit_config(repo)
    records = load_record_inputs(repo)
    timestamp = dt.datetime.now(dt.UTC).strftime("%Y%m%dT%H%M%SZ")
    commit = current_commit(repo)
    run_id = f"{timestamp}-{commit[:8] or 'dirty'}"
    run_dir = out_root / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    run_record = {
        "schema_version": SCHEMA_VERSION,
        "run_id": run_id,
        "created_at": now_utc(),
        "commit": commit,
        "project_prefix": PROJECT_PREFIX,
        "aggregator_module": AGGREGATOR_MODULE,
    }
    write_json(run_dir / "audit-run.json", run_record)

    attestation = technical_attestation(repo, skip_build=args.skip_build)
    write_json(run_dir / "technical-attestation.json", attestation)

    if (
        not args.skip_build
        and (
            attestation.get("lake_build", {}).get("ok") is False
            or attestation.get("sorries", {}).get("ok") is False
        )
    ):
        declarations: list[dict[str, Any]] = []
    else:
        decl_path = run_lean_extractor(repo, run_dir)
        declarations = read_jsonl(decl_path)
    declarations = annotate_declarations(declarations, config)
    write_jsonl(run_dir / "declarations.jsonl", declarations)
    modules = build_modules(repo, declarations)
    graph = semantic_graph(modules, declarations)
    semantic_blocked = technical_gate_failed(attestation)
    packets = generate_work_packets(config, records, declarations, semantic_blocked=semantic_blocked)
    state_for_staleness = {
        "run_dir": run_dir,
        "run": run_record,
        "config": config,
        "declarations": declarations,
        "modules": [asdict(module) for module in modules],
        "graph": graph,
        "packets": packets,
        "records": records,
    }
    apply_context_staleness(repo, state_for_staleness, packets, semantic_blocked=semantic_blocked)
    coverage = coverage_summary(config, declarations, records, packets, semantic_blocked=semantic_blocked)
    findings = deterministic_findings(repo, modules, declarations, attestation, config, records, packets)

    write_json(run_dir / "audit-config.resolved.json", config)
    for key, filename in RECORD_FILE_NAMES.items():
        write_jsonl(run_dir / filename, records.get(key, []))
    write_jsonl(run_dir / "work-packets.jsonl", packets)
    write_json(run_dir / "coverage-summary.json", coverage)
    write_jsonl(run_dir / "modules.jsonl", [asdict(module) for module in modules])
    write_json(run_dir / "semantic-graph.json", graph)
    write_jsonl(run_dir / "findings.jsonl", [asdict(finding) for finding in findings])
    payload = dashboard_payload(
        run_record,
        attestation,
        modules,
        declarations,
        graph,
        findings,
        config,
        records,
        packets,
        coverage,
    )
    dashboard = render_dashboard(repo, run_dir, payload)

    latest = out_root / "latest"
    if latest.exists() or latest.is_symlink():
        if latest.is_dir() and not latest.is_symlink():
            shutil.rmtree(latest)
        else:
            latest.unlink()
    try:
        latest.symlink_to(run_dir.relative_to(out_root), target_is_directory=True)
    except OSError:
        shutil.copytree(run_dir, latest)

    print(f"Run: {run_id}")
    print(f"Declarations: {len(declarations)}")
    print(f"Modules: {len(modules)}")
    print(f"Unanswered packets: {coverage.get('packets_unanswered', coverage.get('packets_open', 0))}")
    print(f"Findings: {len(findings)}")
    print(f"Dashboard: {dashboard}")


def latest_run_dir(repo: Path, out: str | Path = DEFAULT_OUT) -> Path:
    latest = (repo / out / "latest").resolve()
    if not latest.exists():
        raise SystemExit(
            f"No semantic audit latest run found at {latest}. Run `python3 tools/semantic-audit/semantic_audit.py run` first."
        )
    return latest


def load_latest_state(repo: Path, out: str | Path = DEFAULT_OUT) -> dict[str, Any]:
    run_dir = latest_run_dir(repo, out)
    records = {
        key: read_jsonl(run_dir / filename)
        for key, filename in RECORD_FILE_NAMES.items()
    }
    return {
        "run_dir": run_dir,
        "run": read_json(run_dir / "audit-run.json"),
        "config": read_json(run_dir / "audit-config.resolved.json"),
        "declarations": read_jsonl(run_dir / "declarations.jsonl"),
        "modules": read_jsonl(run_dir / "modules.jsonl"),
        "graph": read_json(run_dir / "semantic-graph.json"),
        "packets": read_jsonl(run_dir / "work-packets.jsonl"),
        "records": records,
    }


def load_state_for_cli(repo: Path, out: str | Path, expected_run_id: str | None = None) -> dict[str, Any]:
    state = load_latest_state(repo, out)
    if expected_run_id and state.get("run", {}).get("run_id") != expected_run_id:
        raise SystemExit(
            "Latest semantic-audit run is "
            f"{state.get('run', {}).get('run_id', '')!r}, expected {expected_run_id!r}. "
            "Refresh the dashboard or rerun the command from the current Work Packets tab."
        )
    return state


def packet_identity(packet: dict[str, Any]) -> str:
    return packet.get("packet_id") or packet.get("target") or ""


def find_packet(packets: list[dict[str, Any]], selector: str) -> dict[str, Any]:
    matches = [
        packet for packet in packets
        if selector in {packet.get("packet_id", ""), packet.get("target", ""), packet.get("inputs", {}).get("declaration", "")}
    ]
    if not matches:
        raise SystemExit(f"No packet matches selector: {selector}")
    if len(matches) > 1:
        options = "\n".join(f"- {packet_identity(packet)} ({packet.get('packet_kind')}, {packet.get('status')})" for packet in matches)
        raise SystemExit(f"Selector is ambiguous: {selector}\n{options}")
    return matches[0]


def source_label_from_decl(decl: dict[str, Any], modules_by_name: dict[str, dict[str, Any]]) -> str:
    module = modules_by_name.get(decl.get("module", ""))
    if not module or not decl.get("source_range", {}).get("range"):
        return ""
    line = decl["source_range"]["range"]["start"]["line"]
    return f"{module.get('path', '')}:{line}"


def source_excerpt(repo: Path, rel_path: str, start_line: int | None, end_line: int | None = None, *, radius: int = 8) -> dict[str, Any]:
    path = repo / rel_path
    if not rel_path or not path.exists():
        return {"path": rel_path, "available": False, "text": ""}
    lines = path.read_text(encoding="utf-8").splitlines()
    if start_line is None:
        return {"path": rel_path, "available": True, "text": ""}
    start = max(1, start_line - radius)
    end = min(len(lines), (end_line or start_line) + radius)
    text = "\n".join(
        f"{number}: {lines[number - 1]}"
        for number in range(start, end + 1)
    )
    return {
        "path": rel_path,
        "available": True,
        "start_line": start,
        "end_line": end,
        "text": text,
    }


def declaration_excerpt(repo: Path, decl: dict[str, Any], modules_by_name: dict[str, dict[str, Any]]) -> dict[str, Any]:
    module = modules_by_name.get(decl.get("module", ""))
    source_range = decl.get("source_range", {}).get("range", {})
    return source_excerpt(
        repo,
        module.get("path", "") if module else "",
        source_range.get("start", {}).get("line"),
        source_range.get("end", {}).get("line"),
    )


def line_hint_excerpt(repo: Path, target: dict[str, Any]) -> dict[str, Any]:
    hint = target.get("line_hint", "")
    numbers = [int(value) for value in re.findall(r"\b\d+\b", hint)]
    if len(numbers) >= 2:
        return source_excerpt(repo, target.get("path", ""), numbers[0], numbers[1], radius=5)
    if len(numbers) == 1:
        return source_excerpt(repo, target.get("path", ""), numbers[0], None, radius=12)
    return keyword_source_excerpt(repo, target)


STOPWORDS = {
    "a",
    "an",
    "and",
    "around",
    "as",
    "at",
    "between",
    "by",
    "for",
    "from",
    "in",
    "into",
    "is",
    "it",
    "let",
    "of",
    "on",
    "or",
    "paper",
    "section",
    "the",
    "to",
    "with",
}


def keyword_source_excerpt(repo: Path, target: dict[str, Any], *, radius: int = 36) -> dict[str, Any]:
    rel_path = target.get("path", "")
    path = repo / rel_path
    if not rel_path or not path.exists():
        return {"path": rel_path, "available": False, "text": ""}

    lines = path.read_text(encoding="utf-8").splitlines()
    haystack = " ".join(
        str(target.get(key, ""))
        for key in ("source_id", "paper_label", "line_hint", "summary")
    )
    terms = [
        term
        for term in re.findall(r"[a-z][a-z0-9]*", haystack.lower())
        if len(term) >= 3 and term not in STOPWORDS
    ]
    if not terms:
        return source_excerpt(repo, rel_path, 1, min(len(lines), 30), radius=0)

    lowered_lines = [line.lower() for line in lines]
    best_score = 0
    best_line: int | None = None
    for index in range(1, len(lines) + 1):
        start = max(1, index - radius)
        end = min(len(lines), index + radius)
        window = "\n".join(lowered_lines[start - 1:end])
        score = sum(1 for term in set(terms) if term in window)
        if score > best_score:
            best_score = score
            best_line = index

    if best_line is None:
        return source_excerpt(repo, rel_path, 1, min(len(lines), 30), radius=0)

    excerpt = source_excerpt(repo, rel_path, best_line, None, radius=radius)
    excerpt["selection"] = {
        "method": "keyword_fallback",
        "score": best_score,
        "terms": sorted(set(terms))[:30],
    }
    return excerpt


def short_decl_context(
    name: str,
    declarations_by_name: dict[str, dict[str, Any]],
    lean_answered: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    decl = declarations_by_name.get(name, {})
    record = lean_answered.get(name)
    return {
        "name": name,
        "kind": decl.get("kind", ""),
        "module": decl.get("module", ""),
        "type": decl.get("type", ""),
        "doc": decl.get("doc", ""),
        "answer_record_id": record.get("record_id", "") if record else "",
        "answer_summary": record.get("summary", "") if record else "",
    }


def build_lean_reconstruction_context(repo: Path, state: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    declarations = state["declarations"]
    declarations_by_name = {decl.get("name", ""): decl for decl in declarations}
    modules_by_name = {module.get("module", ""): module for module in state["modules"]}
    lean_answered = answered_by(state["records"].get("lean_reconstructions", []), "declaration")
    declaration = packet.get("inputs", {}).get("declaration") or packet.get("target", "")
    decl = declarations_by_name.get(declaration)
    if not decl:
        raise SystemExit(f"Declaration not found in latest audit extraction: {declaration}")

    type_deps = list(dict.fromkeys(decl.get("deps_type", [])))
    value_deps = list(dict.fromkeys(decl.get("deps_value", [])))
    proof_only_deps = [name for name in value_deps if name not in set(type_deps)]
    reverse = state.get("graph", {}).get("reverseDeps", {}).get(declaration, [])
    return {
        "schema_version": SCHEMA_VERSION,
        "context_kind": "lean_reconstruction",
        "generated_at": now_utc(),
        "packet": packet,
        "decorrelation": (
            "This context is for Lean reconstruction. It intentionally excludes source-intention "
            "and comparison records; use only the Lean signature, docstring, source excerpt, and Lean dependency context."
        ),
        "declaration": {
            "name": declaration,
            "kind": decl.get("kind", ""),
            "module": decl.get("module", ""),
            "source": source_label_from_decl(decl, modules_by_name),
            "type": decl.get("type", ""),
            "doc": decl.get("doc", ""),
            "has_value": decl.get("has_value", False),
            "audit_tier": decl.get("audit_tier", "unassigned"),
            "audit_reason": decl.get("audit_reason", ""),
        },
        "source_excerpt": declaration_excerpt(repo, decl, modules_by_name),
        "dependencies": {
            "statement": [
                short_decl_context(name, declarations_by_name, lean_answered)
                for name in type_deps
                if name in declarations_by_name
            ],
            "proof_only": [
                short_decl_context(name, declarations_by_name, lean_answered)
                for name in proof_only_deps
                if name in declarations_by_name
            ],
        },
        "users": [
            short_decl_context(name, declarations_by_name, lean_answered)
            for name in reverse
            if name in declarations_by_name
        ][:40],
        "record_template": record_template_for_packet(packet, state),
    }


def build_source_intention_context(repo: Path, state: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    target = packet.get("inputs", {})
    return {
        "schema_version": SCHEMA_VERSION,
        "context_kind": "source_intention",
        "generated_at": now_utc(),
        "packet": packet,
        "decorrelation": (
            "This context is for source-intention reconstruction. It intentionally excludes current Lean declarations "
            "as ground truth; read the source passage and state the intended mathematical claim."
        ),
        "source_target": target,
        "source_excerpt": line_hint_excerpt(repo, target),
        "record_template": record_template_for_packet(packet, state),
    }


def build_comparison_context(repo: Path, state: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    inputs = packet.get("inputs", {})
    lean_records = answered_by(state["records"].get("lean_reconstructions", []), "declaration")
    source_records = answered_by(state["records"].get("source_intentions", []), "source_id")
    return {
        "schema_version": SCHEMA_VERSION,
        "context_kind": "comparison",
        "generated_at": now_utc(),
        "packet": packet,
        "lean_record": lean_records.get(inputs.get("lean_declaration", "")),
        "source_record": source_records.get(inputs.get("source_id", "")),
        "record_template": record_template_for_packet(packet, state),
    }


def build_api_boundary_context(repo: Path, state: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    declarations_by_name = {decl.get("name", ""): decl for decl in state["declarations"]}
    modules_by_name = {module.get("module", ""): module for module in state["modules"]}
    declaration = packet.get("inputs", {}).get("lean_declaration", "")
    decl = declarations_by_name.get(declaration, {})
    return {
        "schema_version": SCHEMA_VERSION,
        "context_kind": "api_boundary",
        "generated_at": now_utc(),
        "packet": packet,
        "declaration": decl,
        "source_excerpt": declaration_excerpt(repo, decl, modules_by_name) if decl else {},
        "record_template": record_template_for_packet(packet, state),
    }


def build_packet_context(repo: Path, state: dict[str, Any], packet: dict[str, Any]) -> dict[str, Any]:
    kind = packet.get("packet_kind")
    if kind == "lean_reconstruction":
        return build_lean_reconstruction_context(repo, state, packet)
    if kind == "source_intention":
        return build_source_intention_context(repo, state, packet)
    if kind == "comparison":
        return build_comparison_context(repo, state, packet)
    if kind == "api_boundary":
        return build_api_boundary_context(repo, state, packet)
    raise SystemExit(f"Unsupported packet kind: {kind}")


def next_versioned_record_id(prefix: str, existing_ids: set[str]) -> str:
    pattern = re.compile(rf"^{re.escape(prefix)}(?P<n>\d+)$")
    versions = [
        int(match.group("n"))
        for record_id in existing_ids
        if (match := pattern.match(record_id))
    ]
    return f"{prefix}{max(versions, default=0) + 1}"


def record_template_for_packet(
    packet: dict[str, Any],
    state: dict[str, Any],
    *,
    status: str = "draft",
    provenance: dict[str, Any] | None = None,
) -> dict[str, Any]:
    records = state.get("records", {})
    today = dt.datetime.now(dt.UTC).date().isoformat()
    kind = packet.get("packet_kind")
    inputs = packet.get("inputs", {})
    provenance = provenance or {}
    if kind == "lean_reconstruction":
        declaration = inputs.get("declaration") or packet.get("target", "")
        existing_ids = {record.get("record_id", "") for record in records.get("lean_reconstructions", [])}
        return {
            "schema_version": SCHEMA_VERSION,
            "record_id": next_versioned_record_id(f"lean.{declaration}.v", existing_ids),
            "status": status,
            "declaration": declaration,
            **provenance,
            "summary": "",
            "reconstructed_statement": "",
            "assumptions": [
                "This reconstruction uses only the Lean signature, docstring, source excerpt, and Lean dependency context; it is not a paper-intention card."
            ],
            "updated_at": today,
        }
    if kind == "source_intention":
        source_id = inputs.get("source_id") or packet.get("target", "")
        existing_ids = {record.get("record_id", "") for record in records.get("source_intentions", [])}
        return {
            "schema_version": SCHEMA_VERSION,
            "record_id": next_versioned_record_id(f"source.{source_id}.v", existing_ids),
            "status": status,
            "source_id": source_id,
            **provenance,
            "paper_label": inputs.get("paper_label", ""),
            "summary": "",
            "intended_statement": "",
            "evidence": [],
            "updated_at": today,
        }
    if kind == "comparison":
        return {
            "schema_version": SCHEMA_VERSION,
            "comparison_id": inputs.get("comparison_id") or packet.get("target", ""),
            "status": status,
            "lean_declaration": inputs.get("lean_declaration", ""),
            "lean_record_id": inputs.get("lean_reconstruction_record_id", ""),
            "source_id": inputs.get("source_id", ""),
            "source_record_id": inputs.get("source_intention_record_id", ""),
            **provenance,
            "alignment": "",
            "summary": "",
            "notes": "",
            "updated_at": today,
        }
    if kind == "api_boundary":
        target_id = inputs.get("target_id") or packet.get("target", "")
        existing_ids = {record.get("record_id", "") for record in records.get("api_boundaries", [])}
        return {
            "schema_version": SCHEMA_VERSION,
            "record_id": next_versioned_record_id(f"api.{target_id}.v", existing_ids),
            "status": status,
            "target_id": target_id,
            **provenance,
            "lean_declaration": inputs.get("lean_declaration", ""),
            "summary": "",
            "notes": "",
            "updated_at": today,
        }
    raise SystemExit(f"Unsupported packet kind: {kind}")


def stable_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def digest_json(value: Any) -> str:
    return hashlib.sha256(stable_json(value).encode("utf-8")).hexdigest()


def normalized_context_for_fingerprint(context: dict[str, Any]) -> dict[str, Any]:
    normalized = json.loads(stable_json(context))
    if not isinstance(normalized, dict):
        return {}
    normalized.pop("generated_at", None)
    normalized.pop("record_template", None)
    packet = normalized.get("packet")
    if isinstance(packet, dict):
        packet.pop("status", None)
        packet.pop("record_id", None)
        packet.pop("stale_reasons", None)
    return normalized


def context_fingerprint(context: dict[str, Any]) -> str:
    return digest_json(normalized_context_for_fingerprint(context))


def bundle_record_provenance(
    state: dict[str, Any],
    packet: dict[str, Any],
    context: dict[str, Any],
) -> dict[str, Any]:
    return {
        "packet_id": packet.get("packet_id", ""),
        "source_run_id": state.get("run", {}).get("run_id", ""),
        "context_fingerprint": context_fingerprint(context),
    }


def safe_path_segment(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "-", value).strip("-") or "packet"


def path_label(repo: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(repo).as_posix()
    except ValueError:
        return path.resolve().as_posix()


def default_bundle_dir(repo: Path, state: dict[str, Any], packet: dict[str, Any], work_root: str | Path) -> Path:
    root = Path(work_root)
    if not root.is_absolute():
        root = repo / root
    run_id = state.get("run", {}).get("run_id", "unknown-run")
    return root / run_id / safe_path_segment(packet_identity(packet))


def record_target_field_for_kind(kind: str) -> str:
    mapping = {
        "lean_reconstruction": "declaration",
        "source_intention": "source_id",
        "comparison": "comparison_id",
        "api_boundary": "target_id",
    }
    if kind not in mapping:
        raise SystemExit(f"Unsupported record kind: {kind}")
    return mapping[kind]


def expected_record_target(packet: dict[str, Any]) -> str:
    kind = packet.get("packet_kind", "")
    inputs = packet.get("inputs", {})
    if kind == "lean_reconstruction":
        return inputs.get("declaration") or packet.get("target", "")
    if kind == "source_intention":
        return inputs.get("source_id") or packet.get("target", "")
    if kind == "comparison":
        return inputs.get("comparison_id") or packet.get("target", "")
    if kind == "api_boundary":
        return inputs.get("target_id") or packet.get("target", "")
    raise SystemExit(f"Unsupported packet kind: {kind}")


def bundle_manifest(
    repo: Path,
    state: dict[str, Any],
    packet: dict[str, Any],
    context: dict[str, Any],
    answer: dict[str, Any],
    out_dir: Path,
) -> dict[str, Any]:
    kind = packet.get("packet_kind", "")
    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": BUNDLE_ARTIFACT,
        "created_at": now_utc(),
        "run_id": state.get("run", {}).get("run_id", ""),
        "run_commit": state.get("run", {}).get("commit", ""),
        "run_dir": path_label(repo, state.get("run_dir", repo)),
        "packet_id": packet.get("packet_id", ""),
        "packet_kind": kind,
        "packet_status": packet.get("status", ""),
        "packet_target": packet.get("target", ""),
        "context_file_digest": digest_json(context),
        "context_fingerprint": context_fingerprint(context),
        "record_identity": answer.get(record_identity_field(kind), ""),
        "record_target": expected_record_target(packet),
        "record_file": (RECORDS_DIR / RECORD_FILE_NAMES[record_file_key_for_kind(kind)]).as_posix(),
        "paths": {
            "bundle_dir": path_label(repo, out_dir),
            "manifest": "manifest.json",
            "context": "context.json",
            "instructions": "instructions.md",
            "answer": "answer.json",
        },
    }


def instructions_for_packet(manifest: dict[str, Any], packet: dict[str, Any]) -> str:
    kind = packet.get("packet_kind", "")
    target = packet.get("target", "")
    instructions = packet.get("instructions", "")
    kind_notes = {
        "lean_reconstruction": (
            "Use only the Lean declaration, docstring, source excerpt, and Lean dependency context in context.json. "
            "Do not use paper-intention or comparison cards as ground truth."
        ),
        "source_intention": (
            "Use only the source target and excerpt in context.json. Do not treat the current Lean code as ground truth."
        ),
        "comparison": (
            "Compare the answered Lean reconstruction with the answered source-intention card. "
            "Record exact matches, weakenings, overclaims, convention mismatches, and missing bridge hypotheses."
        ),
        "api_boundary": (
            "Audit whether the public Lean interface exposes the intended mathematical domain. "
            "Separate intentional generality from accidental overbreadth."
        ),
    }
    bundle_dir_arg = shlex.quote(manifest["paths"]["bundle_dir"])
    run_id = manifest.get("run_id", "")
    run_guard = f" --expect-run-id {shlex.quote(run_id)}" if run_id else ""
    return "\n".join([
        "# Semantic Audit Packet",
        "",
        "You are a packet worker. Read `context.json`, fill `answer.json`, and do not edit durable records.",
        "",
        "The controller will validate and ingest the answer. Leave `manifest.json` and `context.json` unchanged.",
        "",
        "## Packet",
        "",
        f"- Packet id: `{manifest.get('packet_id', '')}`",
        f"- Kind: `{kind}`",
        f"- Target: `{target}`",
        f"- Status when bundled: `{packet.get('status', '')}`",
        f"- Run id: `{manifest.get('run_id', '')}`",
        "",
        "## Task",
        "",
        instructions,
        "",
        "## Evidence Discipline",
        "",
        kind_notes.get(kind, "Use only the evidence in `context.json`."),
        "",
        "## Answer Contract",
        "",
        "- Edit `answer.json` only.",
        "- Set `status` to `answered` when complete.",
        "- Fill every required textual field with concise mathematical content.",
        "- Use TeX delimiters such as `\\(...\\)` or `\\[...\\]` for mathematical notation.",
        "- Make assumptions explicit in the relevant field rather than hiding them.",
        "",
        "## Controller Commands",
        "",
        "```bash",
        f"python3 tools/semantic-audit/semantic_audit.py packet ingest {bundle_dir_arg}{run_guard} --dry-run",
        f"python3 tools/semantic-audit/semantic_audit.py packet ingest {bundle_dir_arg}{run_guard} --append",
        "python3 tools/semantic-audit/semantic_audit.py run",
        "```",
        "",
    ])


def write_packet_bundle(repo: Path, state: dict[str, Any], packet: dict[str, Any], out_dir: Path, *, force: bool = False) -> Path:
    if out_dir.exists():
        if not force:
            raise SystemExit(f"Bundle directory already exists: {out_dir}. Use --force to overwrite generated bundle files.")
    out_dir.mkdir(parents=True, exist_ok=True)
    context = build_packet_context(repo, state, packet)
    answer = record_template_for_packet(
        packet,
        state,
        provenance=bundle_record_provenance(state, packet, context),
    )
    manifest = bundle_manifest(repo, state, packet, context, answer, out_dir)
    write_json(out_dir / "manifest.json", manifest)
    write_json(out_dir / "context.json", context)
    write_json(out_dir / "answer.json", answer)
    (out_dir / "instructions.md").write_text(instructions_for_packet(manifest, packet), encoding="utf-8")
    return out_dir


def read_bundle_input(path: Path) -> dict[str, Any]:
    if path.is_dir():
        manifest_path = path / "manifest.json"
        context_path = path / "context.json"
        answer_path = path / "answer.json"
        if not manifest_path.exists():
            raise SystemExit(f"Bundle directory is missing manifest.json: {path}")
        if not context_path.exists():
            raise SystemExit(f"Bundle directory is missing context.json: {path}")
        if not answer_path.exists():
            raise SystemExit(f"Bundle directory is missing answer.json: {path}")
        return {
            "bundle_dir": path,
            "manifest": read_json(manifest_path),
            "context": read_json(context_path),
            "record": read_record_object(answer_path),
        }
    return {
        "bundle_dir": path.parent,
        "manifest": {},
        "context": {},
        "record": read_record_object(path),
    }


def packet_for_record(state: dict[str, Any], kind: str, record: dict[str, Any]) -> dict[str, Any] | None:
    target = record.get(record_target_field_for_kind(kind), "")
    for packet in state.get("packets", []):
        if packet.get("packet_kind") == kind and expected_record_target(packet) == target:
            return packet
    return None


def validate_record_against_packet(record: dict[str, Any], kind: str, packet: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    target_field = record_target_field_for_kind(kind)
    expected_target = expected_record_target(packet)
    if record.get(target_field) != expected_target:
        errors.append(
            f"Record `{target_field}` is {record.get(target_field)!r}, expected {expected_target!r} from packet."
        )
    inputs = packet.get("inputs", {})
    if kind == "comparison":
        if record.get("lean_declaration") != inputs.get("lean_declaration", ""):
            errors.append("Comparison record lean_declaration does not match packet input.")
        if record.get("source_id") != inputs.get("source_id", ""):
            errors.append("Comparison record source_id does not match packet input.")
        if record.get("lean_record_id") != inputs.get("lean_reconstruction_record_id", ""):
            errors.append("Comparison record lean_record_id does not match the packet prerequisite record id.")
        if record.get("source_record_id") != inputs.get("source_intention_record_id", ""):
            errors.append("Comparison record source_record_id does not match the packet prerequisite record id.")
    if kind == "api_boundary" and record.get("lean_declaration", "") != inputs.get("lean_declaration", ""):
        errors.append("API-boundary record lean_declaration does not match packet input.")
    return errors


def lint_record(record: dict[str, Any], kind: str) -> list[str]:
    warnings: list[str] = []
    summary = str(record.get("summary", "")).strip()
    if len(summary) < 20:
        warnings.append("Summary is very short; durable cards should usually be self-explanatory.")
    if kind == "lean_reconstruction":
        if not record.get("assumptions"):
            warnings.append("Lean reconstruction has no assumptions/decorrelation note.")
    if kind == "source_intention":
        if not record.get("evidence"):
            warnings.append("Source-intention record has no evidence entries.")
    if kind == "comparison":
        allowed = {"match", "exact", "partial", "lean_weaker", "lean_stronger", "mismatch", "convention_mismatch", "unclear"}
        alignment = str(record.get("alignment", "")).strip()
        if alignment and alignment not in allowed:
            warnings.append(f"Comparison alignment `{alignment}` is not one of {sorted(allowed)}.")
    return warnings


def validate_bundle_provenance(
    manifest: dict[str, Any],
    context: dict[str, Any],
    packet: dict[str, Any],
    state: dict[str, Any],
    *,
    allow_stale: bool = False,
) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    if not manifest:
        warnings.append("No bundle manifest found; provenance checks were skipped.")
        return errors, warnings
    if manifest.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"Manifest schema_version is {manifest.get('schema_version')!r}, expected {SCHEMA_VERSION}.")
    if manifest.get("artifact") != BUNDLE_ARTIFACT:
        errors.append(f"Manifest artifact is {manifest.get('artifact')!r}, expected {BUNDLE_ARTIFACT}.")
    if not isinstance(context, dict) or not context:
        errors.append("context.json must be a non-empty JSON object.")
    else:
        if context.get("schema_version") != SCHEMA_VERSION:
            errors.append(f"context.json schema_version is {context.get('schema_version')!r}, expected {SCHEMA_VERSION}.")
        if context.get("context_kind") != packet.get("packet_kind"):
            errors.append(
                f"context.json context_kind is {context.get('context_kind')!r}, expected {packet.get('packet_kind')!r}."
            )
    latest_run_id = state.get("run", {}).get("run_id", "")
    if manifest.get("run_id") != latest_run_id:
        message = f"Bundle was created from run {manifest.get('run_id')!r}, latest run is {latest_run_id!r}."
        if allow_stale:
            warnings.append(message)
        else:
            errors.append(message + " Rerun bundle generation or pass --allow-stale.")
    if manifest.get("packet_id") != packet.get("packet_id"):
        errors.append("Manifest packet_id does not match the latest packet selected for this record.")
    if manifest.get("packet_kind") != packet.get("packet_kind"):
        errors.append("Manifest packet_kind does not match the latest packet kind.")
    expected_context_digest = manifest.get("context_file_digest", manifest.get("context_digest"))
    if expected_context_digest != digest_json(context):
        errors.append("context.json has changed since the bundle manifest was written.")
    if manifest.get("context_fingerprint") != context_fingerprint(context):
        errors.append("context.json semantic fingerprint does not match the bundle manifest.")
    return errors, warnings


def validate_manifest_record_consistency(
    manifest: dict[str, Any],
    record: dict[str, Any],
    kind: str,
    packet: dict[str, Any],
) -> list[str]:
    if not manifest:
        return []
    errors: list[str] = []
    target_field = record_target_field_for_kind(kind)
    identity_field = record_identity_field(kind)
    record_target = record.get(target_field, "")
    record_identity = record.get(identity_field, "")
    expected_target = expected_record_target(packet)
    expected_record_file = (RECORDS_DIR / RECORD_FILE_NAMES[record_file_key_for_kind(kind)]).as_posix()
    checks = [
        ("record_identity", record_identity),
        ("record_target", expected_target),
        ("record_file", expected_record_file),
    ]
    for field_name, expected in checks:
        if manifest.get(field_name) != expected:
            errors.append(f"Manifest {field_name} is {manifest.get(field_name)!r}, expected {expected!r}.")
    if record_target != expected_target:
        errors.append(f"Record target {record_target!r} does not match manifest/latest packet target {expected_target!r}.")
    provenance_checks = [
        ("packet_id", packet.get("packet_id", "")),
        ("source_run_id", manifest.get("run_id", "")),
        ("context_fingerprint", manifest.get("context_fingerprint", "")),
    ]
    for field_name, expected in provenance_checks:
        if record.get(field_name) != expected:
            errors.append(f"Record {field_name} is {record.get(field_name)!r}, expected {expected!r} from bundle provenance.")
    return errors


def validate_current_context_for_append(
    repo: Path,
    state: dict[str, Any],
    manifest: dict[str, Any],
    packet: dict[str, Any],
    *,
    allow_stale: bool = False,
) -> tuple[list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    if not manifest:
        return errors, warnings

    live_state = dict(state)
    live_state["records"] = load_record_inputs(repo)
    try:
        current_fingerprint = context_fingerprint(build_packet_context(repo, live_state, packet))
    except SystemExit as exc:
        current_fingerprint = ""
        message = f"Could not rebuild current packet context before append: {exc}"
        if allow_stale:
            warnings.append(message)
        else:
            errors.append(message)
    if current_fingerprint and manifest.get("context_fingerprint") != current_fingerprint:
        message = "Current live packet context differs from the bundle context."
        if allow_stale:
            warnings.append(message)
        else:
            errors.append(message + " Rerun the bundle from the current dashboard before appending.")

    return errors, warnings


def answered_record_for_packet(
    records: dict[str, list[dict[str, Any]]],
    packet: dict[str, Any],
) -> dict[str, Any] | None:
    kind = packet.get("packet_kind", "")
    key = record_file_key_for_kind(kind)
    target_field = record_target_field_for_kind(kind)
    identity_field = record_identity_field(kind)
    target = expected_record_target(packet)
    identity = packet.get("record_id", "")
    candidates = [
        record
        for record in records.get(key, [])
        if record.get("status") == "answered" and record.get(target_field, "") == target
    ]
    if identity:
        for record in reversed(candidates):
            if record.get(identity_field, "") == identity:
                return record
    return candidates[-1] if candidates else None


def mark_packet_stale(packet: dict[str, Any], reason: str) -> None:
    packet["status"] = "stale"
    reasons = packet.setdefault("stale_reasons", [])
    if reason not in reasons:
        reasons.append(reason)


def refresh_comparison_packet_statuses(
    packets: list[dict[str, Any]],
    records: dict[str, list[dict[str, Any]]],
) -> None:
    lean_status = packet_status_map(packets, kind="lean_reconstruction")
    source_status = packet_status_map(packets, kind="source_intention")
    for packet in packets:
        if packet.get("packet_kind") != "comparison":
            continue
        inputs = packet.get("inputs", {})
        record = answered_record_for_packet(records, packet)
        lean_ready = lean_status.get(inputs.get("lean_declaration", "")) == "answered"
        source_ready = source_status.get(inputs.get("source_id", "")) == "answered"
        if record and (not lean_ready or not source_ready):
            mark_packet_stale(packet, "A prerequisite Lean or source-intention packet is not currently answered.")
        elif not record and (not lean_ready or not source_ready):
            packet["status"] = "blocked"
        elif not record:
            packet["status"] = "open"


def apply_context_staleness(
    repo: Path,
    state: dict[str, Any],
    packets: list[dict[str, Any]],
    *,
    semantic_blocked: bool = False,
) -> None:
    if semantic_blocked:
        return
    state["packets"] = packets
    for packet in packets:
        if packet.get("status") != "answered":
            continue
        record = answered_record_for_packet(state.get("records", {}), packet)
        if not record:
            mark_packet_stale(packet, "The packet is marked answered, but no durable answered record was found.")
            continue
        expected = record.get("context_fingerprint", "")
        if not expected:
            mark_packet_stale(packet, "The durable record has no context_fingerprint; regenerate it through a worker bundle.")
            continue
        try:
            current = context_fingerprint(build_packet_context(repo, state, packet))
        except SystemExit as exc:
            mark_packet_stale(packet, f"Could not rebuild the current packet context: {exc}")
            continue
        if current != expected:
            mark_packet_stale(packet, "The current packet context fingerprint differs from the durable record.")
    refresh_comparison_packet_statuses(packets, state.get("records", {}))


def append_record_to_store(
    repo: Path,
    record: dict[str, Any],
    kind: str,
    *,
    replace: bool = False,
    dry_run: bool = False,
) -> dict[str, Any]:
    key = record_file_key_for_kind(kind)
    identity_field = record_identity_field(kind)
    identity = record.get(identity_field, "")
    target_field = record_target_field_for_kind(kind)
    target = record.get(target_field, "")
    path = repo / RECORDS_DIR / RECORD_FILE_NAMES[key]
    records = read_jsonl(path)
    duplicate_indexes = [
        index for index, existing in enumerate(records)
        if existing.get(identity_field) == identity
    ]
    conflicting_targets = sorted({
        str(records[index].get(target_field, ""))
        for index in duplicate_indexes
        if records[index].get(target_field, "") != target
    })
    if conflicting_targets:
        raise SystemExit(
            f"Record `{identity}` exists for target(s) {conflicting_targets}, not target `{target}`. "
            "Refusing to replace an unrelated durable record."
        )
    if replace and not duplicate_indexes:
        raise SystemExit(
            f"Cannot replace `{identity}` in {path}: no existing record with {identity_field} `{identity}`."
        )
    if duplicate_indexes and not replace:
        raise SystemExit(
            f"Record `{identity}` already exists in {path}. Use --replace to replace by {identity_field}."
        )
    action = "replace" if duplicate_indexes and replace else "append"
    result = {
        "action": action,
        "identity": identity,
        "identity_field": identity_field,
        "path": path.as_posix(),
    }
    if dry_run:
        return result
    if duplicate_indexes and replace:
        first = duplicate_indexes[0]
        records = [
            existing
            for index, existing in enumerate(records)
            if index not in set(duplicate_indexes)
        ]
        records.insert(first, record)
    else:
        records.append(record)
    write_jsonl(path, records)
    return result


def emit_json(value: Any, out: str | None) -> None:
    text = json.dumps(value, indent=2, sort_keys=True) + "\n"
    if out:
        path = Path(out)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")
        print(path)
    else:
        print(text, end="")


def infer_record_kind(record: dict[str, Any]) -> str:
    if record.get("declaration") and "reconstructed_statement" in record:
        return "lean_reconstruction"
    if record.get("source_id") and "intended_statement" in record:
        return "source_intention"
    if record.get("comparison_id"):
        return "comparison"
    if record.get("target_id"):
        return "api_boundary"
    raise SystemExit("Could not infer record kind. Pass --kind explicitly.")


def record_file_key_for_kind(kind: str) -> str:
    mapping = {
        "lean_reconstruction": "lean_reconstructions",
        "source_intention": "source_intentions",
        "comparison": "comparisons",
        "api_boundary": "api_boundaries",
    }
    if kind not in mapping:
        raise SystemExit(f"Unsupported record kind: {kind}")
    return mapping[kind]


def record_identity_field(kind: str) -> str:
    return "comparison_id" if kind == "comparison" else "record_id"


def expected_record_id_prefix(record: dict[str, Any], kind: str) -> str:
    if kind == "lean_reconstruction":
        return f"lean.{record.get('declaration', '')}.v"
    if kind == "source_intention":
        return f"source.{record.get('source_id', '')}.v"
    if kind == "api_boundary":
        return f"api.{record.get('target_id', '')}.v"
    return ""


def validate_record(record: dict[str, Any], kind: str | None = None, *, for_append: bool = False) -> list[str]:
    kind = kind or infer_record_kind(record)
    required: dict[str, list[str]] = {
        "lean_reconstruction": ["schema_version", "record_id", "status", "declaration", "summary", "reconstructed_statement", "assumptions", "updated_at"],
        "source_intention": ["schema_version", "record_id", "status", "source_id", "summary", "intended_statement", "evidence", "updated_at"],
        "comparison": ["schema_version", "comparison_id", "status", "lean_declaration", "lean_record_id", "source_id", "source_record_id", "alignment", "summary", "notes", "updated_at"],
        "api_boundary": ["schema_version", "record_id", "status", "target_id", "summary", "notes", "updated_at"],
    }
    errors: list[str] = []
    if kind not in required:
        return [f"Unsupported record kind: {kind}"]
    draft = record.get("status") == "draft"
    identity_fields = {"schema_version", "record_id", "comparison_id", "status", "declaration", "source_id", "target_id"}
    for field_name in required[kind]:
        if field_name not in record:
            errors.append(f"Missing required field `{field_name}`.")
        elif (
            isinstance(record[field_name], str)
            and not record[field_name].strip()
            and (for_append or not draft or field_name in identity_fields)
        ):
            errors.append(f"Required field `{field_name}` is empty.")
    if record.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"Expected schema_version {SCHEMA_VERSION}, got {record.get('schema_version')!r}.")
    if record.get("status") not in {"draft", "answered"}:
        errors.append("Record status must be `draft` or `answered`.")
    if for_append and record.get("status") != "answered":
        errors.append("Only `answered` records may be appended to durable records.")
    if kind == "lean_reconstruction" and not isinstance(record.get("assumptions"), list):
        errors.append("`assumptions` must be a list.")
    if kind == "source_intention" and not isinstance(record.get("evidence"), list):
        errors.append("`evidence` must be a list.")
    if for_append and kind != "comparison":
        prefix = expected_record_id_prefix(record, kind)
        record_id = str(record.get("record_id", ""))
        if prefix and not re.match(rf"^{re.escape(prefix)}[1-9][0-9]*$", record_id):
            errors.append(f"`record_id` must have the target-derived form `{prefix}<positive integer>`.")
    return errors


def read_record_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SystemExit(f"Expected a single JSON object in {path}.")
    return value


def command_packet_list(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    packets = state["packets"]
    if args.kind:
        packets = [packet for packet in packets if packet.get("packet_kind") == args.kind]
    if args.status:
        packets = [packet for packet in packets if packet.get("status") == args.status]
    if args.json:
        emit_json(packets[: args.limit] if args.limit else packets, None)
        return
    for packet in packets[: args.limit] if args.limit else packets:
        print(
            f"{packet.get('status', ''):9} {packet.get('packet_kind', ''):20} "
            f"{packet.get('priority', ''):6} {packet.get('packet_id', '')}"
        )


def command_packet_context(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    packet = find_packet(state["packets"], args.selector)
    emit_json(build_packet_context(repo, state, packet), args.output)


def command_packet_scaffold(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    packet = find_packet(state["packets"], args.selector)
    emit_json(record_template_for_packet(packet, state, status=args.status), args.output)


def command_packet_bundle(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    packet = find_packet(state["packets"], args.selector)
    if packet.get("status") == "blocked" and not args.allow_blocked:
        raise SystemExit(
            f"Packet {packet.get('packet_id', '')} is blocked. Complete prerequisite packets first, "
            "or pass --allow-blocked for debugging-only bundle generation."
        )
    out_dir = Path(args.output) if args.output else default_bundle_dir(repo, state, packet, args.work_root)
    if not out_dir.is_absolute():
        out_dir = repo / out_dir
    bundle_dir = write_packet_bundle(repo, state, packet, out_dir, force=args.force)
    print(bundle_dir)
    print(f"answer: {bundle_dir / 'answer.json'}")
    run_id = state.get("run", {}).get("run_id", "")
    run_guard = f" --expect-run-id {shlex.quote(run_id)}" if run_id else ""
    print(
        "ingest: python3 tools/semantic-audit/semantic_audit.py packet ingest "
        f"{shlex.quote(path_label(repo, bundle_dir))}{run_guard} --dry-run"
    )


def command_packet_validate(args: argparse.Namespace) -> None:
    record = read_record_object(Path(args.record))
    kind = args.kind or infer_record_kind(record)
    errors = validate_record(record, kind, for_append=args.for_append)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
    print(f"valid {kind} record")


def command_packet_append(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    record = read_record_object(Path(args.record))
    kind = args.kind or infer_record_kind(record)
    errors = validate_record(record, kind, for_append=True)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
    result = append_record_to_store(repo, record, kind, replace=args.replace, dry_run=args.dry_run)
    if args.dry_run:
        print(f"dry-run: would {result['action']} {result['identity']} in {result['path']}")
        return
    print(f"wrote {result['identity']} to {result['path']}")


def command_packet_ingest(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    bundle = read_bundle_input(Path(args.input))
    record = bundle["record"]
    kind = args.kind or infer_record_kind(record)
    errors = validate_record(record, kind, for_append=True)
    warnings = lint_record(record, kind)

    packet = None
    manifest = bundle.get("manifest", {})
    if args.append and not manifest and not args.allow_unbundled:
        errors.append("packet ingest --append requires a bundle manifest. Use packet append for raw records, or pass --allow-unbundled.")
    if manifest.get("packet_id"):
        try:
            packet = find_packet(state["packets"], manifest["packet_id"])
        except SystemExit as exc:
            errors.append(str(exc))
    else:
        packet = packet_for_record(state, kind, record)
        if packet is None:
            errors.append("Could not locate a latest work packet matching this record target.")

    if packet is not None:
        errors.extend(validate_record_against_packet(record, kind, packet))
        errors.extend(validate_manifest_record_consistency(manifest, record, kind, packet))
        provenance_errors, provenance_warnings = validate_bundle_provenance(
            manifest,
            bundle.get("context", {}),
            packet,
            state,
            allow_stale=args.allow_stale,
        )
        errors.extend(provenance_errors)
        warnings.extend(provenance_warnings)
        live_errors, live_warnings = validate_current_context_for_append(
            repo,
            state,
            manifest,
            packet,
            allow_stale=args.allow_stale,
        )
        errors.extend(live_errors)
        warnings.extend(live_warnings)

    if args.strict and warnings:
        errors.extend(f"Strict lint: {warning}" for warning in warnings)

    for warning in warnings:
        print(f"WARNING: {warning}", file=sys.stderr)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)

    if args.allow_stale and args.append and warnings:
        record = dict(record)
        record["stale_accepted"] = {
            "accepted_at": now_utc(),
            "warnings": warnings,
        }

    result = append_record_to_store(repo, record, kind, replace=args.replace, dry_run=not args.append)
    if args.append:
        print(f"wrote {result['identity']} to {result['path']}")
    else:
        print(f"dry-run: would {result['action']} {result['identity']} in {result['path']}")
    print(f"kind: {kind}")
    if packet is not None:
        print(f"packet: {packet.get('packet_id', '')}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the DLNFibre semantic audit dashboard pipeline.")
    subparsers = parser.add_subparsers(dest="command")

    run_parser = subparsers.add_parser("run", help="run extraction, deterministic findings, and dashboard generation")
    run_parser.add_argument("--out", default=str(DEFAULT_OUT), help="output directory relative to the repo root")
    run_parser.add_argument("--skip-build", action="store_true", help="skip lake build and scripts/sorries attestation")

    packet_parser = subparsers.add_parser("packet", help="inspect packets and author validated answer records")
    packet_subparsers = packet_parser.add_subparsers(dest="packet_command", required=True)

    list_parser = packet_subparsers.add_parser("list", help="list packets from the latest audit run")
    list_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    list_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    list_parser.add_argument("--kind", choices=["lean_reconstruction", "source_intention", "comparison", "api_boundary"])
    list_parser.add_argument("--status", choices=["open", "blocked", "answered", "stale"])
    list_parser.add_argument("--limit", type=int, default=0)
    list_parser.add_argument("--json", action="store_true", help="emit JSON instead of a compact table")
    list_parser.set_defaults(func=command_packet_list)

    context_parser = packet_subparsers.add_parser("context", help="emit an isolated context bundle for one packet")
    context_parser.add_argument("selector", help="packet_id, target, or Lean declaration")
    context_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    context_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    context_parser.add_argument("--output", "-o", help="write context JSON to this path instead of stdout")
    context_parser.set_defaults(func=command_packet_context)

    scaffold_parser = packet_subparsers.add_parser("scaffold", help="emit a draft answer record for one packet")
    scaffold_parser.add_argument("selector", help="packet_id, target, or Lean declaration")
    scaffold_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    scaffold_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    scaffold_parser.add_argument("--status", choices=["draft", "answered"], default="draft")
    scaffold_parser.add_argument("--output", "-o", help="write record JSON to this path instead of stdout")
    scaffold_parser.set_defaults(func=command_packet_scaffold)

    bundle_parser = packet_subparsers.add_parser("bundle", help="create a worker bundle with context, instructions, and answer scaffold")
    bundle_parser.add_argument("selector", help="packet_id, target, or Lean declaration")
    bundle_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    bundle_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    bundle_parser.add_argument("--work-root", default=str(DEFAULT_WORK), help="root directory for generated worker bundles")
    bundle_parser.add_argument("--output", "-o", help="write the bundle to this directory instead of the default work root")
    bundle_parser.add_argument("--force", action="store_true", help="overwrite generated bundle files if the bundle directory exists")
    bundle_parser.add_argument("--allow-blocked", action="store_true", help="create a debugging bundle even if the packet is blocked")
    bundle_parser.set_defaults(func=command_packet_bundle)

    validate_parser = packet_subparsers.add_parser("validate", help="validate a single answer record JSON object")
    validate_parser.add_argument("record", help="path to a JSON record object")
    validate_parser.add_argument("--kind", choices=["lean_reconstruction", "source_intention", "comparison", "api_boundary"])
    validate_parser.add_argument("--for-append", action="store_true", help="require durable answered-record constraints")
    validate_parser.set_defaults(func=command_packet_validate)

    append_parser = packet_subparsers.add_parser("append", help="append a validated answered record to the durable JSONL store")
    append_parser.add_argument("record", help="path to a JSON record object")
    append_parser.add_argument("--kind", choices=["lean_reconstruction", "source_intention", "comparison", "api_boundary"])
    append_parser.add_argument("--replace", action="store_true", help="replace an existing record with the same identity")
    append_parser.add_argument("--dry-run", action="store_true", help="validate and report the target file without writing")
    append_parser.set_defaults(func=command_packet_append)

    ingest_parser = packet_subparsers.add_parser("ingest", help="lint and ingest a filled worker bundle answer")
    ingest_parser.add_argument("input", help="bundle directory containing answer.json, or a raw JSON answer record")
    ingest_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    ingest_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    ingest_parser.add_argument("--kind", choices=["lean_reconstruction", "source_intention", "comparison", "api_boundary"])
    ingest_parser.add_argument("--dry-run", action="store_true", help="validate and report the target file without writing")
    ingest_parser.add_argument("--append", action="store_true", help="write the validated answer into durable records")
    ingest_parser.add_argument("--replace", action="store_true", help="replace an existing record with the same identity")
    ingest_parser.add_argument("--allow-stale", action="store_true", help="allow bundle run/packet digests to differ from latest")
    ingest_parser.add_argument("--allow-unbundled", action="store_true", help="allow packet ingest --append for a raw JSON record without bundle provenance")
    ingest_parser.add_argument("--strict", action="store_true", help="treat lint warnings as errors")
    ingest_parser.set_defaults(func=command_packet_ingest)

    args = parser.parse_args()
    if getattr(args, "packet_command", None) == "ingest" and args.dry_run and args.append:
        parser.error("packet ingest accepts either --dry-run or --append, not both")
    if args.command in {None, "run"}:
        if args.command is None:
            args.out = str(DEFAULT_OUT)
            args.skip_build = False
        run_audit(args)
    elif args.command == "packet":
        args.func(args)
    else:
        parser.error(f"unknown command: {args.command}")


if __name__ == "__main__":
    main()
