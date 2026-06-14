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
QUEUE_PLAN_ARTIFACT = "semantic-audit-queue-plan"
INPUT_SNAPSHOT_ARTIFACT = "semantic-audit-input-snapshot"
DISPATCH_MANIFEST_ARTIFACT = "semantic-audit-dispatch-manifest"
WORKER_RUN_ARTIFACT = "semantic-audit-worker-run"
QUEUE_PLAN_FILE = "queue-plan.json"
INPUT_SNAPSHOT_FILE = "audit-input-snapshot.json"
DISPATCH_MANIFEST_FILE = "dispatch-manifest.json"
WORKER_RUN_FILE = "worker-run.json"
WORKER_PROMPT_FILE = "worker-prompt.md"
PACKET_KINDS = ["lean_reconstruction", "source_intention", "comparison", "api_boundary"]
PACKET_STATUSES = ["open", "blocked", "answered", "stale"]
ASSIGNABLE_PACKET_STATUSES = ["open", "stale"]
PACKET_PRIORITIES = ["high", "medium", "low"]
PRIORITY_ORDER = {priority: index for index, priority in enumerate(PACKET_PRIORITIES)}
KIND_ORDER = {kind: index for index, kind in enumerate(PACKET_KINDS)}
DEFAULT_DISPATCH_KINDS = ["source_intention"]


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


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def file_digest_or_missing(path: Path) -> str | None:
    if not path.exists() or not path.is_file():
        return None
    return file_sha256(path)


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


def technical_gate_ready(attestation: dict[str, Any]) -> bool:
    return all(
        attestation.get(key, {}).get("ok") is True
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


def audit_input_file_paths(repo: Path, config: dict[str, Any]) -> list[Path]:
    paths: set[Path] = {
        CONFIG_PATH,
        Path("tools/semantic-audit/semantic_audit.py"),
        Path("tools/semantic-audit/LeanExtract.lean"),
    }
    paths.update(path.relative_to(repo) for path in lean_files(repo))
    for target in config.get("source_targets", []):
        rel_path = target.get("path", "")
        if rel_path:
            paths.add(Path(rel_path))
    return sorted(paths, key=lambda path: path.as_posix())


def audit_input_snapshot(repo: Path, config: dict[str, Any], records: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": INPUT_SNAPSHOT_ARTIFACT,
        "created_at": now_utc(),
        "files": {
            path.as_posix(): file_digest_or_missing(repo / path)
            for path in audit_input_file_paths(repo, config)
        },
        "config_digest": digest_json(config),
        "record_digests": {
            filename: digest_json(records.get(key, []))
            for key, filename in RECORD_FILE_NAMES.items()
        },
    }


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
    write_json(run_dir / INPUT_SNAPSHOT_FILE, audit_input_snapshot(repo, config, records))

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
        "attestation": read_json(run_dir / "technical-attestation.json"),
        "input_snapshot": read_json(run_dir / INPUT_SNAPSHOT_FILE),
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


def latest_snapshot_freshness_errors(repo: Path, state: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    run_dir = Path(state.get("run_dir", ""))
    attestation = state.get("attestation", {})
    input_snapshot = state.get("input_snapshot", {})
    run_commit = state.get("run", {}).get("commit", "")
    current_head = current_commit(repo)
    if run_commit and current_head and run_commit != current_head:
        errors.append(f"Latest run commit is {run_commit}, but current HEAD is {current_head}. Rerun the audit.")
    if attestation.get("commit") and current_head and attestation.get("commit") != current_head:
        errors.append(
            f"Technical attestation commit is {attestation.get('commit')}, but current HEAD is {current_head}. Rerun the audit."
        )

    live_config_digest = digest_json(load_audit_config(repo))
    run_config_digest = input_snapshot.get("config_digest") or digest_json(read_json(run_dir / "audit-config.resolved.json"))
    if live_config_digest != run_config_digest:
        errors.append("Live audit config differs from the latest run snapshot. Rerun the audit.")

    for key, filename in RECORD_FILE_NAMES.items():
        live_digest = digest_json(read_jsonl(repo / RECORDS_DIR / filename))
        run_digest = input_snapshot.get("record_digests", {}).get(filename) or digest_json(read_jsonl(run_dir / filename))
        if live_digest != run_digest:
            errors.append(f"Live durable records `{filename}` differ from the latest run snapshot. Rerun the audit.")

    if input_snapshot:
        if input_snapshot.get("schema_version") != SCHEMA_VERSION:
            errors.append("Latest run input snapshot has an unsupported schema version. Rerun the audit.")
        if input_snapshot.get("artifact") != INPUT_SNAPSHOT_ARTIFACT:
            errors.append("Latest run input snapshot has an unsupported artifact type. Rerun the audit.")
        live_snapshot = audit_input_snapshot(repo, load_audit_config(repo), load_record_inputs(repo))
        snapshot_files = input_snapshot.get("files", {})
        live_files = live_snapshot.get("files", {})
        if set(live_files) != set(snapshot_files):
            added = sorted(set(live_files) - set(snapshot_files))
            removed = sorted(set(snapshot_files) - set(live_files))
            errors.append(
                "Live audit input file set differs from the latest run snapshot. "
                f"Added: {added[:5]}; removed: {removed[:5]}. Rerun the audit."
            )
        for path, expected_digest in snapshot_files.items():
            live_digest = live_files.get(path)
            if live_digest != expected_digest:
                errors.append(f"Live audit input `{path}` differs from the latest run snapshot. Rerun the audit.")
    else:
        current_status = git_status(repo)
        if attestation.get("git_status", []) != current_status:
            errors.append("Current git status differs from the latest run's technical attestation. Rerun the audit.")
        errors.append(f"Latest run is missing `{INPUT_SNAPSHOT_FILE}`. Rerun the audit.")
    return errors


def semantic_work_preflight_errors(repo: Path, state: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    attestation = state.get("attestation", {})
    if not technical_gate_ready(attestation):
        errors.append(
            "Latest run is not technically attested: `lake_build.ok` and `sorries.ok` must both be true. "
            "Rerun without --skip-build before assigning semantic work."
        )
    errors.extend(latest_snapshot_freshness_errors(repo, state))
    return errors


def enforce_semantic_work_preflight(repo: Path, state: dict[str, Any], *, allow_unstable: bool = False) -> None:
    errors = semantic_work_preflight_errors(repo, state)
    if not errors:
        return
    stream = sys.stderr
    prefix = "WARNING" if allow_unstable else "ERROR"
    for error in errors:
        print(f"{prefix}: {error}", file=stream)
    if not allow_unstable:
        raise SystemExit(1)


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


def packet_sort_key(packet: dict[str, Any]) -> tuple[int, int, str]:
    return (
        PRIORITY_ORDER.get(packet.get("priority", ""), len(PRIORITY_ORDER)),
        KIND_ORDER.get(packet.get("packet_kind", ""), len(KIND_ORDER)),
        packet_identity(packet),
    )


def selection_filter_summary(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "kind": sorted(args.kind or []),
        "status": sorted(args.status or ASSIGNABLE_PACKET_STATUSES),
        "priority": sorted(args.priority or []),
        "limit": int(args.limit or 0),
    }


def select_queue_packets(
    packets: list[dict[str, Any]],
    *,
    kinds: list[str] | None = None,
    statuses: list[str] | None = None,
    priorities: list[str] | None = None,
    limit: int = 0,
) -> list[dict[str, Any]]:
    wanted_kinds = set(kinds or [])
    wanted_statuses = set(statuses or ASSIGNABLE_PACKET_STATUSES)
    wanted_priorities = set(priorities or [])
    selected = [
        packet for packet in packets
        if (not wanted_kinds or packet.get("packet_kind") in wanted_kinds)
        and packet.get("status") in wanted_statuses
        and (not wanted_priorities or packet.get("priority") in wanted_priorities)
    ]
    selected = sorted(selected, key=packet_sort_key)
    if limit > 0:
        selected = selected[:limit]
    return selected


def queue_plan_digest_payload(
    state: dict[str, Any],
    filters: dict[str, Any],
    packets: list[dict[str, Any]],
) -> dict[str, Any]:
    return {
        "run_id": state.get("run", {}).get("run_id", ""),
        "filters": filters,
        "packet_ids": [packet.get("packet_id", "") for packet in packets],
    }


def default_batch_dir(repo: Path, state: dict[str, Any], work_root: str | Path, digest: str) -> Path:
    root = Path(work_root)
    if not root.is_absolute():
        root = repo / root
    run_id = state.get("run", {}).get("run_id", "unknown-run")
    return root / run_id / f"batch-{digest[:12]}"


def queue_packet_entry(repo: Path, batch_dir: Path, packet: dict[str, Any]) -> dict[str, Any]:
    bundle_dir = batch_dir / "bundles" / safe_path_segment(packet_identity(packet))
    return {
        "packet_id": packet.get("packet_id", ""),
        "packet_kind": packet.get("packet_kind", ""),
        "status": packet.get("status", ""),
        "priority": packet.get("priority", ""),
        "target": packet.get("target", ""),
        "title": packet.get("title", ""),
        "record_id": packet.get("record_id", ""),
        "bundle_dir": path_label(repo, bundle_dir),
    }


def duplicate_values(values: list[str]) -> list[str]:
    seen: set[str] = set()
    duplicates: set[str] = set()
    for value in values:
        if value in seen:
            duplicates.add(value)
        else:
            seen.add(value)
    return sorted(duplicates)


def unique_values(values: list[str]) -> list[str]:
    seen: set[str] = set()
    unique: list[str] = []
    for value in values:
        if value in seen:
            continue
        seen.add(value)
        unique.append(value)
    return unique


def selected_packet_target_key(packet: dict[str, Any]) -> tuple[str, str]:
    return (packet.get("packet_kind", ""), expected_record_target(packet))


def selected_lean_targets(packets: list[dict[str, Any]]) -> set[str]:
    return {
        expected_record_target(packet)
        for packet in packets
        if packet.get("packet_kind") == "lean_reconstruction"
    }


def selected_source_targets(packets: list[dict[str, Any]]) -> set[str]:
    return {
        expected_record_target(packet)
        for packet in packets
        if packet.get("packet_kind") == "source_intention"
    }


def internal_batch_dependency_errors(state: dict[str, Any], packets: list[dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    selected_lean = selected_lean_targets(packets)
    selected_source = selected_source_targets(packets)

    if len(selected_lean) >= 2:
        selected_decl_nodes = {f"decl:{name}" for name in selected_lean}
        for edge in state.get("graph", {}).get("edges", []):
            if not str(edge.get("kind", "")).startswith("USES_CONSTANT_"):
                continue
            source = str(edge.get("source", ""))
            target = str(edge.get("target", ""))
            if source in selected_decl_nodes and target in selected_decl_nodes:
                errors.append(
                    "Queue contains mutually context-sensitive Lean packets: "
                    f"{source.removeprefix('decl:')} uses {target.removeprefix('decl:')}. "
                    "Bundle and ingest one stratum, rerun the audit, then bundle dependents."
                )

    for packet in packets:
        if packet.get("packet_kind") != "comparison":
            continue
        inputs = packet.get("inputs", {})
        lean_declaration = inputs.get("lean_declaration", "")
        source_id = inputs.get("source_id", "")
        if lean_declaration in selected_lean:
            errors.append(
                f"Comparison packet {packet.get('packet_id', '')} depends on Lean packet "
                f"{packet_id('lean_reconstruction', lean_declaration)} selected in the same batch."
            )
        if source_id in selected_source:
            errors.append(
                f"Comparison packet {packet.get('packet_id', '')} depends on source packet "
                f"{packet_id('source_intention', source_id)} selected in the same batch."
            )
    return unique_values(errors)


def validate_selected_packets(
    state: dict[str, Any],
    packets: list[dict[str, Any]],
    plan: dict[str, Any],
    *,
    allow_blocked: bool = False,
    allow_internal_dependencies: bool = False,
) -> list[str]:
    errors: list[str] = []
    packet_ids = [packet.get("packet_id", "") for packet in packets]
    for duplicate in duplicate_values(packet_ids):
        errors.append(f"Queue contains duplicate packet id `{duplicate}`.")
    target_keys = [":".join(selected_packet_target_key(packet)) for packet in packets]
    for duplicate in duplicate_values(target_keys):
        errors.append(f"Queue contains duplicate packet target `{duplicate}`.")
    bundle_dirs = [
        str(entry.get("bundle_dir", ""))
        for entry in plan.get("packets", [])
        if entry.get("bundle_dir")
    ]
    for duplicate in duplicate_values(bundle_dirs):
        errors.append(f"Queue contains duplicate bundle directory `{duplicate}`.")

    unassignable = [
        packet for packet in packets
        if packet.get("status") not in ASSIGNABLE_PACKET_STATUSES
        and not (allow_blocked and packet.get("status") == "blocked")
    ]
    if unassignable:
        ids = ", ".join(packet.get("packet_id", "") for packet in unassignable)
        errors.append(f"Queue contains non-assignable packet status(es): {ids}.")

    if not allow_internal_dependencies:
        errors.extend(internal_batch_dependency_errors(state, packets))
    return errors


def build_queue_plan(
    repo: Path,
    state: dict[str, Any],
    packets: list[dict[str, Any]],
    filters: dict[str, Any],
    *,
    work_root: str | Path = DEFAULT_WORK,
    batch_dir: str | Path | None = None,
) -> dict[str, Any]:
    digest = digest_json(queue_plan_digest_payload(state, filters, packets))
    resolved_batch_dir = Path(batch_dir) if batch_dir else default_batch_dir(repo, state, work_root, digest)
    if not resolved_batch_dir.is_absolute():
        resolved_batch_dir = repo / resolved_batch_dir
    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": QUEUE_PLAN_ARTIFACT,
        "created_at": now_utc(),
        "run_id": state.get("run", {}).get("run_id", ""),
        "run_commit": state.get("run", {}).get("commit", ""),
        "selection_digest": digest,
        "filters": filters,
        "packet_count": len(packets),
        "paths": {
            "batch_dir": path_label(repo, resolved_batch_dir),
            "queue_plan": QUEUE_PLAN_FILE,
            "bundles_dir": "bundles",
        },
        "packets": [
            queue_packet_entry(repo, resolved_batch_dir, packet)
            for packet in packets
        ],
    }


def validate_queue_plan(plan: dict[str, Any], state: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if plan.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"Queue plan schema_version is {plan.get('schema_version')!r}, expected {SCHEMA_VERSION}.")
    if plan.get("artifact") != QUEUE_PLAN_ARTIFACT:
        errors.append(f"Queue plan artifact is {plan.get('artifact')!r}, expected {QUEUE_PLAN_ARTIFACT}.")
    latest_run_id = state.get("run", {}).get("run_id", "")
    if plan.get("run_id") != latest_run_id:
        errors.append(f"Queue plan was created from run {plan.get('run_id')!r}, latest run is {latest_run_id!r}.")
    packets = plan.get("packets", [])
    if not isinstance(packets, list):
        errors.append("Queue plan `packets` must be a list.")
    return errors


def path_from_label(repo: Path, label: str | Path) -> Path:
    path = Path(label)
    if path.is_absolute():
        return path
    return repo / path


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


def answer_contract_for_kind(kind: str) -> dict[str, list[str]]:
    common_protected = [
        "schema_version",
        "packet_id",
        "source_run_id",
        "context_fingerprint",
        "updated_at",
    ]
    if kind == "lean_reconstruction":
        return {
            "protected": common_protected + ["record_id", "declaration"],
            "fill": ["status", "summary", "reconstructed_statement", "assumptions"],
            "notes": [
                "`status` must be `answered` before ingest.",
                "`reconstructed_statement` should say what the Lean declaration currently asserts, not what the paper should assert.",
                "`assumptions` should include decorrelation caveats and any uncertainty about notation or scope.",
            ],
        }
    if kind == "source_intention":
        return {
            "protected": common_protected + ["record_id", "source_id", "paper_label"],
            "fill": ["status", "summary", "intended_statement", "evidence"],
            "notes": [
                "`status` must be `answered` before ingest.",
                "`intended_statement` should reconstruct the source target without treating Lean as ground truth.",
                "`evidence` should identify the source excerpts or labels used.",
            ],
        }
    if kind == "comparison":
        return {
            "protected": common_protected + [
                "comparison_id",
                "lean_declaration",
                "lean_record_id",
                "source_id",
                "source_record_id",
            ],
            "fill": ["status", "alignment", "summary", "notes"],
            "notes": [
                "`status` must be `answered` before ingest.",
                "`alignment` should be one of: match, exact, partial, lean_weaker, lean_stronger, mismatch, convention_mismatch, unclear.",
                "`notes` should name the exact hypothesis, convention, or scope differences.",
            ],
        }
    if kind == "api_boundary":
        return {
            "protected": common_protected + ["record_id", "target_id", "lean_declaration"],
            "fill": ["status", "summary", "notes"],
            "notes": [
                "`status` must be `answered` before ingest.",
                "`notes` should distinguish intentional mathematical generality from accidental API overbreadth.",
            ],
        }
    return {
        "protected": common_protected,
        "fill": ["status", "summary"],
        "notes": ["Use only the evidence in `context.json`."],
    }


def format_answer_contract(contract: dict[str, list[str]]) -> list[str]:
    lines = [
        "- Edit `answer.json` only.",
        "- Set `status` to `answered` when complete.",
        "- Use TeX delimiters such as `\\(...\\)` or `\\[...\\]` for mathematical notation.",
        "- Make assumptions explicit in the relevant field rather than hiding them.",
        f"- Protected fields: {', '.join(f'`{field}`' for field in contract.get('protected', []))}.",
        f"- Worker-filled fields: {', '.join(f'`{field}`' for field in contract.get('fill', []))}.",
    ]
    lines.extend(f"- {note}" for note in contract.get("notes", []))
    return lines


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
    contract = answer_contract_for_kind(kind)
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
        *format_answer_contract(contract),
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


def ingest_validation_outcome(
    repo: Path,
    state: dict[str, Any],
    input_path: Path,
    *,
    kind_override: str | None = None,
    replace: bool = False,
    append_requested: bool = False,
    allow_stale: bool = False,
    allow_unbundled: bool = False,
    allow_nonassignable: bool = False,
    strict: bool = False,
    require_bundle: bool = False,
) -> dict[str, Any]:
    outcome: dict[str, Any] = {
        "input": input_path.as_posix(),
        "kind": "",
        "packet_id": "",
        "identity": "",
        "identity_field": "",
        "action": "",
        "record_path": "",
        "warnings": [],
        "errors": [],
    }
    errors: list[str] = outcome["errors"]
    warnings: list[str] = outcome["warnings"]

    try:
        bundle = read_bundle_input(input_path)
    except (OSError, json.JSONDecodeError, SystemExit) as exc:
        errors.append(str(exc))
        return outcome

    record = bundle["record"]
    manifest = bundle.get("manifest", {})
    if require_bundle and not manifest:
        errors.append("Batch ingest requires packet bundle directories with manifest.json.")

    try:
        kind = kind_override or infer_record_kind(record)
    except SystemExit as exc:
        errors.append(str(exc))
        return outcome

    outcome["kind"] = kind
    identity_field = record_identity_field(kind)
    outcome["identity_field"] = identity_field
    outcome["identity"] = record.get(identity_field, "")

    errors.extend(validate_record(record, kind, for_append=True))
    warnings.extend(lint_record(record, kind))

    packet = None
    if not manifest and append_requested and not allow_unbundled:
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
        outcome["packet_id"] = packet.get("packet_id", "")
        if (
            not allow_nonassignable
            and packet.get("status") not in ASSIGNABLE_PACKET_STATUSES
        ):
            errors.append(
                f"Latest packet status is `{packet.get('status', '')}`; ingest expects one of "
                f"{ASSIGNABLE_PACKET_STATUSES}. Pass the debug override only if this is intentional."
            )
        errors.extend(validate_record_against_packet(record, kind, packet))
        errors.extend(validate_manifest_record_consistency(manifest, record, kind, packet))
        provenance_errors, provenance_warnings = validate_bundle_provenance(
            manifest,
            bundle.get("context", {}),
            packet,
            state,
            allow_stale=allow_stale,
        )
        errors.extend(provenance_errors)
        warnings.extend(provenance_warnings)
        live_errors, live_warnings = validate_current_context_for_append(
            repo,
            state,
            manifest,
            packet,
            allow_stale=allow_stale,
        )
        errors.extend(live_errors)
        warnings.extend(live_warnings)

    if strict and warnings:
        errors.extend(f"Strict lint: {warning}" for warning in warnings)

    record_to_write = record
    if allow_stale and warnings:
        record_to_write = dict(record)
        record_to_write["stale_accepted"] = {
            "accepted_at": now_utc(),
            "warnings": warnings,
        }

    if not errors:
        try:
            result = append_record_to_store(repo, record_to_write, kind, replace=replace, dry_run=True)
            outcome["action"] = result["action"]
            outcome["record_path"] = result["path"]
        except SystemExit as exc:
            errors.append(str(exc))

    outcome["_record"] = record_to_write
    return outcome


def public_ingest_outcome(outcome: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in outcome.items()
        if not key.startswith("_")
    }


def add_batch_duplicate_errors(outcomes: list[dict[str, Any]]) -> None:
    seen: dict[tuple[str, str], int] = {}
    for index, outcome in enumerate(outcomes):
        if outcome.get("errors"):
            continue
        key = (outcome.get("kind", ""), outcome.get("identity", ""))
        if not key[0] or not key[1]:
            continue
        previous = seen.get(key)
        if previous is None:
            seen[key] = index
            continue
        message = (
            f"Batch contains duplicate {outcome.get('identity_field', 'record identity')} "
            f"`{key[1]}` for kind `{key[0]}`."
        )
        outcomes[previous].setdefault("errors", []).append(message)
        outcome.setdefault("errors", []).append(message)


def apply_record_to_records(
    records: list[dict[str, Any]],
    record: dict[str, Any],
    kind: str,
    *,
    replace: bool = False,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    identity_field = record_identity_field(kind)
    identity = record.get(identity_field, "")
    target_field = record_target_field_for_kind(kind)
    target = record.get(target_field, "")
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
        raise SystemExit(f"Cannot replace `{identity}`: no existing record with {identity_field} `{identity}`.")
    if duplicate_indexes and not replace:
        raise SystemExit(f"Record `{identity}` already exists. Use --replace to replace by {identity_field}.")

    action = "replace" if duplicate_indexes and replace else "append"
    if duplicate_indexes and replace:
        first = duplicate_indexes[0]
        duplicate_set = set(duplicate_indexes)
        updated = [
            existing
            for index, existing in enumerate(records)
            if index not in duplicate_set
        ]
        updated.insert(first, record)
    else:
        updated = [*records, record]
    return updated, {
        "action": action,
        "identity": identity,
        "identity_field": identity_field,
    }


def batch_record_write_plan(
    repo: Path,
    outcomes: list[dict[str, Any]],
    *,
    replace: bool = False,
) -> dict[Path, list[dict[str, Any]]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    for outcome in outcomes:
        if outcome.get("errors"):
            raise SystemExit("Cannot create a batch write plan while outcomes contain errors.")
        grouped.setdefault(outcome["kind"], []).append(outcome)

    writes: dict[Path, list[dict[str, Any]]] = {}
    for kind, kind_outcomes in grouped.items():
        key = record_file_key_for_kind(kind)
        path = repo / RECORDS_DIR / RECORD_FILE_NAMES[key]
        records = read_jsonl(path)
        for outcome in kind_outcomes:
            records, result = apply_record_to_records(
                records,
                outcome["_record"],
                kind,
                replace=replace,
            )
            outcome["action"] = result["action"]
            outcome["identity"] = result["identity"]
            outcome["identity_field"] = result["identity_field"]
            outcome["record_path"] = path.as_posix()
        writes[path] = records
    return writes


def write_jsonl_atomic(path: Path, records: list[dict[str, Any]]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.tmp")
    tmp.write_text(
        "".join(json.dumps(record, sort_keys=True) + "\n" for record in records),
        encoding="utf-8",
    )
    return tmp


def commit_batch_ingest_outcomes(repo: Path, outcomes: list[dict[str, Any]], *, replace: bool = False) -> None:
    if any(outcome.get("errors") for outcome in outcomes):
        raise SystemExit("Cannot append a batch with validation errors.")
    writes = batch_record_write_plan(repo, outcomes, replace=replace)
    temp_paths: list[tuple[Path, Path]] = []
    try:
        for path, records in writes.items():
            temp_paths.append((write_jsonl_atomic(path, records), path))
        for tmp, path in temp_paths:
            tmp.replace(path)
    finally:
        for tmp, _path in temp_paths:
            if tmp.exists():
                tmp.unlink()


def commit_ingest_outcome(repo: Path, outcome: dict[str, Any], *, replace: bool = False) -> None:
    if outcome.get("errors"):
        raise SystemExit(f"Cannot append invalid bundle {outcome.get('input', '')}.")
    result = append_record_to_store(
        repo,
        outcome["_record"],
        outcome["kind"],
        replace=replace,
        dry_run=False,
    )
    outcome["action"] = result["action"]
    outcome["identity"] = result["identity"]
    outcome["identity_field"] = result["identity_field"]
    outcome["record_path"] = result["path"]


def print_ingest_outcome(outcome: dict[str, Any]) -> None:
    status = "error" if outcome.get("errors") else "ok"
    print(
        f"{status:5} {outcome.get('kind', ''):20} "
        f"{outcome.get('packet_id', ''):60} {outcome.get('identity', '')}"
    )
    for warning in outcome.get("warnings", []):
        print(f"  WARNING: {warning}", file=sys.stderr)
    for error in outcome.get("errors", []):
        print(f"  ERROR: {error}", file=sys.stderr)


def queue_plan_from_args(
    repo: Path,
    state: dict[str, Any],
    args: argparse.Namespace,
    *,
    batch_dir: str | Path | None = None,
) -> dict[str, Any]:
    filters = selection_filter_summary(args)
    selected = select_queue_packets(
        state["packets"],
        kinds=args.kind,
        statuses=args.status,
        priorities=args.priority,
        limit=args.limit,
    )
    return build_queue_plan(
        repo,
        state,
        selected,
        filters,
        work_root=args.work_root,
        batch_dir=batch_dir,
    )


def packet_ids_from_queue_plan(plan: dict[str, Any]) -> list[str]:
    return [
        str(entry.get("packet_id", ""))
        for entry in plan.get("packets", [])
        if entry.get("packet_id")
    ]


def packets_from_queue_plan(state: dict[str, Any], plan: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        find_packet(state["packets"], packet_id)
        for packet_id in packet_ids_from_queue_plan(plan)
    ]


def bundle_paths_from_batch_input(repo: Path, input_path: Path) -> tuple[dict[str, Any], list[Path]]:
    if input_path.is_file():
        plan = read_json(input_path)
        base_dir = input_path.parent
    elif (input_path / QUEUE_PLAN_FILE).exists():
        plan = read_json(input_path / QUEUE_PLAN_FILE)
        base_dir = input_path
    elif (input_path / "manifest.json").exists():
        return {}, [input_path]
    else:
        manifest_paths = sorted((input_path / "bundles").glob("*/manifest.json"))
        if manifest_paths:
            return {}, [path.parent for path in manifest_paths]
        raise SystemExit(
            f"Could not find {QUEUE_PLAN_FILE}, manifest.json, or bundles/*/manifest.json under {input_path}."
        )

    if plan.get("artifact") != QUEUE_PLAN_ARTIFACT:
        raise SystemExit(f"Expected a {QUEUE_PLAN_ARTIFACT} artifact in {input_path}.")
    bundle_paths: list[Path] = []
    for entry in plan.get("packets", []):
        bundle_label = entry.get("bundle_dir", "")
        if not bundle_label:
            continue
        bundle_path = Path(bundle_label)
        if not bundle_path.is_absolute():
            repo_path = repo / bundle_path
            bundle_path = repo_path if repo_path.exists() else base_dir / bundle_path
        bundle_paths.append(bundle_path)
    return plan, bundle_paths


def queue_plan_from_batch_input(repo: Path, input_path: Path) -> tuple[dict[str, Any], Path, list[Path]]:
    if input_path.is_file():
        plan_path = input_path
        batch_dir = input_path.parent
    elif (input_path / QUEUE_PLAN_FILE).exists():
        plan_path = input_path / QUEUE_PLAN_FILE
        batch_dir = input_path
    else:
        raise SystemExit(f"Expected a batch directory or {QUEUE_PLAN_FILE}: {input_path}")
    plan, bundle_paths = bundle_paths_from_batch_input(repo, plan_path)
    return plan, batch_dir, bundle_paths


def bundle_file_errors(bundle_dir: Path, *, require_answer: bool = True) -> list[str]:
    errors: list[str] = []
    filenames = ["manifest.json", "context.json", "instructions.md"]
    if require_answer:
        filenames.append("answer.json")
    for filename in filenames:
        path = bundle_dir / filename
        if not path.exists():
            errors.append(f"Bundle is missing {filename}: {bundle_dir}")
        elif not path.is_file():
            errors.append(f"Bundle path is not a file: {path}")
    return errors


def dispatch_allowed_kind_errors(packets: list[dict[str, Any]], allowed_kinds: list[str]) -> list[str]:
    allowed = set(allowed_kinds)
    return [
        f"Packet {packet.get('packet_id', '')} has kind `{packet.get('packet_kind', '')}`, not one of {sorted(allowed)}."
        for packet in packets
        if packet.get("packet_kind") not in allowed
    ]


def dispatch_assignment(
    repo: Path,
    packet: dict[str, Any],
    bundle_dir: Path,
    *,
    index: int,
) -> dict[str, Any]:
    worker_id = f"worker-{index + 1:04d}"
    return {
        "worker_id": worker_id,
        "packet_id": packet.get("packet_id", ""),
        "packet_kind": packet.get("packet_kind", ""),
        "packet_status": packet.get("status", ""),
        "packet_target": packet.get("target", ""),
        "priority": packet.get("priority", ""),
        "bundle_dir": path_label(repo, bundle_dir),
        "manifest": path_label(repo, bundle_dir / "manifest.json"),
        "context": path_label(repo, bundle_dir / "context.json"),
        "instructions": path_label(repo, bundle_dir / "instructions.md"),
        "answer": path_label(repo, bundle_dir / "answer.json"),
        "worker_prompt": path_label(repo, bundle_dir / WORKER_PROMPT_FILE),
    }


def worker_prompt_text(assignment: dict[str, Any], run_id: str) -> str:
    bundle_arg = shlex.quote(assignment.get("bundle_dir", ""))
    run_guard = f" --expect-run-id {shlex.quote(run_id)}" if run_id else ""
    return "\n".join([
        "# Semantic Audit Worker Assignment",
        "",
        "You are a semantic audit worker running inside the current Claude Code, Codex, or compatible agent substrate.",
        "",
        "## Assignment",
        "",
        f"- Worker id: `{assignment.get('worker_id', '')}`",
        f"- Packet id: `{assignment.get('packet_id', '')}`",
        f"- Kind: `{assignment.get('packet_kind', '')}`",
        f"- Target: `{assignment.get('packet_target', '')}`",
        f"- Bundle directory: `{assignment.get('bundle_dir', '')}`",
        "",
        "## Files",
        "",
        f"- Read: `{assignment.get('instructions', '')}`",
        f"- Read: `{assignment.get('context', '')}`",
        f"- Edit: `{assignment.get('answer', '')}`",
        f"- Do not edit: `{assignment.get('manifest', '')}`",
        "",
        "## Rules",
        "",
        "- Edit only this bundle's `answer.json`.",
        "- Preserve protected provenance and identity fields already present in `answer.json`.",
        "- Set `status` to `answered` only when the answer is complete.",
        "- Use TeX delimiters such as `\\(...\\)` or `\\[...\\]` for mathematical notation.",
        "- Do not edit durable records under `tools/semantic-audit/records/`.",
        "- Do not edit queue plans, dispatch manifests, other bundles, Lean files, or exposition files.",
        "- Use only the evidence allowed by `context.json` and the evidence discipline in `instructions.md`.",
        "",
        "## Controller Validation",
        "",
        "The controller will validate your returned answer with:",
        "",
        "```bash",
        f"python3 tools/semantic-audit/semantic_audit.py packet ingest {bundle_arg}{run_guard}",
        "```",
        "",
        "Leave your completed answer in `answer.json` for the controller to collect.",
        "",
    ])


def dispatch_manifest(
    repo: Path,
    state: dict[str, Any],
    plan: dict[str, Any],
    batch_dir: Path,
    packets: list[dict[str, Any]],
    bundle_paths: list[Path],
    *,
    allowed_kinds: list[str],
) -> dict[str, Any]:
    assignments = [
        dispatch_assignment(repo, packet, bundle_path, index=index)
        for index, (packet, bundle_path) in enumerate(zip(packets, bundle_paths, strict=True))
    ]
    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": DISPATCH_MANIFEST_ARTIFACT,
        "created_at": now_utc(),
        "run_id": state.get("run", {}).get("run_id", ""),
        "run_commit": state.get("run", {}).get("commit", ""),
        "batch_dir": path_label(repo, batch_dir),
        "queue_plan": path_label(repo, batch_dir / QUEUE_PLAN_FILE),
        "allowed_kinds": sorted(allowed_kinds),
        "assignment_count": len(assignments),
        "assignments": assignments,
        "worker_contract": {
            "workspace_model": "shared_bundle_files",
            "worker_output": "edit_answer_json",
            "durable_append": "controller_only",
        },
    }


def read_dispatch_manifest(batch_dir: Path) -> dict[str, Any]:
    path = batch_dir / DISPATCH_MANIFEST_FILE
    if not path.exists():
        return {}
    return read_json(path)


def dispatch_manifest_errors(
    repo: Path,
    state: dict[str, Any],
    batch_dir: Path,
    plan: dict[str, Any],
    bundle_paths: list[Path],
    dispatch: dict[str, Any],
) -> list[str]:
    errors: list[str] = []
    if dispatch.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"Dispatch manifest schema_version is {dispatch.get('schema_version')!r}, expected {SCHEMA_VERSION}.")
    if dispatch.get("artifact") != DISPATCH_MANIFEST_ARTIFACT:
        errors.append(f"Dispatch manifest artifact is {dispatch.get('artifact')!r}, expected {DISPATCH_MANIFEST_ARTIFACT}.")
    latest_run_id = state.get("run", {}).get("run_id", "")
    if dispatch.get("run_id") != latest_run_id:
        errors.append("Dispatch manifest run_id does not match the latest run.")
    if dispatch.get("batch_dir") != path_label(repo, batch_dir):
        errors.append("Dispatch manifest batch_dir does not match the collected batch directory.")
    if dispatch.get("queue_plan") != path_label(repo, batch_dir / QUEUE_PLAN_FILE):
        errors.append("Dispatch manifest queue_plan does not match the collected queue plan.")

    assignments = dispatch.get("assignments", [])
    if not isinstance(assignments, list):
        errors.append("Dispatch manifest `assignments` must be a list.")
        return errors
    if dispatch.get("assignment_count") != len(assignments):
        errors.append(
            f"Dispatch manifest assignment_count is {dispatch.get('assignment_count')!r}, "
            f"but assignments has length {len(assignments)}."
        )
    for index, assignment in enumerate(assignments):
        if not isinstance(assignment, dict):
            errors.append(f"Dispatch manifest assignment {index} must be an object.")

    expected_packet_ids = packet_ids_from_queue_plan(plan)
    assigned_packet_ids = [
        str(assignment.get("packet_id", ""))
        for assignment in assignments
        if isinstance(assignment, dict)
    ]
    if assigned_packet_ids != expected_packet_ids:
        errors.append(
            "Dispatch manifest packet ids do not match the queue plan: "
            f"expected {expected_packet_ids}, got {assigned_packet_ids}."
        )

    expected_bundle_dirs = [path_label(repo, bundle_path) for bundle_path in bundle_paths]
    assigned_bundle_dirs = [
        str(assignment.get("bundle_dir", ""))
        for assignment in assignments
        if isinstance(assignment, dict)
    ]
    if assigned_bundle_dirs != expected_bundle_dirs:
        errors.append("Dispatch manifest bundle directories do not match the queue plan.")

    return errors


def classify_answer_record(answer_path: Path) -> tuple[str, dict[str, Any], list[str]]:
    if not answer_path.exists():
        return "missing", {}, [f"Missing answer.json: {answer_path}"]
    try:
        record = read_record_object(answer_path)
    except (OSError, json.JSONDecodeError, SystemExit) as exc:
        return "unreadable", {}, [f"Could not read answer.json: {exc}"]
    if record.get("status") != "answered":
        return "draft", record, [f"Answer status is `{record.get('status', '')}`, not `answered`."]
    return "answered", record, []


def collect_assignment_outcome(
    repo: Path,
    state: dict[str, Any],
    bundle_path: Path,
    assignment: dict[str, Any] | None,
    args: argparse.Namespace,
) -> dict[str, Any]:
    answer_status, _record, read_errors = classify_answer_record(bundle_path / "answer.json")
    base = {
        "worker_id": assignment.get("worker_id", "") if assignment else "",
        "packet_id": assignment.get("packet_id", "") if assignment else "",
        "packet_kind": assignment.get("packet_kind", "") if assignment else "",
        "bundle_dir": path_label(repo, bundle_path),
        "answer": path_label(repo, bundle_path / "answer.json"),
        "status": answer_status,
        "warnings": [],
        "errors": read_errors,
    }
    if answer_status != "answered":
        return base

    outcome = ingest_validation_outcome(
        repo,
        state,
        bundle_path,
        kind_override=args.kind,
        replace=args.replace,
        append_requested=args.append,
        allow_stale=args.allow_stale,
        allow_nonassignable=args.allow_nonassignable,
        strict=args.strict,
        require_bundle=True,
    )
    status = "answered-invalid" if outcome.get("errors") else "answered-valid"
    base.update({
        "status": status,
        "kind": outcome.get("kind", ""),
        "identity": outcome.get("identity", ""),
        "identity_field": outcome.get("identity_field", ""),
        "record_path": outcome.get("record_path", ""),
        "warnings": outcome.get("warnings", []),
        "errors": outcome.get("errors", []),
        "validation": public_ingest_outcome(outcome),
        "_ingest_outcome": outcome,
    })
    return base


def public_collect_assignment(assignment: dict[str, Any]) -> dict[str, Any]:
    return {
        key: value
        for key, value in assignment.items()
        if not key.startswith("_")
    }


def worker_run_report(
    repo: Path,
    state: dict[str, Any],
    batch_dir: Path,
    plan: dict[str, Any],
    dispatch: dict[str, Any],
    assignments: list[dict[str, Any]],
    *,
    append_requested: bool,
    appended: bool,
) -> dict[str, Any]:
    counts: dict[str, int] = {}
    for assignment in assignments:
        status = assignment.get("status", "")
        counts[status] = counts.get(status, 0) + 1
    return {
        "schema_version": SCHEMA_VERSION,
        "artifact": WORKER_RUN_ARTIFACT,
        "created_at": now_utc(),
        "run_id": state.get("run", {}).get("run_id", ""),
        "run_commit": state.get("run", {}).get("commit", ""),
        "batch_dir": path_label(repo, batch_dir),
        "queue_plan": path_label(repo, batch_dir / QUEUE_PLAN_FILE),
        "dispatch_manifest": path_label(repo, batch_dir / DISPATCH_MANIFEST_FILE) if dispatch else "",
        "dispatch_present": bool(dispatch),
        "packet_count": len(plan.get("packets", [])),
        "assignment_count": len(assignments),
        "status_counts": counts,
        "ok": bool(assignments) and all(assignment.get("status") == "answered-valid" for assignment in assignments),
        "append_requested": append_requested,
        "appended": appended,
        "assignments": [public_collect_assignment(assignment) for assignment in assignments],
    }


def validate_batch_for_dispatch(
    state: dict[str, Any],
    plan: dict[str, Any],
    packets: list[dict[str, Any]],
    bundle_paths: list[Path],
    *,
    allowed_kinds: list[str],
    allow_blocked: bool = False,
    allow_internal_dependencies: bool = False,
    require_answers: bool = True,
    require_nonempty: bool = True,
) -> list[str]:
    errors = validate_queue_plan(plan, state)
    if require_nonempty and not packets:
        errors.append("Queue selection is empty. Create a non-empty batch before dispatch or collection.")
    errors.extend(validate_selected_packets(
        state,
        packets,
        plan,
        allow_blocked=allow_blocked,
        allow_internal_dependencies=allow_internal_dependencies,
    ))
    errors.extend(dispatch_allowed_kind_errors(packets, allowed_kinds))
    if len(bundle_paths) != len(packets):
        errors.append(f"Queue plan has {len(packets)} packets but {len(bundle_paths)} bundle paths.")
    for bundle_path in bundle_paths:
        errors.extend(bundle_file_errors(bundle_path, require_answer=require_answers))
    return errors


def print_collect_report(report: dict[str, Any]) -> None:
    for assignment in report.get("assignments", []):
        print(
            f"{assignment.get('status', ''):17} {assignment.get('packet_kind', ''):20} "
            f"{assignment.get('packet_id', ''):60} {assignment.get('identity', '')}"
        )
        for warning in assignment.get("warnings", []):
            print(f"  WARNING: {warning}", file=sys.stderr)
        for error in assignment.get("errors", []):
            print(f"  ERROR: {error}", file=sys.stderr)
    print(f"assignments: {report.get('assignment_count', 0)}")
    print(f"ok: {str(report.get('ok', False)).lower()}")
    print(f"appended: {str(report.get('appended', False)).lower()}")
    print(f"report: {Path(report.get('batch_dir', '.')) / WORKER_RUN_FILE}")


def command_packet_dispatch_batch(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    enforce_semantic_work_preflight(repo, state, allow_unstable=args.allow_unstable)
    plan, batch_dir, bundle_paths = queue_plan_from_batch_input(repo, Path(args.input))
    packets = packets_from_queue_plan(state, plan)
    allowed_kinds = sorted(set(DEFAULT_DISPATCH_KINDS + (args.allow_kind or [])))
    errors = validate_batch_for_dispatch(
        state,
        plan,
        packets,
        bundle_paths,
        allowed_kinds=allowed_kinds,
        allow_blocked=args.allow_blocked,
        allow_internal_dependencies=args.allow_internal_dependencies,
    )
    manifest_path = batch_dir / DISPATCH_MANIFEST_FILE
    if manifest_path.exists() and not args.force:
        errors.append(f"Dispatch manifest already exists: {manifest_path}. Use --force to overwrite.")
    for bundle_path in bundle_paths:
        prompt_path = bundle_path / WORKER_PROMPT_FILE
        if prompt_path.exists() and not args.force:
            errors.append(f"Worker prompt already exists: {prompt_path}. Use --force to overwrite.")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)

    manifest = dispatch_manifest(
        repo,
        state,
        plan,
        batch_dir,
        packets,
        bundle_paths,
        allowed_kinds=allowed_kinds,
    )
    for assignment in manifest.get("assignments", []):
        prompt_path = path_from_label(repo, assignment["worker_prompt"])
        prompt_path.write_text(worker_prompt_text(assignment, manifest.get("run_id", "")), encoding="utf-8")
    write_json(manifest_path, manifest)

    print(batch_dir)
    print(f"dispatch: {manifest_path}")
    print(f"assignments: {len(manifest.get('assignments', []))}")
    run_guard = f" --expect-run-id {shlex.quote(manifest.get('run_id', ''))}" if manifest.get("run_id") else ""
    print(
        "collect: python3 tools/semantic-audit/semantic_audit.py packet collect-batch "
        f"{shlex.quote(path_label(repo, batch_dir))}{run_guard}"
    )


def command_packet_collect_batch(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    enforce_semantic_work_preflight(repo, state, allow_unstable=args.allow_unstable)
    plan, batch_dir, bundle_paths = queue_plan_from_batch_input(repo, Path(args.input))
    packets = packets_from_queue_plan(state, plan)
    dispatch = read_dispatch_manifest(batch_dir)
    allowed_kinds = sorted(set(DEFAULT_DISPATCH_KINDS + (args.allow_kind or [])))
    errors = validate_batch_for_dispatch(
        state,
        plan,
        packets,
        bundle_paths,
        allowed_kinds=allowed_kinds,
        allow_blocked=args.allow_blocked,
        allow_internal_dependencies=args.allow_internal_dependencies,
        require_answers=False,
    )
    if dispatch:
        errors.extend(dispatch_manifest_errors(repo, state, batch_dir, plan, bundle_paths, dispatch))
    if errors:
        report = worker_run_report(
            repo,
            state,
            batch_dir,
            plan,
            dispatch,
            [{
                "status": "unreadable",
                "packet_id": "",
                "packet_kind": "",
                "bundle_dir": path_label(repo, batch_dir),
                "answer": "",
                "warnings": [],
                "errors": errors,
            }],
            append_requested=args.append,
            appended=False,
        )
        write_json(batch_dir / WORKER_RUN_FILE, report)
        if args.json:
            emit_json(report, None)
        else:
            print_collect_report(report)
        raise SystemExit(1)

    dispatch_by_packet = {
        assignment.get("packet_id", ""): assignment
        for assignment in dispatch.get("assignments", [])
        if isinstance(assignment, dict) and assignment.get("packet_id")
    }
    collect_assignments: list[dict[str, Any]] = []
    for index, (packet, bundle_path) in enumerate(zip(packets, bundle_paths, strict=True)):
        assignment = dispatch_by_packet.get(packet.get("packet_id", ""))
        if assignment is None:
            assignment = dispatch_assignment(repo, packet, bundle_path, index=index)
        collect_assignments.append(collect_assignment_outcome(repo, state, bundle_path, assignment, args))

    ingest_outcomes = [
        assignment["_ingest_outcome"]
        for assignment in collect_assignments
        if assignment.get("_ingest_outcome")
    ]
    add_batch_duplicate_errors(ingest_outcomes)
    for assignment in collect_assignments:
        outcome = assignment.get("_ingest_outcome")
        if not outcome:
            continue
        assignment["errors"] = outcome.get("errors", [])
        assignment["warnings"] = outcome.get("warnings", [])
        assignment["validation"] = public_ingest_outcome(outcome)
        if outcome.get("errors"):
            assignment["status"] = "answered-invalid"

    ok = bool(collect_assignments) and all(
        assignment.get("status") == "answered-valid"
        for assignment in collect_assignments
    )
    appended = False
    if args.append:
        if not ok:
            report = worker_run_report(
                repo,
                state,
                batch_dir,
                plan,
                dispatch,
                collect_assignments,
                append_requested=True,
                appended=False,
            )
            write_json(batch_dir / WORKER_RUN_FILE, report)
            if args.json:
                emit_json(report, None)
            else:
                print_collect_report(report)
            raise SystemExit(1)
        commit_batch_ingest_outcomes(repo, ingest_outcomes, replace=args.replace)
        appended = True

    report = worker_run_report(
        repo,
        state,
        batch_dir,
        plan,
        dispatch,
        collect_assignments,
        append_requested=args.append,
        appended=appended,
    )
    write_json(batch_dir / WORKER_RUN_FILE, report)
    if args.json:
        emit_json(report, None)
    else:
        print_collect_report(report)
    if not ok:
        raise SystemExit(1)


def command_packet_queue(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    enforce_semantic_work_preflight(repo, state, allow_unstable=args.allow_unstable)
    plan = queue_plan_from_args(repo, state, args)
    packets = packets_from_queue_plan(state, plan)
    errors = validate_selected_packets(
        state,
        packets,
        plan,
        allow_blocked=args.allow_blocked,
        allow_internal_dependencies=args.allow_internal_dependencies,
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
    if args.output:
        emit_json(plan, args.output)
    else:
        emit_json(plan, None)


def command_packet_bundle_batch(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    enforce_semantic_work_preflight(repo, state, allow_unstable=args.allow_unstable)
    if args.plan:
        plan = read_json(Path(args.plan))
        errors = validate_queue_plan(plan, state)
        if errors:
            for error in errors:
                print(f"ERROR: {error}", file=sys.stderr)
            raise SystemExit(1)
        batch_dir = path_from_label(repo, args.output or plan.get("paths", {}).get("batch_dir", ""))
    else:
        batch_dir = Path(args.output) if args.output else None
        plan = queue_plan_from_args(repo, state, args, batch_dir=batch_dir)
        batch_dir = path_from_label(repo, plan.get("paths", {}).get("batch_dir", ""))

    packets = packets_from_queue_plan(state, plan)
    if not packets and not args.allow_empty:
        raise SystemExit("Queue selection is empty. Adjust filters or pass --allow-empty.")
    if batch_dir.exists() and not args.force:
        raise SystemExit(f"Batch directory already exists: {batch_dir}. Use --force to overwrite generated bundle files.")

    plan = build_queue_plan(
        repo,
        state,
        packets,
        plan.get("filters", {}),
        work_root=args.work_root,
        batch_dir=batch_dir,
    )
    errors = validate_selected_packets(
        state,
        packets,
        plan,
        allow_blocked=args.allow_blocked,
        allow_internal_dependencies=args.allow_internal_dependencies,
    )
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
    batch_dir.mkdir(parents=True, exist_ok=True)
    write_json(batch_dir / QUEUE_PLAN_FILE, plan)
    for packet, entry in zip(packets, plan.get("packets", []), strict=True):
        bundle_dir = path_from_label(repo, entry["bundle_dir"])
        write_packet_bundle(repo, state, packet, bundle_dir, force=args.force)

    run_id = state.get("run", {}).get("run_id", "")
    run_guard = f" --expect-run-id {shlex.quote(run_id)}" if run_id else ""
    print(batch_dir)
    print(f"queue: {batch_dir / QUEUE_PLAN_FILE}")
    print(f"bundles: {len(packets)}")
    print(
        "ingest: python3 tools/semantic-audit/semantic_audit.py packet ingest-batch "
        f"{shlex.quote(path_label(repo, batch_dir))}{run_guard}"
    )


def command_packet_ingest_batch(args: argparse.Namespace) -> None:
    repo = repo_root_from_script()
    state = load_state_for_cli(repo, args.out_root, args.expect_run_id)
    enforce_semantic_work_preflight(repo, state, allow_unstable=args.allow_unstable)
    try:
        plan, bundle_paths = bundle_paths_from_batch_input(repo, Path(args.input))
    except (OSError, json.JSONDecodeError, SystemExit) as exc:
        raise SystemExit(str(exc))
    if plan:
        errors = validate_queue_plan(plan, state)
        stale_run_errors = [error for error in errors if "latest run is" in error]
        hard_errors = [error for error in errors if error not in stale_run_errors]
        if hard_errors or (stale_run_errors and not args.allow_stale):
            for error in errors:
                print(f"ERROR: {error}", file=sys.stderr)
            raise SystemExit(1)
        for error in stale_run_errors:
            if args.allow_stale:
                print(f"WARNING: {error}", file=sys.stderr)

    outcomes = [
        ingest_validation_outcome(
            repo,
            state,
            bundle_path,
            kind_override=args.kind,
            replace=args.replace,
            append_requested=args.append,
            allow_stale=args.allow_stale,
            allow_nonassignable=args.allow_nonassignable,
            strict=args.strict,
            require_bundle=True,
        )
        for bundle_path in bundle_paths
    ]
    add_batch_duplicate_errors(outcomes)
    has_errors = any(outcome.get("errors") for outcome in outcomes)

    if args.json:
        emit_json({
            "schema_version": SCHEMA_VERSION,
            "artifact": "semantic-audit-ingest-batch-result",
            "input": args.input,
            "bundle_count": len(outcomes),
            "ok": not has_errors,
            "append": bool(args.append),
            "outcomes": [public_ingest_outcome(outcome) for outcome in outcomes],
        }, None)
    else:
        for outcome in outcomes:
            print_ingest_outcome(outcome)
        print(f"bundles: {len(outcomes)}")
        print(f"errors: {sum(1 for outcome in outcomes if outcome.get('errors'))}")

    if has_errors:
        raise SystemExit(1)

    if args.append:
        commit_batch_ingest_outcomes(repo, outcomes, replace=args.replace)
        if not args.json:
            print(f"appended: {len(outcomes)}")


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
    outcome = ingest_validation_outcome(
        repo,
        state,
        Path(args.input),
        kind_override=args.kind,
        replace=args.replace,
        append_requested=args.append,
        allow_stale=args.allow_stale,
        allow_unbundled=args.allow_unbundled,
        allow_nonassignable=args.allow_nonassignable,
        strict=args.strict,
    )
    for warning in outcome.get("warnings", []):
        print(f"WARNING: {warning}", file=sys.stderr)
    if outcome.get("errors"):
        for error in outcome["errors"]:
            print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)

    if args.append:
        commit_ingest_outcome(repo, outcome, replace=args.replace)
        print(f"wrote {outcome['identity']} to {outcome['record_path']}")
    else:
        print(f"dry-run: would {outcome['action']} {outcome['identity']} in {outcome['record_path']}")
    print(f"kind: {outcome['kind']}")
    if outcome.get("packet_id"):
        print(f"packet: {outcome['packet_id']}")


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
    list_parser.add_argument("--kind", choices=PACKET_KINDS)
    list_parser.add_argument("--status", choices=PACKET_STATUSES)
    list_parser.add_argument("--limit", type=int, default=0)
    list_parser.add_argument("--json", action="store_true", help="emit JSON instead of a compact table")
    list_parser.set_defaults(func=command_packet_list)

    queue_parser = packet_subparsers.add_parser("queue", help="emit a deterministic queue plan for assignable packets")
    queue_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    queue_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    queue_parser.add_argument("--kind", choices=PACKET_KINDS, action="append", help="packet kind to include; repeat to include multiple kinds")
    queue_parser.add_argument("--status", choices=PACKET_STATUSES, action="append", help="packet status to include; default: open and stale")
    queue_parser.add_argument("--priority", choices=PACKET_PRIORITIES, action="append", help="packet priority to include; repeat to include multiple priorities")
    queue_parser.add_argument("--limit", type=int, default=0, help="maximum packets after deterministic sorting")
    queue_parser.add_argument("--work-root", default=str(DEFAULT_WORK), help="root directory for generated worker batches")
    queue_parser.add_argument("--output", "-o", help="write queue plan JSON to this path instead of stdout")
    queue_parser.add_argument("--allow-blocked", action="store_true", help="allow blocked packets in the queue plan for debugging")
    queue_parser.add_argument("--allow-internal-dependencies", action="store_true", help="allow same-batch context dependencies for debugging")
    queue_parser.add_argument("--allow-unstable", action="store_true", help="allow queueing from a non-fresh or non-attested latest run")
    queue_parser.set_defaults(func=command_packet_queue)

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

    bundle_batch_parser = packet_subparsers.add_parser("bundle-batch", help="create a queue plan and worker bundles for many packets")
    bundle_batch_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    bundle_batch_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    bundle_batch_parser.add_argument("--plan", help="existing queue-plan.json to materialize")
    bundle_batch_parser.add_argument("--kind", choices=PACKET_KINDS, action="append", help="packet kind to include; repeat to include multiple kinds")
    bundle_batch_parser.add_argument("--status", choices=PACKET_STATUSES, action="append", help="packet status to include; default: open and stale")
    bundle_batch_parser.add_argument("--priority", choices=PACKET_PRIORITIES, action="append", help="packet priority to include; repeat to include multiple priorities")
    bundle_batch_parser.add_argument("--limit", type=int, default=0, help="maximum packets after deterministic sorting")
    bundle_batch_parser.add_argument("--work-root", default=str(DEFAULT_WORK), help="root directory for generated worker batches")
    bundle_batch_parser.add_argument("--output", "-o", help="write the batch to this directory instead of the deterministic default")
    bundle_batch_parser.add_argument("--force", action="store_true", help="overwrite generated queue and bundle files if the batch directory exists")
    bundle_batch_parser.add_argument("--allow-empty", action="store_true", help="write an empty queue plan when selection has no packets")
    bundle_batch_parser.add_argument("--allow-blocked", action="store_true", help="create debugging bundles for blocked packets")
    bundle_batch_parser.add_argument("--allow-internal-dependencies", action="store_true", help="allow same-batch context dependencies for debugging")
    bundle_batch_parser.add_argument("--allow-unstable", action="store_true", help="allow bundling from a non-fresh or non-attested latest run")
    bundle_batch_parser.set_defaults(func=command_packet_bundle_batch)

    dispatch_batch_parser = packet_subparsers.add_parser("dispatch-batch", help="write agent-native worker prompts for a generated batch")
    dispatch_batch_parser.add_argument("input", help="batch directory or queue-plan.json")
    dispatch_batch_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    dispatch_batch_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    dispatch_batch_parser.add_argument("--allow-kind", choices=PACKET_KINDS, action="append", help="additional packet kind allowed for dispatch; default allows source_intention")
    dispatch_batch_parser.add_argument("--force", action="store_true", help="overwrite existing dispatch manifest and worker prompts")
    dispatch_batch_parser.add_argument("--allow-blocked", action="store_true", help="dispatch blocked packets for debugging")
    dispatch_batch_parser.add_argument("--allow-internal-dependencies", action="store_true", help="dispatch same-batch context dependencies for debugging")
    dispatch_batch_parser.add_argument("--allow-unstable", action="store_true", help="allow dispatch from a non-fresh or non-attested latest run")
    dispatch_batch_parser.set_defaults(func=command_packet_dispatch_batch)

    validate_parser = packet_subparsers.add_parser("validate", help="validate a single answer record JSON object")
    validate_parser.add_argument("record", help="path to a JSON record object")
    validate_parser.add_argument("--kind", choices=PACKET_KINDS)
    validate_parser.add_argument("--for-append", action="store_true", help="require durable answered-record constraints")
    validate_parser.set_defaults(func=command_packet_validate)

    append_parser = packet_subparsers.add_parser("append", help="append a validated answered record to the durable JSONL store")
    append_parser.add_argument("record", help="path to a JSON record object")
    append_parser.add_argument("--kind", choices=PACKET_KINDS)
    append_parser.add_argument("--replace", action="store_true", help="replace an existing record with the same identity")
    append_parser.add_argument("--dry-run", action="store_true", help="validate and report the target file without writing")
    append_parser.set_defaults(func=command_packet_append)

    ingest_parser = packet_subparsers.add_parser("ingest", help="lint and ingest a filled worker bundle answer")
    ingest_parser.add_argument("input", help="bundle directory containing answer.json, or a raw JSON answer record")
    ingest_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    ingest_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    ingest_parser.add_argument("--kind", choices=PACKET_KINDS)
    ingest_parser.add_argument("--dry-run", action="store_true", help="validate and report the target file without writing")
    ingest_parser.add_argument("--append", action="store_true", help="write the validated answer into durable records")
    ingest_parser.add_argument("--replace", action="store_true", help="replace an existing record with the same identity")
    ingest_parser.add_argument("--allow-stale", action="store_true", help="allow bundle run/packet digests to differ from latest")
    ingest_parser.add_argument("--allow-unbundled", action="store_true", help="allow packet ingest --append for a raw JSON record without bundle provenance")
    ingest_parser.add_argument("--allow-nonassignable", action="store_true", help="allow ingest for blocked or already-answered latest packet states")
    ingest_parser.add_argument("--strict", action="store_true", help="treat lint warnings as errors")
    ingest_parser.set_defaults(func=command_packet_ingest)

    ingest_batch_parser = packet_subparsers.add_parser("ingest-batch", help="lint and ingest a queue/bundle batch with two-phase validation")
    ingest_batch_parser.add_argument("input", help="batch directory, queue-plan.json, or bundle directory")
    ingest_batch_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    ingest_batch_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    ingest_batch_parser.add_argument("--kind", choices=PACKET_KINDS)
    ingest_batch_parser.add_argument("--append", action="store_true", help="write all validated answers into durable records")
    ingest_batch_parser.add_argument("--replace", action="store_true", help="replace existing records with matching identities")
    ingest_batch_parser.add_argument("--allow-stale", action="store_true", help="allow stale bundles and mark stale-accepted records when appending")
    ingest_batch_parser.add_argument("--allow-unstable", action="store_true", help="allow ingesting against a non-fresh or non-attested latest run")
    ingest_batch_parser.add_argument("--allow-nonassignable", action="store_true", help="allow ingest for blocked or already-answered latest packet states")
    ingest_batch_parser.add_argument("--strict", action="store_true", help="treat lint warnings as errors")
    ingest_batch_parser.add_argument("--json", action="store_true", help="emit JSON result instead of a compact table")
    ingest_batch_parser.set_defaults(func=command_packet_ingest_batch)

    collect_batch_parser = packet_subparsers.add_parser("collect-batch", help="collect shared-bundle worker answers and write a worker-run report")
    collect_batch_parser.add_argument("input", help="batch directory or queue-plan.json")
    collect_batch_parser.add_argument("--out-root", default=str(DEFAULT_OUT), help="audit output root containing latest/")
    collect_batch_parser.add_argument("--expect-run-id", help="fail if latest/ does not point to this run id")
    collect_batch_parser.add_argument("--kind", choices=PACKET_KINDS)
    collect_batch_parser.add_argument("--append", action="store_true", help="append only if every assignment validates")
    collect_batch_parser.add_argument("--replace", action="store_true", help="replace existing records with matching identities")
    collect_batch_parser.add_argument("--allow-kind", choices=PACKET_KINDS, action="append", help="additional packet kind allowed for collection; default allows source_intention")
    collect_batch_parser.add_argument("--allow-stale", action="store_true", help="allow stale bundles and mark stale-accepted records when appending")
    collect_batch_parser.add_argument("--allow-unstable", action="store_true", help="allow collection against a non-fresh or non-attested latest run")
    collect_batch_parser.add_argument("--allow-nonassignable", action="store_true", help="allow collection for blocked or already-answered latest packet states")
    collect_batch_parser.add_argument("--allow-blocked", action="store_true", help="collect blocked packets for debugging")
    collect_batch_parser.add_argument("--allow-internal-dependencies", action="store_true", help="collect same-batch context dependencies for debugging")
    collect_batch_parser.add_argument("--strict", action="store_true", help="treat lint warnings as errors")
    collect_batch_parser.add_argument("--json", action="store_true", help="emit JSON report instead of a compact table")
    collect_batch_parser.set_defaults(func=command_packet_collect_batch)

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
