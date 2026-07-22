"""Read-only git plumbing. Nothing is checked out; historical states are read
directly from blobs via a persistent `git cat-file --batch` process."""
from __future__ import annotations

import subprocess
from dataclasses import dataclass


@dataclass
class Commit:
    sha: str
    committer_time: int
    author_time: int
    parents: tuple
    subject: str
    author: str


class Repo:
    def __init__(self, root: str):
        self.root = str(root)
        self._batch = None

    def run(self, *args) -> str:
        return subprocess.run(
            ["git", "-C", self.root, *args],
            check=True, capture_output=True, text=True,
        ).stdout

    def rev_parse(self, rev: str) -> str:
        return self.run("rev-parse", rev).strip()

    def merge_base(self, a: str, b: str) -> str:
        return self.run("merge-base", a, b).strip()

    def count(self, spec: str, first_parent: bool = False) -> int:
        args = ["rev-list", "--count"]
        if first_parent:
            args.append("--first-parent")
        return int(self.run(*args, spec).strip())

    def first_parent_lineage(self, base: str, tip: str) -> list:
        """Commits on the first-parent spine, oldest first, excluding base."""
        fmt = "%H%x00%ct%x00%at%x00%P%x00%an%x00%s"
        out = self.run("log", "--first-parent", "--reverse", f"--format={fmt}", f"{base}..{tip}")
        lineage = []
        for line in out.splitlines():
            sha, ct, at, parents, author, subject = line.split("\x00", 5)
            lineage.append(Commit(
                sha=sha, committer_time=int(ct), author_time=int(at),
                parents=tuple(parents.split()) if parents else (),
                subject=subject, author=author,
            ))
        return lineage

    def lean_tree(self, sha: str, lean_root: str) -> list:
        """[(path, blob_sha)] for .lean files under lean_root at the commit."""
        out = self.run("ls-tree", "-r", "-z", sha, "--", lean_root)
        files = []
        for entry in out.split("\0"):
            if not entry or not entry.endswith(".lean"):
                continue
            meta, path = entry.split("\t", 1)
            _mode, otype, blob = meta.split()
            if otype == "blob":
                files.append((path, blob))
        return files

    def numstat_first_parent(self, base: str, tip: str) -> dict:
        """sha → [(path, adds, dels)]; merges measured against first parent."""
        out = self.run(
            "log", "--first-parent", "-m", "--numstat",
            "--format=@%H", f"{base}..{tip}",
        )
        stats, current = {}, None
        for line in out.splitlines():
            if line.startswith("@"):
                current = line[1:]
                stats[current] = []
            elif line and current is not None:
                parts = line.split("\t")
                if len(parts) == 3:
                    adds = int(parts[0]) if parts[0].isdigit() else 0
                    dels = int(parts[1]) if parts[1].isdigit() else 0
                    stats[current].append((parts[2], adds, dels))
        return stats

    # -- batched blob reads ------------------------------------------------

    def _ensure_batch(self):
        if self._batch is None or self._batch.poll() is not None:
            self._batch = subprocess.Popen(
                ["git", "-C", self.root, "cat-file", "--batch"],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            )
        return self._batch

    def blob(self, sha: str) -> bytes:
        proc = self._ensure_batch()
        proc.stdin.write((sha + "\n").encode())
        proc.stdin.flush()
        header = proc.stdout.readline().decode().split()
        if len(header) < 3 or header[1] == "missing":
            raise KeyError(f"missing blob {sha}")
        size = int(header[2])
        data = proc.stdout.read(size)
        proc.stdout.read(1)  # trailing newline
        return data

    def close(self):
        if self._batch is not None:
            self._batch.stdin.close()
            self._batch.wait()
            self._batch = None
