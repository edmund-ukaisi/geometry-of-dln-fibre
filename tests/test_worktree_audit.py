"""scripts/worktree-audit --emit-batch: reviewable cleanup script."""

import os
import sys
import subprocess

import pytest

from conftest import REPO

AUDIT = REPO / "scripts" / "worktree-audit"


def _git(cwd, *args, env=None):
    e = os.environ.copy()
    e.setdefault("GIT_CONFIG_GLOBAL", "/dev/null")
    if env:
        e.update(env)
    return subprocess.run(["git", "-C", str(cwd), *args],
                          capture_output=True, text=True, env=e, check=True)


@pytest.fixture
def repo_with_worktrees(tmp_path):
    """Bare origin + main(dev) + a banked feature worktree + an independent repo."""
    origin = tmp_path / "origin.git"
    subprocess.run(["git", "init", "-q", "--bare", str(origin)], check=True,
                   env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null"})
    main = tmp_path / "main"
    subprocess.run(["git", "init", "-q", str(main)], check=True,
                   env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null"})
    _git(main, "config", "user.email", "t@t")
    _git(main, "config", "user.name", "t")
    _git(main, "config", "commit.gpgsign", "false")
    _git(main, "remote", "add", "origin", str(origin))
    (main / "f.txt").write_text("hi")
    _git(main, "add", "-A")
    _git(main, "commit", "-qm", "init")
    _git(main, "branch", "-M", "dev")
    _git(main, "push", "-q", "origin", "dev")
    # a feature worktree, committed + pushed (banked, ahead of dev)
    feat = tmp_path / "wt-feat"
    _git(main, "worktree", "add", "-q", str(feat), "-b", "feat")
    _git(feat, "config", "user.email", "t@t")
    _git(feat, "config", "user.name", "t")
    (feat / "g.txt").write_text("more")
    _git(feat, "add", "-A")
    _git(feat, "commit", "-qm", "feat-work")
    _git(feat, "push", "-q", "origin", "feat")
    # an independent repo (must never be a removal candidate)
    indep = tmp_path / "indep"
    subprocess.run(["git", "init", "-q", str(indep)], check=True,
                   env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null"})
    _git(indep, "config", "user.email", "t@t")
    _git(indep, "config", "user.name", "t")
    (indep / "z.txt").write_text("z")
    _git(indep, "add", "-A")
    _git(indep, "commit", "-qm", "indep")
    return {"origin": origin, "main": main, "feat": feat, "indep": indep,
            "tmp": tmp_path}


def _audit(*args):
    return subprocess.run([sys.executable, str(AUDIT), *args],
                          capture_output=True, text=True)


def test_report_marks_independent_repo(repo_with_worktrees):
    R = repo_with_worktrees
    r = _audit("--repo", str(R["main"]), "--extra", str(R["tmp"]))
    assert r.returncode == 0, r.stderr
    assert "independent repo" in r.stdout


def test_emit_batch_writes_removals(repo_with_worktrees, tmp_path):
    R = repo_with_worktrees
    out = tmp_path / "batch.sh"
    r = _audit("--repo", str(R["main"]), "--emit-batch", "--min-age-days", "0",
               "--out", str(out))
    assert r.returncode == 0, r.stderr
    text = out.read_text()
    assert text.startswith("#!/bin/sh")
    assert f"git worktree remove {R['feat']}" in text
    assert "branch: feat" in text and "banked: yes" in text
    # the main checkout itself is never a removal candidate
    assert f"git worktree remove {R['main']}" not in text


def test_batch_branch_deletes_are_commented_with_preflight(repo_with_worktrees, tmp_path):
    R = repo_with_worktrees
    out = tmp_path / "batch.sh"
    _audit("--repo", str(R["main"]), "--emit-batch", "--min-age-days", "0",
           "--out", str(out))
    text = out.read_text()
    assert "branch deletion candidates" in text
    # feat is ahead of dev -> preflight NO; the delete line stays commented.
    assert "ancestor of origin/dev = NO" in text
    assert "# git branch -d feat" in text
    # no ACTIVE branch delete line (all commented)
    assert "\ngit branch -d" not in text


def test_batch_min_age_filters_out_new_worktrees(repo_with_worktrees, tmp_path):
    R = repo_with_worktrees
    out = tmp_path / "batch.sh"
    # worktrees are seconds old; a 5-day floor excludes them.
    _audit("--repo", str(R["main"]), "--emit-batch", "--min-age-days", "5",
           "--out", str(out))
    text = out.read_text()
    assert "(none:" in text
    assert "git worktree remove" not in text.split("branch deletion")[0].replace(
        "# `git worktree remove`", "")


def test_batch_never_removes_independent_repo(repo_with_worktrees, tmp_path):
    R = repo_with_worktrees
    out = tmp_path / "batch.sh"
    _audit("--repo", str(R["main"]), "--extra", str(R["tmp"]),
           "--emit-batch", "--min-age-days", "0", "--out", str(out))
    text = out.read_text()
    assert str(R["indep"]) not in text
