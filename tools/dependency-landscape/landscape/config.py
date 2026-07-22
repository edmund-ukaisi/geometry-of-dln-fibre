"""Expedition profile: everything expedition-specific lives in a JSON profile
(area/role classification rules, goal candidates, milestone tag rules), so the
generator and viewers stay expedition-agnostic."""
from __future__ import annotations

import json
import re
from pathlib import Path


class Profile:
    def __init__(self, data: dict):
        self.data = data
        self.name = data["name"]
        self.title = data.get("title", self.name)
        self.lean_root = data.get("leanRoot", "lean")
        self.project_prefix = data.get("projectPrefix", "")
        self.bucket_hours = int(data.get("bucketHours", 1))
        self.goal_candidates = data["goalCandidates"]
        self.goal_label = data.get("goalLabel", "goal cone")

        self.areas = [a["label"] for a in data["areas"]]
        self.area_short = [a.get("short", a["label"]) for a in data["areas"]]
        self.area_colors = [a["color"] for a in data["areas"]]
        self._area_res = [
            [re.compile(p) for p in a.get("match", [])] for a in data["areas"]
        ]
        self.area_order = data.get("areaOrder", list(range(len(self.areas))))

        self.roles = [r["label"] for r in data["roles"]]
        self.role_short = [r.get("short", r["label"]) for r in data["roles"]]
        self.role_colors = [r["color"] for r in data["roles"]]
        self._role_res = [
            [re.compile(p, re.I) for p in r.get("match", [])] for r in data["roles"]
        ]
        self.role_order = data.get("roleOrder", list(range(len(self.roles))))

        self._tags = [
            (t["label"],
             re.compile(t["match"], 0 if t.get("caseSensitive") else re.I))
            for t in data.get("tags", [])
        ]
        self._area_cache = {}

    @classmethod
    def load(cls, path: str | Path) -> "Profile":
        return cls(json.loads(Path(path).read_text()))

    def area_index(self, module: str) -> int:
        hit = self._area_cache.get(module)
        if hit is None:
            hit = len(self.areas) - 1
            for i, patterns in enumerate(self._area_res):
                if any(p.search(module) for p in patterns):
                    hit = i
                    break
            self._area_cache[module] = hit
        return hit

    def role_index(self, name: str, module: str) -> int:
        subject = f"{module} {name}"
        for i, patterns in enumerate(self._role_res):
            if any(p.search(subject) for p in patterns):
                return i
        return len(self.roles) - 1

    def tag_labels(self, subjects: list) -> list:
        text = "\n".join(subjects)
        return [label for label, pattern in self._tags if pattern.search(text)]

    def lane_meta(self) -> dict:
        return {
            "areas": self.areas, "areaShort": self.area_short,
            "areaColors": self.area_colors, "areaOrder": self.area_order,
            "roles": self.roles, "roleShort": self.role_short,
            "roleColors": self.role_colors, "roleOrder": self.role_order,
        }
