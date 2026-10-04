#!/usr/bin/env python3
"""Local metadata checks against the pinned schema and explicit policy rules.

Install PyYAML==6.0.3 and jsonschema==4.26.0 into an isolated environment.
This checks metadata shape, not human authorship, licensing ownership, Lean,
Comparator, NanoDa, or admission to Palomar. --strict rejects draft markers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

import jsonschema
import yaml


class UniqueKeyLoader(yaml.SafeLoader):
    pass


def construct_mapping(loader, node, deep=False):
    result = {}
    for key_node, value_node in node.value:
        if key_node.value == "<<":
            raise ValueError("YAML merge keys are not permitted")
        key = loader.construct_object(key_node, deep=deep)
        if key in result:
            raise ValueError(f"duplicate YAML mapping key: {key!r}")
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


UniqueKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, construct_mapping
)


def check(metadata_path: Path, policy_dir: Path, strict: bool) -> dict:
    pins = json.loads((policy_dir / "source-pins.json").read_text())
    for name, source in pins["files"].items():
        digest = hashlib.sha256((policy_dir / name).read_bytes()).hexdigest()
        if digest != source["sha256"]:
            raise ValueError(f"pinned metadata resource digest mismatch: {name}")
    raw = metadata_path.read_bytes()
    if len(raw) > 256 * 1024:
        raise ValueError("formalization.yaml exceeds 256 KiB")
    metadata = yaml.load(raw.decode("utf-8"), Loader=UniqueKeyLoader)
    schema = json.loads((policy_dir / "v0.4.schema.json").read_text())
    jsonschema.Draft7Validator(schema).validate(metadata)
    project = metadata["project"]
    assert 0 < len(project["name"]) <= 300
    assert 0 < len(project["description"]) <= 10000
    assert project["authors"]
    assert project["responsible_maintainers"]
    assert all(isinstance(s, str) and s.strip() for s in project["authors"])
    assert all(isinstance(s, str) and s.strip()
               for s in project["responsible_maintainers"])
    for field, filename, minimum, maximum in [
        ("arxiv", "arxiv-categories.json", 1, 8),
        ("msc2020", "msc2020-codes.json", 0, 8),
    ]:
        codes = metadata["classification"].get(field, [])
        assert minimum <= len(codes) <= maximum
        assert len(codes) == len(set(codes))
        taxonomy = json.loads((policy_dir / filename).read_text())
        assert all(code in taxonomy for code in codes), (field, codes)
    sources = metadata["sources"]
    permitted_types = {"paper", "book", "web discussion", "folklore",
                       "original-proof", "other"}
    permitted_relationships = {"formalizes", "adapts", "independently-proves",
                               "background", "other"}
    for source in sources:
        assert source["title"].strip()
        assert source["relationship"] in permitted_relationships
        assert "type" not in source or source["type"] in permitted_types
    original = any(s.get("type") == "original-proof" for s in sources)
    if original:
        assert all(s["relationship"] in {"background", "other"}
                   for s in sources)
        assert all(s["relationship"] == "other" for s in sources
                   if s.get("type") == "original-proof")
    else:
        assert any(s["relationship"] in
                   {"formalizes", "adapts", "independently-proves"}
                   for s in sources)
    draft_lines = [i for i, line in enumerate(raw.decode().splitlines(), 1)
                   if re.search(r"PENDING|TEMPLATE", line)]
    report = {
        "metadata": str(metadata_path),
        "schema_validation": "passed",
        "pinned_resource_hashes": "passed",
        "checked_palomar_policy_shape": "passed",
        "derived_origin": "original" if original else "source-based",
        "draft_marker_lines": draft_lines,
        "release_ready": False if draft_lines else "not determined by this check",
        "not_checked": ["actual human identity or authorization",
                        "copyright ownership or license detection",
                        "Lean build and theorem axioms", "Comparator and NanoDa",
                        "full Palomar mechanical verification", "editorial review"],
    }
    print(json.dumps(report, indent=2))
    if strict and draft_lines:
        raise SystemExit(1)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("metadata", nargs="?", type=Path,
                        default=Path(__file__).resolve().parents[2] /
                        "formalization.yaml")
    parser.add_argument("--policy-dir", type=Path,
                        default=Path(__file__).resolve().parent / "policy")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    check(args.metadata, args.policy_dir, args.strict)
