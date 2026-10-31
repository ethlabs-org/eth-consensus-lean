#!/usr/bin/env python3
"""Publication contract fixtures with a local Git-object API, no network or credentials."""
import base64
import copy
import hashlib
import json
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest.mock import patch

M = runpy.run_path(str(Path(__file__).with_name("publish-inventory.py")))
A, B, C = (c * 40 for c in "abc")
INVENTORY = {"schema_version": 1, "mode": "report-only", "status": "incomplete",
             "issues": ["missing root"], "roots": [], "sorries": [{"declaration": "debt", "ancestors": []}]}


class GitAPI:
    def __init__(self):
        self.objects = {}
        self.head = None
        self.fail_write = False
        self.main = A
        self.advance_main = None

    def store(self, data):
        sha = hashlib.sha1(M["encoded"](data)).hexdigest()
        self.objects[sha] = copy.deepcopy(data)
        return {"sha": sha}

    def request(self, slug, path, data=None, missing=False, method="POST"):
        if path == "git/ref/heads/main":
            return {"object": {"sha": self.main}}
        if path == "git/ref/heads/ci-inventory":
            return {"object": {"sha": self.head}} if self.head else None
        if path.startswith("git/commits/"):
            return self.objects[path.split("/")[-1]]
        if path.startswith("git/trees/"):
            files = self.objects[path.split("/")[-1].split("?")[0]]
            return {"tree": [{"path": p, "sha": s, "type": "blob"} for p, s in files.items()]}
        if path.startswith("git/blobs/"):
            return self.objects[path.split("/")[-1]]
        if path == "git/blobs":
            return self.store(data)
        if path == "git/trees":
            files = dict(self.objects.get(data.get("base_tree"), {}))
            files.update({entry["path"]: entry["sha"] for entry in data["tree"]})
            return self.store(files)
        if path == "git/commits":
            if self.advance_main:
                self.main = self.advance_main
                self.advance_main = None
            return self.store({**data, "tree": {"sha": data["tree"]}})
        if path in ("git/refs", "git/refs/heads/ci-inventory"):
            if self.fail_write:
                raise RuntimeError("simulated API outage/racing update")
            parents = self.objects[data["sha"]]["parents"]
            assert parents == ([self.head] if self.head else [])
            if self.head:
                assert method == "PATCH" and data["force"] is False
            self.head = data["sha"]
            return {}
        raise AssertionError(path)

    def read(self, path):
        files = self.objects[self.objects[self.head]["tree"]["sha"]]
        return json.loads(base64.b64decode(self.objects[files[path]]["content"]))


class Publication(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.home = Path(self.tmp.name)
        self.run = self.home / "job"
        (self.run / "check.fresh").mkdir(parents=True)
        self.api = GitAPI()

    def capture(self, sha=A, kind="main", date="2026-10-31T01:00:00Z", inventory=INVENTORY):
        file = self.run / "check.fresh/sorry-inventory.json"
        if inventory is not None:
            file.write_text(json.dumps(inventory))
        elif file.exists():
            file.unlink()
        path = M["capture"](self.home, sha, kind, self.run, date, "passed")
        return json.loads(path.read_text())

    def publish(self, item):
        M["publish"]("fixture/repo", item, self.api.request)

    def test_incomplete_retained_and_discovery_integrity(self):
        self.publish(self.capture())
        payload = self.api.read(f"commits/{A}.json")
        latest = self.api.read("latest.json")
        self.assertEqual(payload["inventory"], INVENTORY)
        self.assertEqual(payload["availability"], "available")
        self.assertEqual(latest["commit"], A)
        self.assertEqual(latest["inventory_status"], "incomplete")
        self.assertEqual(latest["payload_sha256"], hashlib.sha256(M["encoded"](payload)).hexdigest())
        self.assertEqual(json.loads(base64.b64decode(self.api.objects[latest["payload_api"].split("/")[-1]]["content"])), payload)

    def test_missing_is_immutable_unavailable_not_zero_sorry(self):
        self.publish(self.capture(inventory=None))
        initial = self.api.read(f"commits/{A}.json")
        self.assertIsNone(initial["inventory"])
        self.assertEqual(initial["availability"], "unavailable")
        # Even a recovered later capture cannot overwrite the first local/remote record.
        recovered = self.capture()
        self.assertEqual(recovered["report"], initial)
        recovered["report"].update(availability="available", inventory=INVENTORY)
        self.publish(recovered)
        self.assertEqual(self.api.read(f"commits/{A}.json"), initial)

    def test_latest_never_regresses_on_recheck_or_retry(self):
        self.api.main = B
        newer = self.capture(B, date="2026-10-31T02:00:00Z")
        self.publish(newer)
        self.publish(self.capture(A))
        self.publish(self.capture(C, kind="main-recheck", date="2026-10-31T03:00:00Z"))
        self.assertEqual(self.api.read("latest.json")["commit"], B)
        self.assertEqual(self.api.read(f"commits/{C}.json")["commit"], C)

    def test_pending_recheck_promotes_main_eligibility_without_replacing_report(self):
        self.publish(self.capture())
        self.api.main = B
        first = self.capture(B, kind="main-recheck", date="2026-10-31T02:00:00Z", inventory=None)
        self.api.fail_write = True
        with self.assertRaises(RuntimeError):
            self.publish(first)
        promoted = self.capture(B, date="2026-10-31T03:00:00Z")
        self.assertEqual(promoted["kind"], "main")
        self.assertEqual(promoted["report"], first["report"])
        self.api.fail_write = False
        self.publish(promoted)
        self.assertEqual(self.api.read("latest.json")["commit"], B)
        self.assertEqual(self.api.read(f"commits/{B}.json"), first["report"])

    def test_failed_atomic_write_preserves_latest_and_outbox_then_retries(self):
        self.publish(self.capture())
        self.api.main = B
        self.capture(B, date="2026-10-31T02:00:00Z")
        self.api.fail_write = True
        publish = lambda slug, item: M["publish"](slug, item, self.api.request)
        with patch.dict(M["flush"].__globals__, publish=publish):
            self.assertEqual(M["flush"](self.home, "fixture/repo"), 1)
            self.assertEqual(self.api.read("latest.json")["commit"], A)
            self.assertTrue((self.home / f"inventory-outbox/{B}.json").exists())
            self.api.fail_write = False
            self.assertEqual(M["flush"](self.home, "fixture/repo"), 0)
        self.assertEqual(self.api.read("latest.json")["commit"], B)
        self.assertFalse(list((self.home / "inventory-outbox").glob("*.json")))

    def test_current_recheck_advances_existing_immutable_report(self):
        self.publish(self.capture())
        item = self.capture(B, kind="main-recheck", date="2026-10-30T01:00:00Z", inventory=None)
        self.publish(item)  # historical initially: record only
        original = self.api.read(f"commits/{B}.json")
        self.assertEqual(self.api.read("latest.json")["commit"], A)
        self.api.main = B
        self.publish(item)
        self.assertEqual(self.api.read("latest.json")["commit"], B)
        self.assertEqual(self.api.read("latest.json")["availability"], "unavailable")
        self.assertEqual(self.api.read(f"commits/{B}.json"), original)

    def test_main_advances_during_publish_and_retry_rechecks_eligibility(self):
        self.publish(self.capture())
        item = self.capture(B, kind="main-recheck")
        self.api.main = B
        self.api.advance_main = C
        with self.assertRaisesRegex(RuntimeError, "main advanced"):
            self.publish(item)
        self.assertEqual(self.api.read("latest.json")["commit"], A)
        self.publish(self.capture(C))
        self.publish(item)
        self.assertEqual(self.api.read("latest.json")["commit"], C)

    def test_data_cas_failure_retry_cannot_regress_new_main(self):
        self.publish(self.capture())
        item = self.capture(B, kind="main-recheck")
        self.api.main = B
        self.api.fail_write = True
        with self.assertRaises(RuntimeError):
            self.publish(item)
        self.api.fail_write = False
        self.api.main = C
        self.publish(self.capture(C))
        self.publish(item)
        self.assertEqual(self.api.read("latest.json")["commit"], C)
        self.assertEqual(self.api.read(f"commits/{B}.json")["commit"], B)

    def test_invalid_oversize_ambiguous_and_unrelated_old_reports(self):
        old = self.home / "old/check.stale"
        old.mkdir(parents=True)
        (old / "sorry-inventory.json").write_text(json.dumps(INVENTORY))
        self.assertIsNone(self.capture(A, inventory=None)["report"]["inventory"])
        self.assertEqual(self.capture(B, inventory={})["report"]["availability"], "unavailable")
        with patch.dict(M["capture"].__globals__, MAX_BYTES=10):
            report = self.capture(C)["report"]
            self.assertIn("exceeds", report["reason"])
            self.assertIsNone(report["inventory"])
        (self.run / "check.second").mkdir()
        (self.run / "check.second/sorry-inventory.json").write_text(json.dumps(INVENTORY))
        self.assertIn("ambiguous", self.capture("d" * 40)["report"]["reason"])


if __name__ == "__main__":
    unittest.main()
