"""Regression tests for installations that expose only the native Rocq CLI."""
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.bin = Path(self.tmp.name)

    def binary(self, name):
        path = self.bin / (name + (".exe" if os.name == "nt" else ""))
        path.touch()
        return str(path)

    def discover(self, available, **overrides):
        with patch.object(check.shutil, "which", side_effect=lambda name: available.get(name)):
            return check.toolchain(**overrides)

    def test_native_only_installation(self):
        rocq = self.binary("rocq")
        self.assertEqual(self.discover({"rocq": rocq}),
                         ([rocq, "compile"], [rocq, "check"]))

    def test_native_is_preferred_when_aliases_exist(self):
        rocq, coqc = self.binary("rocq"), self.binary("coqc")
        self.binary("coqchk")
        self.assertEqual(self.discover({"rocq": rocq, "coqc": coqc}),
                         ([rocq, "compile"], [rocq, "check"]))

    def test_legacy_only_installation(self):
        coqc, checker = self.binary("coqc"), self.binary("coqchk")
        self.assertEqual(self.discover({"coqc": coqc}), ([coqc], [checker]))

    def test_explicit_legacy_override(self):
        rocq, coqc = self.binary("rocq"), self.binary("coqc")
        checker = self.binary("coqchk")
        self.assertEqual(self.discover({"rocq": rocq}, coqc=coqc), ([coqc], [checker]))

    def test_explicit_native_path_without_path_discovery(self):
        rocq = self.binary("rocq")
        self.assertEqual(self.discover({}, rocq=rocq), ([rocq, "compile"], [rocq, "check"]))

    def test_explicit_checker_override(self):
        rocq, checker = self.binary("rocq"), self.binary("custom-checker")
        self.assertEqual(self.discover({"rocq": rocq}, coqchk=checker),
                         ([rocq, "compile"], [checker]))

    def test_no_compiler_fails(self):
        with self.assertRaisesRegex(RuntimeError, "coqc not found"):
            self.discover({})

    def test_conflicting_overrides_fail(self):
        with self.assertRaisesRegex(RuntimeError, "Choose either"):
            self.discover({}, coqc="coqc", rocq="rocq")


if __name__ == "__main__":
    unittest.main()
