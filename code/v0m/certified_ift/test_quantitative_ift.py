"""Synthetic-only regression tests. No economic calibration data is used."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from check_quantitative_ift import inspect_certificate

N = 33


def toy():
    return {
        "schema": "ie-quantitative-ift-v1",
        "metadata": {"source_commit": "SYNTHETIC-NOT-AN-ECONOMIC-REVISION",
                     "enclosure_provenance": "exactly specified toy map"},
        "dimension": N,
        "center": ["0"] * N,
        "radius": "0.000001",
        "preconditioner": [["1" if i == j else "0" for j in range(N)]
                           for i in range(N)],
        "f_center": [["0", "0"] for _ in range(N)],
        "jacobian_ball": [[["0.9999", "1.0001"] if i == j else ["0", "0"]
                           for j in range(N)] for i in range(N)],
    }


class QuantitativeIFTTests(unittest.TestCase):
    def test_base_ball(self):
        d = toy()
        a = inspect_certificate(d)
        self.assertTrue(a["base_ball_gate_pass"])
        self.assertEqual(a["defect_bound_q"], "1/10000")
        self.assertTrue(a["normalized_zero_reference_condition"])
        self.assertFalse(a["verified_economic_source_enclosures"])
        self.assertFalse(a["formal_Lean_witness_established"])

    def test_five_parameters(self):
        d = toy()
        d["parameter_radius"] = "1e-8"
        d["parameter_dimension"] = 5
        d["fy_ball"] = [[["0.01", "0.01"] if i == 0 and j == 0 else ["0", "0"]
                         for j in range(5)] for i in range(N)]
        a = inspect_certificate(d)
        self.assertTrue(a["uniform_family_gate_pass"])
        self.assertEqual(a["conditional_inverse_norm_bound"], "10000/9999")
        self.assertEqual(a["requested_domain"], "five_parameter_family")

    def test_failing_family_fails_cli(self):
        d = toy()
        d["parameter_radius"] = "1"
        d["parameter_dimension"] = 5
        d["fy_ball"] = [[["0.01", "0.01"] if i == 0 and j == 0 else ["0", "0"]
                         for j in range(5)] for i in range(N)]
        a = inspect_certificate(d)
        self.assertTrue(a["base_ball_gate_pass"])
        self.assertFalse(a["requested_domain_arithmetic_gate_pass"])
        with tempfile.TemporaryDirectory() as directory:
            inp, out = Path(directory)/"data.json", Path(directory)/"audit.json"
            inp.write_text(json.dumps(d), encoding="utf-8")
            p = subprocess.run([sys.executable,
                str(Path(__file__).with_name("check_quantitative_ift.py")),
                "--certificate", str(inp), "--output", str(out)],
                capture_output=True, text=True, check=False)
            self.assertEqual(p.returncode, 2, p.stderr)
            self.assertEqual(len(json.loads(out.read_text())["certificate_sha256"]), 64)

    def test_reject_reversed_interval(self):
        d = toy()
        d["f_center"][0] = ["1", "0"]
        with self.assertRaises(ValueError):
            inspect_certificate(d)

    def test_reject_binary_float(self):
        d = toy()
        d["radius"] = 0.000001
        with self.assertRaises(TypeError):
            inspect_certificate(d)

    def test_nonzero_center_is_not_source_normalization(self):
        d = toy()
        d["center"][0] = "1"
        a = inspect_certificate(d)
        self.assertFalse(a["normalized_zero_reference_condition"])

    def test_disallow_missing_five_parameter_boxes(self):
        d = toy()
        d["parameter_radius"] = "0.00001"
        with self.assertRaises(ValueError):
            inspect_certificate(d)


if __name__ == "__main__":
    unittest.main()
