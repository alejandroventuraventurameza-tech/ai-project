"""Synthetic 34-dimensional regression tests (not economic-source evidence)."""
import unittest
from audit_augmented_34 import audit

N = 33
ROW_MAP = [0, 3, 1, 4, 2, 5, *range(6, 17), 17, 19, 18, 20, *range(21, 33)]


def toy34():
    j = [[["1", "1"] if i == k else ["0", "0"] for k in range(N)] for i in range(N)]
    fy = [[["0", "0"] for _ in range(5)] for _ in range(N)]
    fy[5][0] = ["-1", "-1"]
    fy[5][1] = ["-2", "-2"]
    m = [["-1", "-1"] if i == 5 else ["0", "0"] for i in range(N)]
    flags = {x: False for x in (
        "source_Lean_semantic_identity_proved",
        "uniform_box_contains_Lean_actual_derivatives_proved",
        "exact_zero_center_proved", "formal_Lean_IFT_witness_established")}
    return dict(schema="ie-quantitative-ift-v1",
        metadata=dict(source_commit="SYNTHETIC-TEST-NOT-ECONOMIC", **flags),
        dimension=N, parameter_dimension=5, center=["0"] * N,
        radius="1e-8", parameter_radius="1e-10",
        preconditioner=[["1" if i == k else "0" for k in range(N)] for i in range(N)],
        jacobian_ball=j, fy_ball=fy,
        f_center=[["0", "0"] for _ in range(N)],
        funding_dual_center_box=["0", "0"],
        funding_dual_state_gradient_ball=m,
        funding_dual_direct_parameter_derivatives_ball=[["0", "0"] for _ in range(4)],
        rows_recomputed_as_source_style=[4, 5, 21],
        source_to_legacy_row_permutation=ROW_MAP, **flags)


class Augmented34Tests(unittest.TestCase):
    def test_exact_synthetic_inverse(self):
        p = audit(toy34())
        self.assertTrue(p["contractive_uniform_ball_arithmetic_gate_pass"])
        self.assertEqual(p["weighted_defect_bound_q"], "0")
        self.assertEqual(p["weighted_center_residual_eta"], "0")
        self.assertEqual(p["nominal_schur_rational_not_an_enclosure"], "-2")
        self.assertFalse(p["formal_Lean_IFT_witness_established"])

    def test_small_baseline_dual_creates_policy_shift(self):
        d = toy34()
        d["funding_dual_center_box"] = ["1e-20", "1e-20"]
        p = audit(d)
        self.assertTrue(p["contractive_uniform_ball_arithmetic_gate_pass"])
        self.assertNotEqual(p["weighted_center_residual_eta"], "0")
        self.assertFalse(p["exact_zero_center_proved"])

    def test_wrong_direct_mu_derivative(self):
        d = toy34()
        d["funding_dual_direct_parameter_derivatives_ball"][0] = ["1", "1"]
        with self.assertRaises(ValueError):
            audit(d)

    def test_wrong_row_order(self):
        d = toy34()
        d["source_to_legacy_row_permutation"] = list(range(N))
        with self.assertRaises(ValueError):
            audit(d)

    def test_missing_dual_center(self):
        d = toy34()
        del d["funding_dual_center_box"]
        with self.assertRaises(KeyError):
            audit(d)

    def test_unjustified_provenance_flag(self):
        d = toy34()
        d["formal_Lean_IFT_witness_established"] = True
        with self.assertRaises(ValueError):
            audit(d)

    def test_binary_float_rejected(self):
        d = toy34()
        d["parameter_radius"] = 1e-10
        with self.assertRaises(TypeError):
            audit(d)

    def test_noncontractive_reference_rejected(self):
        d = toy34()
        d["funding_dual_center_box"] = ["1", "1"]
        p = audit(d)
        self.assertFalse(p["contractive_uniform_ball_arithmetic_gate_pass"])

    def test_wrong_policy_column(self):
        d = toy34()
        d["fy_ball"][5][0] = ["1", "1"]
        with self.assertRaises(ValueError):
            audit(d)

    def test_wide_derivative_box_fails_gate(self):
        d = toy34()
        d["jacobian_ball"][0][0] = ["0", "2.5"]
        p = audit(d)
        self.assertFalse(p["contractive_uniform_ball_arithmetic_gate_pass"])


if __name__ == "__main__":
    unittest.main()
