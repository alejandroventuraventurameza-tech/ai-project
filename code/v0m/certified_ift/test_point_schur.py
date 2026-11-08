"""Synthetic checks of the exact point Schur interval error budget."""
import unittest
from test_quantitative_ift import toy
from audit_point_schur import audit


def synthetic_source_point():
    d=toy()
    d["schema"]="ventura-source-point-jacobian-CANDIDATE-v1"
    d["rows_recomputed_as_source_style"]=[4,5,21]
    d["source_to_legacy_row_permutation"]=[
        0,3,1,4,2,5,*range(6,17),17,19,18,20,*range(21,33)]
    d["point_inverse_gate_pass"]=True
    d["point_preconditioned_defect_upper"]="1/10000"
    d["point_policy_derivative_box"]=[
        [["0","0"] for j in range(5)] for i in range(33)]
    d["point_policy_derivative_box"][5][0]=["-1","-1"]
    d["point_policy_derivative_box"][5][1]=["-2","-2"]
    d["funding_dual_state_gradient_box"]=[
        ["-1","-1"] if i==5 else ["0","0"] for i in range(33)]
    d["funding_dual_direct_parameter_derivatives"]=[["0","0"] for j in range(4)]
    d.update(uniform_ball_jacobian_enclosures_proven=False,
        exact_zero_center_proven=False,
        economic_source_row_map_proven=False,
        formal_Lean_witness_established=False)
    return d


class PointSchurAuditTests(unittest.TestCase):
    def test_strict_negative_source_point_signs(self):
        data=synthetic_source_point()
        audit_data=audit(data)
        x=audit_data["policy_derivative_enclosures"]
        self.assertTrue(x[0]["strict_negative_given_semantic_inputs"])
        self.assertTrue(x[1]["strict_negative_given_semantic_inputs"])
        self.assertFalse(audit_data["full_Lean_source_row_identity_proved"])
        self.assertFalse(audit_data["uniform_nonlinear_IFT_box_proved"])

    def test_positive_rate_derivative_not_mislabelled(self):
        d=synthetic_source_point()
        d["point_policy_derivative_box"][5][1]=["2","2"]
        a=audit(d)
        self.assertFalse(a["policy_derivative_enclosures"][1]["strict_negative_given_semantic_inputs"])
        self.assertTrue(a["policy_derivative_enclosures"][1]["strict_positive_given_semantic_inputs"])

    def test_nonzero_direct_marginal_derivative_rejected(self):
        d=synthetic_source_point()
        d["funding_dual_direct_parameter_derivatives"][0]=["1","1"]
        with self.assertRaises(ValueError):
            audit(d)


if __name__=="__main__":
    unittest.main()
