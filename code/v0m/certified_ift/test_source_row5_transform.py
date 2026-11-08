"""Synthetic exact-rational tests of row-five pointwise sign conversion."""
import unittest
from test_quantitative_ift import toy
from check_quantitative_ift import inspect_certificate
from source_row5_transform import (
    FACE_ROW, flip_binding_face_row_at_frontier,
    source_slack_direct_parameter_column,
)


class SourceRow5TransformTests(unittest.TestCase):
    def test_pointwise_defect_is_unchanged(self):
        old = toy()
        q_old = inspect_certificate(old)["defect_bound_q"]
        Jnew, Rnew = flip_binding_face_row_at_frontier(
            old["jacobian_ball"], old["preconditioner"])
        transformed = dict(old, jacobian_ball=Jnew, preconditioner=Rnew)
        self.assertEqual(inspect_certificate(transformed)["defect_bound_q"], q_old)
        self.assertEqual(Jnew[FACE_ROW][FACE_ROW], ["-10001/10000", "-9999/10000"])
        self.assertEqual(Rnew[FACE_ROW][FACE_ROW], "-1")

    def test_other_rows_and_direct_slack_column(self):
        d = toy()
        J, R = flip_binding_face_row_at_frontier(
            d["jacobian_ball"], d["preconditioner"])
        self.assertEqual(J[0][0], ["9999/10000", "10001/10000"])
        self.assertEqual(R[0][0], "1")
        direct = source_slack_direct_parameter_column()
        self.assertEqual(len(direct), 33)
        self.assertEqual(direct.count("-1"), 1)
        self.assertEqual(direct[5], "-1")


if __name__ == "__main__":
    unittest.main()
