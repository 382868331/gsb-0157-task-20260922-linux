"""补充测试：结果 JSON 可序列化与端点往返一致（仅补充，不作为正确性依据）。

正确性依据是符号包含性证书（test_checker.py）与独立具体执行对照
（test_analyzer.py）；这里只验证输出协议的序列化稳定性。
"""

import json
import unittest

from interval_ai import analyze
from interval_ai.interval import Interval

from tests.programs import (
    infinite_growth_program,
    nested_loop_program,
    two_back_edges_program,
)


class TestJsonRoundTrip(unittest.TestCase):
    def test_result_is_json_serializable_with_infinite_nulls(self):
        for make in (
            nested_loop_program,
            infinite_growth_program,
            two_back_edges_program,
        ):
            with self.subTest(prog=make.__name__):
                res = analyze(make())
                blob = json.dumps(res.to_dict(), ensure_ascii=False)
                decoded = json.loads(blob)
                # 往返：块数、断言状态、无穷端点(null) 不丢失
                self.assertEqual(len(decoded["blocks"]), len(make().blocks))
                got = {a["assert_id"]: a["status"] for a in decoded["assertions"]}
                expect = {a.assert_id: a.status for a in res.assertions}
                self.assertEqual(got, expect)

    def test_interval_dict_round_trip(self):
        for iv in (Interval(0, 1), Interval(None, 5), Interval(-3, None),
                   Interval.top(), Interval(10**80, 10**80 + 1)):
            d = iv.to_dict()
            rebuilt = Interval(d["lo"], d["hi"])
            self.assertEqual(rebuilt, iv)
            json.dumps(d)  # 不抛异常即可


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
