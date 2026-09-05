"""Regression tests compile real Lean declarations, including hidden assumptions."""
import contextlib
import io
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import acceptance

FIXTURE = r'''
import Mathlib.Data.Nat.Basic
namespace AuditFixture
theorem closed (d : Nat) (_hd : 3 ≤ d) : d = d := rfl
theorem noBinders : True := True.intro
theorem hiddenInstance (d : Nat) [Fact False] (_hd : 3 ≤ d) : False := Fact.out
theorem hiddenImplicit (d : Nat) {h : False} (_hd : 3 ≤ d) : False := h
theorem hiddenExplicit (d : Nat) (h : False) (_hd : 3 ≤ d) : False := h
theorem hiddenLast (d : Nat) (_hd : 3 ≤ d) [Fact False] : False := Fact.out
theorem conditionalNeZero {d : Nat} [NeZero d] (_hd : 3 ≤ d) : d = d := rfl
structure Certificate where
  impossible : False
theorem hiddenData (d : Nat) (c : Certificate) (_hd : 3 ≤ d) : False := c.impossible
def Concealed : Prop := False → False
theorem hiddenInAlias : Concealed := fun h => h
theorem impossibleDimension (d : Nat) (hd : d < 0) : False := Nat.not_lt_zero d hd
axiom extraAxiom : False
theorem extra : False := extraAxiom
end AuditFixture
'''


class AcceptanceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        names = ["closed", "noBinders", "hiddenInstance", "hiddenImplicit", "hiddenExplicit",
                 "hiddenLast", "conditionalNeZero", "hiddenData", "hiddenInAlias",
                 "impossibleDimension", "extra"]
        queries = ["AuditFixture." + name for name in names]
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "Fixture.lean"
            path.write_text(FIXTURE + acceptance.LEAN_AUDIT + "\n"
                            + "".join("#acceptance_audit %s\n" % q for q in queries))
            result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise AssertionError("Lean fixture did not compile:\n" + result.stdout)
        records = acceptance.records_from_output(result.stdout, queries)
        cls.records = dict(zip(names, records))

    def verdict(self, *names):
        with contextlib.redirect_stdout(io.StringIO()):
            return acceptance.verdict([self.records[name] for name in names])

    def test_cli_compiles_and_cleans_up(self):
        before = set(ROOT.glob("Acceptance_*.lean"))
        with contextlib.redirect_stdout(io.StringIO()):
            result = acceptance.audit(ROOT, ["Mathlib.Data.Nat.Basic:Nat.zero_le"])
        self.assertEqual(result, 0)
        self.assertEqual(set(ROOT.glob("Acceptance_*.lean")), before)

    def test_closed_theorems_pass(self):
        self.assertEqual(self.verdict("closed", "noBinders"), 0)

    def test_hidden_assumptions_are_rejected(self):
        for name in ["hiddenInstance", "hiddenImplicit", "hiddenExplicit", "hiddenLast",
                     "conditionalNeZero", "hiddenData", "hiddenInAlias", "impossibleDimension"]:
            with self.subTest(name=name):
                self.assertEqual(self.verdict(name), 1)

    def test_extra_axiom_is_rejected(self):
        self.assertEqual(self.verdict("extra"), 1)

    def test_mixed_batch_is_rejected(self):
        self.assertEqual(self.verdict("closed", "hiddenInstance"), 1)

    def test_missing_or_duplicate_reports_are_rejected(self):
        with self.assertRaises(ValueError):
            acceptance.records_from_output("", ["AuditFixture.closed"])
        with self.assertRaises(ValueError):
            acceptance.verdict([])
        line = 'ACCEPTANCE_JSON:{"query":"AuditFixture.closed"}\n'
        with self.assertRaises(ValueError):
            acceptance.records_from_output(line + line, ["AuditFixture.closed"])


if __name__ == "__main__":
    unittest.main()
