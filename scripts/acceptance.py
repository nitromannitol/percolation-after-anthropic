#!/usr/bin/env python3
"""Audit a canonical dimension-parametrized theorem using Lean's elaborated type.

Usage: python3 acceptance.py PROJECT Module:Namespace.declaration [...]
PROJECT can be a Lake project or the legacy workspace with build/percolation/KN
and knc.sh. All binders (including implicit and instance binders) are inspected
by Lean. Only Nat parameters and literal lower bounds on them are allowed.
This checks assumptions and axioms, not whether a conclusion encodes the intended
mathematical statement. The complete type is also printed for that review.
"""
import argparse
import json
import pathlib
import re
import subprocess
import tempfile


LEAN_AUDIT = r'''
open Lean Meta Elab Command in
private def acceptanceNumericBound (type : Expr) (params : Array Expr) : MetaM Bool := do
  let type ← whnf type
  let args := type.getAppArgs
  if type.getAppFn.isConstOf ``Nat.le && args.size == 2 then
    return (← getNatValue? args[0]!).isSome && params.contains args[1]!
  return false

open Lean Meta Elab Command in
elab "#acceptance_audit " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo name
  unless info.isTheorem do
    throwError "Acceptance requires a theorem declaration: {name}"
  let axioms ← collectAxioms name
  let record ← liftTermElabM <| forallTelescopeReducing info.type fun xs _ => do
    let mut params : Array Expr := #[]
    let mut binders : Array Json := #[]
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      let type := localDecl.type
      let category ← if ← isDefEq type (mkConst ``Nat) then
          pure "nat_parameter"
        else if ← acceptanceNumericBound type params then
          pure "numeric_side_condition"
        else pure "assumption"
      if category == "nat_parameter" then params := params.push x
      binders := binders.push <| Json.mkObj [
        ("name", toJson localDecl.userName.toString),
        ("type", toJson (toString (← ppExpr type))),
        ("category", toJson category),
        ("instance", toJson localDecl.binderInfo.isInstImplicit)]
    return Json.mkObj [
      ("query", toJson id.getId.toString),
      ("name", toJson name.toString),
      ("type", toJson (toString (← ppExpr info.type))),
      ("binders", Json.arr binders),
      ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.println ("ACCEPTANCE_JSON:" ++ record.compress)
'''

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def candidates(source_root, module, name):
    """Resolve short CLI names from source namespaces; never infer closedness here."""
    path = (source_root / pathlib.Path(*module.split("."))).with_suffix(".lean")
    result = [name]
    if path.exists():
        namespaces = []
        for kind, part in re.findall(r"^(namespace|end)\s+(\S+)", path.read_text(), re.M):
            if kind == "namespace":
                namespaces.append(part)
                candidate = ".".join(namespaces) + "." + name
                if candidate not in result:
                    result.append(candidate)
            elif namespaces and namespaces[-1] == part:
                namespaces.pop()
    return result[:1] + sorted(result[1:], key=len, reverse=True)


def records_from_output(output, queries):
    prefix = "ACCEPTANCE_JSON:"
    records = [json.loads(line[len(prefix):])
               for line in output.splitlines() if line.startswith(prefix)]
    if [r.get("query") for r in records] != queries:
        raise ValueError("Missing, duplicate, or unexpected Lean audit records")
    return records


def verdict(records):
    """Fail closed: every theorem needs a structured binder and axiom report."""
    if not records:
        raise ValueError("No theorem was audited")
    closed = True
    for record in records:
        print(record["name"] + " : " + record["type"])
        print("  axioms: " + ", ".join(record["axioms"]))
        for binder in record["binders"]:
            print("  %s: %s [%s]" % (binder["name"], binder["type"], binder["category"]))
            if binder["category"] not in {"nat_parameter", "numeric_side_condition"}:
                closed = False
        if not set(record["axioms"]) <= STANDARD_AXIOMS:
            print("  EXTRA AXIOMS")
            closed = False
    if closed:
        print("UNCONDITIONAL: no substantive hypothesis, no extra axiom.")
        return 0
    print("NOT CLOSED: substantive assumptions or extra axioms remain.")
    return 1


def audit(project, names):
    project = pathlib.Path(project).resolve()
    legacy = not any((project / p).exists() for p in ("lakefile.toml", "lakefile.lean"))
    source_root = project / "build/percolation" if legacy else project
    if not source_root.is_dir():
        raise ValueError("Source directory not found: " + str(source_root))
    parsed = []
    for name in names:
        if ":" in name:
            module, declaration = name.split(":", 1)
        elif "." in name:
            module, declaration = name.split(".", 1)
            module = "KN." + module
        else:
            raise ValueError("Expected Module:Namespace.declaration: " + name)
        if not NAME.fullmatch(module) or not NAME.fullmatch(declaration):
            raise ValueError("Invalid module or declaration: " + name)
        parsed.append((module, declaration))
    modules, declarations = zip(*parsed)
    choices = [candidates(source_root, m, n) for m, n in zip(modules, declarations)]
    temp_root = source_root / "KN" if legacy else source_root
    with tempfile.NamedTemporaryFile(prefix="Acceptance_", suffix=".lean", dir=temp_root,
                                     delete=False) as temp:
        path = pathlib.Path(temp.name)
    try:
        for attempt in range(max(map(len, choices))):
            queries = [cs[min(attempt, len(cs) - 1)] for cs in choices]
            path.write_text("import Lean\n" + "".join("import %s\n" % m for m in dict.fromkeys(modules))
                            + LEAN_AUDIT + "\n"
                            + "".join("#acceptance_audit %s\n" % q for q in queries))
            command = ([str(project / "knc.sh"), path.stem] if legacy
                       else ["lake", "env", "lean", str(path.relative_to(project))])
            result = subprocess.run(command, cwd=project, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            output = result.stdout
            if "unknownIdentifier" not in output and "Unknown constant" not in output:
                break
        if (result.returncode != 0 or re.search(r"\berror(?:\([^)]*\))?:", output)
                or (legacy and not re.search(r"^EXIT=0\s*$", output, re.M))):
            print("BUILD FAILED\n" + output)
            return 1
        return verdict(records_from_output(output, queries))
    finally:
        try:
            path.unlink()
        except FileNotFoundError:
            pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project")
    parser.add_argument("names", nargs="+")
    args = parser.parse_args()
    try:
        return audit(args.project, args.names)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print("AUDIT FAILED: " + str(error))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
