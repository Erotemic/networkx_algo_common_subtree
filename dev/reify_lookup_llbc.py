#!/usr/bin/env python3
"""Reify the pinned Charon lookup fragment without discarding source statements.

The input must use --no-dedup-serialized-ast and the Aeneas preset. This narrow
adapter rejects unsupported value/control operations. It translates successful
calls only; allocation failure and stack exhaustion retain the existing Aeneas
trust boundary. Generated Lean is checked against a separate operational model.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


FUNCTIONS = {"copy_word": "copyWord", "words_equal": "compare",
             "copy_result": "copyResult", "memo_lookup": "lookup"}
ARITIES = {"copy_word": 1, "words_equal": 2, "copy_result": 1, "memo_lookup": 3}
KINDS = {"BalancedWord": "word", "MemoTable": "table", "MemoEntry": "entry",
         "CommonEmbedding": "embedding", "Option": "optional"}


class Reifier:
    def __init__(self, data):
        if data["charon_version"] != "0.1.315":
            raise ValueError("unsupported Charon serialization version")
        self.crate = data["translated"]
        if self.crate["crate_name"] != "verified_ordered_core":
            raise ValueError("expected the maintained ordered core")
        if not self.crate["options"]["no_dedup_serialized_ast"]:
            raise ValueError("re-extract with --no-dedup-serialized-ast")
        if self.crate["options"]["preset"] != "Aeneas":
            raise ValueError("only the pinned Aeneas extraction preset is supported")
        self.kinds = {}
        self.functions = {}
        self.selected = {}
        for decl in self.crate["type_decls"]:
            if decl:
                name = decl["item_meta"]["name"]
                last = name[-1]
                named = [part.get("Ident", [None])[0] for part in name]
                if named == ["verified_ordered_core", last.get("Ident", [None])[0]] and named[-1] in KINDS:
                    self.kinds[decl["def_id"]] = KINDS[last["Ident"][0]]
                elif named == ["core", "option", "Option"]:
                    self.kinds[decl["def_id"]] = "optional"
                elif "Builtin" in last and last["Builtin"][0] == {"Tuple": 0}:
                    self.kinds[decl["def_id"]] = "tuple"
        for decl in self.crate["fun_decls"]:
            if decl:
                name = decl["item_meta"]["name"]
                last = name[-1].get("Ident", [None])[0]
                if last in FUNCTIONS and name == [
                        {"Ident": ["verified_ordered_core", 0]}, {"Ident": [last, 0]}]:
                    if last in self.selected:
                        raise ValueError(f"duplicate root helper: {last}")
                    arity = ARITIES[last]
                    if (len(decl["signature"]["inputs"]) != arity or
                            decl["body"]["Structured"]["locals"]["arg_count"] != arity):
                        raise ValueError(f"unsupported argument count for {last}")
                    self.functions[decl["def_id"]] = FUNCTIONS[last]
                    self.selected[last] = decl
                elif (len(name) == 4 and name[:2] == [
                        {"Ident": ["alloc", 0]}, {"Ident": ["boxed", 0]}] and
                        name[-1] == {"Ident": ["new", 0]} and
                        name[2].get("Impl", {}).get("Ty", {}).get("kind") == "InherentImplBlock" and
                        name[2]["Impl"]["Ty"]["skip_binder"]["Untagged"].get("Adt", {}).get("builtin") == "Box"):
                    if "boxNew" in self.functions.values():
                        raise ValueError("duplicate Box::new declaration")
                    self.functions[decl["def_id"]] = "boxNew"
        if set(self.selected) != set(FUNCTIONS):
            raise ValueError("the four source definitions must all be present")

    def kind(self, ref):
        return self.kinds[ref["id"]]

    @staticmethod
    def local(place):
        kind = place["kind"]
        if set(kind) != {"Local"}:
            raise ValueError("only whole-local moves/assignments are supported")
        return kind["Local"]

    def place(self, place):
        kind = place["kind"]
        if "Local" in kind:
            return f"(.local {kind['Local']})"
        parent, projection = kind["Projection"]
        if projection == "Deref":
            return f"(.deref {self.place(parent)})"
        variant, field = projection["Field"]
        expected = "none" if variant is None else f"(some {variant})"
        return f"(.field {self.place(parent)} {expected} {field})"

    def key(self, constant):
        raw, _ty = constant["Untagged"]
        if set(raw) == {"Bool"}:
            return f"(.boolean {str(raw['Bool']).lower()})"
        ref, variant = raw["Discriminant"]
        return f"(.variant .{self.kind(ref)} {variant})"

    def operand(self, operand):
        if "Move" in operand:
            return f"(.move {self.local(operand['Move'])})"
        if "Copy" in operand:
            place, _copy_trait = operand["Copy"]
            return f"(.copy {self.place(place)})"
        constant, _ty = operand["Const"]["Untagged"]
        return f"(.boolean {str(constant['Bool']).lower()})"

    def operands(self, operands):
        return "[" + ", ".join(self.operand(op) for op in operands) + "]"

    def rvalue(self, value):
        if "Use" in value:
            operand, marker = value["Use"]
            if marker != "Yes":
                raise ValueError("unsupported Use marker")
            return f"(.use {self.operand(operand)})"
        if "Ref" in value:
            ref = value["Ref"]
            if ref["kind"] != "Shared":
                raise ValueError("mutable references are outside this fragment")
            metadata, _ty = ref["ptr_metadata"]["Const"]["Untagged"]
            if metadata != {"Adt": [None, []]}:
                raise ValueError("only thin, sized shared references are supported")
            return f"(.address {self.place(ref['place'])})"
        aggregate, operands = value["Aggregate"]
        ref, variant, field = aggregate["Adt"]
        if field is not None:
            raise ValueError("union initialization is unsupported")
        return f"(.aggregate .{self.kind(ref)} {variant or 0} {self.operands(operands)})"

    def scrutinee(self, value):
        if "Discriminant" in value:
            return f"(.discriminant {self.place(value['Discriminant'])})"
        return f"(.value {self.operand(value['Value'])})"

    @staticmethod
    def check_unwind(block):
        # Successful primitive calls do not take this edge. Recognize it
        # explicitly rather than silently interpreting arbitrary unwind code.
        for stmt in block["statements"]:
            kind = stmt["kind"]
            allowed = isinstance(kind, dict) and (set(kind) == {"StorageDead"} or
                set(kind) == {"Drop"} and kind["Drop"]["kind"] == "Conditional")
            if kind != "UnwindResume" and not allowed:
                raise ValueError("nontrivial unwind code is outside this pilot")

    def block(self, block, indent=2):
        return self.sequence(block["statements"], indent)

    def sequence(self, statements, indent):
        pad = " " * indent
        if not statements:
            return pad + ".done"
        stmt, *rest = statements
        kind = stmt["kind"]
        if kind == "Return":
            if rest:
                raise ValueError("statements after an unconditional return")
            return pad + ".ret"
        if "Switch" in kind:
            switch = kind["Switch"]
            data = switch["data"]
            branches = data["branches"]
            if len(switch["branches"]) != 2 or not 1 <= len(branches) <= 2:
                raise ValueError("only binary switches are supported")
            first_key, first_index = branches[0]
            if len(branches) == 2:
                second_key, second_index = branches[1]
                if data["fallback"] is not None:
                    raise ValueError("unsupported three-way switch")
                other = f"(some {self.key(second_key)})"
            else:
                second_index = data["fallback"]
                other = "none"
            if {first_index, second_index} != {0, 1}:
                raise ValueError("invalid branch indices")
            return (pad + f".branch {self.scrutinee(data['scrutinee'])} {self.key(first_key)} {other}\n" +
                    pad + "(\n" + self.block(switch["branches"][first_index], indent + 2) + ")\n" +
                    pad + "(\n" + self.block(switch["branches"][second_index], indent + 2) + ")\n" +
                    pad + "(\n" + self.sequence(rest, indent + 2) + ")")
        if "StorageLive" in kind or "StorageDead" in kind:
            action = f"(.scope {next(iter(kind.values()))})"
        elif "Assign" in kind:
            dest, value = kind["Assign"]
            action = f"(.assign {self.local(dest)} {self.rvalue(value)})"
        elif "Call" in kind:
            call = kind["Call"]
            self.check_unwind(call["on_unwind"])
            function = self.functions[call["call"]["func"]["Regular"]["kind"]["Fun"]]
            action = f"(.call .{function} {self.operands(call['call']['args'])} {self.local(call['dest'])})"
        elif "Drop" in kind:
            drop = kind["Drop"]
            if drop["kind"] != "Conditional":
                raise ValueError("live/precise destruction is unsupported")
            action = f"(.dropMoved {self.local(drop['place'])})"
        else:
            raise ValueError(f"unsupported statement: {kind}")
        return pad + f".step {action} (\n" + self.sequence(rest, indent + 2) + ")"

    def lean(self, namespace="Program"):
        definitions = []
        for rust, lean in FUNCTIONS.items():
            source = self.selected[rust]["body"]["Structured"]
            definitions.append(f"def {lean} : Code :=\n{self.block(source['body'])}\n")
        definitions.append("def body : Function → Code\n" + "\n".join(
            f"  | .{name} => {name}" for name in FUNCTIONS.values()) + "\n  | .boxNew => .done\n")
        program = "\n".join(definitions)
        digest = hashlib.sha256(program.encode()).hexdigest()
        header = ("-- Generated by dev/reify_lookup_llbc.py; do not edit.\n"
                  f"-- Reified normal-path code SHA-256: {digest}\n"
                  "module\npublic import SubtreeProofs.Rust.LookupSource\n"
                  f"@[expose] public section\nnamespace SubtreeProofs.Rust.LookupSource.{namespace}\n\n")
        return header + program + f"\nend SubtreeProofs.Rust.LookupSource.{namespace}\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("llbc", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--namespace", default="Program", choices=("Program", "ExtraCompare"))
    args = parser.parse_args()
    raw = args.llbc.read_bytes()
    text = Reifier(json.loads(raw)).lean(args.namespace)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)


if __name__ == "__main__":
    main()
