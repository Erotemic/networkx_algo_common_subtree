"""Frontend identity/schema regressions; real extraction is checked separately.

Fixtures retain only fields consumed by these tests. They are not claimed to
be well-typed LLBC programs or used as the source of any Lean certificate.
"""
from __future__ import annotations

import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "dev"))
from reify_lookup_llbc import ARITIES, Reifier
from regenerate_memo_source import HELPERS as MEMO_HELPERS, ARITIES as MEMO_ARITIES


def fixture(arities=ARITIES):
    functions = []
    for index, (name, arity) in enumerate(arities.items()):
        functions.append({"def_id": index, "item_meta": {"name": [
            {"Ident": ["verified_ordered_core", 0]}, {"Ident": [name, 0]}]},
            "signature": {"inputs": [None] * arity},
            "body": {"Structured": {"locals": {"arg_count": arity},
                                      "body": {"statements": []}}}})
    return {"charon_version": "0.1.315", "translated": {
        "crate_name": "verified_ordered_core", "options": {
            "no_dedup_serialized_ast": True, "preset": "Aeneas"},
        "type_decls": [], "fun_decls": functions}}


class ReifierIdentityTests(unittest.TestCase):
    def test_exact_root_helper_identity(self):
        data = fixture()
        parser = Reifier(data)
        self.assertEqual(parser.functions, {0: "copyWord", 1: "compare", 2: "copyResult", 3: "lookup"})

    def test_nested_same_name_cannot_replace_root_or_alias_call(self):
        data = fixture()
        nested = copy.deepcopy(data["translated"]["fun_decls"][1])
        nested["def_id"] = 99
        nested["item_meta"]["name"].insert(1, {"Ident": ["nested", 0]})
        data["translated"]["fun_decls"].append(nested)
        parser = Reifier(data)
        self.assertEqual(parser.selected["words_equal"]["def_id"], 1)
        self.assertNotIn(99, parser.functions)
        call = {"kind": {"Call": {"call": {"func": {"Regular": {"kind": {"Fun": 99}}},
            "args": []}, "dest": {"kind": {"Local": 0}}, "on_unwind": {"statements": []}}}}
        with self.assertRaises(KeyError):
            parser.sequence([call], 2)

    def test_nested_helper_cannot_satisfy_missing_root(self):
        data = fixture()
        data["translated"]["fun_decls"][1]["item_meta"]["name"].insert(1, {"Ident": ["nested", 0]})
        with self.assertRaisesRegex(ValueError, "four source definitions"):
            Reifier(data)

    def test_duplicate_root_helper_is_rejected(self):
        data = fixture()
        duplicate = copy.deepcopy(data["translated"]["fun_decls"][1])
        duplicate["def_id"] = 99
        data["translated"]["fun_decls"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "duplicate root helper"):
            Reifier(data)

    def test_profile_and_serialization_are_checked(self):
        for key, value in (("preset", "Default"), ("no_dedup_serialized_ast", False)):
            data = fixture()
            data["translated"]["options"][key] = value
            with self.assertRaises(ValueError):
                Reifier(data)

    def test_both_signature_and_body_argument_counts_are_checked(self):
        for location in ("signature", "locals"):
            data = fixture()
            lookup = data["translated"]["fun_decls"][3]
            if location == "signature":
                lookup["signature"]["inputs"].append(None)
            else:
                lookup["body"]["Structured"]["locals"]["arg_count"] += 1
            with self.assertRaisesRegex(ValueError, "argument count"):
                Reifier(data)

    def test_memo_helpers_use_their_own_identity_arity_and_namespace(self):
        data = fixture(MEMO_ARITIES)
        parser = Reifier(data, helpers=MEMO_HELPERS, arities=MEMO_ARITIES)
        self.assertEqual(parser.functions[3], "insert")
        self.assertEqual(parser.arities["memo_insert"], 4)
        generated = parser.lean(root_namespace="SubtreeProofs.Rust.MemoSource",
                                import_module="SubtreeProofs.Rust.MemoSource")
        self.assertIn("def insert : Code", generated)
        self.assertIn("namespace SubtreeProofs.Rust.MemoSource.Program", generated)
        self.assertNotIn("def lookup", generated)

    def test_memo_insert_cannot_be_replaced_by_a_nested_or_wrong_arity_helper(self):
        for nested in (False, True):
            data = fixture(MEMO_ARITIES)
            insert = data["translated"]["fun_decls"][3]
            if nested:
                insert["item_meta"]["name"].insert(1, {"Ident": ["nested", 0]})
            else:
                insert["body"]["Structured"]["locals"]["arg_count"] = 3
            with self.assertRaises(ValueError):
                Reifier(data, helpers=MEMO_HELPERS, arities=MEMO_ARITIES)

    def test_unsupported_live_drop_and_mutable_ref_are_rejected(self):
        parser = Reifier(fixture())
        with self.assertRaisesRegex(ValueError, "destruction"):
            parser.sequence([{"kind": {"Drop": {"kind": "Precise"}}}], 2)
        with self.assertRaisesRegex(ValueError, "mutable references"):
            parser.rvalue({"Ref": {"kind": "Mut"}})


if __name__ == "__main__":
    unittest.main()
