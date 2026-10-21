"""Regression tests for the proof hygiene scanner."""

import importlib.util
from pathlib import Path
import sys
import unittest


SPEC = importlib.util.spec_from_file_location("hygiene", Path(__file__).with_name("check-hygiene.py"))
HYGIENE = importlib.util.module_from_spec(SPEC)
sys.dont_write_bytecode = True
SPEC.loader.exec_module(HYGIENE)


class HygieneTest(unittest.TestCase):
    def test_nested_comments_and_strings_are_not_code(self):
        source = '-- ?\n{- outer {- {!!} -} postulate hidden -}\nx = "postulate ?"\n'
        self.assertEqual(HYGIENE.inspect_source("Proof/Example.agda", source), [])

    def test_holes_inline_postulates_and_primitives_are_rejected(self):
        for source in ("x = {!!}", "x = ?", "postulate hidden : Set", "primitive hidden : Set"):
            with self.subTest(source=source):
                self.assertTrue(HYGIENE.inspect_source("Proof/Example.agda", source))

    def test_predicate_question_mark_is_not_a_meta(self):
        self.assertEqual(HYGIENE.inspect_source("Proof/Example.agda", "present? : Set"), [])

    def test_multiline_options_cannot_disable_checks(self):
        source = "{-# OPTIONS\n --allow-unsolved-metas --no-termination-check #-}"
        self.assertTrue(HYGIENE.inspect_source("Proof/Example.agda", source))

    def test_new_check_bypass_is_rejected(self):
        self.assertTrue(HYGIENE.inspect_source("Proof/Example.agda", "{-# TERMINATING #-}"))

    def test_no_bypass_allowlist_remains(self):
        self.assertEqual(HYGIENE.LEGACY_OVERRIDES, {})

    def test_retired_confluence_override_cannot_be_reintroduced(self):
        path = "Proof/Confluence.agda"
        source = "{-# TERMINATING #-}\n"
        self.assertEqual(HYGIENE.inspect_source(path, "module Proof.Confluence where"), [])
        self.assertTrue(HYGIENE.inspect_source(path, source))
        self.assertTrue(HYGIENE.inspect_source(path, source + "{-# TERMINATING #-}"))
        self.assertTrue(HYGIENE.inspect_source(path, source.replace("TERMINATING", "NON_TERMINATING", 1)))

    def test_parallel_module_cannot_reintroduce_a_termination_override(self):
        for path in ("Core/Parallel.agda", "Core/StrictParallel.agda",
                     "Core/Relation.agda", "Proof/StrictConfluence.agda"):
            self.assertEqual(HYGIENE.inspect_source(path, ""), [])
            for pragma in ("TERMINATING", "NON_TERMINATING", "NO_TERMINATION_CHECK"):
                with self.subTest(path=path, pragma=pragma):
                    self.assertTrue(HYGIENE.inspect_source(path, "{-# " + pragma + " #-}"))

    def test_safe_options_are_explicit(self):
        self.assertEqual(
            HYGIENE.inspect_source("Proof/Example.agda", "{-# OPTIONS --guardedness #-}"), []
        )


if __name__ == "__main__":
    unittest.main()
