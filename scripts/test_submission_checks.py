"""Small regression checks for the trust-token scan's lexical boundary."""
import re
import unittest

from check_submission import code_only


class LeanLexicalBoundary(unittest.TestCase):
    def test_nested_comments_do_not_hide_following_code(self):
        source = '/- outer /- sorry -/ "axiom" -/\ntheorem t : True := by sorry\n'
        stripped = code_only(source)
        self.assertEqual(re.findall(r'\b(?:sorry|axiom)\b', stripped), ['sorry'])
        self.assertEqual(source.count('\n'), stripped.count('\n'))

    def test_strings_and_line_comments_are_not_proof_tokens(self):
        source = 'def s := "native_decide \\"sorry\\""\n-- axiom\nmodule\n'
        self.assertNotRegex(code_only(source), r'\b(?:native_decide|sorry|axiom)\b')

    def test_unterminated_input_is_rejected(self):
        for source in ['/- not closed', '"not closed']:
            with self.assertRaises(ValueError):
                code_only(source)


if __name__ == '__main__':
    unittest.main()
