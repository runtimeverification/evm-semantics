from unittest import TestCase

from kevm_pyk import __version__


class VersionTest(TestCase):
    def test_version(self):
        self.assertEqual(__version__, '0.1.0')
