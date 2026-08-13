from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from harness import verifier


class VerifierRemoteWorkspaceTests(unittest.TestCase):
    def test_verifier_copy_initialises_fetchable_git_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            temp_root = Path(tmp) / "verifier-root"

            def copytree(_src: Path, dst: Path, **_kwargs: object) -> Path:
                dst.mkdir(parents=True)
                return dst

            with mock.patch.object(verifier.tempfile, "mkdtemp", return_value=str(temp_root)), mock.patch.object(
                verifier.shutil, "copytree", side_effect=copytree
            ), mock.patch.object(verifier, "initialise_remote_git_checkout") as initialise, mock.patch.object(
                verifier, "setup_private_lake"
            ):
                result = verifier._copy_repo_for_verification()

        self.assertEqual(result, temp_root / "repo")
        initialise.assert_called_once_with(result)


if __name__ == "__main__":
    unittest.main()
