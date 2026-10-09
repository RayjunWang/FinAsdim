#!/usr/bin/env python3
"""Create and verify a source-only ZIP of this repository.

Run from any directory: python scripts/package.py
The computation record's hashes are checked before the archive is written.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import zipfile


ROOT = Path(__file__).resolve().parent.parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    record = json.loads((ROOT / "computation-record.json").read_text(encoding="utf-8"))
    for entry in [record["task"], *record["artifacts"]]:
        name = entry.get("path", entry.get("file"))
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != entry["sha256"]:
            raise ValueError(f"Artifact hash mismatch or invalid path: {name}")
    names = {
        ".gitignore", "FiniteAsdim.lean", "AxiomAudit.lean", "README.md",
        "LICENSE", "NOTICE.md", "lakefile.toml", "lake-manifest.json",
        "lean-toolchain", "task.md", "computation-record.json",
    }
    for directory, suffixes in [
        ("FiniteAsdim", {".lean"}), ("scripts", {".py", ".ps1"}),
        ("docs", {".md", ".log"}), (".github/workflows", {".yml", ".yaml"}),
    ]:
        names.update(p.relative_to(ROOT).as_posix() for p in (ROOT / directory).rglob("*")
                     if p.is_file() and p.suffix in suffixes and "__pycache__" not in p.parts)
    output = ROOT / "finite-asdim-lean.zip"
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in sorted(names):
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 9, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, (ROOT / name).read_bytes())
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None or set(archive.namelist()) != names:
            raise ValueError("Archive integrity failure")
        for name in names:
            if archive.read(name) != (ROOT / name).read_bytes():
                raise ValueError(f"Archive differs from source: {name}")
    print(f"Verified {len(names)} source files in {output.name} ({output.stat().st_size} bytes)")
    print(f"SHA-256: {digest(output)}")


if __name__ == "__main__":
    main()
