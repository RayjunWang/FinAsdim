#!/usr/bin/env python3
"""Scan authored Lean sources and optionally validate a kernel axiom log.

Usage from the project root:
    python scripts/audit.py
    python scripts/audit.py --axiom-log axiom-audit.log
    python scripts/audit.py FiniteAsdim AxiomAudit.lean --axiom-log axiom-audit.log

The default source scan covers every .lean file beneath the project root,
excluding generated directories such as .lake, .git, and .work. Nested Lean
block comments, line comments, ordinary/raw strings, and quoted identifiers
are masked before token matching. The scan rejects executable occurrences
of sorry, admit, axiom, unsafe, and native_decide.

An axiom log must contain the four final declarations printed by
AxiomAudit.lean. Every reported axiom must be one of propext,
Classical.choice, and Quot.sound. Compilation errors or an incomplete log
fail the audit. This script is an additional safeguard: Lean compilation
and #print axioms establish the kernel dependencies.

Python 3.9 or newer; no third-party packages are required.
"""

from __future__ import annotations

import argparse
import bisect
import os
from pathlib import Path
import re
import sys
from typing import Iterable


PROJECT_ROOT = Path(__file__).resolve().parent.parent
IGNORED_DIRECTORIES = {".git", ".lake", ".work", "__pycache__", ".venv", "venv"}
FORBIDDEN = re.compile(r"(?<![\w'])\b(sorry|admit|axiom|unsafe|native_decide)\b(?![\w'])")
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUIRED_DECLARATIONS = frozenset(
    {
        "FiniteAsdim.theorem1_1",
        "FiniteAsdim.theorem1_1_closed",
        "FiniteAsdim.theorem1_1_statement",
        "FiniteAsdim.lattice_bound",
    }
)
AXIOM_ENTRY = re.compile(
    r"'(?P<name>[^'\r\n]+)'\s+"
    r"(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)",
    re.MULTILINE,
)
COMPILATION_ERROR = re.compile(r"\berror(?:\([^\r\n]*?\))?:")


def mask_non_code(source: str) -> tuple[str, list[tuple[int, str]]]:
    """Preserve offsets/newlines while masking Lean comments and literals.

    Unclosed block comments, strings, and quoted identifiers are errors.
    Raw strings are recognized in Lean's r#"..."# syntax, with any number
    of hashes. Prime marks in ordinary Lean identifiers remain untouched.
    """
    chars = list(source)
    errors: list[tuple[int, str]] = []
    n = len(source)
    i = 0

    def mask(start: int, end: int) -> None:
        for pos in range(start, end):
            if chars[pos] not in "\r\n":
                chars[pos] = " "

    while i < n:
        if source.startswith("--", i):
            end = source.find("\n", i + 2)
            if end < 0:
                end = n
            mask(i, end)
            i = end
        elif source.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while i < n and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            mask(start, i)
            if depth:
                errors.append((start, "unterminated block comment"))
        elif source[i] == "«":
            start = i
            end = source.find("»", i + 1)
            if end < 0:
                errors.append((start, "unterminated quoted identifier"))
                end = n - 1
            i = end + 1
            mask(start, i)
        else:
            # Recognize raw prefixes before the ordinary quotation mark.
            raw_quote = -1
            hashes = 0
            if source[i] == "r" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
                j = i + 1
                while j < n and source[j] == "#":
                    j += 1
                if j < n and source[j] == '"':
                    raw_quote = j
                    hashes = j - i - 1
            if raw_quote >= 0:
                start = i
                delimiter = '"' + "#" * hashes
                end = source.find(delimiter, raw_quote + 1)
                if end < 0:
                    errors.append((start, "unterminated raw string"))
                    i = n
                else:
                    i = end + len(delimiter)
                mask(start, i)
            elif source[i] == '"':
                start = i
                i += 1
                closed = False
                while i < n:
                    if source[i] == "\\":
                        i = min(i + 2, n)
                    elif source[i] == '"':
                        i += 1
                        closed = True
                        break
                    else:
                        i += 1
                mask(start, i)
                if not closed:
                    errors.append((start, "unterminated string"))
            else:
                i += 1
    return "".join(chars), errors


def source_files(roots: Iterable[Path]) -> list[Path]:
    """Return a deterministic list without descending into generated trees."""
    found: set[Path] = set()
    for root in roots:
        if root.is_file():
            if root.suffix == ".lean":
                found.add(root.resolve())
            else:
                raise ValueError(f"source file must have .lean extension: {root}")
        elif root.is_dir():
            for directory, dirs, files in os.walk(root, followlinks=False):
                dirs[:] = sorted(d for d in dirs if d not in IGNORED_DIRECTORIES)
                for filename in files:
                    if filename.endswith(".lean"):
                        found.add((Path(directory) / filename).resolve())
        else:
            raise ValueError(f"source path does not exist: {root}")
    return sorted(found, key=lambda path: str(path).casefold())


def display_path(path: Path) -> str:
    try:
        return path.relative_to(PROJECT_ROOT).as_posix()
    except ValueError:
        return str(path)


def audit_source(path: Path) -> list[str]:
    source = path.read_text(encoding="utf-8-sig")
    masked, errors = mask_non_code(source)
    starts = [0] + [match.end() for match in re.finditer("\n", source)]

    def location(offset: int) -> str:
        index = bisect.bisect_right(starts, offset) - 1
        return f"{display_path(path)}:{index + 1}:{offset - starts[index] + 1}"

    failures = [f"{location(offset)}: {message}" for offset, message in errors]
    failures.extend(
        f"{location(match.start())}: forbidden executable token `{match.group(1)}`"
        for match in FORBIDDEN.finditer(masked)
    )
    return failures


def audit_axiom_log(path: Path, required: set[str]) -> tuple[list[str], int]:
    log = path.read_text(encoding="utf-8-sig")
    failures: list[str] = []
    if COMPILATION_ERROR.search(log):
        failures.append(f"{display_path(path)}: Lean compilation error in axiom log")
    entries = list(AXIOM_ENTRY.finditer(log))
    if not entries:
        failures.append(f"{display_path(path)}: no #print axioms output found")
    seen: set[str] = set()
    for entry in entries:
        declaration = entry.group("name")
        seen.add(declaration)
        dependencies = entry.group("axioms") or ""
        axioms = {name.strip() for name in dependencies.split(",") if name.strip()}
        unexpected = sorted(axioms - ALLOWED_AXIOMS)
        if unexpected:
            failures.append(
                f"{display_path(path)}: {declaration} uses unapproved axioms: "
                + ", ".join(unexpected)
            )
    missing = sorted(required - seen)
    if missing:
        failures.append(
            f"{display_path(path)}: missing audited declarations: " + ", ".join(missing)
        )
    return failures, len(entries)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("sources", nargs="*", type=Path, help="Lean files/directories; default: project root")
    parser.add_argument("--axiom-log", action="append", type=Path, default=[], help="Lean AxiomAudit.lean output to validate")
    parser.add_argument("--require-declaration", action="append", default=[], help="additional declaration required in each axiom log")
    args = parser.parse_args(argv)
    try:
        files = source_files(args.sources or [PROJECT_ROOT])
        if not files:
            raise ValueError("no Lean source files found")
        failures: list[str] = []
        for path in files:
            failures.extend(audit_source(path))
        entry_count = 0
        required = set(REQUIRED_DECLARATIONS) | set(args.require_declaration)
        for path in args.axiom_log:
            errors, count = audit_axiom_log(path, required)
            failures.extend(errors)
            entry_count += count
    except (OSError, UnicodeError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        return 1
    print(f"PASS: scanned {len(files)} Lean source files; no forbidden executable tokens.")
    if args.axiom_log:
        print(f"PASS: checked {entry_count} axiom reports; only standard Lean logical axioms occur.")
    else:
        print("Axiom log not supplied; this run checked source tokens only.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
