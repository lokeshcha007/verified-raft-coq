"""Compile all proofs, audit assumptions, and independently check proof objects.

Uses only Python's standard library. Run from any directory with Python >= 3.9.
"""
import argparse
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def executable(value, fallback):
    value = value or shutil.which(fallback)
    if not value:
        raise RuntimeError(f"{fallback} not found: install Rocq or pass --{fallback}")
    path = shutil.which(str(value)) or str(Path(value).resolve())
    if not Path(path).is_file():
        raise RuntimeError(f"Executable does not exist: {path}")
    return path


def run(command, env):
    result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {shlex.join(command)}")
    return result.stdout


def strip_comments(source):
    # Rocq comments nest. Preserve newlines and reject an unterminated comment.
    result, depth, i = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == "(*":
            depth += 1
            i += 2
        elif pair == "*)" and depth:
            depth -= 1
            i += 2
        else:
            result.append(source[i] if depth == 0 or source[i] == "\n" else " ")
            i += 1
    if depth:
        raise RuntimeError("Unterminated Rocq comment")
    return "".join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coqc", default=os.environ.get("COQC"))
    parser.add_argument("--coqchk", default=os.environ.get("COQCHK"))
    args = parser.parse_args()
    compiler = executable(args.coqc, "coqc")
    sibling = Path(compiler).with_name("coqchk.exe" if os.name == "nt" else "coqchk")
    checker = executable(args.coqchk or (str(sibling) if sibling.is_file() else None), "coqchk")
    env = os.environ.copy()
    # The Windows Platform binaries need their bundled DLL directory on PATH.
    env["PATH"] = str(Path(compiler).parent) + os.pathsep + env.get("PATH", "")

    project = shlex.split((ROOT / "_CoqProject").read_text(encoding="utf-8"))
    flags = project[:3]
    sources = project[3:]
    if flags != ["-Q", "theories", "VerifiedRaft"] or not sources:
        raise RuntimeError("Unexpected _CoqProject format")
    forbidden = re.compile(r"\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters|Abort)\b")
    for source in sources:
        text = strip_comments((ROOT / source).read_text(encoding="utf-8"))
        if forbidden.search(text):
            raise RuntimeError(f"Unfinished proof or axiom declaration in {source}")
    audit_source = strip_comments((ROOT / "theories/Audit.v").read_text(encoding="utf-8"))
    expected = len(re.findall(r"Print\s+Assumptions\s+", audit_source))
    if not expected:
        raise RuntimeError("Assumption audit is empty")

    run([compiler, "--version"], env)
    for source in sources:
        print(f"Compiling {source}", flush=True)
        output = run([compiler, *flags, source], env)
        if source == "theories/Audit.v":
            closed = output.count("Closed under the global context")
            if closed != expected or re.search(r"(?m)^Axioms:", output):
                raise RuntimeError(f"Assumption audit failed: {closed}/{expected} closed")
    print("Independently checking compiled proof objects...", flush=True)
    run([checker, "-silent", *flags, "VerifiedRaft.Audit", "VerifiedRaft.Examples"], env)
    print(f"PASS: {len(sources)} modules compiled; {expected} assumption audits closed; kernel check passed.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
