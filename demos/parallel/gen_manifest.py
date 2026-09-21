"""Corpus manifests for run_parse.sh / run_search.sh: one path per line.

Three corpora, each every non-test .py under its root that the pinned CPython
3.11 oracle's own intake rules accept: real UTF-8 (no other coding cookie), no
symlink, at most 1 MiB. Never imports or executes corpus code.
    python3 gen_manifest.py <outdir>   ->  <outdir>/<name>.txt, one per corpus
Prints `name files bytes manifest` per corpus.
"""
import io
import subprocess
import sys
import tokenize
from pathlib import Path

ORACLE = Path.home() / ".hermes/hermes-agent/venv/bin/python3"
LIBS = Path.home() / "libscout/x"
# the pinned oracle's own stdlib: its top-level modules and five packages
PACKAGES = ["asyncio", "email", "importlib", "multiprocessing", "unittest"]


def stdlib():
    if not ORACLE.exists():
        sys.exit("pinned oracle missing: " + str(ORACLE))
    out = subprocess.run([ORACLE, "-c", "import sysconfig;print(sysconfig.get_path('stdlib'))"],
                         capture_output=True, text=True, check=True)
    lib = Path(out.stdout.strip())
    return sorted(lib.glob("*.py")) + sorted(p for d in PACKAGES for p in (lib / d).rglob("*.py"))


def is_test(path):
    """Any `test*` directory (numpy vendors meson's `test cases/`), any test_*.py."""
    return (any(part.startswith("test") or part == "_pytest" for part in path.parts[:-1])
            or path.name.startswith("test_") or path.name == "conftest.py")


def eligible(path):
    """The corpus rules of tests/parser/manifest.py, applied per file."""
    if path.is_symlink() or is_test(path):
        return False
    raw = path.read_bytes()
    if len(raw) > 1048576:
        return False
    try:
        encoding, _ = tokenize.detect_encoding(io.BytesIO(raw).readline)
        if encoding.lower().replace("_", "-") not in {"utf-8", "utf-8-sig"}:
            return False
        raw.decode("utf-8-sig")
    except (SyntaxError, UnicodeError, ValueError):
        return False
    return True


def corpus(name, paths, outdir):
    kept = [p for p in paths if eligible(p)]
    target = Path(outdir) / (name + ".txt")
    target.write_text("".join(str(p) + "\n" for p in kept))
    print(name, len(kept), sum(p.stat().st_size for p in kept), target)


if __name__ == "__main__":
    out = sys.argv[1]
    for lib in ["numpy-2.4.6", "pandas-3.0.6"]:
        root = LIBS / lib
        if not root.is_dir():
            sys.exit("corpus missing: " + str(root))
        corpus(lib.split("-")[0], sorted(root.rglob("*.py")), out)
    corpus("stdlib", stdlib(), out)
