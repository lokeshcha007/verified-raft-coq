"""Remove only generated proof artifacts under this project's theories folder."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
patterns = ("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux", ".lia.cache", ".nia.cache")
for pattern in patterns:
    for path in (root / "theories").glob(pattern):
        if path.is_file():
            path.unlink()
for name in (".lia.cache", ".nia.cache"):
    path = root / name
    if path.is_file():
        path.unlink()
