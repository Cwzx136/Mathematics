#!/usr/bin/env python3
"""Elaborate the local Lean modules and replay them with leanchecker.
Invoke with 'lake env python3 scripts/check.py'. Uses the Python standard library.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from functools import lru_cache
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1, help="number of parallel module checks")
    parser.add_argument("--cache", type=Path, help="directory for checked objects; temporary by default")
    parser.add_argument("--log", type=Path, help="write the full verification report here")
    options = parser.parse_args()
    if options.jobs < 1:
        parser.error("--jobs must be positive")

    root = Path(__file__).resolve().parents[1]
    sources = sorted((root / "Research").rglob("*.lean")) + sorted(root.glob("*.lean"))
    files = {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p for p in sources}
    imports = {}
    for name, path in files.items():
        names = re.findall(r"^import\s+([\w.]+)", path.read_text(), re.MULTILINE)
        imports[name] = set(names).intersection(files)

    lean = shutil.which("lean")
    checker = shutil.which("leanchecker")
    if not lean or not checker:
        raise SystemExit("Run in the pinned Lake environment, with lean and leanchecker on PATH.")
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    manifest = (root / "lake-manifest.json").read_bytes()
    print(version, flush=True)
    temporary = tempfile.TemporaryDirectory() if options.cache is None else None
    destination = Path(temporary.name if temporary else options.cache).resolve()
    destination.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(destination) + os.pathsep + environment.get("LEAN_PATH", "")

    @lru_cache(maxsize=None)
    def signature(name):
        digest = hashlib.sha256()
        digest.update(files[name].read_bytes())
        digest.update(version.encode())
        digest.update(manifest)
        for dependency in sorted(imports[name]):
            digest.update(signature(dependency).encode())
        return digest.hexdigest()

    def check_module(name):
        relative = files[name].relative_to(root)
        obj = (destination / relative).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        stamp = obj.with_suffix(".checked.json")
        if obj.is_file() and stamp.is_file():
            cached = json.loads(stamp.read_text())
            if cached["signature"] == signature(name):
                return cached["report"]
        commands = [
            [lean, "-j2", "-t0", "-R", ".", "-o", str(obj), str(relative)],
            [checker, "--verbose", name],
        ]
        output = []
        for command in commands:
            result = subprocess.run(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise RuntimeError(f"{name}: {Path(command[0]).name} exited {result.returncode}\n{result.stdout}")
            output.append(result.stdout)
        report = "".join(output).strip()
        stamp.write_text(json.dumps({"signature": signature(name), "report": report}))
        return report

    pending = list(files)
    completed = {}
    active = {}
    with ThreadPoolExecutor(max_workers=options.jobs) as pool:
        while pending or active:
            for name in pending.copy():
                if len(active) == options.jobs:
                    break
                if imports[name] <= completed.keys():
                    pending.remove(name)
                    active[pool.submit(check_module, name)] = name
            if not active:
                raise RuntimeError("Cyclic local imports")
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for job in finished:
                name = active.pop(job)
                completed[name] = job.result()
                print(f"[{len(completed)}/{len(files)}] {name} verified", flush=True)

    if options.log:
        lines = [version]
        for name, report in sorted(completed.items()):
            lines.extend([name, report.replace(str(destination), "[object directory]"), ""])
        lines.append(f"PASS: all {len(files)} local modules compiled and replayed.")
        options.log.write_text("\n".join(lines) + "\n")
    if temporary:
        temporary.cleanup()


if __name__ == "__main__":
    main()
