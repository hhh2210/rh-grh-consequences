"""Build from source and replay each module. Requires Python 3.9+, git and Lean 4.36.0."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
MATHLIB = "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"
LEAN = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
TARGETS_SHA256 = "7a4dc8b3cc972268845ccb2bd23e9c6c1435fbfb103ece80184a47cdc8b06f45"
MODULES = ("Targets", "MillerPrime", "MillerSubgroup", "MillerCharacter",
           "MillerFromSmallNonresidue", "PrimeCountingFromPsi", "RHConsequences", "Audit")


def checked(args, cwd, env):
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    if result.returncode:
        sys.exit(f"{' '.join(args)} exited {result.returncode}\n{result.stdout}")
    return result.stdout.replace("\r\n", "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepared-mathlib", type=Path, help="reuse a built checkout at the exact pin")
    parser.add_argument("--receipt", type=Path, help="write the full verification transcript")
    args = parser.parse_args()
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    version = checked(["lean", "--version"], ROOT, env).strip()
    if f"commit {LEAN}" not in version or "4.36.0" not in version:
        sys.exit(f"Unexpected Lean compiler: {version}")
    if args.prepared_mathlib:
        mathlib = args.prepared_mathlib.resolve()
    else:
        checked(["lake", "resolve-deps"], ROOT, env)
        mathlib = ROOT / ".lake/packages/mathlib"
    if checked(["git", "rev-parse", "HEAD"], mathlib, env).strip() != MATHLIB:
        sys.exit("Mathlib revision does not match the pin")
    if not args.prepared_mathlib:
        checked(["lake", "exe", "cache", "get"], ROOT, env)
    search_path = [mathlib / ".lake/build/lib/lean"]
    manifest = json.loads((mathlib / "lake-manifest.json").read_text(encoding="utf-8"))
    pkgdir = (mathlib if args.prepared_mathlib else ROOT) / ".lake/packages"
    for pkg in manifest["packages"]:
        package = pkgdir / pkg["name"]
        if checked(["git", "rev-parse", "HEAD"], package, env).strip() != pkg["rev"]:
            sys.exit(f"Dependency revision mismatch: {pkg['name']}")
        search_path.append(package / ".lake/build/lib/lean")
    receipt = [version, f"Mathlib {MATHLIB}"]
    with tempfile.TemporaryDirectory() as tmp:
        env["LEAN_PATH"] = os.pathsep.join([tmp, *map(str, search_path)])
        for name in MODULES:
            src = ROOT / f"{name}.lean"
            data = src.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            if (b"\r" in data or re.search(rb"\b(?:sorry|admit|axiom)\b", data)
                    or (name == "Targets" and digest != TARGETS_SHA256)):
                sys.exit(f"Unexpected source content in {src.name}")
            log = checked(["lean", "-o", str(Path(tmp) / f"{name}.olean"), src.name], ROOT, env)
            if "sorryAx" in log or "declaration uses 'sorry'" in log:
                sys.exit(f"Unproved declaration in {name}")
            replay = checked(["leanchecker", "-v", name], ROOT, env)
            if f"replaying {name}" not in replay.splitlines():
                sys.exit(f"No named kernel replay for {name}")
            receipt.extend([f"\n{src.name} sha256={digest}", log.rstrip(),
                            f"lean -o <clean-build>/{name}.olean {src.name} -> exit 0",
                            f"leanchecker -v {name}", replay.rstrip(), "exit 0"])
            print(f"Verified {name}", flush=True)
    if args.receipt:
        args.receipt.write_bytes(("\n".join(receipt) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
