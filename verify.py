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
CRYPTIDS = "3647718b5df22e1a61462dec0376bd204526285a"
VENDOR = ROOT / "vendor/cryptids"
UPSTREAM_MODULES = tuple("Cryptids.Semantics.Riemann." + part for part in (
    "Schmidt", "DigammaBinet", "ExplicitLarge", "VonMangoldtCount",
    "HorizontalBounds", "WeightedStieltjes"))
MODULES = ("Targets", "MillerPrime", "MillerSubgroup", "MillerCharacter",
           "MillerFromSmallNonresidue", "PrimeCountingFromPsi", "PsiCompact", *UPSTREAM_MODULES,
           "PsiFromRH", "PsiZeroCountingWindow", "Cramer", "RHConsequences", "Audit")


def checked(args, cwd, env):
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
    if result.returncode:
        sys.exit(f"{' '.join(args)} exited {result.returncode}\n{result.stdout}")
    return result.stdout.replace("\r\n", "\n")


def prepare_cryptids(env):
    """Assemble canonical modules without modifying the submodule checkout."""
    if not (VENDOR / "Cryptids").is_dir():
        checked(["git", "-c", "core.autocrlf=false", "submodule", "update", "--init",
                 "--depth", "1", "--", "vendor/cryptids"], ROOT, env)
    if checked(["git", "rev-parse", "HEAD"], VENDOR, env).strip() != CRYPTIDS:
        sys.exit("Cryptids revision does not match the pin")
    generated = ROOT / ".lake/cryptids-src"
    for name in UPSTREAM_MODULES:
        relative = Path(*name.split(".")).with_suffix(".lean")
        data = subprocess.check_output(["git", "show", f"{CRYPTIDS}:{relative.as_posix()}"], cwd=VENDOR)
        if name.endswith(".Schmidt"):
            with tempfile.TemporaryDirectory() as scratch:
                source = Path(scratch) / relative
                source.parent.mkdir(parents=True)
                source.write_bytes(data)
                checked(["git", "-c", "core.autocrlf=false", "apply", "--no-index", "--whitespace=error-all",
                         str(ROOT / "compat/Schmidt-4.36.patch")], scratch, env)
                data = source.read_bytes()
            if hashlib.sha256(data).hexdigest() != "fcd500ce61e2575d133d42a44b2131271e374803b55cd95a86f204a500bc0cd9":
                sys.exit("Unexpected Schmidt compatibility patch result")
        dst = generated / relative
        dst.parent.mkdir(exist_ok=True, parents=True)
        if not dst.exists() or dst.read_bytes() != data:
            with tempfile.NamedTemporaryFile(dir=dst.parent, delete=False) as tmp:
                tmp.write(data)
            os.replace(tmp.name, dst)
    return generated


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepared-mathlib", type=Path, help="reuse a built checkout at the exact pin")
    parser.add_argument("--receipt", type=Path, help="write the full verification transcript")
    parser.add_argument("--prepare-sources", action="store_true", help="materialize the Cryptids modules for Lake and exit")
    args = parser.parse_args()
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    generated = prepare_cryptids(env)
    if args.prepare_sources:
        return
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
    receipt = [version, f"Mathlib {MATHLIB}", f"Cryptids {CRYPTIDS}"]
    with tempfile.TemporaryDirectory() as tmp:
        env["LEAN_PATH"] = os.pathsep.join([tmp, *map(str, search_path)])
        for name in MODULES:
            upstream = name in UPSTREAM_MODULES
            srcroot = generated if upstream else ROOT
            relative = Path(*name.split(".")).with_suffix(".lean")
            src = srcroot / relative
            data = src.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            if b"\r" in data or (name == "Targets" and digest != TARGETS_SHA256):
                sys.exit(f"Unexpected source content in {src.name}")
            if not upstream and re.search(rb"\b(?:sorry|admit|axiom)\b", data):
                sys.exit(f"Unexpected proof placeholder or axiom in {relative}")
            obj = (Path(tmp) / relative).with_suffix(".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            log = checked(["lean", "--root=.", "-o", str(obj), str(relative)], srcroot, env)
            if "sorryAx" in log or "declaration uses 'sorry'" in log:
                sys.exit(f"Unproved declaration in {name}")
            replay = checked(["leanchecker", "-v", name], ROOT, env)
            if f"replaying {name}" not in replay.splitlines():
                sys.exit(f"No named kernel replay for {name}")
            receipt.extend([f"\n{relative.as_posix()} sha256={digest}", log.rstrip(),
                            f"lean --root=. -o <clean-build>/{relative.with_suffix('.olean').as_posix()} {relative.as_posix()} -> exit 0",
                            f"leanchecker -v {name}", replay.rstrip(), "exit 0"])
            print(f"Verified {name}", flush=True)
    if args.receipt:
        args.receipt.write_bytes(("\n".join(receipt) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
