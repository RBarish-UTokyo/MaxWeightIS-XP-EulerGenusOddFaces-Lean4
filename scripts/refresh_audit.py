"""Refresh imports and enumerate public declarations from Lean build metadata."""

import argparse
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--built-only", action="store_true",
        help="For intermediate checks, import only modules with existing build objects.",
    )
    args = parser.parse_args()
    sources = sorted((ROOT / "WeightedMIS").rglob("*.lean"))
    selected = [
        p for p in sources
        if not args.built_only or (
            ROOT / ".lake/build/lib/lean" / p.relative_to(ROOT).with_suffix(".olean")
        ).is_file()
    ]
    if not selected:
        raise RuntimeError("No source modules selected")
    imports = [".".join(p.relative_to(ROOT).with_suffix("").parts) for p in selected]
    (ROOT / "WeightedMIS.lean").write_text(
        "module\n\n" + "".join(f"public import {name}\n" for name in imports)
    )
    output = ROOT / "verification"
    output.mkdir(exist_ok=True)
    with (output / "refresh-build.txt").open("w") as log:
        subprocess.run(["lake", "build", "WeightedMIS"], cwd=ROOT, stdout=log,
                       stderr=subprocess.STDOUT, check=True)
    names = set()
    for source in selected:
        metadata = ROOT / ".lake/build/lib/lean" / source.relative_to(ROOT).with_suffix(".ilean")
        declarations = json.loads(metadata.read_text())["decls"]
        names.update(name for name in declarations if name.startswith("WeightedMIS."))
    names = sorted(names)
    if not names:
        raise RuntimeError("Lean metadata did not report any public project declarations")
    (ROOT / "Audit.lean").write_text(
        "module\n\n"
        "import WeightedMIS\n\n"
        "/-! Transitive axiom dependencies of the public project declarations. -/\n\n"
        + "".join(f"#print axioms {name}\n" for name in names)
    )
    (output / "audit-coverage.json").write_text(json.dumps({
        "imported_modules": imports,
        "omitted_sources": [str(p.relative_to(ROOT)) for p in sources if p not in selected],
        "public_declaration_count": len(names),
        "full_source_coverage": len(selected) == len(sources),
    }, indent=2) + "\n")
    print(f"Imported {len(imports)} modules; enumerated {len(names)} public declarations.")


if __name__ == "__main__":
    main()
