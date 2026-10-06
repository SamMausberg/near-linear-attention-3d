#!/usr/bin/env python3
"""Build the paper in an isolated directory and install complete outputs.

Only Python's standard library is required in addition to pdfLaTeX and BibTeX.
Temporary TeX files never share an output name with a delivered document.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent
SOURCES = (
    "paper.tex", "references.bib", "plainurl.bst",
    "lipics-v2021.cls", "socg-lipics-v2021.cls",
)


def install(name: str, contents: bytes) -> None:
    """Atomically replace one output after flushing its complete contents."""
    fd, temporary = tempfile.mkstemp(prefix=".attention-build-", dir=ROOT)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(contents)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, ROOT / name)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def read_pdf(path: Path) -> bytes:
    contents = path.read_bytes()
    if not contents.startswith(b"%PDF-") or not contents.rstrip().endswith(b"%%EOF"):
        raise RuntimeError(f"TeX did not produce a complete PDF: {path.name}")
    return contents


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--latex", default="pdflatex")
    parser.add_argument("--bibtex", default="bibtex")
    args = parser.parse_args()
    transcript: list[bytes] = []
    outputs: dict[str, bytes] = {}

    with tempfile.TemporaryDirectory(prefix="attention-tex-") as directory:
        stage = Path(directory)
        for name in SOURCES:
            shutil.copyfile(ROOT / name, stage / name)

        def run(command: list[str]) -> None:
            result = subprocess.run(
                command, cwd=stage, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, check=False,
            )
            transcript.append(("$ " + shlex.join(command) + "\n").encode())
            transcript.append(result.stdout)
            if result.returncode:
                install("build.log", b"\n".join(transcript))
                raise RuntimeError(
                    f"Build command failed ({result.returncode}); see build.log"
                )

        def latex(source: str, job: str) -> None:
            run(shlex.split(args.latex) + [
                "-interaction=nonstopmode", "-halt-on-error",
                "-file-line-error", f"-jobname={job}", source,
            ])

        main_job = "attention_document"
        latex("paper.tex", main_job)
        run(shlex.split(args.bibtex) + [main_job])
        latex("paper.tex", main_job)
        latex("paper.tex", main_job)
        outputs["paper.pdf"] = read_pdf(stage / f"{main_job}.pdf")
        outputs["paper.bbl"] = (stage / f"{main_job}.bbl").read_bytes()

    # Preserve the earlier outputs if the compilation fails.
    for name, contents in outputs.items():
        install(name, contents)
    install("build.log", b"\n".join(transcript))
    read_pdf(ROOT / "paper.pdf")
    print("Built paper.pdf; transcript: build.log")


if __name__ == "__main__":
    main()
