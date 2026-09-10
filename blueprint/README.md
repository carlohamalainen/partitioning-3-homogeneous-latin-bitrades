# Blueprint

LaTeX source for the [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
version of the formalisation. `src/content.tex` restates the paper's
definitions and lemmas; each one is tagged with the Lean declaration(s) that
formalise it (`\lean{...}`), whether it is done (`\leanok`), and what it
depends on (`\uses{...}`). plasTeX turns that into HTML with MathJax and a
clickable dependency graph; latexmk turns it into a PDF.

## Build

Install the tool once with uv:

    uv tool install leanblueprint

The web build shells out to `plastex`, which uv installs inside the tool's
own environment without exposing it on PATH, so add that directory first:

    export PATH="$(uv tool dir)/leanblueprint/bin:$PATH"

Then, from the repository root:

    leanblueprint web    # HTML + dependency graph  -> blueprint/web/index.html
    leanblueprint pdf    # PDF via latexmk/xelatex  -> blueprint/print/print.pdf
    leanblueprint serve  # serve blueprint/web on http://localhost:8000

The build outputs (`web/`, `print/`, `lean_decls`) are git-ignored.

## Not yet wired up

- `leanblueprint checkdecls` verifies every `\lean{}` name against the
  compiled project. It needs the `checkdecls` package added to
  `lakefile.toml`. Until then, a scratch file of `#check` lines does the
  same job.
- The `\lean{}` links point at doc-gen4 API pages under `\dochome`, which
  are not generated yet. `leanprover-community/docgen-action` can build
  doc-gen4, the blueprint, and deploy both to GitHub Pages.

Proofs go after `\end{theorem}`, not inside it; the dependency-graph
plugin attaches a proof to the environment that precedes it.
