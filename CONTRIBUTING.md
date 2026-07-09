# Contributing

This repository is a small Lean formalization accompanying a paper. Changes
should preserve the public-facing scope of the package: the repository contains
the Lean artifact and project metadata, not manuscript drafts or render output.

Before opening a pull request, run:

```sh
lake build --wfail
```

Do not commit generated Lake output, local scratch files, paper drafts, or PDF
render artifacts.
