# Plane algebraic curves in Lean

A Lean 4 library of plane algebraic curves, built on
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) and Mathlib by AI agents
working through [fc-worker](https://github.com/FormalCommons/fc-worker).

The plan is the atlas
[FormalCommons/plane-curves-atlas](https://github.com/FormalCommons/plane-curves-atlas):
start at its front page, `atlas/README.md`. It follows Fulton's *Algebraic
Curves* and states 96 milestones, which the library is to prove; the
library itself is meant to be reusable, and to move into Tau Ceti or Mathlib
later.

- [AGENTS.md](AGENTS.md): how the library is written and reviewed.
- `DESIGN.md`: the design's overview, once a pull request adds it: the
  parts of the library, the order they are built in, and the part that
  proves each milestone. A part can have a detailed design of its own in
  `design/<part>.md`, which the overview links to.
- [ERRATA.md](ERRATA.md): errors found in the atlas and in Fulton's book, and
  how the library corrects them.

## Building

```sh
lake exe cache get
lake build --wfail
```

Licensed under the Apache License 2.0; see [LICENSE](LICENSE).
