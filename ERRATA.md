# Errata

Errors found in the plan and in the sources it cites while formalizing them,
and what the library does about each. `AGENTS.md` says when to add an entry.

There is a section for each page of the plan, in the plan's order, headed
with the page's path in the atlas, such as
`## atlas/01-local-properties.md`, and `## Other sources` last, for errors in sources that no page covers. Add a
missing section in its place in that order. Within a section, entries go in
alphabetical order of their titles, with a blank line between them, so that
two pull requests conflict only when their entries land in the same place.

Each entry has this form:

```markdown
### <A short title>

- **Where:** the plan's page and milestone, or the source and its location.
- **Error:** what it says, quoted, and why that is wrong: a counterexample,
  or the step that is false or does not follow.
- **Fix:** what the library proves instead, or the route it takes, naming the
  declarations.
  Or, while there is none, **Unresolved:** the routes tried, and where each
  failed.
- **Issue:** #<number>.
```

## auxiliary/affine-varieties.md

### Dimension of k[X]/I^m with no variables and m = 0

- **Where:** `auxiliary/affine-varieties.md`, milestone *Dimensions of spaces of forms and of
  polynomials modulo a power of the ideal of a point*, part (c).
- **Error:** it says "$\dim_k k[X_1,\dots,X_n]/I^m = \binom{m+n-1}{n}$" for every `m` and `n`.
  For `n = 0` and `m = 0` the quotient is $k/k = 0$, but $\binom{-1}{0} = 1$ (and in `ℕ`,
  `(0 + 0 - 1).choose 0 = 1`). Fulton always has `n ≥ 1`, and every other case is right.
- **Fix:** `MvPolynomial.finrank_quotient_pow_vanishingIdeal_singleton` and
  `MvPolynomial.finrank_quotient_pow_idealOfVars` assume `m ≠ 0 ∨ Nonempty σ`; an `example`
  next to the milestone shows the hypothesis is needed.
  `MvPolynomial.finrank_quotient_pow_idealOfVars_succ` states the formula for `I ^ (m + 1)`
  without a hypothesis.
- **Issue:** #22.

## atlas/01-local-properties.md

## auxiliary/projective-varieties.md

## atlas/02-projective-plane-curves.md

## auxiliary/varieties-and-rational-maps.md

## atlas/03-resolution-of-singularities.md

## atlas/04-riemann-roch.md

## Other sources
