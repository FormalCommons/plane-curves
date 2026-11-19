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

### Residual intersection corollary for a constant F

- **Where:** `atlas/02-projective-plane-curves.md`, milestone *Local criteria for Noether's
  conditions and the residual intersection corollary*, the Corollary, read with the page's
  convention that results are stated "for nonzero forms of any degree $d\ge0$".
- **Error:** it says "Let $F,G,H$ be forms with $F,G$ and $F,H$ without common components. If
  either (1) $V(F)\cap V(G)$ consists of $\deg F\cdot\deg G$ distinct points and $H$ vanishes at
  all of them, or (2) every point of $V(F)\cap V(G)$ is a simple point of $F$ and
  $H\bullet F\ge G\bullet F$, then there is a form $B$ of degree $\deg H-\deg G\ge0$". For the
  constant $F = 1$, $G = X$ and $H = 1$, $V(F)\cap V(G)$ is empty, so it has
  $0 = \deg F\cdot\deg G$ points, $H$ vanishes at all of them, every one is simple on $F$, and
  $H\bullet F = 0 = G\bullet F$; but $\deg H-\deg G = -1$. Fulton's curves are nonconstant, so
  the book needs no correction.
- **Fix:** the Corollary assumes $\deg F > 0$:
  `PlaneCurves.Projective.exists_isHomogeneous_intersectionCycle_eq_sub_of_card_eq_mul`,
  `PlaneCurves.Projective.exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint` and
  `PlaneCurves.Projective.noetherConditionsAt_of_intersectionNumber_eq_one_spec` take
  `0 < d`, and `PlaneCurves.Projective.exists_isHomogeneous_zero_and_not_le` is the
  counterexample. $G$, $H$ and $B$ may still be constants.
- **Issue:** #349.

## auxiliary/varieties-and-rational-maps.md

## atlas/03-resolution-of-singularities.md

### Blow-up of ℙ² at the ordinary multiple points stated through the nonsingular model

- **Where:** `atlas/03-resolution-of-singularities.md`, §7.3, milestone *Resolution of a plane
  curve with only ordinary multiple points by blowing up*.
- **Error:** it says "Let $B \subseteq \mathbb{P}^2 \times (\mathbb{P}^1)^t$ be the blow-up of
  $\mathbb{P}^2$ at $P_1, \dots, P_t$ … and $C'$ the closure in $B$ of
  $\pi^{-1}(C \setminus \{P_1, \dots, P_t\})$". This is not a false statement but one the plan
  gives no means to state: $B$ is a multiprojective variety, which the plan defers (the page's
  formalization note: "Fulton's construction needs multiprojective varieties and the Segre
  embedding"), so the library has no $B$ and no closure in it.
- **Fix:** as `DESIGN.md` (departure 7) and the page's recommended route say, $C'$ is the
  nonsingular model of $C$, the places of $k(C)$, and $f$ is the centre map.
  `PlaneCurves.Projective.center_spec_of_isOrdinaryMultiplePoint` proves every conclusion for
  it: finitely many multiple points, every local ring of $C'$ a discrete valuation ring, $f$
  onto, exactly one place with valuation ring $\mathcal{O}_P(C)$ over every other point
  (`centerEquivSimplePoints`), and over each $P_i$ exactly $m_{P_i}(C)$ places in bijection with
  the tangents (`placesOverEquivTangents`). That $C'$ is the closure in $B$ is not proved.
- **Issue:** #109.

## atlas/04-riemann-roch.md

## Other sources
