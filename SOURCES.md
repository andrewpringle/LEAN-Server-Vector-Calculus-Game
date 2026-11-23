# Curriculum references

Scope reference: Gilbert Strang and Edwin “Jed” Herman, *Calculus Volume 3*, OpenStax (2016), [preface](https://openstax.org/books/calculus-volume-3/pages/preface). All explanations, examples, exercises, and proofs in this game are original. This is a section mapping, not a reproduction of textbook exercises or prose.

| World | Relevant OpenStax sections |
|---|---|
| Vector Workshop | [2.2 Vectors in Three Dimensions](https://openstax.org/books/calculus-volume-3/pages/2-2-vectors-in-three-dimensions), [2.3 Dot Product](https://openstax.org/books/calculus-volume-3/pages/2-3-the-dot-product), [2.4 Cross Product](https://openstax.org/books/calculus-volume-3/pages/2-4-the-cross-product) |
| Space Explorer | [2.5 Lines and Planes](https://openstax.org/books/calculus-volume-3/pages/2-5-equations-of-lines-and-planes-in-space), [2.6 Quadric Surfaces](https://openstax.org/books/calculus-volume-3/pages/2-6-quadric-surfaces) |
| Curve Navigator | [3.1 Vector-Valued Functions](https://openstax.org/books/calculus-volume-3/pages/3-1-vector-valued-functions-and-space-curves), [3.2 Calculus of Vector-Valued Functions](https://openstax.org/books/calculus-volume-3/pages/3-2-calculus-of-vector-valued-functions), [3.3 Arc Length and Curvature](https://openstax.org/books/calculus-volume-3/pages/3-3-arc-length-and-curvature), [3.4 Motion in Space](https://openstax.org/books/calculus-volume-3/pages/3-4-motion-in-space) |
| Multivariable Landscapes | [4.1 Functions of Several Variables](https://openstax.org/books/calculus-volume-3/pages/4-1-functions-of-several-variables), [4.2 Limits and Continuity](https://openstax.org/books/calculus-volume-3/pages/4-2-limits-and-continuity) |
| Partial Derivative Lab | [4.3 Partial Derivatives](https://openstax.org/books/calculus-volume-3/pages/4-3-partial-derivatives), [4.4 Tangent Planes and Linear Approximations](https://openstax.org/books/calculus-volume-3/pages/4-4-tangent-planes-and-linear-approximations) |
| Gradient Mountain | [4.5 Chain Rule](https://openstax.org/books/calculus-volume-3/pages/4-5-the-chain-rule), [4.6 Directional Derivatives and Gradient](https://openstax.org/books/calculus-volume-3/pages/4-6-directional-derivatives-and-the-gradient) |
| Optimization Arena | [4.7 Maxima/Minima Problems](https://openstax.org/books/calculus-volume-3/pages/4-7-maxima-minima-problems), [4.8 Lagrange Multipliers](https://openstax.org/books/calculus-volume-3/pages/4-8-lagrange-multipliers) |
| Double Integral Valley | [5.1 Rectangular Regions](https://openstax.org/books/calculus-volume-3/pages/5-1-double-integrals-over-rectangular-regions), [5.2 General Regions](https://openstax.org/books/calculus-volume-3/pages/5-2-double-integrals-over-general-regions), [5.6 Centers of Mass and Moments](https://openstax.org/books/calculus-volume-3/pages/5-6-calculating-centers-of-mass-and-moments-of-inertia) |
| Triple Integral Caverns | [5.4 Triple Integrals](https://openstax.org/books/calculus-volume-3/pages/5-4-triple-integrals), [5.6 Centers of Mass and Moments](https://openstax.org/books/calculus-volume-3/pages/5-6-calculating-centers-of-mass-and-moments-of-inertia) |
| Coordinate Portal | [5.3 Polar Integrals](https://openstax.org/books/calculus-volume-3/pages/5-3-double-integrals-in-polar-coordinates), [5.5 Cylindrical and Spherical Coordinates](https://openstax.org/books/calculus-volume-3/pages/5-5-triple-integrals-in-cylindrical-and-spherical-coordinates), [5.7 Change of Variables](https://openstax.org/books/calculus-volume-3/pages/5-7-change-of-variables-in-multiple-integrals) |
| Vector Field Observatory | [6.1 Vector Fields](https://openstax.org/books/calculus-volume-3/pages/6-1-vector-fields), [6.5 Curl and Divergence](https://openstax.org/books/calculus-volume-3/pages/6-5-curl-and-divergence) |
| Path Integral Trails | [6.2 Line Integrals](https://openstax.org/books/calculus-volume-3/pages/6-2-line-integrals), [6.3 Conservative Vector Fields](https://openstax.org/books/calculus-volume-3/pages/6-3-conservative-vector-fields) |
| Green’s Garden | [6.4 Green’s Theorem](https://openstax.org/books/calculus-volume-3/pages/6-4-greens-theorem) |
| Surface Expedition | [6.6 Surface Integrals](https://openstax.org/books/calculus-volume-3/pages/6-6-surface-integrals) |
| Stokes Summit | [6.7 Stokes’ Theorem](https://openstax.org/books/calculus-volume-3/pages/6-7-stokes-theorem) |
| Gauss Citadel | [6.8 Divergence Theorem](https://openstax.org/books/calculus-volume-3/pages/6-8-the-divergence-theorem) |

## Formal foundations

The Lean learning baseline is completion of the [Natural Number Game](https://github.com/leanprover-community/NNG4), including its [registered worlds](https://github.com/leanprover-community/NNG4/blob/main/Game.lean). This game does not copy NNG exercises or reintroduce a tutorial world. All explanations and worked examples here are original. `Game/Rules.lean` provides proved mathematical interfaces for the additional calculus notation and methods.

Mathlib revision: `56a005855ea17e0b0958f73ec801ae140b0a1679`. The paths below are relative to `.lake/packages/mathlib/Mathlib/` after dependency fetch.

* `Analysis/Calculus/Deriv/`: scalar derivatives and chain rule.
* `Analysis/Calculus/FDeriv/Pi.lean`: total derivatives of projections and Pi-valued maps.
* `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`: `integral_eq_sub_of_hasDerivAt`, `integral_deriv_eq_sub`.
* `Analysis/SpecialFunctions/Integrals/Basic.lean`: polynomial and trigonometric antiderivatives.
* `MeasureTheory/Function/Jacobian.lean`: general `integral_image_eq_integral_abs_det_fderiv_smul`; available, but not claimed as applied by coordinate-side exercises.
* `MeasureTheory/Integral/DivergenceTheorem.lean`: box theorem `integral_divergence_of_hasFDerivAt_off_countable` and planar `integral2_divergence_prod_of_hasFDerivAt`; available foundations. The game uses its own explicitly proved restricted diagonal/shear families.
* `Analysis/BoxIntegral/DivergenceTheorem.lean`: box-integral foundations. A Stokes keyword there does not supply a general parametrized-surface Stokes interface.

GameServer revision: `43fd5128c775ca2385727b9423cc2f7272d0c55e`. Existing solution handling: `GameApi/Commands/Statement.lean`; hints: `GameApi/Tactic/Hint.lean`; current-statement reuse check: `GameServer/Runner.lean`.
