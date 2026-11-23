import Game.Levels.Vectors
import Game.Levels.SpaceExplorer
import Game.Levels.CurveNavigator
import Game.Levels.MultivariableLandscapes
import Game.Levels.PartialDerivativeLab
import Game.Levels.GradientMountain
import Game.Levels.OptimizationArena
import Game.Levels.DoubleIntegralValley
import Game.Levels.TripleIntegralCaverns
import Game.Levels.CoordinatePortal
import Game.Levels.VectorFieldObservatory
import Game.Levels.PathIntegralTrails
import Game.Levels.GreensGarden
import Game.Levels.SurfaceExpedition
import Game.Levels.StokesSummit
import Game.Levels.GaussCitadel

Title "Vector Calculus in Lean"
Introduction "# Welcome to Vector Calculus in Lean\n\n### A Calculus III proof adventure\n\nExplore vectors, curves, multivariable derivatives, multiple integrals, and vector integral theorems across **16 worlds and 96 challenges**.\n\n## Start here\n\nChoose **Vector Workshop** on the world map, then open **Coordinates**. Each world has six levels; its final level brings the earlier ideas together.\n\n## Before you begin\n\nYou should have completed the Natural Number Game and studied single-variable calculus. New calculus notation and a small set of additional tactics are explained where you need them.\n\n## Playing a level\n\nRead the objective, inspect the goal, and enter a tactic. The inventory explains the tools you have unlocked. Use the progressive hints when you need a nudge. **Regular** game rules enforce the unlock sequence.\n\n## The final worlds\n\nThe integral-theorem challenges use explicitly stated, fully proved special cases. Each level tells you which result applies and what it establishes."
Conclusion "You have completed 96 vector calculus proofs, from coordinates to justified integral-theorem special cases."
Info "## About this game\n\nOriginal vector-calculus exercises aligned with [OpenStax Calculus Volume 3](https://openstax.org/books/calculus-volume-3/pages/preface). Proofs use Lean 4 and Mathlib.\n\n## Mathematical scope\n\nThe later worlds include proved special-case families for Green, Stokes, and Gauss, and verified coordinate-side integration examples. They are labeled as special cases rather than proofs of the general integral theorems.\n\n## Project and references\n\n[Game repository](https://github.com/andrewpringle/LEAN-Server-Vector-Calculus-Game) · [Lean4Game framework](https://github.com/leanprover-community/lean4game)\n\nThe repository contains the curriculum map, source references, verification status, and full tactic-unlock schedule."
Languages "en"
CaptionShort "Calculus III, proved in Lean"
CaptionLong "Explore vectors, curves, multivariable derivatives, multiple integrals, and vector integral theorems through 96 proof challenges. Completion of the Natural Number Game and single-variable calculus are assumed. Advanced integral-theorem challenges use explicitly labeled, fully proved special cases."
CoverImage "images/vector-calculus-cover.svg"

Dependency Vectors → SpaceExplorer → CurveNavigator → MultivariableLandscapes → PartialDerivativeLab → GradientMountain → OptimizationArena → DoubleIntegralValley → TripleIntegralCaverns → CoordinatePortal → VectorFieldObservatory → PathIntegralTrails → GreensGarden → SurfaceExpedition → StokesSummit → GaussCitadel

MakeGame
