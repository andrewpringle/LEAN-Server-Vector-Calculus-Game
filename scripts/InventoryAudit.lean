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

open Lean Elab Command
run_cmd do
  let game ← GameServer.getCurGame
  let mut out : Array Json := #[]
  for (wid, world) in game.worlds.nodes.toArray do
    for (lid, level) in world.levels.toArray do
      out := out.push <| Json.mkObj [
        ("world", toJson wid.toString), ("level", toJson lid),
        ("tactics", toJson (level.tactics.used.map Name.toString)),
        ("theorems", toJson (level.theorems.used.map Name.toString)),
        ("definitions", toJson (level.definitions.used.map Name.toString))]
  IO.FS.writeFile "scripts/used-inventory.json" (Json.pretty (toJson out))
  logInfo "Wrote instructor-proof inventory for the 96 compiled levels."
