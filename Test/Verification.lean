import Game
import Lean.Util.CollectAxioms

/-! Kernel-dependency audit of every registered instructor solution and support fact.
The three foundational Lean axioms below are standard. No unfinished proof or
custom mathematical assumption is allowed in the dependency closure. -/
open Lean Elab Command

run_cmd do
  let game ← GameServer.getCurGame
  unless game.worlds.nodes.size == 16 do
    throwError "Expected exactly 16 registered worlds"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let learnerTactics : Array Name := #[`apply, `exact, `have, `intro, `rfl, `rw,
    `use, `left, `right, `constructor, `norm_num, `linarith, `simp, `ring]
  let mut count := 0
  for (_, world) in game.worlds.nodes.toArray do
    unless world.levels.size == 6 do
      throwError "Every world must contain exactly six levels"
    for (_, level) in world.levels.toArray do
      count := count + 1
      unless level.hints.size == 3 do
        throwError "Expected three hints in {level.statementName}"
      if level.statementName.isAnonymous then
        throwError "Exercises must be named to activate the runner's self-reference check"
      for item in level.theorems.used do
        unless level.theorems.tiles.any (fun tile =>
            tile.name == item && !tile.locked && !tile.disabled) do
          throwError "Unavailable theorem {item} in {level.statementName}"
      for item in level.definitions.used do
        unless level.definitions.tiles.any (fun tile =>
            tile.name == item && !tile.locked && !tile.disabled) do
          throwError "Unavailable definition {item} in {level.statementName}"
      for item in level.tactics.used do
        unless learnerTactics.contains item || item == `in do
          throwError "Advanced tactic {item} in {level.statementName}"
        unless level.tactics.tiles.any (fun tile =>
            tile.name == item && !tile.locked && !tile.disabled) do
          throwError "Unavailable tactic {item} in {level.statementName}"
      for ax in (← Lean.collectAxioms level.statementName) do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in {level.statementName}"
  unless count == 96 do throwError "Expected 96 playable levels"
  for (name, _) in (← getEnv).constants.toList do
    if (`VectorCalculus).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do throwError "Disallowed axiom {ax} in {name}"
  logInfo "PASS: 16 worlds, 96 solutions, 14 tactics, three hints per level, and only standard foundational axioms in every shared declaration."
