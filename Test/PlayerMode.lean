import Game
import GameServer

/-! The real player runner at strict difficulty: theorem tools must be unlocked,
and the player receives the exercise goal rather than the instructor proof. -/
Runner "MyGame" "GaussCitadel" 4 (difficulty := 2) (inventory := []) := by
  apply gauss_diagonal
