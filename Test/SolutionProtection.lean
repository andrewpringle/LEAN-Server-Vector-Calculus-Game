import Game
import GameServer

/-! The default-difficulty setting still rejects direct reuse of the current
instructor theorem. This tests the actual framework guard, not a text scan. -/
/-- error: Structural recursion: you can't use 'exercise_Vectors_1' to proof itself! -/
#guard_msgs in
Runner "MyGame" "Vectors" 1 (difficulty := 0) (inventory := []) := by
  exact exercise_Vectors_1
