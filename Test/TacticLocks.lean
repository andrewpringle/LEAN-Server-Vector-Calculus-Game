import Game
import GameServer

/-! Locks must affect actual proof checking, not just inventory colours. -/
/-- error: You have not unlocked the tactic 'norm_num' yet! -/
#guard_msgs in
Runner "MyGame" "Vectors" 1 (difficulty := 2) (inventory := []) := by
  norm_num

open Lean Elab Command

-- The same tool is accepted in its introducing level without earned inventory.
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `Vectors, level := 2} [] 2
    (← `(tactic| norm_num))

/-- error: You have not unlocked the tactic 'ring' yet! -/
#guard_msgs in
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `Vectors, level := 1} [] 2
    (← `(tactic| ring))

run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `PartialDerivativeLab, level := 2} [] 2
    (← `(tactic| ring))

/-- error: You have not unlocked the tactic 'constructor' yet! -/
#guard_msgs in
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `Vectors, level := 3} [] 2
    (← `(tactic| constructor))

run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `Vectors, level := 4} [] 2
    (← `(tactic| constructor))

/-- error: You have not unlocked the tactic 'linarith' yet! -/
#guard_msgs in
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `SpaceExplorer, level := 1} [] 2
    (← `(tactic| linarith))

run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `SpaceExplorer, level := 2} [] 2
    (← `(tactic| linarith))

/-- error: You have not unlocked the tactic 'simp' yet! -/
#guard_msgs in
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `SpaceExplorer, level := 4} [] 2
    (← `(tactic| simp))

run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `SpaceExplorer, level := 5} [] 2
    (← `(tactic| simp))

/-- error: You have not unlocked the tactic 'ring' yet! -/
#guard_msgs in
run_cmd do
  GameServer.findForbiddenTactics
    {game := `MyGame, world := `PartialDerivativeLab, level := 1} [] 2
    (← `(tactic| ring))
