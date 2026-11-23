# Tactic progression

Completion of the Natural Number Game and single-variable calculus are assumed. Nine familiar tactics are available initially. Five more tools unlock gradually: `norm_num`, `constructor`, `linarith`, `simp`, and `ring`. All 96 intended solutions use only these 14 tactics, with explicit mathematical intermediate steps. There is no Lean tutorial world. A new tactic is usable in its introducing level; completing that level adds it to the earned inventory. General support proofs may use additional tactics, but players do not need them.

Use **Game Rules → Regular** to enforce locks. Relaxed mode warns; No Rules deliberately bypasses locks. Existing completed proofs and inventories are preserved, so an older save can retain previously earned tools. Revised statements may require revisiting an old proof; use a separate browser profile to try a fresh progression without erasing your save.

| First available | Newly available tactics |
|---|---|
| Vector Workshop, level 1: Coordinates | `apply`, `exact`, `have`, `intro`, `left`, `rfl`, `right`, `rw`, `use` |
| Vector Workshop, level 2: Adding and scaling | `norm_num` |
| Vector Workshop, level 4: Orthogonality and length | `constructor` |
| Space Explorer, level 2: A plane from a normal | `linarith` |
| Space Explorer, level 5: A paraboloid and its traces | `simp` |
| Partial Derivative Lab, level 2: Hold x fixed | `ring` |
