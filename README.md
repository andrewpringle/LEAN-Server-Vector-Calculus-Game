# Vector Calculus in Lean

This existing Lean4Game repository contains 16 registered worlds, six levels each. Players should have completed the Natural Number Game and studied single-variable calculus. The 96 levels introduce the additional Lean tools inside calculus exercises, with worked examples in the first two levels of each world. See [CURRICULUM.md](CURRICULUM.md), [SOURCES.md](SOURCES.md), and [STATUS.md](STATUS.md) for the curriculum, references, and verification/special-case scope.

Framework documentation is maintained at the [lean4game repository](https://github.com/leanprover-community/lean4game/):

- [Updating an existing game](https://github.com/leanprover-community/lean4game/blob/main/doc/game/update_game.md)
- [Running a game locally](https://github.com/leanprover-community/lean4game/blob/main/doc/game/running_locally.md)

## Quick start

On this Windows checkout, run:

```powershell
.\scripts\start-local-game.ps1
```

Then open the local game URL printed by the script. It starts the existing Lean4Game browser client on port 3000 and the proof server on port 8000, both bound to this computer. Node.js, npm, Git, and the pinned Lean toolchain must be available. On the first run it downloads the matching official `lean4game` v4.35.0 runtime and its locked npm dependencies into the ignored `.lake/leangame-runtime` folder. It uses this same game's compiled files; no second game project is created. Runtime logs and process IDs are in `.lake/local-game/`. Leave the background processes running while playing. The first level can take a short time to initialize Lean before its tactic box becomes available.

The runtime's sibling-folder discovery is given an explicit local games directory so the downloaded dependency can stay inside `.lake`. This small adjustment applies only to the ignored runtime checkout. No game dependency versions are changed.

Alternatively, use the existing development container:

- Open this existing checkout in VSCode. Do not create another repository.
- `Ctrl + Shift + P` and enter `Dev Containers: Reopen in Container`
- The server starts automatically, once it's started you should be able to play your game at http://localhost:3000.

## Build and verify

Install elan and Git. Keep `lean-toolchain` and `lake-manifest.json`: Lean 4.35.0 and compatible Mathlib/GameServer revisions are pinned. From this checkout:

```sh
lake exe cache get
lake build
lake build GameServer
lake test
node scripts/check-curriculum.mjs
```

The initial Mathlib cache extraction can take several minutes on Windows. Do not run `lake update` just to build: it can change locked versions. This curriculum requires no dependency changes.

The Lean test target explicitly includes the verification and player-runner tests. The existing hidden `.sofi-test-folders` files are shell-script fixtures containing deliberately invalid Lean and are preserved outside that target.

The existing development container builds the game and starts the existing Lean4Game client on port 3000. Open the local URL printed by `.devcontainer/start-server.sh`; its route includes `/g/local/` and the checkout folder name. That shell script expects the container's sibling `/workspaces/leangame` installation; the native Windows launcher is `scripts/start-local-game.ps1`. After edits, run `lake build` and refresh the browser. No publishing step is needed.

## Publishing and appearance

The Lean Game Server supplies the shared layout used by its hosted games, including the Natural Number Game. This repository supplies the game's text, images, world graph, and supported display settings; local client/CSS edits are not shipped as game customizations. See [HOSTING_REPORT.md](HOSTING_REPORT.md) for the comparison, documentation audit, and changes made.

When you decide to publish, use this existing repository and its successful Linux GitHub Actions build. The main-branch workflow creates a `build-for-server-import` artifact containing `game.zip`; then follow the [official import procedure](https://github.com/leanprover-community/lean4game/blob/main/doc/game/publish_game.md). A main-page listing is arranged separately with the server maintainers. Nothing is uploaded by the local launch or packaging scripts.

For local archive inspection with PowerShell 7:

```powershell
./scripts/package-game.ps1 -ListOnly
./scripts/test-package-game.ps1
```

The packager excludes `.lake/leangame-runtime`, `.lake/local-game`, and `.lake/validation`, while retaining the Lean dependencies, build files, generated game data, and assets required by the importer. Create a full archive with `./scripts/package-game.ps1` only when needed; the native Windows archive is not a substitute for the Linux CI artifact.

## Review and author

Tactics unlock progressively using the framework's `NewTactic` declarations. Nine familiar NNG tools are available initially; five additional tools unlock gradually. All 96 intended solutions use only these 14 tactics. [TACTIC_UNLOCKS.md](TACTIC_UNLOCKS.md) lists the schedule. **Game Rules → Regular** enforces locks; Relaxed mode warns, and No Rules intentionally permits every tool. Existing progress is preserved. Older saves may retain previously earned tactics, and a revised statement can require revisiting a saved proof. Use a separate browser profile to try the new progression without erasing an existing save.

* `Game.lean`: root imports, metadata, prerequisite chain, `MakeGame`.
* `Game/Levels/<World>.lean`: six level imports and world description.
* `Game/Levels/<World>/L*.lean`: objective, prerequisites, explanation, formal exercise, three hints, instructor proof, interpretation.
* `Game/Calculus.lean`: Mathlib-based coordinate derivatives and integrals; proved infrastructure. `Game/Coordinates.lean` and `Game/PathLimits.lean` supply Jacobian and punctured-path support.
* `Game/Advanced.lean`: explicitly oriented boundary integrals and proved restricted theorem families.
* `Game/Rules.lean`: proved coordinate comparison, derivative, continuity, limit, and integral rules that keep library implementation details out of player proofs. Its readable limit and regularity names abbreviate the actual underlying conditions.
* `scripts/curriculum-levels.json`: canonical source for all 96 exercises, explanations, hints, and intended proofs. Edit it and run `node scripts/write-curriculum.mjs` to regenerate the Lean levels and curriculum map. The renderer also maintains registration, inventory documentation, and first-use unlocks. Edit shared Lean modules directly. After compiling changed proofs, run `lake env lean scripts/InventoryAudit.lean`, regenerate again, and rebuild to refresh the compiler-derived inventory in `scripts/used-inventory.json`.

Instructor proofs use the existing `Statement ... := by` mechanism and are not prefilled into player editors. Every statement has an explicit unique name so the GameServer runner rejects reuse of the current exercise theorem. Earlier completed levels are handled by the framework. The first hint is visible; the next two are revealable progressive hints for the initial proof state. Unregistered HelloWorld template files remain preserved; no tutorial world is imported.

Vectors retain `Fin 3 → ℝ`. Euclidean lengths use the coordinate dot product, not the Pi type's library norm. Coordinate partial derivatives use scalar `deriv`; total directional derivatives use `fderiv`. Arc lengths use ordered parameter bounds and regular examples. Advanced levels clearly distinguish direct special-case verification from a general integral theorem.
