# Presentation and Lean Game Server compatibility report

## Will the Natural Number Game layout appear after upload?

The hosted Lean Game Server supplies the shared interface. A game artifact supplies Lean code, compiled game data, text, and images; it does not install its own React client or stylesheet. Importing this game into that service therefore uses the service's interface. It cannot freeze a particular historical Natural Number Game layout. This follows from the [official framework README](https://github.com/leanprover-community/lean4game), its [client documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/client/client.md), and the separate game-artifact import implementation in the pinned runtime.

The supplied [Natural Number Game reference](https://adam.math.hhu.de/#/g/leanprover-community/nng4) was opened in the browser. It currently uses a hash-based URL and the familiar introduction, world-map, and inventory interface. Our local v4.35.0 runtime uses path-based URLs; its desktop view also displayed introduction, map, and inventory panels. The reference was observed in a smaller viewport, so that comparison does not isolate a client-version difference. Exact panel placement, editor behaviour, theme, and responsive breakpoints remain controlled by the host and player preferences, rather than a custom layout in this game's Lean files.

| Aspect | Game repository control | What is carried by the artifact |
|---|---|---|
| Welcome screen, Game Info, captions | `Introduction`, `Info`, `Title`, captions, Markdown | The authored content and formatting |
| Cover and world illustrations | `CoverImage`, `Image`, files in `images/` | The selected assets |
| World map | World registrations and prerequisite graph | Sixteen worlds and the existing dependency chain; the host lays out the graph |
| Panels, editor, menus, theme, screen-size behaviour | Shared client and player preferences | The game does not ship a replacement client |
| Hypothesis grouping | Documented `Settings (unbundleHyps := ...)` | The setting, if used; the current default is retained |

The [game-authoring documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/game/create_game.md) documents those content commands and the limited game-side UI settings. Its [Markdown guide](https://github.com/leanprover-community/lean4game/blob/main/doc/game/markdown.md) describes text and image formatting. There is no documented per-game facility here for replacing the host's complete layout with custom CSS. Editing the ignored local runtime's client would not make those edits travel with a hosted game upload.

The long prerequisite chain is deliberately preserved. Making the map branch like the NNG map would change the course dependencies, beyond this presentation-only request.

## Changes made

1. **Player-facing welcome and Game Info.** `Game.lean` now has a structured Markdown welcome, clear starting instructions, play guidance, and an accessible explanation of the special-case scope. Repository filenames are no longer presented as things players must open to begin. The generator in `scripts/write-curriculum.mjs` contains the same metadata so regeneration preserves it.
2. **Server landing tile.** The long caption now follows the documented multi-sentence format. `images/vector-calculus-cover.svg` is original, wide 500×200 artwork suited to the documented cover proportions; `CoverImage` selects it. Existing images are preserved, with the new asset's licence noted separately.
3. **Locked builds in CI.** Both workflows fetch the existing locked dependencies and Mathlib cache rather than updating dependency resolutions. They build the game and GameServer, run the Lean tests and curriculum/tactic checks, and test packaging. No Lean, Mathlib, or GameServer version was changed.
4. **Clean server-import archive.** The former blanket `.lake/` ZIP would include the locally installed web runtime, its npm dependencies, the local database, process IDs, logs, and test fixtures. `scripts/package-game.ps1` selects the actual game, assets, source, Lean dependencies, build output, configuration, and generated game data. It excludes the local web runtime and local-session data. `scripts/test-package-game.ps1` tests the manifest and a real small ZIP. `game.zip` is ignored by Git.
5. **Publishing guidance.** README.md now separates local launch from publication. This report records which appearance changes survive upload and which require the shared server client.

During that presentation-only pass, all existing level files, mathematical support, instructor proofs, hint text, stable identifiers, tactic unlocks, prerequisites, and dependency locks were preserved byte for byte. Only game-level presentation metadata and publication support changed. A subsequent, separately authorized rewrite for Natural Number Game graduates changes the level content and tactic schedule; its record is in STATUS.md. The source-language catalogue is regenerated by the normal `MakeGame` build. English remains the advertised game language; no unreviewed translations were added.

## Publication procedure, when authorized

The [official publishing guide](https://github.com/leanprover-community/lean4game/blob/main/doc/game/publish_game.md) requires a public GitHub repository and a successful build artifact, followed by importing that existing repository at [the server import page](https://adam.math.hhu.de/import). The updated main-branch workflow creates `game.zip` and uploads it as `build-for-server-import`. It does not itself deploy the game. The importer supplies the final play URL. The guide notes that a tile on the server's main page is a separate manual step handled by its maintainers.

Use the Linux GitHub Actions artifact for hosting. The native Windows checkout is for local play and verification, not a certification that its native build products can be served on Linux. Whether the deployed service currently accepts the pinned Lean 4.35.0/toolchain and API must be established by the real Linux build/import; that has not been tested by publishing.

No repository was created, no branch was pushed, no workflow was remotely triggered, and no import, upload, deployment, or maintainer message was sent.

## Verification record

The official README and its linked authoring, local-running, publishing, exercise, hint, Markdown, LaTeX, translation-maintenance, and client guides were reviewed alongside the pinned v4.35.0 implementation. Documentation examples are not treated as mandatory additions: for example, no tutorial world, custom axioms, or new language support was added.

Final local checks and browser observations are recorded in STATUS.md. A complete production-size ZIP, a GitHub Actions Linux run, and an actual hosted import are not claimed as verified by the local packaging fixture test.
