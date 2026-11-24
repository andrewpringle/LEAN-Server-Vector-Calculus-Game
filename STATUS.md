## Lean 4.36.0 upgrade — 2026-11-24

The existing game now targets `leanprover/lean4:v4.36.0`. Mathlib is locked to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and GameServer to `d35ca713145fdce6d7b0bc450e64295b36ae38f5`, with their compatible transitive dependencies in `lake-manifest.json`. This dependency update is required for the toolchain upgrade requested by the server maintainer in [issue #634](https://github.com/leanprover-community/lean4game/issues/634).

The lakefile was refreshed from the current official [GameSkeleton](https://github.com/leanprover-community/lean4game/tree/main/GameSkeleton), retaining Mathlib and this game's five test modules. Its default target now includes GameServer and image/translation inputs. The container setup was compared with the current template and remains compatible; Docker itself was not executed. CI retains the committed dependency lock, game tests, and allowlisted ZIP packaging, and points to the maintainer-requested [development importer](https://adam-dev.math.hhu.de/import). The native launcher selects the matching official runtime version from `lean-toolchain` into a versioned ignored directory.

All 96 level statements, instructor proofs, explanations, hints, world descriptions, root metadata, tactic schedule, and cover artwork remain unchanged. A SHA-256 comparison checked 120 preserved curriculum and presentation inputs. No mathematical support code or frontend styling changed. The regenerated English catalogue changes only its Lean-version header and creation date.

| Executed local check with Lean 4.36.0 | Result |
|---|---|
| `lake update -R --keep-toolchain` | Passed; matching release dependencies and 9,117 cached files downloaded and extracted. |
| `lake build` | Passed, 6,073 jobs, including all 96 instructor solutions, 16 world imports, root game, and GameServer. |
| `lake test` | Passed all five test modules, including the axiom audit and every intended proof through the strict player runner. |
| `lake build --no-build` | Passed; all 6,073 jobs up to date. |
| `lake build GameServer --no-build` | Passed; all 73 jobs up to date. |
| `node scripts/check-curriculum.mjs` | Passed 16/96 registration, prerequisites, reachability, blank templates, hints, and all 1,344 visible tactic lock states. |
| `pwsh -File scripts/test-package-game.ps1` | Passed real ZIP fixture; both old and versioned local runtimes excluded. |
| Official v4.36.0 local runtime on ports 3001/8001 | Passed HTTP checks of all 96 level records and a successful first-level proof at strict difficulty with no diagnostics. |

The normal legacy-module/Mathlib interoperation warnings and informational default-docstring messages remain nonfatal. Browser automation could not start because of a Windows process-launch failure; the runtime checks above are API checks, not a new visual browser inspection. The same game presentation sources are preserved.

The Linux release build and development import must follow this commit. Their current results are available through this repository's GitHub Actions and the development import page; local verification alone does not establish hosted acceptance. Local logs are under `.lake/validation/lean436-*`. All verification records below this section describe earlier Lean 4.35.0 work unless explicitly dated otherwise.

# Implementation and verification status

Date: 2026-11-22. Changes are local to the specified existing repository; nothing has been pushed, published, forked, or deployed. The workspace was empty, so the existing repository was cloned here before editing. No dependency versions were changed.

## Current state: rewrite for Natural Number Game graduates

All 96 registered level files have been revised for players who completed the Natural Number Game and studied single-variable calculus. The 16 world identifiers, world and level titles, six-level structure, prerequisite chain, shared visual assets, and pinned dependencies are unchanged. The original four mathematical foundation modules are preserved; `Game/Rules.lean` adds proved, reusable coordinate and calculus rules.

The intended solutions now use **14 visible tactics**, reduced from 32. Nine familiar tools are available initially. Five additional tools are introduced separately: `norm_num` at Vector Workshop 2, `constructor` at Vector Workshop 4, `linarith` at Space Explorer 2, `simp` at Space Explorer 5, and `ring` at Partial Derivative Lab 2. All 32 guided levels include worked analogous examples. Every level has revised explanations, three progressive hints, a complete hidden instructor solution, and a brief mathematical conclusion. There is no new tutorial world, client, stylesheet, or replacement application.

Coordinate-comparison rules replace finite-index tactics. Proved derivative, integral-replacement, continuity, and path-limit rules remove the need for continuous linear-map construction and filter bookkeeping in player proofs. The readable limit and regularity names abbreviate the actual underlying Mathlib predicates. Necessary nonzero, unit-direction, integrability, and orientation conditions are retained. Advanced integral-theorem coverage remains the explicitly proved special-case scope documented below.

Most mathematical statements are unchanged. Four levels use readable, definitionally equivalent limit/regularity predicates; the y-partial level writes its answer as y+y to introduce polynomial algebra. Stokes Summit 1 now checks all four oriented boundary traces, and Gauss Citadel 1 checks all six outward face normals. No mathematical target is assumed as a hypothesis or supplied as an unproved rule.

The pinned framework scans alphabetic syntax tokens as possible tactics, including the `in` keyword in interval integrals. A game-local `NewHiddenTactic «in»` declaration permits that syntax without showing a fifteenth tactic. Its hidden, unlocked status is checked in all 96 levels. Distinct intermediate names such as `innerValue` also avoid the framework mistaking local names for global constants such as `Inner.inner`; no framework dependency was patched for this rewrite.

`scripts/curriculum-levels.json` is now the canonical authoring source, and `scripts/write-curriculum.mjs` renders the registered levels, world map, curriculum, inventory, and player regression tests. The generator preserves identical files on subsequent runs. Instructor solutions remain inside the existing `Statement` mechanism; the game does not import test solutions.

| Final executed check | Result |
|---|---|
| `lake build` | Passed with Lean 4.35.0, including all 96 solutions, shared rules, 16 worlds, and `MakeGame` (2,997 jobs). |
| `lake build GameServer` | Passed with the existing pinned proof-server dependency. |
| `lake test` | Passed all five test modules (3,012 jobs). |
| `Test/LearnerProgression.lean` | All 96 intended solutions passed the actual player runner at Regular difficulty with an empty saved inventory. |
| `Test/Verification.lean` | All levels have three hints and available tools. Every solution and every shared `VectorCalculus` declaration depends only on the standard `propext`, `Classical.choice`, and `Quot.sound` foundations. |
| Tactic locks and solution protection | Passed before/after checks for all five new tactics and the current-exercise theorem reuse guard. |
| `node scripts/check-curriculum.mjs` | Passed 16 worlds, 96 reachable levels, acyclicity, empty player templates, 32 guided examples, the restricted proof vocabulary, and all 1,344 visible tactic/level lock states. |
| Compiler inventory refresh and regeneration | Passed; refreshing `scripts/used-inventory.json` regenerated byte-identical Lean sources. |
| `lake build --no-build` | Passed; all final game build targets are current. |
| Preservation review | All 96 registered level files changed; cover artwork, toolchain, manifest, identifiers, titles, and prerequisite chain remain unchanged. `git diff --check` passed. |
| Browser review | All 16 named worlds with six markers each appeared. Updated beginning, middle, and final-world lessons rendered with 14 visible tactics. The middle rectangle and late missing-flux levels returned active Lean goals and enabled input. |

Successful final logs are `.lake/validation/nng-build-final.log`, `nng-server-final.log`, `nng-tests-final.log`, `nng-curriculum-final.log`, and `nng-no-build.log`. Screenshots include `nng-middle.jpg` and `nng-end.jpg`. Earlier draft-build logs are retained separately and are superseded by these final passing checks. The existing nonfatal Mathlib module-interoperation warnings and informational exercise-docstring messages remain; the final assembly has no missing-tool or dependency-cycle warnings.

Existing browser progress was preserved. The browser restored an old Vector Workshop 2 attempt containing `funext`, which is no longer an available teaching tactic; that attempt was left intact. Old saved attempts may need rewriting, and older inventories can retain previously earned tools. Use a separate browser profile to try the complete fresh progression without erasing a save. No proof input was edited or manually submitted during browser review. The local game was left on its welcome/world-map page.

README.md, CURRICULUM.md, SOURCES.md, and TACTIC_UNLOCKS.md describe the revised progression and authoring process. No GitHub push, remote workflow run, upload, import, or deployment was performed. Linux hosting and Docker remain untested as recorded in the earlier audit. The sections below retain the previous implementation and verification history; their earlier 32-tactic schedule is superseded by this section.

## Implemented scope

All 16 requested worlds have six playable levels (96 total), with root imports, world imports, a prerequisite chain, original explanations, objectives, prerequisites, three progressive hints, and complete instructor solutions inside the existing framework's `Statement` mechanism. `Vectors` retains the repository's established world identifier and first-level filename; other identifiers follow its descriptive CamelCase convention. The old unregistered HelloWorld files are preserved and excluded from the playable graph.

`CURRICULUM.md` lists every level. `SOURCES.md` maps the curriculum to OpenStax and records the locked formal sources. The levels use the existing `Fin 3 → ℝ` representation. Shared modules distinguish scalar coordinate partials from total Fréchet derivatives and define vector operators and geometric integrals from actual Mathlib derivatives/integrals.

## Advanced-theorem audit and exact special-case scope

The selected Mathlib source was inspected before authoring the advanced worlds. All support proofs are explicit Lean proofs; no custom axioms or assumed target conclusions are used.

| Topic | Audited Mathlib support | Implemented coverage and deferred generalization |
|---|---|---|
| Change of variables | `MeasureTheory/Function/Jacobian.lean`, including `integral_image_eq_integral_abs_det_fderiv_smul` | The polar and linear Jacobians are derived from coordinate derivatives. The polar/cylindrical/spherical levels evaluate the correctly weighted coordinate-side integrals, with domain restrictions explained and absolute-factor signs justified. The orientation-reversing linear map's constant-density rectangle equality is proved by evaluating both integrals. General measurable-set substitution, injectivity/a.e. boundary bridges, and a formal Cartesian identification of the disk/ball integrals are deferred. These levels do not claim to apply the general substitution theorem. |
| Fundamental theorem for line integrals | `IntervalIntegral/FundThmCalculus.lean`, `integral_eq_sub_of_hasDerivAt`, `integral_deriv_eq_sub` | `work_eq_endpoint` applies the existing verified fundamental theorem, with explicit derivative-along-path and interval-integrability hypotheses. Path independence is proved concretely for the globally defined potential φ(p)=p₀. Automatic derivation of the chain-rule hypothesis from arbitrary vector-field regularity is deferred. |
| Green | Planar box divergence theorem `integral2_divergence_prod_of_hasFDerivAt` exists | Fully proved unit-square circulation identity for smooth linear shears F=(0,kx,0), plus direct planar flux and area examples. The general theorem's product-space derivative/integrability interface is not wrapped here; general simple closed boundaries and arbitrary fields are deferred. The game accurately labels its directly proved family as a Green special case. |
| Stokes | The audited integral/calculus sources do not provide a ready general real parametrized-surface Stokes interface for this representation | Fully proved shear-field identity on the upward unit-square patch. A polynomial graph with exactly the same four oriented boundary traces has the same curl flux, verified from the actual parameter derivatives. General oriented manifolds, arbitrary surfaces, and a general surface-independence theorem are deferred. |
| Gauss | General divergence results for boxes exist in `MeasureTheory/Integral/DivergenceTheorem.lean` and `Analysis/BoxIntegral/DivergenceTheorem.lean` | Fully proved unit-cube identity for smooth diagonal fields F=(ax,by,cz), computed from six actual outward-oriented parametrized fluxes and the divergence volume integral. Bridging the general box API to this game's surface representation, arbitrary solids, and general divergence-theorem hypotheses are deferred. |

The special-case route keeps 96 exercises focused on calculus while avoiding a new general theory of oriented boundaries and measure conversion. Players apply the proved restricted families in the corresponding theorem-application levels. Direct calculations are never presented as proofs of the general theorems. The final boss combines justified restricted Green, Stokes, and Gauss identities.

## Mathematical conventions and limits

* `lengthSq`, `length`, and `dot` give Euclidean lengths explicitly. The Pi type's default norm is not substituted for Euclidean speed.
* `coordPartial` holds the other coordinates fixed; `directional` applies `fderiv`. Unit direction assumptions appear in the directional-rate and ascent-bound exercises.
* Curve examples used for geometric speed, arc length, tangent, and curvature are regular on the relevant intervals. Arc-length and scalar surface integrals use increasing bounds; reversing a work interval reverses oriented work.
* Surface normals are parameter cross products. Flux uses the unnormalized area vector, while scalar surface integration uses its length. Cube face parametrizations encode all six outward orientations.
* Projection and distance examples have explicit nonzero numerical normals. Centroid calculations have positive numerical masses.
* Mixed-partial and differential-identity levels compute explicit smooth polynomial cases. No unrestricted interchange or curl-free-implies-conservative principle is assumed.
* The two-path exercise disproves a genuine punctured multivariable limit of xy/(x²+y²), using paths proved to approach the punctured origin. The piecewise-origin boss proves an extension equal to a continuous polynomial.

## Verification

Pinned toolchain: `leanprover/lean4:v4.35.0`; Mathlib and GameServer revisions remain those in `lake-manifest.json`.

| Executed check | Result |
|---|---|
| `lake exe cache get` | Passed; matching Mathlib cache extracted (8,858 cached files). |
| `lake build` | Passed with Lean 4.35.0: all shared modules, 96 instructor solutions, 16 world imports, and the root `MakeGame` (2,996 build jobs including dependencies). |
| `lake build GameServer` | Passed (38 jobs); existing server components compile. |
| `lake test` | Passed the four actual Lean test modules described below, including tactic-lock enforcement. |
| `node scripts/check-curriculum.mjs` | Passed source registration, six levels per world, three hints per level, unique statements, no unproved placeholders, emitted game cardinality, reachability, acyclicity, empty player templates, and locked current-solution checks. |
| Dependency lock review | `lean-toolchain` and `lake-manifest.json` unchanged. |

The Lean test modules are:

* `Test/Verification.lean`: inspects all registered levels, verifies that every explicitly used theorem, definition, and tactic is available at that level, and audits the transitive axiom dependencies of all 96 solutions and shared support theorems. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` foundations are permitted; unfinished proofs and custom mathematical axioms fail the test.
* `Test/PlayerMode.lean`: runs an advanced Gauss application through the actual GameServer player runner at strict difficulty.
* `Test/SolutionProtection.lean`: checks that the actual runner rejects using the current instructor theorem to solve its own exercise, even at default difficulty.
* `Test/TacticLocks.lean`: checks the actual strict player runner rejects `norm_num` in the first level, and that `norm_num` and `ring` are rejected before their introductions and accepted when introduced.

The original test-driver glob included `Test/.sofi-test-folders`, whose shell-test fixtures intentionally contain `Level ???` and nonexistent imports. The Lean test target now lists the four real test modules explicitly. The fixtures and `sofi.sh` are unchanged; the unrelated shell utility tests were not executed.

The final game assembly has no missing-tool or dependency-cycle warnings. The legacy game architecture produces nonfatal interoperation warnings when importing module-based Mathlib files, and the framework reports informational use of existing docstrings for some tools and statements. These are not missing proofs.

Successful command logs are stored locally under the ignored `.lake/validation/` directory. They are build artifacts rather than required source files.

## Local browser verification

On 2026-11-22, the matching official Lean4Game v4.35.0 runtime was installed under the ignored `.lake/leangame-runtime` directory and launched natively on Windows with `scripts/start-local-game.ps1`. The browser client listens on loopback port 3000 and the proof server on loopback port 8000. The runtime reads this same repository's compiled game. A local-directory override adapts the upstream sibling-folder discovery to an ignored dependency checkout; no replacement frontend or second game project was created.

The in-app browser opened `http://localhost:3000/g/local/differential%20equations%20lean%20game`. Its rendered world map was inspected and showed all 16 requested named worlds, each with six level markers. The first level, **Coordinates**, was also opened: Lean returned its active goal and first hint, and the tactic input and Execute control became enabled. No player exercise was completed during this check. The browser was returned to the world map and left open for play.

The existing container's outdated `hhu-adam/leangame` download URL returned not found and was corrected to the official `leanprover-community/lean4game` location. A Docker CLI was unavailable on the host, so the Docker image build remains untested. Native launch and browser verification passed. Nothing was pushed or published.

## Progressive tactic unlocks

The initial blanket tactic grant has been replaced with per-level `NewTactic` declarations. Nine elementary tools are available initially, matching the assumed basic Lean proficiency. The other 23 tactics unlock at their first mathematical use, and the introducing level explains each one. `TACTIC_UNLOCKS.md` and `scripts/tactic-unlocks.json` record the complete schedule. No mathematical exercises, instructor proofs, world prerequisites, or dependency versions were changed for this adjustment.

Regular mode enforces locked tools, Relaxed mode warns, and No Rules deliberately bypasses locks. Existing saved proofs, completed levels, and previously earned inventory are preserved. In particular, a save that already earned the old first-level inventory can retain those tactics; the new schedule applies to a fresh inventory without erasing the player's earlier work.

Validation of this adjustment passed: `lake build`, `lake test`, and all 3,072 tactic/level lock-state checks in `scripts/check-curriculum.mjs`. Logs are in `.lake/validation/tactic-unlocks-*.log`. The refreshed browser was checked in Regular mode: the Coordinates inventory showed nine usable tools and the other 23 marked “Not unlocked yet.” The first level was left open with that inventory visible; no player proof was submitted or saved progress erased during the check.

## Presentation and hosting-documentation audit

On 2026-11-22, the official Lean4Game README and its relevant linked authoring, client, publishing, local-running, exercise, hint, Markdown, LaTeX, and translation guides were reviewed against the pinned runtime. `HOSTING_REPORT.md` records the conclusions and changes. The hosted service supplies the shared interface; this game supplies its text, images, supported settings, and prerequisite graph. A game import does not install a custom client stylesheet.

Presentation changes comprise a structured welcome, updated Game Info, a three-sentence landing caption, and original 500×200 cover artwork. The curriculum generator preserves these updates. Release workflows now fetch the locked Mathlib cache, run the game checks, and use an explicit packaging script that excludes the local web runtime and session data. README.md explains the distinction between local play, a Linux release artifact, and the later manual import. No publication action was taken.

| Executed check after these changes | Result |
|---|---|
| `lake build` | Passed with Lean 4.35.0, 2,996 jobs; regenerated game data and English source catalogue. |
| `lake test` | Passed all four Lean verification/player-runner modules. |
| `node scripts/check-curriculum.mjs` | Passed all 16 worlds, 96 levels, reachability, acyclicity, solution protection, and 3,072 tactic/level lock-state checks. |
| Before/after SHA-256 comparison | Every existing level file, four shared mathematical modules, tactic schedule, toolchain, and dependency lock remained identical; the root prerequisite declaration was unchanged. |
| `scripts/package-game.ps1 -ListOnly` | Inspected 150,766 actual release inputs; generated game data and root Lean build present, local runtime/session/validation directories excluded. |
| `scripts/test-package-game.ps1` | Passed a real small ZIP fixture, including portable relative paths and preservation of hidden Lean build files. |
| Browser inspection | Updated welcome and Game Info rendered; all 16 named worlds with six markers each remained in the map. New cover and 16-world/96-level metadata displayed on the local games page. |

The initial root rebuild encountered a read-only attribute on generated `.lake/gamedata` files in this OneDrive checkout. Clearing that attribute only within the generated output allowed the build to pass; source permissions were not changed. Successful logs, preservation hashes, archive manifest, and screenshots are under `.lake/validation/presentation-*` (packaging checks also use `package-*` and `publication-files.txt`). The game was left on its welcome/world-map page for local review; no proof was submitted and no saved progress was erased.

A complete production-size ZIP, the revised GitHub Actions workflow on Linux, and an import into the public server have not been executed. Host acceptance of the pinned toolchain and exact deployed appearance therefore remain unverified. No changes were pushed to GitHub, uploaded, imported, or deployed.
