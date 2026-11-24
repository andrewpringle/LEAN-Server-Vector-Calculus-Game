import fs from 'node:fs';
import path from 'node:path';

// Canonical exercises live in curriculum-levels.json; this file registers and renders them.
const worlds = JSON.parse(fs.readFileSync(new URL('./curriculum-levels.json', import.meta.url)));

const quote = s => JSON.stringify(s);
const write = (file, content) => {
  if(fs.existsSync(file)&&fs.readFileSync(file,'utf8')===content) return;
  fs.mkdirSync(path.dirname(file), {recursive:true}); fs.writeFileSync(file, content, 'utf8');
};
const theoremExamples = JSON.parse(fs.readFileSync('scripts/theorem-examples.json','utf8'));
const tacticExamples = JSON.parse(fs.readFileSync('scripts/tactic-examples.json','utf8'));
const workedDoc = (name,description,kind) => {
  const example = (kind === 'tactic' ? tacticExamples : theoremExamples)[name];
  if (!example?.code || !example?.explanation) throw Error('Missing worked example: '+name);
  const later = name.startsWith('exercise_') ? '\n\nThis is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.' : '';
  const fence = String.fromCharCode(96).repeat(3);
  return (description || 'Use this established result with the hypotheses shown below.') + later + '\n\n### Worked usage example\n\n' + example.explanation + '\n\nExamples use the namespaces and notation opened in the calculus levels.\n\n' + fence + 'lean\n' + example.code + '\n' + fence;
};
const qualify = t => ['dot_cross_left','work_eq_endpoint','green_shear','stokes_shear_patch','gauss_diagonal'].includes(t)?'VectorCalculus.'+t:t==='intervalIntegrable_id'?'intervalIntegral.'+t:t;
// This snapshot comes from Lean's actual proof-syntax inventory, not a hand-built
// approximation. Keep it updated with InventoryAudit.lean after changing proofs.
const usage = JSON.parse(fs.readFileSync('scripts/used-inventory.json','utf8'));
const firstUse = {tactics:new Map(), theorems:new Map(), definitions:new Map()};
const order = (w,l) => worlds.findIndex(x=>x.id===w)*6+l-1;
const introduce = (type,name,index) => firstUse[type].set(name,Math.min(index,firstUse[type].get(name)??Infinity));
// General shared rules have explanatory docstrings and are introduced only
// where a player first uses them. The compiler audit below supplies library names.
const localDocs = new Map();
const localKinds = new Map();
for (const file of ['Game/Calculus.lean','Game/Advanced.lean','Game/Coordinates.lean','Game/PathLimits.lean','Game/Rules.lean']) {
  const source=fs.readFileSync(file,'utf8');
  for (const m of source.matchAll(/^(theorem|def|abbrev)\s+(\w+)/gm)) {
    // Read docstrings separately: Lean's /-- ... -/ convention.
    const before=source.slice(0,m.index);
    const doc=before.slice(before.lastIndexOf('/--')).match(/^\/--([\s\S]*?)-\/\s*$/)?.[1];
    localDocs.set('VectorCalculus.'+m[2],doc?.trim().replace(/\s+/g,' '));
    localKinds.set('VectorCalculus.'+m[2],m[1]==='theorem'?'theorems':'definitions');
  }
}
for (const u of usage) {
  const wi=worlds.findIndex(w=>w.id===u.world), l=worlds[wi].levels[u.level-1];
  for (const type of ['tactics','theorems','definitions']) for (const name of u[type]) {
    if(type==='tactics' && name==='in') continue; // integral syntax, permitted separately
    const leaf=name.split('.').at(-1);
    if (new RegExp(`(?<![a-zA-Z0-9_])${leaf}(?![a-zA-Z0-9_])`).test(l.proof)) introduce(type,name,wi*6+u.level-1);
  }
}
for (const [wi,w] of worlds.entries()) for (const [li,l] of w.levels.entries()) {
  for (const t of l.tools.split(/\s+/).filter(Boolean)) introduce('theorems',qualify(t),wi*6+li);
  for (const [name,type] of localKinds) {
    const leaf=name.split('.').at(-1);
    if (new RegExp(`(?<![a-zA-Z0-9_])${leaf}(?![a-zA-Z0-9_])`).test(l.proof+(type==='definitions'?' '+l.statement:''))) introduce(type,name,wi*6+li);
  }
}
introduce('definitions','VectorCalculus.Vec',0);
introduce('definitions','VectorCalculus.dot',2);
introduce('definitions','VectorCalculus.lengthSq',3);
introduce('definitions','VectorCalculus.cross',4);
introduce('definitions','VectorCalculus.projection',5);
introduce('definitions','deriv',13);
introduce('definitions','Continuous',20);
introduce('definitions','HasDerivAt',32);
introduce('definitions','Real.pi',55);
introduce('definitions','IntervalIntegrable',71);
introduce('theorems','not_exists',22);
// NNG vocabulary is available initially; five additional tactics are learned
// inside mathematical exercises. No finite-index or library-engineering tactics.
const baselineTactics = ['rfl','exact','apply','rw','intro','have','use','left','right'];
for (const t of baselineTactics) introduce('tactics', t, 0);
const tacticDescriptions = {
  rfl: 'Close a definitional equality.', exact: 'Finish a goal with a proof of its statement.',
  apply: 'Apply a lemma to the current goal.', rw: 'Rewrite using proved equalities.',
  intro: 'Introduce a hypothesis or a universally quantified variable.',
  have: 'Name an intermediate mathematical fact.', constructor: 'Split a conjunction or construct a structured proof.',
  simp: 'Simplify using elementary identities and the explicitly supplied definitions.',
  norm_num: 'Check numerical coordinate arithmetic after expanding the relevant definitions.',
  use: 'Supply a parameter witnessing membership in a parametric line.',
  linarith: 'Solve linear equations or inequalities arising from a plane equation.',
  ring: 'Check polynomial identities, including the tangent-plane approximation error.',
  left: 'Choose the first candidate in the Lagrange-system case split.',
  right: 'Choose the second candidate in the Lagrange-system case split.'
};
const readableDocs = {
  'deriv': 'The scalar derivative value deriv f t. The derivative rules in the inventory justify the calculations used here.',
  'Continuous': 'Joint continuity of a function at every point of its domain. The sum, power, and coordinate continuity rules build proofs.',
  'HasDerivAt': 'HasDerivAt f a t means f is differentiable at t with derivative a. It states existence and the value together.',
  'IntervalIntegrable': 'A real function is integrable over the interval between its two endpoints. This analytic hypothesis justifies splitting and endpoint evaluation rules.',
  'VectorCalculus.dot_cross_left': 'A vector is perpendicular to its cross product with another vector: dot u (cross u v) = 0.',
  'VectorCalculus.reverse_integral': 'Interchanging interval endpoints negates the signed integral of the same integrand.',
  'VectorCalculus.work_eq_endpoint': 'The fundamental theorem along a path: if the potential derivative is the work integrand and that integrand is interval integrable, work equals the potential endpoint difference.',
  'Real.pi': 'The real number π. Standard polar and azimuthal angular intervals have length 2π, measured in radians.',
  'one_mul': 'Multiplying by one leaves a value unchanged. Here it simplifies the three unit coefficients of the radial field.',
  'not_exists': 'There is no witness satisfying P exactly when every proposed witness fails. Rewrite with this equivalence, then introduce a proposed witness and its claimed property.',
  'VectorCalculus.normal_congr': 'Replacing a surface by a pointwise equal parametrization preserves its two derivative tangents and oriented parameter normal.',
  'VectorCalculus.Field': 'A vector field takes a spatial point and returns a spatial vector.',
  'VectorCalculus.ScalarField': 'A scalar field assigns one real value to each spatial point.',
  'VectorCalculus.arcLength': 'Integrate Euclidean speed over the parameter interval. Geometric arc length uses increasing bounds.',
  'VectorCalculus.circle': 'The unit circle parametrization t ↦ (cos t, sin t, 0). Increasing t gives counterclockwise motion.',
  'VectorCalculus.curl': 'Right-handed curl: the three differences of cross-coordinate partial derivatives in cyclic coordinate order.',
  'VectorCalculus.curvature': 'For a regular curve, curvature is the length of velocity cross acceleration divided by speed cubed.',
  'VectorCalculus.divergence': 'Sum the three matching-coordinate partials of a vector field; cross-coordinate partials do not enter divergence.',
  'VectorCalculus.gradient': 'The vector of a scalar field’s three coordinate partial derivatives, in x, y, z order.',
  'VectorCalculus.helix': 'The spatial curve t ↦ (cos t, sin t, t), combining circular motion with uniform vertical motion.',
  'VectorCalculus.liftedPatch': 'The graph (u,v,u(1-u)v(1-v)) on the unit parameter square. Its height vanishes on all four boundary edges.',
  'VectorCalculus.patch': 'The horizontal parametrization (u,v,0). On the unit parameter square it gives an upward-oriented square patch.',
  'VectorCalculus.planarJacobian': 'The 2 by 2 matrix whose columns are the actual first and second parameter derivatives of a planar map.',
  'VectorCalculus.planeDistance': 'Absolute normal displacement divided by the Euclidean normal length. The plane normal must be nonzero.',
  'VectorCalculus.pathRatio': 'The field xy/(x²+y²). Its value at the origin does not repair its different limiting values along two paths.',
  'VectorCalculus.polarX': 'The first polar coordinate function: r cos θ.',
  'VectorCalculus.polarY': 'The second polar coordinate function: r sin θ.',
  'VectorCalculus.radial': 'The radial field F(p)=p, pointing directly away from the origin.',
  'VectorCalculus.rotation': 'The planar rotational field (-y/2,x/2,0), whose vertical curl is one.',
  'VectorCalculus.scalarLineIntegral': 'Integrate scalar density along a curve, multiplied by Euclidean speed. Increasing bounds give arc-length weighting.',
  'VectorCalculus.speed': 'The Euclidean length of velocity, always nonnegative.',
  'VectorCalculus.squarePotential': 'The scalar field x²+y²+z², measuring squared Euclidean distance from the origin.',
  'VectorCalculus.surfaceFlux': 'Integrate the field dotted with the parameter cross-product normal. The normal already includes the oriented area factor.',
  'VectorCalculus.surfaceIntegral': 'Integrate scalar density on a parametrized surface, multiplied by the Euclidean length of its parameter normal.',
  'VectorCalculus.surfaceNormal': 'Differentiate in the first parameter, differentiate in the second, then take their cross product in that order.',
  'VectorCalculus.unitTangent': 'Divide velocity by its Euclidean speed on a regular curve, where speed is nonzero.',
  'VectorCalculus.work': 'Integrate field-along-path dotted with velocity. This signed integral depends on path orientation.',
  'VectorCalculus.Vec': 'A spatial real vector with coordinates 0, 1, and 2. Write ![x,y,z] and read its coordinates with v 0, v 1, v 2.',
  'VectorCalculus.dot': 'Euclidean dot product: multiply the three matching coordinates and add. Use rw [dot] to display the formula.',
  'VectorCalculus.lengthSq': 'Squared Euclidean length: dot v v. No square root is needed for unit-vector and orthogonality calculations.',
  'VectorCalculus.length': 'Euclidean length, the nonnegative square root of lengthSq. This differs from the default Pi-type norm.',
  'VectorCalculus.cross': 'The right-handed cross product in coordinate order. Its direction changes when the two input vectors are exchanged.',
  'VectorCalculus.projection': 'Projection of v onto n: (dot v n / lengthSq n) times n. The geometric formula requires a nonzero direction n.',
  'VectorCalculus.onLine': 'Line membership means there is a real parameter t for which q = p + t times v. Supply a witness with use.',
  'VectorCalculus.onPlane': 'Point-normal plane equation: dot n (q-p) = 0. A nonzero normal gives a genuine plane.',
  'VectorCalculus.partialX': 'Vary the first real argument and hold the second fixed: deriv (fun t => f t y) x.',
  'VectorCalculus.partialY': 'Hold the first real argument fixed and vary the second: deriv (fun t => f x t) y.',
  'VectorCalculus.coordPartial': 'Vary exactly one spatial coordinate while fixing the other two. This is a scalar partial derivative, not the total derivative map.',
  'VectorCalculus.directional': 'Apply the total derivative to a direction vector. For a unit direction, this is rate of change per unit distance.',
  'VectorCalculus.velocity': 'Differentiate the three component functions of a parametrized curve. Use velocity_components to display those derivatives.',
  'VectorCalculus.jacobian': 'Derivative matrix: row i, column j is the j partial of output component i.',
  'hasDerivAt_pow': 'Power rule with differentiability included: hasDerivAt_pow n t gives derivative n*t^(n-1) of the nth power at t.',
  'deriv_pow_field': 'Power rule for the scalar derivative of x raised to a natural-number power. Numeric exponents simplify with norm_num.',
  'intervalIntegral.integral_id': 'Integral of the identity function: (b^2-a^2)/2 on a..b.',
  'intervalIntegral.integral_pow': 'Power integration rule: integrate a natural power using its next power divided by the next exponent.',
  'intervalIntegral.integral_const_mul': 'A constant real factor may be pulled outside an interval integral.',
  'intervalIntegral.integral_mul_const': 'A fixed right-hand real factor may be pulled outside an interval integral.',
  'intervalIntegral.integral_sub': 'Split an integral of f-g into the difference of integrals. Both functions must be interval integrable.',
  'intervalIntegral.integral_div': 'Division by a fixed scalar commutes with interval integration.',
  'continuous_apply': 'A coordinate projection on a product space is continuous. Supply its coordinate index, for example continuous_apply 0.',
  'sq_nonneg': 'Every real square is nonnegative: sq_nonneg x proves 0 ≤ x^2.',
  'sq_pos_of_ne_zero': 'A nonzero real number has a strictly positive square. Supply the proof that the number is nonzero.',
  'le_of_sq_le_sq': 'From a^2 ≤ b^2 and 0 ≤ b, conclude a ≤ b. The upper bound must be nonnegative; a may have either sign.',
  'Or.elim': 'To use a hypothesis P or Q, prove the goal assuming P and prove it again assuming Q. apply Or.elim h produces these two branches.',
  'not_exists.mpr': 'To refute an existential statement, introduce an arbitrary proposed witness and derive a contradiction from its claimed property.',
  'mul_left_cancel₀': 'Cancel a common nonzero left factor in a real multiplication equality. Supply the nonzero-factor proof and the equality.',
  'mul_eq_zero': 'A product of real numbers is zero exactly when at least one factor is zero. Use .mp to obtain the two alternatives.',
  'Real.sin_sq_add_cos_sq': 'The trigonometric identity sin(t)^2 + cos(t)^2 = 1.',
  'Matrix.det_fin_two': 'The 2 by 2 determinant formula: top-left times bottom-right minus top-right times bottom-left.',
  'Matrix.det': 'The signed determinant of a square matrix. Change-of-variables area and volume use its absolute value.',
  'Matrix.one_apply': 'The identity matrix has ones on its diagonal and zeros elsewhere.',
  'Real.cos': 'The real cosine function, with angles in radians.',
  'Real.sin': 'The real sine function, with angles in radians.',
  'Real.sin_nonneg_of_mem_Icc': 'Sine is nonnegative on the closed interval from 0 to π. Supply both interval bounds.',
  'abs_of_nonneg': 'For a nonnegative real a, its absolute value equals a. Supply the nonnegativity proof.',
  'deriv_add_const': 'Adding a constant to a scalar function does not change its derivative.',
  'deriv_const_add': 'A constant added before a scalar function does not change its derivative.',
  'deriv_const_mul_field': 'A fixed left scalar factor pulls outside the scalar derivative.',
  'deriv_mul_const_field': 'A fixed right scalar factor pulls outside the scalar derivative.',
  'deriv_const_mul_id': 'The derivative of t ↦ a*t is the constant a.',
  'deriv_const_sub_id': 'The derivative of t ↦ a-t is -1, preserving the sign of a reversed parameter.',
  'deriv_neg': 'The scalar function t ↦ -t has derivative -1 at every real point.',
  'deriv_const': 'A constant scalar function has derivative zero.',
  'eq_comm': 'An equality may be read in either direction: a=b is equivalent to b=a.',
  'integral_id': 'Integrate the identity function using (b²-a²)/2.',
  'integral_pow': 'Integrate a natural power using the next power divided by the next exponent.',
  'integral_sin': 'The integral of sine on a..b is cos a minus cos b.',
  'le_trans': 'Combine a≤b and b≤c to obtain a≤c.',
  'mul_nonneg': 'A product of two nonnegative real numbers is nonnegative. Prove the sign of each factor.',
  'add_nonneg': 'A sum of two nonnegative real numbers is nonnegative.',
  'add_pos_of_pos_of_nonneg': 'A positive first summand plus a nonnegative second summand is positive.',
  'add_pos_of_nonneg_of_pos': 'A nonnegative first summand plus a positive second summand is positive.',
  'Eq.trans': 'Join equalities through an intermediate value. apply Eq.trans (b := value) asks for the first and second equality.',
};
for (const [name,doc] of Object.entries(readableDocs)) localDocs.set(name,doc);
// Also find the small, explicitly supported tactic vocabulary directly, so a
// changed proof's first build does not depend on an earlier inventory snapshot.
for (const [wi,w] of worlds.entries()) for (const [li,l] of w.levels.entries()) {
  for (const name of Object.keys(tacticDescriptions)) {
    if (new RegExp(`(?<![a-zA-Z0-9_])${name}(?![a-zA-Z0-9_])`).test(l.proof)) introduce('tactics',name,wi*6+li);
  }
}
for (const [name] of firstUse.tactics) {
  if (!tacticDescriptions[name]) throw Error(`Undocumented tactic unlock: ${name}`);
}
// The framework keeps the first documentation entry; the shared file must
// contain these examples before any level registers a tactic. Templates do not unlock tools.
const tacticInsert = {rfl:'rfl',rw:'rw [$,]',have:'have $_ : $+ := by $;'};
write('Game/Doc/Tactics.lean', 'import GameApi\n\n' + Object.entries(tacticDescriptions).map(([name,description]) =>
  '/-- '+workedDoc(name,description,'tactic')+' -/\nTacticDoc «'+name+'»'+(Object.hasOwn(tacticInsert,name) ? ' insert '+quote(tacticInsert[name]) : '')+'\n').join('\n'));
const tacticSchedule = [...firstUse.tactics].map(([name,index])=>({
  name, world:worlds[Math.floor(index/6)].id, level:index%6+1,
  baseline:baselineTactics.includes(name), explanation:tacticDescriptions[name]
})).sort((a,b)=>order(a.world,a.level)-order(b.world,b.level)||a.name.localeCompare(b.name));
for (const [wi,w] of worlds.entries()) {
  if (w.levels.length !== 6) throw Error(`${w.id}: expected exactly six levels`);
  const imports = [];
  for (const [li,l] of w.levels.entries()) {
    const file = wi === 0 && li === 0 ? 'L01_ZeroAdd' : `L${String(li+1).padStart(2,'0')}_${l.title.replaceAll(/[^a-zA-Z0-9 ]/g,'').split(' ').map(t=>t[0]?.toUpperCase()+t.slice(1)).join('')}`;
    imports.push(`import Game.Levels.${w.id}.${file}`);
    const name = `exercise_${w.id}_${li+1}`;
    const newTools = [...firstUse.theorems].filter(([,index])=>index===wi*6+li).map(([name])=>name).sort();
    const newDefinitions = [...firstUse.definitions].filter(([,index])=>index===wi*6+li).map(([name])=>name).sort();
    const newTactics = tacticSchedule.filter(t=>t.world===w.id && t.level===li+1);
    const toolIntroduction = newTactics.filter(t=>!t.baseline).map(t=>`\`${t.name}\`: ${t.explanation}`).join('\n\n');
    const levelExplanation = l.explanation + (toolIntroduction ? `\n\nNew tools unlocked here:\n\n${toolIntroduction}` : '');
    let text = `import Game.Metadata\nimport Game.Rules\n\nopen VectorCalculus\nopen MeasureTheory intervalIntegral\nopen scoped Topology\nnoncomputable section\n\nWorld ${quote(w.id)}\nLevel ${li+1}\nTitle ${quote(l.title)}\n\nIntroduction ${quote(`Objective: ${l.objective}\n\nMathematical prerequisites: ${w.prerequisites}${li ? ` Earlier levels of ${w.title}.` : ''}\n\n${levelExplanation}\n\nExercise: prove the statement below.${li===5?' Combine earlier methods and justify every hypothesis.':li<2?' The hints guide the main steps.':''}`)}\n\n`;
    for (const t of newTactics) text += `/-- ${workedDoc(t.name,t.explanation,"tactic")} -/\nTacticDoc «${t.name}»\n`;
    if (newTactics.length) text += `NewTactic ${newTactics.map(t=>`«${t.name}»`).join(' ')}\n`;
    // This pinned GameServer scans every alphabetic syntax atom as a tactic.
    // Permit the interval-integral keyword globally without a spurious UI tile.
    if(wi===0 && li===0) text += '/-- The keyword in belongs to interval-integral notation; it is not a tactic. -/\nTacticDoc «in»\nNewHiddenTactic «in»\n';
    const qualifiedTools = newTools;
    for (const t of qualifiedTools) text += `/-- ${workedDoc(t,localDocs.get(t),"theorem")} -/\n`+`TheoremDoc ${t} as ${quote(t.split('.').at(-1))} in "Calculus"\n`;
    if (qualifiedTools.length) text += `NewTheorem ${qualifiedTools.join(' ')}\n`;
    for (const t of newDefinitions) text += (localDocs.get(t)?`/-- ${localDocs.get(t)} -/\n`:'')+`DefinitionDoc ${t} as ${quote(t.split('.').at(-1))} in "Calculus notation"\n`;
    if (newDefinitions.length) text += `NewDefinition ${newDefinitions.join(' ')}\n`;
    text += `\n/-- ${workedDoc(name,l.objective,"theorem")} -/\nTheoremDoc ${name} as ${quote(name)} in "[anonymous]"\n`;
    text += `\n/-- ${l.objective} -/\nStatement ${name} ${l.statement} := by\n`;
    l.hints.forEach((h,i)=>text += `  Hint${i ? ' (hidden := true)' : ''} ${quote(`${i+1}. ${h}`)}\n`);
    text += l.proof.split('\n').map(line=>'  '+line).join('\n');
    text += `\n\nConclusion ${quote(l.conclusion || `Established: ${l.objective} ${l.explanation.split(/(?<=\.)\s/)[0]}`)}\n`;
    write(`Game/Levels/${w.id}/${file}.lean`, text);
  }
  write(`Game/Levels/${w.id}.lean`, `${imports.join('\n')}\n\nWorld ${quote(w.id)}\nTitle ${quote(w.title)}\nIntroduction ${quote(`Six exercises in ${w.title.toLowerCase()}. Prerequisites: ${w.prerequisites} Levels 1–2 are guided, 3–4 develop independent calculation, 5 applies the ideas, and 6 combines them.`)}\n`);
}
const welcome = '# Welcome to Vector Calculus in Lean\n\n### A Calculus III proof adventure\n\nExplore vectors, curves, multivariable derivatives, multiple integrals, and vector integral theorems across **16 worlds and 96 challenges**.\n\n## Start here\n\nChoose **Vector Workshop** on the world map, then open **Coordinates**. Each world has six levels; its final level brings the earlier ideas together.\n\n## Before you begin\n\nYou should have completed the Natural Number Game and studied single-variable calculus. New calculus notation and a small set of additional tactics are explained where you need them.\n\n## Playing a level\n\nRead the objective, inspect the goal, and enter a tactic. The inventory explains the tools you have unlocked. Use the progressive hints when you need a nudge. **Regular** game rules enforce the unlock sequence.\n\n## The final worlds\n\nThe integral-theorem challenges use explicitly stated, fully proved special cases. Each level tells you which result applies and what it establishes.';
const gameInfo = '## About this game\n\nOriginal vector-calculus exercises aligned with [OpenStax Calculus Volume 3](https://openstax.org/books/calculus-volume-3/pages/preface). Proofs use Lean 4 and Mathlib.\n\n## Mathematical scope\n\nThe later worlds include proved special-case families for Green, Stokes, and Gauss, and verified coordinate-side integration examples. They are labeled as special cases rather than proofs of the general integral theorems.\n\n## Project and references\n\n[Game repository](https://github.com/andrewpringle/LEAN-Server-Vector-Calculus-Game) · [Lean4Game framework](https://github.com/leanprover-community/lean4game)\n\nThe repository contains the curriculum map, source references, verification status, and full tactic-unlock schedule.';
write('Game.lean', worlds.map(w=>`import Game.Levels.${w.id}`).join('\n') + `\n\nTitle "Vector Calculus in Lean"\nIntroduction ${quote(welcome)}\nConclusion "You have completed 96 vector calculus proofs, from coordinates to justified integral-theorem special cases."\nInfo ${quote(gameInfo)}\nLanguages "en"\nCaptionShort "Calculus III, proved in Lean"\nCaptionLong "Explore vectors, curves, multivariable derivatives, multiple integrals, and vector integral theorems through 96 proof challenges. Completion of the Natural Number Game and single-variable calculus are assumed. Advanced integral-theorem challenges use explicitly labeled, fully proved special cases."\nCoverImage "images/vector-calculus-cover.svg"\n\nDependency ${worlds.map(w=>w.id).join(' → ')}\n\nMakeGame\n`);
write('CURRICULUM.md', '# Vector calculus curriculum\n\nCompletion of the Natural Number Game and single-variable calculus are assumed. There is no Lean tutorial world. Follow the prerequisite chain below; every world contains exactly six playable exercises. In each world, levels 1–2 include worked analogous examples, 3–4 are less scaffolded, 5 applies a method, and 6 synthesizes earlier ideas. Each level carries its objective, mathematical prerequisites, original explanation, formal exercise, three progressive hints, hidden instructor proof, and brief proof interpretation.\n\nAll 96 intended solutions use 14 tactics. Nine familiar NNG tools are available initially; `norm_num`, `constructor`, `linarith`, `simp`, and `ring` are introduced separately inside the mathematical progression. See TACTIC_UNLOCKS.md. Proved reusable rules expose coordinate calculations, partial derivatives, integral replacement, continuity, and limits without requiring players to manipulate finite indices, continuous linear maps, or filter implementation details. The limit and regularity names abbreviate the actual underlying Mathlib predicates. All intended solutions are also checked through the real player runner in Regular mode with a fresh inventory.\n\n' + worlds.map((w,i)=>`## ${String(i+1).padStart(2,'0')}. ${w.title} (\`${w.id}\`)\n\nPrerequisites: ${w.prerequisites} ${i?`Complete ${worlds[i-1].title}.`:''}\n\n${w.levels.map((l,j)=>`${j+1}. **${l.title}:** ${l.objective}`).join('\n')}\n`).join('\n') + '\nThe advanced families are deliberately restricted: see STATUS.md before interpreting a calculation as an application of a general theorem.\n');
write('scripts/curriculum-manifest.json', JSON.stringify(worlds.map(w=>({id:w.id,title:w.title,levels:w.levels.map(l=>l.title)})),null,2)+'\n');
write('scripts/tactic-unlocks.json', JSON.stringify(tacticSchedule,null,2)+'\n');
write('TACTIC_UNLOCKS.md', '# Tactic progression\n\nCompletion of the Natural Number Game and single-variable calculus are assumed. Nine familiar tactics are available initially. Five more tools unlock gradually: `norm_num`, `constructor`, `linarith`, `simp`, and `ring`. All 96 intended solutions use only these 14 tactics, with explicit mathematical intermediate steps. There is no Lean tutorial world. A new tactic is usable in its introducing level; completing that level adds it to the earned inventory. General support proofs may use additional tactics, but players do not need them.\n\nUse **Game Rules → Regular** to enforce locks. Relaxed mode warns; No Rules deliberately bypasses locks. Existing completed proofs and inventories are preserved, so an older save can retain previously earned tools. Revised statements may require revisiting an old proof; use a separate browser profile to try a fresh progression without erasing your save.\n\n| First available | Newly available tactics |\n|---|---|\n' + worlds.flatMap(w=>w.levels.flatMap((l,i)=>{const names=tacticSchedule.filter(t=>t.world===w.id&&t.level===i+1).map(t=>'`'+t.name+'`');return names.length?[`| ${w.title}, level ${i+1}: ${l.title} | ${names.join(', ')} |`]:[]})).join('\n')+'\n');
console.log(`Wrote ${worlds.length} worlds and ${worlds.reduce((s,w)=>s+w.levels.length,0)} levels.`);
// Run the exact intended proofs through the real player checker, with a fresh
// inventory and Regular rules. These tests are never imported by the game.
write('Test/LearnerProgression.lean', 'import Game\nimport GameServer\n\nopen VectorCalculus\nopen MeasureTheory intervalIntegral\nopen scoped Topology\nnoncomputable section\n\n/-! All 96 intended solutions must be playable with only the tools available at that level. -/\n\n'+worlds.flatMap(w=>w.levels.map((l,i)=>`-- ${w.title}: ${l.title}\nRunner "MyGame" "${w.id}" ${i+1} (difficulty := 2) (inventory := []) := by\n${l.proof.split('\n').map(s=>'  '+s).join('\n')}\n`)).join('\n'));


// Compile the exact displayed examples separately: none become player lemmas.
write('Test/ToolExamples.lean', 'import Game\n\nopen VectorCalculus MeasureTheory intervalIntegral\nopen scoped Topology\nnoncomputable section\n\n' + [...Object.entries(theoremExamples),...Object.entries(tacticExamples)].sort(([a],[b])=>a.localeCompare(b)).map(([name,e])=>'-- '+name+'\n'+e.code+'\n').join('\n'));
