import fs from 'node:fs';
import assert from 'node:assert/strict';

const manifest = JSON.parse(fs.readFileSync('scripts/curriculum-manifest.json','utf8'));
const root = fs.readFileSync('Game.lean','utf8');
assert.equal(manifest.length,16);
const ids=manifest.map(w=>w.id);
const tacticUnlocks=JSON.parse(fs.readFileSync('scripts/tactic-unlocks.json','utf8'));
const baseline=new Set(['apply','exact','have','intro','rfl','rw','use','left','right']);
const allowedTactics=new Set([...baseline,'constructor','norm_num','simp','linarith','ring']);
assert.equal(tacticUnlocks.length,14);
assert.deepEqual(new Set(tacticUnlocks.map(t=>t.name)),allowedTactics);
const lessons=JSON.parse(fs.readFileSync('scripts/curriculum-levels.json','utf8'));
const forbiddenSyntax=/<;>|\b(?:fin_cases|funext|ext|convert|rintro|refine|simp_rw|fun_prop|nlinarith|positivity|rcases|by_cases|subst|unfold|calc)\b/;
for (const w of lessons) for (const [i,l] of w.levels.entries()) {
  assert(l.rewritten,`Missing rewrite: ${w.id} ${i+1}`);
  assert.equal(l.hints.length,3);
  assert(!forbiddenSyntax.test(l.proof),`Advanced proof syntax in ${w.id} ${i+1}`);
  if(i<2) assert(l.explanation.includes('Worked example:'),`Missing guided example: ${w.id} ${i+1}`);
}
assert.equal(lessons.flatMap(w=>w.levels).length,96);
assert.equal(new Set(ids).size,16);
assert.equal((root.match(/^import Game.Levels\./gm)||[]).length,16);
assert.deepEqual(root.match(/^Dependency (.+)$/m)?.[1].split(' → '),ids);
let count=0;
const names=new Set();
const allFiles=['Game/Calculus.lean','Game/Advanced.lean','Game/Coordinates.lean','Game/PathLimits.lean','Game/Rules.lean'];
for (const w of manifest) {
  const worldSource=fs.readFileSync(`Game/Levels/${w.id}.lean`,'utf8');
  const imports=[...worldSource.matchAll(/^import (Game\.Levels\.[\w.]+)$/gm)].map(m=>m[1].replaceAll('.','/')+'.lean');
  assert.equal(imports.length,6,w.id);
  assert.equal(w.levels.length,6);
  assert(root.includes(`import Game.Levels.${w.id}\n`));
  const registered=[];
  for (const f of imports) {
    const text=fs.readFileSync(f,'utf8');
    assert(text.includes(`World "${w.id}"`),f);
    const n=Number(text.match(/^Level (\d+)$/m)?.[1]); registered.push(n);
    assert(text.includes(`Title ${JSON.stringify(w.levels[n-1])}`),f);
    assert.equal((text.match(/^Statement /gm)||[]).length,1,f);
    assert.equal((text.match(/^  Hint/gm)||[]).length,3,f);
    assert(text.includes('Objective:')&&text.includes('Mathematical prerequisites:')&&text.includes('Exercise:')&&text.includes('Conclusion '),f);
    const name=text.match(/^Statement (\w+)/m)?.[1];
    assert(name&&!names.has(name),f); names.add(name);
    const proof=text.split(':= by\n').at(-1).split('\nConclusion')[0];
    assert(!proof.includes(name),`Instructor solution reuses itself: ${f}`);
    assert(!/^import Game\.Levels\./m.test(text),f);
    allFiles.push(f); count++;
  }
  assert.deepEqual(registered,[1,2,3,4,5,6],w.id);
}
assert.equal(count,96);
for (const f of allFiles) assert(!/\b(sorry|admit|axiom)\b/.test(fs.readFileSync(f,'utf8')),`Unproved declaration in ${f}`);
for (const f of ['Game/Calculus.lean','Game/Advanced.lean']) assert(!/^import Game\.Levels\./m.test(fs.readFileSync(f,'utf8')));
console.log('PASS: 16 root-registered worlds; 96 unique playable statements; six ordered levels per world.');
console.log('PASS: three hints per level and learning metadata; complete proof bodies; no unproved placeholders.');
console.log('PASS: all 96 levels rewritten for NNG graduates; worked examples in all 32 guided levels; no advanced tactic syntax in intended solutions.');
console.log('PASS: prerequisite chain covers every world exactly once; no structural import cycles or solution imports into support.');
console.log('NOTE: these structural checks complement, and never replace, lake build / MakeGame and the Lean compiler.');

if (fs.existsSync('.lake/gamedata/game.json')) {
  const game=JSON.parse(fs.readFileSync('.lake/gamedata/game.json','utf8'));
  assert.equal(game.tile.worlds,16); assert.equal(game.tile.levels,96);
  assert.deepEqual(Object.keys(game.worldSize).sort(),[...ids].sort());
  for(const id of ids) assert.equal(game.worldSize[id],6);
  for(const w of manifest) for(let n=1;n<=6;n++) {
    const file=`.lake/gamedata/level__${w.id}__${n}.json`;
    const data=JSON.parse(fs.readFileSync(file,'utf8'));
    assert.equal(data.index,n); assert(data.statementName);
    for (const unlock of tacticUnlocks) {
      const tile=data.tactics.find(t=>t.name===unlock.name);
      assert(tile,`Missing tactic ${unlock.name} in ${file}`);
      const current=ids.indexOf(w.id)*6+n;
      const introduced=ids.indexOf(unlock.world)*6+unlock.level;
      assert.equal(tile.locked,current<introduced,`Incorrect lock for ${unlock.name} in ${file}`);
      assert.equal(tile.new,current===introduced,`Incorrect introduction for ${unlock.name} in ${file}`);
    }
    const syntaxKeyword=data.tactics.find(t=>t.name==='in');
    assert(syntaxKeyword?.hidden&&!syntaxKeyword.locked,`Integral syntax is not permitted invisibly in ${file}`);
    assert.equal(data.tactics.filter(t=>!t.hidden).length,14);
    if(w.id==='Vectors'&&n===1) assert.deepEqual(new Set(data.tactics.filter(t=>!t.locked&&!t.hidden).map(t=>t.name)),baseline);
    assert(!data.template || !data.template.trim(),`Prefilled instructor solution in ${file}`);
    assert(!data.theorems.some(t=>t.name===data.statementName&&!t.locked),`Current solution unlocked in ${file}`);
  }
  const edges=game.worlds.edges;
  const incoming=new Map(ids.map(id=>[id,0]));
  const adjacency=new Map(ids.map(id=>[id,[]]));
  for(const [from,to] of edges) { assert(ids.includes(from)&&ids.includes(to)); adjacency.get(from).push(to); incoming.set(to,incoming.get(to)+1); }
  const roots=ids.filter(id=>incoming.get(id)===0); assert.deepEqual(roots,['Vectors']);
  const queue=[...roots],visited=[];
  while(queue.length) { const from=queue.shift(); visited.push(from); for(const to of adjacency.get(from)) { incoming.set(to,incoming.get(to)-1); if(!incoming.get(to)) queue.push(to); } }
  assert.equal(visited.length,16,'Cycle in emitted game graph');
  console.log('PASS: emitted game data has 16 reachable worlds, 96 levels, no cycles, no prefilled or unlocked current solutions.');
  console.log('PASS: all 14 tactics have the intended lock state in all 96 levels; nine familiar tools initially and five gradual introductions.');
} else console.log('Emitted game-data checks pending: run lake build first.');
