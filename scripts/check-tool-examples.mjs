import fs from 'node:fs';
import assert from 'node:assert/strict';
const worlds=JSON.parse(fs.readFileSync('scripts/curriculum-manifest.json','utf8'));
const theorems=JSON.parse(fs.readFileSync('scripts/theorem-examples.json','utf8'));
const tactics=JSON.parse(fs.readFileSync('scripts/tactic-examples.json','utf8'));
const expectedTheorems=new Set(), expectedTactics=new Set();
let levels=0;
for(const w of worlds){
 const index=fs.readFileSync(`Game/Levels/${w.id}.lean`,'utf8');
 for(const match of index.matchAll(/^import (Game\.Levels\.[\w.]+)$/gm)){
  const text=fs.readFileSync(match[1].replaceAll('.','/')+'.lean','utf8');
  levels++;
  const own=text.match(/^Statement (\w+)/m)[1];
  const names=[own,...[...text.matchAll(/^NewTheorem (.+)$/gm)].flatMap(m=>m[1].trim().split(/\s+/))];
  for(const name of names){
   expectedTheorems.add(name);
   assert(theorems[name]?.code&&theorems[name]?.explanation,`Missing theorem example: ${name}`);
   assert(text.includes(`TheoremDoc ${name}\n`) || text.includes(`TheoremDoc ${name} `),`Missing framework documentation: ${name}`);
   assert(text.includes(theorems[name].code),`Example not displayed verbatim: ${name}`);
   assert(theorems[name].code.includes(name.split('.').at(-1)),`Example does not use its theorem: ${name}`);
  }
  for(const match of text.matchAll(/^NewTactic (.+)$/gm)) for(const item of match[1].matchAll(/«([^»]+)»/g)){
   const name=item[1]; expectedTactics.add(name);
   assert(tactics[name]?.code&&text.includes(tactics[name].code),`Missing displayed tactic example: ${name}`);
  }
 }
}
const sharedTactics=fs.readFileSync('Game/Doc/Tactics.lean','utf8');
for(const [name,e] of Object.entries(tactics)) assert(sharedTactics.includes(e.code),`Missing earliest tactic help example: ${name}`);
assert.equal(levels,96);assert.equal(expectedTheorems.size,175);assert.equal(expectedTactics.size,14);
assert.deepEqual(new Set(Object.keys(theorems)),expectedTheorems);
assert.deepEqual(new Set(Object.keys(tactics)),expectedTactics);
const source=fs.readFileSync('Test/ToolExamples.lean','utf8');
for(const [name,e] of [...Object.entries(theorems),...Object.entries(tactics)]){
 assert(e.code.startsWith('example '),`Expected a complete independent example: ${name}`);
 assert(!/\b(sorry|admit|axiom)\b/.test(e.code),`Unproved example: ${name}`);
 assert(source.includes(e.code),`Displayed example not tested: ${name}`);
}
assert(!fs.readFileSync('Game.lean','utf8').includes('Test.ToolExamples'));
console.log('PASS: all 175 theorem entries and 14 visible tactics display complete examples; the exact displayed code is included in Test.ToolExamples, outside the player import graph.');
for (const [kind,examples] of [['theorem',theorems],['tactic',tactics]]) {
  for (const [name,e] of Object.entries(examples)) {
    const doc=JSON.parse(fs.readFileSync(`.lake/gamedata/doc__${kind}__${name}.json`,'utf8'));
    assert(doc.content.includes(e.code),`Compiled help does not display the tested example: ${name}`);
  }
}
console.log('PASS: all 189 emitted help entries contain the exact tested examples, including the shared baseline tactic documentation.');