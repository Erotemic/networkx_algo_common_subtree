/* Optional PowerPoint overview of the canonical Manim source.
 * Run from repo root: node presentations/storyboard_preview.js
 * Output: presentations/media/common-subtree-storyboard.pptx (Git-ignored).
 */
'use strict';
const fs = require('fs');
const path = require('path');
const pptxgen = require('pptxgenjs');
// Optional validation helper: available in the authoring environment, but
// the distributable source must also run on a normal workstation with PptxGenJS.
let warnIfSlideElementsOutOfBounds = null;
try {
  ({ warnIfSlideElementsOutOfBounds } =
    require(process.env.SLIDE_HELPERS_PATH || 'pptxgenjs_helpers'));
} catch (_) {
  // Use the included geometry and rendered slides for QA if not available.
}
const pptx = new pptxgen();
pptx.layout = 'LAYOUT_WIDE';
pptx.author = 'Common subtree research program';
pptx.subject = 'Mathematical storyboard of common subtree algorithms';
pptx.title = 'Common Subtrees: Three Mathematical Families';
pptx.lang = 'en-US';
pptx.theme = {headFontFace:'Aptos Display', bodyFontFace:'Aptos', lang:'en-US'};
const S = pptx.ShapeType;
const C = {bg:'0B1525', panel:'14243A', outline:'2E4D68', white:'F4F6FB',muted:'9DB3C8',teal:'35D5C5',amber:'FFC36B',rose:'FF758B',blue:'68A9FF'};
const W=13.3333333333, H=7.5;
const setBg = s => {s.background={color:C.bg};};
function text(s,txt,x,y,w,h,size=18,color=C.white,opt={}) {
 s.addText(txt,{x,y,w,h,margin:0,fontFace:'Aptos',fontSize:size,color,bold:false,
                valign:'mid',breakLine:false,fit:'shrink',...opt});
}
function line(s,x1,y1,x2,y2,color=C.outline,width=1){s.addShape(S.line,{x:x1,y:y1,w:x2-x1,h:y2-y1,line:{color,width}});}
function rectangle(s,x,y,w,h,color=C.panel,accent=C.outline){
 s.addShape(S.roundRect,{x,y,w,h,rectRadius:.14,radius:.14,
   fill:{color},line:{color:accent,width:1.2}});
}
function card(s,x,y,w,h,ttl,body,accent=C.teal){
 rectangle(s,x,y,w,h);
 if (h <= 1.30) {
   text(s,ttl,x+.22,y+.14,3.53,h-.28,17,accent,{bold:true});
   text(s,body,x+3.76,y+.14,w-3.98,h-.28,19,C.white,{valign:'mid'});
 } else {
   text(s,ttl,x+.23,y+.24,w-.46,.43,22,accent,{bold:true});
   text(s,body,x+.23,y+.83,w-.46,h-1.00,17,C.white,{valign:'top'});
 }
}
function head(s,number,title,tag,source){
 setBg(s);
 text(s,String(number).padStart(2,'0'),.48,.30,.54,.45,20,C.teal,{bold:true});
 text(s,title,1.08,.27,11.75,.57,29,C.white,{bold:true});
 text(s,tag.toUpperCase(),.5,.99,12,.25,11,C.teal,{charSpacing:2.0});
 line(s,.5,1.37,12.83,1.37,C.outline,1.7);
 text(s,source,.5,7.04,12.33,.24,10,C.muted,{align:'center'});
}
function paragraph(s,title,description,formula,number,source){
 head(s,number,title,'Mathematical sequence',source);
 card(s,.68,1.76,11.98,2.85,'IDEA',description,C.teal);
 rectangle(s,.68,4.88,11.98,1.60,C.panel,C.outline);
 text(s,formula,1.02,5.18,11.3,.89,22,C.amber,{align:'center',bold:true});
}
function tree(s, nodes, x, y, scale=1, colored=[]){
 for (const n of nodes){if(n.p!==undefined){const p=nodes[n.p];line(s,x+p.x*scale,y+p.y*scale,x+n.x*scale,y+n.y*scale,C.muted,3);}}
 for(let i=0;i<nodes.length;i++){
  const n=nodes[i];const cx=x+n.x*scale,cy=y+n.y*scale;
  s.addShape(S.ellipse,{x:cx-.18,y:cy-.18,w:.36,h:.36,
   fill:{color:C.bg},line:{color:colored.includes(i)?C.teal:C.blue,width:2.7}});
  text(s,n.label,cx-.22,cy-.13,.44,.26,13,C.white,{align:'center',bold:true});
 }
}
const sources={
 lv:'Lozano & Valiente (2004); source and Lean proof crosswalk',
 d16:'Droschinsky, Kriege & Mutzel (MFCS 2016)',
 d18:'Droschinsky, Kriege & Mutzel (MFCS 2018)',
 project:'Repository proofs/PROOF_STATUS.md, 2026-11-14 snapshot',
 app:'APTED; GumTree; RefactoringMiner; application pilot is proposed'
};
function notes(s,links){
 s.addNotes(`[Sources]\n${links.map(u=>'- '+u).join('\n')}\n[/Sources]`);
}
let s = pptx.addSlide(); head(s,1,'Maximum common structure in trees','Three problem families',sources.lv);
card(s,.55,2.05,3.85,3.65,'ORDERED','Embedded subtrees\nEdge contractions\nChild order preserved',C.teal);
card(s,4.75,2.05,3.85,3.65,'UNORDERED','Weighted isomorphism\nChild permutations\nPartial bipartite matching',C.amber);
card(s,8.94,2.05,3.85,3.65,'TOPOLOGICAL','Skipped vertices\nPath constraints\nDistance penalties',C.rose);
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf','https://doi.org/10.4230/LIPIcs.MFCS.2016.33','https://doi.org/10.4230/LIPIcs.MFCS.2018.54']);

s=pptx.addSlide();head(s,2,'Ordered edge contraction','Operations determine feasible mappings',sources.lv);
const b=[{x:0,y:0,label:'r'},{x:0,y:1.2,p:0,label:'a'},{x:-.64,y:2.4,p:1,label:'b'},{x:.64,y:2.4,p:1,label:'c'}];
const a=[{x:0,y:0,label:'r'},{x:0,y:1.2,p:0,label:'a'},{x:0,y:2.4,p:1,label:'b'}];
tree(s,b,3,2.23,1.0,[3]);tree(s,a,10.2,2.23,1.0,[2]);
text(s,'BEFORE',1.62,1.75,2.7,.4,20,C.muted,{align:'center'});
text(s,'AFTER',8.86,1.75,2.7,.4,20,C.muted,{align:'center'});
text(s,'CONTRACT',5.38,3.24,2.2,.6,19,C.teal,{align:'center',bold:true});
line(s,5.5,3.98,7.9,3.98,C.teal,3);
text(s,'Splice children at the same ordered position; retain the root.',1.1,6.17,11.15,.55,21,C.white,{align:'center'});
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf']);

s=pptx.addSlide();head(s,3,'A rooted tree is a balanced word','Depth-first encoding',sources.lv);
tree(s,b,3.2,2.15,.95);
rectangle(s,6.35,2.02,5.80,2.27);
text(s,'0  0  1  0  1  1',6.75,2.57,5.00,1.03,35,C.teal,{align:'center',bold:true});
text(s,'0 = descend      1 = return',5.75,4.62,6.8,.4,21,C.muted,{align:'center'});
text(s,'semilength = number of tree edges = 3',1.0,6.22,11.3,.45,21,C.amber,{align:'center'});
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf']);

paragraph(pptx.addSlide(),'Paired deletion mirrors contraction',
 'Remove a matched 0...1 pair and retain its interior. The tree children are spliced in the corresponding position. The theorem is proved in both directions for the operational relation.',
 '001011    →    0011          tree contraction <=> word deletion',4,sources.project);
notes(pptx._slides[pptx._slides.length-1],['https://www.cs.upc.edu/~antoni/subtree.pdf']);

s=pptx.addSlide();head(s,5,'The three-way dynamic program','Lozano–Valiente / Lemma 8',sources.lv);
text(s,'a = 0 x 1 y          b = 0 u 1 v',1.3,1.68,10.8,.52,28,C.white,{align:'center'});
card(s,.67,2.52,12,1.12,'KEEP FIRST PAIR','1 + L(x,u) + L(y,v)',C.teal);
card(s,.67,3.84,12,1.12,'CONTRACT LEFT','L(x+y, b)',C.amber);
card(s,.67,5.16,12,1.12,'CONTRACT RIGHT','L(a, u+v)',C.rose);
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf']);

s=pptx.addSlide();head(s,6,'What the proof establishes','Specification, soundness, optimality',sources.project);
card(s,.75,1.80,5.60,1.85,'SPECIFICATION','Maximum over all independently feasible common contractions',C.teal);
card(s,6.98,1.80,5.60,1.85,'SOUNDNESS','Every recurrence candidate decodes to a feasible common tree',C.blue);
card(s,.75,4.15,5.60,1.85,'OPTIMALITY','Every common tree fits a recurrence branch',C.amber);
card(s,6.98,4.15,5.60,1.85,'COMPLEXITY','State count and concrete implementation costs are separate proofs',C.rose);
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf']);

paragraph(pptx.addSlide(),'Extensions: node affinities and witnesses',
 'Original code supports optional compatibility or affinity functions, original-input identifiers, and separate embedding/isomorphism modes. Specifications must be recovered independently; Cython might be wrong.',
 'score(M) = Σ (u,v)∈M affinity(u,v)   [illustrative contract]',7,sources.project);
notes(pptx._slides[pptx._slides.length-1],['https://github.com/Erotemic/networkx_algo_common_subtree']);

s=pptx.addSlide();head(s,8,'Unordered children require weighted matching','Droschinsky 2016 / rooted subproblem',sources.d16);
const vals=[[8,1,4],[3,7,2]];
for(let r=0;r<2;r++) for(let c=0;c<3;c++){
 const x=4.52+c*1.28,y=2.13+r*1.10,hl=(r===c);
 rectangle(s,x,y,1.07,.9,C.panel,hl?C.teal:C.outline);
 text(s,String(vals[r][c]),x+.15,y+.14,.77,.56,25,hl?C.teal:C.white,{align:'center',bold:hl});
}
text(s,'Best partial matching: 8 + 7 = 15',2.0,4.91,9.33,.66,27,C.amber,{align:'center',bold:true});
text(s,'Children can be permuted; unmatched branches are allowed.',1.7,6.06,9.93,.45,20,C.muted,{align:'center'});
notes(s,['https://doi.org/10.4230/LIPIcs.MFCS.2016.33']);

paragraph(pptx.addSlide(),'Reuse matching work across related states',
 'A generic Hungarian solver on each subtree pair can be correct but fails to establish the published optimized bound. Related matching instances carry reusable structure.',
 'Published 2016 time bound: O(n² Δ)   [not automatic for reference code]',9,sources.d16);
notes(pptx._slides[pptx._slides.length-1],['https://doi.org/10.4230/LIPIcs.MFCS.2016.33']);

s=pptx.addSlide();head(s,10,'Skipped vertices change the edge score','Droschinsky 2018 / Definition 4',sources.d18);
tree(s,[{x:0,y:0,label:'A'},{x:0,y:1.3,p:0,label:'B'}],3.15,2.24,1.0);
tree(s,[{x:0,y:0,label:'A'},{x:0,y:1.1,p:0,label:'X'},{x:0,y:2.2,p:1,label:'B'}],10.10,2.05,1.0,[1]);
text(s,'length 1',1.65,1.72,3.0,.35,19,C.teal,{align:'center'});
text(s,'length 2',8.61,1.72,3.0,.35,19,C.amber,{align:'center'});
text(s,'1 + 1 - 0.25 = 1.75',2.5,5.26,8.33,.55,29,C.teal,{align:'center',bold:true});
text(s,'No direct-edge reward when either path has skipped vertices.',1.3,6.14,10.73,.45,20,C.rose,{align:'center'});
notes(s,['https://doi.org/10.4230/LIPIcs.MFCS.2018.54']);

s=pptx.addSlide();head(s,11,'Two DP states: mapped and skipped','Droschinsky 2018 / rooted recurrence',sources.d18);
card(s,.75,1.90,5.62,2.70,'M(u,v)','Map endpoints: node reward plus maximum child matching',C.teal);
card(s,6.97,1.90,5.62,2.70,'S(u,v)','Skip one intermediate vertex, pay p, continue in either tree',C.amber);
text(s,'Child-pair reward = max(direct edge + M, skipped continuation S)',.8,5.23,11.9,.63,21,C.white,{align:'center'});
text(s,'Reference DP: exhaustive matching; optimized 2018 bound is separate.',1.0,6.27,11.35,.38,18,C.muted,{align:'center'});
notes(s,['https://doi.org/10.4230/LIPIcs.MFCS.2018.54']);

s=pptx.addSlide();head(s,12,'From mathematics to verified executable code','Separate assurance layers',sources.project);
const cols=[['SPEC','Independent feasible mappings',C.teal],['DP PROOF','Recurrence optimality',C.blue],['AENEAS','Real Rust source refinement',C.amber],['COST','Measured and proved resource bounds',C.rose]];
cols.forEach((p,i)=>card(s,.40+3.23*i,2.24,2.91,2.9,p[0],p[1],p[2]));
text(s,'The fastest production backend may still lie outside the current proof boundary.',.86,6.25,11.75,.42,18,C.muted,{align:'center'});
notes(s,['https://github.com/Erotemic/networkx_algo_common_subtree']);

s=pptx.addSlide();head(s,13,'Candidate application: structural code comparison','A controlled pilot, not a claimed win',sources.app);
[['PARSE','code revisions → AST',C.teal],['MATCH','ordered embedding / affinity',C.blue],['BASELINES','APTED, GumTree, RefactoringMiner',C.amber],['EVALUATE','mapping quality, runtime, memory',C.rose]].forEach((p,i)=>card(s,.40+3.23*i,2.25,2.91,2.94,p[0],p[1],p[2]));
text(s,'Different objectives: evaluate on a shared downstream task.',.6,6.15,12.1,.48,20,C.white,{align:'center'});
notes(s,['https://github.com/DatabaseGroup/apted','https://doi.org/10.1145/3597503.3639148','https://arxiv.org/abs/2403.05939']);

s=pptx.addSlide();head(s,14,'What would justify a new paper?','Distinguish reproduction from a new contribution',sources.app);
[['VERIFICATION','Source-level Rust theorems',C.teal],['EXTENSIONS','A new precisely specified scoring or constraint model',C.blue],['ENGINEERING','Reproducible wins vs. strong native baselines',C.amber],['APPLICATION','Measured benefit on a held-out public task',C.rose]].forEach((p,i)=>{
 card(s,.92,1.7+i*1.22,11.5,1.07,p[0],p[1],p[2]);
});
notes(s,['https://www.cs.upc.edu/~antoni/subtree.pdf','https://doi.org/10.4230/LIPIcs.MFCS.2016.33','https://doi.org/10.4230/LIPIcs.MFCS.2018.54']);

// Intended overlays (text inside cards, headings, tree edges) are purposeful.
// Boundary detection is still run on every slide.
if (warnIfSlideElementsOutOfBounds) {
  for(const sl of pptx._slides) warnIfSlideElementsOutOfBounds(sl,pptx);
}
const dest=path.join(__dirname,'media','common-subtree-storyboard.pptx');
fs.mkdirSync(path.dirname(dest),{recursive:true});
pptx.writeFile({fileName:dest}).then(()=>console.log('Wrote',dest));
