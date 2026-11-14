// Dashboard snapshot validation and formatting checks; no browser or dependencies.
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const assert = require('assert/strict');
const root = path.resolve(__dirname, '..');
const directory = path.join(root, 'tools/cache-origin/dashboard');
const source = fs.readFileSync(path.join(directory, 'app.js'), 'utf8');
const replacement = `  globalThis.testAPI = {validate, bytes, bitrate, duration, leanVersion,
    renderState(data, failed = false) {
      snapshot = data; fetchFailed = failed; renderFreshness(); renderStorage();
    }};
})();`;
if (!source.endsWith('  refresh();\n})();\n')) throw new Error('Unexpected script ending');
// Freeze this run's wall clock so relative-age assertions stay deterministic
// without treating later production snapshots as future data.
const now = Date.now();
class TestDate extends Date { static now() { return now; } }
const nodes = new Map();
function element() {
  return {textContent: '', className: '', hidden: false,
    addEventListener() {}, replaceChildren() {}, append() {}, setAttribute() {}};
}
const context = {
  document: {
    getElementById(id) { if (!nodes.has(id)) nodes.set(id, element()); return nodes.get(id); },
    querySelectorAll() { return []; }, createElementNS() { return element(); },
  },
  setInterval() {}, Intl, Date: TestDate, console,
};
vm.createContext(context);
vm.runInContext(source.replace('  refresh();\n})();\n', replacement), context);
const {validate, bytes, bitrate, duration, leanVersion, renderState} = context.testAPI;
const fixture = JSON.parse(fs.readFileSync(path.join(directory, 'preview-data.json'), 'utf8'));
validate(fixture);
const empty = JSON.parse(JSON.stringify(fixture));
empty.coverage = {since:null,until:null,records:0,invalid_records:0,excluded_requests:0,limited:true};
empty.series = []; empty.latest = null; empty.builds = []; empty.popular_builds = [];
empty.storage = {snapshot_at:null,stale:true,entry_count:null,artifact_count:null,mapping_count:null,artifact_bytes:null,mapping_bytes:null,logical_retained_bytes:null,saved_bytes:null,dedup_ratio:null,missing_artifacts:null,disk:{total_bytes:null,used_bytes:null,available_bytes:null,inodes_total:null,inodes_available:null}};
empty.gc = {status:'unknown',last_run_at:null,last_success_at:null,deleted_artifacts:null,deleted_mappings:null,deleted_bytes:null};
for (const win of Object.values(empty.windows)) {
  for (const key of Object.keys(win)) if(typeof win[key] === 'number')win[key]=0;
  win.status_counts={};win.median_seconds=null;win.p95_seconds=null;
}
validate(empty);
let failures = 0;
for (const mutate of [
  d=>{d.schema=2}, d=>{d.windows.day.seconds=-1}, d=>{d.storage=null},
  d=>{d.latest.revision='https://attacker.invalid/'},d=>{d.builds=[null]},
  d=>{d.series[0].body_bytes=Infinity},d=>{d.windows.hour.median_seconds='0'},
  d=>{d.gc.deleted_bytes=-1}, d=>{d.coverage.records=undefined},
  d=>{d.generated_at=new Date(now + 600001).toISOString()},
]) {
  const data=JSON.parse(JSON.stringify(fixture));mutate(data);
  try {validate(data)} catch(_) {failures++;continue}
  throw new Error('Invalid snapshot accepted');
}
if(bytes(null)!=='—'||bitrate(0)!=='0 bit/s'||duration(null)!=='—'||leanVersion('leanprover--lean4---v4.36.0-rc2')!=='Lean v4.36.0-rc2') throw new Error('Formatting assertion failed');

// A recent export can carry old inventory while its traffic data keeps refreshing.
const staleInventory = JSON.parse(JSON.stringify(fixture));
staleInventory.generated_at = new Date(now - 20000).toISOString();
staleInventory.storage.stale = true;
staleInventory.storage.snapshot_at = new Date(now - 6 * 86400000).toISOString();
staleInventory.storage.missing_artifacts = 99;
renderState(staleInventory);
assert.equal(nodes.get('freshness').textContent, 'Traffic updated just now');
assert.equal(nodes.get('notice').hidden, false);
assert.equal(nodes.get('notice').className, 'notice warning');
assert.match(nodes.get('notice').textContent, /Build and storage details are stale.*6 days ago/);
assert.match(nodes.get('notice').textContent, /Traffic statistics were refreshed separately/);
assert.doesNotMatch(nodes.get('notice').textContent, /missing artifacts|downloads may be unavailable/);
assert.equal(nodes.get('storage-freshness').textContent, 'Stale · updated 6 days ago');

const fresh = JSON.parse(JSON.stringify(staleInventory));
fresh.storage.stale = false; fresh.storage.missing_artifacts = 0;
fresh.storage.snapshot_at = fresh.generated_at;
renderState(fresh);
assert.equal(nodes.get('freshness').textContent, 'Updated just now');
assert.equal(nodes.get('notice').hidden, true);
assert.equal(nodes.get('storage-freshness').textContent, '');
fresh.storage.missing_artifacts = 1;
renderState(fresh);
assert.equal(nodes.get('notice').hidden, false);
assert.match(nodes.get('notice').textContent, /Some downloads may be unavailable/);

empty.generated_at = staleInventory.generated_at;
renderState(empty);
assert.match(nodes.get('notice').textContent, /Build and storage details are not available yet/);
assert.equal(nodes.get('storage-freshness').textContent, 'Waiting for first snapshot');
assert.doesNotMatch(nodes.get('notice').textContent, /NaN|Not recorded|days ago/);
const oldExport = JSON.parse(JSON.stringify(staleInventory));
oldExport.generated_at = new Date(now - 3600000).toISOString();
renderState(oldExport);
assert.match(nodes.get('notice').textContent, /statistics have not refreshed recently/);
assert.match(nodes.get('freshness').textContent, /^Snapshot from /);
renderState(staleInventory, true);
assert.match(nodes.get('notice').textContent, /latest snapshot could not be loaded/);

if (process.argv[2]) {
  const live = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
  validate(live);
  renderState(live);
  console.log('Captured live snapshot validation and rendering passed.');
}

console.log(`Frontend validation passed: populated/empty snapshots, ${failures} malformed snapshots rejected, formatting and fresh/stale/unavailable/failed-export states.`);
