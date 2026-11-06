# T13: Dijkstra on the word RAM, phase 1 plan

Branch `t13-dijkstra-plan`, based on `ea36c1fe` (main after the #442 merge). Line numbers are at
that commit. Paths: `C/` = `Complexity/Computability/WordRAM/`, `A/` = `Complexity/Algorithms/WordRAM/`.
"(inferred)" marks what I derived rather than read.

## The proposed phase-1 statement

File: `A/Dijkstra/Statement.lean` (imported from `Complexity.lean`; `lake build --wfail` passes,
no `sorry`). Core part:

```lean
structure Instance where
  n : ℕ
  weight : Fin n → Fin n → Option ℕ   -- `some c`: edge u → v of weight c; `none`: no edge
  source : Fin n

def Instance.Vertex (I : Instance) : Type := Fin I.n
instance : Quiver I.Vertex where Hom u v := {c : ℕ // I.weight u v = some c}

noncomputable def Instance.dist (u v : Fin I.n) : ℕ∞ :=
  ⨅ p : Quiver.Path (V := I.Vertex) u v, p.addWeight I.arrowWeight

def Instance.maxWeight : ℕ := Finset.univ.sup fun uv => (I.weight uv.1 uv.2).getD 0
def Instance.encode : List ℕ := n :: source :: (matrix row by row, none ↦ 0, some c ↦ c + 1)
def Instance.outAddr (v : Fin I.n) : ℕ := I.n * I.n + 3 + v
def encodeDist (d : ℕ∞) : ℕ := if d = ⊤ then 0 else d.toNat + 1

def QuadraticSpec {r : ℕ} (p : Program .standard r) (K : ℕ) : Prop :=
  ∀ (I : Instance) (w : ℕ), Fits w ((I.n + 2) ^ 2 * (I.maxWeight + 2)) →
    ∃ t m, Runs w p (.init I.encode) t m ∧ (∃ v, step w p t = .halt v) ∧
      m + 1 ≤ K * I.n ^ 2 ∧
      ∀ v : Fin I.n, t.data.mem (I.outAddr v) = encodeDist (I.dist I.source v)

def QuadraticStatement : Prop :=
  ∃ r, ∃ p : Program .standard r, ∃ K, QuadraticSpec p K
```

Plus a corollary form in the library's own notion (`C/Function.lean:107`):

```lean
abbrev Query := Σ I : Instance, Fin I.n
def QueryStatement : Prop :=
  UniformComputableInO .standard (fun q : Query => encodeDist (q.1.dist q.1.source q.2))
    (fun _ q => q.1.encode ++ [(q.2 : ℕ)]) (fun q => q.1.n) (fun n _ => n ^ 2)
    (fun q w => Fits w ((q.1.n + 2) ^ 2 * (q.1.maxWeight + 2)))
```

The phase-1 deliverable would be a concrete structured program `dijkstra : Code .standard r`
and a theorem `QuadraticSpec (dijkstra.program out) K` with an explicit `K`; `QuadraticStatement`
and `QueryStatement` follow from it. The statement file quantifies over the program (`∃ p`)
only because the program is not written yet; `QuadraticSpec` takes it as a parameter, so the
final theorem names the actual program and a reader can check it is Dijkstra's algorithm.

A sanity lemma `Instance.dist_self : I.dist u u = 0` is proved, so `dist` is not trivially `⊤`.

## Decisions, one line each

| Item | Choice | Reason |
|---|---|---|
| Input | words `n, s`, then the `n × n` matrix row by row; entry `0` = no edge, `c + 1` = weight `c`; entry `(u, v)` at address `u n + v + 3` | O(n²) reading fits the O(n²) bound; one row scan per extracted vertex; same layout as `USTCONInstance` (`Complexity/Computability/Complexity/Problems/USTCON.lean:64-78`) |
| Output | memory cells `n² + 3 + v` (just past the input) at the halting state; `0` = unreachable, `d + 1` = distance `d` | no library notion returns a vector (see survey §2); a width-independent encoding of `⊤` keeps the statement free of `w` |
| Assumption | weights in ℕ (so nonnegative); `Fits w ((n + 2)² (W + 2))`, `W` = largest weight | bounds every address (`≤ n² + 2n + 3`), the matrix entries (`≤ W + 1`), and every tentative distance (`≤ n W + 1`) and sum (`≤ (n + 1) W + 2`), with slack for two scratch arrays (inferred, from the planned layout below) |
| Basis | `Basis.standard` | the library's default and that of every algorithm in `A/`; the `ram[...]` notation's binary operations are standard (`C/Notation.lean:21, 30-31`); the program uses `*` (for `u n` row offsets), which the additive basis lacks (`C/Basis.lean:307-308`: only add and sub); `MapOp` in `A/ElementDistinctness.lean:145-146` maps additive → standard, not back, so an additive version would need its own program and cost proof. `Basis.exact` makes truncated subtraction fault (`C/Basis.lean:193`) and gains nothing here |
| Time | `m + 1 ≤ K n²`, halt included, one program for every `w`; `K` existential in the statement, explicit in the final theorem | uniform: one fixed program for every `w`; the statements do not forbid reading `w` (`width d`, `C/Defs.lean:207-208`; uniform programs may use it, `C/Function.lean:18-20`), but the planned implementation will not read `w`; `n ≥ 1` always since `source : Fin n`, so `K n²` needs no `+1` |
| Correctness | final memory of a halting run, stated with the core `Runs`/`step` (`C/Defs.lean:431, 357`); corollary via `UniformComputableInO` | `Executes` (`C/Defs.lean:436`) and `Program.ComputesInTime` (`C/Function.lean:59`) expose only the halt register, not memory |
| Shortest-path spec | Mathlib `Quiver.Path` + `Quiver.Path.addWeight` (`Mathlib/Combinatorics/Quiver/Path/Weight.lean:47`), infimum in `ℕ∞` (`⊤` = no path) | reuses Mathlib's paths and path weights; `SimpleGraph.dist`/`edist` are unweighted and undirected; Mathlib's `Digraph` has no walks; CSLib has no graph library |

## Survey

### 1. Word RAM core (`C/`)

- Machine: registers `Fin r → ℕ`, memory `ℕ → ℕ` (`C/Defs.lean:209`); `Fits w v := v < 2^w`
  (`:156`); ops `const | copy | alu | load | store` (`:160`), `jump | branch | halt` (`:190`).
  `halt i` returns one register (`:366`). One instruction = one time unit.
- Input: `Data.init input` puts `input.length` at address 0 and the words at `1..len`; all other
  memory is `0` (`C/Defs.lean:545-547`). `InputFits` (`:563-565`) asks the input length and
  every input word to fit.
- Structured layer: `Code` (`C/Structured.lean:80`) with big-step `Exec` counting exactly the
  instructions of the compiled flat program (`:126`, header `:17-22`); `ExecWithin` (`:148`)
  composes like Hoare logic; `ExecWithin.loop_invariant` (`:324`) is the loop rule with an
  invariant and a measure. `Exec.runs` (`C/Compile.lean:136`) turns a structured execution into
  a flat `Runs` with the same count; `Code.program c out = c.assemble 0 ++ [.halt out]` (`:82`).
- Arrays: `alloc`, `readAt`, `writeAt` (`C/Allocation.lean:185, 252, 256`) with exact-count specs;
  `Block.Realizes` (`:75`) and `HeapAssertion.array` (`C/Heap.lean:118`) describe arrays in
  memory. `Modifies` (`C/Heap.lean:67`) and the frame rule (`:140`) handle untouched regions.
- Notation `ram[ … ]` and the `ram_eval` symbolic-execution tactic (`C/Notation.lean:12-48`).
- `Trace.lean` logs memory probes; `Dynamic.lean` charges per-operation cost of data structures
  (`DynamicProgram`, `C/Dynamic.lean:53`); `RAMInput.lean` compiles additive programs to the
  log-cost `Cslib.RAM`. None of these is needed for phase 1.

### 2. Computation notions after #430 (`C/Function.lean`, `C/Time.lean`)

- `Program.ComputesInTime p encode time allowed f` (`Function:59`): for every admitted `(a, w)` with
  fitting input, `Executes w p (.init (encode w a)) (f a) n ∧ n ≤ time a w`. Output `f a : ℕ` is
  the halt register. `WordSizeDependentProgram B r := ℕ → Program B r` (`Time:131`) and its
  `ComputesInTime` (`Function:66`) allow the code to depend on `w`.
- `ComputableInTime` (`:73`, family with bounded code length), `UniformComputableInTime` (`:79`,
  one program), `…LogWord` (`:86, :93`, admitted widths `≥ logWidth k (size a)`),
  `ComputableInO`/`UniformComputableInO` (`:100, :107`, `time a w ≤ c · T (size a) w` for
  `size a ≥ n₀`), `…InPolyTime` (`:115, :122`).
- So the leads are right: all of these compute one ℕ. A distance vector needs either one
  statement per queried vertex (`QueryStatement`) or a memory-output statement (`QuadraticSpec`).
  No memory-output notion exists in `C/` (searched `^def .*(Output|Leaves|Halts|Computes)`).
- A `LogWord` form does not fit here: distances need `w ≳ log n + log W`, and `W` is not bounded
  by `n`. The admitted-width predicate is therefore an explicit `Fits` condition.

### 3. Nearest existing pattern: element distinctness (`A/ElementDistinctness.lean`)

It reads an array from the input, allocates a zeroed table, runs one loop, and answers in a
register. Its proof is the template for phase 1:
`setup_spec` (`:183`) → loop `Invariant` structure (`:158`) → `body_spec` (`:216`) →
`exit_spec` (`:289`) → `answers` (`:304`, `Code.Answers` in `14 n + 15`, via
`ExecWithin.loop_invariant`) → `decidesInTime_nodup` (`:318`, flat program, `16 (n + 1)`) →
`uniformLinearTime_nodup` (`:329`). The fit condition is `Fits w (2 n + 1)`, derived from
`logWidth 2 n ≤ w` (`:169`). The other algorithms (Stack, Queue, PrefixSums, vEB, FusionTree,
DynamicArray) certify data-structure operations from a prepared state through
`DynamicProgram`/`Stateful` bounds, not input-to-output computations; the Stack controller
(`A/Stack/Controller.lean:201`) is the only other `ComputesInTime` result, with a scalar output.

### 4. The older survey T5

`reports/T5-wordram-survey.md` is not on main; it is on branch `t5-wordram-survey` at `19a41424`,
written at `8a2d724d`. Its model description still holds. Out of date after #430/#442: the
line numbers (e.g. `Fits` moved from Defs:143 to :156, `decidesInTime_nodup` from :287 to :318),
and its summary of the function notions ("∃ flat program"): the non-uniform notions now take a
width-indexed family with bounded code (`Function:73-77`), and `ComputableInO`, `…LogWord` and
`Uniform…` variants were added.

### 5. Shortest-path specifications

- Mathlib `SimpleGraph.dist`/`edist` (`Mathlib/Combinatorics/SimpleGraph/Metric.lean`) and this
  repo's `Complexity/Foundations/Combinatorics/SimpleGraph/Metric.lean`: unweighted, undirected.
- Mathlib `Digraph` (`Mathlib/Combinatorics/Digraph/Basic.lean`): no walks or weights.
  `Complexity/Computability/Complexity/Problems/Hamiltonian.lean:28` notes the same gap.
- Mathlib `Quiver.Path` with `Quiver.Path.addWeight` and `addWeightOfEPs`
  (`Mathlib/Combinatorics/Quiver/Path/Weight.lean:47, 55`): directed paths with summed weights.
  Chosen. A quiver on a type synonym `I.Vertex` whose arrows `u ⟶ v` are the weights `c` with
  `weight u v = some c` gives exactly the paths of the weighted digraph. `Path.cons` appends an
  edge at the end, which is the shape of a relaxation step `d(v) ≤ d(u) + c(u, v)`.
- CSLib (`.lake/packages/cslib/Cslib`): no graph definitions (searched "graph").
- No `Dijkstra`, `shortest path` or `Bellman` anywhere in the repo, Mathlib or CSLib.

## Proof plan for phase 1

Planned layout (inferred; the proof may move scratch arrays): `D` = the output block
`n² + 3 + v`; visited flags at `n² + 3 + n + v`. For `QuadraticSpec` both are already `0` by
`Data.init`, so `D[v] = 0` means `∞`. For `QueryStatement` they are not all `0`: the target word
is appended, so it sits at `n² + 3` = `outAddr 0`, and the length header at address 0 is
`n² + 3`, not `n² + 2`. The query wrapper must read `n` from address 1 (not from the header),
save the target, clear that cell, and only then run the core loops. Program over about 16
registers:

1. setup: read `n`, `s`; compute bases with one multiplication; `D[s] ← 1`.
2. outer loop (at most `n` rounds): scan `v < n` for the unvisited `v` with the least nonzero
   `D[v]`; if none, stop; mark it visited; scan its matrix row: for each edge `u → v` with
   `v` unvisited, `cand ← D[u] + entry − 1`, and `D[v] ← cand` if `D[v] = 0 ∨ cand < D[v]`.
3. `halt`.

Each round is two linear scans, so `≈ c n` instructions per round and `K n²` total with `K`
around 40-60 (inferred).

Proof pieces:

- Graph lemmas (~300-450 lines): `dist` is attained when finite (`ℕ∞` is well-ordered);
  `dist v ≤ dist u + c` along an edge; the cut lemma: for a set `S` containing `s`, every path
  from `s` to a vertex outside `S` has a first edge leaving `S` (induction on `Quiver.Path`);
  the standard Dijkstra invariant: for `v ∈ S`, `D[v] = dist v`; for `v ∉ S`, `D[v]` is the least
  weight of a path whose inner vertices are all in `S`.
- Encoding lemma (~50-100 lines): `I.encode` has the matrix entry `(u, v)` at index `u n + v + 2`
  (`List.flatMap` over `List.finRange`), and every word fits under the `Fits` hypothesis.
- Program lemmas (~800-1200 lines): one invariant + `loop_invariant` application for each of the
  three loops (outer, min-scan, relax-scan), following `A/ElementDistinctness.lean`; memory
  reasoning via `Function.update` and the frame lemmas of `C/Heap.lean`.
- Wrapper (~50 lines): `Exec.runs` + the final `halt` give `QuadraticSpec`, then
  `QuadraticStatement`; `QueryStatement` needs a variant program that saves the target word
  (at `outAddr 0`), clears that cell, runs the core loops, then loads `D[t]` and halts (its own
  small setup proof, which also handles the changed length header; the core loops are reused).

Total: about 1300-1800 lines (inferred, by comparison with element distinctness, ~360 lines for
one loop and no graph theory).

Main risks:

1. Nested loops: the inner scans need invariants about memory that the outer invariant then
   consumes; time arithmetic for nested `loop_invariant` bounds (`μ (T + 2) + 2`) is tedious.
2. The encoding of `⊤` as `0` adds case splits to every comparison in the program and proof. An
   alternative is an internal sentinel and a final conversion pass, which costs a third scan.
3. Dependent types in `Quiver.Path` over the synonym `I.Vertex` may make the cut lemma awkward;
   fallback: prove the graph lemmas over an inductive "walk of weight `d`" relation and show it
   equals `dist` once.
4. Simp performance of `ram_eval` on a 16-register file with memory updates.

## Phase 2 notes (m log n)

- Input: adjacency lists in CSR form (`n`, `m`, `s`, offsets of length `n + 1`, then
  `(target, weight)` pairs), `O(n + m)` words. An unsorted edge list also works but costs an
  extra bucketing pass.
- Heap: binary heap of size `≤ n` keyed by tentative distance, with a position array for
  decrease-key; `O(log n)` per operation. A lazy heap without decrease-key holds up to `m`
  entries and costs `O(m log m)`, which is `O(m log n)` only when `m ≤ n^O(1)` (true without
  parallel edges, `m ≤ n²`). No priority queue exists on the word RAM in the library; vEB
  (`A/VanEmdeBoas/`) has only membership certified (T5), so the heap is new work.
- Spec: phase 2 gets its own instance type; it maps to `Instance` at the spec level (weight of
  `u → v` = the least weight of its parallel edges) or the quiver arrows are generalized to edge
  indices. `dist` and the graph lemmas carry over.
- Does phase 1 block phase 2? No. The matrix encoding is specific to phase 1, but phase 2 states a
  separate theorem with its own encoding; the shared parts (`dist`, the cut lemma, the invariant)
  are encoding-independent. The memory-output form of `QuadraticSpec` also fits phase 2.

## Questions for the user

1. Main form: memory-output vector (`QuadraticSpec`) as the main theorem, with the per-target
   `QueryStatement` (library's `UniformComputableInO`) as a corollary? Recommendation: yes;
   the vector form is what Dijkstra computes; the query form ties it to the library's notions.
2. Constant: state the final theorem with an explicit `K` (e.g. `QuadraticSpec dijkstraProgram 60`)
   or only `O(n²)`? Recommendation: explicit `K` in the theorem, `∃ K` in the summary statement.
3. Unreachable encoding `0` and distance `d` as `d + 1`? Recommendation: keep; it is independent
   of `w`. The alternative, `2^w − 1` as `∞`, ties the output to the word size.

Other changes found (not made): a reusable memory-output notion in `C/Function.lean` (e.g.
`Program.ComputesMemInTime`), if phase 2 or other algorithms need vector outputs too.
