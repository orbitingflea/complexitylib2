# T14: Dijkstra on the word RAM, phase 2 plan (O(m log n))

Branch `t14-dijkstra-heap-plan`, based on `de10fb7b` (fork main with phase 1, T13, merged). Line
numbers are at that commit. Paths: `C/` = `Complexity/Computability/WordRAM/`,
`A/` = `Complexity/Algorithms/WordRAM/`, `D/` = `A/Dijkstra/`. "(inferred)" marks what I derived
rather than read.

## The proposed phase-2 statement

File: `D/HeapStatement.lean` (imported from `Complexity.lean`; `lake build --wfail` and
`lake exe mk_all --check` pass; no `sorry`). Core part:

```lean
structure ListInstance where
  n : ℕ
  adj : Fin n → List (Fin n × ℕ)   -- (v, c) ∈ adj u: an edge u → v of weight c; repeats allowed
  source : Fin n

namespace ListInstance
variable (G : ListInstance)

/-- The least weight of an edge from `u` to `v`, and `none` when there is no such edge. -/
def lightest (u v : Fin G.n) : Option ℕ :=
  ((G.adj u).filterMap fun e => if e.1 = v then some e.2 else none).min?

/-- The phase-1 weight-matrix instance, keeping the lightest edge of each pair. -/
def toInstance : Instance where
  n := G.n
  weight := G.lightest
  source := G.source

noncomputable def dist (u v : Fin G.n) : ℕ∞ := G.toInstance.dist u v

def m : ℕ := ∑ u, (G.adj u).length
def maxWeight : ℕ := Finset.univ.sup fun u => ((G.adj u).map Prod.snd).foldr max 0
def offset (u : ℕ) : ℕ := (((List.finRange G.n).take u).map fun x => (G.adj x).length).sum

/-- `n`, the source, the offsets of `0, …, n`, then every edge as `target, weight`. -/
def encode : List ℕ :=
  G.n :: (G.source : ℕ) ::
    ((List.range (G.n + 1)).map G.offset ++
      (List.finRange G.n).flatMap fun u => (G.adj u).flatMap fun e => [(e.1 : ℕ), e.2])

/-- The `n` cells just past the input (`n + 2 m + 3` words). -/
def outAddr (v : Fin G.n) : ℕ := G.n + 2 * G.m + 4 + v

theorem lightest_eq_some_iff {u v : Fin G.n} {c : ℕ} :
    G.lightest u v = some c ↔ (v, c) ∈ G.adj u ∧ ∀ c', (v, c') ∈ G.adj u → c ≤ c'
theorem lightest_eq_none_iff {u v : Fin G.n} :
    G.lightest u v = none ↔ ∀ c, (v, c) ∉ G.adj u
end ListInstance

def LogLinearSpec {r : ℕ} (p : Program .standard r) (K : ℕ) : Prop :=
  ∀ (G : ListInstance) (w : ℕ), Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)) →
    ∃ t steps, Runs w p (.init G.encode) t steps ∧ (∃ v, step w p t = .halt v) ∧
      steps + 1 ≤ K * (G.m + 1) * (Nat.log 2 G.n + 1) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v)

def LogLinearStatement : Prop :=
  ∃ r, ∃ p : Program .standard r, ∃ K, LogLinearSpec p K
```

The shape is that of `QuadraticSpec` (`D/Statement.lean:127-137`); only the instance, the `Fits`
term and the time term change. `encodeDist` (`D/Statement.lean:120`) and `Instance.dist`
(`D/Statement.lean:89`) are reused as they are. As in phase 1, the final theorem will name the
concrete program and an explicit `K` (`LogLinearSpec (dijkstraHeap.program out) K`), and
`LogLinearStatement` follows.

Checked by `#eval` on a 3-vertex example with a parallel edge (scratch file, not committed): the
encoding has `n + 2m + 3` words, edge `j` has its target at word `n + 3 + 2j`, and `lightest`
takes the minimum of the parallel weights.

## Decisions, one line each

| Item | Choice | Reason |
|---|---|---|
| Input | CSR adjacency arrays: words `n, s`, offsets `off 0 … off n` (`off u` = number of edges out of vertices `< u`, so `off n = m`), then each edge as `target, weight` in list order; `n + 2m + 3` words | O(n + m) words; the edges out of `u` are a contiguous range found in O(1) from `off u, off (u + 1)`; the prefix `n :: s :: …` matches phase 1 (`D/Statement.lean:108-111`). A plain edge list would need a bucketing pass first (more proof, and an O(n) pass that rules out the `m + 1` time form below) |
| Parallel edges, self-loops | allowed; `toInstance` keeps the lightest edge of each pair (`lightest`, via `List.min?`); self-loops stay as arrows `u → u` of the phase-1 quiver | no side condition on the input; the phase-1 quiver has at most one arrow per pair (`D/Statement.lean:80-81`), and the lightest parallel edge gives the same distances (a heavier parallel edge can be swapped for the lighter one in any path; inferred, standard). `lightest_eq_some_iff` / `lightest_eq_none_iff` (proved) pin the map down; self-loops never shorten a path since weights are in ℕ |
| Distance | `G.dist := G.toInstance.dist`, the phase-1 `Instance.dist` | the same notion of distance as phase 1, so phase 1's `Inv` lemmas apply to `G.toInstance` |
| Output | as phase 1: memory cells `outAddr v = n + 2m + 4 + v` just past the input, `0` = unreachable, `d + 1` = distance `d` | the form the user approved for phase 1 ("1 可以 2 存在即可 3 可以") |
| Assumption | weights in ℕ; `Fits w (8 (n + m + 2) (W + 2))`, `W` = largest weight over all list entries (parallel ones included) | i.e. `w ≥ log₂(n + m + 2) + log₂(W + 2) + 3`. Bounds every address: input `≤ n + 2m + 3`, plus four `n`-cell arrays (distances, heap, positions, visited flags) `≤ 5n + 2m + 7`; every distance word `≤ (n − 1) W + 1` and candidate `≤ n W + 1`; heap child index `≤ 2n + 1` (inferred, from the planned layout). `W` must cover every list weight, since the program adds each one, not only the lightest |
| Basis | `Basis.standard` | as phase 1; the heap index arithmetic `2 i`, `2 i + 1`, `i / 2` uses `mul`/`div` (or shifts), all in `BinOp` of the standard basis (`C/Basis.lean:99-140, 164`) |
| Time | `steps + 1 ≤ K (m + 1) (⌊log₂ n⌋ + 1)`, halt included, one program for every `w`, `K` existential in the statement and explicit in the final theorem | see "Time bound form" below |
| Correctness | final memory of a halting run, with the core `Runs`/`step`, as phase 1 | the library's computation notions return one register only (T13 report §2) |

## Time bound form

- **Chosen: `K (m + 1) (Nat.log 2 n + 1)`.** It is the literal "m log n" with `+1`s for `m = 0`
  and `n = 1`. It holds because the program needs no Θ(n) pass: memory past the input is `0`
  (`Data.init`, `C/Defs.lean:545-547`), so the distance, position and flag arrays start
  correct for free, `m = off n` is one load, and the offsets reach the adjacency list of any
  vertex in O(1). So the run touches only vertices it reaches. Each reached vertex other than the
  source is first reached through an edge, so at most `m + 1` vertices enter the heap, at most
  `m + 1` extract-mins run, at most `m` edges are relaxed, each heap operation costs
  O(log n) (heap size `≤ n`) (inferred, standard).
- `K (n + m) (log n + 1)` is the textbook form (CLRS §24.3 states `O((V + E) lg V)` for a binary
  heap). It follows from the chosen form, since `m + 1 ≤ n + m` when `n ≥ 1` (and `n ≥ 1` always,
  as `source : Fin n`). It would be the fallback if the `m + 1` amortization proves awkward.
- The two agree up to a factor of 2 when `m ≥ n − 1`, e.g. when every vertex is reachable from the
  source (each non-source vertex then has an incoming edge).
- `log` in Lean: `Nat.log 2 n + 1`, the same term as the library's `logWidth k n = k (Nat.log 2 n
  + 1)` (`C/Time.lean:94`). The `+1` is needed since `Nat.log 2 1 = 0`. `Nat.clog 2` would also
  give `0` at `n = 1`; `Nat.size n` equals `Nat.log 2 n + 1` for `n ≥ 1` (inferred) but is less
  used in the library.
- Uniform in `w`: one program, `K` independent of `w`; the planned program does not read `w`.

## The priority queue

### Library survey

- `C/Heap.lean`: finite-footprint memory assertions and a frame rule (separation-logic style), a
  memory model, not a priority queue (header, `C/Heap.lean:12-34`).
- `C/Allocation.lean`: `zeroFill`, `alloc`, `readAt`, `writeAt` with exact counts
  (`C/Allocation.lean:193, 259, 267`), arrays, not a priority queue.
- `C/Dynamic.lean`: the `DynamicProgram` interface (`C/Dynamic.lean:53`) for data structures whose
  operations are separate calls, each ending in `halt`; not a priority queue, and not usable as a
  subroutine inside one program (each call halts).
- `A/`: Stack, Queue, DynamicArray, PrefixSums, FusionTree, VanEmdeBoas, ElementDistinctness,
  Dijkstra. No priority queue (searched `priority|binary heap|decrease.?key|extract.?min|sift`
  over `Complexity/`; only unrelated hits). vEB has only membership certified (T13 report,
  phase 2 notes).
- CSLib (`.lake/packages/cslib`): no heap or priority queue (searched `priority|heap`).
- Batteries `Batteries.BinaryHeap` (`.lake/packages/batteries/Batteries/Data/BinaryHeap/`, rev
  `4453b52d`): a functional max-heap on `Vector` with direct keys, 0-based, with `heapifyUp`,
  `heapifyDown`, `insert`, `popMax`, `decreaseKey`, `increaseKey` (`Basic.lean:42-190`) and
  well-formedness lemmas `heapifyDown_wf`, `heapifyUp_topDown`, `insert_wf`, `popMax_wf`
  (`Lemmas.lean:195, 240, 389, 427`). It has no positions array and no lemma for
  `decreaseKey`/`increaseKey` beyond size. Usable only as a reference; a refinement proof (the
  RAM sift loop implements `heapifyUp` on an abstracted `Vector`) would fight dependent `Fin`
  indices and still miss the position array (inferred).

So the heap is new work, written as inline structured code (`⟪…⟫`), not as a `DynamicProgram`.

### Recommended design: binary min-heap with decrease-key and a positions array

- Arrays past the input, all `0` initially: distance words `D` (= the output cells), heap `H`
  (1-based, `H[1..size]`), positions `P` (`P[v] = i` iff `H[i] = v`, `0` = not in the heap),
  visited flags `F` (as phase 1).
- Keys are indirect: the key of `H[i]` is `D[H[i]]`; every vertex in the heap has `D ≠ 0`, so word
  order is distance order. Heap property: `D[H[i / 2]] ≤ D[H[i]]` for `2 ≤ i ≤ size`.
- Heap contents = the unvisited vertices with finite tentative distance. Then the root `u` is an
  unvisited vertex of least finite `D`, and unvisited vertices outside the heap have `D = ⊤`, so
  `u` meets the `hmin` and `hfin` hypotheses of phase 1's `Inv.step` (`D/Invariant.lean:176-177`).
- Operations: `siftUp i` (at most `Nat.log 2 i + 1` swaps; measure `Nat.log 2 i`), `siftDown i`
  (measure `Nat.log 2 size − Nat.log 2 i`), each swap also updating `P`; `insert v` (append,
  `siftUp`); `extractMin` (root out, last to root, `siftDown 1`); `decreaseKey v` (write `D[v]`,
  `siftUp P[v]`).
- Program: setup (read `n`, `s`, `m = off n`, compute array bases, `D[s] ← 1`, insert `s`); while
  the heap is not empty: `u ← extractMin`, `F[u] ← 1`, for each edge `(v, c)` of `u` with `F[v] = 0`:
  `cand ← D[u] + c`; if `D[v] = 0` then `D[v] ← cand`, `insert v`; else if `cand < D[v]` then
  `decreaseKey v` with `cand`; `halt`.

Why this one rather than lazy deletion (push duplicates, skip stale entries, no positions array):

1. **Statement.** Lazy deletion's heap holds up to `m + 1` entries, so its time is
   `O((m + 1) log (m + 1))`. With parallel edges `m` is not bounded by a polynomial in `n`, so this
   is not `O((m + 1) log n)`; we would have to forbid parallel edges (then `m ≤ n²` and
   `log (m + 1) ≤ 2 log n + 1`) or weaken the bound. Decrease-key keeps heap size `≤ n` with no
   input condition.
2. **Proof size.** Both need the same sift loops and the same heap-property argument, which is
   most of the work. Decrease-key adds the position array: two extra stores per swap and an
   inverse invariant `P[H[i]] = i`. Lazy deletion instead needs key/vertex pairs in the heap, a
   stale-entry skip in the outer loop, a multiset invariant ("every unvisited finite `v` has an
   entry `(D v, v)`, every entry `(d, v)` has `d ≥ D v`"), and an outer-loop measure counting
   entries rather than vertices. I judge these about equal (inferred); point 1 decides.

## What is reused from phase 1

As is (no change to phase-1 files):

- `Instance`, `Instance.dist`, `encodeDist` (`D/Statement.lean:64, 89, 120`); `decodeDist` and its
  two simp lemmas (`D/Invariant.lean:54-66`).
- `Instance.relax`, `Instance.Inv`, `Inv.init`, `Inv.step`, `Inv.eq_dist`
  (`D/Invariant.lean:86, 93, 158, 176, 233`), applied to `G.toInstance`. Glue needed in phase-2
  files: (a) relaxing the edges of `adj u` one at a time in list order gives
  `G.toInstance.relax D u` (min over parallel edges = `lightest`, via `lightest_eq_some_iff`);
  (b) `G.toInstance.maxWeight ≤ G.maxWeight` for `Inv.bound`; (c) an edge to a visited vertex
  never changes `D` — derivable from the conclusion of `Inv.step` together with `Inv.eq_of_mem`.
- `Instance.le_maxWeight` (`D/Invariant.lean:73`).
- The proof pattern: register file `Reg`, `distOf`/`visitedOf`-style readers of memory, an
  `OuterInv`, `setup_spec` / `round_spec` / `exit_spec` / wrapper (`D/Quadratic.lean:57-481`).

Would need a change to a phase-1 file (not made; listed under "Other changes found"):

- `Instance.dist_le_edge` (`D/Invariant.lean:113`) is private; making it public would shorten
  glue (c).
- `decodeDist_ne_top`, `decodeDist_le` (`D/Quadratic.lean:194, 198`) are private; phase 2 needs
  the same two facts. Moving them to `Invariant.lean` as public lemmas would avoid copies.
- `getD_flatMap_rows`, `init_past` (`D/Quadratic.lean:86, 121`) are private and matrix-specific;
  phase 2 needs CSR analogues (new).
- Not reused: `minScan`, `relax`, `relaxWord` (`D/Program.lean`): matrix-specific; phase 2 stores
  raw weights, not `c + 1`.

## Proof approach and size

Phase 1 calibration: its proof files are 1328 lines (`Invariant` 249, `Program` 165, `MinScan`
238, `Relax` 195, `Quadratic` 481).

| Piece | Lines (inferred) |
|---|---|
| CSR encoding lemmas: `Data.init G.encode` holds `n`, `s`, `off u`, edge `j`'s target and weight at the stated addresses; length; every word fits | 150-250 |
| Graph glue (a)-(c) above | 150-250 |
| Heap: a memory predicate (`size`, `H`, `P`, heap property, `P` inverse to `H`, contents as a `Finset`), `siftUp`/`siftDown` loop invariants ("heap except at `i`"), specs of `insert`, `extractMin`, `decreaseKey` with `O(log n)` counts | 800-1200 |
| Relax loop over the edge range of `u` | 300-400 |
| Outer loop, with an amortized loop rule, and the time bound | 400-500 |
| Wrapper to `LogLinearSpec` / `LogLinearStatement` | 50 |
| **Total** | **≈ 1900-2700** |

Main risks:

1. **The heap invariant through swaps.** Each swap writes four cells (`H[i]`, `H[j]`, `P[a]`,
   `P[b]`); the invariant is about `Function.update` chains on memory. Mitigation: state the heap
   over abstract functions `H, P : ℕ → ℕ` read from memory, prove the swap lemma once, and reuse
   it in both sift loops.
2. **Varying cost per round.** `ExecWithin.loop_invariant` (`C/Structured.lean:324`) charges one
   bound `T` per iteration; a round of Dijkstra costs `O((deg u + 1) log n)`, so a uniform `T` gives
   `n · max deg · log n`. A potential-style loop rule is needed (each iteration within
   `Φ x − Φ y` instructions, total `≤ Φ x₀ + 2`). It does not exist in `C/Structured.lean`
   (searched `potential|amortiz|theorem loop`); it is about 40 lines by strong induction from
   `loop_iter` (`C/Structured.lean:293`). Potential (inferred): `c (log n + 1)` times
   (edges out of unvisited vertices + `1` + number of unvisited vertices in the heap).
3. **`Nat.log` arithmetic** in the sift-loop measures (`Nat.log 2 (i / 2) = Nat.log 2 i − 1`
   for `i ≥ 2`, `Nat.log 2 (2 i + 1) = Nat.log 2 i + 1`); Mathlib has the base lemmas
   (`Nat.log_div_base`, `Nat.log_mul_base`, `Mathlib/Data/Nat/Log.lean:279, 229`).
4. **`ram_eval` cost** with about 25 registers (phase 1 used 17).
5. If the `m + 1` amortization is harder than expected, fall back to the `n + m` form, which
   would change only the time term of the statement (a weaker theorem; needs the user's OK).

## Not included

- A per-target `QueryStatement` as in phase 1 (`D/Statement.lean:140-150`).
  `UniformComputableInO` (`C/Function.lean:107`) takes one size function; with size `m + 1` the
  bound would read `O((m + 1) log (m + 1))`, which is not `O((m + 1) log n)` with parallel edges.
  It could be added later with size `n + m` and time `T k = k (log k + 1)`, valid when
  `m ≤ poly(n)`; I left it out.

## Questions for the user

1. Time form: `K (m + 1) (log₂ n + 1)` (chosen: the literal "m log n", strongest, and implies the
   textbook form) or `K (n + m) (log₂ n + 1)` (CLRS form, and lets the program spend O(n) on
   setup)? Recommendation: `m + 1`, with `n + m` as fallback only if the proof stalls.
2. Input: CSR adjacency arrays with offsets (chosen), or a plain edge list `u, v, c` (the
   program would bucket it first, which costs O(n + m) and forces the `n + m` form)?
   Recommendation: CSR.
3. Parallel edges: allowed, distance via the lightest one (chosen), or forbidden by a condition
   on the input? Recommendation: allowed; it costs only the `lightest` map and two proved lemmas.

## Other changes found (not made)

- Make `Instance.dist_le_edge` (`D/Invariant.lean:113`) public.
- Move `decodeDist_ne_top` and `decodeDist_le` (`D/Quadratic.lean:194, 198`) to
  `D/Invariant.lean` as public lemmas.
- A potential-style (amortized) loop rule in `C/Structured.lean` next to
  `ExecWithin.loop_invariant`; useful beyond Dijkstra.
- A reusable memory-output computation notion in `C/Function.lean` (already noted by T13).
