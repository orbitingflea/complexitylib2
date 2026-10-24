# T15: formal abstract of Dijkstra's algorithm, O((m + 1) log n)

Branch `t15-dijkstra-abstract`, first based on `c766a2cf` (fork main with T14 merged), later
merged with `origin/main` `ddd3a2a9`. Line numbers in `C/` and `D/` are at `c766a2cf`; those in `X/`
are at the branch head. Paths: `C/` = `Complexity/Computability/WordRAM/`,
`D/` = `Complexity/Algorithms/WordRAM/Dijkstra/`, `X/` = `abstracts/ComplexityAbstracts/`.
"(inferred)" marks what I derived rather than read.

## Files

* `X/DijkstraAbstract.lean`: the abstract. It defines the graph, walks, the distance, the number
  of edges, the largest weight, the input and output layouts, and states `dijkstra_logLinear`.
  The proof is one line through the bridge. `#check_abstract` passes with the allowlist
  `Complexity.Computability.WordRAM.Defs` and `Complexity.Computability.WordRAM.Basis`.
* `X/DijkstraBridge.lean`: proves that the walk distance equals the library's distance
  (`walkDist_eq`) and transfers `logLinearStatement` (`logLinear`).
* `abstracts/ComplexityAbstracts.lean`: imports both.

No library file changed. No `catalogue.json` entry was added.

## Layout

Following "Lead with the mathematics" (`.agents/skills/lean-abstract/SKILL.md`) and "Layout and
sources" (`abstracts/README.md`), the abstract has, in source order:

1. the module docstring;
2. "Graphs and distances": `Graph`, `IsWalk`, `dist`, `numEdges`, `maxWeight`;
3. "Input, output and cost": prose only, stating in words the input, the output cells, the
   word-size condition and the cost model;
4. "Representation details": `offset`, `encode`, `outAddr`, `encodeDist`, and the prose on the
   machine;
5. "Main theorem": `dijkstra_logLinear` and the audit.

The renderer moves a `## Representation details` group, up to the next `##` heading, to an
appendix after the main text (`scripts/abstract_to_tex.py`, `split_sections` and
`presentation_sections`). The group sits before the theorem in the source because the theorem uses
its definitions; `CookLevinAbstract.lean` does the same.

## Main theorem

```lean
theorem dijkstra_logLinear :
    ∃ r, ∃ p : Cslib.WordRAM.Program .standard r, ∃ K, ∀ (n : ℕ) (G : Graph n) (s : Fin n) (w : ℕ),
      8 * (n + numEdges G + 2) * (maxWeight G + 2) < 2 ^ w →
      ∃ t steps, Cslib.WordRAM.Runs w p (Cslib.WordRAM.State.init (encode G s)) t steps ∧
        (∃ v, Cslib.WordRAM.step w p t = .halt v) ∧
        steps + 1 ≤ K * (numEdges G + 1) * (Nat.log 2 n + 1) ∧
        ∀ v : Fin n, t.data.mem (outAddr G v) = encodeDist (dist G s v)
```

## Machine choice: allowlist the library word RAM

The library theorem is over `Basis.standard` (`D/HeapStatement.lean:157`, `:166`). The
self-contained machine of `X/WordRAMAbstract.lean` is the exact basis, and its `runsAgree` relates
it only to `Cslib.WordRAM.Program .exact r` (`X/WordRAMAbstract.lean:241-251`). I found no
simulation of a standard-basis program by an exact-basis one in the library (`rg` over
`Complexity/`). Option (b) would therefore need a new instruction-level simulation in the bridge,
and the constants `r` and `K` would change. Option (a) is allowed by the skill
(`.agents/skills/lean-abstract/SKILL.md:37`), keeps the statement equal to the library's, and the
audit shows the allowlist closes over `Defs` and `Basis` alone. The prose on the machine in the
abstract's appendix states in prose what a reader needs of the five library names it uses: `Program`,
`State.init`, `step`, `Runs` and `.halt`.

## Distance and the bridge

The abstract defines distance by walks:

```lean
def IsWalk (G : Graph n) : Fin n → List (Fin n × ℕ) → Fin n → Prop
  | u, [], v => u = v
  | u, e :: l, v => e ∈ G u ∧ IsWalk G e.1 l v

noncomputable def dist (G : Graph n) (u v : Fin n) : ℕ∞ :=
  ⨅ (l : List (Fin n × ℕ)) (_ : IsWalk G u l v), ((l.map Prod.snd).sum : ℕ∞)
```

The library defines it as the least `Quiver.Path` weight of the weight-matrix instance that keeps
the lightest parallel edge (`D/HeapStatement.lean:82-96`, `D/Statement.lean:89`). The bridge
takes any walk predicate `W` with the two defining laws (`WalkLaws`, `X/DijkstraBridge.lean:45`)
and proves `walkDist_eq` (`X/DijkstraBridge.lean:126`) by two inequalities:

* every path is a walk of the same weight (`exists_walk`, `X/DijkstraBridge.lean:77`);
* every walk gives a path of at most its weight, replacing each edge by the lightest one between
  the same endpoints (`exists_path`, `X/DijkstraBridge.lean:96`), using `lightest_eq_some_iff`
  and `lightest_eq_none_iff` (`D/HeapStatement.lean:125`, `:138`).

The abstract passes `@IsWalk` with both laws proved by `Iff.rfl`. The laws are needed because
`IsWalk` is defined by recursion in the abstract, so the bridge cannot name it (inferred: a
bridge cannot import the abstract that imports it).

## Fidelity

Compared with `LogLinearSpec` (`D/HeapStatement.lean:157-161`) and `LogLinearStatement`
(`:166`):

* Quantifiers: the same, `∃ r p K, ∀ instance w`. The instance `⟨n, G, s⟩` is three parameters.
* Encoding: `offset`, `encode`, `numEdges`, `maxWeight` are the library's `offset`, `encode`,
  `m`, `maxWeight` (`D/HeapStatement.lean:99-118`) with the structure unfolded. They agree by
  `rfl` (the bridge passes them unchanged).
* Output: `outAddr G v = n + 2 m + 4 + v` is `D/HeapStatement.lean:121`, and `encodeDist` is
  `D/Statement.lean:120`.
* Word size: `8 (n + m + 2) (W + 2) < 2 ^ w` is `Fits` (`C/Defs.lean:156`) unfolded.
* Bound: `steps + 1 ≤ K (m + 1) (Nat.log 2 n + 1)`, as in the library.
* No added hypotheses.

What the abstract does not say exactly or not self-contained:

1. The machine is not defined in the file. It is read through the allowlisted modules `Defs` and
   `Basis`; the file describes it in prose only.
2. The value returned by `halt` is not part of the result (as in the library).
3. `Nat.log 2 n` is `⌊log₂ n⌋` for `n ≥ 1` and `0` for `n = 0`.
4. The constants (`r = 27`, `K = 230`, `D/LogLinear.lean:421`) are hidden behind `∃`.

## Rendering

The PDF was rendered with upstream's renderer without changing `catalogue.json`: a helper script
outside the repository imports `scripts/build_abstracts.py`, builds an in-memory catalogue entry
(id `dijkstra`, headline `ComplexityAbstracts.DijkstraAbstract.dijkstra_logLinear`), and calls
`render_entry`, `document` and `build_pdf`. The abstract imports no shared foundation, so the entry
lists none. The renderer has no list support in section comments
and no TeX mapping for `⌊`, `⌋` or `ᵢ`, so the docstrings avoid them.

## Checks

* `scripts/check.sh`: all six gates pass.
* `lake build --wfail --iofail ComplexityAbstracts.DijkstraAbstract`: passes.
* `#check_abstract`: "abstract audit passed for `ComplexityAbstracts.DijkstraAbstract`: 14 root
  declarations, 249 dependencies checked".
* `#print axioms ComplexityAbstracts.DijkstraAbstract.dijkstra_logLinear`:
  `[propext, Classical.choice, Quot.sound]`.
* `python3 -B scripts/build_abstracts.py --check`: passes (12 abstracts, 16 headline theorems;
  the new abstract is not in the catalogue).
* `scripts/check_abstract_ci.py` checks GitHub CI of a pushed `main` commit before a release; it
  does not apply to a branch before merge, so I did not run it.
