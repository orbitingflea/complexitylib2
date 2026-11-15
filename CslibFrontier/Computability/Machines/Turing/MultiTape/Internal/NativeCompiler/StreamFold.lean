/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-!
# Named native streaming folds

This module retains the concrete `streamTM` assembled from named callback compilers. The framed
initial state is copied directly from the input prefix, list elements are decoded one frame at a
time, and the input list is never copied to work tapes. The construction records the exact
callback-lifting, loop, finalization, cleanup and rewind bounds from the stream kernel.

No machine is selected from an existential computability certificate. The only supplied bounds
are `sMax`, for the peak lifted callback workspace, and `lMax`, for the encoded state and element
lengths along this particular fold. The per-round clock is the explicit construction formula.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.frameValueReader`: read the contents of one framed
  list element without retaining its framing.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairMachine`: the concrete stream
  assembly from named callback machines.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPairRoundCost`, `.streamFoldPairTime`,
  `.streamFoldPairWorkspace`: the construction-derived resource formulas.
* `Turing.MultiTapeTM.Internal.NativeCompiler.streamFoldPair`: retain the concrete single-pass
  stream machine for an initial state paired with an encoded list.

## Main results

* `Turing.MultiTapeTM.Internal.NativeCompiler.machine_streamFoldPair`: identify the retained
  machine with the exposed concrete assembly.
* `Turing.MultiTapeTM.Internal.NativeCompiler.time_streamFoldPair`, `.workspace_streamFoldPair`:
  identify the recorded resource maps with the exposed construction formulas.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

open Encodings

/-- Read one standard framed value, emitting its contents and stopping after its closing marker. -/
@[expose] def frameValueReader : InputReader Bool Bool where
  q₀ := false
  step
    | false, true => (some true, none)
    | false, false => (none, none)
    | true, bit => (some false, some bit)

/-- `frameValueReader` removes exactly one layer of standard framing. -/
theorem read_frameValueReader (word rest : List Bool) :
    frameValueReader.read false (frame word ++ rest) = (word, (frame word).length) := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [frame_cons, List.cons_append, List.cons_append,
      frameValueReader.read_cons_of_some (q' := true) _ rfl,
      frameValueReader.read_cons_of_some (q' := false) _ rfl, ih]
    simp [frameValueReader, Nat.add_assoc]

/-- The next-state callback followed by the retained framing transducer required by `streamTM`. -/
@[expose] noncomputable def streamFramedNext {Alpha Sigma : Type*}
    {next : Sigma × Alpha → Sigma} {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    (compiler : NativeCompiler next (encPair encS encA) encS) :
    NativeCompiler (fun input => frame (encS (next input)))
      (encPair encS encA) encBits :=
  (encodeFrame encS).comp compiler

/-- The final callback preceded by the retained typed unframing transducer required by
`streamTM`. -/
@[expose] noncomputable def streamUnframedFinish {Sigma Phi : Type*}
    {finish : Sigma → Phi} {encS : Sigma ↪ List Bool} {encF : Phi ↪ List Bool}
    (compiler : NativeCompiler finish encS encF) :
    NativeCompiler finish (encFramed encS) encF :=
  compiler.comp (unframeValue encS)

/-- Exact clock of a tidy callback lifted to emit from a selected work tape. -/
@[expose] def inputFromWordTime {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.time input + 4

/-- Construction-derived workspace bound for a tidy callback lifted to emit from a selected work
tape in a `K`-tape stream machine. -/
@[expose] def inputFromWordWorkspace {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (K : ℕ) (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.workspace input + 2 * ((encIn input).length + 2) + 2 * compiler.tapeCount + 8 +
    (K - (compiler.tapeCount + 2))

/-- Exact clock of a tidy callback lifted to write its output between selected work tapes. -/
@[expose] def onWordsTime {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.time input + (encOut (f input)).length + 6

/-- Construction-derived workspace bound for a tidy callback lifted to write its output between
selected work tapes in a `K`-tape stream machine. -/
@[expose] def onWordsWorkspace {Alpha Beta : Type*} {f : Alpha → Beta}
    {encIn : Alpha ↪ List Bool} {encOut : Beta ↪ List Bool}
    (K : ℕ) (compiler : NativeCompiler f encIn encOut) (input : Alpha) : ℕ :=
  compiler.workspace input + 2 * (encIn input).length + 2 * (encOut (f input)).length +
    3 * compiler.tapeCount + 18 + (K - (compiler.tapeCount + 1 + 2))

/-- The exact number of tapes in the retained pair-stream assembly. -/
@[expose] noncomputable def streamFoldPairTapeCount {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) : ℕ :=
  emitCompiler.tapeCount + (streamFramedNext nextCompiler).tapeCount +
    (streamUnframedFinish finishCompiler).tapeCount + 11

/-- Explicit embedding into a larger tape set sending `source` to `target`. -/
@[expose] def embeddingAt {m K : ℕ} (h : m ≤ K) (source : Fin m) (target : Fin K) :
    Fin m ↪ Fin K :=
  (Fin.castLEEmb h).trans (Equiv.swap (Fin.castLE h source) target).toEmbedding

/-- The explicit one-point embedding has its requested endpoint. -/
@[simp] theorem embeddingAt_source {m K : ℕ} (h : m ≤ K) (source : Fin m)
    (target : Fin K) : embeddingAt h source target source = target := by
  simp [embeddingAt]

/-- Explicit embedding into a larger tape set sending two distinct sources to two distinct
targets. -/
@[expose] def embeddingAt₂ {m K : ℕ} (h : m ≤ K) {input output : Fin m}
    (_hio : input ≠ output) {source target : Fin K} (_hst : source ≠ target) : Fin m ↪ Fin K :=
  let first := embeddingAt h input source
  first.trans (Equiv.swap (first output) target).toEmbedding

/-- The first endpoint of the explicit two-point embedding. -/
@[simp] theorem embeddingAt₂_input {m K : ℕ} (h : m ≤ K) {input output : Fin m}
    (hio : input ≠ output) {source target : Fin K} (hst : source ≠ target) :
    embeddingAt₂ h hio hst input = source := by
  let first := embeddingAt h input source
  have hout : first output ≠ source := fun heq =>
    hio (first.injective (heq.trans (embeddingAt_source h input source).symm)).symm
  simp only [embeddingAt₂, Function.Embedding.trans_apply]
  rw [embeddingAt_source]
  exact Equiv.swap_apply_of_ne_of_ne hout.symm hst

/-- The second endpoint of the explicit two-point embedding. -/
@[simp] theorem embeddingAt₂_output {m K : ℕ} (h : m ≤ K) {input output : Fin m}
    (hio : input ≠ output) {source target : Fin K} (hst : source ≠ target) :
    embeddingAt₂ h hio hst output = target := by
  simp [embeddingAt₂]

/-- Selected-tape layout for the retained stream assembly. The layout records the embeddings and
their endpoint equations once so the exposed machine and its correctness proof share the same
choices. -/
structure StreamFoldPairLayout {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) where
  /-- Tape holding the framed current state. -/
  V : Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- Tape receiving the framed next state. -/
  N : Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- Copying flag tape. -/
  F : Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- The current- and next-state tapes are distinct. -/
  hVN : V ≠ N
  /-- The current-state and flag tapes are distinct. -/
  hVF : V ≠ F
  /-- The next-state and flag tapes are distinct. -/
  hNF : N ≠ F
  /-- Selected tapes for the emitting callback. -/
  emitEmbedding : Fin (emitCompiler.tapeCount + 2) ↪
    Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- The emitting callback reads the current-state tape. -/
  emitInput : emitEmbedding (Fin.natAdd emitCompiler.tapeCount (0 : Fin 2)) = V
  /-- Selected tapes for the next-state callback. -/
  nextEmbedding : Fin ((streamFramedNext nextCompiler).tapeCount + 1 + 2) ↪
    Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- The next-state callback reads the current-state tape. -/
  nextInput : nextEmbedding
    (Fin.natAdd ((streamFramedNext nextCompiler).tapeCount + 1) (0 : Fin 2)) = V
  /-- The next-state callback writes the next-state tape. -/
  nextOutput : nextEmbedding ((Fin.last (streamFramedNext nextCompiler).tapeCount).castAdd 2) = N
  /-- Selected tapes for the final callback. -/
  finishEmbedding : Fin ((streamUnframedFinish finishCompiler).tapeCount + 2) ↪
    Fin (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
  /-- The final callback reads the current-state tape. -/
  finishInput : finishEmbedding
    (Fin.natAdd (streamUnframedFinish finishCompiler).tapeCount (0 : Fin 2)) = V

/-- A selected-tape layout exists with the three stream tapes placed after every callback's tape
budget. These choices select tape positions, not erased callback machines. -/
@[expose] noncomputable def streamFoldPairLayout {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) :
    StreamFoldPairLayout nextCompiler emitCompiler finishCompiler := by
  let framedNext := streamFramedNext nextCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  let M := emitCompiler.tapeCount + framedNext.tapeCount + unframedFinish.tapeCount + 8
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let V : Fin K := ⟨M, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let N : Fin K := ⟨M + 1, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  let F : Fin K := ⟨M + 2, by
    simp only [K, streamFoldPairTapeCount, M, framedNext, unframedFinish]; omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVF : V ≠ F := by simp [V, F, Fin.ext_iff]
  have hNF : N ≠ F := by simp [N, F, Fin.ext_iff]
  let emitSource := Fin.natAdd emitCompiler.tapeCount (0 : Fin 2)
  let nextSource := Fin.natAdd (framedNext.tapeCount + 1) (0 : Fin 2)
  let nextTarget := (Fin.last framedNext.tapeCount).castAdd 2
  have hNextSourceTarget : nextSource ≠ nextTarget := by simp [nextSource, nextTarget, Fin.ext_iff]
  let finishSource := Fin.natAdd unframedFinish.tapeCount (0 : Fin 2)
  have hEmit : emitCompiler.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount]; omega
  have hNext : framedNext.tapeCount + 1 + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, framedNext]; omega
  have hFinish : unframedFinish.tapeCount + 2 ≤ K := by
    simp only [K, streamFoldPairTapeCount, unframedFinish]; omega
  let eE := embeddingAt hEmit emitSource V
  let eN := embeddingAt₂ hNext hNextSourceTarget hVN
  let eF := embeddingAt hFinish finishSource V
  exact {
    V := V
    N := N
    F := F
    hVN := hVN
    hVF := hVF
    hNF := hNF
    emitEmbedding := eE
    emitInput := by
      simpa only [eE, emitSource, K] using embeddingAt_source hEmit emitSource V
    nextEmbedding := eN
    nextInput := by
      simpa only [eN, nextSource, framedNext, K] using
        embeddingAt₂_input hNext hNextSourceTarget hVN
    nextOutput := by
      simpa only [eN, nextTarget, framedNext, K] using
        embeddingAt₂_output hNext hNextSourceTarget hVN
    finishEmbedding := eF
    finishInput := by
      simpa only [eF, finishSource, unframedFinish, K] using
        embeddingAt_source hFinish finishSource V
  }

/-- Concrete `streamTM` assembled from the three named callback machines. -/
@[expose] noncomputable def streamFoldPairMachine {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) :=
  let layout := streamFoldPairLayout nextCompiler emitCompiler finishCompiler
  let framedNext := streamFramedNext nextCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  streamTM frameValueReader (appendRead rawFrameReader layout.V)
    ((emitCompiler.machine.inputFromWord true).extendTapes layout.emitEmbedding)
    ((framedNext.machine.onWords true).extendTapes layout.nextEmbedding)
    ((unframedFinish.machine.inputFromWord true).extendTapes layout.finishEmbedding)
    layout.V layout.N layout.F layout.hVN layout.hVF layout.hNF

/-- Exact time charged to round `j`. Outside the list range it is zero; the stream machine uses
this function only over `Finset.range input.2.length`. -/
@[expose] noncomputable def streamFoldPairRoundCost {Alpha Sigma Epsilon : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (input : Sigma × List Alpha) (j : ℕ) : ℕ :=
  if hj : j < input.2.length then
    let pair := (streamState input.1 next input.2 j, input.2[j])
    inputFromWordTime emitCompiler pair + onWordsTime (streamFramedNext nextCompiler) pair +
      12 * ((encS (streamState input.1 next input.2 j)).length +
        (encS (streamState input.1 next input.2 (j + 1))).length +
        (encA input.2[j]).length) + 32
  else
    0

/-- Construction-derived clock of the retained pair-stream machine. -/
@[expose] noncomputable def streamFoldPairTime {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF) (input : Sigma × List Alpha) : ℕ :=
  let finalState := streamState input.1 next input.2 input.2.length
  let initialFrame := frame (encS input.1)
  let finalFrame := frame (encS finalState)
  let unframedFinish := streamUnframedFinish finishCompiler
  2 * initialFrame.length + 4 +
    ((encList encA input.2).length +
      (∑ j ∈ Finset.range input.2.length,
        streamFoldPairRoundCost nextCompiler emitCompiler input j) + 1) +
    ((inputFromWordTime unframedFinish finalState + 3 * (finalFrame.length + 1)) +
      ((encPair encS (encList encA) input).length + 2))

/-- Construction-derived workspace bound of the retained pair-stream machine. -/
@[expose] noncomputable def streamFoldPairWorkspace {Alpha Sigma Epsilon Phi : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon} {finish : Sigma → Phi}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (sMax lMax : Sigma × List Alpha → ℕ) (input : Sigma × List Alpha) : ℕ :=
  let finalState := streamState input.1 next input.2 input.2.length
  let initialFrame := frame (encS input.1)
  let finalFrame := frame (encS finalState)
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  initialFrame.length + 2 + (K - 1) +
    (2 * K * (sMax input + 16 * lMax input + 4 * K + 26) + K +
      (inputFromWordWorkspace K unframedFinish finalState +
        (finalFrame.length + 1 + K) + K))

/-- Retain the concrete pair-prefix streaming fold. `sMax` bounds the sum of the two lifted
callback workspaces in each round; `lMax` bounds every encoded stream state and element. -/
@[expose] noncomputable def streamFoldPair
    {Alpha Sigma Epsilon Phi Omega : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi} {result : Sigma × List Alpha → Omega}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    {encOut : Omega ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (hresult : ∀ input, encOut (result input) =
      streamEmit next (fun pair => encE (emit pair)) input.1 input.2 ++
        encF (finish (streamState input.1 next input.2 input.2.length)))
    (sMax lMax : Sigma × List Alpha → ℕ)
    (hspace : ∀ input j (hj : j < input.2.length),
      let pair := (streamState input.1 next input.2 j, input.2[j])
      inputFromWordWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          emitCompiler pair +
        onWordsWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          (streamFramedNext nextCompiler) pair ≤ sMax input)
    (hstate : ∀ input j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lMax input)
    (helem : ∀ input j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lMax input) :
    NativeCompiler result (encPair encS (encList encA)) encOut := by
  let layout := streamFoldPairLayout nextCompiler emitCompiler finishCompiler
  let framedNext := streamFramedNext nextCompiler
  let unframedFinish := streamUnframedFinish finishCompiler
  let K := streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler
  let emitter :=
    (emitCompiler.machine.inputFromWord true).extendTapes layout.emitEmbedding
  let nextMachine := (framedNext.machine.onWords true).extendTapes layout.nextEmbedding
  let finalizer :=
    (unframedFinish.machine.inputFromWord true).extendTapes layout.finishEmbedding
  let machine := streamFoldPairMachine nextCompiler emitCompiler finishCompiler
  letI := emitCompiler.stateFintype
  letI := framedNext.stateFintype
  letI := unframedFinish.stateFintype
  refine
    { tapeCount := K
      State := _
      machine := machine
      stateEncoding := fintypeStateEncoding _
      time := streamFoldPairTime nextCompiler emitCompiler finishCompiler
      workspace := streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler sMax lMax
      computes := ?_ }
  intro input
  let finalState := streamState input.1 next input.2 input.2.length
  have hreadInit : rawFrameReader.read rawFrameReader.q₀
      ((encPair encS (encList encA) input).drop 0) =
      (frame (encS input.1), (frame (encS input.1)).length) := by
    rw [List.drop_zero, encPair_apply]
    exact read_rawFrameReader (encS input.1) (encList encA input.2)
  have hinit := transformsTapesAt_appendRead rawFrameReader layout.V
    (encPair encS (encList encA) input) 1 (by simp) []
  simp only [Fin.val_one, Nat.sub_self, hreadInit, List.length_nil, List.nil_append] at hinit
  have hinit' := hinit.imp
    (P' := fun input' p ws => input' = encPair encS (encList encA) input ∧
      p.val = 1 ∧ ws = fun _ => [])
    (Q' := fun _ _ _ p' ws' e => p'.val = 1 + (frame (encS input.1)).length ∧
      ws' = Function.update (fun _ => []) layout.V (frame (encS input.1)) ∧ e = [])
    (fun _ _ ws ⟨hin, hp, hws⟩ => ⟨hin, hp, by simp [hws]⟩)
    (by
      rintro _ _ ws _ _ _ ⟨_, _, rfl⟩ ⟨hp, hws, hem⟩
      exact ⟨hp, hws, hem⟩)
    le_rfl le_rfl
  have hE := fun pair => (emitCompiler.computes pair).inputFromWord_extendTapes true
    layout.emitInput
  have hN := fun pair => (framedNext.computes pair).onWords_extendTapes true
    layout.nextInput layout.nextOutput
  have hloop := transformsTapesAt_streamLoop_encoded_after frameValueReader
    (fun value => frame (encA value)) (fun value => frame_ne_nil (encA value))
    (fun value rest => read_frameValueReader (encA value) rest)
    layout.hVN layout.hVF layout.hNF
    (frame (encS input.1)) input.1 input.2 next (fun pair => encE (emit pair)) hE hN
    (roundCost := streamFoldPairRoundCost nextCompiler emitCompiler input)
    (sMax := sMax input) (lMax := lMax input) (by
      intro j hj
      simp only [streamFoldPairRoundCost, hj, dite_true, inputFromWordTime, onWordsTime,
        framedNext, streamFramedNext, encBits_apply]
      rw [streamState_succ input.1 next input.2 hj])
    (by
      intro j hj
      simpa only [inputFromWordWorkspace, onWordsWorkspace, framedNext] using
        hspace input j hj)
    (hstate input) (helem input)
  have hF := (unframedFinish.computes finalState).inputFromWord_extendTapes true
    layout.finishInput
  have h := computesTidily_streamTM_after (r := frameValueReader)
    layout.hVN layout.hVF layout.hNF
    (encPair encS (encList encA) input) (frame (encS input.1))
    (frame (encS input.1)) (frame (encS finalState))
    (streamEmit next (fun pair => encE (emit pair)) input.1 input.2)
    (encF (finish finalState)) hinit' hloop hF
  rw [hresult input]
  have hencList :
      encList encA input.2 =
        List.flatMap (fun value => frame (encA value)) input.2 := rfl
  refine h.mono ?_ ?_
  · simp only [streamFoldPairTime, inputFromWordTime, finalState, hencList, unframedFinish]
    omega
  · simp only [streamFoldPairWorkspace, inputFromWordWorkspace, finalState, unframedFinish]
    exact le_rfl

/-- The retained pair-stream compiler contains the exposed concrete `streamTM` assembly. -/
theorem machine_streamFoldPair
    {Alpha Sigma Epsilon Phi Omega : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi} {result : Sigma × List Alpha → Omega}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    {encOut : Omega ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (hresult : ∀ input, encOut (result input) =
      streamEmit next (fun pair => encE (emit pair)) input.1 input.2 ++
        encF (finish (streamState input.1 next input.2 input.2.length)))
    (sMax lMax : Sigma × List Alpha → ℕ)
    (hspace : ∀ input j (hj : j < input.2.length),
      let pair := (streamState input.1 next input.2 j, input.2[j])
      inputFromWordWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          emitCompiler pair +
        onWordsWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          (streamFramedNext nextCompiler) pair ≤ sMax input)
    (hstate : ∀ input j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lMax input)
    (helem : ∀ input j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lMax input) :
    (streamFoldPair nextCompiler emitCompiler finishCompiler hresult sMax lMax
      hspace hstate helem).machine =
      streamFoldPairMachine nextCompiler emitCompiler finishCompiler :=
  rfl

/-- The retained pair-stream clock is the exposed construction formula. -/
theorem time_streamFoldPair
    {Alpha Sigma Epsilon Phi Omega : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi} {result : Sigma × List Alpha → Omega}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    {encOut : Omega ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (hresult : ∀ input, encOut (result input) =
      streamEmit next (fun pair => encE (emit pair)) input.1 input.2 ++
        encF (finish (streamState input.1 next input.2 input.2.length)))
    (sMax lMax : Sigma × List Alpha → ℕ)
    (hspace : ∀ input j (hj : j < input.2.length),
      let pair := (streamState input.1 next input.2 j, input.2[j])
      inputFromWordWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          emitCompiler pair +
        onWordsWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          (streamFramedNext nextCompiler) pair ≤ sMax input)
    (hstate : ∀ input j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lMax input)
    (helem : ∀ input j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lMax input) (input : Sigma × List Alpha) :
    (streamFoldPair nextCompiler emitCompiler finishCompiler hresult sMax lMax
      hspace hstate helem).time input =
      streamFoldPairTime nextCompiler emitCompiler finishCompiler input :=
  rfl

/-- The retained pair-stream workspace map is the exposed construction-derived bound. -/
theorem workspace_streamFoldPair
    {Alpha Sigma Epsilon Phi Omega : Type*}
    {next : Sigma × Alpha → Sigma} {emit : Sigma × Alpha → Epsilon}
    {finish : Sigma → Phi} {result : Sigma × List Alpha → Omega}
    {encA : Alpha ↪ List Bool} {encS : Sigma ↪ List Bool}
    {encE : Epsilon ↪ List Bool} {encF : Phi ↪ List Bool}
    {encOut : Omega ↪ List Bool}
    (nextCompiler : NativeCompiler next (encPair encS encA) encS)
    (emitCompiler : NativeCompiler emit (encPair encS encA) encE)
    (finishCompiler : NativeCompiler finish encS encF)
    (hresult : ∀ input, encOut (result input) =
      streamEmit next (fun pair => encE (emit pair)) input.1 input.2 ++
        encF (finish (streamState input.1 next input.2 input.2.length)))
    (sMax lMax : Sigma × List Alpha → ℕ)
    (hspace : ∀ input j (hj : j < input.2.length),
      let pair := (streamState input.1 next input.2 j, input.2[j])
      inputFromWordWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          emitCompiler pair +
        onWordsWorkspace (streamFoldPairTapeCount nextCompiler emitCompiler finishCompiler)
          (streamFramedNext nextCompiler) pair ≤ sMax input)
    (hstate : ∀ input j, j ≤ input.2.length →
      (encS (streamState input.1 next input.2 j)).length ≤ lMax input)
    (helem : ∀ input j (hj : j < input.2.length),
      (encA input.2[j]).length ≤ lMax input) (input : Sigma × List Alpha) :
    (streamFoldPair nextCompiler emitCompiler finishCompiler hresult sMax lMax
      hspace hstate helem).workspace input =
      streamFoldPairWorkspace nextCompiler emitCompiler finishCompiler sMax lMax input :=
  rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
