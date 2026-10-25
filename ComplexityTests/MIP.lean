/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import Complexity.Computability.Complexity.Classes.IP.Shamir
import Complexity.Computability.Complexity.Classes.MIP

/-! Multiprover interactive proofs (`MIP₂` and `MIP`), non-communicating provers, deterministic
prover optimality, transcript consistency, and the upper bound `MIP ⊆ NEXP`. -/

namespace ComplexityTests.MIP

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-! ### Non-communicating provers and transcript consistency -/

-- Querying channel `0` leaves channel `1`'s state untouched.
example (P : Fin 2 → Prover Unit) (word : List Bool) (s s' : ∀ i : Fin 2, (P i).State)
    (reply : List Bool)
    (hout : (reply, s') ∈ (((Prover.independent P).respond ((0 : Fin 2), word)).run s).support) :
    s' 1 = s 1 :=
  Prover.independent_state_eq_of_ne P ((0 : Fin 2), word) s s' reply (by decide : (1 : Fin 2) ≠ 0)
    hout

-- `projHistory` filters and extracts the `(query, reply)` pairs of a single prover channel.
example : MIP.projHistory 0
    [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
    [([true], [false]), ([true, false], [true])] := rfl

example : MIP.projHistory 1
    [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
    [([false], [true])] := rfl

-- Two histories that agree on their common prefix and then diverge in query are `consistentHist`.
example : MIP.consistentHist
    [([true], [false]), ([false], [true])]
    [([true], [false]), ([true], [false])] = true := rfl

-- Two histories that give different replies to the first common query are inconsistent.
example : MIP.consistentHist
    [([true], [false])]
    [([true], [true])] = false := rfl

/-! ### Non-vacuity: concrete `IsMultiproverProof` instance -/

-- Every single-prover interactive proof embeds into a two-prover interactive proof via channel 0.
example : IsMultiproverProof
    (fun x : Graph × Graph =>
      WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
    GraphNonIsomorphism 1 ((17 / 32) ^ 2) :=
  GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle (0 : Fin 2)

-- GraphNonIsomorphism and TQBF belong to `MIP₂`, `MIP`, and `NEXP`.
example : GraphNonIsomorphism ∈ MIP₂ (encPair encGraph encGraph) :=
  IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP

example : GraphNonIsomorphism ∈ MIP (encPair encGraph encGraph) :=
  MIP₂_subset_MIP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP)

example : GraphNonIsomorphism ∈ NEXP (encPair encGraph encGraph) :=
  MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP)

example : TQBF ∈ MIP₂ encQBF :=
  IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1)

example : TQBF ∈ NEXP encQBF :=
  MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1))

end ComplexityTests.MIP
