/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (inductive-encoding visibility regression tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive

/-! A module producer whose generated declarations must survive an ordinary import. -/

public section

namespace CslibFrontierTests.InductiveEncodingVisibility

open Turing.MultiTapeTM

/-- Zero, one and three fields exercise tags, empty payloads and repeated frame removal. -/
inductive Message where
  | idle
  | word (bits : List Bool)
  | triple (n : ℕ) (bits : List Bool) (flag : Bool)

enc_inductive eMessage : Message where
  | idle
  | word : encBits
  | triple : encUnary, encBits, encBool

end CslibFrontierTests.InductiveEncodingVisibility
