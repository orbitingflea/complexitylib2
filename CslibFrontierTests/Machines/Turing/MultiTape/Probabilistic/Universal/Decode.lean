/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Decode

/-! Checked round-trip clients for constructive probabilistic universal decoders. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.Decode

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM.Universal

example (z : ℤ) :
    MultiTapeTM.Universal.intUnaryDecoder.decode (encIntUnary z) = z :=
  MultiTapeTM.Universal.intUnaryDecoder.decode_enc z

example (tape : MultiTapeTM.Universal.Tape) :
    MultiTapeTM.Universal.tapeDecoder.decode (MultiTapeTM.Universal.eTape tape) = tape :=
  MultiTapeTM.Universal.tapeDecoder.decode_enc tape

example (key : Key) : keyDecoder.decode (eKey key) = key := keyDecoder.decode_enc key

example (action : Act) : actDecoder.decode (eAct action) = action := actDecoder.decode_enc action

example (branches : Branches) : branchesDecoder.decode (eBranches branches) = branches :=
  branchesDecoder.decode_enc branches

example (description : Desc) : descDecoder.decode (eDesc description) = description :=
  descDecoder.decode_enc description

example (channel : Channel) : channelDecoder.decode (eChannel channel) = channel :=
  channelDecoder.decode_enc channel

example (cfg : ICfg) : iCfgDecoder.decode (eICfg cfg) = cfg := iCfgDecoder.decode_enc cfg

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.Decode
