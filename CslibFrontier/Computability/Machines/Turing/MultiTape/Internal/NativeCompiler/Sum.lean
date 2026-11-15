/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Conditional
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-!
# Named native sum destructors

The standard sum encoding begins with a constructor bit. These total destructors retain the tag
test, payload-tail transducer and conditional default substitution. The opposite-constructor
default is explicit, so clients can extract a typed payload without a decoder callback or an
invalid cast.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.sumLeftD`: left payload or an explicit default.
* `Turing.MultiTapeTM.Internal.NativeCompiler.sumRightD`: right payload or an explicit default.
* `Turing.MultiTapeTM.Internal.NativeCompiler.optionGetD`: optional payload or an explicit default.
* `Turing.MultiTapeTM.Internal.NativeCompiler.listHeadD`, `.listGetDUnary`: total standard-list
  access with an explicit default.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Emit the untagged payload word of a standard option encoding. -/
@[expose] noncomputable def optionPayload {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun value : Option Alpha => (encOption enc value).tail)
      (encOption enc) encBits :=
  tailDecoder.ofInputEq (fun value => encOption enc value) fun _ => rfl

/-- Extract an optional payload, using the explicit default on `none`. -/
@[expose] noncomputable def optionGetD {Alpha : Type*} (default : Alpha)
    (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun value : Option Alpha => value.getD default) (encOption enc) enc := by
  let fallback := const (encOption enc) encBits (enc default)
  exact (ite (optionIsSomeTest enc) (optionPayload enc) fallback).ofOutputEq
    fun value => by cases value <;> rfl

/-- Test whether a standard encoded list is empty. -/
@[expose] noncomputable def listIsEmpty {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler List.isEmpty (encList enc) encTest :=
  (boolToTest.comp
    (isEmpty.ofInputEq (fun list => encList enc list) fun _ => rfl)).ofOutputEq fun list => by
      cases list <;> simp [encList_cons]

/-- Emit the first framed list element as a raw payload word. On the empty list this emits the
frame parser's total empty-word result, which is replaced by `listHeadD`. -/
@[expose] noncomputable def listHeadPayload {Alpha : Type*} (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun list : List Alpha => unframe (encList enc list))
      (encList enc) encBits :=
  unframeDecoder.ofInputEq (fun list => encList enc list) fun _ => rfl

/-- First list element, or the explicit default on the empty list. -/
@[expose] noncomputable def listHeadD {Alpha : Type*} (default : Alpha)
    (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun list : List Alpha => list.headD default) (encList enc) enc := by
  let fallback := const (encList enc) encBits (enc default)
  exact (ite (listIsEmpty enc) fallback (listHeadPayload enc)).ofOutputEq fun list => by
    cases list <;> simp [encList_cons, unframe_frame_append]

/-- Unary-indexed list access, including the direct suffix scan and total head default. -/
@[expose] noncomputable def listGetDUnary {Alpha : Type*} (default : Alpha)
    (enc : Alpha ↪ List Bool) :
    NativeCompiler (fun input : List Alpha × ℕ => input.1.getD input.2 default)
      (encPair (encList enc) encUnary) enc :=
  ((listHeadD default enc).comp (dropUnary enc)).ofOutputEq fun input => by
    simp [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

/-- Extract a left payload, using the explicit default on right inputs. -/
@[expose] noncomputable def sumLeftD {Alpha Beta : Type*} (default : Alpha)
    (encLeft : Alpha ↪ List Bool) (encRight : Beta ↪ List Bool) :
    NativeCompiler (Sum.elim id (Function.const Beta default))
      (encSum encLeft encRight) encLeft := by
  let tag := boolToTest.comp (sumTag encLeft encRight)
  let payload := sumPayload encLeft encRight
  let fallback := const (encSum encLeft encRight) encBits (encLeft default)
  exact (ite tag fallback payload).ofOutputEq fun value => by cases value <;> rfl

/-- Extract a right payload, using the explicit default on left inputs. -/
@[expose] noncomputable def sumRightD {Alpha Beta : Type*} (default : Beta)
    (encLeft : Alpha ↪ List Bool) (encRight : Beta ↪ List Bool) :
    NativeCompiler (Sum.elim (Function.const Alpha default) id)
      (encSum encLeft encRight) encRight := by
  let tag := boolToTest.comp (sumTag encLeft encRight)
  let payload := sumPayload encLeft encRight
  let fallback := const (encSum encLeft encRight) encBits (encRight default)
  exact (ite tag payload fallback).ofOutputEq fun value => by cases value <;> rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
