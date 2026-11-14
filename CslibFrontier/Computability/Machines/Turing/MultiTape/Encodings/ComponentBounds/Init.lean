/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Component-size simplification attribute

The opt-in `enc_component` simp set proves component-to-container length bounds without
expanding encoded words. Its rules are supplied by `Encodings.ComponentBounds`.
-/

public meta section

/-- Component-to-container encoded-length inequalities, retaining the encoding layout. -/
register_simp_attr enc_component

end
