import NlsGge.Schur.ResonantParityPairBasisAction

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur

/-- Concrete complex inner-product additivity on the actual parity-pair
carrier. The target type fixes the exact pinned Mathlib instance dictionary;
no explicit guessed type-argument prefix is needed. -/
theorem actualParityPairComplexInnerAddRightMinimumV1_32
    (n : ℤ) (x y z : ParityPair n) :
    inner ℂ x (y + z) = inner ℂ x y + inner ℂ x z := by
  simpa only using! _root_.inner_add_right (𝕜 := ℂ) x y z

end NlsGge.Schur
