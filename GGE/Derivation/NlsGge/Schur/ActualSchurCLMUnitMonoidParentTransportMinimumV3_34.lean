import NlsGge.Schur.PhysicalSector
import Mathlib.Algebra.GroupWithZero.Hom

set_option autoImplicit false

noncomputable section

namespace NlsGge.Schur

abbrev ActualSchurCLMEndV3_34 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

/-- The direct semiring's monoid-with-zero parent for the actual CLM carrier. -/
abbrev actualSchurCLMSourceMonoidWithZeroV3_34 (n : ℤ) :
    MonoidWithZero (ActualSchurCLMEndV3_34 n) :=
  @Semiring.toMonoidWithZero (ActualSchurCLMEndV3_34 n)
    ContinuousLinearMap.semiring

/-- The monoid-with-zero parent of the actual CLM normed-ring projection. -/
abbrev actualSchurCLMRingMonoidWithZeroV3_34 (n : ℤ) :
    MonoidWithZero (ActualSchurCLMEndV3_34 n) :=
  @Semiring.toMonoidWithZero (ActualSchurCLMEndV3_34 n)
    (@Ring.toSemiring (ActualSchurCLMEndV3_34 n)
      (@NormedRing.toRing (ActualSchurCLMEndV3_34 n)
        ContinuousLinearMap.toNormedRing))

/-- Identity on the CLM carrier between its direct semiring parent and its
normed-ring parent. These fields isolate agreement of zero, one, and product. -/
def actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34
    (n : ℤ) :
    @MonoidWithZeroHom (ActualSchurCLMEndV3_34 n)
      (ActualSchurCLMEndV3_34 n)
      (@MonoidWithZero.toMulZeroOneClass (ActualSchurCLMEndV3_34 n)
        (actualSchurCLMSourceMonoidWithZeroV3_34 n))
      (@MonoidWithZero.toMulZeroOneClass (ActualSchurCLMEndV3_34 n)
        (actualSchurCLMRingMonoidWithZeroV3_34 n)) where
  toFun := id
  map_zero' := by rfl
  map_one' := by rfl
  map_mul' := by
    intro x y
    rfl

@[simp]
theorem actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34_apply
    (n : ℤ) (x : ActualSchurCLMEndV3_34 n) :
    actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n x = x := rfl

@[simp]
theorem actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34_map_zero
    (n : ℤ) :
    actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n 0 = 0 := rfl

@[simp]
theorem actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34_map_one
    (n : ℤ) :
    actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n 1 = 1 := rfl

@[simp]
theorem actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34_map_mul
    (n : ℤ) (x y : ActualSchurCLMEndV3_34 n) :
    actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n (x * y) =
      actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n x *
        actualSchurCLMSourceToRingParentMonoidWithZeroHomV3_34 n y := rfl

/-- Reverse identity-shaped hom, needed later to transport nonunit evidence. -/
def actualSchurCLMRingParentToSourceMonoidWithZeroHomV3_34
    (n : ℤ) :
    @MonoidWithZeroHom (ActualSchurCLMEndV3_34 n)
      (ActualSchurCLMEndV3_34 n)
      (@MonoidWithZero.toMulZeroOneClass (ActualSchurCLMEndV3_34 n)
        (actualSchurCLMRingMonoidWithZeroV3_34 n))
      (@MonoidWithZero.toMulZeroOneClass (ActualSchurCLMEndV3_34 n)
        (actualSchurCLMSourceMonoidWithZeroV3_34 n)) where
  toFun := id
  map_zero' := by rfl
  map_one' := by rfl
  map_mul' := by
    intro x y
    rfl

end NlsGge.Schur
