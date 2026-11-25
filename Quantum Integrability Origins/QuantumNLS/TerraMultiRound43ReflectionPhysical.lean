import QuantumNLS.TerraMultiRound43ReflectionAlgebra
import QuantumNLS.RiccatiPointwiseDisc

/-! The Fourier reflection is spatial reflection of the physical representative. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound43ReflectionPhysical
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwise
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound43Reflection
open QuantumNLS.TerraMultiRound43ReflectionAlgebra

theorem ex_reflect (L : ℝ) (k : ℤ) (t : ℝ) : ex L (-k) t = ex L k (-t) := by
  unfold ex
  congr 1
  push_cast
  ring

theorem physRep_reflect (L a : ℝ) (x : Ell2) (t : ℝ) :
    physRep L a (reflectEll x) t = physRep L a x (-t) := by
  unfold physRep series
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => toField L a x k * ex L k (-t))]
  apply tsum_congr
  intro k
  change toField L a (reflectEll x) k * ex L k t =
    toField L a x (-k) * ex L (-k) (-t)
  rw [toField_reflectEll, ex_reflect, neg_neg]

#print axioms ex_reflect
#print axioms physRep_reflect
end QuantumNLS.TerraMultiRound43ReflectionPhysical
