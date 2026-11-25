import QuantumNLS.TerraMultiRound43Reflection
import QuantumNLS.TerraMultiRound40Conjugation

/-! Algebraic properties of frequency reflection for the signed Riccati map. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate
namespace QuantumNLS.TerraMultiRound43ReflectionAlgebra
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound43Reflection

theorem toField_reflectEll (L a : ℝ) (x : Ell2) (k : ℤ) :
    toField L a (reflectEll x) k = toField L a x (-k) := by
  simp [toField, pw_neg]

theorem reflectEll_jEll (x : Ell2) : reflectEll (jEll x) = jEll (reflectEll x) := by
  apply lp.ext
  funext k
  simp

/-- Reflection preserves Fourier convolution. -/
theorem reflectEll_mulBil {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (x y : Ell2) :
    reflectEll (mulBil hL ha x y) = mulBil hL ha (reflectEll x) (reflectEll y) := by
  have hfields : toField L a (reflectEll (mulBil hL ha x y)) =
      toField L a (mulBil hL ha (reflectEll x) (reflectEll y)) := by
    funext k
    rw [toField_reflectEll, mulBil_apply, toField_mulEll, mulBil_apply, toField_mulEll]
    simp only [convC, toField_reflectEll]
    rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ =>
      toField L a x j * toField L a y (-k - j))]
    apply tsum_congr
    intro j
    change toField L a x (-j) * toField L a y (-k - -j) =
      toField L a x (-j) * toField L a y (-(k - j))
    rw [show -k - -j = -(k - j) by omega]
  apply lp.ext
  funext k
  have h := congrFun hfields k
  dsimp [toField] at h
  have hp := pw_ne_zero L a k
  have hm := congrArg (fun z : ℂ => z * ((pw L a k : ℝ) : ℂ)) h
  simpa only [div_mul_cancel₀ _ hp, reflectEll_apply] using hm

#print axioms toField_reflectEll
#print axioms reflectEll_jEll
#print axioms reflectEll_mulBil
end QuantumNLS.TerraMultiRound43ReflectionAlgebra
