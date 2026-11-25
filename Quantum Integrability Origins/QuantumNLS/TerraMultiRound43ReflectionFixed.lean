import QuantumNLS.TerraMultiRound43ReflectionAlgebra

/-! Reflection intertwines the nonlinear signed fixed-point maps. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound43ReflectionFixed
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound43Reflection QuantumNLS.TerraMultiRound43ReflectionAlgebra

theorem reflectEll_sub (x y : Ell2) : reflectEll (x - y) = reflectEll x - reflectEll y := by
  apply lp.ext
  funext k
  simp

theorem reflectEll_smul (c : ℂ) (x : Ell2) : reflectEll (c • x) = c • reflectEll x := by
  apply lp.ext
  funext k
  simp

/-- A reflected solution changes the sign of height and of the solution,
while the field is reflected without a sign. -/
theorem reflect_physicalT {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2) :
    physicalT hL ha (by simpa using hY : 0 < |-Y|) κ (reflectEll u) (-reflectEll r) =
      -reflectEll (physicalT hL ha hY κ u r) := by
  simp only [physicalT, signedT, reflectEll_sub, reflectEll_smul,
    reflect_signedCLM, reflectEll_mulBil, reflectEll_jEll, map_neg]
  simp
  abel

/-- Any signed fixed point gives a reflected fixed point at the opposite height. -/
theorem reflect_physical_fixed {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hL ha hY κ u r = r) :
    physicalT hL ha (by simpa using hY : 0 < |-Y|) κ (reflectEll u) (-reflectEll r) =
      -reflectEll r := by
  rw [reflect_physicalT hL ha hY κ u r, hr]

#print axioms reflectEll_sub
#print axioms reflectEll_smul
#print axioms reflect_physicalT
#print axioms reflect_physical_fixed
end QuantumNLS.TerraMultiRound43ReflectionFixed
