import NlsGge.Hierarchy.RiccatiSobolevJetCoefficientL2BoundRecovery28Second
import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot

/-- The actual derivative-class Fourier coefficient is additive on the
concrete restricted-real Sobolev carrier. -/
theorem riccatiSobolevJetCoefficient_addRecovery29Isolated
    (m k : ℕ) (x y : SobolevHilbert (m : ℝ)) :
    riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y) =
      riccatiSobolevJetCoefficientL2Recovery28Second m k x +
        riccatiSobolevJetCoefficientL2Recovery28Second m k y := by
  funext n
  change fourierMultiplier n ^ k *
      ((show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n +
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n) =
    fourierMultiplier n ^ k *
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n +
      fourierMultiplier n ^ k *
        (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from y) n
  ring

/-- The same coefficient respects the source's actual real scalar action. -/
theorem riccatiSobolevJetCoefficient_smulRecovery29Isolated
    (m k : ℕ) (r : ℝ) (x : SobolevHilbert (m : ℝ)) :
    riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x) =
      (r : ℂ) • riccatiSobolevJetCoefficientL2Recovery28Second m k x := by
  funext n
  change fourierMultiplier n ^ k *
      ((r : ℂ) * (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n) =
    (r : ℂ) * (fourierMultiplier n ^ k *
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n)
  ring

/-- Explicit unit-weight sequence identity matching the exact add API. -/
theorem riccatiSobolevJetCoefficient_weightedCoordinates_addRecovery29Isolated
    (m k : ℕ) (x y : SobolevHilbert (m : ℝ)) :
    weightedCoordinates (fun _ : ℤ => (1 : ℝ))
        (riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y)) =
      weightedCoordinates (fun _ : ℤ => (1 : ℝ))
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x) +
      weightedCoordinates (fun _ : ℤ => (1 : ℝ))
        (riccatiSobolevJetCoefficientL2Recovery28Second m k y) := by
  rw [riccatiSobolevJetCoefficient_addRecovery29Isolated]
  exact weightedCoordinates_add (fun _ : ℤ => (1 : ℝ))
    (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
    (riccatiSobolevJetCoefficientL2Recovery28Second m k y)

/-- Explicit unit-weight sequence identity matching the exact scalar API. -/
theorem riccatiSobolevJetCoefficient_weightedCoordinates_smulRecovery29Isolated
    (m k : ℕ) (r : ℝ) (x : SobolevHilbert (m : ℝ)) :
    weightedCoordinates (fun _ : ℤ => (1 : ℝ))
        (riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x)) =
      (r : ℂ) • weightedCoordinates (fun _ : ℤ => (1 : ℝ))
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x) := by
  rw [riccatiSobolevJetCoefficient_smulRecovery29Isolated]
  exact weightedCoordinates_smul (fun _ : ℤ => (1 : ℝ)) (r : ℂ)
    (riccatiSobolevJetCoefficientL2Recovery28Second m k x)

/-- Exact additive identity at the concrete unit-weight `lp` carrier used
by the derivative-class CLM. The summability witnesses come from the checked
coefficient bound for each source vector. -/
theorem riccatiSobolevJetCoefficient_weightedL2Element_addRecovery29Isolated
    (m k : ℕ) (hkm : k ≤ m) (x y : SobolevHilbert (m : ℝ)) :
    weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y))
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm (x + y)) =
      weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x) +
      weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k y)
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm y) := by
  apply lp.ext
  funext n
  change weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y)) n =
    weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k x) n +
    weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k y) n
  rw [riccatiSobolevJetCoefficient_addRecovery29Isolated]
  exact congrFun (weightedCoordinates_add (fun _ : ℤ => (1 : ℝ))
    (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
    (riccatiSobolevJetCoefficientL2Recovery28Second m k y)) n

/-- Exact scalar identity at the concrete unit-weight `lp` carrier used by
the derivative-class CLM. -/
theorem riccatiSobolevJetCoefficient_weightedL2Element_smulRecovery29Isolated
    (m k : ℕ) (hkm : k ≤ m) (r : ℝ) (x : SobolevHilbert (m : ℝ)) :
    weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x))
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm (r • x)) =
      (r : ℂ) • weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x) := by
  apply lp.ext
  funext n
  change weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x)) n =
    (r : ℂ) * weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (riccatiSobolevJetCoefficientL2Recovery28Second m k x) n
  rw [riccatiSobolevJetCoefficient_smulRecovery29Isolated]
  have hcoord := weightedCoordinates_smul (fun _ : ℤ => (1 : ℝ)) (r : ℂ)
    (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
  rw [congrFun hcoord n]
  simp only [Pi.smul_apply, smul_eq_mul]

/-- Minimal order-theoretic postprocessing of the norm-square estimate used
by the full derivative CLM. -/
theorem norm_le_of_sq_leRecovery29Isolated
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

end NlsGge.HierarchyRiccati.Core

end
