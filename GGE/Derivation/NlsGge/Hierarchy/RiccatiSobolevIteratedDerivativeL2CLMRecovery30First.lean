import NlsGge.Hierarchy.RiccatiSobolevJetCoefficientL2BoundRecovery28Second
import NlsGge.Hierarchy.RiccatiSobolevDerivativeCoefficientCoordinateLinearityRecovery29Isolated
import NlsGge.Hierarchy.RiccatiPowerFactorizationMinimumRecovery30
import NlsGge.Hierarchy.RiccatiUnitWeightedL2ElementCoordinateMinimumRecovery30
import NlsGge.Hierarchy.RiccatiPhysicalFourierL2SymmCoefficientsSecond
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot

/-- The actual physical-L² representative of the order-`k` Fourier multiplier
on the concrete source Sobolev carrier. The coefficient bound and summability
are supplied by the passed batch-28 weighted estimate. -/
def riccatiSobolevIteratedDerivativeL2ValueRecovery30First
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ)) : PhysicalL2 :=
  physicalFourierL2.symm
    (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
      (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
      (by simpa only [one_mul] using riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x))

private theorem riccatiSobolevIteratedDerivativeL2Value_norm_leRecovery30First
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ‖riccatiSobolevIteratedDerivativeL2ValueRecovery30First m k hkm x‖ ≤
      (2 * Real.pi) ^ k * ‖x‖ := by
  let d := riccatiSobolevJetCoefficientL2Recovery28Second m k x
  let hd := riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x
  have hdunit : Summable (fun n : ℤ => (1 : ℝ) * ‖d n‖ ^ 2) := by
    simpa only [one_mul] using hd
  have hout : ‖physicalFourierL2.symm
      (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num) d hdunit)‖ ^ 2 =
      ∑' n : ℤ, ‖d n‖ ^ 2 := by
    rw [physicalFourierL2.symm.norm_map, weightedL2Element_norm_sq]
    simpa only [one_mul]
  have hin : ‖x‖ ^ 2 = ∑' n : ℤ,
      sobolevModeWeight (m : ℝ) n *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)
  have hsourceSummable : Summable (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)).summable
  have hfactor := NlsGge.HierarchyRiccati.Core.real_two_pi_power_factorizationMinimumRecovery30 k
  have hsum := hd.tsum_le_tsum
      (fun n => riccatiSobolevJetCoefficient_square_leL2Recovery28Second m k hkm x n)
      (hsourceSummable.mul_left ((2 * Real.pi) ^ (2 * k)))
  have hpow : ((2 * Real.pi) ^ k) ^ 2 =
      ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 := by
    calc
      ((2 * Real.pi) ^ k) ^ 2 = (2 * Real.pi) ^ (2 * k) := by
        rw [← pow_mul]
        congr 1
        omega
      _ = _ := hfactor.symm
  have hsumBound : (∑' n : ℤ, ‖d n‖ ^ 2) ≤
      ∑' n : ℤ, ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 *
        (sobolevModeWeight (m : ℝ) n *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
    calc
      ∑' n : ℤ, ‖d n‖ ^ 2 ≤
          ∑' n : ℤ, (2 * Real.pi) ^ (2 * k) *
            (sobolevModeWeight (m : ℝ) n *
              ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
        simpa only [d, riccatiSobolevJetCoefficientL2Recovery28Second] using hsum
      _ = _ := by
        apply tsum_congr
        intro n
        rw [← hfactor]
  have hsum' : (∑' n : ℤ, ‖d n‖ ^ 2) ≤
      ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 * ‖x‖ ^ 2 := by
    calc
      ∑' n : ℤ, ‖d n‖ ^ 2 ≤
          ∑' n : ℤ, ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 *
            (sobolevModeWeight (m : ℝ) n *
              ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := hsumBound
      _ = ((2 : ℝ) ^ k) ^ 2 * (Real.pi ^ k) ^ 2 * ‖x‖ ^ 2 := by
        rw [tsum_mul_left, hin]
  have hsq : ‖riccatiSobolevIteratedDerivativeL2ValueRecovery30First m k hkm x‖ ^ 2 ≤
      ((2 * Real.pi) ^ k * ‖x‖) ^ 2 := by
    rw [riccatiSobolevIteratedDerivativeL2ValueRecovery30First, physicalFourierL2.symm.norm_map,
      weightedL2Element_norm_sq]
    simpa only [one_mul, mul_pow, hpow] using hsum'
  exact norm_le_of_sq_leRecovery29Isolated (norm_nonneg _) (by positivity) hsq

private theorem riccatiSobolevJetCoefficient_addRecovery30First
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

private theorem riccatiSobolevJetCoefficient_smulRecovery30First
    (m k : ℕ) (r : ℝ) (x : SobolevHilbert (m : ℝ)) :
    riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x) =
      (r : ℂ) • riccatiSobolevJetCoefficientL2Recovery28Second m k x := by
  funext n
  change fourierMultiplier n ^ k *
      ((r : ℂ) * (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n) =
    (r : ℂ) * (fourierMultiplier n ^ k *
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n)
  ring

/-- Bounded real-linear order-`k` derivative-class map on actual source
Sobolev carriers. This theorem constructs the Fourier multiplier class; its
agreement with classical derivatives is stated separately. -/
def riccatiSobolevIteratedDerivativeL2CLMRecovery30First
    (m k : ℕ) (hkm : k ≤ m) : SobolevHilbert (m : ℝ) →L[ℝ] PhysicalL2 := by
  let f : SobolevHilbert (m : ℝ) →ₗ[ℝ] PhysicalL2 := {
    toFun := riccatiSobolevIteratedDerivativeL2ValueRecovery30First m k hkm
    map_add' := by
      intro x y
      change physicalFourierL2.symm
          (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
            (riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y))
            (by simpa only [one_mul] using
              riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm (x + y))) =
        physicalFourierL2.symm
            (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
              (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
              (by simpa only [one_mul] using
                riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x)) +
          physicalFourierL2.symm
            (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
              (riccatiSobolevJetCoefficientL2Recovery28Second m k y)
              (by simpa only [one_mul] using
                riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm y))
      have helem := riccatiSobolevJetCoefficient_weightedL2Element_addRecovery29Isolated
        m k hkm x y
      calc
        _ = physicalFourierL2.symm
              ((weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
                (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
                (by simpa only [one_mul] using
                  riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x)) +
               weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
                (riccatiSobolevJetCoefficientL2Recovery28Second m k y)
                (by simpa only [one_mul] using
                  riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm y)) :=
            congrArg physicalFourierL2.symm helem
        _ = _ := map_add physicalFourierL2.symm _ _
    map_smul' := by
      intro r x
      change physicalFourierL2.symm
          (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
            (riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x))
            (by simpa only [one_mul] using
              riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm (r • x))) =
        r • physicalFourierL2.symm
            (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
              (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
              (by simpa only [one_mul] using
                riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x))
      have helem := riccatiSobolevJetCoefficient_weightedL2Element_smulRecovery29Isolated
        m k hkm r x
      calc
        _ = physicalFourierL2.symm
              ((r : ℂ) • weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
                (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
                (by simpa only [one_mul] using
                  riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x)) :=
            congrArg physicalFourierL2.symm helem
        _ = (r : ℂ) • physicalFourierL2.symm
              (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
                (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
                (by simpa only [one_mul] using
                  riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x)) :=
            map_smul physicalFourierL2.symm (r : ℂ) _
        _ = _ := by simp
  }
  exact f.mkContinuous ((2 * Real.pi) ^ k) (by
    intro x
    exact riccatiSobolevIteratedDerivativeL2Value_norm_leRecovery30First m k hkm x)

theorem riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier
    (m k : ℕ) (hkm : k ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    physicalFourier (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m k hkm x) n =
      riccatiSobolevJetCoefficientL2Recovery28Second m k x n := by
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First, LinearMap.mkContinuous_apply]
  change physicalFourier
    (physicalFourierL2.symm
      (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x))) n = _
  calc
    _ = (weightedL2Element (fun _ : ℤ => (1 : ℝ)) (fun _ => by norm_num)
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
        (by simpa only [one_mul] using
          riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x)) n :=
      physicalFourier_symm_apply _ n
    _ = riccatiSobolevJetCoefficientL2Recovery28Second m k x n :=
      NlsGge.Pilot.weightedL2Element_unit_coordinateMinimumRecovery30
        (riccatiSobolevJetCoefficientL2Recovery28Second m k x)
        (by simpa only [one_mul] using riccatiSobolevJetCoefficients_l2SummableRecovery28 m k hkm x) n

end NlsGge.HierarchyRiccati.Core

end
