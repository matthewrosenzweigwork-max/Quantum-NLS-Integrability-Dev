import NlsGge.Hierarchy.RiccatiSobolevJetCoefficientL2BoundRecovery28Second
import NlsGge.Hierarchy.RiccatiAttachedRecursionCore
import NlsGge.Hierarchy.RiccatiPhysicalH1CanonicalAndDerivativeCLMAfterDerivativeClassLinearityPrerequisite
import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Hierarchy.RiccatiSobolevJetBooleanAndNormAlgebraMinimumRecovery30Fifth
import NlsGge.Hierarchy.RiccatiTopJetSlotMultiplicityAtMostTwoMinimumRecovery30Third
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot

private theorem riccatiSobolevJetH1_pointwiseBoundRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    sobolevModeWeight (1 : ℝ) n *
        ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 ≤
      (2 * Real.pi) ^ (2 * k) *
        (sobolevModeWeight (m : ℝ) n *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
  let wM := sobolevModeWeight (m : ℝ)
  let w1 := sobolevModeWeight (1 : ℝ)
  have hn : |(n : ℝ)| ≤ japaneseBracket n := by
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    linarith
  have hpowN : |(n : ℝ)| ^ (2 * k) ≤ japaneseBracket n ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg _) hn _
  have hpowB : japaneseBracket n ^ (2 * (k + 1)) ≤
      japaneseBracket n ^ (2 * m) :=
    pow_le_pow_right₀ (japaneseBracket_one_le n) (by
      have hexp : k + 1 ≤ m := hkm
      omega)
  have hweightM : wM n = japaneseBracket n ^ (2 * m) := by
    dsimp [wM, sobolevModeWeight]
    have he : 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [he]
    exact Real.rpow_natCast _ _
  have hweight1 : w1 n = japaneseBracket n ^ (2 : ℕ) := by
    dsimp [w1, sobolevModeWeight]
    have he : 2 * (1 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [he]
    exact Real.rpow_natCast _ _
  have hfreq : japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) ≤
      japaneseBracket n ^ (2 * m) := by
    calc
      japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) ≤
          japaneseBracket n ^ 2 * japaneseBracket n ^ (2 * k) :=
        mul_le_mul_of_nonneg_left hpowN (by positivity)
      _ = japaneseBracket n ^ (2 * (k + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ japaneseBracket n ^ (2 * m) := hpowB
  change w1 n *
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2 ≤
    (2 * Real.pi) ^ (2 * k) *
      (wM n * ‖(show WeightedHilbert wM from x) n‖ ^ 2)
  rw [hweight1, riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second]
  calc
    japaneseBracket n ^ 2 *
        ((2 * Real.pi) ^ (2 * k) * |(n : ℝ)| ^ (2 * k) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) =
        (2 * Real.pi) ^ (2 * k) *
          (japaneseBracket n ^ 2 * |(n : ℝ)| ^ (2 * k) *
            ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by ring
    _ ≤ (2 * Real.pi) ^ (2 * k) *
        (japaneseBracket n ^ (2 * m) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfreq (sq_nonneg _)) (by positivity)
    _ = (2 * Real.pi) ^ (2 * k) *
        (wM n * ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
      rw [← hweightM]

private theorem riccatiSobolevJetH1_summableRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    Summable (fun n : ℤ => sobolevModeWeight (1 : ℝ) n *
      ‖riccatiSobolevJetCoefficientL2Recovery28Second m k x n‖ ^ 2) := by
  let wM := sobolevModeWeight (m : ℝ)
  have hsource : Summable (fun n : ℤ => wM n *
      ‖(show WeightedHilbert wM from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum wM (show WeightedHilbert wM from x)).summable
  have hmajor := hsource.mul_left ((2 * Real.pi) ^ (2 * k))
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sobolevModeWeightPositive 1 |>.out n).le (sq_nonneg _))
    (fun n => riccatiSobolevJetH1_pointwiseBoundRecovery30Eighth m k hkm x n)
    hmajor

private noncomputable def riccatiSobolevJetH1ValueRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    SobolevHilbert (1 : ℝ) := by
  let d := riccatiSobolevJetCoefficientL2Recovery28Second m k x
  have hd := riccatiSobolevJetH1_summableRecovery30Eighth m k hkm x
  have hmem : d ∈ weightedSubmodule (sobolevModeWeight (1 : ℝ)) := by
    change Memℓp (weightedCoordinates (sobolevModeWeight (1 : ℝ)) d) 2
    exact (weightedCoordinates_mem_l2_iff (sobolevModeWeight (1 : ℝ))
      (fun n => (sobolevModeWeightPositive 1).out n |>.le) d).2 (by simpa [d] using hd)
  exact (⟨d, hmem⟩ : WeightedHilbert (sobolevModeWeight (1 : ℝ)))

private theorem riccatiSobolevJetH1Value_coordinateRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight (1 : ℝ)) from
      riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x) n =
      riccatiSobolevJetCoefficientL2Recovery28Second m k x n := rfl

private theorem riccatiSobolevJetCoefficient_addRecovery30Eighth
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

private theorem riccatiSobolevJetCoefficient_smulRecovery30Eighth
    (m k : ℕ) (r : ℝ) (x : SobolevHilbert (m : ℝ)) :
    riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x) =
      (r : ℂ) • riccatiSobolevJetCoefficientL2Recovery28Second m k x := by
  funext n
  change fourierMultiplier n ^ k *
      ((r : ℂ) * (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n) =
    (r : ℂ) * (fourierMultiplier n ^ k *
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n)
  ring

private theorem riccatiSobolevJetH1Value_norm_leRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) (x : SobolevHilbert (m : ℝ)) :
    ‖riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x‖ ≤
      (2 * Real.pi) ^ k * ‖x‖ := by
  let wM := sobolevModeWeight (m : ℝ)
  let w1 := sobolevModeWeight (1 : ℝ)
  let d := riccatiSobolevJetCoefficientL2Recovery28Second m k x
  have hsource : Summable (fun n : ℤ => wM n *
      ‖(show WeightedHilbert wM from x) n‖ ^ 2) :=
    (weightedHilbert_hasSum wM (show WeightedHilbert wM from x)).summable
  have htarget := riccatiSobolevJetH1_summableRecovery30Eighth m k hkm x
  have hpoint := fun n => riccatiSobolevJetH1_pointwiseBoundRecovery30Eighth m k hkm x n
  have hsum := htarget.tsum_le_tsum hpoint (hsource.mul_left ((2 * Real.pi) ^ (2 * k)))
  have hout := weightedHilbert_norm_sq w1
    (show WeightedHilbert w1 from riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x)
  have hin0 := weightedHilbert_norm_sq wM (show WeightedHilbert wM from x)
  have hin : ‖x‖ ^ 2 = ∑' n : ℤ, wM n *
      ‖(show WeightedHilbert wM from x) n‖ ^ 2 := by
    simpa only using! hin0
  have hsq : ‖riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x‖ ^ 2 ≤
      ((2 * Real.pi) ^ k * ‖x‖) ^ 2 := by
    calc
      ‖riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x‖ ^ 2 =
          ∑' n : ℤ, w1 n *
            ‖(show WeightedHilbert w1 from
              riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x) n‖ ^ 2 := hout
      _ = ∑' n : ℤ, w1 n * ‖d n‖ ^ 2 := by
        apply tsum_congr
        intro n
        rw [riccatiSobolevJetH1Value_coordinateRecovery30Eighth]
      _ ≤ ∑' n : ℤ, (2 * Real.pi) ^ (2 * k) *
          (wM n * ‖(show WeightedHilbert wM from x) n‖ ^ 2) := hsum
      _ = (2 * Real.pi) ^ (2 * k) * ‖x‖ ^ 2 := by
        rw [tsum_mul_left, hin]
      _ = ((2 * Real.pi) ^ k * ‖x‖) ^ 2 := by
        have hpow : (2 * Real.pi) ^ (2 * k) = ((2 * Real.pi) ^ k) ^ 2 := by
          calc
            (2 * Real.pi) ^ (2 * k) = (2 * Real.pi) ^ (k * 2) := by
              congr 1
              omega
            _ = ((2 * Real.pi) ^ k) ^ 2 := by
              rw [pow_mul]
        calc
          (2 * Real.pi) ^ (2 * k) * ‖x‖ ^ 2 =
              ((2 * Real.pi) ^ k) ^ 2 * ‖x‖ ^ 2 := by rw [hpow]
          _ = ((2 * Real.pi) ^ k * ‖x‖) ^ 2 := by
            simpa only [Real.norm_of_nonneg (norm_nonneg x)] using
              (riccatiSobolevJet_multiplierNormProductSquareMinimumRecovery30Fifth
                k ‖x‖).symm
  have hnonneg : 0 ≤ (2 * Real.pi) ^ k * ‖x‖ := by positivity
  nlinarith [sq_nonneg (‖riccatiSobolevJetH1ValueRecovery30Eighth m k hkm x‖ -
    (2 * Real.pi) ^ k * ‖x‖)]

/-- For k+1≤m the actual multiplier coefficients define a bounded map into
H¹; composing the existing H¹ representative embedding gives the concrete
continuous representative of the k-th jet. -/
noncomputable def riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
    (m k : ℕ) (hkm : k + 1 ≤ m) :
    SobolevHilbert (m : ℝ) →L[ℝ] C(PhysicalCircle, ℂ) := by
  let f : SobolevHilbert (m : ℝ) →ₗ[ℝ] SobolevHilbert (1 : ℝ) := {
    toFun := riccatiSobolevJetH1ValueRecovery30Eighth m k hkm
    map_add' := by
      intro x y
      apply Subtype.ext
      change riccatiSobolevJetCoefficientL2Recovery28Second m k (x + y) =
        riccatiSobolevJetCoefficientL2Recovery28Second m k x +
          riccatiSobolevJetCoefficientL2Recovery28Second m k y
      exact riccatiSobolevJetCoefficient_addRecovery30Eighth m k x y
    map_smul' := by
      intro r x
      apply Subtype.ext
      change riccatiSobolevJetCoefficientL2Recovery28Second m k (r • x) =
        (r : ℂ) • riccatiSobolevJetCoefficientL2Recovery28Second m k x
      exact riccatiSobolevJetCoefficient_smulRecovery30Eighth m k r x
  }
  let F := f.mkContinuous ((2 * Real.pi) ^ k) (by
    intro x
    exact riccatiSobolevJetH1Value_norm_leRecovery30Eighth m k hkm x)
  exact physicalH1CanonicalContinuousRepresentativeCLM.comp F

/-- Actual source jet convention: the true Boolean component is star of the
continuous representative; the false component is the representative itself. -/
noncomputable def riccatiSobolevJetContinuousRepresentativeRecovery30Eighth
    (m : ℕ) (v : Jet) (horder : v.2 + 1 ≤ m) :
    SobolevHilbert (m : ℝ) → C(PhysicalCircle, ℂ) :=
  fun x => if v.1 then
    star (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m v.2 horder x)
    else riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m v.2 horder x

theorem riccatiSobolevJetContinuousRepresentative_continuousRecovery30Eighth
    (m : ℕ) (v : Jet) (horder : v.2 + 1 ≤ m) :
    Continuous (riccatiSobolevJetContinuousRepresentativeRecovery30Eighth m v horder) := by
  let G : ℕ → SobolevHilbert (m : ℝ) → C(PhysicalCircle, ℂ) := fun _ =>
    riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth m v.2 horder
  have hG : ∀ k, Continuous (G k) := by
    intro k
    exact (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth
      m v.2 horder).continuous
  change Continuous (fun x =>
    if v.1 then star (G v.2 x) else G v.2 x)
  exact continuous_riccatiBooleanJetFromContinuousFamilyMinimumRecovery30Fifth G hG v

end NlsGge.HierarchyRiccati.Core

end
