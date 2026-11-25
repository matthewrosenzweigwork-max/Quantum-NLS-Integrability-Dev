import Mathlib
import NlsGge.Atomic.KSN.KSN012Host
import NlsGge.ThirdConsultation.M.M021Host
import NlsGge.ThirdConsultation.M.M031Weight
import NlsGge.Analysis.FullCoverFourier

/- KSN012B1 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN012B1.lean.
   Supporting bridge B1 of proof development/KSN012_STOP.md (statement verbatim from that file):
     ∃ w₁ : ℤ → ℝ, NlsGge.ThirdConsultation.M.OneDerivativeWeight w₁ ∧ ∃ C : ℝ, ∀ x : PairScale 1,
       MTwoMode.potentialCoefficientEnergy w₁ (pairPotential 1 (by norm_num) x) ≤ ENNReal.ofReal (C * ‖x‖ ^ 2).
   Witnesses: w₁ = sourceH1Weight (landed M-031, `oneDerivativeWeight_sourceH1Weight`), C = (1 + 2π)².
   Route (period-1/2 normalization): the M-021 coefficient pair is the period-2 Fourier coefficient of the natural cover
   (doubled spectral interval); it vanishes at odd raw indices and at 2m equals the period-1 physicalFourier at m
   (landed `naturalPhysicalCoverL2_fourier_odd/_even_index`), which for pairPotential is rawCoefficient 1 x b m
   = x(b,m)/⟨m⟩ (physicalFourierL2 isometric equivalence, `physicalFourierL2_apply`). Pointwise
   (1 + π|2m|) ≤ (1 + 2π)⟨m⟩, so each even term is ≤ (1+2π)² (‖x(true,m)‖² + ‖x(false,m)‖²); reindex the ENNReal
   sum along k = 2m (odd terms are zero) and use the ℓ² Parseval sum of x over Bool × ℤ. All sums are nonnegative
   ENNReal sums; the real sum is used only after its HasSum is proved. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem KSN012B1_coeff_odd (φ : PotPair) (b : Bool) (k : ℤ) (hk : k % 2 ≠ 0) :
    MTwoMode.potentialCoefficientPair φ b k = 0 := by
  unfold MTwoMode.potentialCoefficientPair
  exact NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ k hk

theorem KSN012B1_coeff_even (x : PairScale 1) (b : Bool) (m : ℤ) :
    MTwoMode.potentialCoefficientPair (pairPotential 1 (by norm_num) x) b (2 * m) =
      rawCoefficient 1 x b m := by
  unfold MTwoMode.potentialCoefficientPair
  rw [NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even_index _ (2 * m) (by omega),
    show 2 * m / 2 = m by omega]
  cases b
  · simp only [Bool.false_eq_true, ite_false, pairPotential]
    rw [← physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
  · simp only [ite_true, pairPotential]
    rw [← physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]

theorem KSN012B1_weight_le (m : ℤ) :
    M.sourceH1Weight (2 * m) ≤ (1 + 2 * Real.pi) * scaleWeight 1 m := by
  unfold M.sourceH1Weight scaleWeight bracket
  rw [Real.rpow_one]
  have habs : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  have h1 : |Real.pi * ((2 * m : ℤ) : ℝ)| = 2 * Real.pi * |(m : ℝ)| := by
    push_cast
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    ring
  rw [h1]
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ max 1 |(m : ℝ)| := le_max_left _ _
  have hm2 : |(m : ℝ)| ≤ max 1 |(m : ℝ)| := le_max_right _ _
  nlinarith

theorem KSN012B1_term_le (x : PairScale 1) (b : Bool) (m : ℤ) :
    M.sourceH1Weight (2 * m) ^ 2 * ‖rawCoefficient 1 x b m‖ ^ 2 ≤
      (1 + 2 * Real.pi) ^ 2 * ‖x (b, m)‖ ^ 2 := by
  have hw1 : 1 ≤ scaleWeight 1 m := by
    unfold scaleWeight bracket
    rw [Real.rpow_one]
    exact le_max_left _ _
  have hwpos : 0 < scaleWeight 1 m := by linarith
  have hraw : ‖rawCoefficient 1 x b m‖ = ‖x (b, m)‖ / scaleWeight 1 m := by
    unfold rawCoefficient
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hwpos.le]
  rw [hraw, div_pow]
  have hW0 : 0 ≤ M.sourceH1Weight (2 * m) := by
    unfold M.sourceH1Weight
    positivity
  have hle := KSN012B1_weight_le m
  have hsq : M.sourceH1Weight (2 * m) ^ 2 ≤ ((1 + 2 * Real.pi) * scaleWeight 1 m) ^ 2 :=
    pow_le_pow_left₀ hW0 hle 2
  have hs2 : 0 < scaleWeight 1 m ^ 2 := by positivity
  rw [mul_div_assoc', div_le_iff₀ hs2]
  calc M.sourceH1Weight (2 * m) ^ 2 * ‖x (b, m)‖ ^ 2
      ≤ ((1 + 2 * Real.pi) * scaleWeight 1 m) ^ 2 * ‖x (b, m)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (1 + 2 * Real.pi) ^ 2 * ‖x (b, m)‖ ^ 2 * scaleWeight 1 m ^ 2 := by ring

theorem KSN012B1_hasSum_sq (x : PairScale 1) :
    HasSum (fun m : ℤ => ‖x (true, m)‖ ^ 2 + ‖x (false, m)‖ ^ 2) (‖x‖ ^ 2) := by
  have hx := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx
  have hsw := (Equiv.prodComm ℤ Bool).hasSum_iff.mpr hx
  have hfib := HasSum.prod_fiberwise hsw (fun m => hasSum_fintype _)
  simpa only [Function.comp_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Fintype.sum_bool,
    add_comm] using hfib

theorem KSN012B1_main :
    ∃ w₁ : ℤ → ℝ, NlsGge.ThirdConsultation.M.OneDerivativeWeight w₁ ∧ ∃ C : ℝ, ∀ x : PairScale 1,
      MTwoMode.potentialCoefficientEnergy w₁ (pairPotential 1 (by norm_num) x) ≤
        ENNReal.ofReal (C * ‖x‖ ^ 2) := by
  refine ⟨M.sourceH1Weight, M.oneDerivativeWeight_sourceH1Weight, (1 + 2 * Real.pi) ^ 2, fun x => ?_⟩
  set D : ℝ := (1 + 2 * Real.pi) ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set T : ℤ → ℝ≥0∞ := fun k => ENNReal.ofReal (M.sourceH1Weight k ^ 2 *
      (‖MTwoMode.potentialCoefficientPair (pairPotential 1 (by norm_num) x) true k‖ ^ 2 +
        ‖MTwoMode.potentialCoefficientPair (pairPotential 1 (by norm_num) x) false k‖ ^ 2)) with hT
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := by
    intro a b h
    simp only at h
    omega
  have hsupp : Function.support T ⊆ Set.range (fun m : ℤ => 2 * m) := by
    intro k hk
    by_contra hk'
    apply hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hk' ⟨k / 2, by simp only; omega⟩
    simp only [hT, KSN012B1_coeff_odd _ _ k hodd, norm_zero]
    simp
  have hre : MTwoMode.potentialCoefficientEnergy M.sourceH1Weight (pairPotential 1 (by norm_num) x) =
      ∑' m : ℤ, T (2 * m) := by
    unfold MTwoMode.potentialCoefficientEnergy
    exact (hinj.tsum_eq hsupp).symm
  rw [hre]
  have hterm : ∀ m : ℤ, T (2 * m) ≤ ENNReal.ofReal (D * (‖x (true, m)‖ ^ 2 + ‖x (false, m)‖ ^ 2)) := by
    intro m
    simp only [hT]
    apply ENNReal.ofReal_le_ofReal
    rw [KSN012B1_coeff_even x true m, KSN012B1_coeff_even x false m, mul_add, mul_add]
    exact add_le_add (KSN012B1_term_le x true m) (KSN012B1_term_le x false m)
  have hS := KSN012B1_hasSum_sq x
  have hsum : ∑' m : ℤ, ENNReal.ofReal (D * (‖x (true, m)‖ ^ 2 + ‖x (false, m)‖ ^ 2)) =
      ENNReal.ofReal (D * ‖x‖ ^ 2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (hS.summable.mul_left D),
      tsum_mul_left, hS.tsum_eq]
  calc ∑' m : ℤ, T (2 * m)
      ≤ ∑' m : ℤ, ENNReal.ofReal (D * (‖x (true, m)‖ ^ 2 + ‖x (false, m)‖ ^ 2)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (D * ‖x‖ ^ 2) := hsum

end
end NlsGge.ThirdConsultation.KSN
