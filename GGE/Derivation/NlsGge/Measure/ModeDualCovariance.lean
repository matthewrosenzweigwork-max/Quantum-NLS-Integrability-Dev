import NlsGge.Measure.WeightedModes
import NlsGge.Sobolev.RealBasis
import Mathlib.Analysis.Normed.Operator.Basic
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace NlsGge.Measure

local instance instFullWeightedDualNormAfterReopen {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :=
  (ContinuousLinearMap.hasOpNorm :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ))

def fullWeightedDualCovarianceTerm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L M : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) (n : ℤ) : ℝ :=
  (L (fullWeightedModeMap c s n (1 : ℂ)) * M (fullWeightedModeMap c s n (1 : ℂ)) +
    L (fullWeightedModeMap c s n Complex.I) * M (fullWeightedModeMap c s n Complex.I)) /
      (2 * NlsGge.Pilot.sourceRate c n)

lemma fullWeightedDualCovarianceTerm_abs_le {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (L M : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) (n : ℤ) :
    |fullWeightedDualCovarianceTerm c s L M n| ≤
      ‖L‖ * ‖M‖ * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s) := by
  let e₁ : NlsGge.Pilot.FullWeightedHilbert c s := fullWeightedModeMap c s n (1 : ℂ)
  let eᵢ : NlsGge.Pilot.FullWeightedHilbert c s := fullWeightedModeMap c s n Complex.I
  have hrate : 0 < NlsGge.Pilot.sourceRate c n := NlsGge.Pilot.sourceRate_pos c n
  have hden : 0 < 2 * NlsGge.Pilot.sourceRate c n := mul_pos (by norm_num) hrate
  have hprod (x : NlsGge.Pilot.FullWeightedHilbert c s) :
      |L x * M x| ≤ ‖L‖ * ‖M‖ * ‖x‖ ^ 2 := by
    calc
      |L x * M x| = ‖L x‖ * ‖M x‖ := by
        rw [← Real.norm_eq_abs, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (‖L‖ * ‖x‖) * (‖M‖ * ‖x‖) :=
        mul_le_mul (L.le_opNorm x) (M.le_opNorm x) (norm_nonneg _)
          (mul_nonneg L.opNorm_nonneg (norm_nonneg x))
      _ = ‖L‖ * ‖M‖ * ‖x‖ ^ 2 := by ring
  have he₁ : ‖e₁‖ ^ 2 = NlsGge.Pilot.fullModeWeight c s n := by
    dsimp [e₁]
    rw [fullWeightedModeMap_norm, norm_one, mul_one,
      Real.sq_sqrt (NlsGge.Pilot.fullModeWeight_pos c s n).le]
  have heᵢ : ‖eᵢ‖ ^ 2 = NlsGge.Pilot.fullModeWeight c s n := by
    dsimp [eᵢ]
    rw [fullWeightedModeMap_norm, Complex.norm_I, mul_one,
      Real.sq_sqrt (NlsGge.Pilot.fullModeWeight_pos c s n).le]
  have hnum :
      |L e₁ * M e₁ + L eᵢ * M eᵢ| ≤
        2 * (‖L‖ * ‖M‖ * NlsGge.Pilot.fullModeWeight c s n) := by
    calc
      |L e₁ * M e₁ + L eᵢ * M eᵢ| ≤
          |L e₁ * M e₁| + |L eᵢ * M eᵢ| := abs_add_le _ _
      _ ≤ (‖L‖ * ‖M‖ * ‖e₁‖ ^ 2) + (‖L‖ * ‖M‖ * ‖eᵢ‖ ^ 2) :=
        add_le_add (hprod e₁) (hprod eᵢ)
      _ = 2 * (‖L‖ * ‖M‖ * NlsGge.Pilot.fullModeWeight c s n) := by
        rw [he₁, heᵢ]
        ring
  rw [fullWeightedDualCovarianceTerm, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |L e₁ * M e₁ + L eᵢ * M eᵢ| ≤
        2 * (‖L‖ * ‖M‖ * NlsGge.Pilot.fullModeWeight c s n) := hnum
    _ = (‖L‖ * ‖M‖ * Real.rpow (NlsGge.Pilot.japaneseBracket n) (-2 * s)) *
        (2 * NlsGge.Pilot.sourceRate c n) := by
      rw [NlsGge.Pilot.fullModeWeight]
      ring

lemma summable_fullWeightedDualCovarianceTerm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (L M : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    Summable (fun n : ℤ => fullWeightedDualCovarianceTerm c s L M n) := by
  apply Summable.of_norm_bounded
    ((summable_japaneseBracket_sobolev_decay s hs).mul_left (‖L‖ * ‖M‖))
  intro n
  rw [Real.norm_eq_abs]
  exact fullWeightedDualCovarianceTerm_abs_le c s L M n

end NlsGge.Measure
