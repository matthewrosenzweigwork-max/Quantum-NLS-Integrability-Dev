import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.NormCalculus

                                                                                                            
                                                                                                 
                                                             
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem h1_of_two (u : PhysicalL2) (hu : physicalSobolev 2 u) : physicalSobolev 1 u := by
  have h := (psn_mono (m := 1) (m' := 2) (by norm_num) (by simpa using hu)).1
  simpa using h

theorem h1_neg (u : PhysicalL2) (hu : physicalSobolev 1 u) : physicalSobolev 1 (-u) := by
  have h := (psn_neg 1 (by simpa using hu)).1
  simpa using h

theorem wd_H1_of_two (u : PhysicalL2) (hu : physicalSobolev 2 u) :
    physicalSobolev 1 (weakDerivative u) := by
  have h := (psn_deriv 1 (by simpa using hu)).1
  simpa using h

theorem physicalFourier_star (u : PhysicalL2) (n : ℤ) :
    physicalFourier (⇑(star u)) n = star (physicalFourier (⇑u) (-n)) := by
  unfold physicalFourier fourierCoeff
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  rw [ht]
  simp [fourier_neg, Complex.star_def]

theorem integral_mul_eq_tsum_fourier (u v : PhysicalL2) :
    ∫ x : PhysicalCircle, u x * v x ∂spatialMeasure =
      ∑' n : ℤ, physicalFourier (⇑u) n * physicalFourier (⇑v) (-n) := by
  have hI : ∫ x : PhysicalCircle, u x * v x ∂spatialMeasure = inner ℂ (star u) v := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with x hx
    rw [hx]
    simp [RCLike.inner_apply]
    ring
  rw [hI, ← LinearIsometryEquiv.inner_map_map physicalFourierL2 (star u) v, lp.inner_eq_tsum]
  have key : ∀ n : ℤ, inner ℂ (physicalFourierL2 (star u) n) (physicalFourierL2 v n) =
      physicalFourier (⇑u) (-n) * physicalFourier (⇑v) n := by
    intro n
    rw [physicalFourierL2_apply, physicalFourierL2_apply, physicalFourier_star]
    simp [RCLike.inner_apply, Complex.star_def]
    ring
  rw [tsum_congr key]
  have hr := (Equiv.neg ℤ).tsum_eq (fun m : ℤ => physicalFourier (⇑u) m * physicalFourier (⇑v) (-m))
  simp only [Equiv.neg_apply, neg_neg] at hr
  exact hr

theorem physicalFourier_weakDerivative (f : PhysicalL2) (hf : physicalSobolev 1 f) (k : ℤ) :
    physicalFourier (⇑(weakDerivative f)) k =
      2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * physicalFourier (⇑f) k := by
  have h := weakDerivative_coeff f (weakDerivative_domain_of_H1 f hf) (-k)
  rw [reflectedFourierL2_apply, reflectedFourierL2_apply] at h
  unfold reflectedFourier at h
  simp only [neg_neg] at h
  push_cast at h ⊢
  linear_combination (-1 : ℂ) * h

theorem integral_weakDerivative_mul (f g : PhysicalL2) (hf : physicalSobolev 1 f)
    (hg : physicalSobolev 1 g) :
    ∫ x : PhysicalCircle, weakDerivative f x * g x ∂spatialMeasure =
      -∫ x : PhysicalCircle, f x * weakDerivative g x ∂spatialMeasure := by
  rw [integral_mul_eq_tsum_fourier, integral_mul_eq_tsum_fourier, ← tsum_neg]
  congr 1
  funext m
  rw [physicalFourier_weakDerivative f hf m, physicalFourier_weakDerivative g hg (-m)]
  push_cast
  ring

end NlsGge.GKDefinitionDesign
end
