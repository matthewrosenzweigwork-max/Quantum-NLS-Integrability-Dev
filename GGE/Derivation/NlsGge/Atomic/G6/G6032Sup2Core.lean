import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.Atomic.KSN.KSN012Sup4

/- G6032 SUP2 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6032Sup2Core.lean, namespace NlsGge.ThirdConsultation.G6032S.  SUPPORT (no packet
   increment): weakDerivative_star : weakDerivative (star w) = star (weakDerivative w) (grep NlsGge/ 2026-11-02: absent).
   Route: reflected Fourier coefficients of star w are star of the reflected coefficients at -n (landed
   KSN.sup4_physicalFourier_star); the multiplier -2πi n turns into its conjugate at -n, so the multiplier sequence of
   star w is n ↦ star (d (-n)); ℓ²-membership is invariant under reflection and conjugation; Fourier injectivity.
   Both totalized branches of the landed weakDerivative are treated (non-ℓ² gives 0 = star 0). -/
set_option autoImplicit false

open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6032S
noncomputable section
attribute [local instance] Classical.propDecidable

def dF (u : PhysicalL2) (n : ℤ) : ℂ := (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * reflectedFourierL2 u n

theorem wd_eq (u : PhysicalL2) :
    weakDerivative u = if h : Memℓp (dF u) 2 then reflectedFourierL2.symm ⟨dF u, h⟩ else 0 := rfl

theorem rF_star (w : PhysicalL2) (n : ℤ) :
    reflectedFourierL2 (star w) n = star (reflectedFourierL2 w (-n)) := by
  rw [reflectedFourierL2_apply, reflectedFourierL2_apply]
  unfold reflectedFourier
  rw [NlsGge.ThirdConsultation.KSN.sup4_physicalFourier_star, star_neg]

theorem dF_star (w : PhysicalL2) : dF (star w) = fun n => star (dF w (-n)) := by
  funext n
  unfold dF
  rw [rF_star, star_mul']
  congr 1
  rw [Complex.star_def]
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast, Int.cast_neg]
  ring

theorem mem_iff (d : ℤ → ℂ) : Memℓp (fun n => star (d (-n))) 2 ↔ Memℓp d 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  rw [memℓp_gen_iff hp, memℓp_gen_iff hp]
  simp only [norm_star]
  exact (Equiv.neg ℤ).summable_iff (f := fun n => ‖d n‖ ^ (2 : ENNReal).toReal)

theorem weakDerivative_star (w : PhysicalL2) :
    weakDerivative (star w) = star (weakDerivative w) := by
  rw [wd_eq, wd_eq]
  by_cases hd : Memℓp (dF w) 2
  · have hd' : Memℓp (dF (star w)) 2 := by rw [dF_star]; exact (mem_iff _).2 hd
    rw [dif_pos hd', dif_pos hd]
    apply reflectedFourierL2.injective
    apply lp.ext
    funext n
    rw [LinearIsometryEquiv.apply_symm_apply, rF_star, LinearIsometryEquiv.apply_symm_apply]
    show dF (star w) n = star (dF w (-n))
    rw [dF_star]
  · have hd' : ¬ Memℓp (dF (star w)) 2 := by rw [dF_star]; exact fun h => hd ((mem_iff _).1 h)
    rw [dif_neg hd', dif_neg hd]
    apply reflectedFourierL2.injective
    apply lp.ext
    funext n
    rw [rF_star, map_zero, lp.coeFn_zero, Pi.zero_apply, Pi.zero_apply, star_zero]

end
end NlsGge.ThirdConsultation.G6032S
