import NlsGge.Spectral.ActualPhysicalL2ZsSubintervalHomogeneousUniquenessV1
import NlsGge.Spectral.ComplexAbsolutelyContinuousAEODEIntegralIdentityV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

theorem actualPhysicalL2ZsProductContinuousState_subintervalIntegrable
    (u : PhysicalL2) (z : ℂ) (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 2)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) T)) (i j : Fin 2) :
    IntervalIntegrable (fun s => (zsCoefficientComplex
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
      z s * F s) i j) volume 0 T := by
  have hsub : Set.uIcc (0 : ℝ) T ⊆ Set.uIcc (0 : ℝ) 2 := by
    rw [Set.uIcc_of_le hT.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    exact fun s hs => ⟨hs.1, hs.2.trans hT.2⟩
  have hA (k : Fin 2) :=
    (actualPhysicalL2ZsCoefficient_all_entries_intervalIntegrable u z i k).mono_set hsub
  have hFc (k : Fin 2) : ContinuousOn (fun t => F t k j) (Set.uIcc (0 : ℝ) T) := by
    simpa only [Set.uIcc_of_le hT.1, Function.comp_def] using!
      (continuous_apply j).comp_continuousOn ((continuous_apply k).comp_continuousOn hF)
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using!
    ((hA 0).mul_continuousOn (hFc 0)).add ((hA 1).mul_continuousOn (hFc 1))

/-- Equal arbitrary initial matrices determine the same AC solution of the
actual rough physical ZS equation on every initial subinterval of [0,2].
This is the genuine uniqueness prerequisite for the rough monodromy shift. -/
theorem actualPhysicalL2Zs_subinterval_AC_same_initial_unique
    (u : PhysicalL2) (z : ℂ) (T : ℝ) (hT : T ∈ Set.Icc (0 : ℝ) 2)
    (F G : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (hinit : F 0 = G 0)
    (hF : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => F t i j) 0 T)
    (hG : ∀ i j : Fin 2, AbsolutelyContinuousOnInterval (fun t => G t i j) 0 T)
    (hFODE : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => F s i j)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          z t * F t) i j) t)
    (hGODE : ∀ i j : Fin 2, ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => G s i j)
        ((zsCoefficientComplex
          (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle))
          z t * G t) i j) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, F t = G t := by
  let U : ℝ → ℂ := fun x =>
    (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)
  let H : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t => F t - G t
  have hAC (i j : Fin 2) : AbsolutelyContinuousOnInterval (fun t => H t i j) 0 T := by
    simpa only [H, Matrix.sub_apply] using! (hF i j).sub (hG i j)
  have hH : ContinuousOn H (Set.Icc (0 : ℝ) T) := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    simpa only [Set.uIcc_of_le hT.1] using (hAC i j).continuousOn
  have hODE (i j : Fin 2) : ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) T →
      HasDerivAt (fun s => H s i j) ((zsCoefficientComplex U z t * H t) i j) t := by
    filter_upwards [hFODE i j, hGODE i j] with t hf hg
    intro ht
    simpa only [H, Matrix.mul_sub, Matrix.sub_apply] using! (hf ht).sub (hg ht)
  have hVolterra : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
      H t i j = ∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * H s) i j := by
    intro t ht i j
    have hint := actualPhysicalL2ZsProductContinuousState_subintervalIntegrable u z T hT H hH i j
    have htu : t ∈ Set.uIcc (0 : ℝ) T := by
      simpa only [Set.uIcc_of_le hT.1] using ht
    have hp := complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
      (hAC i j) hint (hODE i j) t htu
    have hzero : H 0 i j = 0 := by simp only [H, hinit, sub_self, Matrix.zero_apply]
    simpa only [hzero, zero_add] using! hp
  have hz := actualPhysicalL2ZsHomogeneousVolterra_subinterval_continuous_eq_zero
    u z T hT.2 H hH hVolterra
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end NlsGge.SpectralFoundations
end
