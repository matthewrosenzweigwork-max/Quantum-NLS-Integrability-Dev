import Mathlib
import NlsGge.Ramer.General.RamerGeneral

                                                                                                          
                                                                                                                       
                                                                                                                           
                                                                                                            
                                                                                                               
                                                                                                                                             
set_option autoImplicit false
noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

namespace NlsGge.ThirdConsultation.R

def GeneralRamerConclusion
    (S : NlsGge.Ramer.General.RamerSetting)
    (T : S.E ≃ₜ S.E) (K : S.E → S.H)
    (δK : (ℤ → ℂ) → ℝ) : Prop :=
  AEStronglyMeasurable δK S.γ ∧
  (∀ x₀ : S.E, ∃ r : ℝ, 0 < r ∧
    ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
      EqOn G K (ball x₀ r) ∧ S.IsClosedDiv (fun z => G (S.R z)) η) ∧
  (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
    EqOn G K (ball x₀ r) →
    S.IsClosedDiv (fun z => G (S.R z)) η →
      ∀ᵐ z ∂S.γ, S.R z ∈ ball x₀ r → δK z = η z) ∧
  let Jlim : S.E → ℝ := fun x =>
    |NlsGge.Analysis.RegularizedDeterminant.det2 (S.hsDerivH K x)| *
      Real.exp (-δK (S.coordE x) - ‖K x‖ ^ 2 / 2)
  S.γE.map T.symm = S.γE.withDensity
    (fun x => ENNReal.ofReal (Jlim x)) ∧
  (∀ x : S.E, 0 < Jlim x) ∧ Integrable Jlim S.γE ∧
  (∫ x : S.E, Jlim x ∂S.γE) = 1 ∧
  TendstoInMeasure S.γ
    (fun N z => NlsGge.Ramer.finiteRamerDensity
      (fun v => v + S.truncField K N v) (S.headPt N z))
    atTop (fun z => Jlim (S.R z))

theorem ramer_general
    (S : NlsGge.Ramer.General.RamerSetting)
    (T : S.E ≃ₜ S.E) (K Kinv : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hKi : ContDiff ℝ 2 Kinv)
    (hT : ∀ x : S.E, T x = x + S.incl (K x))
    (hTi : ∀ y : S.E, T.symm y = y + S.incl (Kinv y)) :
    ∃ δK : (ℤ → ℂ) → ℝ, GeneralRamerConclusion S T K δK := by
  obtain ⟨δK, h2, h3, hrest⟩ := S.ramer_general T K Kinv hT hTi hK hKi
  obtain ⟨δ0, hm0, -, h3', -, -⟩ := S.divergence_identification K hK
  have hae : δK =ᵐ[S.γ] δ0 := S.v2_divergence_unique K δK δ0 h2 h3 h3'
  exact ⟨δK, hm0.congr hae.symm, h2, h3, hrest⟩

end NlsGge.ThirdConsultation.R
end
