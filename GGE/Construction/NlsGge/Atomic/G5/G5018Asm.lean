import Mathlib
import NlsGge.Atomic.G5.G5018Host
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5018Dir
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5024
import NlsGge.GK38.DirichletRealSign
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealBridge
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                  
                                                                              
                                                                                                                                              
                                                  
                                                                                                                                     
                                                                                                                              
                                  
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018_antiDiscrim_ne_zero (u : PhysicalL2) (m : ℤ)
    (hm : InteriorRealDirichletGap m u) :
    antiDiscrim (realSlice u) (muSeq (realSlice u) m) ≠ 0 := by
  intro h0
  rw [muSeq_eq_gkMu38] at h0
  have hsq := dirichlet_perChar_eq_anti_sq38 (realSlice u) (gkMu u m : ℂ) (gkMu_root38 u m)
  rw [h0] at hsq
  have hx : perChar (realSlice u) (gkMu u m : ℂ) = 0 := by rw [hsq]; ring
  have hlevel : NlsGge.SpectralFoundations.actualQuasimomentumRealPartE02_38 u (gkMu u m) =
      (m : ℝ) * Real.pi := by
    have hmem := gkMu_mem_gap38 u m
    rw [← (NlsGge.SpectralFoundations.actualGapLevelSet_eq_Icc_E02_38 u m).2] at hmem
    exact hmem
  have hroot := periodic_level_root_pair38 u (gkMu u m) m hx hlevel
  obtain ⟨hP, hM⟩ := lamPlus_real u m
  obtain ⟨hlo, hhi⟩ := hm
  rcases hroot with h | h
  · rw [hM] at h
    have := Complex.ofReal_injective h
    linarith
  · rw [hP] at h
    have := Complex.ofReal_injective h
    linarith

/-- Riesz bridge: pairing with the discriminant functional is evaluation on the spectral Hamiltonian field. -/
theorem g5018_pairPoissonCLM_discrim (u : PhysicalL2) (lam : ℂ) (M : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM M (fderiv ℂ (fun φ : PotPair => discrim φ lam) (realSlice u)) =
      M (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) := by
  rw [(hasFDerivAt_gradDiscrimCLM (realSlice u) lam).fderiv]
  unfold pairPoissonCLM
  rw [NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_gradDiscrimCLM]
  rfl

theorem g5018_assembly (u : PhysicalL2) (m n : ℤ) (lam : ℂ)
    (hm : InteriorRealDirichletGap m u) (hn : gamma2 (realSlice u) n ≠ 0)
    (hM4 : m ≠ n →
      fderiv ℂ (offDiagonalBeta n m) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
      (psiAt n (muSeq (realSlice u) m) (realSlice u) /
        antiDiscrim (realSlice u) (muSeq (realSlice u) m)) *
      fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam))
    (hM5b : m = n →
      (angleDerivative n (realSlice u) -
        fderiv ℂ (betaSum n) (realSlice u))
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
      (psiAt n (muSeq (realSlice u) n) (realSlice u) /
        antiDiscrim (realSlice u) (muSeq (realSlice u) n)) *
      fderiv ℂ (fun ψ : PotPair => muSeq ψ n) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam)) :
    2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
      (angleIntegralDerivative m n (realSlice u)) =
    psiAt n (muSeq (realSlice u) m) (realSlice u) *
      PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) m) lam := by
  have hδ := g5018_antiDiscrim_ne_zero u m hm
  have hD := g5018_dirichlet_fderiv_hamField u m lam hm
  rw [pairPoissonCLM_antisymm, g5018_pairPoissonCLM_discrim]
  have hB : angleIntegralDerivative m n (realSlice u)
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
      (psiAt n (muSeq (realSlice u) m) (realSlice u) /
        antiDiscrim (realSlice u) (muSeq (realSlice u) m)) *
      fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) := by
    by_cases h : m = n
    · subst h
      unfold angleIntegralDerivative
      rw [if_pos rfl]
      exact hM5b rfl
    · unfold angleIntegralDerivative
      rw [if_neg h]
      exact hM4 h
  rw [hB]
  rw [show 2 * -(psiAt n (muSeq (realSlice u) m) (realSlice u) /
        antiDiscrim (realSlice u) (muSeq (realSlice u) m) *
      fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam)) =
      -(psiAt n (muSeq (realSlice u) m) (realSlice u) /
        antiDiscrim (realSlice u) (muSeq (realSlice u) m)) *
      (2 * fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam)) by ring, hD]
  field_simp

end
end NlsGge.GKDefinitionDesign
