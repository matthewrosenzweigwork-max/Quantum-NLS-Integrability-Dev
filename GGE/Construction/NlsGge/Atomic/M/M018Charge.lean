import Mathlib
import NlsGge.Atomic.G2.G2045SupB4
import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.NLS38.FlowMaps38
import NlsGge.ThirdConsultation.M.MOdd1Core

                                                                                                                     
                                                                                                        
                                                                         
                                                                                                               
                                                                                                                    
                                                                                                                       
                                                                                                         
set_option autoImplicit false
open Filter Topology MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.Atomic.Common NlsGge.NLS38

namespace NlsGge.ThirdConsultation.M018C

open NlsGge.ThirdConsultation.M

theorem fourierSeq38_physicalOfSobolev (m : ℕ) (x : SobolevR m) (n : ℤ) :
    fourierSeq38 (physicalOfSobolev x) n =
      carrierCoe38 (m : ℝ) (physicalSobolevFourierEquiv38 (m : ℝ) x) n := by
  rw [← physicalSobolevEmbed_eq_M]; exact physicalSobolevEmbed_fourier m x n

theorem psn_physicalOfSobolev_sub (m : ℕ) (x y : SobolevR m) :
    physicalSobolevNorm (m : ℝ) (physicalOfSobolev x - physicalOfSobolev y) = ‖x - y‖ := by
  rw [psn_eq_hn]
  have e1 : ‖x - y‖ = ‖physicalSobolevFourierEquiv38 (m : ℝ) x - physicalSobolevFourierEquiv38 (m : ℝ) y‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [e1, norm_sub_eq_hn38]
  congr 1
  funext n
  have h : fourierSeq38 (physicalOfSobolev x - physicalOfSobolev y) n =
      fourierSeq38 (physicalOfSobolev x) n - fourierSeq38 (physicalOfSobolev y) n := by
    unfold fourierSeq38; rw [map_sub]; rfl
  rw [h, fourierSeq38_physicalOfSobolev, fourierSeq38_physicalOfSobolev]

theorem pairSobolev_realSlice (m : ℕ) (x : SobolevR m) :
    pairSobolev (m : ℝ) (realSlice (physicalOfSobolev x)) := by
  have h1 : physicalSobolev (m : ℝ) (physicalOfSobolev x) := by
    rw [physicalSobolev_iff_mem, ← physicalSobolevEmbed_eq_M]
    exact NlsGge.GKDefinitionDesign.physicalSobolevEmbed_mem m x
  exact ⟨h1, g2045b_psob_star (m : ℝ) _ h1⟩

theorem pairSobolevNorm_realSlice_sub (m : ℕ) (x y : SobolevR m) :
    pairSobolevNorm (m : ℝ) (realSlice (physicalOfSobolev x) - realSlice (physicalOfSobolev y)) =
      Real.sqrt 2 * ‖x - y‖ := by
  rw [← map_sub]
  unfold pairSobolevNorm
  rw [realSlice_apply]
  simp only
  rw [g2045b_psn_star, psn_physicalOfSobolev_sub]
  rw [show ‖x - y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x - y‖ ^ 2 by ring, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (norm_nonneg _)]

theorem hierarchyCharge_tendsto_of_lift (k : ℕ) (hk : 2 ≤ k) (u : SobolevR (k - 1))
    (v : ℕ → SobolevR (k - 1)) (ψ : ℕ → KSPS.SobolevC (k - 1)) (φ : KSPS.SobolevC (k - 1)) :
    Tendsto v atTop (𝓝 u) →
    (∀ j, KSPS.toPotPair (ψ j) = realSlice (physicalOfSobolev (v j))) →
    KSPS.toPotPair φ = realSlice (physicalOfSobolev u) →
    Tendsto (fun j => hierarchyCharge (ψ j) ⟨k, (by omega), (by omega)⟩) atTop
      (𝓝 (hierarchyCharge φ ⟨k, (by omega), (by omega)⟩)) := by
  intro hv hψ hφ
  have eψ : ∀ j, hierarchyCharge (ψ j) ⟨k, (by omega), (by omega)⟩ =
      hierarchyHamiltonian k (realSlice (physicalOfSobolev (v j))) := by
    intro j
    rw [NlsGge.ThirdConsultation.MOdd.hierarchyCharge_eq_hamiltonian (ψ j) k hk (by omega), hψ j]
  have eφ : hierarchyCharge φ ⟨k, (by omega), (by omega)⟩ =
      hierarchyHamiltonian k (realSlice (physicalOfSobolev u)) := by
    rw [NlsGge.ThirdConsultation.MOdd.hierarchyCharge_eq_hamiltonian φ k hk (by omega), hφ]
  simp only [eψ, eφ]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := g2045b_hamiltonian_continuous k hk _ (pairSobolev_realSlice (k - 1) u) ε hε
  have hδ' : 0 < δ / 2 := by positivity
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 hv) (δ / 2) hδ'
  refine ⟨J, fun j hj => ?_⟩
  rw [dist_eq_norm]
  refine hcont _ (pairSobolev_realSlice (k - 1) (v j)) ?_
  rw [pairSobolevNorm_realSlice_sub]
  have h1 := hJ j hj
  rw [dist_eq_norm] at h1
  have hs : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  nlinarith [norm_nonneg (v j - u), Real.sqrt_nonneg 2]

end NlsGge.ThirdConsultation.M018C
