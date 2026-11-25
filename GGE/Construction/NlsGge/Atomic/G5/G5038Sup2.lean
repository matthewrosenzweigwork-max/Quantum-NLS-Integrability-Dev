import Mathlib
import NlsGge.Atomic.KST.KST066
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.ThirdConsultation.KST.KST066Host

                                                                                                                       
                                                                                                                             
                                                                                                           
                                                                                                        
                                                                                                                              
                                                                                                                             
                                                                                                                           
                                                                                                                        
                                                                                                           
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.Atomic.Common

namespace NlsGge.GKDefinitionDesign

/-- Fourier coefficients of the real-exponent embedding (level-zero instance of the landed
`KST066S.embed_fourierSeq`, reproved here to keep this module's closure small). -/
theorem g5038sup2_embed_fourierSeq (u : PhysicalSobolev38 0) (n : ℤ) :
    fourierSeq38 (physicalSobolevEmbedRealExponent 0 le_rfl u) n =
      carrierCoe38 0 (physicalSobolevFourierEquiv38 0 u) n := by
  unfold fourierSeq38 physicalSobolevEmbedRealExponent
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact congrFun (carrierCoe38_incl38 le_rfl _) n

theorem g5038sup2_sobolevModeWeight_zero (n : ℤ) : sobolevModeWeight 0 n = 1 := by
  simp [sobolevModeWeight]

/-- At level zero the real-exponent embedding preserves norms of differences. -/
theorem g5038sup2_embed_zero_norm_sub (a b : PhysicalSobolev38 0) :
    ‖physicalSobolevEmbedRealExponent 0 le_rfl a - physicalSobolevEmbedRealExponent 0 le_rfl b‖ =
      ‖a - b‖ := by
  set d : SobolevCarrier38 0 := physicalSobolevFourierEquiv38 0 (a - b) with hd
  have hnorm : ‖a - b‖ = ‖d‖ := ((physicalSobolevFourierEquiv38 0).norm_map _).symm
  have hcoe : carrierCoe38 0 d = fourierSeq38 (physicalSobolevEmbedRealExponent 0 le_rfl a -
      physicalSobolevEmbedRealExponent 0 le_rfl b) := by
    funext n
    rw [fourierSeq38_sub, Pi.sub_apply, g5038sup2_embed_fourierSeq, g5038sup2_embed_fourierSeq, hd,
      map_sub]
    rfl
  have hsum := carrier_hasSum_norm_sq38 0 d
  rw [hcoe] at hsum
  simp only [g5038sup2_sobolevModeWeight_zero, one_mul] at hsum
  have hsq : ‖physicalSobolevEmbedRealExponent 0 le_rfl a -
      physicalSobolevEmbedRealExponent 0 le_rfl b‖ ^ 2 = ‖d‖ ^ 2 := by
    rw [norm_sq_eq_tsum_fourierSeq38, hsum.tsum_eq]
  rw [hnorm]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

theorem g5038sup2_embed_zero_isometry :
    Isometry (physicalSobolevEmbedRealExponent 0 le_rfl) :=
  Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, g5038sup2_embed_zero_norm_sub]

theorem g5038sup2_embed_zero_continuous :
    Continuous (physicalSobolevEmbedRealExponent 0 le_rfl) :=
  g5038sup2_embed_zero_isometry.continuous

/-- Level-zero surjectivity: every `L²` field is the embedding of its own Fourier sequence. -/
theorem g5038sup2_embed_zero_surjective :
    Function.Surjective (physicalSobolevEmbedRealExponent 0 le_rfl) := fun u => by
  refine ⟨(physicalSobolevFourierEquiv38 0).symm
    (carrierMk38 0 (fourierSeq38 u) (fourierSeq38_mem_zero u)), ?_⟩
  apply fourierSeq38_injective
  funext n
  rw [g5038sup2_embed_fourierSeq]
  simp

/-- Core transfer: a level-zero Sobolev finite-gap density statement (the finite-gap conjunct of
landed `kst066 0 le_rfl`) gives `L²` finite-gap density. -/
theorem g5038sup2_core
    (hk : ∀ u0 : PhysicalSobolev38 0, ∃ v : ℕ → PhysicalSobolev38 0,
      Tendsto v atTop (𝓝 u0) ∧
      ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (physicalSobolevEmbedRealExponent 0 le_rfl (v j)))
    (u : PhysicalL2) :
    ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧
      ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (v j) := by
  obtain ⟨u0, hu0⟩ := g5038sup2_embed_zero_surjective u
  obtain ⟨w, hw, hfg⟩ := hk u0
  refine ⟨fun j => physicalSobolevEmbedRealExponent 0 le_rfl (w j), ?_, hfg⟩
  rw [← hu0]
  exact (g5038sup2_embed_zero_continuous.tendsto u0).comp hw

theorem finiteGap_seq_tendsto (u : PhysicalL2) :
  ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧
    ∀ j : ℕ, NlsGge.ThirdConsultation.finiteGap (v j) :=
  g5038sup2_core (fun u0 => by
    obtain ⟨w, hw, hfg⟩ := NlsGge.ThirdConsultation.KST.kst066 0 le_rfl u0
    exact ⟨w, hw, fun j => (hfg j).1⟩) u

end NlsGge.GKDefinitionDesign
end
