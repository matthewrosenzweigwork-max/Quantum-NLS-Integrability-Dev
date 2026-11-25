import Mathlib
import NlsGge.Atomic.I.I022Core
import NlsGge.Birkhoff.H02Hierarchy38

                                                                                                                 
                                                                                  
                                                                                                                      
                                                                                                                
                                                                                                                         
                                                                                                                       
                                                                                                                        
                                                                                                                       
                                                 
                                                                                                        
                                                                                                               
                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I040C

theorem tendsto_hier (Bk : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c)
    (r : ℕ) :
    Tendsto (fun k : ℕ => physFS38 r (Bk.cleanΦinv (zHier38 c (k + (r + 2)) g))) atTop
      (𝓝 (physFS38 r (Bk.cleanΦinv (zFull38 c g)))) := by
  have h := (((continuous_physFS_comp38 r).comp (Bk.continuous_TinvC r)).tendsto _).comp
    (tendsto_carrier_scale38 lower upper c hlower hbound hupper hg r)
  rw [NlsGge.ThirdConsultation.I022C.physFS_eq, Bk.cleanTinvC_of_mem r _
    (zFull38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg r)]
  refine h.congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [NlsGge.ThirdConsultation.I022C.physFS_eq, Bk.cleanTinvC_of_mem r _
    (zHier38_mem_seqSobolev38_nat lower upper c hlower hbound hupper hg (by omega))]

theorem tendsto_hier_from (Bk : BirkhoffTop38) (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) {g : ℤ → ℂ} (hg : g ∈ Omega1_38 c)
    (r m₀ : ℕ) :
    Tendsto (fun k : ℕ => physFS38 r (Bk.cleanΦinv (zHier38 c (m₀ + k) g))) atTop
      (𝓝 (physFS38 r (Bk.cleanΦinv (zFull38 c g)))) := by
  rw [← tendsto_add_atTop_iff_nat (r + 2)]
  have h := (tendsto_hier Bk lower upper c hlower hbound hupper hg r).comp
    (tendsto_add_atTop_nat m₀)
  refine h.congr (fun k => ?_)
  simp only [Function.comp_apply]
  have e : k + m₀ + (r + 2) = m₀ + (k + (r + 2)) := by omega
  rw [e]

theorem i040_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∀ g ∈ Omega1_38 c.val,
      (∀ (r m₀ : ℕ), max 2 (r + 1) ≤ m₀ →
        SobolevSquareSummable (r : ℝ) (physicalFourier (physicalOfSequence (zFull38 c.val g))) ∧
        (∀ m : ℕ, m₀ ≤ m → SobolevSquareSummable (r : ℝ)
          (physicalFourier (physicalOfSequence (zHier38 c.val m g)))) ∧
        Tendsto (fun k : ℕ => physFS38 r (physicalOfSequence (zHier38 c.val (m₀ + k) g)))
          atTop (𝓝 (physFS38 r (physicalOfSequence (zFull38 c.val g))))) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ‖physFS38 1 (physicalOfSequence (zFull38 c.val g))‖ ≤ B ∧
        ∀ m : ℕ, 2 ≤ m → ‖physFS38 1 (physicalOfSequence (zHier38 c.val m g))‖ ≤ B := by
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  intro g hg
  refine ⟨fun r m₀ hm => ⟨?_, fun m hm' => ?_, ?_⟩, ?_⟩
  · rw [← hB]
    exact Bk.sobolev_cleanΦinv38 r _ (zFull38_mem_seqSobolev38_nat lower upper c.val hl hb' hu' hg r)
  · have h2 : 2 ≤ m := (le_max_left _ _).trans (hm.trans hm')
    have h3 : r + 1 ≤ m := (le_max_right _ _).trans (hm.trans hm')
    rw [← hB]
    exact Bk.sobolev_cleanΦinv38 r _ (seqSobolev38_mono (by exact_mod_cast (by omega : r ≤ m - 1))
      (zHier38_mem_seqSobolev38 lower upper c.val hl hb' hu' hg h2))
  · simpa only [hB] using tendsto_hier_from Bk lower upper c.val hl hb' hu' hg r m₀
  · have ht := (tendsto_hier_from Bk lower upper c.val hl hb' hu' hg 1 2).norm
    simp only [hB] at ht
    obtain ⟨M, hM⟩ := ht.bddAbove_range
    refine ⟨max M ‖physFS38 1 (physicalOfSequence (zFull38 c.val g))‖,
      (norm_nonneg _).trans (le_max_right _ _), le_max_right _ _, fun m hm => ?_⟩
    have hk := hM (Set.mem_range_self (m - 2))
    simp only [Nat.add_sub_cancel' hm] at hk
    exact hk.trans (le_max_left _ _)

end NlsGge.ThirdConsultation.I040C
