import Mathlib
import NlsGge.Atomic.G4.G4017

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.KSN008Sup1
noncomputable section

theorem sheetSign_collapse_facts
    (n : ℤ) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW)
    (hγ : gamma2 φ₀ n = 0) (hμ : muSeq φ₀ n ≠ tauN φ₀ n) :
    canonRoot38 φ₀ (muSeq φ₀ n) ≠ 0 ∧
    (sheetSign n φ₀ = 1 ∨ sheetSign n φ₀ = -1) ∧
    ∃ U : Set PotPair, IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧
      ∀ φ ∈ U, gamma2 φ n = 0 → sheetSign n φ = sheetSign n φ₀ := by
  have hgk : φ₀ ∈ gkW := G4017Aux.sourceBetaW_gkW hφ₀
  have hEnds : lamPlus φ₀ n = lamMinus φ₀ n := by
    have h := gamma2_value38 φ₀ hgk n
    rw [h] at hγ
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hγ)
  have hTau : tauN φ₀ n = lamMinus φ₀ n := by
    rw [tauN_value38 φ₀ hgk n, hEnds]
    ring
  have hμoff : muSeq φ₀ n ∉ gapSegment φ₀ n := by
    change muSeq φ₀ n ∉ segment ℝ (lamMinus φ₀ n) (lamPlus φ₀ n)
    rw [hEnds, segment_same, Set.mem_singleton_iff]
    intro hm
    exact hμ (hm.trans hTau.symm)
  have hoff : φ₀ ∈ offGapSet n := ⟨hφ₀, hμoff⟩
  obtain ⟨hroot, hsign, hloc⟩ := (G4017 n).2.2.2 φ₀ hoff
  obtain ⟨V, hV, hVoff, hconst⟩ := hloc
  obtain ⟨U, hUV, hUopen, hUφ⟩ := mem_nhds_iff.mp hV
  refine ⟨hroot, hsign, U, hUopen, hUφ, ?_, ?_⟩
  · intro φ hφ
    exact (hVoff (hUV hφ)).1
  · intro φ hφ hγφ
    exact hconst φ (hUV hφ)

end
end NlsGge.Atomic.KSN008Sup1
