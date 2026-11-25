import Mathlib
import NlsGge.Atomic.KSN.KSN013Asm
import NlsGge.Atomic.KSN.KSN014Core

                                                                                              
                                                                                                                  
                                                                                                  
                                                                                              
                                                                                                             
                                                                                                                     
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- The KSN-014 head, conditional only on the landed M-032 conclusion. -/
theorem KSN014_of_M032
    (hM032 : ∀ (w : ℤ → ℝ), NlsGge.ThirdConsultation.M.OneDerivativeWeight w → ∀ (N : ℕ) (φ : PotPair),
      φ ∈ gkW → NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight (N : ℤ) →
      NlsGge.ThirdConsultation.MTwoMode.complexGapTailEnergy w φ N ≤
        6 * NlsGge.ThirdConsultation.MTwoMode.potentialTailEnergy w φ N +
        ENNReal.ofReal (1152 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 6 /
          NlsGge.Atomic.M.M054.indexWeight (N : ℤ))) :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      ‖xiN38 n (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) := by
  have hgap := ksn013_gap_high hM032
  constructor
  · intro x₀ hx₀
    obtain ⟨O, hOo, hφO, hOsub, C, R, c, J, hgeom, hspec, hbd⟩ :=
      ksn013_local_bounds hgap (pairPotential 1 (by norm_num) x₀) hx₀
    obtain ⟨Aa, Γ, hbx⟩ := hbd (‖x₀‖ + 1) (by positivity)
    obtain ⟨C1, hC1, hxi⟩ := ksn014_xi_estimate C R c J hgeom Aa Γ
    refine ⟨pairPotential 1 (by norm_num) ⁻¹' O ∩ ball x₀ 1, C1,
      (hOo.preimage KSN012B2_main).inter isOpen_ball, ⟨hφO, mem_ball_self one_pos⟩,
      fun x hx => hOsub hx.1, hC1, ?_⟩
    intro x hx n
    have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 := norm_sub_norm_le x x₀
      have h2 := mem_ball_iff_norm.mp hx.2
      linarith
    obtain ⟨ha, hΓk⟩ := hbx x hxn hx.1
    refine (hxi _ (ksn013_sourceBetaW_gkW (hOsub hx.1)) (hspec _ hx.1) ha hΓk n).trans ?_
    exact div_le_div_of_nonneg_left hC1 (ksn013_bracket_pos n) (ksn013_bracket_le_japanese n)
  · intro B hB
    obtain ⟨K, hK, hKsub, hKmem⟩ := ksn013_realBall_compact B hB
    have hloc := fun φ : K => ksn013_local_bounds hgap φ.1 (hKsub φ.2)
    choose O hOo hφO hOsub C R c J hgeom hspec hbd using hloc
    choose Aa Γ hbx using fun φ : K => hbd φ B hB
    choose C1 hC1 hxi using fun φ : K => ksn014_xi_estimate (C φ) (R φ) (c φ) (J φ) (hgeom φ) (Aa φ) (Γ φ)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun φ : K => O φ) hOo
      (fun φ hφ => mem_iUnion.mpr ⟨⟨φ, hφ⟩, hφO _⟩)
    refine ⟨∑ φ ∈ t, C1 φ, Finset.sum_nonneg (fun φ _ => hC1 φ), ?_⟩
    intro x hxr hx n
    have hmem := ht (hKmem x hxr hx)
    rw [mem_iUnion₂] at hmem
    obtain ⟨φ, hφt, hφx⟩ := hmem
    obtain ⟨ha, hΓk⟩ := hbx φ x hx hφx
    refine (hxi φ _ (ksn013_sourceBetaW_gkW (hOsub φ hφx)) (hspec φ _ hφx) ha hΓk n).trans ?_
    refine (div_le_div_of_nonneg_left (hC1 φ) (ksn013_bracket_pos n) (ksn013_bracket_le_japanese n)).trans ?_
    exact div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun φ _ => hC1 φ) hφt) (ksn013_bracket_pos n).le

end
end NlsGge.ThirdConsultation.KSN
