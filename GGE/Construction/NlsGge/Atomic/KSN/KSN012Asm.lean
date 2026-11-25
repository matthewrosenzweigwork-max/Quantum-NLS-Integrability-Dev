import Mathlib
import NlsGge.Atomic.KSN.KSN013Asm
import NlsGge.Atomic.KSN.KSN004Host

                                                                                      
                                                                                                                      
                                                                                                                     
                                               
                                                                                                      
                                                                                                  
                                                                                  
                                                                                                                  
                                                                                                                
                                                                                                              
                                                                                   
set_option autoImplicit false

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN012L
noncomputable section
open NlsGge.ThirdConsultation.KSN

/-- (ii) local beta + eta data. -/
theorem local_data
    (hbeta : ∀ φ₀ : PotPair, φ₀ ∈ sourceBetaW →
      ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
        ∀ H : ℝ, 0 ≤ H → ∃ A : ℝ, 0 ≤ A ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
          pairPotential 1 (by norm_num) x ∈ O → ∀ n : ℤ,
            ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ A / bracket n ∧
            ‖lamPlus (pairPotential 1 (by norm_num) x) n - lamMinus (pairPotential 1 (by norm_num) x) n‖ +
              ‖muSeq (pairPotential 1 (by norm_num) x) n - tauN (pairPotential 1 (by norm_num) x) n‖ ≤
                A / bracket n)
    (heta : ∀ φ₀ ∈ sourceBetaW, ∃ (U : Set PotPair) (C : ℝ),
      IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧ 0 ≤ C ∧
      ∀ φ ∈ U, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
        ‖eta n a φ - 1‖ ≤ C *
          (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖))
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
      ∀ H : ℝ, 0 ≤ H → ∃ A : ℝ, 0 ≤ A ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
        pairPotential 1 (by norm_num) x ∈ O → ∀ n : ℤ,
          ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ A / bracket n ∧
          ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ A / bracket n := by
  obtain ⟨O, hOo, hφO, hOS, hA⟩ := hbeta φ₀ hφ₀
  obtain ⟨U, Ce, hUo, hφU, -, hCe, hU⟩ := heta φ₀ hφ₀
  refine ⟨O ∩ U, hOo.inter hUo, ⟨hφO, hφU⟩, fun φ hφ => hOS hφ.1, fun H hH => ?_⟩
  obtain ⟨A, hA0, hAb⟩ := hA H hH
  refine ⟨max A (Ce * A), le_trans hA0 (le_max_left _ _), fun x hx hxO n => ?_⟩
  obtain ⟨hb, hm⟩ := hAb x hx hxO.1 n
  have hbr : 0 < bracket n := ksn013_bracket_pos n
  refine ⟨hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) hbr.le), fun a ha => ?_⟩
  refine (hU _ hxO.2 n a ha).trans ?_
  calc Ce * (‖lamPlus (pairPotential 1 (by norm_num) x) n - lamMinus (pairPotential 1 (by norm_num) x) n‖ +
        ‖muSeq (pairPotential 1 (by norm_num) x) n - tauN (pairPotential 1 (by norm_num) x) n‖)
      ≤ Ce * (A / bracket n) := mul_le_mul_of_nonneg_left hm hCe
    _ = Ce * A / bracket n := by ring
    _ ≤ max A (Ce * A) / bracket n := div_le_div_of_nonneg_right (le_max_right _ _) hbr.le

/-- The KSN-012 head conclusion from hbeta and heta (KSN013_of_M032 assembly). -/
theorem KSN012_of
    (hbeta : ∀ φ₀ : PotPair, φ₀ ∈ sourceBetaW →
      ∃ O : Set PotPair, IsOpen O ∧ φ₀ ∈ O ∧ O ⊆ sourceBetaW ∧
        ∀ H : ℝ, 0 ≤ H → ∃ A : ℝ, 0 ≤ A ∧ ∀ x : PairScale 1, ‖x‖ ≤ H →
          pairPotential 1 (by norm_num) x ∈ O → ∀ n : ℤ,
            ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ A / bracket n ∧
            ‖lamPlus (pairPotential 1 (by norm_num) x) n - lamMinus (pairPotential 1 (by norm_num) x) n‖ +
              ‖muSeq (pairPotential 1 (by norm_num) x) n - tauN (pairPotential 1 (by norm_num) x) n‖ ≤
                A / bracket n)
    (heta : ∀ φ₀ ∈ sourceBetaW, ∃ (U : Set PotPair) (C : ℝ),
      IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧ 0 ≤ C ∧
      ∀ φ ∈ U, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
        ‖eta n a φ - 1‖ ≤ C *
          (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖)) :
  (∀ x₀ ∈ complexDomain 1 (by norm_num),
    ∃ (U : Set (PairScale 1)) (C : ℝ), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ complexDomain 1 (by norm_num) ∧ 0 ≤ C ∧
      ∀ x ∈ U, ∀ n : ℤ,
        ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) ∧
  (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : PairScale 1, IsRealPair 1 x → ‖x‖ ≤ B → ∀ n : ℤ,
      ‖betaSum n (pairPotential 1 (by norm_num) x)‖ ≤ C / bracket n ∧
        ∀ a : ℤ, (a = 1 ∨ a = -1) → ‖eta n a (pairPotential 1 (by norm_num) x) - 1‖ ≤ C / bracket n) := by
  have hloc := local_data hbeta heta
  constructor
  · intro x₀ hx₀
    obtain ⟨O, hOo, hφO, hOsub, hA⟩ := hloc (pairPotential 1 (by norm_num) x₀) hx₀
    obtain ⟨A, hA0, hAest⟩ := hA (‖x₀‖ + 1) (by positivity)
    refine ⟨pairPotential 1 (by norm_num) ⁻¹' O ∩ ball x₀ 1, A,
      (hOo.preimage KSN012B2_main).inter isOpen_ball, ⟨hφO, mem_ball_self one_pos⟩,
      fun x hx => hOsub hx.1, hA0, ?_⟩
    intro x hx n
    have hxn : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have h1 := norm_sub_norm_le x x₀
      have h2 := mem_ball_iff_norm.mp hx.2
      linarith
    exact hAest x hxn hx.1 n
  · intro B hB
    obtain ⟨K, hK, hKsub, hKmem⟩ := ksn013_realBall_compact B hB
    have hloc' := fun φ : K => hloc φ.1 (hKsub φ.2)
    choose O hOo hφO hOsub hA using hloc'
    choose A hA0 hAest using fun φ : K => hA φ B hB
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun φ : K => O φ) hOo
      (fun φ hφ => mem_iUnion.mpr ⟨⟨φ, hφ⟩, hφO _⟩)
    refine ⟨∑ φ ∈ t, A φ, Finset.sum_nonneg (fun φ _ => hA0 φ), fun x hxr hx n => ?_⟩
    have hmem := ht (hKmem x hxr hx)
    rw [mem_iUnion₂] at hmem
    obtain ⟨φ, hφt, hφx⟩ := hmem
    obtain ⟨hb, he⟩ := hAest φ x hx hφx n
    have hle : A φ / bracket n ≤ (∑ φ ∈ t, A φ) / bracket n :=
      div_le_div_of_nonneg_right (Finset.single_le_sum (fun φ _ => hA0 φ) hφt) (ksn013_bracket_pos n).le
    exact ⟨hb.trans hle, fun a ha => (he a ha).trans hle⟩

end
end NlsGge.ThirdConsultation.KSN012L
