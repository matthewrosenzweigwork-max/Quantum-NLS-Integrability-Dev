import Mathlib
import NlsGge.Atomic.G3.G3023
import NlsGge.Atomic.G3.G3027
import NlsGge.Atomic.G3.G3006
import NlsGge.Atomic.G4.G4011
import NlsGge.ThirdConsultation.G3.G3026Support

                                                                                      
                                                                           
                                                                                                                                   
                                                                              
                                                                                                                                    
                                                                                                                  
                                                                                                                                   
                                                                  
                                                                                                       
                                                                                                                                        
                                                                      
                                                                                                                                
                                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G3031Aux
noncomputable section

theorem summable_norm_offDiagonalBeta (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) :
    Summable (fun m : ℤ => ‖offDiagonalBeta n m φ‖) := by
  have hφW : φ ∈ sourceW := sourceFamily.V_W hφ
  obtain ⟨hsum, -⟩ := sourceFamily.beta_spec n ⟨φ, hφW⟩ hφ
  have e : (fun m : P2Index38 n => ‖offDiagonalBeta n m.1 φ‖) =
      fun m : P2Index38 n =>
        ‖gkSourceBeta38 sourceFamily.W sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceFamily.F sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m.1 m.2 ⟨φ, hφW⟩‖ :=
    funext fun m => congrArg norm
      (gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m.1 m.2 ⟨φ, hφW⟩)
  have key : Summable (fun m : P2Index38 n => ‖offDiagonalBeta n m.1 φ‖) := by
    rw [e]
    exact hsum
  have hzero : ∀ x : ℤ, x ∉ Set.range (Subtype.val : P2Index38 n → ℤ) →
      ‖offDiagonalBeta n x φ‖ = 0 := by
    intro x hx
    have hxn : x = n := by
      by_contra h
      exact hx ⟨⟨x, h⟩, rfl⟩
    rw [hxn, offDiagonalBeta_diag n φ, norm_zero]
  exact (Subtype.val_injective.summable_iff hzero).mp key

theorem analyticOnNhd_betaPartialSum (n : ℤ) (R : ℕ) :
    AnalyticOnNhd ℂ (betaPartialSum n R) sourceW := by
  have h : betaPartialSum n R =
      fun φ : PotPair => ∑ m ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), offDiagonalBeta n m φ :=
    funext fun φ => rfl
  rw [h]
  refine Finset.analyticOnNhd_fun_sum (𝕜 := ℂ) (f := fun m => offDiagonalBeta n m) _ fun m _ => ?_
  by_cases hmn : m = n
  · subst hmn
    have h0 : offDiagonalBeta m m = fun _ => (0 : ℂ) :=
      funext fun φ => offDiagonalBeta_diag m φ
    rw [h0]
    exact analyticOnNhd_const
  · exact (G3_023 n m hmn).1

theorem im_betaSum_realSlice (n : ℤ) (u : PhysicalL2) :
    (betaSum n (realSlice u)).im = 0 := by
  have hV : realSlice u ∈ sourceBetaW := sourceFamily.V_real (mem_range_self u)
  have hs := hasSum_offDiagonalBeta_betaSum n (realSlice u) hV
  rw [Complex.hasSum_iff] at hs
  have him : (fun m : ℤ => (offDiagonalBeta n m (realSlice u)).im) = fun _ => (0 : ℝ) := by
    funext m
    by_cases hmn : m = n
    · subst hmn
      rw [offDiagonalBeta_diag]
      simp
    · exact (G3_006 u).1 n m hmn
  have h2 := hs.2
  change HasSum (fun m : ℤ => (offDiagonalBeta n m (realSlice u)).im) (betaSum n (realSlice u)).im at h2
  rw [him] at h2
  exact h2.unique hasSum_zero

end
end G3031Aux

noncomputable section

theorem G3_031 :
  ∃ U : Set PotPair, IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ sourceBetaW ∧
    ∀ n : ℤ,
      AnalyticOnNhd ℂ (betaSum n) U ∧
      (∀ φ ∈ U, Summable (fun m : ℤ => ‖offDiagonalBeta n m φ‖) ∧
        HasSum (fun m : ℤ => offDiagonalBeta n m φ) (betaSum n φ)) ∧
      ∀ u : PhysicalL2, (betaSum n (realSlice u)).im = 0 := by
  obtain ⟨U, hUo, hUr, hUsub, hlim, -⟩ := G3_027
  refine ⟨U, hUo, hUr, hUsub, fun n => ⟨?_, fun φ hφ => ⟨?_, ?_⟩, fun u => ?_⟩⟩
  · exact NlsGge.Atomic.G4.analyticOnNhd_of_locally_uniform_limit hUo
      (f := betaPartialSum n) (g := betaSum n)
      (fun R => (G3031Aux.analyticOnNhd_betaPartialSum n R).mono
        (fun φ hφ => sourceFamily.V_W (hUsub hφ)))
      (hlim n)
  · exact G3031Aux.summable_norm_offDiagonalBeta n φ (hUsub hφ)
  · exact hasSum_offDiagonalBeta_betaSum n φ (hUsub hφ)
  · exact G3031Aux.im_betaSum_realSlice n u

end
end NlsGge.GKDefinitionDesign
