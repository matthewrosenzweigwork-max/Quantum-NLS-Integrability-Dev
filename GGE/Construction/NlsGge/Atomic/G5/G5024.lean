import Mathlib
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.Lib.EntireProductsC34h
import NlsGge.GK38.DirichletL2
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                                                 
                                                                                                                                                
                                                                                                
                                                                                                                                                  
                                                                                   
                                                                                                                                                      
                                                     
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def psiAt (n : ℤ) (z : ℂ) (φ : PotPair) : ℂ :=
  p6PsiNumerator38 n (sourceF n) φ z

def CircleRatioTendstoZero (f g : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ R : ℕ, N ≤ R →
    ∀ z : ℂ, ‖z‖ = (R : ℝ) * Real.pi + Real.pi / 2 → ‖f z‖ ≤ ε * ‖g z‖

theorem G5024_gen (F : (n : ℤ) → PotPair → P2Space38 n) (n : ℤ) (u : PhysicalL2) :
  CircleRatioTendstoZero (fun z => p6PsiNumerator38 n (F n) (realSlice u) z) Complex.sin ∧
  Function.Injective (fun m : ℤ => muSeq (realSlice u) m) ∧
  Memℓp (fun m : ℤ => muSeq (realSlice u) m - (m : ℂ) * Real.pi) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have hrep : ∀ z : ℂ, p6PsiNumerator38 n (F n) (realSlice u) z =
        (-2 : ℂ) * Lib.omitProd n (p2Extend38 n (F n (realSlice u))) z := fun z => rfl
    obtain ⟨N, hN⟩ := Lib.omitProd_circle_decay n (p2Extend38 n (F n (realSlice u))) (ε / 2) (by positivity)
    refine ⟨N, fun R hR z hz => ?_⟩
    show ‖p6PsiNumerator38 n (F n) (realSlice u) z‖ ≤ ε * ‖Complex.sin z‖
    rw [hrep, norm_mul]
    have h := hN R hR z hz
    have h2 : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [h2]
    nlinarith [h, norm_nonneg (Complex.sin z)]
  · intro m k hmk
    have hocc := muSeq_occurrence38 (realSlice u) (muSeq (realSlice u) m)
    have hsimp := muSeq_simple38 u m
    have h1 : Set.encard {j : ℤ | muSeq (realSlice u) j = muSeq (realSlice u) m} = 1 := by
      rw [hocc.2, hsimp]
    obtain ⟨x, hx⟩ := Set.encard_eq_one.1 h1
    have hm : m ∈ {j : ℤ | muSeq (realSlice u) j = muSeq (realSlice u) m} := rfl
    have hk : k ∈ {j : ℤ | muSeq (realSlice u) j = muSeq (realSlice u) m} := hmk.symm
    rw [hx] at hm hk
    rw [Set.mem_singleton_iff] at hm hk
    rw [hm, hk]
  · have hs := muSeq_summable38 (realSlice u)
    rw [memℓp_gen_iff (by simp)]
    simpa using hs


theorem G5024 (n : ℤ) (u : PhysicalL2) :
  CircleRatioTendstoZero (fun z => psiAt n z (realSlice u)) Complex.sin ∧
  Function.Injective (fun m : ℤ => muSeq (realSlice u) m) ∧
  Memℓp (fun m : ℤ => muSeq (realSlice u) m - (m : ℂ) * Real.pi) 2 :=
  G5024_gen sourceF n u

end
end NlsGge.GKDefinitionDesign
