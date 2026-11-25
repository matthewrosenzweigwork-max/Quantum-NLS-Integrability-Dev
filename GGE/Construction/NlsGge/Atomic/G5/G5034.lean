import Mathlib
import NlsGge.Atomic.G5.G5033
import NlsGge.Atomic.G5.G5024
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5.G5034Support1
import NlsGge.GK38.Lib.InterpolationHilbertOp
-- MODULE: NlsGge.Atomic.G5.G5034

                                                                                                             
                                                                                                                    
                                                                                                                
                                         
                                             
                                                                                                                       
                                                                                                             
                                                                                                                   
                                                                        
                                                                                                              
                                                
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5034 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) :
  CircleRatioTendstoZero
    (fun z => pairPoissonCLM (fderiv ℂ (psiAt n z) (realSlice u))
      (angleDerivative m (realSlice u))) Complex.sin := by
  intro ε hε
  -- Root shifts t_k = (p2Extend38 n (sourceF n φ)) k, with σ_k = psiRootAt n k φ = kπ + t_k.
  have ht : Summable fun k : ℤ => ‖(p2Extend38 n (sourceF n (realSlice u))) k‖ ^ 2 :=
    Lib.summable_sq_lp _
  have hT : ∀ k : ℤ, ‖(p2Extend38 n (sourceF n (realSlice u))) k‖ ≤
      ‖p2Extend38 n (sourceF n (realSlice u))‖ :=
    fun k => lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) _ k
  have hσ : ∀ k : ℤ, psiRootAt n k (realSlice u) =
      (k : ℂ) * (Real.pi : ℂ) + (p2Extend38 n (sourceF n (realSlice u))) k :=
    fun k => rfl
  obtain ⟨N₁, hav⟩ := NlsGge.ThirdConsultation.G5034Support1.circle_tail_avoid
    (fun k => psiRootAt n k (realSlice u)) (fun k => (p2Extend38 n (sourceF n (realSlice u))) k)
    hσ _ hT ht
  -- The coefficient family, in ℓ², from G5-033 at one avoiding circle point.
  have hz0n : ‖(((N₁ : ℝ) * Real.pi + Real.pi / 2 : ℝ) : ℂ)‖ =
      (N₁ : ℝ) * Real.pi + Real.pi / 2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hz0 := hav N₁ le_rfl _ hz0n
  obtain ⟨hmem, -, -⟩ := G5033 u m n hm _ (fun k _ => hz0 k)
  have hb : Summable fun k : ℤ => ‖(if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))‖ ^ 2 := by
    have := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp hmem
    simpa using this
  obtain ⟨N₂, B, hbd⟩ := NlsGge.ThirdConsultation.G5034Support1.circle_tail_bound
    (fun k => psiRootAt n k (realSlice u)) (fun k => (p2Extend38 n (sourceF n (realSlice u))) k)
    (fun k => if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
    hσ _ hT ht hb
  obtain ⟨N₃, hN₃⟩ := (G5024 n u).1 (ε / (|B| + 1)) (div_pos hε (by positivity))
  refine ⟨max (max N₁ N₂) N₃, fun R hR z hzR => ?_⟩
  have h1 : N₁ ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have h2 : N₂ ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have h3 : N₃ ≤ R := (le_max_right _ _).trans hR
  have hzk : ∀ k : ℤ, z ≠ psiRootAt n k (realSlice u) := hav R h1 z hzR
  obtain ⟨-, -, hid⟩ := G5033 u m n hm z (fun k _ => hzk k)
  have hsum : (∑' k : ℤ, if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)) /
        (psiRootAt n k (realSlice u) - z)) =
      ∑' k : ℤ, (if k = n then (0 : ℂ) else
        pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
        / (psiRootAt n k (realSlice u) - z) := by
    congr 1
    funext k
    by_cases hk : k = n <;> simp [hk]
  have hbound : ‖∑' k : ℤ, (if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
      / (psiRootAt n k (realSlice u) - z)‖ ≤ B := hbd R h2 z hzR
  have hpsi : ‖psiAt n z (realSlice u)‖ ≤ ε / (|B| + 1) * ‖Complex.sin z‖ := hN₃ R h3 z hzR
  show ‖pairPoissonCLM (fderiv ℂ (psiAt n z) (realSlice u)) (angleDerivative m (realSlice u))‖ ≤
    ε * ‖Complex.sin z‖
  rw [hid, norm_mul]
  rw [hsum] at *
  have hS0 : 0 ≤ ‖∑' k : ℤ, (if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
      / (psiRootAt n k (realSlice u) - z)‖ := norm_nonneg _
  have hSB : ‖∑' k : ℤ, (if k = n then (0 : ℂ) else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
      / (psiRootAt n k (realSlice u) - z)‖ ≤ |B| := hbound.trans (le_abs_self B)
  have hsin : 0 ≤ ‖Complex.sin z‖ := norm_nonneg _
  have hden : 0 < |B| + 1 := by positivity
  have hkey : ε / (|B| + 1) * |B| ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [abs_nonneg B]
  calc ‖psiAt n z (realSlice u)‖ * ‖∑' k : ℤ, (if k = n then (0 : ℂ) else
        pairPoissonCLM (fderiv ℂ (psiRootAt n k) (realSlice u)) (angleDerivative m (realSlice u)))
        / (psiRootAt n k (realSlice u) - z)‖
      ≤ (ε / (|B| + 1) * ‖Complex.sin z‖) * |B| :=
        mul_le_mul hpsi hSB hS0 (mul_nonneg (div_nonneg hε.le hden.le) hsin)
    _ = (ε / (|B| + 1) * |B|) * ‖Complex.sin z‖ := by ring
    _ ≤ ε * ‖Complex.sin z‖ := mul_le_mul_of_nonneg_right hkey hsin

end
end NlsGge.GKDefinitionDesign
