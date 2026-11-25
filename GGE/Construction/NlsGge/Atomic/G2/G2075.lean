import Mathlib
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2074
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.Lib.EntireProductsParamd

                                                                                                    
                                                                                                     
                                                                           
                                                                                             
                                                                                              
                                                                                                                  
                                                                                                
                                                                                             
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open SummationFilter
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g2075_root_eq_sigma (n m : ℤ) (φ : PotPair) (hmn : m ≠ n) :
    normalizedRoot n m φ = Lib.sigmaOf (p2Extend38 n (sourceF n φ)) m := by
  have h : p2Extend38 n (sourceF n φ) m = sourceF n φ (⟨m, hmn⟩ : P2Index38 n) :=
    p2Extend_at38 n _ ⟨m, hmn⟩
  rw [normalizedRoot, dif_pos hmn, Lib.sigmaOf, countingCenter38, h]

theorem g2075_term (n : ℤ) (φ : PotPair) (z : ℂ) (m : ℤ) :
    (if m = n then (1 : ℂ) else (normalizedRoot n m φ - z) / (Lib.piN m : ℂ)) =
      if m = n then (1 : ℂ) else Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n φ))) z m := by
  by_cases hm : m = n
  · simp only [if_pos hm]
  · simp only [if_neg hm, g2075_root_eq_sigma n m φ hm, Lib.prodFactor]

theorem g2075_fun_eq (n : ℤ) (φ : PotPair) (z : ℂ) :
    (fun m : ℤ => if m = n then (1 : ℂ) else (normalizedRoot n m φ - z) / (Lib.piN m : ℂ)) =
      fun m : ℤ => if m = n then (1 : ℂ) else
        Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n φ))) z m :=
  funext fun m => g2075_term n φ z m

theorem g2075_psi_eq_omit (n : ℤ) (φ : PotPair) (z : ℂ) :
    psi n φ z = -2 * Lib.omitProd n (p2Extend38 n (sourceF n φ)) z :=
  rfl

theorem g2075_psi_sigma (n : ℤ) (φ : PotPair) (z : ℂ) :
    psi n φ z = (-2 / (Lib.piN n : ℂ)) * ∏'[symmetricIcc ℤ] m : ℤ,
      (if m = n then (1 : ℂ) else Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n φ))) z m) := by
  rw [g2075_psi_eq_omit, Lib.omitProd]
  ring

theorem g2075_psi_prod (n : ℤ) (φ : PotPair) (z : ℂ) :
    psi n φ z = (-2 / (Lib.piN n : ℂ)) * ∏'[symmetricIcc ℤ] m : ℤ,
      (if m = n then (1 : ℂ) else (normalizedRoot n m φ - z) / (Lib.piN m : ℂ)) := by
  rw [g2075_psi_sigma, g2075_fun_eq n φ z]

theorem g2075_zero (n : ℤ) (φ : PotPair) (z : ℂ) :
    psi n φ z = 0 ↔ ∃ m : P2Index38 n, normalizedRoot n m.1 φ = z := by
  rw [g2075_psi_eq_omit, mul_eq_zero, or_iff_right (by norm_num : (-2 : ℂ) ≠ 0),
    Lib.omitProd_eq_zero_iff]
  constructor
  · rintro ⟨m, hm, hz⟩
    exact ⟨⟨m, hm⟩, (g2075_root_eq_sigma n m φ hm).trans hz⟩
  · rintro ⟨m, hz⟩
    exact ⟨m.1, m.2, (g2075_root_eq_sigma n m.1 φ m.2).symm.trans hz⟩

theorem g2075_tendsto (n : ℤ) (φ : PotPair) (z : ℂ) :
    Tendsto (fun N : ℕ => (-2 / (Lib.piN n : ℂ)) *
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = n then (1 : ℂ) else (normalizedRoot n m φ - z) / (Lib.piN m : ℂ)))
      atTop (𝓝 (psi n φ z)) := by
  have hfn : (fun N : ℕ => (-2 / (Lib.piN n : ℂ)) *
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = n then (1 : ℂ) else (normalizedRoot n m φ - z) / (Lib.piN m : ℂ))) =
      (fun N : ℕ => (-2 / (Lib.piN n : ℂ)) *
        ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = n then (1 : ℂ) else
            Lib.prodFactor (Lib.sigmaOf (p2Extend38 n (sourceF n φ))) z m)) := by
    funext N
    congr 1
    exact Finset.prod_congr rfl (fun m _ => g2075_term n φ z m)
  have hHas := SummationFilter.hasProd_symmetricIcc_iff.mp
    (Lib.multipliable_omit n (p2Extend38 n (sourceF n φ)) z).hasProd
  have hT := hHas.const_mul (-2 / (Lib.piN n : ℂ))
  rw [hfn, g2075_psi_sigma]
  exact hT

theorem g2075_periods (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) (m : ℤ) :
    CircleIntegrable (fun z => psi n φ z / canonRoot38 φ z) (discC φ m) (discR φ m) ∧
    abelianPeriod38 m φ (psi n φ) = if m = n then 2 * (Real.pi : ℂ) else 0 :=
  ⟨(p6PsiNumerator_integrable_and_off_diagonal_periods38 n φ (sourceFamily.W_gk hφ)
      (sourceF n) (sourceFamily.F_zero n φ hφ)).1 m,
    sourceFamily.F_period n φ hφ m⟩

theorem g2075_gap (u : PhysicalL2) (n m : ℤ) (hmn : m ≠ n) :
    normalizedRoot n m (realSlice u) ∈ gapSegment (realSlice u) m := by
  obtain ⟨t, ht, _, hFt⟩ := sourceFamily.F_real n u
  have hall : ∀ k : P2Index38 n, countingCenter38 k.1 + ((t k : ℝ) : ℂ) ∈
      segment ℝ (lamMinus (realSlice u) k.1) (lamPlus (realSlice u) k.1) := ht
  have he : sourceF n (realSlice u) (⟨m, hmn⟩ : P2Index38 n) = ((t ⟨m, hmn⟩ : ℝ) : ℂ) := by
    rw [show sourceF n (realSlice u) = p3RealInclude38 n t from hFt]
    exact p3RealInclude_apply38 n t ⟨m, hmn⟩
  rw [normalizedRoot, dif_pos hmn, he]
  exact hall ⟨m, hmn⟩

theorem G2_075 :
    IsOpen sourceW ∧ Set.range realSlice ⊆ sourceW ∧ sourceW ⊆ gkW ∧
    (∀ n : ℤ,
      AnalyticOnNhd ℂ (fun p : PotPair × ℂ => psi n p.1 p.2)
        (sourceW ×ˢ (Set.univ : Set ℂ))) ∧
    (∀ n : ℤ, ∀ φ ∈ sourceW,
      AnalyticOnNhd ℂ (psi n φ) Set.univ ∧
      (∀ m : ℤ,
        CircleIntegrable (fun z => psi n φ z/canonRoot38 φ z) (discC φ m) (discR φ m) ∧
        abelianPeriod38 m φ (psi n φ)=if m=n then 2*(Real.pi : ℂ) else 0) ∧
      (∀ z : ℂ, psi n φ z=0 ↔
        ∃ m : P2Index38 n, normalizedRoot n m.1 φ=z) ∧
      (∀ z : ℂ,
        Tendsto (fun N : ℕ => (-2/(Lib.piN n : ℂ))*
          ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            if m=n then (1 : ℂ) else
              (normalizedRoot n m φ-z)/(Lib.piN m : ℂ))
          atTop (𝓝 (psi n φ z))) ∧
      (∀ z : ℂ, psi n φ z=(-2/(Lib.piN n : ℂ))*
        ∏'[symmetricIcc ℤ] m : ℤ,
          if m=n then 1 else (normalizedRoot n m φ-z)/(Lib.piN m : ℂ))) ∧
    (∀ u : PhysicalL2, ∀ n m : ℤ, m ≠ n →
      normalizedRoot n m (realSlice u) ∈ gapSegment (realSlice u) m) ∧
    (∀ φ₀ ∈ sourceW,
      ∃ V : Set PotPair, IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ sourceW ∧
        ∃ B : ℝ, 0 < B ∧ ∀ φ ∈ V, ∀ n : ℤ, ∃ A : P2Space38 n,
          (∀ m : P2Index38 n,
            normalizedRoot n m.1 φ=tauN φ m.1+gamma2 φ m.1*A m) ∧
          Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
          (∑' m : P2Index38 n, ‖A m‖^2) ≤ B)
 := by
  refine ⟨sourceFamily.W_open, sourceFamily.W_real, sourceFamily.W_gk,
    fun n => p6PsiNumerator_joint_analytic38 n sourceW (sourceF n) (sourceFamily.F_analytic n),
    fun n φ hφ => ⟨p6PsiNumerator_entire38 n (sourceF n) φ,
      fun m => g2075_periods n φ hφ m,
      fun z => g2075_zero n φ z,
      fun z => g2075_tendsto n φ z,
      fun z => g2075_psi_prod n φ z⟩,
    fun u n m hmn => g2075_gap u n m hmn,
    fun φ₀ hφ₀ => G2_074 φ₀ hφ₀⟩

end
end NlsGge.GKDefinitionDesign
