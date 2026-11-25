import Mathlib
import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.CountingLemmaGeometry
import NlsGge.GK38.Lib.EntireProductsParama
import NlsGge.GK38.AbelianPeriods
import NlsGge.GK38.AbelianPsiNumerator
import NlsGge.GK38.AbelianNumeratorVariation
import NlsGge.Atomic.G2.G2055

                                                                                                                  
                                                                                                      
                                                 
                                                                                                     
                                                                                        
                                                                                                        
                                                                                                         
set_option autoImplicit false

open Set Filter Topology
open NlsGge.GK38

namespace NlsGge.ThirdConsultation.G5033Support1
noncomputable section

/-- The sigma coordinate of the extended root at an omitted-free index is k π + s_k. -/
theorem sigmaOf_ext_eq (n : ℤ) (s : P2Space38 n) (k : ℤ) (hk : k ≠ n) :
    Lib.sigmaOf (p2Extend38 n s) k = countingCenter38 k + s ⟨k, hk⟩ := by
  have h : p2Extend38 n s k = s ⟨k, hk⟩ := p2Extend_at38 n s ⟨k, hk⟩
  simp [Lib.sigmaOf, countingCenter38, h]

/-- Fréchet derivative of one sigma coordinate: the k-th coordinate of the derivative of the root map. -/
theorem fderiv_sigma_coord (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair)
    (hF : DifferentiableAt ℂ F φ) (k : ℤ) (hk : k ≠ n) (H : PotPair) :
    fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H = fderiv ℂ F φ H ⟨k, hk⟩ := by
  have hev : HasFDerivAt (fun ψ => F ψ ⟨k, hk⟩)
      ((lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 ⟨k, hk⟩).comp (fderiv ℂ F φ)) φ :=
    (lp.evalCLM ℂ (fun _ : P2Index38 n => ℂ) 2 ⟨k, hk⟩).hasFDerivAt.comp φ hF.hasFDerivAt
  have hfun : (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) =
      fun ψ => countingCenter38 k + F ψ ⟨k, hk⟩ := by
    funext ψ
    exact sigmaOf_ext_eq n (F ψ) k hk
  rw [hfun, (hev.const_add (countingCenter38 k)).fderiv]
  rfl

/-- Chain rule for the entire numerator: the derivative of φ ↦ p2Numerator(F φ)(z) in direction H
is the landed-variation p4NumeratorVariation38 at the extended root, in the extended direction. -/
theorem fderiv_psiNumerator (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair)
    (hF : DifferentiableAt ℂ F φ) (z : ℂ) (H : PotPair) :
    fderiv ℂ (fun ψ => p6PsiNumerator38 n F ψ z) φ H =
      p4NumeratorVariation38 n (p2Extend38 n (F φ)) (p2Extend38 n (fderiv ℂ F φ H)) z := by
  have hΦ : DifferentiableAt ℂ (fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1)
      (z, p2Extend38 n (F φ)) :=
    ((p2FullNumerator_joint_analytic38 n) (z, p2Extend38 n (F φ)) (mem_univ _)).differentiableAt
  have hg : HasFDerivAt (fun ψ => (z, p2Extend38 n (F ψ)))
      ((0 : PotPair →L[ℂ] ℂ).prod ((p2Extend38 n).comp (fderiv ℂ F φ))) φ :=
    (hasFDerivAt_const z φ).prodMk ((p2Extend38 n).hasFDerivAt.comp φ hF.hasFDerivAt)
  have hcomp := hΦ.hasFDerivAt.comp φ hg
  show fderiv ℂ ((fun p : ℂ × Lib.L2Seq => p2FullNumerator38 n p.2 p.1) ∘
    (fun ψ => (z, p2Extend38 n (F ψ)))) φ H = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply]
  rfl

/-- Summability over ℤ with the omitted index set to zero is summability over the omitted-index subtype. -/
theorem summable_ite_iff_subtype (n : ℤ) (g : ℤ → ℂ) :
    Summable (fun k : ℤ => if k = n then (0 : ℂ) else g k) ↔
      Summable (fun r : P2Index38 n => g r.1) := by
  have hf : ∀ x ∉ Set.range (Subtype.val : P2Index38 n → ℤ),
      (fun k : ℤ => if k = n then (0 : ℂ) else g k) x = 0 := by
    intro x hx
    have hxn : x = n := by
      by_contra hne
      exact hx ⟨⟨x, hne⟩, rfl⟩
    simp [hxn]
  have key := Function.Injective.summable_iff (f := fun k : ℤ => if k = n then (0 : ℂ) else g k)
    Subtype.val_injective hf
  have hc : ((fun k : ℤ => if k = n then (0 : ℂ) else g k) ∘ (Subtype.val : P2Index38 n → ℤ)) =
      fun r : P2Index38 n => g r.1 := by
    funext r
    exact if_neg r.2
  rw [hc] at key
  exact key.symm

/-- The same reindexing for the sum. -/
theorem tsum_ite_eq_subtype (n : ℤ) (g : ℤ → ℂ) :
    ∑' k : ℤ, (if k = n then (0 : ℂ) else g k) = ∑' r : P2Index38 n, g r.1 := by
  have hsupp : Function.support (fun k : ℤ => if k = n then (0 : ℂ) else g k) ⊆
      Set.range (Subtype.val : P2Index38 n → ℤ) := by
    intro k hk
    by_cases hkn : k = n
    · simp [hkn] at hk
    · exact ⟨⟨k, hkn⟩, rfl⟩
  have h := Function.Injective.tsum_eq (f := fun k : ℤ => if k = n then (0 : ℂ) else g k)
    Subtype.val_injective hsupp
  calc ∑' k : ℤ, (if k = n then (0 : ℂ) else g k)
      = ∑' c : P2Index38 n, (if c.1 = n then (0 : ℂ) else g c.1) := h.symm
    _ = ∑' r : P2Index38 n, g r.1 := tsum_congr fun r => if_neg r.2

/-- Pointwise form: the derivative sequence with the omitted index removed, as an ℓ²-extension. -/
theorem ite_term_eq (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair)
    (hF : DifferentiableAt ℂ F φ) (H : PotPair) (z : ℂ) (k : ℤ) :
    (if k = n then (0 : ℂ) else
        fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H /
          (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) =
      (if k = n then (0 : ℂ) else
        p2Extend38 n (fderiv ℂ F φ H) k / (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) := by
  by_cases hk : k = n
  · simp [hk]
  · rw [if_neg hk, if_neg hk, fderiv_sigma_coord n F φ hF k hk H]
    congr 1
    exact (p2Extend_at38 n _ ⟨k, hk⟩).symm

/-- G5-033 core, generic in F. Premise `hF` is the G2-071 consumption point (differentiability of the
root map at φ). Conjunct 1: ℓ² of the root derivatives. Conjunct 2: summability of the log-derivative
series. Conjunct 3: the logarithmic-derivative identity in direction H. -/
theorem assembly (n : ℤ) (F : PotPair → P2Space38 n) (φ : PotPair)
    (hF : DifferentiableAt ℂ F φ) (z : ℂ)
    (hz : ∀ k : ℤ, k ≠ n → z ≠ Lib.sigmaOf (p2Extend38 n (F φ)) k) (H : PotPair) :
    Memℓp (fun k : ℤ => if k = n then (0 : ℂ) else
        fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H) 2 ∧
    Summable (fun k : ℤ => if k = n then (0 : ℂ) else
        fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H /
          (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) ∧
    fderiv ℂ (fun ψ => p6PsiNumerator38 n F ψ z) φ H =
      p6PsiNumerator38 n F φ z * ∑' k : ℤ, (if k = n then (0 : ℂ) else
        fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H /
          (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) := by
  have hl : (fun k : ℤ => if k = n then (0 : ℂ) else
        fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H) =
      ⇑(p2Extend38 n (fderiv ℂ F φ H)) := by
    funext k
    by_cases hk : k = n
    · simp [hk]
    · rw [if_neg hk, fderiv_sigma_coord n F φ hF k hk H]
      exact (p2Extend_at38 n _ ⟨k, hk⟩).symm
  have hpt : ∀ r : P2Index38 n,
      p2Extend38 n (fderiv ℂ F φ H) r.1 / (Lib.sigmaOf (p2Extend38 n (F φ)) r.1 - z) =
        fderiv ℂ F φ H r / (countingCenter38 r.1 + F φ r - z) := by
    intro r
    rw [p2Extend_at38 n _ r, sigmaOf_ext_eq n (F φ) r.1 r.2]
  have hden : ∀ r : P2Index38 n, countingCenter38 r.1 + F φ r - z ≠ 0 := by
    intro r hr
    apply hz r.1 r.2
    rw [sigmaOf_ext_eq n (F φ) r.1 r.2]
    have hr' : countingCenter38 r.1 + F φ ⟨r.1, r.2⟩ - z = 0 := hr
    linear_combination -hr'
  obtain ⟨hsum, hid⟩ := (NlsGge.GKDefinitionDesign.G2_055 n (F φ) (fderiv ℂ F φ H)).2.1 z hden
  have hsumS : Summable (fun r : P2Index38 n =>
      p2Extend38 n (fderiv ℂ F φ H) r.1 / (Lib.sigmaOf (p2Extend38 n (F φ)) r.1 - z)) :=
    hsum.congr (fun r => (hpt r).symm)
  have hZ : Summable (fun k : ℤ => if k = n then (0 : ℂ) else
      p2Extend38 n (fderiv ℂ F φ H) k / (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) :=
    (summable_ite_iff_subtype n (fun k : ℤ =>
      p2Extend38 n (fderiv ℂ F φ H) k / (Lib.sigmaOf (p2Extend38 n (F φ)) k - z))).2 hsumS
  refine ⟨?_, ?_, ?_⟩
  · rw [hl]
    exact lp.memℓp _
  · exact hZ.congr (fun k => (ite_term_eq n F φ hF H z k).symm)
  · calc fderiv ℂ (fun ψ => p6PsiNumerator38 n F ψ z) φ H
        = p4NumeratorVariation38 n (p2Extend38 n (F φ)) (p2Extend38 n (fderiv ℂ F φ H)) z :=
          fderiv_psiNumerator n F φ hF z H
      _ = p2Numerator38 n (F φ) z *
            ∑' r : P2Index38 n, fderiv ℂ F φ H r / (countingCenter38 r.1 + F φ r - z) := hid
      _ = p6PsiNumerator38 n F φ z *
            ∑' r : P2Index38 n,
              p2Extend38 n (fderiv ℂ F φ H) r.1 / (Lib.sigmaOf (p2Extend38 n (F φ)) r.1 - z) := by
          unfold p6PsiNumerator38
          congr 1
          exact tsum_congr (fun r => (hpt r).symm)
      _ = p6PsiNumerator38 n F φ z * ∑' k : ℤ, (if k = n then (0 : ℂ) else
            p2Extend38 n (fderiv ℂ F φ H) k / (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) := by
          rw [tsum_ite_eq_subtype]
      _ = p6PsiNumerator38 n F φ z * ∑' k : ℤ, (if k = n then (0 : ℂ) else
            fderiv ℂ (fun ψ => Lib.sigmaOf (p2Extend38 n (F ψ)) k) φ H /
              (Lib.sigmaOf (p2Extend38 n (F φ)) k - z)) := by
          congr 1
          exact tsum_congr (fun k => (ite_term_eq n F φ hF H z k).symm)

end
end NlsGge.ThirdConsultation.G5033Support1
