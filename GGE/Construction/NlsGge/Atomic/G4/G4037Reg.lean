import Mathlib
import NlsGge.Atomic.G3.G3007
import NlsGge.GK38.AngleRegularFactor
import NlsGge.GK38.AbelianDenominator

                                                                                                        
                                                                                                                              
                                                                                                         
                                                                                                               
                                                                                                                         
                                                                  
                                                                                                                      
                                                                                                                        
                                                                                        
                                                                                                                          
                                                                                                               
                                                                                                                      
                                                                                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G4037Aux

theorem psiZeta_eq_angleRegularFactor (ψ : PotPair) (t : Lib.L2Seq) (n m : ℤ) (hmn : m ≠ n)
    (z : ℂ) (hp : (ψ, z) ∈ a5OmittedRootDomain38 m) (hσ : Lib.sigmaOf t n - z ≠ 0) :
    psiZeta ψ t n m z = angleRegularFactor38 n m ((ψ, t), z) := by
  have hgk : ψ ∈ gkW := hp.1
  have hav : z ∉ segment ℝ (lamMinus ψ n) (lamPlus ψ n) := hp.2 n (Ne.symm hmn)
  have hwn : standardRoot ψ n z ≠ 0 := by
    have hs := stdRoot_ne_zero38 (lamMinus ψ n) (lamPlus ψ n) z hav
    simpa only [standardRoot, add_comm (lamMinus ψ n), ← tauN_value38 ψ hgk n,
      ← gamma2_value38 ψ hgk n] using hs
  have hnm : n ≠ m := Ne.symm hmn
  have hp0 : ((ψ, t), z) ∈ {p : (PotPair × Lib.L2Seq) × ℂ |
      (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} := hp
  have hT := ((G2_022 m).2.tendsto_at hp0)
  set L : ℂ := p2OmittedRatio38 m ((ψ, t), z) with hL
  have hrel : ∀ᶠ N : ℕ in atTop,
      (∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if k = n ∨ k = m then (1 : ℂ) else (Lib.sigmaOf t k - z) / standardRoot ψ k z) =
      (standardRoot ψ n z / (Lib.sigmaOf t n - z)) *
        ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k = m then (1 : ℂ) else (Lib.sigmaOf t k - z) / standardRoot ψ k z := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [← Finset.mul_prod_erase _ _ hn, ← Finset.mul_prod_erase _ _ hn]
    have e1 : (if n = n ∨ n = m then (1 : ℂ) else (Lib.sigmaOf t n - z) / standardRoot ψ n z) = 1 := by
      simp
    have e2 : (if n = m then (1 : ℂ) else (Lib.sigmaOf t n - z) / standardRoot ψ n z) =
        (Lib.sigmaOf t n - z) / standardRoot ψ n z := by
      rw [if_neg hnm]
    have e3 : ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (if k = n ∨ k = m then (1 : ℂ) else (Lib.sigmaOf t k - z) / standardRoot ψ k z) =
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (if k = m then (1 : ℂ) else (Lib.sigmaOf t k - z) / standardRoot ψ k z) := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := (Finset.mem_erase.1 hk).1
      by_cases hkm : k = m
      · simp [hkm]
      · rw [if_neg (by tauto), if_neg hkm]
    rw [e1, e2, e3]
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k = n ∨ k = m then (1 : ℂ) else (Lib.sigmaOf t k - z) / standardRoot ψ k z)
      atTop (𝓝 ((standardRoot ψ n z / (Lib.sigmaOf t n - z)) * L)) := by
    refine Tendsto.congr' (hrel.mono fun N h => h.symm) ?_
    exact hT.const_mul (standardRoot ψ n z / (Lib.sigmaOf t n - z))
  have hHP : HasProd (fun k : ℤ => if k = n ∨ k = m then (1 : ℂ)
      else (Lib.sigmaOf t k - z) / standardRoot ψ k z)
      ((standardRoot ψ n z / (Lib.sigmaOf t n - z)) * L) (symmetricIcc ℤ) :=
    hasProd_symmetricIcc_iff.2 hlim
  have hdrr : doubleRootRatio ψ t n m z =
      (standardRoot ψ n z / (Lib.sigmaOf t n - z)) * L := hHP.tprod_eq
  unfold psiZeta angleRegularFactor38
  rw [hdrr]
  field_simp
  exact hL

/-- The full sequence with n-th root placed at `a`. -/
def g4037S (n : ℤ) (ψ : PotPair) (a : ℂ) : Lib.L2Seq :=
  p2Extend38 n (sourceF n ψ) + (a - (n : ℂ) * (Real.pi : ℂ)) • lp.single 2 n (1 : ℂ)

theorem g4037S_sigma_self (n : ℤ) (ψ : PotPair) (a : ℂ) :
    Lib.sigmaOf (g4037S n ψ a) n = a := by
  unfold g4037S
  rw [G2048Aux.sigma_shift_eq]
  simp only [Lib.sigmaOf, p2Extend_self38]
  ring

theorem g4037S_sigma_ne (n : ℤ) (ψ : PotPair) (a : ℂ) (k : ℤ) (hk : k ≠ n) :
    Lib.sigmaOf (g4037S n ψ a) k = countingCenter38 k + sourceF n ψ ⟨k, hk⟩ := by
  unfold g4037S
  rw [G2048Aux.sigma_shift_ne _ n _ k hk]
  have h := p2Extend_at38 n (sourceF n ψ) ⟨k, hk⟩
  simp only [Lib.sigmaOf, countingCenter38]
  rw [h]

theorem g4037S_numerator (n : ℤ) (ψ : PotPair) (a : ℂ) :
    p2FullNumerator38 n (g4037S n ψ a) = p6PsiNumerator38 n (sourceF n) ψ := by
  funext z
  unfold g4037S p2FullNumerator38 p6PsiNumerator38 p2Numerator38 p2FullNumerator38
  rw [Lib.omitProd_add_single]

theorem g4037S_psiZeta (n m : ℤ) (ψ : PotPair) (a z : ℂ) :
    psiZeta ψ (g4037S n ψ a) n m z = psiZeta ψ (p2Extend38 n (sourceF n ψ)) n m z := by
  unfold psiZeta doubleRootRatio
  congr 2
  funext k
  by_cases hk : k = n ∨ k = m
  · simp [hk]
  · have hkn : k ≠ n := fun h => hk (Or.inl h)
    rw [if_neg hk, if_neg hk]
    unfold g4037S
    rw [G2048Aux.sigma_shift_ne _ n _ k hkn]

/-- Complex-base regular-factor bound for the fixed discs of `φ0`, uniformly in `n`, `m`, `ψ`. -/
theorem g4037_reg_factor (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ∃ V : Set PotPair, ∃ B : ℝ, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧ 0 < B ∧
      ∀ ψ ∈ V, IsolatingFamily38 ψ (discC φ0) (discR φ0) ∧
        ∀ n m : ℤ, m ≠ n → ∀ z ∈ Metric.ball (discC φ0 m) (discR φ0 m),
          ‖angleRegularFactor38 n m ((ψ, g4037S n ψ (discC φ0 n)), z)‖ ≤ B * Lib.c3w n m := by
  obtain ⟨V, B, hVo, hφV, hVW, hB, hbd⟩ := G3_007_bound φ0 hφ0
  refine ⟨V, B, hVo, hφV, hVW, hB, fun ψ hψ => ⟨(hbd ψ hψ).1, ?_⟩⟩
  intro n m hmn z hz
  have hfam := (hbd ψ hψ).1
  have hψgk : ψ ∈ gkW := sourceFamily.W_gk (hVW hψ)
  obtain ⟨c, N, hg, hs⟩ := hfam
  have hzc : z ∈ closedBall (discC φ0 m) (discR φ0 m) := ball_subset_closedBall hz
  have hsn : Lib.sigmaOf (g4037S n ψ (discC φ0 n)) n ∈ closedBall (discC φ0 n) (discR φ0 n) := by
    rw [g4037S_sigma_self]
    exact mem_closedBall_self (hg.1 n).1.le
  have hden := (p2OwnSigma_denominator38 (discC φ0) (discR φ0) c N hg n m (Ne.symm hmn)
    (g4037S n ψ (discC φ0 n)) hsn z hzc).1
  have hdom : (ψ, z) ∈ a5OmittedRootDomain38 m :=
    a5OwnClosedBall_omittedDomain38 ψ hψgk (discC φ0) (discR φ0) ⟨c, N, hg, hs⟩ m z hzc
  rw [← psiZeta_eq_angleRegularFactor ψ _ n m hmn z hdom hden, g4037S_psiZeta]
  exact (hbd ψ hψ).2 n m hmn z hzc

end G4037Aux
end
end NlsGge.GKDefinitionDesign
