import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus

                                                                                                                                          
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem wkbList_length (φ : PotPair) (n : ℕ) : (wkbList φ n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wkbList, ih]

theorem wkbList_succ (φ : PotPair) (n : ℕ) : ∃ x, wkbList φ (n + 1) = wkbList φ n ++ [x] := ⟨_, rfl⟩

theorem wkbList_getD_wkbR (φ : PotPair) (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    (wkbList φ n).getD (k - 1) 0 = wkbR φ k := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : k = n + 1
    · subst h; rfl
    · obtain ⟨x, hx⟩ := wkbList_succ φ n
      rw [hx, List.getD_append _ _ _ _ (by rw [wkbList_length]; omega)]
      exact ih (by omega)

theorem wkbR_one (φ : PotPair) : wkbR φ 1 = -φ.2 := by
  simp [wkbR, wkbList]

theorem wkbR_succ (φ : PotPair) (n : ℕ) (hn : 1 ≤ n) :
    wkbR φ (n + 1) = weakDerivative (wkbR φ n) +
      physicalProduct φ.1
        (∑ k ∈ Finset.Icc 1 (n - 1), physicalProduct (wkbR φ k) (wkbR φ (n - k))) := by
  have hne : n ≠ 0 := by omega
  have h1 : wkbR φ (n + 1) = (wkbList φ n ++ [ (weakDerivative ((wkbList φ n).getD (n - 1) 0) +
      physicalProduct φ.1
        (∑ k ∈ Finset.range (n - 1),
          physicalProduct ((wkbList φ n).getD k 0) ((wkbList φ n).getD (n - 2 - k) 0))) ]).getD n 0 := by
    show (wkbList φ (n + 1)).getD (n + 1 - 1) 0 = _
    simp only [Nat.add_sub_cancel]
    show (wkbList φ n ++ [if n = 0 then -φ.2 else _]).getD n 0 = _
    rw [if_neg hne]
  rw [h1, List.getD_append_right _ _ _ _ (by rw [wkbList_length])]
  simp only [wkbList_length, Nat.sub_self, List.getD_cons_zero]
  rw [wkbList_getD_wkbR φ n n hn le_rfl]
  congr 2
  have hI : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have e1 : n - 2 - k = (n - (1 + k)) - 1 := by omega
  rw [e1, wkbList_getD_wkbR φ n (n - (1 + k)) (by omega) (by omega),
    show k = (1 + k) - 1 by omega]
  rw [wkbList_getD_wkbR φ n (1 + k) (by omega) (by omega)]
  simp

theorem weakDerivative_neg' (w : PhysicalL2) : weakDerivative (-w) = -weakDerivative w := by
  by_cases hd : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      reflectedFourierL2 w n) 2
  · have hd' : Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 (-w) n) 2 := by
      have := hd.neg
      convert this using 1
      funext n
      simp
    apply reflectedFourierL2.injective
    apply lp.ext
    funext n
    rw [map_neg]
    show reflectedFourierL2 (weakDerivative (-w)) n = -(reflectedFourierL2 (weakDerivative w) n)
    rw [weakDerivative_coeff _ hd' n, weakDerivative_coeff _ hd n]
    simp
  · have hd' : ¬ Memℓp (fun n : ℤ => (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 (-w) n) 2 := by
      intro h
      apply hd
      have := h.neg
      convert this using 1
      funext n
      simp
    unfold weakDerivative
    simp only [dif_neg hd, dif_neg hd', neg_zero]

theorem physicalProduct_zero' (u : PhysicalL2) : physicalProduct u 0 = 0 := by
  have h0 : (fun x : PhysicalCircle => u x * (0 : PhysicalL2) x) =ᵐ[spatialMeasure] fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 spatialMeasure] with x hx
    show u x * (0 : PhysicalL2) x = 0
    rw [show ((0 : PhysicalL2) : PhysicalCircle → ℂ) x = 0 from hx, mul_zero]
  have hd : productInL2 u 0 := (MemLp.zero (p := 2) (μ := spatialMeasure)).ae_eq h0.symm
  apply Lp.ext
  filter_upwards [physicalProduct_ae u 0 hd, h0, Lp.coeFn_zero ℂ 2 spatialMeasure] with x h1 h2 h3
  rw [h1, h2]
  exact (show ((0 : PhysicalL2) : PhysicalCircle → ℂ) x = 0 from h3).symm

theorem wkbR_two (φ : PotPair) : wkbR φ 2 = -weakDerivative φ.2 := by
  have := wkbR_succ φ 1 le_rfl
  simp only [Nat.reduceAdd, Nat.sub_self] at this
  rw [this, wkbR_one, weakDerivative_neg']
  simp [physicalProduct_zero']

end NlsGge.GKDefinitionDesign
end
