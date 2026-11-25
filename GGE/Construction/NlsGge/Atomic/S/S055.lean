import Mathlib
import NlsGge.ThirdConsultation.S.SShared06
import NlsGge.Atomic.S.S073
import NlsGge.Hierarchy.UniformPartitionBoundAux38

                                                                                                           
                                                                                                                            
                                                                                                                                     
                                                       
                                                                                                                     
                                                                                                                      
                                                                                                                            
                                                                                                              
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.Measure
open NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.S

/-- S-055 helper (signed modes to the Fin enumeration): the product over the signed mode set `|n| ≤ N`
equals the product over `i : Fin (2N+1)` of `g (modeIndex N i)`. Argument of S045.lean:26-40. -/
theorem S055_modes_prod (N : ℕ) (g : ℤ → ℝ) :
    ∏ n ∈ normalizerModes N, g n = ∏ i : Fin (2 * N + 1), g (modeIndex N i) := by
  have himg : Finset.univ.image (modeIndex N) = normalizerModes N := by
    ext n
    simp only [Finset.mem_image, Finset.mem_univ, true_and, normalizerModes, Finset.mem_Icc]
    constructor
    · rintro ⟨i, rfl⟩
      have := i.isLt
      unfold modeIndex
      constructor <;> omega
    · intro h
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ n + (N : ℤ) by omega)
      refine ⟨⟨k, by omega⟩, ?_⟩
      unfold modeIndex
      dsimp only
      omega
  rw [← himg, Finset.prod_image]
  intro i _ j _ h
  exact modeIndex_injective38 N h

/-- S-055 (NEW-F07 ratio): the original over shifted Gaussian normalizer ratio is bounded uniformly. -/
theorem freeNormalizer_reserved_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ (lo up : ℝ) (c : BoundedCoefficients lo up) (N : ℕ),
      (∏ n ∈ normalizerModes N, fullWeightRate c.val n / shiftedRateV6 c n) ≤ C := by
  obtain ⟨C₀, hC₀, hle⟩ := freeNormalizer_shifted_le38
  refine ⟨C₀, hC₀, fun lo up c N => ?_⟩
  rw [S055_modes_prod N (fun n => fullWeightRate c.val n / shiftedRateV6 c n)]
  show (∏ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) / shiftedRateV6 c (modeIndex N i)) ≤ C₀
  have hterm : ∀ i : Fin (2 * N + 1),
      fullWeightRate c.val (modeIndex N i) / shiftedRateV6 c (modeIndex N i) =
        (Real.pi / shiftedRateV6 c (modeIndex N i)) /
          (Real.pi / fullWeightRate c.val (modeIndex N i)) := by
    intro i
    have h1 : fullWeightRate c.val (modeIndex N i) ≠ 0 :=
      (fullWeightRate_pos38 c (modeIndex N i)).ne'
    have h2 : shiftedRateV6 c (modeIndex N i) ≠ 0 :=
      (fullWeightRate_pos38 (shiftedCoefficients38 c) (modeIndex N i)).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    try ring
  have hprod : (∏ i : Fin (2 * N + 1),
        fullWeightRate c.val (modeIndex N i) / shiftedRateV6 c (modeIndex N i)) =
      (∏ i : Fin (2 * N + 1), Real.pi / shiftedRateV6 c (modeIndex N i)) /
        (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl (fun i _ => hterm i)
  have hden : (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) =
      freeNormalizer38 c N := rfl
  have hnum : (∏ i : Fin (2 * N + 1), Real.pi / shiftedRateV6 c (modeIndex N i)) =
      freeNormalizer38 (shiftedCoefficients38 c) N := rfl
  have hF : 0 < freeNormalizer38 c N := freeNormalizer38_pos c N
  have hL : freeNormalizer38 (shiftedCoefficients38 c) N ≤ C₀ * freeNormalizer38 c N :=
    hle lo up c N
  rw [hprod, hden, hnum, div_le_iff₀ hF]
  exact hL

end NlsGge.ThirdConsultation.S
end
