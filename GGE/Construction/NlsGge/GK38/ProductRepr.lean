import NlsGge.GK38.ProductReprRatio

/-! # S4: exact periodic and critical product representations

GK book I.6, Lemmas 6.8 and 6.5. The accepted entire-ratio theorem uses
entire differentiability, exact multiplicities and the strict circle estimates.
The symmetric convergence results are established in ProductReprConstruction.
-/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
namespace NlsGge.GK38
noncomputable section

theorem perChar_eq_periodicProduct38 (φ : PotPair) : perChar φ = periodicProduct38 φ := by
  apply Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_perChar_z φ w (mem_univ w)).differentiableAt)
    (differentiable_periodicProduct38 φ)
  · intro w
    exact (analyticOrderAt_periodicProduct38 φ w).le
  · intro ε hε
    obtain ⟨N, hN⟩ := productRepr_circle_ratio38 φ ε hε
    exact ⟨N, fun n hn z hz => (hN n hn z hz).2.2.1⟩

theorem discrimDeriv_eq_criticalProduct38 (φ : PotPair) :
    deriv (discrim φ) = criticalProduct38 φ := by
  apply Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_discrimDeriv38 φ w (mem_univ w)).differentiableAt)
    (differentiable_criticalProduct38 φ)
  · intro w
    exact (analyticOrderAt_criticalProduct38 φ w).le
  · intro ε hε
    obtain ⟨N, hN⟩ := productRepr_circle_ratio38 φ ε hε
    exact ⟨N, fun n hn z hz => (hN n hn z hz).2.2.2⟩

theorem perChar_product (φ : PotPair) (z : ℂ) :
    perChar φ z = -4 * ∏'[symmetricIcc ℤ] m : ℤ,
      (lamPlus φ m - z) * (lamMinus φ m - z) / (πn m : ℂ) ^ 2 :=
  congrFun (perChar_eq_periodicProduct38 φ) z

theorem discrimDeriv_product (φ : PotPair) (z : ℂ) :
    deriv (discrim φ) z = 2 * ∏'[symmetricIcc ℤ] k : ℤ,
      (lamDot φ k - z) / (πn k : ℂ) :=
  congrFun (discrimDeriv_eq_criticalProduct38 φ) z

end
end NlsGge.GK38
