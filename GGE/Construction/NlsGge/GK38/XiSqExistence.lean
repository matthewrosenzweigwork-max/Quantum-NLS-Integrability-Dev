import NlsGge.GK38.XiSqLocal
import NlsGge.Analysis.AnalyticDivisionGluing

set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- Full selected existence target, contingent only on the actual preceding native proof modules. -/
theorem a5XiSqExists38 (n : ℤ) :
    ∃ g : PotPair → ℂ, XiSqSpec38 n g ∧
      ∀ g' : PotPair → ℂ, XiSqSpec38 n g' → Set.EqOn g g' gkW := by
  have hw : ∃ φ ∈ gkW, gamma2 φ n ≠ 0 := by
    refine ⟨realSlice (a5OpenWitness38 n), realSlice_mem_gkW (a5OpenWitness38 n), ?_⟩
    rw [a5OpenWitness_gamma2_38]
    norm_num
  obtain ⟨G, hGa, hGprod⟩ := NlsGge.Analysis.AnalyticDivisionGluing.exists_analytic_mul_eq_of_local
    (gamma2_analytic n) isPreconnected_gkW hw (a5Xi_local_divisibility38 n)
  have hGspec : XiSqSpec38 n G := ⟨hGa, fun φ hφ _ => hGprod φ hφ⟩
  exact ⟨G, hGspec, fun G' hG' => xiSqCandidate_unique38 n G G' hGspec hG'⟩

theorem a5XiSqExistence38 : XiSqExistence38 := a5XiSqExists38

end
end NlsGge.GK38
