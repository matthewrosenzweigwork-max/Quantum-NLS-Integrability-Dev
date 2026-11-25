import NlsGge.GK38.StdRootBranchesDomain
import NlsGge.GK38.StdRootBranchesOrders
import NlsGge.GK38.StdRootBranchesLines
import NlsGge.GK38.RealTypeSpectrumProbe

/-! Actual free near-axis domain and characteristic endpoint regressions. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem rootDomain_free_near_axis_probe38 (x ε : ℝ) (hε : 0 < ε) :
    ((0 : PotPair), (x : ℂ) + (ε : ℂ) * Complex.I) ∈ rootDomain38 := by
  refine ⟨by simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2), ?_⟩
  intro hgap
  obtain ⟨n, hn⟩ := mem_iUnion.mp hgap
  rw [lamMinus_zero38, lamPlus_zero38, segment_same] at hn
  have he : (x : ℂ) + (ε : ℂ) * Complex.I = countingCenter38 n := hn
  have him := congrArg Complex.im he
  simp [countingCenter38] at him
  linarith

theorem rootDomain_free_factor_analytic_probe38 (x ε : ℝ) (hε : 0 < ε) (n : ℤ) :
    AnalyticAt ℂ (rootFactor38 n) ((0 : PotPair), (x : ℂ) + (ε : ℂ) * Complex.I) :=
  rootFactor_analytic38 n _ (rootDomain_free_near_axis_probe38 x ε hε)

theorem rootDomain_free_collapsed_order_probe38 (n : ℤ) :
    analyticOrderAt (perChar 0) (countingCenter38 n) = 2 := by
  have h := perChar_collapsed_endpoint_order38 0
    (by simpa only [realSlice_zero] using realSlice_mem_gkW (0 : PhysicalL2)) n
    (by rw [lamMinus_zero38, lamPlus_zero38])
  simpa only [lamMinus_zero38] using h

theorem rootDomain_actual_nonfree_order_probe38 :
    analyticOrderAt (perChar (realSlice (constL2 1)))
      (lamMinus (realSlice (constL2 1)) 0) = 1 ∧
    analyticOrderAt (perChar (realSlice (constL2 1)))
      (lamPlus (realSlice (constL2 1)) 0) = 1 := by
  apply perChar_simple_endpoint_orders38 _ (realSlice_mem_gkW _) 0
  rw [realType_const_central_labels38.1, realType_const_central_labels38.2]
  norm_num

end
end NlsGge.GK38
