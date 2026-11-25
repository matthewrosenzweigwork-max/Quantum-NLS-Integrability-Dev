import NlsGge.GK38.AngleEndpointVariety
import NlsGge.GK38.TauGamma
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Source-only actual ordered-selector continuity AT A COLLAPSED PAIR ONLY.
This does not assert continuity or analyticity of global complex lambda labels
at simple roots. Exact symmetric values force both labels to the same center. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleCentered_endpoint_norm38 (a b : ℂ) :
    ‖a - (a + b) / 2‖ = Real.sqrt ‖(b - a) ^ 2‖ / 2 := by
  have he : a - (a + b) / 2 = -(b - a) / 2 := by ring
  calc
    _ = ‖b - a‖ / 2 := by rw [he, norm_div, norm_neg]; norm_num
    _ = _ := by rw [norm_pow, Real.sqrt_sq (norm_nonneg _)]

theorem anglePeriodic_centered_norm38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) :
    ‖lamMinus φ m - tauN φ m‖ = Real.sqrt ‖gamma2 φ m‖ / 2 ∧
    ‖lamPlus φ m - tauN φ m‖ = Real.sqrt ‖gamma2 φ m‖ / 2 := by
  rw [tauN_value38 φ hφ m, gamma2_value38 φ hφ m]
  constructor
  · simpa only [add_comm (lamPlus φ m)] using
      angleCentered_endpoint_norm38 (lamMinus φ m) (lamPlus φ m)
  · have he : (lamMinus φ m - lamPlus φ m) ^ 2 =
        (lamPlus φ m - lamMinus φ m) ^ 2 := by ring
    simpa only [he] using angleCentered_endpoint_norm38 (lamPlus φ m) (lamMinus φ m)

/-- A generic scalar selector with this ACTUALLY REALIZED symmetric-distance
identity is continuous at a collapsed value. No local uniform ell2 tail bound
or continuity of the selector away from the collapsed point is needed. -/
theorem angleCollapsed_selector_continuousAt38 (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ)
    (hgap : gamma2 φ m = 0) (L : PotPair → ℂ)
    (hL : ∀ ψ ∈ gkW, ‖L ψ - tauN ψ m‖ = Real.sqrt ‖gamma2 ψ m‖ / 2) :
    ContinuousAt L φ := by
  have hc : ContinuousAt (fun ψ => Real.sqrt ‖gamma2 ψ m‖ / 2) φ :=
    (((gamma2_analytic m φ hφ).continuousAt.norm).sqrt).div_const 2
  have ht : Tendsto (fun ψ => Real.sqrt ‖gamma2 ψ m‖ / 2) (nhds φ) (nhds 0) := by
    simpa only [hgap, norm_zero, Real.sqrt_zero, zero_div] using hc.tendsto
  have hnorm : Tendsto (fun ψ => ‖L ψ - tauN ψ m‖) (nhds φ) (nhds 0) := by
    apply ht.congr'
    filter_upwards [isOpen_gkW.mem_nhds hφ] with ψ hψ
    exact (hL ψ hψ).symm
  have hzero : L φ = tauN φ m := by
    have hh := hL φ hφ
    rw [hgap, norm_zero, Real.sqrt_zero, zero_div] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp hh)
  have hdiff : Tendsto (fun ψ => L ψ - tauN ψ m) (nhds φ) (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsum := hdiff.add (tauN_analytic m φ hφ).continuousAt
  have he : (fun ψ => (L ψ - tauN ψ m) + tauN ψ m) = L := by
    funext ψ
    ring
  rw [he, zero_add] at hsum
  change Tendsto L (nhds φ) (nhds (tauN φ m)) at hsum
  rw [← hzero] at hsum
  exact hsum

theorem angleActual_collapsed_endpoint_continuity38 (φ : PotPair) (hφ : φ ∈ gkW)
    (m : ℤ) (hgap : gamma2 φ m = 0) :
    ContinuousAt (fun ψ => lamMinus ψ m) φ ∧ ContinuousAt (fun ψ => lamPlus ψ m) φ :=
  ⟨angleCollapsed_selector_continuousAt38 φ hφ m hgap (fun ψ => lamMinus ψ m)
      (fun ψ hψ => (anglePeriodic_centered_norm38 ψ hψ m).1),
    angleCollapsed_selector_continuousAt38 φ hφ m hgap (fun ψ => lamPlus ψ m)
      (fun ψ hψ => (anglePeriodic_centered_norm38 ψ hψ m).2)⟩

end
end NlsGge.GK38
