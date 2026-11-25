import NlsGge.GK38.AbelianRotatedSquareSectors
import NlsGge.GK38.AbelianSquareAnnulusGeometry

/-! SOURCE ONLY: exact quarter arcs, straightedges, genuine wholecircle CI.
CurveFUNCTION equalities precede derivative/parameter manipulation. No contour
identity is assumed. Exact targets+English preceded proof; UNCOMPILED/outside
currently prospective sectortransport4 scientific scope. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6QuarterTurn_circleMap38 (c : ℂ) (r : ℝ) (k : ℕ) (θ : ℝ) :
    c+Complex.I^k*circleMap 0 r θ = circleMap c r (θ+(k : ℝ)*(Real.pi/2)) := by
  have hpow : Complex.I^k = circleMap 0 1 ((k : ℝ)*(Real.pi/2)) := by
    simpa only [circleMap_pi_div_two,Complex.ofReal_one,one_mul,zero_add,one_pow] using
      circleMap_zero_pow k 1 (Real.pi/2)
  rw [hpow,circleMap_zero_mul]
  simp only [one_mul]
  rw [add_comm ((k : ℝ)*(Real.pi/2)) θ]
  simp only [circleMap,zero_add]

theorem p6Rotated_sector_circle_curve38 (c : ℂ) (r : ℝ) (k : ℕ) :
    (fun y : ℝ => p6RotatedSquareSector38 c r k 0 y) =
      (fun y : ℝ => circleMap c r (Real.arctan y+(k : ℝ)*(Real.pi/2))) := by
  funext y
  unfold p6RotatedSquareSector38
  rw [p6SquareSector_at_zero38]
  exact p6QuarterTurn_circleMap38 c r k (Real.arctan y)

theorem p6Rotated_sector_square_curve38 (c : ℂ) (r : ℝ) (k : ℕ) :
    (fun y : ℝ => p6RotatedSquareSector38 c r k 1 y) =
      (fun y : ℝ => c+Complex.I^k*((r : ℂ)*((1 : ℂ)+(y : ℂ)*Complex.I))) := by
  funext y
  simp only [p6RotatedSquareSector38,p6SquareSector_at_one38,zero_add,Complex.real_smul]

theorem p6Annulus_circle_integrable38 (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (p6SquareAnnulus38 c r)) :
    CircleIntegrable f c r := by
  have hs : sphere c r ⊆ p6SquareAnnulus38 c r := by
    intro z hz
    have hn : ‖z-c‖ = r := mem_sphere_iff_norm.mp hz
    refine ⟨hn.ge,?_⟩
    have hre := Complex.abs_re_le_norm (z-c)
    simpa only [Complex.sub_re,hn] using hre
  exact (hf.continuousOn.mono hs).circleIntegrable hr

end
end NlsGge.GK38
