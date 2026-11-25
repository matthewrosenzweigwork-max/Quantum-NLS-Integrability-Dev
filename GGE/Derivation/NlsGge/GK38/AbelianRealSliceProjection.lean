import NlsGge.GK38.PairPotential

/-! The actual nonexpansive real retraction preserves every ball centered
on the real slice. Hence any overlap of two such complex balls has a real
point, without a finite-dimensional or complex-identity assumption. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def p6PotentialRealProjection38 : PotPair →L[ℝ] PhysicalL2 :=
  (1/2 : ℝ) • ((ContinuousLinearMap.fst ℝ PhysicalL2 PhysicalL2)+
    starLp.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ PhysicalL2 PhysicalL2))

theorem p6PotentialRealProjection_realSlice38 (u : PhysicalL2) :
    p6PotentialRealProjection38 (realSlice u)=u := by
  change (1/2 : ℝ) • (u+star (star u))=u
  rw [star_star,← two_smul ℝ u,smul_smul]
  norm_num

theorem p6PotentialRealProjection_norm_le38 (φ : PotPair) :
    ‖p6PotentialRealProjection38 φ‖ ≤ ‖φ‖ := by
  change ‖(1/2 : ℝ) • (φ.1+star φ.2)‖ ≤ ‖φ‖
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have hs : ‖star φ.2‖=‖φ.2‖ := starLp.norm_map φ.2
  calc
    _ ≤ (1/2 : ℝ)*(‖φ.1‖+‖star φ.2‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ ‖φ‖ := by rw [hs]; linarith [norm_fst_le φ,norm_snd_le φ]

theorem p6RealSlice_projection_dist_le38 (φ : PotPair) (u : PhysicalL2) :
    dist (realSlice (p6PotentialRealProjection38 φ)) (realSlice u) ≤ dist φ (realSlice u) := by
  rw [dist_realSlice,dist_eq_norm,dist_eq_norm]
  have h := p6PotentialRealProjection_norm_le38 (φ-realSlice u)
  simpa only [map_sub,p6PotentialRealProjection_realSlice38] using h

theorem p6RealSlice_projection_mem_ball38 (φ : PotPair) (u : PhysicalL2) (r : ℝ)
    (hφ : φ ∈ ball (realSlice u) r) :
    realSlice (p6PotentialRealProjection38 φ) ∈ ball (realSlice u) r :=
  mem_ball.mpr ((p6RealSlice_projection_dist_le38 φ u).trans_lt (mem_ball.mp hφ))

end
end NlsGge.GK38
