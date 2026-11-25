import QuantumNLS.TerraMultiRound85H1Scaling

/-! Amplitude scaling of the actual H¹ mild equation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.H1Bridge QuantumNLS.L2Flow
open QuantumNLS.TerraMultiRound85H1Bridge QuantumNLS.TerraMultiRound85H1Scaling
namespace QuantumNLS.TerraMultiRound85MildScaling
variable {L : ℝ} [Fact (0 < L)]

/-- A real amplitude changes the cubic coupling by its square. -/
theorem scale_mild {κ : ℝ} (r : ℝ) (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) (κ*r^2) Set.univ u0 u) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ ((r : ℂ) • u0) (fun t => (r : ℂ) • u t) := by
  refine ⟨Set.mem_univ _, Set.ordConnected_univ, ?_, ?_⟩
  · exact ((continuousOn_univ.mp hu.cont).const_smul (r : ℂ)).continuousOn
  · intro t ht
    have h := hu.duhamel_eq t (Set.mem_univ t)
    unfold duhamel at h ⊢
    simp_rw [Fh_real_scale, map_smul, intervalIntegral.integral_smul]
    rw [h, smul_sub]
    simp only [smul_smul]
    congr 1
    congr 1
    push_cast
    ring

/-- Such a scaled mild curve is the actual L² solution by the accepted bridge. -/
theorem scaled_mild_is_flow {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) (κ*r^2) Set.univ u0 u) :
    ∀ t, flowMap hκ (emb ((r : ℂ) • u0)) t = emb ((r : ℂ) • u t) :=
  flowMap_of_global_mild hκ _ _ (scale_mild r u0 u hu)

#print axioms scale_mild
#print axioms scaled_mild_is_flow
end QuantumNLS.TerraMultiRound85MildScaling
