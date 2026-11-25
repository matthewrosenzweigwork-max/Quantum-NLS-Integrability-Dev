import QuantumNLS.IndexedGlobalR27b

/-! Fixed-amplitude scaling of the actual indexed Hamiltonian and its
constructed complete flow. The mass-scaling premise in the elementary
Hilbert-space calculation is proved for the physical mass in this module. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology InnerProductSpace
namespace QuantumNLS.IndexedScalingR27b
open PhysicalTensor (L2T)
open SymplecticBracket RootMassInvolutionR8 IndexedFieldR27b IndexedGlobalR27b
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

theorem hamField_scaling {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F G : H → ℝ} {a : ℝ}
    (ha : 0 < a) (hFG : ∀ w : H, F (a • w) = a^2 * G w) (u : H)
    (hF : DifferentiableAt ℝ F (a • u)) (hG : DifferentiableAt ℝ G u) :
    hamField F (a • u) = a • hamField G u := by
  let S : H →L[ℝ] H := a • ContinuousLinearMap.id ℝ H
  have he : (fderiv ℝ F (a • u)).comp S = a^2 • fderiv ℝ G u := by
    have h1 := hF.hasFDerivAt.comp u S.hasFDerivAt
    have h2 : HasFDerivAt (fun w : H => F (a • w)) (a^2 • fderiv ℝ G u) u := by
      simp_rw [hFG]
      exact hG.hasFDerivAt.const_mul (a^2)
    exact h1.unique h2
  have hd : fderiv ℝ F (a • u) = a • fderiv ℝ G u := by
    ext h
    have hh := DFunLike.congr_fun he h
    simp only [S,ContinuousLinearMap.comp_apply,smul_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] at hh
    change fderiv ℝ F (a • u) h = a * fderiv ℝ G u h
    apply (mul_left_cancel₀ ha.ne')
    nlinarith [hh]
  unfold hamField SymplecticBracket.gradient
  rw [hd,map_smul]
  rw [smul_comm (2 : ℝ)⁻¹ a,smul_comm (-Complex.I) a]

theorem mass_scaling (hκ : 0 < κ) {a : ℝ} (ha : 0 < a) (n : ℤ) (u : L2T L) :
    mass hκ n (a • u) = a^2 * mass (mul_pos hκ (sq_pos_of_pos ha)) n u := by
  have hc : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := RootMassScaling.masses_smul hκ (a : ℂ) hc u n
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hn : ‖(a : ℂ)‖ = a := by simp [abs_of_pos ha]
  convert h using 1
  simp only [hn]

theorem field_scaling (hκ : 0 < κ) {a : ℝ} (ha : 0 < a) (n : ℤ) (u : L2T L) :
    field hκ n (a • u) = a • field (mul_pos hκ (sq_pos_of_pos ha)) n u :=
  hamField_scaling ha (mass_scaling hκ ha n) u
    (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n (a • u)).differentiableAt
    (DEF014MassAnalytic.analyticAt_physical_coordinate
      (mul_pos hκ (sq_pos_of_pos ha)) n u).differentiableAt

theorem flow_scaling (hκ : 0 < κ) {a : ℝ} (ha : 0 < a) (n : ℤ) (u : L2T L) (t : ℝ) :
    flow hκ n t (a • u) = a • flow (mul_pos hκ (sq_pos_of_pos ha)) n t u := by
  let hκa := mul_pos hκ (sq_pos_of_pos ha)
  have he := solution_unique hκ n (a • u)
    (γ := fun s => a • flow hκa n s u) (by rw [flow_initial])
    (fun s => by
      rw [field_scaling hκ ha]
      exact (flow_derivative hκa n u s).const_smul a)
  exact (congrFun he t).symm

theorem stationary_on_each_sphere (hκ : 0 < κ) (n : ℤ) {m : ℝ} (hm : 0 < m) :
    ∃ u : L2T L, ‖u‖^2 = m ∧ ∀ t : ℝ, flow hκ n t u = u := by
  let u : L2T L := (Real.sqrt m : ℂ) • Fourier.modeLp L (n+1)
  refine ⟨u,?_,fun t => flow_plane hκ n (n+1) (by omega) _ t⟩
  simp only [u,norm_smul,OneParticleBorn.norm_modeLp,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg m),Real.sq_sqrt hm.le]

end QuantumNLS.IndexedScalingR27b
#print axioms QuantumNLS.IndexedScalingR27b.flow_scaling
#print axioms QuantumNLS.IndexedScalingR27b.stationary_on_each_sphere
