import QuantumNLS.IndexedUnitRayR30b
import QuantumNLS.IndexedScalingR27b
import QuantumNLS.IndexedSymplecticR28b

/-! LOCAL-016, reset:period-theorem, quantum_periods.tex:436-492. One named
theorem includes the printed radius, all integer labels, every point of the
open physical L2 ball, exact common 2pi period and invariance for every time.
No least-period assertion or joint-stabilizer assertion is made. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Complex
open scoped InnerProductSpace
namespace QuantumNLS.IndexedPeriodTheoremR30b
open PhysicalTensor IndexedUnitRayR30b IndexedGlobalR27b IndexedScalingR27b
  IndexedRegularityR28b IndexedSymplecticR28b RayPeriodUpgrade
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

theorem physical_dimension : 2 ≤ Module.rank ℂ (L2T L) := by
  apply two_le_rank_of_orthonormal (e₁ := Fourier.modeLp L 0) (e₂ := Fourier.modeLp L 1)
  rw [orthonormal_iff_ite]
  intro i j
  rw [← (Fourier.fourierL2 L).inner_map_map]
  fin_cases i <;> fin_cases j <;>
    norm_num [Fourier.fourierL2_modeLp,lp.inner_single_left,lp.single_apply]

theorem scaled_ray (hκ : 0 < κ) (n : ℤ) (u : L2T L)
    (hu : u ∈ puncturedBall (L2T L) (delta L κ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ flow hκ n (2*Real.pi) u = c • u := by
  obtain ⟨ha,haδ⟩ := mem_puncturedBall.mp hu
  let a : ℝ := ‖u‖
  let v : L2T L := a⁻¹ • u
  have hav : a • v = u := by
    change a • (a⁻¹ • u) = u
    rw [smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hv : ‖v‖ = 1 := by
    change ‖a⁻¹ • u‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    change a⁻¹*a = 1
    exact inv_mul_cancel₀ ha.ne'
  have hκa : 0 < κ*a^2 := mul_pos hκ (sq_pos_of_pos ha)
  have hsmall : (κ*a^2)*L ≤ 1/1000000000000 := by
    have hL : 0 < L := Fact.out
    have hδ := (printed_ball_invariant (L := L) hκ).2.1
    have hsq : a^2 < (delta L κ)^2 := pow_lt_pow_left₀ haδ ha.le (by norm_num)
    have he : κ*L*(delta L κ)^2 = 1/1000000000000 := by rw [hδ]; field_simp [hκ.ne',hL.ne']
    calc
      _ = (κ*L)*a^2 := by ring
      _ ≤ (κ*L)*(delta L κ)^2 := mul_le_mul_of_nonneg_left hsq.le (by positivity)
      _ = _ := he
  obtain ⟨c,hcn,hc⟩ := actual_unit_ray hκa hsmall n v hv
  have hr := flow_scaling hκ ha n v (2*Real.pi)
  rw [hav,hc,smul_comm a c,hav] at hr
  exact ⟨c,hcn,hr⟩

/-- The complete printed LOCAL-016 theorem. The only parameter assumptions
are the printed L>0 and kappa>0. -/
theorem reset_period_theorem (hκ : 0 < κ) :
    0 < delta L κ ∧ (delta L κ)^2 = (1/1000000000000 : ℝ)/(κ*L) ∧
    (∀ n : ℤ, ∀ u : L2T L, ‖u‖ < delta L κ → flow hκ n (2*Real.pi) u = u) ∧
    (∀ n : ℤ, ∀ t : ℝ, MapsTo (flow (L := L) hκ n t)
      (ball 0 (delta L κ)) (ball 0 (delta L κ))) := by
  obtain ⟨hδ,hδsq,hinv⟩ := printed_ball_invariant (L := L) hκ
  refine ⟨hδ,hδsq,?_,hinv⟩
  intro n
  have hp := ray_period_upgrade (H := L2T L) (physical_dimension (L := L)) (R := delta L κ)
    (F := flow hκ n (2*Real.pi)) (contDiff_flow hκ n (2*Real.pi)).contDiffOn
    (fun u _ a b => symplectic_flow hκ n (2*Real.pi) u a b)
    (scaled_ray hκ n)
    (fun m hm _ => by
      obtain ⟨v,hv,hfix⟩ := stationary_on_each_sphere (L := L) hκ n hm
      exact ⟨v,hv,hfix (2*Real.pi)⟩)
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    exact flow_zero hκ n _
  · exact hp u (mem_puncturedBall.mpr ⟨norm_pos_iff.mpr hu0,hu⟩)

end QuantumNLS.IndexedPeriodTheoremR30b
#print axioms QuantumNLS.IndexedPeriodTheoremR30b.reset_period_theorem
