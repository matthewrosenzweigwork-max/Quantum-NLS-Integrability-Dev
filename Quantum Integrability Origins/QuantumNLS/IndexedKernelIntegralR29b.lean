import QuantumNLS.IndexedKernelContinuityR29b
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.RealVectorSpace

/-! Interval integration of actual chosen kernel expansions: uniform radius
bounds and fixed-degree norm limits. No kernel integral interchange is a premise. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators
namespace QuantumNLS.IndexedKernelIntegralR29b
open TensorCarrier KernelDefinition LocalPlacement KernelConvergence Local013PowerSeries
attribute [local instance] IndexedKernelContinuityR29b.kernelNormed
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def intList (A : ℝ → ∀ N : ℕ, KernelList (H := H) N) (a b : ℝ) (N : ℕ) : KernelList (H := H) N :=
  fun p => ∫ x in a..b, A x N p

def intLimit (Alim : ℝ → ∀ p : ℕ, BoundedSymmetricKernel H p) (a b : ℝ) (p : ℕ) :
    BoundedSymmetricKernel H p := ∫ x in a..b, Alim x p

theorem integrated_radius_bound {R B a b : ℝ} (hR : 0 ≤ R) (hab : a ≤ b)
    (A : ℝ → ∀ N : ℕ, KernelList (H := H) N)
    (hc : ∀ N p, ContinuousOn (fun x => A x N p) (Icc a b))
    (hb : ∀ x ∈ Icc a b, ∀ N, RadiusBound.radiusBound R (A x N) ≤ B) (N : ℕ) :
    RadiusBound.radiusBound R (intList A a b N) ≤ (b-a)*B := by
  have hc' (p : Fin (N+1)) : ContinuousOn (fun x => A x N p) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hc N p
  have hi (p : Fin (N+1)) : IntervalIntegrable (fun x => R^p.1*‖A x N p‖) volume a b :=
    (continuousOn_const.mul (hc' p).norm).intervalIntegrable
  unfold RadiusBound.radiusBound intList
  calc
    _ ≤ ∑ p : Fin (N+1), R^p.1*(∫ x in a..b, ‖A x N p‖) :=
      Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
        (intervalIntegral.norm_integral_le_integral_norm hab) (pow_nonneg hR _)
    _ = ∑ p : Fin (N+1), ∫ x in a..b, R^p.1*‖A x N p‖ := by
      simp only [intervalIntegral.integral_const_mul]
    _ = ∫ x in a..b, ∑ p : Fin (N+1), R^p.1*‖A x N p‖ :=
      (intervalIntegral.integral_finsetSum (fun p _ => hi p)).symm
    _ ≤ ∫ x in a..b, B := by
      apply intervalIntegral.integral_mono_on hab
        ((continuousOn_finsetSum _ fun p _ => continuousOn_const.mul (hc' p).norm).intervalIntegrable)
        intervalIntegrable_const
      intro x hx
      exact hb x hx N
    _ = _ := by rw [intervalIntegral.integral_const]; ring

theorem continuousOn_coeffAt (A : ℝ → ∀ N : ℕ, KernelList (H := H) N)
    {a b : ℝ} (hc : ∀ N p, ContinuousOn (fun x => A x N p) (Icc a b)) (N j : ℕ) :
    ContinuousOn (fun x => coeffAt (A x) N j) (Icc a b) := by
  unfold coeffAt
  split_ifs with h
  · exact hc N ⟨j,by omega⟩
  · exact continuousOn_const

theorem coeffAt_intList (A : ℝ → ∀ N : ℕ, KernelList (H := H) N) (a b : ℝ) (N j : ℕ) :
    coeffAt (intList A a b) N j = ∫ x in a..b, coeffAt (A x) N j := by
  unfold coeffAt intList
  split_ifs with h
  · rfl
  · simp only [intervalIntegral.integral_zero]

/-- Finite contour segments preserve both parts of chosen kernel convergence.
Measurability and domination are proved from coordinate continuity and the
actual uniform radius bound, so no Fubini/Tonelli repair is assumed. -/
theorem integrated_converges {R B a b : ℝ} (hR : 1 ≤ R) (hab : a ≤ b)
    (A : ℝ → ∀ N : ℕ, KernelList (H := H) N)
    (Alim : ℝ → ∀ p : ℕ, BoundedSymmetricKernel H p)
    (hc : ∀ N p, ContinuousOn (fun x => A x N p) (Icc a b))
    (hb : ∀ x ∈ Icc a b, ∀ N, RadiusBound.radiusBound R (A x N) ≤ B)
    (hlim : ∀ x ∈ Icc a b, ConvergesOnRadius R (A x) (Alim x)) :
    ConvergesOnRadius R (intList A a b) (intLimit Alim a b) := by
  refine ⟨⟨(b-a)*B,integrated_radius_bound (by linarith) hab A hc hb⟩,fun j => ?_⟩
  have hm (N : ℕ) : AEStronglyMeasurable (fun x => coeffAt (A x) N j)
      (volume.restrict (Ioc a b)) :=
    (show ContinuousOn (fun x => coeffAt (A x) N j) (uIcc a b) from by
      simpa only [uIcc_of_le hab] using continuousOn_coeffAt A hc N j).intervalIntegrable.1.aestronglyMeasurable
  have hbound (N : ℕ) : ∀ᵐ x ∂(volume.restrict (Ioc a b)), ‖coeffAt (A x) N j‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (norm_coeffAt_le hR (A x) N j).trans (hb x ⟨hx.1.le,hx.2⟩ N)
  have ht : ∀ᵐ x ∂(volume.restrict (Ioc a b)),
      Tendsto (fun N => coeffAt (A x) N j) atTop (𝓝 (Alim x j)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mpr ((hlim x ⟨hx.1.le,hx.2⟩).2 j)
  have hi := tendsto_integral_of_dominated_convergence (fun _ : ℝ => B) hm
    (integrable_const B) hbound ht
  apply (tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mp
  simpa only [coeffAt_intList,intLimit,intervalIntegral.integral_of_le hab] using hi


/-- A continuous additive map commutes with the interval Bochner integral.
The scalar structures here are the canonical restrictions of complex ones. -/
theorem additive_intervalIntegral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →+ F) (hT : Continuous T) {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    T (∫ x in a..b, f x) = ∫ x in a..b, T (f x) :=
  ((T.toRealLinearMap hT).intervalIntegral_comp_comm hf).symm

/-- The integrated chosen kernels represent the literal Bochner integral
of their operators. -/
theorem represented_intList {a b : ℝ}
    (A : ℝ → ∀ N : ℕ, KernelList (H := H) N)
    (hc : ∀ N p, ContinuousOn (fun x => A x N p) (uIcc a b)) (N : ℕ) :
    RadiusBound.represented (intList A a b N) =
      ∫ x in a..b, RadiusBound.represented (A x N) := by
  have hi (p : Fin (N+1)) : IntervalIntegrable (fun x => A x N p) volume a b :=
    (hc N p).intervalIntegrable
  have he (p : Fin (N+1)) : RadiusBound.Q N p.1 (by omega) (∫ x in a..b, A x N p) =
      ∫ x in a..b, RadiusBound.Q N p.1 (by omega) (A x N p) :=
    additive_intervalIntegral (qHom (H := H) N p) (continuous_qHom (H := H) N p) (hi p)
  unfold RadiusBound.represented intList
  simp only [he]
  exact (intervalIntegral.integral_finsetSum (fun p _ =>
    ((continuous_qHom (H := H) N p).comp_continuousOn (hc N p)).intervalIntegrable)).symm

end QuantumNLS.IndexedKernelIntegralR29b
#print axioms QuantumNLS.IndexedKernelIntegralR29b.integrated_radius_bound
#print axioms QuantumNLS.IndexedKernelIntegralR29b.integrated_converges

#print axioms QuantumNLS.IndexedKernelIntegralR29b.represented_intList
