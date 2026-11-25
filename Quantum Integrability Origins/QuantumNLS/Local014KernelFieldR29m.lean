import QuantumNLS.Local014RealSymbol
import QuantumNLS.Q07TensorCoefficientsR15
import QuantumNLS.IndexedFieldR27b

/-!
The field in the source's GP-04 argument for LOCAL-014 is the Hamiltonian
field of the real part of the radius-8 kernel symbol. Its power series uses
the degree-2p real multilinear coefficient of each diagonal kernel term.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace QuantumNLS.Local014KernelFieldR29m

open Function Metric
open KernelDefinition KernelConvergence Local014RealSymbol Q07TensorCoefficientsR15
  TensorPlacements RootOverlapLimit SymplecticBracket
open scoped NNReal ENNReal

attribute [local instance] InnerProductSpace.complexToReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def kernelCoefficient {p d : ℕ} (A : BoundedSymmetricKernel H p) (hd : p + p = d) :
    ContinuousMultilinearMap ℝ (fun _ : Fin d => H) ℂ :=
  (tensorCoefficient p (extendSymKernel A)).domDomCongr (finCongr hd)

private theorem norm_kernelCoefficient_le {p d : ℕ} (A : BoundedSymmetricKernel H p)
    (hd : p + p = d) : ‖kernelCoefficient A hd‖ ≤ ‖A‖ := by
  rw [kernelCoefficient, ContinuousMultilinearMap.norm_domDomCongr]
  exact (norm_tensorCoefficient_le p (extendSymKernel A)).trans (norm_extendSymKernel_le A)

private theorem kernelCoefficient_diagonal {p d : ℕ} (A : BoundedSymmetricKernel H p)
    (hd : p + p = d) (u : H) : kernelCoefficient A hd (fun _ => u) = kernelProductSymbol A u := by
  rw [kernelCoefficient, ContinuousMultilinearMap.domDomCongr_apply]
  change tensorCoefficient p (extendSymKernel A) (fun _ => u) = _
  rw [tensorCoefficient_diagonal, RootSymbolFrechet.symFun, extend_htpow, kernelProductSymbol]

private def series (A : ∀ p : ℕ, BoundedSymmetricKernel H p) :
    FormalMultilinearSeries ℝ H ℂ :=
  fun d => if hd : d / 2 + d / 2 = d then kernelCoefficient (A (d / 2)) hd else 0

private theorem evenDegree_injective : Injective (fun p : ℕ => p + p) := by
  intro a b h
  change a + a = b + b at h
  omega

private theorem norm_series_even_le (A : ∀ p : ℕ, BoundedSymmetricKernel H p) (p : ℕ) :
    ‖series A (p + p)‖ ≤ ‖A p‖ := by
  have hp : (p + p) / 2 = p := by omega
  have hd : (p + p) / 2 + (p + p) / 2 = p + p := by rw [hp]
  rw [series, dite_eq_left hd]
  exact (norm_kernelCoefficient_le (A ((p + p) / 2)) hd).trans_eq
    (congrArg (fun i => ‖A i‖) hp)

private theorem series_diagonal_even (A : ∀ p : ℕ, BoundedSymmetricKernel H p) (p : ℕ) (u : H) :
    series A (p + p) (fun _ => u) = kernelProductSymbol (A p) u := by
  have hp : (p + p) / 2 = p := by omega
  have hd : (p + p) / 2 + (p + p) / 2 = p + p := by rw [hp]
  rw [series, dite_eq_left hd, kernelCoefficient_diagonal, hp]

private theorem series_zero_of_not_in_range (A : ∀ p : ℕ, BoundedSymmetricKernel H p) {d : ℕ}
    (hd : d ∉ Set.range (fun p : ℕ => p + p)) : series A d = 0 := by
  exact dite_eq_right (fun he => hd ⟨d / 2, he⟩)

private theorem norm_series_summable {r : ℝ≥0} {A : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : Summable (fun p : ℕ => ((r : ℝ) ^ 2) ^ p * ‖A p‖)) :
    Summable (fun d : ℕ => ‖series A d‖ * (r : ℝ) ^ d) := by
  apply (evenDegree_injective.summable_iff (fun d hd => by
    rw [series_zero_of_not_in_range A hd, norm_zero, zero_mul])).mp
  refine hA.of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _))
    (fun p => ?_)
  change ‖series A (p + p)‖ * (r : ℝ) ^ (p + p) ≤ ((r : ℝ) ^ 2) ^ p * ‖A p‖
  have hpow : (r : ℝ) ^ (p + p) = ((r : ℝ) ^ 2) ^ p := by
    simpa only [two_mul] using (pow_mul (r : ℝ) 2 p)
  rw [hpow, mul_comm ‖series A (p + p)‖]
  exact mul_le_mul_of_nonneg_left (norm_series_even_le A p) (pow_nonneg (sq_nonneg _) _)

/-- The canonical scalar symbol is real analytic on the open convergence ball. -/
theorem analytic_symbol {r : ℝ≥0} (hr : 0 < r)
    {Ak : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {A : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius ((r : ℝ) ^ 2) Ak A) :
    AnalyticOnNhd ℝ (symbol A) (ball (0 : H) (r : ℝ)) := by
  obtain ⟨_, hs, _, _, hval⟩ := kernel_convergence (by positivity) hA
  have hp : HasFPowerSeriesOnBall (symbol A) (series A) 0 (r : ℝ≥0∞) := by
    refine ⟨(series A).le_radius_of_summable_norm (norm_series_summable hs),
      ENNReal.coe_pos.mpr hr, ?_⟩
    intro y hy
    rw [eball_coe] at hy
    have hy' : ‖y‖ ≤ (r : ℝ) := (mem_ball_zero_iff.mp hy).le
    have hsq := pow_le_pow_left₀ (norm_nonneg y) hy' 2
    rw [zero_add]
    apply (evenDegree_injective.hasSum_iff (fun d hd => by
      rw [series_zero_of_not_in_range A hd, zero_apply])).mp
    exact ((hval y hsq).1.of_norm).hasSum.congr_fun (fun p => series_diagonal_even A p y)
  simpa only [eball_coe] using hp.analyticOnNhd

/-- The source's canonical radius-8 real Hamiltonian gives an analytic field. -/
theorem analytic_kernel_field {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius 8 Hk Hlim) :
    AnalyticOnNhd ℝ (hamField (hReal Hlim)) (ball (0 : H) (Real.sqrt 8)) := by
  let r : ℝ≥0 := ⟨Real.sqrt 8, Real.sqrt_nonneg _⟩
  have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hr2 : (r : ℝ) ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have ha := analytic_symbol hr (hr2.symm ▸ hH)
  intro u hu
  exact IndexedFieldR27b.analytic_hamField ((Complex.reCLM.analyticAt _).comp (ha u hu))

/-- GP-04 state derivative for the canonical LOCAL-014 field, on a ball
containing both the unit sphere and the source's closed ball of radius 3/2. -/
theorem continuousOn_kernel_field_derivative
    {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius 8 Hk Hlim) :
    ContinuousOn (fderiv ℝ (hamField (hReal Hlim))) (ball (0 : H) (Real.sqrt 8)) :=
  (analytic_kernel_field hH).fderiv.continuousOn

end QuantumNLS.Local014KernelFieldR29m

#print axioms QuantumNLS.Local014KernelFieldR29m.analytic_symbol
#print axioms QuantumNLS.Local014KernelFieldR29m.analytic_kernel_field
#print axioms QuantumNLS.Local014KernelFieldR29m.continuousOn_kernel_field_derivative
