import QuantumNLS.Prop022TensorCalculusR116
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The full classical factorial series has a proved time derivative along
any differentiable unit profile with a uniform speed bound. This does not
identify the mixed and conjugate Hessian blocks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022ClassicalTimeR116
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022TensorCalculusR116
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

lemma powerDifferential_unit_bound (m : ℕ) (u h : L2T L) (hu : ‖u‖ = 1) :
    ‖powerDifferential m u h‖ ≤ (m : ℝ) * ‖h‖ := by
  classical
  unfold powerDifferential
  rw [sum_apply]
  calc
    _ ≤ ∑ i : Fin m, ‖((tensorMultilinear (L := L) m).restrictScalars ℝ).toContinuousLinearMap
        (fun _ => u) i h‖ := norm_sum_le _ _
    _ = ∑ _i : Fin m, ‖h‖ := by
      apply Finset.sum_congr rfl
      intro i _
      change ‖(tensorMultilinear (L := L) m) (Function.update (fun _ => u) i h)‖ = ‖h‖
      rw [tensorMultilinear_apply, UniformSpace.Completion.norm_coe, norm_ptprod]
      simp [Function.update_apply, apply_ite, hu]
    _ = _ := by simp

/-- Differential of the actual symmetric tensor power. -/
def powerD (m : ℕ) (u : L2T L) : L2T L →L[ℝ] HN L m :=
  ((physSector L m).orthogonalProjectionOnto.restrictScalars ℝ) ∘L powerDifferential m u

lemma powerD_bound (m : ℕ) (u h : L2T L) (hu : ‖u‖ = 1) :
    ‖powerD m u h‖ ≤ (m : ℝ) * ‖h‖ := by
  change ‖(physSector L m).orthogonalProjectionOnto (powerDifferential m u h)‖ ≤ _
  exact (Submodule.norm_orthogonalProjectionOnto_apply_le (physSector L m)
    (powerDifferential m u h)).trans (powerDifferential_unit_bound m u h hu)

lemma powerD_time (m : ℕ) (u : ℝ → L2T L) (v : L2T L) (t : ℝ)
    (hu : HasDerivAt u v t) : HasDerivAt (fun s => power m (u s)) (powerD m (u t) v) t := by
  have heq : (fun s => (physSector L m).orthogonalProjectionOnto (htpow m (u s))) =
      fun s => power m (u s) := by
    funext s
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (power m (u s))
  rw [← heq]
  exact (((physSector L m).orthogonalProjectionOnto.restrictScalars ℝ).hasFDerivAt.comp
    (u t) (htpow_hasFDerivAt m (u t))).comp_hasDerivAt t hu

/-- Literal derivative of the real rank-m Hamiltonian polynomial. -/
def classicalRate (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (u v : L2T L) : ℝ :=
  (⟪power m u, B m (powerD m u v)⟫_ℂ + ⟪powerD m u v, B m (power m u)⟫_ℂ).re

lemma classicalTerm_time (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ)
    (u : ℝ → L2T L) (v : L2T L) (t : ℝ) (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => classicalTerm B m (u s)) (classicalRate B m (u t) v) t := by
  have hp := powerD_time m u v t hu
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hp.inner ℂ (((B m).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hp))

lemma norm_realPart_le (z : ℂ) : ‖z.re‖ ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z

lemma classicalRate_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ)
    (u v : L2T L) (hu : ‖u‖ = 1) :
    ‖classicalRate B m u v‖ ≤ 2 * (m : ℝ) * ‖B m‖ * ‖v‖ := by
  have hp : ‖power m u‖ = 1 := by rw [power_norm, hu, one_pow]
  have hd := powerD_bound m u v hu
  calc
    _ ≤ ‖⟪power m u, B m (powerD m u v)⟫_ℂ +
        ⟪powerD m u v, B m (power m u)⟫_ℂ‖ := norm_realPart_le _
    _ ≤ ‖⟪power m u, B m (powerD m u v)⟫_ℂ‖ +
        ‖⟪powerD m u v, B m (power m u)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖power m u‖ * (‖B m‖ * ‖powerD m u v‖) +
        ‖powerD m u v‖ * (‖B m‖ * ‖power m u‖) := by
      apply add_le_add
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
      · exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
    _ ≤ 2 * (m : ℝ) * ‖B m‖ * ‖v‖ := by
      rw [hp]
      nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (B m))]

lemma classicalTerm_unit_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ)
    (u : L2T L) (hu : ‖u‖ = 1) : ‖classicalTerm B m u‖ ≤ ‖B m‖ := by
  have hp : ‖power m u‖ = 1 := by rw [power_norm, hu, one_pow]
  exact (norm_realPart_le _).trans
    ((norm_inner_le_norm _ _).trans (by simpa [hp] using le_opNorm (B m) (power m u)))

/-- Positive ranks of the pinned factorial Hamiltonian. -/
def classicalSeries (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : ℝ :=
  ∑' r, classicalTerm B (r+1) u

def classicalSeriesRate (B : ∀ m, HN L m →L[ℂ] HN L m) (u v : L2T L) : ℝ :=
  ∑' r, classicalRate B (r+1) u v

lemma classical_summable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hA : 0 ≤ A) (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    Summable (fun r => classicalTerm B (r+1) u) := by
  apply Summable.of_norm_bounded
    (((summable_nat_add_iff 1).mpr (weight_summable 0 A hA)).mul_left M)
  intro r
  exact (classicalTerm_unit_bound B (r+1) u hu).trans (by
    simpa [weight, mul_div_assoc] using hB (r+1) (by omega))

lemma rate_dominated (B : ∀ m, HN L m →L[ℂ] HN L m) (M A K : ℝ)
    (hB : FactorialBound B M A) (_hK : 0 ≤ K) (u v : L2T L) (hu : ‖u‖ = 1)
    (hv : ‖v‖ ≤ K) (r : ℕ) :
    ‖classicalRate B (r+1) u v‖ ≤ (2*K*M) * weight 1 A (r+1) := by
  calc
    _ ≤ 2 * ((r+1 : ℕ) : ℝ) * ‖B (r+1)‖ * ‖v‖ := classicalRate_bound B (r+1) u v hu
    _ ≤ 2 * ((r+1 : ℕ) : ℝ) * (M * A^(r+1) /
        Real.sqrt ((2*(r+1)).factorial : ℝ)) * K := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hB (r+1) (by omega)) (by positivity)
      · exact hv
      · exact norm_nonneg v
      · have h := (norm_nonneg (B (r+1))).trans (hB (r+1) (by omega))
        positivity
    _ = _ := by unfold weight; ring

/-- Full-series differentiation: the derivative series is proved summable
from the factorial bound and the speed estimate, not assumed. -/
theorem classicalSeries_hasDerivAt (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A K : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) (hK : 0 ≤ K)
    (u v : ℝ → L2T L) (hu : ∀ t, HasDerivAt u (v t) t)
    (hn : ∀ t, ‖u t‖ = 1) (hv : ∀ t, ‖v t‖ ≤ K) (t : ℝ) :
    HasDerivAt (fun s => classicalSeries B (u s)) (classicalSeriesRate B (u t) (v t)) t := by
  unfold classicalSeries classicalSeriesRate
  apply hasDerivAt_tsum
    (((summable_nat_add_iff 1).mpr (weight_summable 1 A hA)).mul_left (2*K*M))
    (fun r s => classicalTerm_time B (r+1) u (v s) s (hu s))
    (fun r s => rate_dominated B M A K hB hK (u s) (v s) (hn s) (hv s) r)
    (classical_summable B M A hA hB (u 0) (hn 0))

/-- The derivative sum is continuous for a C1 unit path. -/
theorem classicalSeriesRate_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A K : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) (hK : 0 ≤ K)
    (u v : ℝ → L2T L) (hu : ContDiff ℝ 1 u)
    (hd : ∀ t, HasDerivAt u (v t) t) (hn : ∀ t, ‖u t‖ = 1)
    (hv : ∀ t, ‖v t‖ ≤ K) :
    Continuous (fun t => classicalSeriesRate B (u t) (v t)) := by
  unfold classicalSeriesRate
  apply continuous_tsum _
    (((summable_nat_add_iff 1).mpr (weight_summable 1 A hA)).mul_left (2*K*M))
    (fun r t => rate_dominated B M A K hB hK (u t) (v t) (hn t) (hv t) r)
  intro r
  have hh := ((classicalTerm_smooth B (r+1) 1).comp hu).continuous_deriv_one
  have heq : deriv (fun t => classicalTerm B (r+1) (u t)) =
      fun t => classicalRate B (r+1) (u t) (v t) := by
    funext t
    exact (classicalTerm_time B (r+1) u (v t) t (hd t)).deriv
  change Continuous (deriv (fun t => classicalTerm B (r+1) (u t))) at hh
  rwa [heq] at hh

/-- C1 regularity of the full, positively ranked classical factorial series. -/
theorem classicalSeries_time_C1 (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A K : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) (hK : 0 ≤ K)
    (u v : ℝ → L2T L) (hu : ContDiff ℝ 1 u)
    (hd : ∀ t, HasDerivAt u (v t) t) (hn : ∀ t, ‖u t‖ = 1)
    (hv : ∀ t, ‖v t‖ ≤ K) : ContDiff ℝ 1 (fun t => classicalSeries B (u t)) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · intro t
    exact (classicalSeries_hasDerivAt B M A K hA hB hK u v hd hn hv t).differentiableAt
  · have hh := classicalSeriesRate_continuous B M A K hA hB hK u v hu hd hn hv
    have heq : deriv (fun t => classicalSeries B (u t)) =
        fun t => classicalSeriesRate B (u t) (v t) := by
      funext t
      exact (classicalSeries_hasDerivAt B M A K hA hB hK u v hd hn hv t).deriv
    rwa [heq]

end QuantumNLS.Prop022ClassicalTimeR116
#print axioms QuantumNLS.Prop022ClassicalTimeR116.powerDifferential_unit_bound
#print axioms QuantumNLS.Prop022ClassicalTimeR116.classicalSeries_hasDerivAt
#print axioms QuantumNLS.Prop022ClassicalTimeR116.classicalSeries_time_C1

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022ClassicalTimeR116." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022ClassicalTimeR116." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R116 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
