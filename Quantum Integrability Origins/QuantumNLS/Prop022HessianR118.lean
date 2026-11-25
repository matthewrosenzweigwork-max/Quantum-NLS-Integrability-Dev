import QuantumNLS.Prop022SecondSlotR118
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Local factorial majorants for the second Frechet derivative of the full
classical Hamiltonian. No evolution estimates are inputs to this result. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022HessianR118
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022TensorCompressionR115 Prop022TensorCalculusR116 Prop022ClassicalTimeR116
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
open Prop022GradientR118 Prop022SecondSlotR118
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

lemma powerDifferential_ball_bound (m : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (u h : L2T L) (hu : ‖u‖ ≤ R) :
    ‖powerDifferential m u h‖ ≤ (m : ℝ) * R^m * ‖h‖ := by
  classical
  unfold powerDifferential
  rw [sum_apply]
  calc
    _ ≤ ∑ i : Fin m, ‖((tensorMultilinear (L := L) m).restrictScalars ℝ).toContinuousLinearMap
        (fun _ => u) i h‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, R^m * ‖h‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖tensorMultilinear m (Function.update (fun _ => u) i h)‖ ≤ _
      rw [tensorMultilinear_apply, UniformSpace.Completion.norm_coe, norm_ptprod]
      have he : (fun j => ‖Function.update (fun _ : Fin m => u) i h j‖) =
          Function.update (fun _ : Fin m => ‖u‖) i ‖h‖ := by
        funext j
        by_cases hj : j = i <;> simp [hj]
      rw [he, Finset.prod_update_of_mem (Finset.mem_univ i)]
      rw [Finset.prod_const]
      have hc : (Finset.univ \ {i} : Finset (Fin m)).card ≤ m := by
        simpa using Finset.card_le_card (Finset.sdiff_subset :
          (Finset.univ \ {i} : Finset (Fin m)) ⊆ Finset.univ)
      have hp : ‖u‖ ^ (Finset.univ \ {i} : Finset (Fin m)).card ≤ R^m :=
        (pow_le_pow_left₀ (norm_nonneg u) hu _).trans (pow_le_pow_right₀ hR hc)
      nlinarith [norm_nonneg h]
    _ = _ := by simp; ring

lemma powerD_ball_bound (m : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (u h : L2T L) (hu : ‖u‖ ≤ R) :
    ‖powerD m u h‖ ≤ (m : ℝ) * R^m * ‖h‖ := by
  change ‖(physSector L m).orthogonalProjectionOnto (powerDifferential m u h)‖ ≤ _
  exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans
    (powerDifferential_ball_bound m R hR u h hu)

lemma powerDD_ball_bound (r : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (u h k : L2T L) (hu : ‖u‖ ≤ R) :
    ‖powerDD r u h k‖ ≤ ((r+1 : ℕ) : ℝ)^2 * R^(r+1) * ‖h‖ * ‖k‖ := by
  change ‖((r+1 : ℕ) : ℝ) • appendFixed r h (powerDifferential r u k)‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ((r+1 : ℕ) : ℝ))]
  calc
    _ ≤ ((r+1 : ℕ) : ℝ) * ((r : ℝ) * R^r * ‖k‖ * ‖h‖) := by
      gcongr
      exact (appendFixed_norm r h _).trans
        (mul_le_mul_of_nonneg_right (powerDifferential_ball_bound r R hR u k hu) (norm_nonneg h))
    _ ≤ ((r+1 : ℕ) : ℝ) * (((r+1 : ℕ) : ℝ) * R^(r+1) * ‖k‖ * ‖h‖) := by
      gcongr <;> norm_num
    _ = _ := by ring

lemma inner_B_bound {m : ℕ} (B : HN L m →L[ℂ] HN L m) (x y : HN L m) :
    ‖⟪x, B y⟫_ℂ‖ ≤ ‖x‖ * (‖B‖ * ‖y‖) :=
  (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg x))

/-- A proved operator-norm Hessian majorant on every fixed ball. -/
lemma classicalHessian_ball_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (r : ℕ) (R : ℝ) (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) :
    ‖classicalHessian B (r+1) u‖ ≤ 4 * ((r+1 : ℕ) : ℝ)^2 * ‖B (r+1)‖ * R^(2*(r+1)) := by
  have hp : ‖power (r+1) u‖ ≤ R^(r+1) := by rw [power_norm]; gcongr
  have hd := powerD_ball_bound (r+1) R hR u
  have hdd := powerDD_ball_bound r R hR u
  apply opNorm_le_bound _ (by positivity)
  intro k
  apply opNorm_le_bound _ (by positivity)
  intro h
  rw [classicalHessian_apply]
  calc
    _ ≤ ‖⟪powerD (r+1) u k, B (r+1) (powerD (r+1) u h)⟫_ℂ +
        ⟪power (r+1) u, B (r+1) (powerDD r u h k)⟫_ℂ +
        (⟪powerDD r u h k, B (r+1) (power (r+1) u)⟫_ℂ +
        ⟪powerD (r+1) u h, B (r+1) (powerD (r+1) u k)⟫_ℂ)‖ := norm_realPart_le _
    _ ≤ (‖powerD (r+1) u k‖ * (‖B (r+1)‖ * ‖powerD (r+1) u h‖) +
        ‖power (r+1) u‖ * (‖B (r+1)‖ * ‖powerDD r u h k‖)) +
        (‖powerDD r u h k‖ * (‖B (r+1)‖ * ‖power (r+1) u‖) +
        ‖powerD (r+1) u h‖ * (‖B (r+1)‖ * ‖powerD (r+1) u k‖)) := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (inner_B_bound _ _ _) (inner_B_bound _ _ _)))
        ((norm_add_le _ _).trans (add_le_add (inner_B_bound _ _ _) (inner_B_bound _ _ _))))
    _ ≤ (((r+1 : ℕ) : ℝ) * R^(r+1) * ‖k‖ *
          (‖B (r+1)‖ * (((r+1 : ℕ) : ℝ) * R^(r+1) * ‖h‖)) +
        R^(r+1) * (‖B (r+1)‖ * (((r+1 : ℕ) : ℝ)^2 * R^(r+1) * ‖h‖ * ‖k‖))) +
        ((((r+1 : ℕ) : ℝ)^2 * R^(r+1) * ‖h‖ * ‖k‖) * (‖B (r+1)‖ * R^(r+1)) +
        (((r+1 : ℕ) : ℝ) * R^(r+1) * ‖h‖) *
          (‖B (r+1)‖ * (((r+1 : ℕ) : ℝ) * R^(r+1) * ‖k‖))) := by
      gcongr <;> first | exact hp | exact hd _ hu | exact hdd _ _ hu
    _ = (4 * ((r+1 : ℕ) : ℝ)^2 * ‖B (r+1)‖ * R^(2*(r+1)) * ‖k‖) * ‖h‖ := by
      rw [pow_mul, pow_two]
      ring

lemma hessian_dominated (B : ∀ m, HN L m →L[ℂ] HN L m) (M A R : ℝ)
    (hB : FactorialBound B M A) (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) (r : ℕ) :
    ‖classicalHessian B (r+1) u‖ ≤ (4*M) * weight 2 (A*R^2) (r+1) := by
  calc
    _ ≤ 4 * ((r+1 : ℕ) : ℝ)^2 * ‖B (r+1)‖ * R^(2*(r+1)) :=
      classicalHessian_ball_bound B r R hR u hu
    _ ≤ 4 * ((r+1 : ℕ) : ℝ)^2 *
        (M * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) * R^(2*(r+1)) := by
      gcongr
      exact hB (r+1) (by omega)
    _ = _ := by unfold weight; rw [mul_pow, pow_mul]; ring

def seriesHessian (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    L2T L →L[ℝ] L2T L →L[ℝ] ℝ := ∑' r, classicalHessian B (r+1) u

lemma hessian_summable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A R : ℝ)
    (hA : 0 ≤ A) (hB : FactorialBound B M A) (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) :
    Summable (fun r => classicalHessian B (r+1) u) := by
  apply Summable.of_norm_bounded (f := fun r => classicalHessian B (r+1) u)
    (((summable_nat_add_iff 1).mpr (weight_summable 2 (A*R^2) (by positivity))).mul_left (4*M))
  intro r
  exact hessian_dominated B M A R hB hR u hu r

/-- Full second Frechet derivative. Its series convergence and all local
operator-norm bounds are conclusions of the factorial kernel hypothesis. -/
theorem classicalSeries_hasSecondFDerivAt (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) :
    HasFDerivAt (fderiv ℝ (classicalSeries B)) (seriesHessian B u) u := by
  have he : fderiv ℝ (classicalSeries B) = seriesD B := by
    funext v
    exact (classicalSeries_hasFDerivAt B hs M A hA hB v).fderiv
  rw [he]
  let R := ‖u‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg u]
  have hu : u ∈ Metric.ball (0 : L2T L) R := by simp [R]
  apply hasFDerivAt_tsum_of_isPreconnected
    (((summable_nat_add_iff 1).mpr (weight_summable 2 (A*R^2) (by positivity))).mul_left (4*M))
    Metric.isOpen_ball (convex_ball (0 : L2T L) R).isPreconnected
    (fun r v _ => (classicalD_smooth B (r+1)).differentiable (by norm_num) v |>.hasFDerivAt)
    (fun r v hv => hessian_dominated B M A R hB hR v (by simpa using (Metric.mem_ball.mp hv).le) r)
    hu
    (Summable.of_norm_bounded
      ((((summable_nat_add_iff 1).mpr (weight_summable 1 (A*R^2) (by positivity))).mul_left M).mul_left 2)
      (classicalD_ball_bound B hs M A R hB hR u (by dsimp [R]; linarith))) hu

lemma classicalHessian_symmetric (B : ∀ m, HN L m →L[ℂ] HN L m)
    (m : ℕ) (u h k : L2T L) :
    classicalHessian B m u h k = classicalHessian B m u k h :=
  ((classicalTerm_smooth B m 2).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq h k

/-- Every Hessian entry follows from its diagonal by real polarization. -/
theorem seriesHessian_polarization (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) (u h k : L2T L) :
    2 * seriesHessian B u h k = seriesHessian B u (h+k) (h+k) -
      seriesHessian B u h h - seriesHessian B u k k := by
  have hh := hessian_summable B M A (‖u‖+1) hA hB
    (by linarith [norm_nonneg u]) u (by linarith)
  have he (a b : L2T L) : seriesHessian B u a b =
      ∑' r, classicalHessian B (r+1) u a b := by
    have hm := (ContinuousLinearMap.apply ℝ ℝ b).comp (ContinuousLinearMap.apply ℝ (L2T L →L[ℝ] ℝ) a) |>.map_tsum hh
    exact hm
  have hsym : seriesHessian B u k h = seriesHessian B u h k := by
    rw [he, he]
    exact tsum_congr (fun r => classicalHessian_symmetric B (r+1) u k h)
  simp only [map_add, add_apply]
  rw [hsym]
  ring

/-- C2 regularity follows from the locally uniform Hessian majorants. -/
theorem seriesHessian_continuous (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A) :
    Continuous (seriesHessian B) := by
  rw [continuous_iff_continuousAt]
  intro u
  let R := ‖u‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg u]
  have hu : u ∈ Metric.ball (0 : L2T L) R := by simp [R]
  have hc : ContinuousOn (seriesHessian B) (Metric.ball (0 : L2T L) R) :=
    continuousOn_tsum
      (fun r => ((classicalD_smooth B (r+1)).continuous_fderiv (by norm_num)).continuousOn)
      (((summable_nat_add_iff 1).mpr (weight_summable 2 (A*R^2) (by positivity))).mul_left (4*M))
      (fun r v hv => hessian_dominated B M A R hB hR v (by simpa using (Metric.mem_ball.mp hv).le) r)
  exact hc.continuousAt (Metric.isOpen_ball.mem_nhds hu)

theorem classicalSeries_C2 (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) : ContDiff ℝ 2 (classicalSeries B) := by
  have h1 := fun u => classicalSeries_hasFDerivAt B hs M A hA hB u
  have h2 := fun u => classicalSeries_hasSecondFDerivAt B hs M A hA hB u
  have he : fderiv ℝ (fderiv ℝ (classicalSeries B)) = seriesHessian B :=
    funext (fun u => (h2 u).fderiv)
  apply (contDiff_succ_iff_fderiv (n := (1 : ℕ∞ω))).mpr
  refine ⟨fun u => (h1 u).differentiableAt, by norm_num, ?_⟩
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun u => (h2 u).differentiableAt, ?_⟩
  rw [he]
  exact seriesHessian_continuous B M A hA hB

lemma classicalHessian_one (B : ∀ m, HN L m →L[ℂ] HN L m) (u h : L2T L) :
    classicalHessian B 1 u h h =
      2 * (⟪power 1 h, mixedTerm B u 0 (power 1 h)⟫_ℂ).re := by
  rw [classicalHessian_apply B 0]
  simp [powerDD_one, Prop022SymmetricSlotR117.powerD_eq_insertion, mixedTerm,
    adjoint_inner_right, comp_apply]
  ring

/-- The real quadratic diagonal determined by the two literal report contractions. -/
def coefficientDiagonal (B : ∀ m, HN L m →L[ℂ] HN L m) (u h : L2T L) : ℝ :=
  2 * (⟪power 1 h, numberCoefficient B u (power 1 h)⟫_ℂ).re +
  2 * (⟪power 2 h, pairCoefficient B u⟫_ℂ).re

/-- Full-series diagonal identification, with each reindexing and every
interchange of evaluation and summation justified by proved summability. -/
theorem seriesHessian_eq_coefficients_diagonal (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u h : L2T L) (hu : ‖u‖ = 1) :
    seriesHessian B u h h = coefficientDiagonal B u h := by
  let evA : (HN L 1 →L[ℂ] HN L 1) →L[ℝ] ℝ :=
    (2 : ℝ) • ((Complex.reCLM.comp ((innerSL ℂ (power 1 h)).restrictScalars ℝ)).comp
      ((ContinuousLinearMap.apply ℂ (HN L 1) (power 1 h)).restrictScalars ℝ))
  let evB : HN L 2 →L[ℝ] ℝ :=
    (2 : ℝ) • (Complex.reCLM.comp ((innerSL ℂ (power 2 h)).restrictScalars ℝ))
  let a := fun r => evA (mixedTerm B u r)
  let b := fun r => evB (pairTerm B u r)
  have hm := mixed_summable B M A hA hB u hu
  have hp := Prop022FactorialCoefficientsR115.pair_summable B M A hA hB u hu
  have ha : Summable a := evA.summable hm
  have hb : Summable b := evB.summable hp
  have hAeq : evA (numberCoefficient B u) = ∑' r, a r := evA.map_tsum hm
  have hBeq : evB (pairCoefficient B u) = ∑' r, b r := evB.map_tsum hp
  have hh := hessian_summable B M A 1 hA hB (by norm_num) u hu.le
  let evH := (ContinuousLinearMap.apply ℝ ℝ h).comp
    (ContinuousLinearMap.apply ℝ (L2T L →L[ℝ] ℝ) h)
  have hHs := evH.summable hh
  change Summable (fun r => classicalHessian B (r+1) u h h) at hHs
  have hHeq := evH.map_tsum hh
  change seriesHessian B u h h = ∑' r, classicalHessian B (r+1) u h h at hHeq
  calc
    _ = classicalHessian B 1 u h h + ∑' r, classicalHessian B (r+2) u h h := by
      rw [hHeq]
      simpa only [Finset.sum_range_one, Nat.zero_add, Nat.add_assoc] using (hHs.sum_add_tsum_nat_add 1).symm
    _ = a 0 + ∑' r, (a (r+1) + b r) := by
      rw [classicalHessian_one]
      congr 1
      exact tsum_congr (fun r => classicalHessian_diagonal B hs r u h)
    _ = a 0 + ((∑' r, a (r+1)) + ∑' r, b r) := by
      rw [Summable.tsum_add ((summable_nat_add_iff 1).mpr ha) hb]
    _ = (∑' r, a r) + ∑' r, b r := by
      have he : a 0 + (∑' r, a (r+1)) = ∑' r, a r := by
        simpa only [Finset.sum_range_one] using (ha.sum_add_tsum_nat_add 1)
      linarith
    _ = coefficientDiagonal B u h := by
      rw [← hAeq, ← hBeq]
      rfl

/-- All real Hessian entries are now identified, not just its diagonal. -/
theorem seriesHessian_eq_coefficients (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u h k : L2T L) (hu : ‖u‖ = 1) :
    2 * seriesHessian B u h k = coefficientDiagonal B u (h+k) -
      coefficientDiagonal B u h - coefficientDiagonal B u k := by
  rw [seriesHessian_polarization B M A hA hB,
    seriesHessian_eq_coefficients_diagonal B hs M A hA hB u (h+k) hu,
    seriesHessian_eq_coefficients_diagonal B hs M A hA hB u h hu,
    seriesHessian_eq_coefficients_diagonal B hs M A hA hB u k hu]

end QuantumNLS.Prop022HessianR118
#print axioms QuantumNLS.Prop022HessianR118.classicalSeries_hasSecondFDerivAt
#print axioms QuantumNLS.Prop022HessianR118.seriesHessian_polarization
#print axioms QuantumNLS.Prop022HessianR118.classicalSeries_C2
#print axioms QuantumNLS.Prop022HessianR118.seriesHessian_eq_coefficients

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022HessianR118." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022HessianR118." then
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
  Lean.logInfo m!"R118 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
