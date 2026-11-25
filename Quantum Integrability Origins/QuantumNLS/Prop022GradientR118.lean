import QuantumNLS.Prop022SymmetricSlotR117
import QuantumNLS.Prop022ActualProfileR117

/-! Full real Frechet differentiation of the factorial Hamiltonian and its
identification with the literal source first-slot Hartree gradient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped InnerProductSpace ComplexConjugate Topology ContDiff
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
namespace QuantumNLS.Prop022GradientR118
open TensorCarrier PhysicalTensor BetheCoefficientTransform TensorPlacements
open Prop022TensorCompressionR115 Prop022TensorCalculusR116 Prop022ClassicalTimeR116
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022SymmetricSlotR117
variable {L : ℝ} [Fact (0 < L)]
local instance : AddCommGroup (L2T L) := (inferInstance : NormedAddCommGroup (L2T L)).toAddCommGroup
local instance (n : ℕ) : AddCommGroup (HilbertTensorPower ℂ (L2T L) n) :=
  (inferInstance : NormedAddCommGroup (HilbertTensorPower ℂ (L2T L) n)).toAddCommGroup

lemma power_hasFDerivAt (m : ℕ) (u : L2T L) :
    HasFDerivAt (power (L := L) m) (powerD m u) u := by
  have hh := ((physSector L m).orthogonalProjectionOnto.restrictScalars ℝ).hasFDerivAt.comp
    u (htpow_hasFDerivAt m u)
  convert hh using 1
  · funext v
    exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (power m v)).symm
  · rfl

/-- The derivative functional, whose formula below is proved by the chain rule. -/
def classicalD (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (u : L2T L) : L2T L →L[ℝ] ℝ :=
  fderiv ℝ (classicalTerm B m) u

lemma classicalD_apply (B : ∀ m, HN L m →L[ℂ] HN L m) (m : ℕ) (u h : L2T L) :
    classicalD B m u h = classicalRate B m u h := by
  have hp := power_hasFDerivAt m u
  have hh := Complex.reCLM.hasFDerivAt.comp u
    (hp.inner ℂ (((B m).restrictScalars ℝ).hasFDerivAt.comp u hp))
  change HasFDerivAt (classicalTerm B m) _ u at hh
  rw [classicalD, hh.fderiv]
  rfl

lemma powerD_eq_first (r : ℕ) (u h : L2T L) :
    powerD (r+1) u h = ((r+1 : ℕ) : ℝ) •
      (physSector L (r+1)).orthogonalProjectionOnto (Ext025A8.insertFirst r u h) := by
  classical
  rw [powerD_eq_insertion, insertion_one_slot]
  congr 1
  rw [projected_slots_eq (r+1) u h (Fin.last r) 0]
  congr 1
  change tensorMultilinear (r+1) (Function.update (fun _ => u) 0 h) =
    tensorMultilinear (r+1) (Fin.cons h (fun _ => u))
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma symProjToSector_power (m : ℕ) (u : L2T L) :
    symProjToSector m (htpow m u) = power m u := by
  apply Subtype.ext
  change symProj ℂ (L2T L) m (htpow m u) = htpow m u
  rw [symProj_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (htpow_mem_symSector m u)

/-- Literal source gradient term: no gradient formula is assumed. -/
def gradientTerm (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (u : L2T L) : L2T L :=
  Ext025A8.hartreeTerm (fun n => extendSymKernel (B (n+1))) r u

lemma gradientTerm_pairing (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (u h : L2T L) :
    ⟪h, gradientTerm B r u⟫_ℂ = ((r+1 : ℕ) : ℂ) *
      ⟪(physSector L (r+1)).orthogonalProjectionOnto (Ext025A8.insertFirst r u h),
        B (r+1) (power (r+1) u)⟫_ℂ := by
  unfold gradientTerm Ext025A8.hartreeTerm
  rw [inner_smul_right, Ext025A8.hartreeContraction_pairing, Ext025A8.insertFirst_self]
  congr 1
  change ⟪Ext025A8.insertFirst r u h,
    (B (r+1) (symProjToSector (r+1) (htpow (r+1) u)) :
      HilbertTensorPower ℂ (L2T L) (r+1))⟫_ℂ = _
  rw [symProjToSector_power]
  exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (B (r+1) (power (r+1) u)) (Ext025A8.insertFirst r u h)).symm

lemma inner_smul_left_real {m : ℕ} (x y : HN L m) (c : ℝ) :
    ⟪c • x, y⟫_ℂ = c • ⟪x,y⟫_ℂ := by
  change ⟪(c : ℂ) • x, y⟫_ℂ = (c : ℂ) * ⟪x,y⟫_ℂ
  simp only [inner_smul_left, Complex.conj_ofReal]

/-- Exact physical convention dF[h] = 2 Re <grad F,h>, at each rank. -/
theorem classicalD_eq_gradientTerm (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (r : ℕ) (u h : L2T L) :
    classicalD B (r+1) u h = 2 * (⟪h, gradientTerm B r u⟫_ℂ).re := by
  rw [classicalD_apply, classicalRate]
  have he : (⟪power (r+1) u, B (r+1) (powerD (r+1) u h)⟫_ℂ).re =
      (⟪powerD (r+1) u h, B (r+1) (power (r+1) u)⟫_ℂ).re := by
    rw [← adjoint_inner_left, hs]
    exact inner_re_symm (𝕜 := ℂ) _ _
  rw [Complex.add_re, he, powerD_eq_first, inner_smul_left_real, gradientTerm_pairing]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma gradientTerm_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (r : ℕ) (u : L2T L) :
    ‖gradientTerm B r u‖ ≤ ((r+1 : ℕ) : ℝ) * ‖B (r+1)‖ * ‖u‖^(2*r+1) := by
  exact (Ext025A8.hartreeTerm_norm _ r u).trans (by
    gcongr
    exact norm_extendSymKernel_le (B (r+1)))

/-- A summable majorant on any fixed ball. -/
lemma gradientTerm_ball_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A R : ℝ)
    (hB : FactorialBound B M A) (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) (r : ℕ) :
    ‖gradientTerm B r u‖ ≤ M * weight 1 (A * R^2) (r+1) := by
  calc
    _ ≤ ((r+1 : ℕ) : ℝ) * ‖B (r+1)‖ * R^(2*(r+1)) := by
      apply (gradientTerm_bound B r u).trans
      gcongr
      exact (pow_le_pow_left₀ (norm_nonneg u) hu _).trans (pow_le_pow_right₀ hR (by omega))
    _ ≤ ((r+1 : ℕ) : ℝ) * (M * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) * R^(2*(r+1)) := by
      gcongr
      exact hB (r+1) (by omega)
    _ = _ := by unfold weight; simp only [mul_pow, pow_mul]; ring

lemma classicalD_ball_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A R : ℝ) (hB : FactorialBound B M A)
    (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) (r : ℕ) :
    ‖classicalD B (r+1) u‖ ≤ 2 * (M * weight 1 (A * R^2) (r+1)) := by
  have hb := gradientTerm_ball_bound B M A R hB hR u hu r
  apply opNorm_le_bound _ (by linarith [norm_nonneg (gradientTerm B r u)])
  intro h
  rw [classicalD_eq_gradientTerm B hs, norm_mul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (‖h‖ * ‖gradientTerm B r u‖) :=
      mul_le_mul_of_nonneg_left ((norm_realPart_le _).trans (norm_inner_le_norm _ _)) (by norm_num)
    _ ≤ 2 * (M * weight 1 (A * R^2) (r+1)) * ‖h‖ := by nlinarith [norm_nonneg h]

lemma classicalTerm_ball_bound (B : ∀ m, HN L m →L[ℂ] HN L m) (M A R : ℝ)
    (hB : FactorialBound B M A) (hR : 0 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) (r : ℕ) :
    ‖classicalTerm B (r+1) u‖ ≤ M * weight 0 (A * R^2) (r+1) := by
  calc
    _ ≤ ‖power (r+1) u‖ * (‖B (r+1)‖ * ‖power (r+1) u‖) :=
      (norm_realPart_le _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)))
    _ ≤ R^(r+1) * ((M * A^(r+1) / Real.sqrt ((2*(r+1)).factorial : ℝ)) * R^(r+1)) := by
      have hpos := (norm_nonneg (B (r+1))).trans (hB (r+1) (by omega))
      rw [power_norm]
      gcongr
      exact hB (r+1) (by omega)
    _ = _ := by unfold weight; simp only [mul_pow, pow_zero, one_mul]; ring

/-- The full source first-slot gradient. -/
def gradient (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L :=
  ∑' r, gradientTerm B r u

theorem gradient_summable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A R : ℝ)
    (hA : 0 ≤ A) (hB : FactorialBound B M A) (hR : 1 ≤ R) (u : L2T L) (hu : ‖u‖ ≤ R) :
    Summable (fun r => gradientTerm B r u) := by
  exact Summable.of_norm_bounded
    (((summable_nat_add_iff 1).mpr (weight_summable 1 (A*R^2) (by positivity))).mul_left M)
    (gradientTerm_ball_bound B M A R hB hR u hu)

def seriesD (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) : L2T L →L[ℝ] ℝ :=
  ∑' r, classicalD B (r+1) u

/-- Frechet differentiation in an open ball, proved using local factorial
majorants; unit-sphere time differentiation alone is not used for this. -/
theorem classicalSeries_hasFDerivAt (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) :
    HasFDerivAt (classicalSeries B) (seriesD B u) u := by
  let R := ‖u‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg u]
  have hu : u ∈ Metric.ball (0 : L2T L) R := by simp [R]
  apply hasFDerivAt_tsum_of_isPreconnected
    ((((summable_nat_add_iff 1).mpr (weight_summable 1 (A*R^2) (by positivity))).mul_left M).mul_left 2)
    Metric.isOpen_ball (convex_ball (0 : L2T L) R).isPreconnected
    (fun r v _ => (classicalTerm_smooth B (r+1) 1).differentiable (by norm_num) v |>.hasFDerivAt)
    (fun r v hv => classicalD_ball_bound B hs M A R hB hR v (by simpa using (Metric.mem_ball.mp hv).le) r)
    hu
    (Summable.of_norm_bounded
      (((summable_nat_add_iff 1).mpr (weight_summable 0 (A*R^2) (by positivity))).mul_left M)
      (classicalTerm_ball_bound B M A R hB (by positivity) u (by dsimp [R]; linarith))) hu

/-- The infinite-series differential equals twice the real inner product with
the actual source gradient, with convergence proved from the factorial bound. -/
theorem seriesD_eq_gradient (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hs : ∀ m, (B m).adjoint = B m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u h : L2T L) :
    seriesD B u h = 2 * (⟪gradient B u, h⟫_ℂ).re := by
  let R := ‖u‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg u]
  have hu : ‖u‖ ≤ R := by dsimp [R]; linarith
  have hg := gradient_summable B M A R hA hB hR u hu
  have hd : Summable (fun r => classicalD B (r+1) u) :=
    Summable.of_norm_bounded
      ((((summable_nat_add_iff 1).mpr (weight_summable 1 (A*R^2) (by positivity))).mul_left M).mul_left 2)
      (classicalD_ball_bound B hs M A R hB hR u hu)
  have ha := (ContinuousLinearMap.apply ℝ ℝ h).map_tsum hd
  change (∑' r, classicalD B (r+1) u) h = ∑' r, classicalD B (r+1) u h at ha
  rw [seriesD, ha]
  simp_rw [classicalD_eq_gradientTerm B hs]
  rw [tsum_mul_left]
  congr 1
  have hh := (Complex.reCLM.comp ((innerSL ℂ h).restrictScalars ℝ)).map_tsum hg
  change (⟪h, ∑' r, gradientTerm B r u⟫_ℂ).re = ∑' r, (⟪h, gradientTerm B r u⟫_ℂ).re at hh
  rw [← hh, gradient]
  exact inner_re_symm (𝕜 := ℂ) _ _

/-- The accepted actual source trajectory solves precisely -i grad F. -/
theorem velocity_eq_neg_I_gradient (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    Prop022ActualProfileR117.velocity B u = (-Complex.I) • gradient B u := rfl

end QuantumNLS.Prop022GradientR118
#print axioms QuantumNLS.Prop022GradientR118.classicalSeries_hasFDerivAt
#print axioms QuantumNLS.Prop022GradientR118.seriesD_eq_gradient
#print axioms QuantumNLS.Prop022GradientR118.velocity_eq_neg_I_gradient

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022GradientR118." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022GradientR118." then
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
