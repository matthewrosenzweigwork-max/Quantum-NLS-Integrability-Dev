import QuantumNLS.L1SpatialTransfer
import QuantumNLS.RealAnalyticDef

/-! A bounded bilinear Volterra operator for genuinely L1 coefficient families.
Linearity of representatives is required only almost everywhere. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Interval
namespace QuantumNLS.DEF014VolterraOperator
variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable {L : ℝ} (hL : 0 ≤ L)
abbrev Path (L : ℝ) (𝔸 : Type*) [TopologicalSpace 𝔸] := C(Icc (0 : ℝ) L, 𝔸)

def extend (f : Path L 𝔸) : ℝ → 𝔸 := IccExtend hL f

theorem continuous_extend (f : Path L 𝔸) : Continuous (extend hL f) :=
  f.continuous.comp continuous_projIcc

/-- The data express a bounded real-linear map into L1; no analytic conclusion is input. -/
structure Family (E 𝔸 : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] (L : ℝ) where
  coef : E → ℝ → 𝔸
  integrable : ∀ e, IntervalIntegrable (coef e) volume 0 L
  add_ae : ∀ e f, coef (e + f) =ᵐ[volume.restrict (Ioc 0 L)] fun t => coef e t + coef f t
  smul_ae : ∀ (c : ℝ) e, coef (c • e) =ᵐ[volume.restrict (Ioc 0 L)] fun t => c • coef e t
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_integral_le : ∀ e, (∫ t in (0 : ℝ)..L, ‖coef e t‖) ≤ bound * ‖e‖

variable (A : Family E 𝔸 L)

def applyPath (e : E) (f : Path L 𝔸) : Path L 𝔸 where
  toFun x := ∫ t in (0 : ℝ)..x.1, A.coef e t * extend hL f t
  continuous_toFun := by
    have hi := (A.integrable e).mul_continuousOn (continuous_extend hL f).continuousOn
    have hc := intervalIntegral.continuousOn_primitive_interval
      ((intervalIntegrable_iff' (by finiteness)).mp hi)
    rw [uIcc_of_le hL] at hc
    exact hc.domRestrict

theorem norm_applyPath_le (e : E) (f : Path L 𝔸) :
    ‖applyPath hL A e f‖ ≤ A.bound * ‖e‖ * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg A.bound_nonneg (norm_nonneg e)) (norm_nonneg f))).mpr
  intro x
  change ‖∫ t in (0 : ℝ)..x.1, A.coef e t * extend hL f t‖ ≤ _
  have hsub : uIcc (0 : ℝ) x.1 ⊆ uIcc (0 : ℝ) L := by
    rw [uIcc_of_le x.2.1, uIcc_of_le hL]
    exact Icc_subset_Icc_right x.2.2
  have hAx := (A.integrable e).mono_set hsub
  calc
    _ ≤ ∫ t in (0 : ℝ)..x.1, ‖A.coef e t‖ * ‖f‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm x.2.1).trans ?_
      apply intervalIntegral.integral_mono_on x.2.1
        (hAx.mul_continuousOn (continuous_extend hL f).continuousOn).norm
        (hAx.norm.mul_const _) fun t _ => ?_
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (f.norm_coe_le_norm _) (norm_nonneg _))
    _ = (∫ t in (0 : ℝ)..x.1, ‖A.coef e t‖) * ‖f‖ :=
      intervalIntegral.integral_mul_const _ _
    _ ≤ (∫ t in (0 : ℝ)..L, ‖A.coef e t‖) * ‖f‖ := by
      gcongr
      exact intervalIntegral.integral_mono_interval le_rfl x.2.1 x.2.2
        (Filter.Eventually.of_forall (fun t => norm_nonneg _)) (A.integrable e).norm
    _ ≤ A.bound * ‖e‖ * ‖f‖ :=
      mul_le_mul_of_nonneg_right (A.norm_integral_le e) (norm_nonneg _)

def linear : E →ₗ[ℝ] Path L 𝔸 →ₗ[ℝ] Path L 𝔸 where
  toFun e :=
    { toFun := applyPath hL A e
      map_add' := by
        intro f g
        ext x
        change (∫ t in (0 : ℝ)..x.1, A.coef e t * (extend hL (f + g) t)) = _
        simp only [extend, IccExtend, Function.comp_apply, ContinuousMap.add_apply, mul_add]
        exact intervalIntegral.integral_add
          (((A.integrable e).mul_continuousOn (continuous_extend hL f).continuousOn).mono_set
            (by rw [uIcc_of_le x.2.1, uIcc_of_le hL]; exact Icc_subset_Icc_right x.2.2))
          (((A.integrable e).mul_continuousOn (continuous_extend hL g).continuousOn).mono_set
            (by rw [uIcc_of_le x.2.1, uIcc_of_le hL]; exact Icc_subset_Icc_right x.2.2))
      map_smul' := by
        intro c f
        ext x
        simp only [applyPath, ContinuousMap.coe_mk, extend, IccExtend,
          Function.comp_apply, ContinuousMap.smul_apply, mul_smul_comm, RingHom.id_apply]
        exact intervalIntegral.integral_smul c _ }
  map_add' := by
    intro e d
    ext f x
    change (∫ t in (0 : ℝ)..x.1, A.coef (e + d) t * extend hL f t) = _
    have hsub : Ioc (0 : ℝ) x.1 ⊆ Ioc 0 L := Ioc_subset_Ioc_right x.2.2
    rw [intervalIntegral.integral_of_le x.2.1]
    have hae := ae_restrict_of_ae_restrict_of_subset hsub (A.add_ae e d)
    calc
      _ = ∫ t in Ioc (0 : ℝ) x.1, A.coef e t * extend hL f t +
          A.coef d t * extend hL f t := integral_congr_ae (hae.mono fun t ht => by rw [ht, add_mul])
      _ = _ := by
        rw [integral_add, ← intervalIntegral.integral_of_le x.2.1,
          ← intervalIntegral.integral_of_le x.2.1]
        · rfl
        all_goals
          apply (intervalIntegrable_iff_integrableOn_Ioc_of_le x.2.1).mp
          apply IntervalIntegrable.mono_set ((A.integrable _).mul_continuousOn
            (continuous_extend hL f).continuousOn)
          rw [uIcc_of_le x.2.1, uIcc_of_le hL]
          exact Icc_subset_Icc_right x.2.2
  map_smul' := by
    intro c e
    ext f x
    change (∫ t in (0 : ℝ)..x.1, A.coef (c • e) t * extend hL f t) = _
    have hsub : Ioc (0 : ℝ) x.1 ⊆ Ioc 0 L := Ioc_subset_Ioc_right x.2.2
    rw [intervalIntegral.integral_of_le x.2.1]
    have hae := ae_restrict_of_ae_restrict_of_subset hsub (A.smul_ae c e)
    calc
      _ = ∫ t in Ioc (0 : ℝ) x.1, c • (A.coef e t * extend hL f t) :=
        integral_congr_ae (hae.mono fun t ht => by rw [ht, smul_mul_assoc])
      _ = _ := by rw [integral_smul, ← intervalIntegral.integral_of_le x.2.1]; rfl

/-- The actual bounded bilinear integral operator. -/
def operator : E →L[ℝ] Path L 𝔸 →L[ℝ] Path L 𝔸 :=
  (linear hL A).mkContinuous₂ A.bound (norm_applyPath_le hL A)

@[simp] theorem operator_apply (e : E) (f : Path L 𝔸) (x : Icc (0 : ℝ) L) :
    operator hL A e f x = ∫ t in (0 : ℝ)..x.1, A.coef e t * extend hL f t := rfl

end QuantumNLS.DEF014VolterraOperator

-- ROUND 4 AUTHOR AUDIT
#print axioms QuantumNLS.DEF014VolterraOperator.norm_applyPath_le
#print axioms QuantumNLS.DEF014VolterraOperator.operator

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.DEF014VolterraOperator." then
      pending := pending.push n
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
  Lean.logInfo m!"DEF014VolterraOperator audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
