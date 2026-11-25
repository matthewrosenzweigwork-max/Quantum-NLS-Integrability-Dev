import QuantumNLS.Ext025B3FormSpectral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.LinearPMap

/-! Author sol_ext_b, Round 4. Actual maximal multiplication and square-root
realizations in L² over arbitrary measure spaces (including nonatomic measures).
No spectral representation theorem for an arbitrary H is postulated. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Ext025B4ContinuousForms
open Ext025B3FormSpectral
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
abbrev Hilbert (μ : Measure α) := Lp ℂ 2 μ

/-- Maximal multiplication domain; no boundedness hypothesis on a. -/
def domain (a : α → ℂ) : Submodule ℂ (Hilbert μ) where
  carrier := {v | MemLp (fun x => a x * v x) 2 μ}
  zero_mem' := by
    change MemLp (fun x => a x * (0 : Hilbert μ) x) 2 μ
    apply (MemLp.zero : MemLp (0 : α → ℂ) 2 μ).ae_eq
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx]
    simp
  add_mem' := by
    intro v w hv hw
    change MemLp (fun x => a x * (v+w) x) 2 μ
    apply (hv.add hw).ae_eq
    filter_upwards [Lp.coeFn_add v w] with x hx
    rw [hx]
    simp only [Pi.add_apply, mul_add]
  smul_mem' := by
    intro c v hv
    change MemLp (fun x => a x * (c • v) x) 2 μ
    apply (hv.const_smul c).ae_eq
    filter_upwards [Lp.coeFn_smul c v] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- The genuine partial linear multiplier on its entire maximal domain. -/
def multiplier (a : α → ℂ) : Hilbert μ →ₗ.[ℂ] Hilbert μ where
  domain := domain a
  toFun :=
    { toFun := fun v => v.property.toLp (fun x => a x * v.val x)
      map_add' := by
        intro v w
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (show MemLp (fun x => a x * (v+w).val x) 2 μ from (v+w).property),
          MemLp.coeFn_toLp v.property, MemLp.coeFn_toLp w.property,
          Lp.coeFn_add v.val w.val,
          Lp.coeFn_add (v.property.toLp _) (w.property.toLp _)] with x h h₁ h₂ h₃ h₄
        simp_all [mul_add]
      map_smul' := by
        intro c v
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (show MemLp (fun x => a x * (c • v).val x) 2 μ from (c • v).property),
          MemLp.coeFn_toLp v.property, Lp.coeFn_smul c v.val,
          Lp.coeFn_smul c (v.property.toLp _)] with x h h₁ h₂ h₃
        simp_all [smul_eq_mul, mul_left_comm] }

theorem multiplier_ae (a : α → ℂ) (v : (multiplier (μ := μ) a).domain) :
    multiplier a v =ᵐ[μ] fun x => a x * v.val x := MemLp.coeFn_toLp v.property

theorem norm_sq_integral (v : Hilbert μ) : ‖v‖^2 = ∫ x, ‖v x‖^2 ∂μ := by
  have h := integral_re (𝕜 := ℂ) (L2.integrable_inner v v)
  rw [← L2.inner_def] at h
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using h.symm

variable (ev : α → ℝ≥0) (hev : Measurable ev)

def formDomain (v : Hilbert μ) : Prop :=
  v ∈ domain (μ := μ) (fun x => (Real.sqrt (ev x) : ℂ))

def formRoot (v : Hilbert μ) (hv : formDomain ev v) : Hilbert μ :=
  multiplier (fun x => (Real.sqrt (ev x) : ℂ)) ⟨v, hv⟩

include hev in
theorem root_measurable : AEStronglyMeasurable (fun x => (Real.sqrt (ev x) : ℂ)) μ := by
  apply Measurable.aestronglyMeasurable
  fun_prop

theorem root_density (v : Hilbert μ) (x : α) :
    ‖(Real.sqrt (ev x) : ℂ) * v x‖^2 = (ev x : ℝ) * ‖v x‖^2 := by
  simp [mul_pow, Complex.norm_real, Real.sq_sqrt (ev x).coe_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg _)]

include hev in
/-- The maximal square-root domain is precisely the finite first moment. -/
theorem formDomain_iff (v : Hilbert μ) :
    formDomain ev v ↔ Integrable (fun x => (ev x : ℝ) * ‖v x‖^2) μ := by
  change MemLp (fun x => (Real.sqrt (ev x) : ℂ) * v x) 2 μ ↔ _
  simpa only [Pi.mul_def, root_density] using
    (memLp_two_iff_integrable_sq_norm ((root_measurable ev hev).mul (Lp.aestronglyMeasurable v)))

/-- Actual first-moment identity in the multiplication realization. -/
theorem firstMoment_identity (v : Hilbert μ) (hv : formDomain ev v) :
    ‖formRoot ev v hv‖^2 = ∫ x, (ev x : ℝ) * ‖v x‖^2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [multiplier_ae (fun x => (Real.sqrt (ev x) : ℂ)) ⟨v, hv⟩] with x hx
  rw [show formRoot ev v hv x = (Real.sqrt (ev x) : ℂ) * v x from hx, root_density]

include hev in
theorem phase_measurable (t : ℝ) : Measurable (fun x => phase t (ev x)) := by
  unfold phase
  fun_prop

/-- Everywhere-defined phase multiplication, constructed in L². -/
def evolution (t : ℝ) (v : Hilbert μ) : Hilbert μ :=
  ((Lp.memLp v).congr_norm
    ((phase_measurable ev hev t).aestronglyMeasurable.mul (Lp.aestronglyMeasurable v))
    (Eventually.of_forall fun x => by simp [phase_norm])).toLp
    (fun x => phase t (ev x) * v x)

theorem evolution_ae (t : ℝ) (v : Hilbert μ) :
    evolution ev hev t v =ᵐ[μ] fun x => phase t (ev x) * v x := MemLp.coeFn_toLp _

theorem evolution_increment_identity (t : ℝ) (v : Hilbert μ) :
    ‖evolution ev hev t v - v‖^2 = ∫ x, ‖phase t (ev x) - 1‖^2 * ‖v x‖^2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (evolution ev hev t v) v, evolution_ae ev hev t v] with x hx he
  rw [hx, Pi.sub_apply, he]
  have hmul : phase t (ev x) * v x - v x = (phase t (ev x)-1)*v x := by ring
  rw [hmul, norm_mul, mul_pow]

/-- Both signs of time; only a first moment is required. -/
theorem strong_square (v : Hilbert μ) (hv : formDomain ev v) :
    Tendsto (fun t : ℝ => ‖evolution ev hev t v - v‖^2 / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  have hm := (formDomain_iff ev hev v).mp hv
  have hphase (t : ℝ) : Measurable (fun x => phase t (ev x)) := by
    unfold phase
    fun_prop
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[≠] (0 : ℝ)) (fun x => 2 * ((ev x : ℝ) * ‖v x‖^2))
    (F := fun t x => (‖phase t (ev x)-1‖^2 / |t|) * ‖v x‖^2)
    (f := fun _ => (0 : ℝ))
    (Eventually.of_forall fun t => by
      simpa only [div_eq_mul_inv, Pi.mul_def, Pi.sub_def, Pi.pow_def] using
        (((((hphase t).aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2).mul_const |t|⁻¹).mul
          ((Lp.aestronglyMeasurable v).norm.pow 2)))
    (Eventually.of_forall fun t => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (square_bound t (ev x) (ev x).coe_nonneg) (sq_nonneg ‖v x‖))
    (hm.const_mul 2)
    (Eventually.of_forall fun x => by simpa using (square_limit (ev x)).mul_const (‖v x‖^2))
  simpa only [integral_zero, evolution_increment_identity, div_mul_eq_mul_div,
    integral_div] using h

theorem strong_small_o (v : Hilbert μ) (hv : formDomain ev v) :
    Tendsto (fun t : ℝ => ‖evolution ev hev t v - v‖ / Real.sqrt |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp (strong_square ev hev v hv)
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_div' _ (abs_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

end QuantumNLS.Ext025B4ContinuousForms

#print axioms QuantumNLS.Ext025B4ContinuousForms.multiplier_ae

#print axioms QuantumNLS.Ext025B4ContinuousForms.norm_sq_integral

#print axioms QuantumNLS.Ext025B4ContinuousForms.root_measurable

#print axioms QuantumNLS.Ext025B4ContinuousForms.root_density

#print axioms QuantumNLS.Ext025B4ContinuousForms.formDomain_iff

#print axioms QuantumNLS.Ext025B4ContinuousForms.firstMoment_identity

#print axioms QuantumNLS.Ext025B4ContinuousForms.evolution_ae

#print axioms QuantumNLS.Ext025B4ContinuousForms.evolution_increment_identity

#print axioms QuantumNLS.Ext025B4ContinuousForms.strong_square

#print axioms QuantumNLS.Ext025B4ContinuousForms.strong_small_o

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B4ContinuousForms." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B4ContinuousForms audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
