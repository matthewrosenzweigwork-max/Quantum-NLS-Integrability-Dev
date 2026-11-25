import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Bounded integral operators on finite measure spaces. This construction is
used below with the literal ordered physical transfer kernels, rather than
postulating an operator with a prescribed adjoint. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.BetheIntegralOperator
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

abbrev H (μ : Measure X) := Lp ℂ 2 μ

/-- The constant-one L² vector; its norm is the finite-volume L²→L¹ constant. -/
def oneVector (μ : Measure X) [IsFiniteMeasure μ] : H μ :=
  (memLp_const (1 : ℂ)).toLp (fun _ => 1)

theorem integrable_vector (f : H μ) : Integrable f μ :=
  (Lp.memLp f).integrable (by norm_num)

theorem integral_norm_le (f : H μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖oneVector μ‖ * ‖f‖ := by
  let v : H μ := ((Lp.memLp f).norm.ofReal).toLp (fun x => (‖f x‖ : ℂ))
  have hv : v =ᵐ[μ] fun x => (‖f x‖ : ℂ) := MemLp.coeFn_toLp _
  have ho : oneVector μ =ᵐ[μ] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
  have hn : ‖v‖ ≤ ‖f‖ := Lp.norm_le_norm_of_ae_le (by
    filter_upwards [hv] with x hx
    simp [hx])
  have hi : ⟪oneVector μ, v⟫_ℂ = Complex.ofReal (∫ x, ‖f x‖ ∂μ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hv, ho] with x hx hy
    simp [hx, hy]
  have hb := norm_inner_le_norm (𝕜 := ℂ) (oneVector μ) v
  rw [hi, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-- A bounded measurable kernel, with its actual function retained. -/
structure Kernel (μ : Measure X) where
  fn : X × X → ℂ
  measurable : Measurable fn
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ p, ‖fn p‖ ≤ bound

namespace Kernel
variable (k : Kernel μ)

def integrand (f g : H μ) (p : X × X) : ℂ := conj (f p.1) * k.fn p * g p.2

theorem integrable_integrand (f g : H μ) : Integrable (k.integrand f g) (μ.prod μ) := by
  have hb : Integrable (fun p : X × X => k.bound * (‖f p.1‖ * ‖g p.2‖)) (μ.prod μ) :=
    ((integrable_vector f).norm.mul_prod (integrable_vector g).norm).const_mul _
  apply hb.mono' (((Lp.aestronglyMeasurable f).comp_fst.star.mul
    k.measurable.aestronglyMeasurable).mul (Lp.aestronglyMeasurable g).comp_snd)
  filter_upwards with p
  change ‖conj (f p.1) * k.fn p * g p.2‖ ≤ _
  simp only [norm_mul, Complex.norm_conj]
  nlinarith [mul_le_mul_of_nonneg_left (k.norm_le p) (norm_nonneg (f p.1)),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (k.norm_le p)
      (norm_nonneg (f p.1))) (norm_nonneg (g p.2))]

def form (f g : H μ) : ℂ := ∫ p, k.integrand f g p ∂μ.prod μ

theorem norm_form_le (f g : H μ) :
    ‖k.form f g‖ ≤ (k.bound * ‖oneVector μ‖ ^ 2) * ‖f‖ * ‖g‖ := by
  have hb := ((integrable_vector f).norm.mul_prod (integrable_vector g).norm).const_mul k.bound
  calc
    ‖k.form f g‖ ≤ ∫ p : X × X, k.bound * (‖f p.1‖ * ‖g p.2‖) ∂μ.prod μ := by
      apply norm_integral_le_of_norm_le hb
      filter_upwards with p
      simp only [integrand, norm_mul, Complex.norm_conj]
      calc
        _ ≤ ‖f p.1‖ * k.bound * ‖g p.2‖ := by gcongr; exact k.norm_le p
        _ = _ := by ring
    _ = k.bound * ((∫ x, ‖f x‖ ∂μ) * ∫ y, ‖g y‖ ∂μ) := by
      rw [integral_const_mul, integral_prod_mul (fun x => ‖f x‖) (fun x => ‖g x‖)]
    _ ≤ k.bound * ((‖oneVector μ‖ * ‖f‖) * (‖oneVector μ‖ * ‖g‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (integral_norm_le f) (integral_norm_le g)
          (integral_nonneg fun _ => norm_nonneg _) (by positivity)) k.bound_nonneg
    _ = _ := by ring

theorem form_add_left (f h g : H μ) : k.form (f+h) g = k.form f g + k.form h g := by
  simp only [form]
  rw [← integral_add (k.integrable_integrand f g) (k.integrable_integrand h g)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_add f h)] with p hp
  simp only [Function.comp_apply, Pi.add_apply] at hp
  simp only [integrand]
  rw [hp]
  simp only [map_add, add_mul]

theorem form_smul_left (c : ℂ) (f g : H μ) : k.form (c • f) g = conj c * k.form f g := by
  simp only [form]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul c f)] with p hp
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hp
  simp [integrand, hp, map_mul, mul_assoc]

theorem form_add_right (f g h : H μ) : k.form f (g+h) = k.form f g + k.form f h := by
  simp only [form]
  rw [← integral_add (k.integrable_integrand f g) (k.integrable_integrand f h)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add g h)] with p hp
  simp only [Function.comp_apply, Pi.add_apply] at hp
  simp only [integrand]
  rw [hp]
  simp only [mul_add]

theorem form_smul_right (c : ℂ) (f g : H μ) : k.form f (c • g) = c * k.form f g := by
  simp only [form]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_smul c g)] with p hp
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hp
  simp [integrand, hp]
  ring

def formCLM : H μ →L⋆[ℂ] H μ →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) k.form
      k.form_add_left (fun c f g => k.form_smul_left c f g)
      k.form_add_right (fun c f g => k.form_smul_right c f g))
    (k.bound * ‖oneVector μ‖ ^ 2) k.norm_form_le

/-- The bounded integral operator, constructed by Riesz duality. -/
def operator : H μ →L[ℂ] H μ :=
  (InnerProductSpace.continuousLinearMapOfBilin k.formCLM).adjoint

theorem inner_operator (f g : H μ) : ⟪f, k.operator g⟫_ℂ = k.form f g := by
  rw [operator, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- This is the literal weak integral action of the constructed operator. -/
theorem inner_operator_integral (f g : H μ) :
    ⟪f, k.operator g⟫_ℂ = ∫ x, ∫ y, conj (f x) * k.fn (x,y) * g y ∂μ ∂μ := by
  rw [inner_operator, form, integral_prod _ (k.integrable_integrand f g)]
  rfl

/-- The actual conjugate-swapped kernel. -/
def adjointKernel : Kernel μ where
  fn p := conj (k.fn p.swap)
  measurable := Complex.continuous_conj.measurable.comp (k.measurable.comp measurable_swap)
  bound := k.bound
  bound_nonneg := k.bound_nonneg
  norm_le p := by simpa using k.norm_le p.swap

theorem form_adjoint (f g : H μ) : k.adjointKernel.form f g = conj (k.form g f) := by
  simp only [form]
  rw [← integral_conj, ← integral_prod_swap (fun p => conj (k.integrand g f p))]
  apply integral_congr_ae
  filter_upwards with p
  simp only [integrand, adjointKernel, map_mul, starRingEnd_self_apply, Prod.fst_swap, Prod.snd_swap]
  ring

theorem operator_adjoint : k.operator.adjoint = k.adjointKernel.operator := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, inner_operator,
    form_adjoint, ← inner_conj_symm, inner_operator]

theorem operator_eq_smul_of_fn (j : Kernel μ) (c : ℂ)
    (h : ∀ p, k.fn p = c * j.fn p) : k.operator = c • j.operator := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [smul_apply, inner_smul_right, inner_operator, inner_operator]
  simp only [form]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp only [integrand, h]
  ring

theorem operator_adjoint_eq (j : Kernel μ) (c : ℂ)
    (h : ∀ p, conj (k.fn p.swap) = c * j.fn p) :
    k.operator.adjoint = c • j.operator := by
  rw [operator_adjoint]
  exact k.adjointKernel.operator_eq_smul_of_fn j c h

/-- The pointwise integral exists as an L² function, by the finite-volume bound. -/
theorem memLp_action (g : H μ) :
    MemLp (fun x => ∫ y, k.fn (x,y) * g y ∂μ) 2 μ := by
  apply MemLp.of_bound
    ((k.measurable.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g).comp_snd).integral_prod_right')
    (k.bound * ∫ y, ‖g y‖ ∂μ)
  filter_upwards with x
  calc
    ‖∫ y, k.fn (x,y) * g y ∂μ‖ ≤ ∫ y, k.bound * ‖g y‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((integrable_vector g).norm.const_mul _)
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (k.norm_le _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The constructed operator agrees almost everywhere with the literal
pointwise integral, for every L² input. -/
theorem operator_apply_ae (g : H μ) :
    k.operator g =ᵐ[μ] fun x => ∫ y, k.fn (x,y) * g y ∂μ := by
  let v : H μ := (k.memLp_action g).toLp _
  have hv : v =ᵐ[μ] fun x => ∫ y, k.fn (x,y) * g y ∂μ := MemLp.coeFn_toLp _
  have he : k.operator g = v := by
    apply ext_inner_left ℂ
    intro f
    rw [inner_operator_integral, L2.inner_def]
    calc
      (∫ x, ∫ y, conj (f x) * k.fn (x,y) * g y ∂μ ∂μ) =
          ∫ x, conj (f x) * (∫ y, k.fn (x,y) * g y ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        ring
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hv] with x hx
        simp only [hx, RCLike.inner_apply']
  rw [he]
  exact hv

theorem norm_operator_le : ‖k.operator‖ ≤ k.bound * ‖oneVector μ‖ ^ 2 := by
  have hbn := k.bound_nonneg
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hbn (sq_nonneg _))
  intro g
  by_cases hz : k.operator g = 0
  · simp only [hz, norm_zero]; positivity
  · have hp : 0 < ‖k.operator g‖ := norm_pos_iff.mpr hz
    have hb := k.norm_form_le (k.operator g) g
    rw [← inner_operator, inner_self_eq_norm_sq_to_K] at hb
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at hb
    nlinarith

end Kernel
end QuantumNLS.BetheIntegralOperator

#print axioms QuantumNLS.BetheIntegralOperator.H
#print axioms QuantumNLS.BetheIntegralOperator.oneVector
#print axioms QuantumNLS.BetheIntegralOperator.integrable_vector
#print axioms QuantumNLS.BetheIntegralOperator.integral_norm_le
#print axioms QuantumNLS.BetheIntegralOperator.Kernel
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.integrand
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.integrable_integrand
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.norm_form_le
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form_add_left
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form_smul_left
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form_add_right
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form_smul_right
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.formCLM
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.operator
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.inner_operator
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.inner_operator_integral
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.adjointKernel
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.form_adjoint
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.operator_adjoint
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.operator_eq_smul_of_fn
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.operator_adjoint_eq
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.memLp_action
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.operator_apply_ae
#print axioms QuantumNLS.BetheIntegralOperator.Kernel.norm_operator_le
