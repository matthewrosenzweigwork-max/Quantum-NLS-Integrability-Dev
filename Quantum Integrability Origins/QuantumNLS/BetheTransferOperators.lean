import QuantumNLS.BetheIntegralOperator
import QuantumNLS.BetheTransferKernelAdjoint
import QuantumNLS.BetheWeakGradient
import QuantumNLS.ContactOperator

/-! Literal finite-volume physical transfer kernels as bounded L² operators.
Source: periodic_basis.tex:316–339,375–394. The ordered kernels and full
interval phase are retained byte-for-byte through the frozen BTKA1 definitions.
The operator construction is by the actual double-integral pairing.
The symmetric compression uses the actual physical permutation-invariant
subspace. No on-shell eigenvalue formula or completeness is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace QuantumNLS.BetheTransferOperators
open BetheTransferKernelAdjoint BetheIntegralOperator
open PhysicalTensor BetheWeakGradient ContactOperator

/-- The alternating chamber is a measurable subset of the two real cubes. -/
theorem measurableSet_plusOrder (m : ℕ) (L : ℝ) :
    MeasurableSet {p : (Fin m → ℝ) × (Fin m → ℝ) | PlusOrder L p.1 p.2} := by
  simp only [PlusOrder]
  measurability

theorem measurable_displacement (m : ℕ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => displacement p.1 p.2) := by
  unfold displacement
  fun_prop

theorem measurable_rawPlus (m : ℕ) (L : ℝ) (z : ℂ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => rawPlus L z p.1 p.2) := by
  unfold rawPlus
  exact Measurable.ite (measurableSet_plusOrder m L)
    (Complex.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_const).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_displacement m)))) measurable_const

theorem measurable_rawMinus (m : ℕ) (L : ℝ) (z : ℂ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) => rawMinus L z p.1 p.2) := by
  unfold rawMinus MinusOrder
  apply Measurable.ite ((measurableSet_plusOrder m L).preimage measurable_swap)
  · apply Complex.continuous_exp.measurable.comp
    have hd := (measurable_displacement m).comp measurable_swap
    exact measurable_const.sub ((measurable_const.mul measurable_const).mul
      (Complex.continuous_ofReal.measurable.comp hd))
  · exact measurable_const

/-- The printed alternating-chain argument bounds the total phase length,
independently of particle number. -/
theorem displacement_range {m : ℕ} {L : ℝ} (hL : 0 ≤ L)
    {x y : Fin m → ℝ} (h : PlusOrder L x y) :
    0 ≤ displacement x y ∧ displacement x y ≤ L := by
  induction m generalizing L with
  | zero => simpa [displacement] using hL
  | succ m ih =>
    obtain ⟨hy, hyx, hxL, ht⟩ := (plusOrder_cons L x y).mp h
    obtain ⟨ha, hb⟩ := ih hy.le ht
    have he : displacement x y = x 0 - y 0 + displacement (Fin.tail x) (Fin.tail y) := by
      simp only [displacement, Fin.sum_univ_succ, Fin.tail_def]
    rw [he]
    constructor <;> linarith

theorem norm_phase_le (L : ℝ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) (htL : t ≤ L) :
    ‖Complex.exp (Complex.I * z * t)‖ ≤ Real.exp (L * |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, mul_zero, zero_sub]
  nlinarith [abs_nonneg z.im, neg_le_abs z.im,
    mul_le_mul_of_nonneg_right (neg_le_abs z.im) ht,
    mul_le_mul_of_nonneg_left htL (abs_nonneg z.im)]

theorem norm_rawPlus_le {m : ℕ} (L : ℝ) (hL : 0 ≤ L) (z : ℂ) (x y : Fin m → ℝ) :
    ‖rawPlus L z x y‖ ≤ Real.exp (L * |z.im|) := by
  classical
  unfold rawPlus
  split_ifs with h
  · exact norm_phase_le L z (displacement_range hL h).1 (displacement_range hL h).2
  · simp only [norm_zero]; positivity

theorem norm_rawMinus_le {m : ℕ} (L : ℝ) (hL : 0 ≤ L) (z : ℂ) (x y : Fin m → ℝ) :
    ‖rawMinus L z x y‖ ≤ Real.exp (L * |z.im|) := by
  classical
  unfold rawMinus
  split_ifs with h
  · have hd := displacement_range hL h
    have he : Complex.I * z * L - Complex.I * z * (∑ j, (y j-x j) : ℝ) =
        Complex.I * z * ((L - displacement y x : ℝ) : ℂ) := by
      simp only [displacement, Complex.ofReal_sub]
      ring
    rw [he]
    exact norm_phase_le L z (sub_nonneg.mpr hd.2) (by linarith [hd.1])
  · simp only [norm_zero]; positivity

variable (L : ℝ) [Fact (0 < L)] (m : ℕ)

/-- Literal physical raw upper kernel in the canonical [0,L) torus representatives. -/
def plusKernel (z : ℂ) : Kernel (torusPiMeasure L m) where
  fn p := rawPlus L z (representatives L p.1) (representatives L p.2)
  measurable := (measurable_rawPlus m L z).comp
    (((measurable_representatives m L).comp measurable_fst).prodMk
      ((measurable_representatives m L).comp measurable_snd))
  bound := Real.exp (L * |z.im|)
  bound_nonneg := (Real.exp_pos _).le
  norm_le _p := norm_rawPlus_le L (Fact.out : 0 < L).le z _ _

/-- Literal physical raw lower kernel, including e^(izL). -/
def minusKernel (z : ℂ) : Kernel (torusPiMeasure L m) where
  fn p := rawMinus L z (representatives L p.1) (representatives L p.2)
  measurable := (measurable_rawMinus m L z).comp
    (((measurable_representatives m L).comp measurable_fst).prodMk
      ((measurable_representatives m L).comp measurable_snd))
  bound := Real.exp (L * |z.im|)
  bound_nonneg := (Real.exp_pos _).le
  norm_le _p := norm_rawMinus_le L (Fact.out : 0 < L).le z _ _

/-- The actual uncompressed physical integral operator. -/
def rawOperator (z : ℂ) : L2TN L m →L[ℂ] L2TN L m :=
  (plusKernel L m z).operator + (minusKernel L m z).operator

/-- The actual source compression P_m (K⁺+K⁻) P_m restricted to H_m. -/
def compressedOperator (z : ℂ) : SymL2 L m →L[ℂ] SymL2 L m :=
  (SymL2 L m).subtypeL.adjoint ∘L rawOperator L m z ∘L (SymL2 L m).subtypeL

theorem plusOperator_adjoint (z : ℂ) :
    (plusKernel L m z).operator.adjoint =
      adjointPhase L z • (minusKernel L m (conj z)).operator := by
  apply Kernel.operator_adjoint_eq
  intro p
  exact rawPlus_adjoint L z (representatives L p.1) (representatives L p.2)

theorem minusOperator_adjoint (z : ℂ) :
    (minusKernel L m z).operator.adjoint =
      adjointPhase L z • (plusKernel L m (conj z)).operator := by
  apply Kernel.operator_adjoint_eq
  intro p
  exact rawMinus_adjoint L z (representatives L p.1) (representatives L p.2)

/-- The printed conjugate-swap calculation now holds for bounded physical
operators, rather than solely for pointwise kernels. -/
theorem rawOperator_adjoint (z : ℂ) :
    (rawOperator L m z).adjoint = adjointPhase L z • rawOperator L m (conj z) := by
  rw [rawOperator, map_add, plusOperator_adjoint,
    minusOperator_adjoint, rawOperator, smul_add, add_comm]

/-- The actual P_m compression preserves the literal phase adjoint identity. -/
theorem compressedOperator_adjoint (z : ℂ) :
    (compressedOperator L m z).adjoint =
      adjointPhase L z • compressedOperator L m (conj z) := by
  simp only [compressedOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, rawOperator_adjoint,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_assoc]

/-- Gauged compressed physical kernel for a real spectral parameter. -/
def realOperator (a : ℝ) : SymL2 L m →L[ℂ] SymL2 L m :=
  Complex.exp (-Complex.I * L * a / 2) • compressedOperator L m a

theorem realOperator_adjoint (a : ℝ) :
    (realOperator L m a).adjoint = realOperator L m a := by
  rw [realOperator, map_smulₛₗ, compressedOperator_adjoint]
  simp only [Complex.conj_ofReal, smul_smul, ← Complex.exp_conj,
    map_div₀, map_neg, Complex.conj_I, map_mul, Complex.conj_ofReal,
    map_ofNat, adjointPhase, ← Complex.exp_add]
  congr 2
  ring

theorem realOperator_isSelfAdjoint (a : ℝ) : IsSelfAdjoint (realOperator L m a) := by
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr (realOperator_adjoint L m a)

/-- Explicit weak action against arbitrary physical L² vectors. -/
theorem inner_rawOperator (z : ℂ) (f g : L2TN L m) :
    ⟪f, rawOperator L m z g⟫_ℂ =
      (∫ x, ∫ y, conj (f x) * rawPlus L z (representatives L x)
        (representatives L y) * g y ∂torusPiMeasure L m ∂torusPiMeasure L m) +
      (∫ x, ∫ y, conj (f x) * rawMinus L z (representatives L x)
        (representatives L y) * g y ∂torusPiMeasure L m ∂torusPiMeasure L m) := by
  rw [rawOperator, add_apply, inner_add_right,
    Kernel.inner_operator_integral, Kernel.inner_operator_integral]
  rfl

/-- The source sandwich on symmetric vectors, with no new carrier or measure. -/
theorem inner_compressedOperator (z : ℂ) (f g : SymL2 L m) :
    ⟪f, compressedOperator L m z g⟫_ℂ = ⟪(f : L2TN L m),
      rawOperator L m z (g : L2TN L m)⟫_ℂ := by
  exact (ContinuousLinearMap.adjoint_inner_right (SymL2 L m).subtypeL f
    (rawOperator L m z g))

/-- Explicit finite-volume norm bound. The sharper simplex factorial bound
from the report is not needed for construction or the adjoint proof. -/
theorem norm_rawOperator_le (z : ℂ) :
    ‖rawOperator L m z‖ ≤ 2 * Real.exp (L * |z.im|) *
      ‖oneVector (torusPiMeasure L m)‖ ^ 2 := by
  calc
    ‖rawOperator L m z‖ ≤ ‖(plusKernel L m z).operator‖ +
        ‖(minusKernel L m z).operator‖ := norm_add_le _ _
    _ ≤ (plusKernel L m z).bound * ‖oneVector (torusPiMeasure L m)‖ ^ 2 +
        (minusKernel L m z).bound * ‖oneVector (torusPiMeasure L m)‖ ^ 2 :=
      add_le_add (Kernel.norm_operator_le _) (Kernel.norm_operator_le _)
    _ = _ := by simp only [plusKernel, minusKernel]; ring

end QuantumNLS.BetheTransferOperators

#print axioms QuantumNLS.BetheTransferOperators.measurableSet_plusOrder
#print axioms QuantumNLS.BetheTransferOperators.measurable_displacement
#print axioms QuantumNLS.BetheTransferOperators.measurable_rawPlus
#print axioms QuantumNLS.BetheTransferOperators.measurable_rawMinus
#print axioms QuantumNLS.BetheTransferOperators.displacement_range
#print axioms QuantumNLS.BetheTransferOperators.norm_phase_le
#print axioms QuantumNLS.BetheTransferOperators.norm_rawPlus_le
#print axioms QuantumNLS.BetheTransferOperators.norm_rawMinus_le
#print axioms QuantumNLS.BetheTransferOperators.plusKernel
#print axioms QuantumNLS.BetheTransferOperators.minusKernel
#print axioms QuantumNLS.BetheTransferOperators.rawOperator
#print axioms QuantumNLS.BetheTransferOperators.compressedOperator
#print axioms QuantumNLS.BetheTransferOperators.plusOperator_adjoint
#print axioms QuantumNLS.BetheTransferOperators.minusOperator_adjoint
#print axioms QuantumNLS.BetheTransferOperators.rawOperator_adjoint
#print axioms QuantumNLS.BetheTransferOperators.compressedOperator_adjoint
#print axioms QuantumNLS.BetheTransferOperators.realOperator
#print axioms QuantumNLS.BetheTransferOperators.realOperator_adjoint
#print axioms QuantumNLS.BetheTransferOperators.realOperator_isSelfAdjoint
#print axioms QuantumNLS.BetheTransferOperators.inner_rawOperator
#print axioms QuantumNLS.BetheTransferOperators.inner_compressedOperator
#print axioms QuantumNLS.BetheTransferOperators.norm_rawOperator_le
