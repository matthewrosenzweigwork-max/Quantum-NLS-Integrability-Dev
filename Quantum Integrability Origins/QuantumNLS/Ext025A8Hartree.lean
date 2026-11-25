import QuantumNLS.TensorPlacements
import QuantumNLS.Ext025A2ODE

/-! Concrete partial contractions for PROP-001. Ranks are indexed by n+1;
the distinguished slot is first, as in the report. No gradient, differentiability of a series,
or local solution is an input to the estimates below. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Ext025A8
open TensorCarrier TensorPlacements
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tensorMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => H) (HilbertTensorPower ℂ H n) :=
  MultilinearMap.mkContinuous
    ((UniformSpace.Completion.toComplL : AlgTensorPower ℂ H n →L[ℂ]
      HilbertTensorPower ℂ H n).toLinearMap.compMultilinearMap
        (PiTensorProduct.tprod ℂ)) 1 (fun v => by
          change ‖((ptprod v : AlgTensorPower ℂ H n) :
            HilbertTensorPower ℂ H n)‖ ≤ 1 * ∏ i, ‖v i‖
          simp only [UniformSpace.Completion.norm_coe, norm_ptprod, one_mul, le_refl])

theorem tensorMultilinear_norm (n : ℕ) : ‖tensorMultilinear (H := H) n‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

def insertFirst (n : ℕ) (u : H) : H →L[ℂ] HilbertTensorPower ℂ H (n + 1) :=
  (tensorMultilinear (H := H) (n + 1)).curryLeft.flipMultilinear (fun _ => u)

theorem insertFirst_self (n : ℕ) (u : H) : insertFirst n u u = htpow (n + 1) u := by
  change tensorMultilinear (n + 1) (Fin.cons u (fun _ => u)) = _
  have he : Fin.cons u (fun _ : Fin n => u) = (fun _ : Fin (n + 1) => u) := by
    ext i
    exact Fin.cases (by simp) (fun j => by simp) i
  rw [he]
  rfl

theorem insertFirst_norm (n : ℕ) (u : H) : ‖insertFirst n u‖ ≤ ‖u‖ ^ n := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖((ptprod (Fin.cons v (fun _ : Fin n => u)) : AlgTensorPower ℂ H (n + 1)) :
    HilbertTensorPower ℂ H (n + 1))‖ ≤ ‖u‖ ^ n * ‖v‖
  simp only [UniformSpace.Completion.norm_coe, norm_ptprod, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_comm _ _).le

variable [CompleteSpace H]

/-- The actual bounded one-body contraction J(u)* A J(u). -/
def hartreeContraction {n : ℕ}
    (A : HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (u : H) : H →L[ℂ] H :=
  (insertFirst n u).adjoint.comp (A.comp (insertFirst n u))

theorem hartreeContraction_pairing {n : ℕ}
    (A : HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (u v w : H) :
    ⟪v, hartreeContraction A u w⟫_ℂ =
      ⟪insertFirst n u v, A (insertFirst n u w)⟫_ℂ := by
  exact ContinuousLinearMap.adjoint_inner_right (insertFirst n u) v
    (A (insertFirst n u w))

theorem hartreeContraction_norm {n : ℕ}
    (A : HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (u : H) : ‖hartreeContraction A u‖ ≤ ‖A‖ * ‖u‖ ^ (2 * n) := by
  calc
    _ ≤ ‖(insertFirst n u).adjoint‖ * (‖A‖ * ‖insertFirst n u‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖u‖ ^ n * (‖A‖ * ‖u‖ ^ n) := by
      simp only [ContinuousLinearMap.adjoint.norm_map]
      gcongr <;> exact insertFirst_norm n u
    _ = _ := by rw [show 2 * n = n + n by omega, pow_add]; ring

theorem hartreeContraction_selfAdjoint {n : ℕ}
    (A : HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (hA : IsSelfAdjoint A) (u : H) : IsSelfAdjoint (hartreeContraction A u) := by
  change (hartreeContraction A u).adjoint = hartreeContraction A u
  simp only [hartreeContraction, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  rw [show A.adjoint = A from hA, ContinuousLinearMap.comp_assoc]

def hartreeTerm (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (n : ℕ) (u : H) : H := ((n + 1 : ℕ) : ℂ) • hartreeContraction (A n) u u

theorem hartreeTerm_norm (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (n : ℕ) (u : H) :
    ‖hartreeTerm A n u‖ ≤ (n + 1 : ℕ) * ‖A n‖ * ‖u‖ ^ (2 * n + 1) := by
  calc
    _ = (n + 1 : ℕ) * ‖hartreeContraction (A n) u u‖ := by
      rw [hartreeTerm, norm_smul]
      rw [Complex.norm_natCast]
    _ ≤ (n + 1 : ℕ) * (‖hartreeContraction (A n) u‖ * ‖u‖) := by
      gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (n + 1 : ℕ) * ((‖A n‖ * ‖u‖ ^ (2 * n)) * ‖u‖) := by
      gcongr; exact hartreeContraction_norm _ _
    _ = _ := by rw [pow_succ]; ring

/-- Norm convergence of the literal vector series on a larger ball follows
from its geometric rank majorant, not an assumed Hartree field. -/
theorem hartree_series_summable (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    {S : ℝ} (_hS : 0 ≤ S)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * S ^ (2 * n + 1)))
    {u : H} (hu : ‖u‖ ≤ S) : Summable (fun n => hartreeTerm A n u) := by
  apply Summable.of_norm_bounded hs
  intro n
  exact (hartreeTerm_norm A n u).trans (by gcongr)
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.tensorMultilinear
#print axioms QuantumNLS.Ext025A8.tensorMultilinear_norm
#print axioms QuantumNLS.Ext025A8.insertFirst
#print axioms QuantumNLS.Ext025A8.insertFirst_self
#print axioms QuantumNLS.Ext025A8.insertFirst_norm
#print axioms QuantumNLS.Ext025A8.hartreeContraction
#print axioms QuantumNLS.Ext025A8.hartreeContraction_pairing
#print axioms QuantumNLS.Ext025A8.hartreeContraction_norm
#print axioms QuantumNLS.Ext025A8.hartreeContraction_selfAdjoint
#print axioms QuantumNLS.Ext025A8.hartreeTerm
#print axioms QuantumNLS.Ext025A8.hartreeTerm_norm
#print axioms QuantumNLS.Ext025A8.hartree_series_summable
