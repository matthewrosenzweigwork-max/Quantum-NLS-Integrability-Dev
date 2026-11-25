import QuantumNLS.Ext005Moments
import QuantumNLS.PhysicalEnergy

/-! Self-adjoint maximal real sector multipliers on the physical Fock sum.
The square-root identity is an operator identity including domains; no abstract
unbounded spectral calculus is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ENNReal InnerProductSpace ComplexConjugate LinearPMap
namespace QuantumNLS.Ext005Spectral
open Ext025B3PhysicalSectors Ext005Moments BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

def family (m : ℕ → ℝ) (N : ℕ) : HN L N →L[ℂ] HN L N :=
  (m N : ℂ) • ContinuousLinearMap.id ℂ (HN L N)

def multiplier (m : ℕ → ℝ) : Fock L →ₗ.[ℂ] Fock L := block (family (L := L) m)

@[simp] theorem multiplier_apply (m : ℕ → ℝ) (x : (multiplier (L := L) m).domain) (N : ℕ) :
    multiplier m x N = (m N : ℂ) • x.val N := rfl

theorem bounded_mem (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (x : Fock L) :
    Memℓp (fun n => (c n : ℂ) • x n) 2 := by
  apply (lp.memℓp x).mono'
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [norm_nonneg (x n), hc n]

def boundedMultiplier (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) : Fock L →L[ℂ] Fock L :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => (c n : ℂ) • x n, bounded_mem c hc x⟩
      map_add' := by
        intro x y
        apply Subtype.ext; funext n
        exact smul_add _ _ _
      map_smul' := by
        intro a x
        apply Subtype.ext; funext n
        change (c n : ℂ) • (a • x n) = a • ((c n : ℂ) • x n)
        exact smul_comm (c n : ℂ) a (x n) }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num)
      intro n
      change ‖(c n : ℂ) • x n‖ ≤ ‖x n‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [norm_nonneg (x n), hc n])

@[simp] theorem boundedMultiplier_apply (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1)
    (x : Fock L) (n : ℕ) : boundedMultiplier c hc x n = (c n : ℂ) • x n := rfl

theorem multiplier_symmetric (m : ℕ → ℝ) (x y : (multiplier (L := L) m).domain) :
    ⟪multiplier m x, (y : Fock L)⟫_ℂ = ⟪(x : Fock L), multiplier m y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [multiplier_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem boundedMultiplier_symmetric (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (x y : Fock L) :
    ⟪boundedMultiplier c hc x, y⟫_ℂ = ⟪x, boundedMultiplier c hc y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [boundedMultiplier_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem inverse_bound (m : ℕ → ℝ) (hm : ∀ n, 1 ≤ m n) (n : ℕ) : |(m n)⁻¹| ≤ 1 := by
  rw [abs_of_nonneg (inv_nonneg.mpr (by linarith [hm n]))]
  exact inv_le_one_of_one_le₀ (hm n)

def inverse (m : ℕ → ℝ) (hm : ∀ n, 1 ≤ m n) : Fock L →L[ℂ] Fock L :=
  boundedMultiplier (fun n => (m n)⁻¹) (inverse_bound m hm)

theorem inverse_mem (m : ℕ → ℝ) (hm : ∀ n, 1 ≤ m n) (x : Fock L) :
    inverse m hm x ∈ (multiplier (L := L) m).domain := by
  change Memℓp (fun n => (m n : ℂ) • inverse m hm x n) 2
  have h : (fun n => (m n : ℂ) • inverse m hm x n) = (x : ∀ n, HN L n) := by
    funext n
    simp only [inverse, boundedMultiplier_apply, smul_smul, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀ (by linarith [hm n]), Complex.ofReal_one, one_smul]
  rw [h]
  exact lp.memℓp x

theorem multiplier_inverse (m : ℕ → ℝ) (hm : ∀ n, 1 ≤ m n) (x : Fock L) :
    multiplier m ⟨inverse m hm x, inverse_mem m hm x⟩ = x := by
  ext n
  simp only [multiplier_apply, inverse, boundedMultiplier_apply, smul_smul, ← Complex.ofReal_mul]
  rw [mul_inv_cancel₀ (by linarith [hm n]), Complex.ofReal_one, one_smul]

theorem multiplier_selfAdjoint (m : ℕ → ℝ) (hm : ∀ n, 1 ≤ m n) :
    IsSelfAdjoint (multiplier (L := L) m) := by
  exact QuantumNLS.PhysicalEnergy.isSelfAdjoint_of_inverse
    (multiplier (L := L) m) (inverse (L := L) m hm)
    (boundedMultiplier_symmetric (L := L) _ _) (inverse_mem (L := L) m hm)
    (multiplier_inverse (L := L) m hm) (multiplier_symmetric (L := L) m)

def momentOperator (j : ℕ) : Fock L →ₗ.[ℂ] Fock L := multiplier (momentWeight j)

theorem momentOperator_selfAdjoint (j : ℕ) : IsSelfAdjoint (momentOperator (L := L) j) :=
  multiplier_selfAdjoint _ (momentWeight_one_le j)

theorem momentRoot_selfAdjoint (j : ℕ) : IsSelfAdjoint (momentRoot (L := L) j) := by
  change IsSelfAdjoint (multiplier (L := L) (fun n => Real.sqrt (momentWeight j n)))
  apply multiplier_selfAdjoint
  intro n
  exact Real.one_le_sqrt.mpr (momentWeight_one_le j n)

/-- The full operator domain embeds in the square-root domain. -/
theorem operator_mem_root (j : ℕ) (x : (momentOperator (L := L) j).domain) :
    (x : Fock L) ∈ momentDomain (L := L) j := by
  change Memℓp (fun n => (Real.sqrt (momentWeight j n) : ℂ) • x.val n) 2
  apply x.property.mono'
  intro n
  change ‖(Real.sqrt (momentWeight j n) : ℂ) • x.val n‖ ≤
    ‖(momentWeight j n : ℂ) • x.val n‖
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (momentWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right
    (Real.sqrt_le_self_iff.mpr (Or.inr (momentWeight_one_le j n))) (norm_nonneg _)

/-- Applying the root twice has exactly the maximal full-multiplier domain. -/
theorem root_twice_domain (j : ℕ) (x : momentDomain (L := L) j) :
    momentRoot j x ∈ momentDomain (L := L) j ↔
      (x : Fock L) ∈ (momentOperator (L := L) j).domain := by
  change Memℓp (fun n => (Real.sqrt (momentWeight j n) : ℂ) •
    ((Real.sqrt (momentWeight j n) : ℂ) • x.val n)) 2 ↔ _
  have h : (fun n => (Real.sqrt (momentWeight j n) : ℂ) •
      ((Real.sqrt (momentWeight j n) : ℂ) • x.val n)) =
      (fun n => (momentWeight j n : ℂ) • x.val n) := by
    funext n
    rw [smul_smul, ← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (momentWeight_nonneg j n)]
  rw [h]
  rfl

theorem root_twice (j : ℕ) (x : (momentOperator (L := L) j).domain) :
    momentRoot (L := L) j ⟨momentRoot (L := L) j ⟨x, operator_mem_root (L := L) j x⟩,
      (root_twice_domain (L := L) j ⟨x, operator_mem_root (L := L) j x⟩).2 x.property⟩ = momentOperator (L := L) j x := by
  apply Subtype.ext; funext n
  change (Real.sqrt (momentWeight j n) : ℂ) •
    ((Real.sqrt (momentWeight j n) : ℂ) • x.val n) = (momentWeight j n : ℂ) • x.val n
  rw [smul_smul, ← Complex.ofReal_mul, ← pow_two,
    Real.sq_sqrt (momentWeight_nonneg j n)]

/-- The number-moment operator is positive and bounded below by identity. -/
theorem momentOperator_lower (j : ℕ) (x : (momentOperator (L := L) j).domain) :
    ‖(x : Fock L)‖ ^ 2 ≤ RCLike.re ⟪(x : Fock L), momentOperator (L := L) j x⟫_ℂ := by
  let y : momentDomain (L := L) j := ⟨x, operator_mem_root (L := L) j x⟩
  have hinner : ⟪(x : Fock L), momentOperator (L := L) j x⟫_ℂ =
      ⟪momentRoot (L := L) j y, momentRoot (L := L) j y⟫_ℂ := by
    rw [← root_twice (L := L) j x]
    exact (multiplier_symmetric (L := L) (fun n => Real.sqrt (momentWeight j n))
      y ⟨momentRoot (L := L) j y, (root_twice_domain (L := L) j y).2 x.property⟩).symm
  rw [hinner, inner_self_eq_norm_sq]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply lp.norm_mono (by norm_num)
  intro n
  change ‖x.val n‖ ≤ ‖(Real.sqrt (momentWeight j n) : ℂ) • x.val n‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [norm_nonneg (x.val n), Real.one_le_sqrt.mpr (momentWeight_one_le j n)]

#print axioms QuantumNLS.Ext005Spectral.multiplier_selfAdjoint
#print axioms QuantumNLS.Ext005Spectral.momentOperator_selfAdjoint
#print axioms QuantumNLS.Ext005Spectral.momentRoot_selfAdjoint
#print axioms QuantumNLS.Ext005Spectral.root_twice_domain
#print axioms QuantumNLS.Ext005Spectral.root_twice
#print axioms QuantumNLS.Ext005Spectral.momentOperator_lower
end QuantumNLS.Ext005Spectral
