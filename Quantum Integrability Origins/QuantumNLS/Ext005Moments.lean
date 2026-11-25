import QuantumNLS.Ext025B3PhysicalSectors

/-!
EXT-005 / FIN-CORE-LNS-01, partial groundwork for the specific Fock-space
application in fluctuations.tex:161–165. The construction below uses the
actual physical Fock space and number sectors, and gives the square-root
multiplier and its moment domain. It does not assert the LNS evolution theorem.
-/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace QuantumNLS.Ext005Moments
open Ext025B3PhysicalSectors BetheCoefficientTransform

variable {L : ℝ} [Fact (0 < L)]

/-- Eigenvalue of `(Num + 1)^j` on the `N`-particle sector. -/
def momentWeight (j N : ℕ) : ℝ := ((N : ℝ) + 1) ^ j

/-- Square root of the number-moment weight as a sector operator. -/
def rootFamily (j N : ℕ) : HN L N →L[ℂ] HN L N :=
  ((Real.sqrt (momentWeight j N) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L N)

/-- Actual maximal square-root multiplier on physical bosonic Fock space. -/
def momentRoot (j : ℕ) : Fock L →ₗ.[ℂ] Fock L := block (rootFamily (L := L) j)

/-- The finite number-moment form domain. -/
def momentDomain (j : ℕ) : Submodule ℂ (Fock L) := (momentRoot (L := L) j).domain

lemma momentWeight_nonneg (j N : ℕ) : 0 ≤ momentWeight j N := by
  unfold momentWeight
  positivity

lemma momentWeight_one_le (j N : ℕ) : 1 ≤ momentWeight j N := by
  unfold momentWeight
  have h : 1 ≤ (N : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact one_le_pow₀ h

/-- Higher number weights dominate the first number weight. -/
theorem first_weight_le (j N : ℕ) (hj : 1 ≤ j) :
    (N : ℝ) + 1 ≤ momentWeight j N := by
  unfold momentWeight
  apply le_self_pow₀
  · nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · omega

@[simp] theorem momentRoot_apply (j : ℕ) (x : momentDomain (L := L) j) (N : ℕ) :
    momentRoot j x N = ((Real.sqrt (momentWeight j N) : ℝ) : ℂ) • x.val N := by
  rfl

/-- Each entire homogeneous particle sector belongs to every moment domain. -/
theorem sector_mem_momentDomain (j N : ℕ) (x : Fock L) :
    projection L N x ∈ momentDomain (L := L) j :=
  projection_mem_blockDomain (rootFamily (L := L) j) N x

/-- The form domain is precisely the finite weighted particle-number moment. -/
theorem momentDomain_iff (j : ℕ) (x : Fock L) :
    x ∈ momentDomain (L := L) j ↔
      Summable (fun N => momentWeight j N * ‖x N‖ ^ 2) := by
  change Memℓp (fun N => ((Real.sqrt (momentWeight j N) : ℝ) : ℂ) • x N) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (momentWeight_nonneg _ _)]

/-- The form norm squared is exactly the number-moment series. -/
theorem momentRoot_norm_sq (j : ℕ) (x : momentDomain (L := L) j) :
    ‖momentRoot j x‖ ^ 2 = ∑' N, momentWeight j N * ‖x.val N‖ ^ 2 := by
  rw [show ‖momentRoot j x‖ ^ 2 = ∑' N, ‖momentRoot j x N‖ ^ 2 by
    simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (momentRoot j x)]
  apply tsum_congr
  intro N
  rw [momentRoot_apply]
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (momentWeight_nonneg _ _)]

/-- Scalar inequality underlying the lower form bound when `B = A`. -/
theorem lower_bound_with_equal_comparators (a h c₀ c : ℝ)
    (ha : 0 ≤ a)
    (hchoice : c₀ ≤ c - c⁻¹) (hlower : -c₀ * a ≤ h) :
    c⁻¹ * a - c * a ≤ h := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hchoice) ha]

#print axioms QuantumNLS.Ext005Moments.momentWeight_one_le
#print axioms QuantumNLS.Ext005Moments.first_weight_le
#print axioms QuantumNLS.Ext005Moments.sector_mem_momentDomain
#print axioms QuantumNLS.Ext005Moments.momentDomain_iff
#print axioms QuantumNLS.Ext005Moments.momentRoot_norm_sq
#print axioms QuantumNLS.Ext005Moments.lower_bound_with_equal_comparators
end QuantumNLS.Ext005Moments
