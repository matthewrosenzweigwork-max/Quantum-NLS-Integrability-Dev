import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Tactic

/-! Batch 38 salvage of the owner's UNCOMPILED candidate `FinitePolynomial.lean`
(renamed with suffix 38). A finite real combination of diagonals of real
continuous multilinear forms: continuity, explicit polynomial representation and
the `C (1 + ‖u‖^D)` growth bound. Generic; no hierarchy identity is claimed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Sobolev38


section Polynomial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Type*} [Fintype A]
  (q : A -> ℕ) (L : (a : A) -> ContinuousMultilinearMap ℝ (fun _ : Fin (q a) => E) ℝ)
  (beta : A -> ℝ)

/-- The coefficient vector is finite and arbitrary; no infinite factorial constraint occurs. -/
def finitePolynomial38 (u : E) : ℝ := ∑ a, beta a * L a (fun _ => u)

def finitePolynomialConstant38 : ℝ := ∑ a, |beta a| * ‖L a‖

theorem finitePolynomialConstant_nonneg38 : 0 ≤ finitePolynomialConstant38 q L beta := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem finitePolynomial_continuous38 : Continuous (finitePolynomial38 q L beta) := by
  unfold finitePolynomial38
  apply continuous_finsetSum
  intro a _
  apply continuous_const.mul
  exact (L a).cont.comp (continuous_pi fun _ => continuous_id)

/-- The polynomial representation is explicit, with real multilinear forms and the degree cap. -/
theorem finitePolynomial_representation38 (D : ℕ) (hq : forall a, q a ≤ D) :
    ∃ F : (a : A) -> ContinuousMultilinearMap ℝ (fun _ : Fin (q a) => E) ℝ,
      (forall a, q a ≤ D) ∧
        (forall u : E, finitePolynomial38 q L beta u = ∑ a, F a (fun _ => u)) := by
  refine ⟨(fun a => beta a • L a), hq, ?_ ⟩
  intro u
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- Elementary power bound covering the unit ball and degree zero. -/
theorem normPower_le_one_add38 {t : ℝ} (ht : 0 ≤ t) {d D : ℕ} (hd : d ≤ D) :
    t ^ d ≤ 1 + t ^ D := by
  by_cases hsmall : t ≤ 1
  · have hall : forall r : ℕ, t ^ r ≤ 1 := by
      intro r
      induction r with
      | zero => simp
      | succ d ih =>
        rw [pow_succ]
        calc
          t ^ d * t ≤ 1 * 1 := mul_le_mul ih hsmall ht (by norm_num)
          _ = 1 := one_mul 1
    have hp := hall d
    linarith [pow_nonneg ht D]
  · have hone : 1 ≤ t := le_of_lt (lt_of_not_ge hsmall)
    have hmon : forall r : ℕ, t ^ d ≤ t ^ (d + r) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        rw [Nat.add_succ, pow_succ]
        exact ih.trans (le_mul_of_one_le_right (pow_nonneg ht _) hone)
    have hp := hmon (D - d)
    rw [Nat.add_sub_of_le hd] at hp
    linarith

theorem finitePolynomial_bound38 (D : ℕ) (hq : forall a, q a ≤ D) (u : E) :
    |finitePolynomial38 q L beta u| ≤
      finitePolynomialConstant38 q L beta * (1 + ‖u‖ ^ D) := by
  calc
    |finitePolynomial38 q L beta u| = ‖∑ a, beta a * L a (fun _ => u)‖ := by
      rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑ a, ‖beta a * L a (fun _ => u)‖ := norm_sum_le _ _
    _ ≤ ∑ a, (|beta a| * ‖L a‖) * (1 + ‖u‖ ^ D) := by
      apply Finset.sum_le_sum
      intro a _
      have hL : ‖L a (fun _ : Fin (q a) => u)‖ ≤ ‖L a‖ * ‖u‖ ^ q a := by
        simpa using (L a).le_opNorm (fun _ : Fin (q a) => u)
      rw [norm_mul, Real.norm_eq_abs (beta a)]
      calc
        |beta a| * ‖L a (fun _ => u)‖ ≤ |beta a| * (‖L a‖ * ‖u‖ ^ q a) :=
          mul_le_mul_of_nonneg_left hL (abs_nonneg _)
        _ = (|beta a| * ‖L a‖) * ‖u‖ ^ q a := by ring
        _ ≤ (|beta a| * ‖L a‖) * (1 + ‖u‖ ^ D) :=
          mul_le_mul_of_nonneg_left (normPower_le_one_add38 (norm_nonneg u) (hq a))
            (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    _ = finitePolynomialConstant38 q L beta * (1 + ‖u‖ ^ D) := by
      rw [<- Finset.sum_mul]
      rfl

theorem finitePolynomial_bound_on_ball38 (D : ℕ) (hq : forall a, q a ≤ D)
    (R : ℝ) (hR : 0 ≤ R) (u : E) (hu : ‖u‖ ≤ R) :
    |finitePolynomial38 q L beta u| ≤ finitePolynomialConstant38 q L beta * (1 + R ^ D) := by
  apply (finitePolynomial_bound38 q L beta D hq u).trans
  apply mul_le_mul_of_nonneg_left _ (finitePolynomialConstant_nonneg38 q L beta)
  gcongr

theorem finitePolynomial_bounded_image38 (D : ℕ) (hq : forall a, q a ≤ D)
    (S : Set E) (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (finitePolynomial38 q L beta '' S) := by
  obtain ⟨R, hR, hnorm ⟩ := hS.exists_pos_norm_le
  apply isBounded_iff_forall_norm_le.2
  refine ⟨finitePolynomialConstant38 q L beta * (1 + R ^ D), ?_ ⟩
  intro y hy
  obtain ⟨u, hu, rfl ⟩ := hy
  rw [Real.norm_eq_abs]
  exact finitePolynomial_bound_on_ball38 q L beta D hq R hR.le u (hnorm u hu)

/-- In particular no strictly positive coefficient hypothesis is needed analytically. -/
theorem finitePolynomial_exists_bound38 (D : ℕ) (hq : forall a, q a ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧
      forall u : E, |finitePolynomial38 q L beta u| ≤ C * (1 + ‖u‖ ^ D) :=
  ⟨finitePolynomialConstant38 q L beta, finitePolynomialConstant_nonneg38 q L beta,
    finitePolynomial_bound38 q L beta D hq ⟩

theorem finitePolynomial_zero_coefficients38 (u : E) :
    finitePolynomial38 q L (fun _ => 0) u = 0 := by
  simp [finitePolynomial38]

end Polynomial
end NlsGge.Sobolev38
