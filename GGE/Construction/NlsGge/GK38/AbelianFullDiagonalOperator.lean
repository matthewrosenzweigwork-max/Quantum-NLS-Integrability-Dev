import NlsGge.GK38.AbelianFullRealSpace
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Normed.Group.Continuity

/-! Genuine full-Z real lp2 diagonal multiplication and inverse, exact diagonal
plus off-diagonal decomposition, and positive lower bound from square error.
Actual Qstar coefficient premises are realized in a separate leaf. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P6DiagonalOperator
noncomputable section

def diagonalCLM (d : ℤ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : ℤ, ‖d m‖ ≤ B) :
    P6RealSpace38 →L[ℝ] P6RealSpace38 :=
  lp.mapCLM 2 (fun m : ℤ => d m • ContinuousLinearMap.id ℝ ℝ)
    hB (fun m => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd m)

@[simp] theorem diagonalCLM_apply (d : ℤ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : ℤ, ‖d m‖ ≤ B)
    (s : P6RealSpace38) (m : ℤ) :
    diagonalCLM d B hB hd s m = d m * s m := rfl

theorem diagonalCLM_norm_le (d : ℤ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : ℤ, ‖d m‖ ≤ B) :
    ‖diagonalCLM d B hB hd‖ ≤ B :=
  lp.norm_mapCLM_le 2 (fun m : ℤ => d m • ContinuousLinearMap.id ℝ ℝ)
    hB (fun m => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd m)

/-- No reciprocal cancellation occurs until the lower bound has earned nonzero. -/
theorem exists_diagonal_equiv_of_bounds (d : ℤ → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hupper : ∀ m : ℤ, ‖d m‖ ≤ B)
    (hlower : ∀ m : ℤ, δ ≤ ‖d m‖) :
    ∃ D : P6RealSpace38 ≃L[ℝ] P6RealSpace38,
      (∀ (s : P6RealSpace38) (m : ℤ), D s m = d m * s m) ∧
      (∀ (s : P6RealSpace38) (m : ℤ), D.symm s m = (d m)⁻¹ * s m) := by
  have hne (m : ℤ) : d m ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hδ (hlower m))
  have hinv (m : ℤ) : ‖(d m)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hδ (hlower m)) hδ).mpr (hlower m)
  let A := diagonalCLM d B hB hupper
  let Ainv := diagonalCLM (fun m => (d m)⁻¹) δ⁻¹ (inv_nonneg.mpr hδ.le) hinv
  have hleft : Function.LeftInverse Ainv A := by
    intro s
    apply Subtype.ext
    funext m
    change (d m)⁻¹ * (d m * s m) = s m
    rw [← mul_assoc, inv_mul_cancel₀ (hne m), one_mul]
  have hright : Function.RightInverse Ainv A := by
    intro s
    apply Subtype.ext
    funext m
    change d m * ((d m)⁻¹ * s m) = s m
    rw [← mul_assoc, mul_inv_cancel₀ (hne m), one_mul]
  refine ⟨ContinuousLinearEquiv.equivOfInverse A Ainv hleft hright, ?_, ?_⟩
  · intro s m
    rfl
  · intro s m
    rfl

theorem actual_diagonal_coefficient_bound (Q : P6RealSpace38 →L[ℝ] P6RealSpace38) (m : ℤ) :
    ‖Q (lp.single 2 m (1 : ℝ)) m‖ ≤ ‖Q‖ := by
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (Q (lp.single 2 m (1 : ℝ))) m
  have hQ := Q.le_opNorm (lp.single 2 m (1 : ℝ))
  have hsingle : ‖lp.single (E := fun _ : ℤ => ℝ) 2 m (1 : ℝ)‖ = 1 := by
    rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one]
  rw [hsingle, mul_one] at hQ
  exact he.trans hQ

def actualDiagonal (Q : P6RealSpace38 →L[ℝ] P6RealSpace38) :
    P6RealSpace38 →L[ℝ] P6RealSpace38 :=
  diagonalCLM (fun m => Q (lp.single 2 m (1 : ℝ)) m)
    ‖Q‖ (norm_nonneg _) (actual_diagonal_coefficient_bound Q)

def actualOffDiagonal (Q : P6RealSpace38 →L[ℝ] P6RealSpace38) :
    P6RealSpace38 →L[ℝ] P6RealSpace38 := Q - actualDiagonal Q

@[simp] theorem actualDiagonal_apply (Q : P6RealSpace38 →L[ℝ] P6RealSpace38)
    (s : P6RealSpace38) (m : ℤ) :
    actualDiagonal Q s m = Q (lp.single 2 m (1 : ℝ)) m * s m := rfl

theorem actual_decomposition (Q : P6RealSpace38 →L[ℝ] P6RealSpace38) :
    Q = actualDiagonal Q + actualOffDiagonal Q := by
  unfold actualOffDiagonal
  abel

theorem actualOffDiagonal_diagonal_zero (Q : P6RealSpace38 →L[ℝ] P6RealSpace38) (m : ℤ) :
    actualOffDiagonal Q (lp.single 2 m (1 : ℝ)) m = 0 := by
  change Q (lp.single 2 m (1 : ℝ)) m -
    actualDiagonal Q (lp.single 2 m (1 : ℝ)) m = 0
  rw [actualDiagonal_apply, lp.single_apply_self, mul_one, sub_self]

theorem exists_pos_lower_of_square_error (d a : ℤ → ℝ)
    (hne : ∀ m, d m ≠ 0) (ha0 : ∀ m, 0 ≤ a m)
    (has : Summable (fun m => a m^2)) (herror : ∀ m, ‖d m-2‖ ≤ a m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m, δ ≤ ‖d m‖ := by
  have ha2 : Tendsto (fun m => a m^2) cofinite (𝓝 0) := has.tendsto_cofinite_zero
  have ha : Tendsto a cofinite (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp ha2
    have hsqrt : (fun m => Real.sqrt (a m^2)) = a := by
      funext m
      rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (ha0 m)]
    change Tendsto (fun m => Real.sqrt (a m^2)) cofinite (𝓝 (Real.sqrt 0)) at hs
    simpa only [hsqrt,Real.sqrt_zero] using hs
  have hd0 : Tendsto (fun m => d m-2) cofinite (𝓝 0) := squeeze_zero_norm herror ha
  have hd : Tendsto d cofinite (𝓝 (2 : ℝ)) := by
    simpa only [sub_add_cancel,zero_add] using hd0.add_const 2
  have hinv := (hd.inv₀ (by norm_num : (2 : ℝ) ≠ 0)).norm
  obtain ⟨B,hB⟩ := hinv.bddAbove_range_of_cofinite
  let M : ℝ := max B 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right B 1)
  refine ⟨M⁻¹,inv_pos.mpr hM,?_⟩
  intro m
  have hb : ‖(d m)⁻¹‖ ≤ M := (hB (mem_range_self m)).trans (le_max_left B 1)
  have he : ‖d m‖*‖(d m)⁻¹‖ = 1 := by
    rw [← norm_mul,mul_inv_cancel₀ (hne m),norm_one]
  have hmul : 1 ≤ ‖d m‖*M := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  rw [← one_div]
  exact (div_le_iff₀ hM).mpr hmul


end
end NlsGge.GK38.P6DiagonalOperator
