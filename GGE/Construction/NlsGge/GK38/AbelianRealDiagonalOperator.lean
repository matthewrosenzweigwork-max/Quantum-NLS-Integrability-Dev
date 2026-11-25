import NlsGge.GK38.AbelianRealSequenceSpace

/-! Concrete real diagonal multiplication, exact actual-Q decomposition and bounded inverse.
UNCOMPILED source preparation; actual P3 source coefficient bounds remain to be earned. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38.P3DiagonalOperator
noncomputable section

def diagonalCLM (n : ℤ) (d : P2Index38 n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : P2Index38 n, ‖d m‖ ≤ B) :
    P3RealSpace38 n →L[ℝ] P3RealSpace38 n :=
  lp.mapCLM 2 (fun m : P2Index38 n => d m • ContinuousLinearMap.id ℝ ℝ)
    hB (fun m => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd m)

@[simp] theorem diagonalCLM_apply (n : ℤ) (d : P2Index38 n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : P2Index38 n, ‖d m‖ ≤ B)
    (s : P3RealSpace38 n) (m : P2Index38 n) :
    diagonalCLM n d B hB hd s m = d m * s m := rfl

theorem diagonalCLM_norm_le (n : ℤ) (d : P2Index38 n → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hd : ∀ m : P2Index38 n, ‖d m‖ ≤ B) :
    ‖diagonalCLM n d B hB hd‖ ≤ B :=
  lp.norm_mapCLM_le 2 (fun m : P2Index38 n => d m • ContinuousLinearMap.id ℝ ℝ)
    hB (fun m => by
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hd m)

/-- No reciprocal cancellation occurs until the lower bound has earned nonzero. -/
theorem exists_diagonal_equiv_of_bounds (n : ℤ) (d : P2Index38 n → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hupper : ∀ m : P2Index38 n, ‖d m‖ ≤ B)
    (hlower : ∀ m : P2Index38 n, δ ≤ ‖d m‖) :
    ∃ D : P3RealSpace38 n ≃L[ℝ] P3RealSpace38 n,
      (∀ (s : P3RealSpace38 n) (m : P2Index38 n), D s m = d m * s m) ∧
      (∀ (s : P3RealSpace38 n) (m : P2Index38 n), D.symm s m = (d m)⁻¹ * s m) := by
  have hne (m : P2Index38 n) : d m ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hδ (hlower m))
  have hinv (m : P2Index38 n) : ‖(d m)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hδ (hlower m)) hδ).mpr (hlower m)
  let A := diagonalCLM n d B hB hupper
  let Ainv := diagonalCLM n (fun m => (d m)⁻¹) δ⁻¹ (inv_nonneg.mpr hδ.le) hinv
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

theorem actual_diagonal_coefficient_bound (n : ℤ)
    (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) (m : P2Index38 n) :
    ‖Q (lp.single 2 m (1 : ℝ)) m‖ ≤ ‖Q‖ := by
  have he := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (Q (lp.single 2 m (1 : ℝ))) m
  have hQ := Q.le_opNorm (lp.single 2 m (1 : ℝ))
  have hsingle : ‖lp.single (E := fun _ : P2Index38 n => ℝ) 2 m (1 : ℝ)‖ = 1 := by
    rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)), norm_one]
  rw [hsingle, mul_one] at hQ
  exact he.trans hQ

def actualDiagonal (n : ℤ) (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) :
    P3RealSpace38 n →L[ℝ] P3RealSpace38 n :=
  diagonalCLM n (fun m => Q (lp.single 2 m (1 : ℝ)) m)
    ‖Q‖ (norm_nonneg _) (actual_diagonal_coefficient_bound n Q)

def actualOffDiagonal (n : ℤ) (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) :
    P3RealSpace38 n →L[ℝ] P3RealSpace38 n := Q - actualDiagonal n Q

@[simp] theorem actualDiagonal_apply (n : ℤ)
    (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n)
    (s : P3RealSpace38 n) (m : P2Index38 n) :
    actualDiagonal n Q s m = Q (lp.single 2 m (1 : ℝ)) m * s m := rfl

theorem actual_decomposition (n : ℤ) (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) :
    Q = actualDiagonal n Q + actualOffDiagonal n Q := by
  unfold actualOffDiagonal
  abel

theorem actualOffDiagonal_diagonal_zero (n : ℤ)
    (Q : P3RealSpace38 n →L[ℝ] P3RealSpace38 n) (m : P2Index38 n) :
    actualOffDiagonal n Q (lp.single 2 m (1 : ℝ)) m = 0 := by
  change Q (lp.single 2 m (1 : ℝ)) m -
    actualDiagonal n Q (lp.single 2 m (1 : ℝ)) m = 0
  rw [actualDiagonal_apply, lp.single_apply_self, mul_one, sub_self]

end
end NlsGge.GK38.P3DiagonalOperator
