import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- Coordinate expansion of the actual resonant projection on the actual
paired Fourier basis. -/
theorem resonantParityPair_two_term_prerequisite (n : ℤ) (x : ParityPair n) :
    resonantParityPair n x =
      (inner ℂ (parityPairVector n (true, resonantIndex n)) x) •
          parityPairVector n (true, resonantIndex n) +
        (inner ℂ (parityPairVector n (false, resonantIndex n)) x) •
          parityPairVector n (false, resonantIndex n) := by
  apply (parityPairRepr n).injective
  apply lp.ext
  funext i
  rw [resonantParityPair_repr_apply]
  simp only [map_add, map_smul, parityPairRepr_vector, lp.coeFn_single]
  rcases i with ⟨b, m⟩
  change (if m = resonantIndex n then parityPairRepr n x (b, m) else 0) =
    inner ℂ (parityPairVector n (true, resonantIndex n)) x *
        (lp.single (E := fun _ : Bool × Sector n => ℂ) 2 (true, resonantIndex n) (1 : ℂ)) (b, m) +
      inner ℂ (parityPairVector n (false, resonantIndex n)) x *
        (lp.single (E := fun _ : Bool × Sector n => ℂ) 2 (false, resonantIndex n) (1 : ℂ)) (b, m)
  by_cases hm : m = resonantIndex n
  · subst m
    cases b <;> simp [parityPairRepr_inner, lp.single_apply]
  · simp [hm, lp.single_apply]

/-- Cauchy--Schwarz for the exact inner product dictionary used by the
actual paired parity space, phrased as a typed prerequisite for the rank-two
operator estimate. -/
theorem parityPair_inner_norm_le_prerequisite
    (n : ℤ) (x y : ParityPair n) :
    ‖inner ℂ x y‖ ≤ ‖x‖ * ‖y‖ := by
  calc
    ‖inner ℂ x y‖ = ‖innerSL ℂ x y‖ := by
      simpa only [innerSL_apply_apply]
    _ ≤ ‖innerSL ℂ x‖ * ‖y‖ := (innerSL ℂ x).le_opNorm y
    _ = ‖x‖ * ‖y‖ := by rw [innerSL_apply_norm]

private theorem parityPair_resonant_basis_norm_prerequisite (n : ℤ) (b : Bool) :
    ‖parityPairVector n (b, resonantIndex n)‖ = 1 := by
  rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
  simp

/-- Generic actual rank-two column estimate using the proved coordinates and
the typed Hilbert-space inner bound. -/
theorem comp_resonantParityPair_opNorm_le_columns_prerequisite
    (n : ℤ) (S : ParityPair n →L[ℂ] ParityPair n) :
    ‖S.comp (resonantParityPair n)‖ ≤
      ‖S (parityPairVector n (true, resonantIndex n))‖ +
        ‖S (parityPairVector n (false, resonantIndex n))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [ContinuousLinearMap.comp_apply, resonantParityPair_two_term_prerequisite]
  have htrue :
      ‖inner ℂ (parityPairVector n (true, resonantIndex n)) x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖parityPairVector n (true, resonantIndex n)‖ * ‖x‖ :=
        parityPair_inner_norm_le_prerequisite n _ _
      _ = ‖x‖ := by rw [parityPair_resonant_basis_norm_prerequisite]; simp
  have hfalse :
      ‖inner ℂ (parityPairVector n (false, resonantIndex n)) x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖parityPairVector n (false, resonantIndex n)‖ * ‖x‖ :=
        parityPair_inner_norm_le_prerequisite n _ _
      _ = ‖x‖ := by rw [parityPair_resonant_basis_norm_prerequisite]; simp
  calc
    ‖S ((inner ℂ (parityPairVector n (true, resonantIndex n)) x) •
          parityPairVector n (true, resonantIndex n) +
        (inner ℂ (parityPairVector n (false, resonantIndex n)) x) •
          parityPairVector n (false, resonantIndex n))‖ ≤
        ‖S (parityPairVector n (true, resonantIndex n))‖ *
            ‖inner ℂ (parityPairVector n (true, resonantIndex n)) x‖ +
          ‖S (parityPairVector n (false, resonantIndex n))‖ *
            ‖inner ℂ (parityPairVector n (false, resonantIndex n)) x‖ := by
      calc
        _ = ‖(inner ℂ (parityPairVector n (true, resonantIndex n)) x) •
              S (parityPairVector n (true, resonantIndex n)) +
            (inner ℂ (parityPairVector n (false, resonantIndex n)) x) •
              S (parityPairVector n (false, resonantIndex n))‖ := by
          rw [map_add, map_smul, map_smul]
        _ ≤ _ := norm_add_le _ _
        _ = _ := by simp [norm_smul, mul_comm]
    _ ≤ (‖S (parityPairVector n (true, resonantIndex n))‖ +
          ‖S (parityPairVector n (false, resonantIndex n))‖) * ‖x‖ := by
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left htrue (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hfalse (norm_nonneg _))

/-- Generic actual rank-two row estimate using explicit representing vectors. -/
theorem resonantParityPair_comp_opNorm_le_rows_prerequisite
    (n : ℤ) (S : ParityPair n →L[ℂ] ParityPair n)
    (r₁ r₂ : ParityPair n)
    (h₁ : ∀ x, inner ℂ (parityPairVector n (true, resonantIndex n)) (S x) =
      inner ℂ r₁ x)
    (h₂ : ∀ x, inner ℂ (parityPairVector n (false, resonantIndex n)) (S x) =
      inner ℂ r₂ x) :
    ‖(resonantParityPair n).comp S‖ ≤ ‖r₁‖ + ‖r₂‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  rw [ContinuousLinearMap.comp_apply, resonantParityPair_two_term_prerequisite,
    h₁, h₂]
  calc
    ‖(inner ℂ r₁ x) • parityPairVector n (true, resonantIndex n) +
        (inner ℂ r₂ x) • parityPairVector n (false, resonantIndex n)‖ ≤
        ‖inner ℂ r₁ x‖ + ‖inner ℂ r₂ x‖ := by
      calc
        _ ≤ ‖(inner ℂ r₁ x) • parityPairVector n (true, resonantIndex n)‖ +
              ‖(inner ℂ r₂ x) • parityPairVector n (false, resonantIndex n)‖ :=
          norm_add_le _ _
        _ = _ := by
          rw [norm_smul, norm_smul]
          rw [parityPair_resonant_basis_norm_prerequisite,
            parityPair_resonant_basis_norm_prerequisite]
          simp
    _ ≤ (‖r₁‖ + ‖r₂‖) * ‖x‖ := by
      rw [add_mul]
      exact add_le_add
        (parityPair_inner_norm_le_prerequisite n r₁ x)
        (parityPair_inner_norm_le_prerequisite n r₂ x)

end NlsGge.Schur
