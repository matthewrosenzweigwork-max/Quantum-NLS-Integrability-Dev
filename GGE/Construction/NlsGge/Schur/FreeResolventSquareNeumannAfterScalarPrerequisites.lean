import NlsGge.Schur.FreeResolventNeumannScalarPrerequisites
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- If the square of an endomorphism has norm at most one half, the exact
two-sided inverse of `1 - A` is `(1 + A) * ∑ k, (A*A)^k`. This is the
operator-algebra step used by the complementary free-resolvent construction;
the hypotheses are only norm estimates on the actual endomorphism. -/
theorem continuousLinearMap_square_neumann_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E] (A : E →L[ℂ] E) (B : ℝ) (hB : 0 ≤ B)
    (hA : ‖A‖ ≤ B) (hA2 : ‖A * A‖ ≤ (1 / 2 : ℝ)) :
    ∃ S : E →L[ℂ] E,
      S * (1 - A) = 1 ∧ (1 - A) * S = 1 ∧ ‖S‖ ≤ 2 * (1 + B) := by
  let X : E →L[ℂ] E := A * A
  let G : E →L[ℂ] E := ∑' k : ℕ, X ^ k
  have hX : ‖X‖ < 1 := by
    dsimp [X]
    exact lt_of_le_of_lt hA2 (by norm_num)
  have hseries : Summable (fun k : ℕ => X ^ k) :=
    summable_geometric_of_norm_lt_one hX
  have hgeomLeft : (1 - X) * G = 1 :=
    mul_neg_geom_series X hX
  have hAX : Commute A X := by
    dsimp [X]
    exact (Commute.refl A).mul_right (Commute.refl A)
  have hAG : Commute A G := by
    apply Commute.tsum_right
    intro k
    exact hAX.pow_right k
  have hfacLeft : (1 - A) * (1 + A) = 1 - X := by
    dsimp [X]
    noncomm_ring
  have hfacRight : (1 + A) * (1 - A) = 1 - X := by
    dsimp [X]
    noncomm_ring
  have hGcomm : G * (1 - A) = (1 - A) * G := by
    calc
      G * (1 - A) = G - G * A := by rw [mul_sub, mul_one]
      _ = G - A * G := by rw [hAG.eq]
      _ = (1 - A) * G := by rw [sub_mul, one_mul]
  let S : E →L[ℂ] E := (1 + A) * G
  have hleft : (1 - A) * S = 1 := by
    calc
      (1 - A) * S = ((1 - A) * (1 + A)) * G := by
        dsimp [S]
        rw [mul_assoc]
      _ = (1 - X) * G := by rw [hfacLeft]
      _ = 1 := hgeomLeft
  have hright : S * (1 - A) = 1 := by
    calc
      S * (1 - A) = (1 + A) * (G * (1 - A)) := by
        dsimp [S]
        rw [mul_assoc]
      _ = (1 + A) * ((1 - A) * G) := by rw [hGcomm]
      _ = ((1 + A) * (1 - A)) * G := by rw [mul_assoc]
      _ = (1 - X) * G := by rw [hfacRight]
      _ = 1 := hgeomLeft
  have hGnorm : ‖G‖ ≤ 2 := by
    have hbase := tsum_geometric_le_of_norm_lt_one X hX
    have hden : ‖X‖ ≤ (1 / 2 : ℝ) := by
      dsimp [X]
      exact hA2
    have hinv : (1 - ‖X‖)⁻¹ ≤ 2 := real_inv_one_sub_le_two hden
    have hone : ‖(1 : E →L[ℂ] E)‖ = 1 := norm_one
    rw [hone] at hbase
    calc
      ‖G‖ ≤ 1 - 1 + (1 - ‖X‖)⁻¹ := hbase
      _ ≤ 2 := by linarith
  refine ⟨S, hright, hleft, ?_⟩
  calc
    ‖S‖ = ‖(1 + A) * G‖ := rfl
    _ ≤ ‖1 + A‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ (1 + B) * 2 := by
      apply mul_le_mul
      · exact norm_one_add_le_of_norm_le A B hA
      · exact hGnorm
      · exact norm_nonneg _
      · positivity
    _ = 2 * (1 + B) := by ring

end NlsGge.Schur
