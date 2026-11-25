import NlsGge.Schur.FreeResolventComplementarySquareBoundAfterQDTransport
import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange
import NlsGge.Schur.ComplementaryResolventMonoidInverseIntertwiningPrerequisite

set_option autoImplicit false

namespace NlsGge.Schur

/-- The actual Schur factors intertwine with the free resolvent from the two
actual projection support identities. -/
theorem freeResolventSchurFactors_intertwine_afterMonoid_actual22
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D V Q : E →L[ℂ] E)
    (hQD : Q.comp D = D) (hDQ : D.comp Q = D) :
    (1 - D.comp (V.comp Q)).comp D =
      D.comp (1 - Q.comp (V.comp D)) := by
  have hleft : (D.comp (V.comp Q)).comp D = D.comp (V.comp D) := by
    calc
      (D.comp (V.comp Q)).comp D =
          D.comp (V.comp (Q.comp D)) := by
            simp only [ContinuousLinearMap.comp_assoc]
      _ = D.comp (V.comp D) := by rw [hQD]
  have hright : D.comp (Q.comp (V.comp D)) = D.comp (V.comp D) := by
    calc
      D.comp (Q.comp (V.comp D)) = (D.comp Q).comp (V.comp D) := by
        rw [← ContinuousLinearMap.comp_assoc]
      _ = D.comp (V.comp D) := by rw [hDQ]
  calc
    (1 - D.comp (V.comp Q)).comp D =
        D - (D.comp (V.comp Q)).comp D := by
          rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def,
            ContinuousLinearMap.id_comp]
    _ = D - D.comp (V.comp D) := by rw [hleft]
    _ = D - D.comp (Q.comp (V.comp D)) := by rw [hright]
    _ = D.comp (1 - Q.comp (V.comp D)) := by
          rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.one_def,
            ContinuousLinearMap.comp_id]

/-- The actual complementary resolvent formula follows from the true
intertwining relation; multiplication order is discharged in a generic monoid. -/
theorem freeResolventSchurCanonicalFormula_afterMonoid_actual22
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D V Q S₁ S₁' S₂ S₂' : E →L[ℂ] E)
    (hQD : Q.comp D = D) (hDQ : D.comp Q = D)
    (hS₁left : S₁.comp (1 - D.comp (V.comp Q)) = 1)
    (hS₁right : (1 - D.comp (V.comp Q)).comp S₁ = 1)
    (hS₁'left : S₁'.comp (1 - D.comp (V.comp Q)) = 1)
    (hS₁'right : (1 - D.comp (V.comp Q)).comp S₁' = 1)
    (hS₂left : S₂.comp (1 - Q.comp (V.comp D)) = 1)
    (hS₂right : (1 - Q.comp (V.comp D)).comp S₂ = 1)
    (hS₂'left : S₂'.comp (1 - Q.comp (V.comp D)) = 1)
    (hS₂'right : (1 - Q.comp (V.comp D)).comp S₂' = 1) :
    S₁.comp D = D.comp S₂ ∧
      S₁.comp D = S₁'.comp D ∧ D.comp S₂ = D.comp S₂' := by
  let X : E →L[ℂ] E := 1 - D.comp (V.comp Q)
  let Y : E →L[ℂ] E := 1 - Q.comp (V.comp D)
  have hintertwine : X.comp D = D.comp Y := by
    exact freeResolventSchurFactors_intertwine_afterMonoid_actual22 D V Q hQD hDQ
  have hformula : S₁.comp D = D.comp S₂ := by
    have h := monoid_intertwining_twoSidedInverses_actual22
      X Y D S₁ S₂ (by simpa only [ContinuousLinearMap.mul_def] using hintertwine)
      (by simpa only [ContinuousLinearMap.mul_def] using hS₁left)
      (by simpa only [ContinuousLinearMap.mul_def] using hS₂right)
    simpa only [ContinuousLinearMap.mul_def] using h
  have hleftunique : S₁ = S₁' := by
    have h := monoid_twoSidedInverse_unique_actual22 X S₁ S₁'
      (by simpa only [ContinuousLinearMap.mul_def] using hS₁left)
      (by simpa only [ContinuousLinearMap.mul_def] using hS₁'right)
    exact h
  have hrightunique : S₂ = S₂' := by
    have h := monoid_twoSidedInverse_unique_actual22 Y S₂ S₂'
      (by simpa only [ContinuousLinearMap.mul_def] using hS₂left)
      (by simpa only [ContinuousLinearMap.mul_def] using hS₂'right)
    exact h
  exact ⟨hformula, by rw [hleftunique], by rw [hrightunique]⟩

end NlsGge.Schur
