import NlsGge.Schur.FreeResolventComplementaryDQTransportAfterCoordinateRange

set_option autoImplicit false

namespace NlsGge.Schur

/-- For actual continuous-linear-map composition, the opposite `Q V D`
product factors through `D Q = D` before the `D V D` abbreviation is used. -/
theorem continuousLinearMap_QVD_square_factorization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q V D DVD : E →L[ℂ] E)
    (hDQ : D.comp Q = D)
    (hDVD : D.comp (V.comp D) = DVD) :
    (Q.comp (V.comp D)).comp (Q.comp (V.comp D)) =
      Q.comp (V.comp DVD) := by
  calc
    (Q.comp (V.comp D)).comp (Q.comp (V.comp D)) =
        Q.comp (V.comp ((D.comp Q).comp (V.comp D))) := by
          simp only [ContinuousLinearMap.comp_assoc]
    _ = Q.comp (V.comp (D.comp (V.comp D))) := by rw [hDQ]
    _ = Q.comp (V.comp DVD) := by rw [hDVD]

end NlsGge.Schur
