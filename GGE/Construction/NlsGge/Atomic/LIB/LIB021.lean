import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
Finite-rank continuous linear maps factor continuously through their actual
range. The finite-dimensional range is locally compact, so this factorization
also proves compactness of the original map.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Atomic.LIB

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map corestricted to its actual range. -/
def finiteRankCorestriction (T : E →L[𝕜] F) :
    E →L[𝕜] LinearMap.range T.toLinearMap :=
  T.rangeRestrict

omit [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜] in
/-- A finite-rank continuous linear map factors continuously through its actual
finite-dimensional range. -/
theorem finiteRank_factorization (T : E →L[𝕜] F)
    (h : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    ∃ S : E →L[𝕜] LinearMap.range T.toLinearMap,
      T = (LinearMap.range T.toLinearMap).subtypeL.comp S ∧
        FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) := by
  exact ⟨finiteRankCorestriction T, by ext x; rfl, h⟩

/-- A bounded linear map with finite-dimensional range is a compact operator. -/
theorem finiteRank_isCompact (T : E →L[𝕜] F)
    (h : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap)) :
    IsCompactOperator T := by
  letI : FiniteDimensional 𝕜 (LinearMap.range T.toLinearMap) := h
  letI : LocallyCompactSpace (LinearMap.range T.toLinearMap) :=
    LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 _
  have hcore : IsCompactOperator (finiteRankCorestriction T) :=
    isCompactOperator_of_locallyCompactSpace_dom (finiteRankCorestriction T)
  have hfactor : T = (LinearMap.range T.toLinearMap).subtypeL.comp
      (finiteRankCorestriction T) := by
    ext x
    rfl
  rw [hfactor]
  exact hcore.clm_comp (LinearMap.range T.toLinearMap).subtypeL

end NlsGge.Atomic.LIB
