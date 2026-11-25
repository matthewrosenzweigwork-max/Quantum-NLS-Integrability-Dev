import NlsGge.Atomic.LIB.LIB017
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Analyticity of the actual local inverse chart from LIB017.
The strict derivative is derived from analyticity and the given derivative
equivalence. Its inverse is analytic on a smaller open target neighborhood. -/

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace NlsGge.Atomic.LIB018

open NlsGge.Atomic.LIB017

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {L : E ≃L[𝕜] F} {a : E}

/-- LIB017's same local chart, with strict differentiability proved from analyticity. -/
def analyticLocalInverseChart (hf : AnalyticAt 𝕜 f a)
    (hL : fderiv 𝕜 f a = (L : E →L[𝕜] F)) : OpenPartialHomeomorph E F :=
  localInverseChart (show HasStrictFDerivAt f (L : E →L[𝕜] F) a from
    hL ▸ hf.hasStrictFDerivAt)

/-- The inverse of the source chart is analytic at the image of the base point. -/
theorem localInverseChart_analyticAt (hf : AnalyticAt 𝕜 f a)
    (hL : fderiv 𝕜 f a = (L : E →L[𝕜] F)) :
    AnalyticAt 𝕜 (analyticLocalInverseChart hf hL).symm (f a) := by
  obtain ⟨p, hp⟩ := hf
  have h0 : a ∈ (analyticLocalInverseChart ⟨p, hp⟩ hL).source :=
    mem_localInverseChart_source _
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm
      (L : E →L[𝕜] F) := by
    apply (continuousMultilinearCurryFin1 𝕜 E F).injective
    simpa using hp.fderiv_eq.symm.trans hL
  exact ((analyticLocalInverseChart ⟨p, hp⟩ hL).hasFPowerSeriesAt_symm
    h0 hp hcoeff).analyticAt

/-- Shrink the target to an open neighborhood on which that same inverse is analytic. -/
theorem localInverseChart_analyticOnNhd_target (hf : AnalyticAt 𝕜 f a)
    (hL : fderiv 𝕜 f a = (L : E →L[𝕜] F)) :
    ∃ V : Set F, IsOpen V ∧ f a ∈ V ∧
      V ⊆ (analyticLocalInverseChart hf hL).target ∧
      AnalyticOnNhd 𝕜 (analyticLocalInverseChart hf hL).symm V := by
  let e := analyticLocalInverseChart hf hL
  refine ⟨e.target ∩ {y | AnalyticAt 𝕜 e.symm y},
    e.open_target.inter (isOpen_analyticAt 𝕜 e.symm), ?_,
    inter_subset_left, ?_⟩
  · exact ⟨mem_localInverseChart_target _, localInverseChart_analyticAt hf hL⟩
  · intro y hy
    exact hy.2

end NlsGge.Atomic.LIB018
