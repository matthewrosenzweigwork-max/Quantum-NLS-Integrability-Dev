import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# LIB-017: the local inverse chart of an invertible strict derivative

This bounded bridge uses the pinned Mathlib inverse function theorem. The forward map
is exactly `f`; its source and target are open neighborhoods of `a` and `f a`.
The inverse identities hold throughout these sets, and the inverse has strict derivative
`L.symm` at `f a`. No analyticity hypothesis is needed. Completeness of the domain
suffices, so in particular this applies to the Banach spaces in the packet.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace NlsGge.Atomic.LIB017

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {L : E ≃L[𝕜] F} {a : E}

/-- The open local inverse chart supplied by the invertible strict derivative. -/
def localInverseChart (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    OpenPartialHomeomorph E F :=
  hf.toOpenPartialHomeomorph f

@[simp]
theorem localInverseChart_coe (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    (localInverseChart hf : E → F) = f :=
  rfl

theorem localInverseChart_source_open (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    IsOpen (localInverseChart hf).source :=
  (localInverseChart hf).open_source

theorem localInverseChart_target_open (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    IsOpen (localInverseChart hf).target :=
  (localInverseChart hf).open_target

theorem mem_localInverseChart_source (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    a ∈ (localInverseChart hf).source :=
  hf.mem_toOpenPartialHomeomorph_source

theorem mem_localInverseChart_target (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    f a ∈ (localInverseChart hf).target :=
  hf.image_mem_toOpenPartialHomeomorph_target

theorem localInverseChart_source_mem_nhds (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    (localInverseChart hf).source ∈ 𝓝 a :=
  (localInverseChart_source_open hf).mem_nhds (mem_localInverseChart_source hf)

theorem localInverseChart_target_mem_nhds (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    (localInverseChart hf).target ∈ 𝓝 (f a) :=
  (localInverseChart_target_open hf).mem_nhds (mem_localInverseChart_target hf)

theorem localInverseChart_bijOn (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    BijOn f (localInverseChart hf).source (localInverseChart hf).target :=
  (localInverseChart hf).bijOn

theorem localInverseChart_left_inv (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    {x : E} (hx : x ∈ (localInverseChart hf).source) :
    (localInverseChart hf).symm (f x) = x :=
  (localInverseChart hf).left_inv hx

theorem localInverseChart_right_inv (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    {y : F} (hy : y ∈ (localInverseChart hf).target) :
    f ((localInverseChart hf).symm y) = y :=
  (localInverseChart hf).right_inv hy

theorem localInverseChart_eventually_left_inv
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, (localInverseChart hf).symm (f x) = x :=
  hf.eventually_left_inverse

theorem localInverseChart_eventually_right_inv
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f ((localInverseChart hf).symm y) = y :=
  hf.eventually_right_inverse

theorem localInverseChart_inverse_continuousOn
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ContinuousOn (localInverseChart hf).symm (localInverseChart hf).target :=
  (localInverseChart hf).symm.continuousOn

theorem localInverseChart_inverse_continuousAt
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    ContinuousAt (localInverseChart hf).symm (f a) :=
  hf.localInverse_continuousAt

theorem localInverseChart_inverse_hasStrictFDerivAt
    (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a) :
    HasStrictFDerivAt (localInverseChart hf).symm (L.symm : F →L[𝕜] E) (f a) :=
  hf.to_localInverse

end NlsGge.Atomic.LIB017
