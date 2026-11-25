import Mathlib
import NlsGge.Atomic.LIB.LIB081

/- G5-031 SUPPORT 1 `G5031Sup1` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5031Sup1.lean, namespace NlsGge.GKDefinitionDesign.G5031Sup1.
   Local (ContDiffAt at the evaluation point) version of the landed LIB081 constant-tensor Jacobi identity.  The proof is the landed
   LIB081 proof with the hypotheses `ContDiff 𝕜 2 f` weakened to `ContDiffAt 𝕜 2 f x`, which is all that is used: only the derivative of the
   bracket at the single point x and symmetry of the second derivative at x enter.  Needed because the angle primitives and the action are
   only defined/analytic on open subsets of the potential space. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.GKDefinitionDesign
namespace G5031Sup1

open NlsGge.Atomic.LIB

theorem fderiv_constantPoisson_at {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (f g : E → 𝕜) (x v : E)
    (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x) :
    fderiv 𝕜 (constantPoisson J f g) x v =
      fderiv 𝕜 (fderiv 𝕜 f) x v (J (fderiv 𝕜 g x)) +
      fderiv 𝕜 f x (J (fderiv 𝕜 (fderiv 𝕜 g) x v)) := by
  let B := constantPoissonBilinear J
  have hfd : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgd : DifferentiableAt 𝕜 (fderiv 𝕜 g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hderiv := ContinuousLinearMap.fderiv_of_bilinear B hfd hgd
  have h := congrArg (fun L : E →L[𝕜] 𝕜 => L v) hderiv
  change fderiv 𝕜 (fun y => B (fderiv 𝕜 f y) (fderiv 𝕜 g y)) x v = _
  simpa [B, constantPoissonBilinear, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, add_comm] using h

theorem constantPoisson_jacobi_at {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (hJ : IsSkewDualMap J)
    (f g h : E → 𝕜) (x : E) (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g x)
    (hh : ContDiffAt 𝕜 2 h x) :
    constantPoisson J (constantPoisson J f g) h x +
      constantPoisson J (constantPoisson J g h) f x +
      constantPoisson J (constantPoisson J h f) g x = 0 := by
  have hexpand (p q r : E → 𝕜) (hp : ContDiffAt 𝕜 2 p x) (hq : ContDiffAt 𝕜 2 q x) :
      constantPoisson J (constantPoisson J p q) r x =
        fderiv 𝕜 (fderiv 𝕜 p) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 q x)) -
          fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 p x)) := by
    change fderiv 𝕜 (constantPoisson J p q) x (J (fderiv 𝕜 r x)) = _
    rw [fderiv_constantPoisson_at J p q x _ hp hq]
    have hskew := hJ (fderiv 𝕜 p x)
      (fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)))
    have hskew' : fderiv 𝕜 p x
        (J (fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)))) =
        -fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 p x)) := by
      simpa only [ContinuousLinearMap.apply_apply] using hskew
    rw [hskew']
    ring
  rw [hexpand f g h hf hg, hexpand g h f hg hh, hexpand h f g hh hf]
  have hfs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap f x
    (J (fderiv 𝕜 h x)) (J (fderiv 𝕜 g x)) hf
  have hgs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap g x
    (J (fderiv 𝕜 f x)) (J (fderiv 𝕜 h x)) hg
  have hhs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap h x
    (J (fderiv 𝕜 g x)) (J (fderiv 𝕜 f x)) hh
  rw [hfs, hgs, hhs]
  ring

end G5031Sup1
end NlsGge.GKDefinitionDesign
