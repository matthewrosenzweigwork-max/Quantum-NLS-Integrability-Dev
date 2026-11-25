import NlsGge.GK38.ActionGradientQuotient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
open Set Metric Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.Pilot
namespace NlsGge.GK38.ActionGradient
noncomputable section

theorem gradDiscrim_spectral_hasDeriv (φ : PotPair) (z : ℂ) (h : PotPair) :
    HasDerivAt (fun w : ℂ => gradDiscrimCLM φ w h)
      (fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h) z := by
  let F : PotPair × ℂ → ℂ := fun p => discrim p.1 p.2
  let p : PotPair × ℂ := (φ, z)
  let v : PotPair × ℂ := (h, 0)
  let e : PotPair × ℂ := (0, 1)
  let evv : ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ v
  let eve : ((PotPair × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ e
  have hA : AnalyticAt ℂ F p := analyticOnNhd_discrim p (mem_univ _)
  have hJ : HasFDerivAt (fderiv ℂ F) (fderiv ℂ (fderiv ℂ F) p) p :=
    hA.fderiv.differentiableAt.hasFDerivAt
  have hv : HasFDerivAt (fun q => fderiv ℂ F q v)
      (evv.comp (fderiv ℂ (fderiv ℂ F) p)) p := evv.hasFDerivAt.comp p hJ
  have he : HasFDerivAt (fun q => fderiv ℂ F q e)
      (eve.comp (fderiv ℂ (fderiv ℂ F) p)) p := eve.hasFDerivAt.comp p hJ
  have hspectral : HasDerivAt (fun w : ℂ => (φ, w)) e z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hline := hv.comp_hasDerivAt z hspectral
  have hpotential : HasFDerivAt (fun ψ : PotPair => (ψ, z))
      (ContinuousLinearMap.inl ℂ PotPair ℂ) φ := by
    convert (hasFDerivAt_id φ).prodMk (hasFDerivAt_const z φ) using 1 <;> ext q <;> rfl
  have hpartial := he.comp φ hpotential
  simp only [Function.comp_def] at hpartial
  have hfun : (fun ψ : PotPair => deriv (discrim ψ) z) =
      (fun ψ : PotPair => fderiv ℂ F (ψ, z) e) := by
    funext ψ
    exact (jointDiscrim_derivative38 ψ z).symm
  have hcoef : fderiv ℂ (fun ψ : PotPair => deriv (discrim ψ) z) φ h =
      fderiv ℂ (fderiv ℂ F) p v e := by
    rw [hfun, hpartial.fderiv]
    rfl
  have hactual : (fun w : ℂ => gradDiscrimCLM φ w h) =
      (fun w : ℂ => fderiv ℂ F (φ, w) v) := by
    funext w
    rw [gradDiscrim_eq_partial]
    rfl
  rw [hactual]
  apply hline.congr_deriv
  rw [hcoef]
  exact hA.contDiffAt.isSymmSndFDerivAt_of_omega e v

end
end NlsGge.GK38.ActionGradient
