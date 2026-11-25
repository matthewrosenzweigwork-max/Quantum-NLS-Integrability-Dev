import Mathlib
import NlsGge.GK38.XiSqCenteredKernel
import NlsGge.GK38.XiSqLocal
import NlsGge.GK38.XiSqChi
import NlsGge.GK38.TauGamma
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.G2.G2046
import NlsGge.ThirdConsultation.G2.Reparam032N
import NlsGge.ThirdConsultation.G2.Reparam032O
import NlsGge.ThirdConsultation.G2.Reparam032P

                                                                                       
                                                                                               
                                                                                                         
                                                                                                                 
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open scoped Real
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def rescaledActionIntegrand (φ : PotPair) (n : ℤ) (t : ℝ) : ℂ :=
  ((t : ℂ) - 2*(lamDot φ n-tauN φ n)/gap φ n)^2 *
    a5Chi38 n (φ,tauN φ n + (t : ℂ)*gap φ n/2) /
    (Real.sqrt (1-t^2) : ℂ)

def rescaledActionIntegral (φ : PotPair) (n : ℤ) : ℂ :=
  (2/(Real.pi : ℂ)) * ∫ t in (-1 : ℝ)..1, rescaledActionIntegrand φ n t

/-- The integrand without the square-root weight (the polynomial-times-χ factor). -/
def arcF (φ : PotPair) (n : ℤ) (t : ℝ) : ℂ :=
  ((t : ℂ) - 2*(lamDot φ n-tauN φ n)/gap φ n)^2 * a5Chi38 n (φ,tauN φ n + (t : ℂ)*gap φ n/2)

theorem exp_add_inv_eq (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      2 * ((Real.cos θ : ℝ) : ℂ) := by
  have e2 : Complex.exp (-((θ : ℂ) * Complex.I)) = Complex.exp (-(θ : ℂ) * Complex.I) :=
    congrArg Complex.exp (by ring)
  rw [← Complex.exp_neg, e2, Complex.ofReal_cos]
  unfold Complex.cos
  ring

theorem arcF_continuousOn (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    ContinuousOn (arcF φ n) (Icc (-1) 1) := by
  have hs : ∀ m : ℤ, segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ ball (discC φ m) (discR φ m) := by
    obtain ⟨c, N, -, h⟩ := isolating_family38 φ hφ
    unfold IsolatingSpectral38 at h
    exact fun m => (h.1 m).1
  have hτ : tauN φ n = (lamPlus φ n + lamMinus φ n) / 2 := tauN_value38 φ hφ n
  have hmem : ∀ t : ℝ, t ∈ Icc (-1 : ℝ) 1 →
      (φ, tauN φ n + (t : ℂ) * gap φ n / 2) ∈ a5OmittedRootDomain38 n := by
    intro t ht
    have hseg : tauN φ n + (t : ℂ) * gap φ n / 2 ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      refine ⟨(1 - t) / 2, (1 + t) / 2, by linarith [ht.2], by linarith [ht.1], by ring, ?_⟩
      simp only [Complex.real_smul, gap]
      push_cast
      rw [hτ]
      ring
    exact a5OwnClosedBall_omittedDomain38 φ hφ (discC φ) (discR φ) (isolating_family38 φ hφ) n _
      (ball_subset_closedBall (hs n hseg))
  apply ContinuousOn.mul
  · exact (by fun_prop : Continuous fun t : ℝ =>
      ((t : ℂ) - 2*(lamDot φ n-tauN φ n)/gap φ n)^2).continuousOn
  · intro t ht
    apply ContinuousAt.continuousWithinAt
    have hAn := a5Chi_analytic38 n _ (hmem t ht)
    have hc : Continuous (fun t : ℝ => (φ, tauN φ n + (t : ℂ) * gap φ n / 2)) := by fun_prop
    exact ContinuousAt.comp (g := a5Chi38 n) (f := fun t : ℝ => (φ, tauN φ n + (t : ℂ) * gap φ n / 2))
      hAn.continuousAt hc.continuousAt

theorem G2_032 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (hgap : gap φ n ≠ 0) :
    gamma2 φ n ≠ 0 ∧ IntervalIntegrable (rescaledActionIntegrand φ n) volume (-1) 1 ∧
      4*gkActionC38 φ n/gamma2 φ n = rescaledActionIntegral φ n := by
  have hγ : lamPlus φ n - lamMinus φ n ≠ 0 := hgap
  have hg2 : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hφ n
  have hg2ne : gamma2 φ n ≠ 0 := by rw [hg2]; exact pow_ne_zero 2 hγ
  have hF := arcF_continuousOn φ hφ n
  refine ⟨hg2ne, ?_, ?_⟩
  · exact G2032Arcsine.arcsine_intervalIntegrable (arcF φ n) hF
  · have hf := isolating_family38 φ hφ
    have hK := G2032KerP.kernel_unit_circle φ hφ n hγ
    have hX := a5CenteredLocalXi_identity38 φ hφ (discC φ) (discR φ) hf n
    unfold a5CenteredLocalXi38 at hX
    rw [hK] at hX
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hI : (∫ θ in (0 : ℝ)..(2 * π), G2032KerP.Xf φ n (tauN φ n)
          ((lamPlus φ n - lamMinus φ n) / 4) θ * G2032KerP.Lf φ n (tauN φ n)
          ((lamPlus φ n - lamMinus φ n) / 4) θ ^ 2) =
        ((lamPlus φ n - lamMinus φ n) ^ 2 / 4) * ∫ θ in (0 : ℝ)..(2 * π), arcF φ n (Real.cos θ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [G2032KerP.Xf, G2032KerP.Lf, G2032PerO.Jth, arcF, gap]
      rw [exp_add_inv_eq]
      have harg : tauN φ n + (lamPlus φ n - lamMinus φ n) / 4 * (2 * ((Real.cos θ : ℝ) : ℂ)) =
          tauN φ n + ((Real.cos θ : ℝ) : ℂ) * (lamPlus φ n - lamMinus φ n) / 2 := by ring
      rw [harg]
      field_simp
      ring
    have hJ : (∫ θ in (0 : ℝ)..(2 * π), arcF φ n (Real.cos θ)) =
        2 * ∫ t in (-1 : ℝ)..1, arcF φ n t / ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) :=
      G2032Arcsine.arcsine_substitution (arcF φ n) hF
    rw [hI, hJ] at hX
    rw [hg2] at hX
    have hdef : (∫ t in (-1 : ℝ)..1, rescaledActionIntegrand φ n t) =
        ∫ t in (-1 : ℝ)..1, arcF φ n t / ((Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) := rfl
    unfold rescaledActionIntegral
    rw [hdef, hg2, ← hX]
    field_simp
    ring
end
end NlsGge.GKDefinitionDesign
