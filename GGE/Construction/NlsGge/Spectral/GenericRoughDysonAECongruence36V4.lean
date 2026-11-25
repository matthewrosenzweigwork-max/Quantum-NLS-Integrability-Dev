import NlsGge.Spectral.ActualPhysicalCouplingCoefficientHomogeneity36V2
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
/-- Equality of coefficients almost everywhere on the source interval gives
pointwise equality of every finite ordered Dyson integral on that interval.
No choice of pointwise representative or extra regularity is assumed. -/
theorem genericRoughMatrixDysonTerm_aeCongruence36V4
    (B C : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hBC : B =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] C) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      genericRoughMatrixDysonTerm32 B n t = genericRoughMatrixDysonTerm32 C n t := by
  have hae : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) 1 → B s = C s :=
    (ae_restrict_iff' measurableSet_Ioc).mp hBC
  intro n
  induction n with
  | zero => intro t ht; rfl
  | succ n ih =>
    intro t ht
    ext i j
    change (∫ s in (0 : ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B n s) i j) =
      ∫ s in (0 : ℝ)..t, (C s * genericRoughMatrixDysonTerm32 C n s) i j
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with s hs
    intro hst
    rw [Set.uIoc_of_le ht.1] at hst
    have hs1 : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hst.1, hst.2.trans ht.2⟩
    rw [hs hs1, ih s ⟨hst.1.le, hs1.2⟩]

/-- Finite Dyson integrals for the actual raw representative of τ•u, for
REAL τ, agree with τ^n times the finite integral for u. This realizes the
representative transfer, rather than postulating scalar homogeneity. -/
theorem actualPhysicalInteractionDysonTerm_realCoupling36V4
    (u : PhysicalL2) (τ : ℝ) (z : ℂ) (n : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z) n t =
    (τ : ℂ)^n • genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z) n t := by
  have hae := actualPhysicalRawCover_scalarCoupling_ae36V2 u (τ : ℂ)
  have hcoeff :
      actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 ((τ : ℂ) • u) (s : SpectralCircle)) z
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      actualZsInteractionCoefficient32
        (fun s => (τ : ℂ) * naturalPhysicalCoverL2 u (s : SpectralCircle)) z := by
    filter_upwards [hae] with s hs
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [actualZsInteractionCoefficient32, zsCoefficientComplex, hs]
  rw [genericRoughMatrixDysonTerm_aeCongruence36V4 _ _ hcoeff n t ht]
  exact actualInteractionDysonTerm_realCoupling36V2 _ τ z n t
end NlsGge.SpectralFoundations
end
