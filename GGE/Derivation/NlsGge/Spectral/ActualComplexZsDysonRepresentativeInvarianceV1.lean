import NlsGge.Spectral.ActualComplexZsDysonProductHasSumV2
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.SpectralFoundations

/-- The actual nested Dyson integrals are unchanged by replacing the
potential on a null subset of the doubled interval. No regularity or
summability of an arbitrary input is asserted here. -/
theorem actualComplexZsDysonTerm_eq_of_ae_eq
    (U V : ℝ → ℂ) (z : ℂ)
    (hUV : U =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)] V)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualComplexZsDysonTerm U z n t = actualComplexZsDysonTerm V z n t := by
  have hAE : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) 2 → U s = V s :=
    (ae_restrict_iff' measurableSet_Ioc).1 hUV
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    ext i j
    change (∫ s in (0 : ℝ)..t,
      (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j) =
      ∫ s in (0 : ℝ)..t,
        (zsCoefficientComplex V z s * actualComplexZsDysonTerm V z n s) i j
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hAE] with s hs
    intro hst
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) t := by
      simpa only [Set.uIoc_of_le ht.1] using hst
    have hs2 : s ∈ Set.Ioc (0 : ℝ) 2 := ⟨hsIoc.1, hsIoc.2.trans ht.2⟩
    have hcoeff : zsCoefficientComplex U z s = zsCoefficientComplex V z s := by
      simp only [zsCoefficientComplex, hs hs2]
    rw [hcoeff, ih s ⟨hsIoc.1.le, hsIoc.2.trans ht.2⟩]

/-- Equality of the actual recursively defined entries transfers to the
entrywise totalized sum. For arbitrary inputs this is only invariance, not
an existence/summability assertion; the physical-L² construction supplies
summability and ODE regularity independently. -/
theorem actualComplexZsDysonTsum_eq_of_ae_eq
    (U V : ℝ → ℂ) (z : ℂ)
    (hUV : U =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)] V)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    actualComplexZsDysonTsum U z t = actualComplexZsDysonTsum V z t := by
  ext i j
  apply tsum_congr
  intro n
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
    (actualComplexZsDysonTerm_eq_of_ae_eq U V z hUV n t ht)

end NlsGge.SpectralFoundations
end
