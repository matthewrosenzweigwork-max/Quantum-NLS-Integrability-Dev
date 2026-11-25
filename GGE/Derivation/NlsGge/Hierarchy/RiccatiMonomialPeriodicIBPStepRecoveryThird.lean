import NlsGge.Hierarchy.PeriodicIntegrationByParts
import NlsGge.Hierarchy.RiccatiDerivativeExcessAndPeriodicEvaluatorRecoverySecond
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory
open scoped ContDiff Interval

/-- Every smooth evaluation of an actual jet polynomial is continuous,
because its derivative is given by the checked formal spatial derivation. -/
theorem riccatiJetEvaluation_continuousNativeRecovery
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (P : Poly) :
    Continuous (fun x => riccatiJetEvaluation u x P) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (riccatiJetEvaluation_hasDerivAt u hu P x).continuousAt

/-- The concrete monomial integration-by-parts step for a selected high jet.
The selected jet is differentiated down one order, and differentiating the
residual polynomial is represented by the actual `spatialD` in the pinned
jet evaluator. -/
theorem riccatiJetMonomial_periodic_ibp_stepNativeRecovery
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (m : Jet →₀ ℕ) (c : ℤ) (v : Jet)
    (hv : v ∈ m.support) (horder : 0 < v.2) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial m c)) =
      -(∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (MvPolynomial.X (v.1, v.2 - 1)) *
          riccatiJetEvaluation u x
            (spatialD (MvPolynomial.monomial (m - Finsupp.single v 1) c))) := by
  let r : Jet →₀ ℕ := m - Finsupp.single v 1
  let f : ℝ → ℂ := fun x =>
    riccatiJetEvaluation u x (MvPolynomial.X (v.1, v.2 - 1))
  let g : ℝ → ℂ := fun x => riccatiJetEvaluation u x (MvPolynomial.monomial r c)
  let f' : ℝ → ℂ := fun x => riccatiJetEvaluation u x (MvPolynomial.X v)
  let g' : ℝ → ℂ := fun x =>
    riccatiJetEvaluation u x (spatialD (MvPolynomial.monomial r c))
  have hne : m v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hsplit : r + Finsupp.single v 1 = m :=
    Finsupp.sub_add_single_one_cancel hne
  have hX : MvPolynomial.X v =
      MvPolynomial.monomial (Finsupp.single v 1) (1 : ℤ) := by
    simpa using (MvPolynomial.X_pow_eq_monomial (n := v) (e := 1))
  have hmain :
      MvPolynomial.X v * MvPolynomial.monomial r c =
        MvPolynomial.monomial m c := by
    calc
      MvPolynomial.X v * MvPolynomial.monomial r c =
          MvPolynomial.monomial (Finsupp.single v 1) 1 *
            MvPolynomial.monomial r c := by rw [hX]
      _ = MvPolynomial.monomial (Finsupp.single v 1 + r) (1 * c) :=
        MvPolynomial.monomial_mul_monomial
      _ = MvPolynomial.monomial (r + Finsupp.single v 1) c := by
        congr 1 <;> simp [add_comm]
      _ = MvPolynomial.monomial m c := by rw [hsplit]
  have heval : ∀ x : ℝ,
      riccatiJetEvaluation u x (MvPolynomial.monomial m c) = f' x * g x := by
    intro x
    rw [← hmain]
    simp [f', g, riccatiJetEvaluation]
  have hshift : (v.1, v.2 - 1 + 1) = v := by
    have hpos : 1 ≤ v.2 := by omega
    rcases v with ⟨b, n⟩
    simp only [Prod.mk.injEq]
    constructor
    · trivial
    · exact Nat.sub_add_cancel hpos
  have hfper : Function.Periodic f 1 := by
    exact riccatiJetEvaluation_periodic_of_smooth_periodicNativeRecovery
      u hu hper (MvPolynomial.X (v.1, v.2 - 1))
  have hgper : Function.Periodic g 1 := by
    exact riccatiJetEvaluation_periodic_of_smooth_periodicNativeRecovery
      u hu hper (MvPolynomial.monomial r c)
  have hf : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (f' x) x := by
    intro x hx
    have h := riccatiJetEvaluation_hasDerivAt u hu
      (MvPolynomial.X (v.1, v.2 - 1)) x
    simpa [f, f', spatialD_jet, riccatiJetEvaluation, hshift] using h
  have hg : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' x) x := by
    intro x hx
    exact riccatiJetEvaluation_hasDerivAt u hu (MvPolynomial.monomial r c) x
  have hf'Cont : Continuous f' := by
    exact riccatiJetEvaluation_continuousNativeRecovery u hu (MvPolynomial.X v)
  have hg'Cont : Continuous g' := by
    exact riccatiJetEvaluation_continuousNativeRecovery u hu
      (spatialD (MvPolynomial.monomial r c))
  have hf'Int : IntervalIntegrable f' MeasureTheory.volume 0 1 :=
    hf'Cont.continuousOn.intervalIntegrable
  have hg'Int : IntervalIntegrable g' MeasureTheory.volume 0 1 :=
    hg'Cont.continuousOn.intervalIntegrable
  have hparts := NlsGge.HierarchyRiccati.unitPeriod_integral_mul_deriv_eq_neg_deriv_mul
    hfper hgper hf hg hf'Int hg'Int
  have hparts' :
      -(∫ x in (0 : ℝ)..1, f x * g' x) =
        ∫ x in (0 : ℝ)..1, f' x * g x := by
    simpa using congrArg (fun z : ℂ => -z) hparts
  calc
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (MvPolynomial.monomial m c)) =
        ∫ x in (0 : ℝ)..1, f' x * g x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact heval x
    _ = -(∫ x in (0 : ℝ)..1, f x * g' x) := hparts'.symm
    _ = -(∫ x in (0 : ℝ)..1,
        riccatiJetEvaluation u x (MvPolynomial.X (v.1, v.2 - 1)) *
          riccatiJetEvaluation u x
            (spatialD (MvPolynomial.monomial r c))) := by rfl

end NlsGge.HierarchyRiccati.Core

end
