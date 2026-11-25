import QuantumNLS.TerraMultiRound40PhysicalParity
import QuantumNLS.TerraMultiRound41CoefficientParity
import QuantumNLS.TerraMultiRound43TwoSidedExpansion
import QuantumNLS.TerraMultiRound43AllAgreement

/-! REG-005: signed small solutions, identification, scalar parity, and the
smooth two-sided expansion with its literal recursive coefficients. -/
set_option autoImplicit false
noncomputable section
open Complex Finset ComplexConjugate
namespace QuantumNLS.TerraMultiRound43REG005
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiODEConverse
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound39AlgebraBall
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound40PhysicalParity
open QuantumNLS.TerraMultiRound40SignedODE
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound41CoefficientParity
open QuantumNLS.TerraMultiRound43TwoSidedExpansion QuantumNLS.TerraMultiRound43AllAgreement
open QuantumNLS.RootH1RatioBounds

/-- Signed small solutions and parity on the physical Sobolev field. The
weighted Fourier norm is equivalent to the usual H^k norm, and its rescaling
`algebraNorm` is an algebra norm. The conclusion includes the selected ratio,
the signed scalar identity, regularity gain, all smooth expansions and
coefficient parity. -/
theorem signed_small_solutions_and_parity (L : ℝ) [hLf : Fact (0 < L)] (a : ℝ)
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L a (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ a), fieldMap L a ha0 x = u ∧
      (∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
        ∃ (hY : 0 < |Y|) (r s : Ell2),
          algebraNorm L a r ≤ 2 * algebraNorm L a x / |Y| ∧
          algebraNorm L a s ≤ 2 * algebraNorm L a x / |Y| ∧
          physicalT hLf.out ha hY κ x r = r ∧
          physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ x s = s ∧
          (∀ t : ℝ, HasDerivAt (physRep L a r)
            (-(Y : ℂ) * physRep L a r t + physRep L a x t -
              (κ : ℂ) * conj (physRep L a x t) * physRep L a r t ^ 2) t) ∧
          physRep L a r L = physRep L a r 0 ∧
          (∀ t : ℝ, HasDerivAt (physRep L a s)
            (-((-Y : ℝ) : ℂ) * physRep L a s t + physRep L a x t -
              (κ : ℂ) * conj (physRep L a x t) * physRep L a s t ^ 2) t) ∧
          physRep L a s L = physRep L a s 0 ∧
          hsq L (a + 1) (toField L a r) ≠ ⊤ ∧
          hsq L (a + 1) (toField L a s) ≠ ⊤ ∧
          (∀ t : Ell2, algebraNorm L a t ≤ 2 * algebraNorm L a x / |Y| →
            physicalT hLf.out ha hY κ x t = t → t = r) ∧
          (∀ t : Ell2, algebraNorm L a t ≤ 2 * algebraNorm L a x / |Y| →
            physicalT hLf.out ha (by simpa using hY : 0 < |-Y|) κ x t = t → t = s) ∧
          scalar L a x r = -conj (scalar L a x s)) ∧
      (∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y → ∀ r : Ell2,
        algebraNorm L a r ≤ 2 * algebraNorm L a x / Y →
        ∀ (hY : 0 < Y), physicalT hLf.out ha (abs_pos.mpr hY.ne') κ x r = r →
        ∃ (hlog : Real.log 3 ≤ Y * L) (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
          fieldMap L a ha0 r = ratioL2 hY hlog hκ.le u hsmall) ∧
      (∀ f : ℝ → ℂ, physRep L a x = f → SmoothPeriodic L f →
        aseq κ f 1 = f ∧
        (∀ n : ℕ, aseq κ f (n + 2) = fun t =>
          -deriv (aseq κ f (n + 1)) t - (κ : ℂ) * conj (f t) *
            ∑ j ∈ Finset.Icc 1 n, aseq κ f j t * aseq κ f (n + 1 - j) t) ∧
        (∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
          ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
            physicalT hLf.out ha (abs_pos.mpr hY.ne') κ x r = r ∧
            (∀ t : ℝ, physRep L a p t =
              ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * ((Y : ℂ)⁻¹) ^ n) ∧
            ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹) ∧
        (∀ M : ℕ, 1 ≤ M → ∃ B C : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y →
          ∃ (hY : 0 < Y) (r p : Ell2), ‖r‖ ≤ 2 * ‖x‖ / Y ∧
            physicalT hLf.out ha (by simpa using (abs_pos.mpr hY.ne') : 0 < |-Y|) κ x r = r ∧
            (∀ t : ℝ, physRep L a p t =
              ∑ n ∈ Finset.Icc 1 M, aseq κ f n t * (((-Y : ℝ) : ℂ)⁻¹) ^ n) ∧
            ‖r - p‖ ≤ C * (Y ^ (M + 1))⁻¹) ∧
        (∀ m : ℕ, (coefficient L κ f (2 * m + 1)).im = 0) ∧
        (∀ m : ℕ, (coefficient L κ f (2 * m + 2)).re = 0)) := by
  obtain ⟨x, ha0, hx, hpar⟩ := physical_field_scalar_parity L a ha κ hκ.ne' u hu
  obtain ⟨B, hB, hagree⟩ := positive_solution_agreement_all L ha κ hκ x
  refine ⟨x, ha0, hx, ?_, ⟨B, hB, ?_⟩, ?_⟩
  · obtain ⟨B₀, hB₀, hb⟩ := hpar
    refine ⟨B₀, hB₀, ?_⟩
    intro Y hYB
    obtain ⟨hY, r, s, hrn, hsn, hr, hs, hrg, hsg, hru, hsu, hparity⟩ := hb Y hYB
    have hrODE := physical_signed_ode L ha hY κ x r hr
    have hsODE := physical_signed_ode L ha (by simpa using hY : 0 < |-Y|) κ x s hs
    exact ⟨hY, r, s, hrn, hsn, hr, hs, hrODE.1, hrODE.2, hsODE.1, hsODE.2,
      hrg, hsg, hru, hsu, hparity⟩
  · intro Y hY r hrn hYpos hr
    have hnorm : ‖r‖ ≤ 2 * ‖x‖ / Y := by
      have hs : 0 < algebraScale L a := algebraScale_pos L a
      have hh : algebraScale L a * ‖r‖ ≤ algebraScale L a * (2 * ‖x‖ / Y) := by
        dsimp [algebraNorm] at hrn
        convert hrn using 1
        ring
      nlinarith
    obtain ⟨hlog, hsmall, he⟩ := hagree Y hY r hnorm hYpos hr
    have hsmallU : 16 * κ * ‖u‖ ^ 2 ≤ Y := by simpa only [hx] using hsmall
    refine ⟨hlog, hsmallU, ?_⟩
    simpa only [hx] using he
  · intro f hrep hf
    obtain ⟨y, hy, _, hp, hn⟩ := smooth_two_sided_expansion L ha κ f hf
    have he : y = x := physRep_injective hLf.out ha (hy.trans hrep.symm)
    subst y
    exact ⟨aseq_one κ f, aseq_succ κ hf, hp, hn,
      (coefficient_parity hκ hf).1, (coefficient_parity hκ hf).2⟩

#print axioms signed_small_solutions_and_parity
end QuantumNLS.TerraMultiRound43REG005
