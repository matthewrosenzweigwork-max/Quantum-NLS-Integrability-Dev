import QuantumNLS.TerraMultiRound43REG005
/-! integrator-authored trusted spec for REG-005 CC:G04:parity (terra_review r204 PASS): headline statement(s) copied verbatim from TerraMultiRound43REG005 (QuantumNLS.TerraMultiRound43REG005). -/
set_option autoImplicit false
noncomputable section
open Complex Finset ComplexConjugate
namespace QuantumNLS.REG005Spec
open QuantumNLS.TerraMultiRound43REG005
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

set_option maxHeartbeats 8000000 in
theorem signed_small_solutions_and_parity_spec (L : ℝ) [hLf : Fact (0 < L)] (a : ℝ)
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
  exact QuantumNLS.TerraMultiRound43REG005.signed_small_solutions_and_parity L a ha κ hκ u hu

end QuantumNLS.REG005Spec
#print axioms QuantumNLS.REG005Spec.signed_small_solutions_and_parity_spec
