import QuantumNLS.HaarSummableReconstruction
/-! integrator-authored trusted spec for R-9A71E77E QG:prop:haar-summable-reconstruction (Terra r143 ACCEPT):
headline copied verbatim from HS2 HaarSummableReconstruction 2fb65a43, with rfl defining equations of
the remainder r_N, the printed constants C0, C1 and the zero background G0. -/
set_option autoImplicit false
noncomputable section
open Complex Filter Topology Asymptotics Set
namespace R9A71Spec
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionAsymp
  QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction QuantumNLS.PeriodTwoTerm
  QuantumNLS.HaarSummableCore QuantumNLS.HaarSummableReconstruction QuantumNLS

set_option maxHeartbeats 8000000 in
theorem haar_summable_reconstruction_spec {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {E : ℝ} (hE : 0 < E) :
    ∃ (NE : ℕ) (RE CE : ℝ), 0 < NE ∧ 2 ≤ RE ∧ 0 ≤ CE ∧
      ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ), NE ≤ N →
        RootContraction.IsActualConfig L (κ / N) n q → (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
        (∀ m : ℤ, RE < |(m : ℝ)| → ∀ z ∈ HighContours.Γ L m,
          (∀ j, 2 * |κ / (N : ℝ)| < ‖z - q j‖) ∧
          aNf L κ (κ / N) G0 q z ^ 2 - sNf L (κ / N) q z * aNf L κ (κ / N) G0 q z + ef L z = 0 ∧
          ‖aNf L κ (κ / N) G0 q z - 1‖ ≤ 1 / 2 ∧
          DifferentiableAt ℂ (aNf L κ (κ / N) G0 q) z ∧
          log (aNf L κ (κ / N) G0 q z) =
            LabelExactPeriod.logT (aNf L κ (κ / N) G0 q z - 1) ∧
          ‖rN L κ q z‖ ≤ CE / ((N : ℝ) ^ 2 * (m : ℝ) ^ 2) ∧
          ‖corrf L κ (κ / N) G0 q z‖ ≤ CE / (m : ℝ) ^ 2) ∧
        (∀ m : ℤ, RE < |(m : ℝ)| →
          |((Finset.univ.filter fun j => n j = m).card : ℝ) - N * C0 L κ q m - C1 L κ q m| ≤
            CE / (N * (m : ℝ) ^ 2)) ∧
        (∀ R : ℝ, RE ≤ R → ∀ I : Finset ℤ, (∀ m ∈ I, R < |(m : ℝ)|) → ∀ t : ℤ → ℝ,
          (∀ m, |t m| ≤ 1) →
          |∑ m ∈ I, t m * (((Finset.univ.filter fun j => n j = m).card : ℝ) -
              N * C0 L κ q m - C1 L κ q m)| ≤ CE / (N * R)) ∧
        (∀ R : ℝ, RE ≤ R →
          Summable (fun m : ℤ => if R < |(m : ℝ)| then |C1 L κ q m| else 0) ∧
          ∑' m : ℤ, (if R < |(m : ℝ)| then |C1 L κ q m| else 0) ≤ CE / R) :=
  QuantumNLS.HaarSummableReconstruction.haar_summable_reconstruction hL hκ hE

theorem G0_def : G0 = fun _ => (0 : ℂ) := rfl
theorem rN_def (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : rN L κ q z =
  LabelExactPeriod.ellN κ q z - log (aNf L κ (κ / N) G0 q z) +
    I * κ / (N : ℂ) * corrf L κ (κ / N) G0 q z := rfl
theorem C0_def (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (m : ℤ) : C0 L κ q m =
  -(1 / (2 * Real.pi * κ)) *
    (HighContours.boundaryIntegral L m (fun z => log (aNf L κ (κ / N) G0 q z))).re := rfl
theorem C1_def (L κ : ℝ) {N : ℕ} (q : Fin N → ℝ) (m : ℤ) : C1 L κ q m =
  (I / (2 * Real.pi) * HighContours.boundaryIntegral L m (corrf L κ (κ / N) G0 q)).re := rfl
end R9A71Spec
#print axioms R9A71Spec.haar_summable_reconstruction_spec
