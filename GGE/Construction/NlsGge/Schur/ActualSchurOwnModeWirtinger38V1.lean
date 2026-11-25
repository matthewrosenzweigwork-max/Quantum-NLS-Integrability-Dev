import NlsGge.Schur.ActualSchurOwnModeDerivative38V1
import NlsGge.Schur.ActualSchurWirtinger38V1

/-!
# NEW-F04 on the real-type subspace: the Wirtinger form of F:eq:diagonal

For `‖u‖_{H¹} ≤ R` and `|n| ≥ C (2R)^3`, with `Rem(v) = q_n(v, v̄) - v_n`
(holomorphy radius `2R`), the Wirtinger derivative
`∂Rem/∂u_n = ½(dRem[δ_n] - i·dRem[iδ_n]) = ∂q_n/∂u_n - 1` has size at most
`2 C_I^2 C_S^2 (2R)^4/n^2`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

theorem actualSchurQnRealType_ownMode_wirtinger38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (2 * R) ^ 3 ≤ |(n : ℝ)|)
    (u : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hu : ‖u‖ ≤ R) :
    ‖(1 / 2 : ℂ) *
        (fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) u (actualH1ModeVector38 n) -
          Complex.I * fderiv ℝ (actualSchurQnRealRemainder38 (2 * R) n) u
            (Complex.I • actualH1ModeVector38 n))‖ ≤
      2 * actualSchurOwnModeScale38 (2 * R) n := by
  have h2R : 1 ≤ 2 * R := by linarith
  rw [actualSchurQnRealRemainder38_wirtinger (2 * R) h2R n hthr u (by linarith)]
  have h1 : (actualH1ModeVector38 n : ℤ → ℂ) n = 1 := by
    rw [actualH1ModeVector38_apply]; simp
  rw [h1]
  exact actualSchurQn38_ownMode_derivative R hR n hthr (u, actualH1Conj38 u) hu
    (by rw [actualH1Conj38_norm]; exact hu)

end NlsGge.Schur
