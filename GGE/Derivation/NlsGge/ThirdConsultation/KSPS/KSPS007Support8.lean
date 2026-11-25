import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5

/- KSPS-007 SUPPORT08 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support8.lean.
   Pure 2x2 matrix algebra. `theta_alg`: the first-order terms of M(x) M(t)^{-1} R cancel exactly; what is left is
   -E(x) r'(t) R - r(x) E(-t) R - (M(x)-E(x)) (N(t)-E(-t)) R, the (M N) second-order remainder.
   (Verified entrywise with J*J = -1 and c*(2l) = 1; the two linear_combination coefficients per entry were
   obtained by polynomial reduction.)  `theta_EB` bounds it entrywise. -/
set_option autoImplicit false
noncomputable section
open NlsGge.ThirdConsultation.KSPS007Support5
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support8

theorem theta_alg (a0 a1 b0 b1 q1 q2 c l J : ℂ) (hJ : J * J = -1) (hc : c * (2 * l) = 1)
    (R Ex Et Q1 Q2 M1x M1t rx rp Mx Nt : Mt)
    (hR00 : R 0 0 = J) (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hR11 : R 1 1 = -J)
    (hE00 : Ex 0 0 = a0) (hE01 : Ex 0 1 = 0) (hE10 : Ex 1 0 = 0) (hE11 : Ex 1 1 = a1)
    (hT00 : Et 0 0 = b0) (hT01 : Et 0 1 = 0) (hT10 : Et 1 0 = 0) (hT11 : Et 1 1 = b1)
    (hQ100 : Q1 0 0 = q1) (hQ101 : Q1 0 1 = 0) (hQ110 : Q1 1 0 = 0) (hQ111 : Q1 1 1 = q1)
    (hQ200 : Q2 0 0 = q2) (hQ201 : Q2 0 1 = 0) (hQ210 : Q2 1 0 = 0) (hQ211 : Q2 1 1 = q2)
    (hMx : Mx = Ex + M1x + c • (Ex * R * Q1) + rx)
    (hNt : Nt = Et - M1t - c • (Et * R * Q2) + rp) :
    -(Mx * (Nt * R)) + R * (Ex * Et) -
        c • (-(2 * l) • (M1x * (R * Et)) + Q1 * (Ex * Et) + Ex * ((2 * l) • (M1t * R)) -
          (Ex * Et) * Q2) =
      -(Ex * (rp * R)) - rx * (Et * R) - (Mx - Ex) * ((Nt - Et) * R) := by
  subst hMx hNt
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, hR00, hR01, hR10, hR11, hE00, hE01,
      hE10, hE11, hT00, hT01, hT10, hT11, hQ100, hQ101, hQ110, hQ111, hQ200, hQ201, hQ210, hQ211]
    linear_combination (-a0 * b0 * c * q1 + a0 * b0 * c * q2) * hJ +
      (-J * M1t 0 0 * a0 + J * M1x 0 0 * b0) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, hR00, hR01, hR10, hR11, hE00, hE01,
      hE10, hE11, hT00, hT01, hT10, hT11, hQ100, hQ101, hQ110, hQ111, hQ200, hQ201, hQ210, hQ211]
    linear_combination (J * M1t 0 1 * a0 - J * M1x 0 1 * b1) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, hR00, hR01, hR10, hR11, hE00, hE01,
      hE10, hE11, hT00, hT01, hT10, hT11, hQ100, hQ101, hQ110, hQ111, hQ200, hQ201, hQ210, hQ211]
    linear_combination (-J * M1t 1 0 * a1 + J * M1x 1 0 * b0) * hc
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, hR00, hR01, hR10, hR11, hE00, hE01,
      hE10, hE11, hT00, hT01, hT10, hT11, hQ100, hQ101, hQ110, hQ111, hQ200, hQ201, hQ210, hQ211]
    linear_combination (-a1 * b1 * c * q1 + a1 * b1 * c * q2) * hJ +
      (J * M1t 1 1 * a1 - J * M1x 1 1 * b1) * hc

theorem theta_EB {Ex Et R rx rp M N : Mt} {ε br bp bm bn : ℝ}
    (hEx : EB Ex ε) (hEt : EB Et ε) (hR : EB R 1) (hrx : EB rx br) (hrp : EB rp bp)
    (hM : EB M bm) (hN : EB N bn) :
    EB (-(Ex * (rp * R)) - rx * (Et * R) - M * (N * R))
      (2 * (ε * (2 * (bp * 1))) + 2 * (br * (2 * (ε * 1))) + 2 * (bm * (2 * (bn * 1)))) :=
  ((hEx.mul (hrp.mul hR)).neg.sub (hrx.mul (hEt.mul hR))).sub (hM.mul (hN.mul hR))

end NlsGge.ThirdConsultation.KSPS007Support8
