import NlsGge.GK38.TauGammaOmittedCauchy
import NlsGge.GK38.TauGammaDeviationBounds

/-! The actual exterior value and derivative errors combine paired Cauchy and translated sinc bounds. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exterior_inner_error_bounds38 (φ : PotPair) (n : ℤ) (z : ℂ)
    (hz : z ∈ ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 8)) (b K : ℝ)
    (hb : ‖Lib.omitProd n (periodicPlusDeviation38 φ) z * Lib.omitProd n (periodicMinusDeviation38 φ) z -
      (Lib.sincAt n z) ^ 2‖ ≤ b ∧
      ‖deriv (fun w => Lib.omitProd n (periodicPlusDeviation38 φ) w *
          Lib.omitProd n (periodicMinusDeviation38 φ) w) z -
        deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ b)
    (hK : ‖(Lib.sincAt n z) ^ 2 - 1‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (fun w => (Lib.sincAt n w) ^ 2) z‖ ≤ K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖) :
    ‖exteriorFactor38 φ n z - 1‖ ≤ b + K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ∧
      ‖deriv (exteriorFactor38 φ n) z‖ ≤ b + K * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
  have hval : ‖exteriorFactor38 φ n z - (Lib.sincAt n z) ^ 2‖ ≤ b := by
    rw [exterior_eq_omitProducts38]
    exact hb.1
  have heD : deriv (exteriorFactor38 φ n) z = deriv (fun w =>
      Lib.omitProd n (periodicPlusDeviation38 φ) w * Lib.omitProd n (periodicMinusDeviation38 φ) w) z :=
    congrArg (fun f : ℂ → ℂ => deriv f z) (funext (exterior_eq_omitProducts38 φ n))
  have hder := hb.2
  rw [← heD] at hder
  constructor
  · have he : exteriorFactor38 φ n z - 1 =
        (exteriorFactor38 φ n z - (Lib.sincAt n z) ^ 2) + ((Lib.sincAt n z) ^ 2 - 1) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hval hK.1)
  · exact (norm_le_norm_sub_add (deriv (exteriorFactor38 φ n) z)
      (deriv (fun w => (Lib.sincAt n w) ^ 2) z)).trans (add_le_add hder hK.2)

end
end NlsGge.GK38
