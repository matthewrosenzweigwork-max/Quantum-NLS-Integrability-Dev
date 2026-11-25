import NlsGge.Schur.ActualSchurBallIntegral38V1
import NlsGge.Hierarchy.FullEnergySpectralIdentification38

/-!
# NEW-F05 (F:prop:ball): unconditional form for the full source energy

The domination hypothesis of `actualSchurBallIntegral_conditional38` is discharged for
`E = fullEnergy38 c N` by the hierarchy trace bound `fullEnergy38_ge_gapSum_window_uniform`
(gaps labelled at `+m`; the Schur side uses the reflected label `-n`, so `S ↦ -S`).
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Measure
  NlsGge.HierarchyRiccati.Core

namespace NlsGge.Schur

/-- **NEW-F05, F:prop:ball (unconditional).**  There is `C > 0`, depending only on the
coefficient bounds `lo, up`, such that for every admitted coefficient sequence `c`, every
`R ≥ 1` and every Fourier cutoff `N`, the Lebesgue integral over the open plane H¹ ball of
radius `R` of `exp(-E_c)` (`E_c = fullEnergy38 c N`, the full source charge series) is at most
`∏_{|n| ≤ N} (π / a_n) · exp(C (1+R)^9)`, with `a_n = weight c (2π n)`. -/
theorem actualSchurBallIntegral_fullEnergy38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ C : ℝ, 0 < C ∧
    ∀ c : BoundedCoefficients lo up, ∀ R : ℝ, 1 ≤ R → ∀ N : ℕ,
    ∫⁻ z in {z | planeH1Norm38 N z < R},
        ENNReal.ofReal (Real.exp (-fullEnergy38 c N z)) ∂planeVolume N ≤
      (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi / fullWeightRate c.val (modeIndex N i))) *
        ENNReal.ofReal (Real.exp (C * (1 + R) ^ 9)) := by
  obtain ⟨K2, hK2, hW2⟩ := fullEnergy38_ge_gapSum_window_uniform
  obtain ⟨C, K, hC, hK, hKK2, hmain⟩ := actualSchurBallIntegral_conditional38 lo up hl hlu K2
  refine ⟨C, hC, fun c R hR N => ?_⟩
  obtain ⟨-, -, hb, hu⟩ := boundedCoefficients_bounds38 c
  refine hmain c.val hb hu R hR N (fullEnergy38 c N) (continuous_fullEnergy38 c N).measurable
    (fullEnergy38_nonneg c N) ?_
  intro z hz S hS
  have hsum : SobolevSquareSummable 1 (physicalFourier (planeL2 N z)) := by
    rw [← planeField38_eq_planeL2]
    exact physicalH1ComplexCarrierToL2Actual22_sobolevSquareSummable _
  have hnorm : ‖physicalSobolevL2 1 (planeL2 N z) hsum‖ ≤ R := by
    rw [← planeH1Norm38_eq_physicalSobolev N z hsum]; exact hz.le
  have hR2 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR (by norm_num)
  have hS' : ∀ m ∈ S.image (fun n => -n), K2 * R ^ 2 ≤ |(m : ℝ)| := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have h1 := (hS n hn).1
    rw [Int.cast_neg, abs_neg]
    have : K2 * R ^ 2 ≤ K * R ^ 3 := by
      apply mul_le_mul hKK2 hR2 (by positivity) hK.le
    linarith
  have hW := hW2 c N z R hR hsum hnorm (S.image (fun n => -n)) hS'
  rw [Finset.sum_image (fun a _ b _ h => neg_injective h)] at hW
  refine le_trans (le_of_eq ?_) hW
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [planeGapAction38, planeField38_eq_planeL2]

end NlsGge.Schur
