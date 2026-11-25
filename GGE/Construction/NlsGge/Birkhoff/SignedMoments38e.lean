import NlsGge.Birkhoff.SignedMoments38d

/-! # SIGNED-MOMENTS.02/.03 on `H^{m-1}` (`B`-free)

Cauchy-Schwarz and the arithmetic-geometric mean bound for the continuous extensions: by density of the Fourier
truncations (smooth fields, where `C_{2j+1}`, `C_{2j}`, `C_{2j+2}` are the spectral moments of `v`) and continuity of
`oddChargeSobolev38`, `chargeSobolev38`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations MeasureTheory
  Filter Topology
open scoped ContDiff ENNReal

/-- Cauchy-Schwarz on smooth fields: `(Im ∫ (-1)^{j+1} u p_{2j+2})² ≤ Q_{2j} Q_{2j+2}`. -/
theorem oddLocal_cs_smooth38 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ) :
    oddLocalCharge38 U j ^ 2 ≤ localCharge38 U j * localCharge38 U (j + 1) ∧
    |oddLocalCharge38 U j| ≤ (localCharge38 U j + localCharge38 U (j + 1)) / 2 := by
  obtain ⟨hint, hodd⟩ := signedSpectral_moments38 U hU hper (j + 1)
  have hoddj := hodd j le_rfl
  have e0 := signedSpectral_even_eq_localCharge38 U hU hper j
  have e2 := signedSpectral_even_eq_localCharge38 U hU hper (j + 1)
  rw [← hoddj, ← e0, ← e2]
  have i0 := hint (2 * j) (by omega)
  have i1 := hint (2 * j + 1) (by omega)
  have i2 := hint (2 * j + 2) (by omega)
  exact ⟨signedSpectral_cs38 _ j i0 i1 i2, signedSpectral_amgm38 _ j i0 i1 i2⟩

/-- **SIGNED-MOMENTS.02 on `H^{m-1}`.** -/
theorem oddChargeSobolev_cs38 (m j : ℕ) (hmj : j + 2 ≤ m) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    oddChargeSobolev38 m j x ^ 2 ≤ chargeSobolev38 m j x * chargeSobolev38 m (j + 1) x := by
  have hm : 2 ≤ m := by omega
  have hc1 := (continuous_oddChargeSobolev38 m j hmj).pow 2
  have hc2 := (continuous_chargeSobolev38 m j (by omega)).mul
    (continuous_chargeSobolev38 m (j + 1) (by omega))
  refine le_of_tendsto_of_tendsto' (hc1.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x))
    (hc2.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x)) (fun N => ?_)
  simp only [Function.comp, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  rw [oddChargeSobolev38_smooth m j hmj _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _
      (truncSobolev38_link _ N x),
    chargeSobolev38_smooth m j hm (by omega) _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _
      (truncSobolev38_link _ N x),
    chargeSobolev38_smooth m (j + 1) hm (by omega) _ (contDiff_truncField38 _ N x)
      (periodic_truncField38 _ N x) _ (truncSobolev38_link _ N x)]
  exact (oddLocal_cs_smooth38 _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) j).1

/-- **SIGNED-MOMENTS.03 on `H^{m-1}`.** -/
theorem oddChargeSobolev_amgm38 (m j : ℕ) (hmj : j + 2 ≤ m) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    |oddChargeSobolev38 m j x| ≤ (chargeSobolev38 m j x + chargeSobolev38 m (j + 1) x) / 2 := by
  have hm : 2 ≤ m := by omega
  have hc1 := (continuous_oddChargeSobolev38 m j hmj).abs
  have hc2 := ((continuous_chargeSobolev38 m j (by omega)).add
    (continuous_chargeSobolev38 m (j + 1) (by omega))).div_const 2
  refine le_of_tendsto_of_tendsto' (hc1.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x))
    (hc2.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ x)) (fun N => ?_)
  simp only [Function.comp, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  rw [oddChargeSobolev38_smooth m j hmj _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _
      (truncSobolev38_link _ N x),
    chargeSobolev38_smooth m j hm (by omega) _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) _
      (truncSobolev38_link _ N x),
    chargeSobolev38_smooth m (j + 1) hm (by omega) _ (contDiff_truncField38 _ N x)
      (periodic_truncField38 _ N x) _ (truncSobolev38_link _ N x)]
  exact (oddLocal_cs_smooth38 _ (contDiff_truncField38 _ N x) (periodic_truncField38 _ N x) j).2

end NlsGge.Birkhoff
end
