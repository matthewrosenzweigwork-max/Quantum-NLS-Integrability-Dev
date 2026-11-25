import NlsGge.GK38.PoissonSpectralMatrix

/-! Actual rough-potential cyclic matrices: AC, ODE and endpoint identity. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.PoissonSpectral38
noncomputable section

theorem ac_cyclicMatrix38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => cyclicMatrix38 φ z s i j) 0 1 :=
  ac_cyclicEntry38 (monodromyPair φ z) (ac_fundContP_entry38 φ z) i j

theorem ae_hasDerivAt_cyclicMatrix38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => cyclicMatrix38 φ z r i j)
        ((zsCoeffPot38 φ z s * cyclicMatrix38 φ z s -
          cyclicMatrix38 φ z s * zsCoeffPot38 φ z s) i j) s := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z 0 0,
    ae_hasDerivAt_fundContP_entry38 φ z 0 1,
    ae_hasDerivAt_fundContP_entry38 φ z 1 0,
    ae_hasDerivAt_fundContP_entry38 φ z 1 1] with s h00 h01 h10 h11 hs
  have hM (a b : Fin 2) : HasDerivAt (fun r => ext38 (fundContP φ z) r a b)
      ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) a b) s := by
    fin_cases a <;> fin_cases b
    · exact h00 hs
    · exact h01 hs
    · exact h10 hs
    · exact h11 hs
  exact hasDerivAt_cyclicEntry38 φ z (monodromyPair φ z) hM i j

theorem cyclicMatrix38_zero (φ : PotPair) (z : ℂ) :
    cyclicMatrix38 φ z 0 = monodromyPair φ z := by
  have h0 : ext38 (fundContP φ z) 0 = (1 : PairMat38) := by
    simpa only [fundPair_zero] using
      k1FundContEndpoint38 φ z ⟨0, le_rfl, zero_le_one⟩
  simp only [cyclicMatrix38, h0, Matrix.adjugate_one, one_mul, mul_one]

theorem cyclicMatrix38_one (φ : PotPair) (z : ℂ) :
    cyclicMatrix38 φ z 1 = monodromyPair φ z := by
  have h1 : ext38 (fundContP φ z) 1 = monodromyPair φ z :=
    (k1FundContEndpoint38 φ z ⟨1, zero_le_one, le_rfl⟩).trans
      (monodromyPair_eq_fundPair φ z).symm
  have hdet : (monodromyPair φ z).det = 1 := by
    rw [monodromyPair_eq_fundPair]
    exact det_fundPair38 φ z ⟨1, zero_le_one, le_rfl⟩
  simp only [cyclicMatrix38, h1, mul_assoc, Matrix.mul_adjugate, hdet, one_smul, mul_one]

theorem spectralGradientWedge38_cyclic (φ : PotPair) (z w : ℂ) (s : ℝ) :
    spectralGradientWedge38 φ z w s =
      cyclicMatrix38 φ z s 1 0 * cyclicMatrix38 φ w s 0 1 -
        cyclicMatrix38 φ z s 0 1 * cyclicMatrix38 φ w s 1 0 := by
  unfold spectralGradientWedge38
  rw [gradDiscrim38_cyclic φ z s, gradDiscrim38_cyclic φ w s]
  change (Complex.I * cyclicMatrix38 φ z s 1 0) *
      (-Complex.I * cyclicMatrix38 φ w s 0 1) -
    (-Complex.I * cyclicMatrix38 φ z s 0 1) *
      (Complex.I * cyclicMatrix38 φ w s 1 0) = _
  calc
    _ = -(Complex.I * Complex.I) *
        (cyclicMatrix38 φ z s 1 0 * cyclicMatrix38 φ w s 0 1 -
          cyclicMatrix38 φ z s 0 1 * cyclicMatrix38 φ w s 1 0) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem ac_cyclicTraceProduct38 (φ : PotPair) (z w : ℂ) :
    AbsolutelyContinuousOnInterval (cyclicTraceProduct38 φ z w) 0 1 := by
  have h0 := ac_mulEntry38 (ac_cyclicMatrix38 φ z) (ac_cyclicMatrix38 φ w) 0 0
  have h1 := ac_mulEntry38 (ac_cyclicMatrix38 φ z) (ac_cyclicMatrix38 φ w) 1 1
  convert! h0.add h1 using 1 <;> rfl

theorem ae_hasDerivAt_cyclicTraceProduct38 (φ : PotPair) (z w : ℂ) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (cyclicTraceProduct38 φ z w)
        (2 * Complex.I * (z - w) * spectralGradientWedge38 φ z w s) s := by
  filter_upwards [ae_hasDerivAt_cyclicMatrix38 φ z 0 0,
    ae_hasDerivAt_cyclicMatrix38 φ z 0 1,
    ae_hasDerivAt_cyclicMatrix38 φ z 1 0,
    ae_hasDerivAt_cyclicMatrix38 φ z 1 1,
    ae_hasDerivAt_cyclicMatrix38 φ w 0 0,
    ae_hasDerivAt_cyclicMatrix38 φ w 0 1,
    ae_hasDerivAt_cyclicMatrix38 φ w 1 0,
    ae_hasDerivAt_cyclicMatrix38 φ w 1 1]
    with s hz00 hz01 hz10 hz11 hw00 hw01 hw10 hw11 hs
  have hA (a b : Fin 2) : HasDerivAt (fun r => cyclicMatrix38 φ z r a b)
      ((zsCoeffPot38 φ z s * cyclicMatrix38 φ z s -
        cyclicMatrix38 φ z s * zsCoeffPot38 φ z s) a b) s := by
    fin_cases a <;> fin_cases b
    · exact hz00 hs
    · exact hz01 hs
    · exact hz10 hs
    · exact hz11 hs
  have hB (a b : Fin 2) : HasDerivAt (fun r => cyclicMatrix38 φ w r a b)
      ((zsCoeffPot38 φ w s * cyclicMatrix38 φ w s -
        cyclicMatrix38 φ w s * zsCoeffPot38 φ w s) a b) s := by
    fin_cases a <;> fin_cases b
    · exact hw00 hs
    · exact hw01 hs
    · exact hw10 hs
    · exact hw11 hs
  have hd := (hasDerivAt_mulEntry38 hA hB 0 0).fun_add
    (hasDerivAt_mulEntry38 hA hB 1 1)
  apply hd.congr_deriv
  have halg := trace_commutator_spectral38 φ z w s
    (cyclicMatrix38 φ z s) (cyclicMatrix38 φ w s)
  rw [spectralGradientWedge38_cyclic]
  simp only [traceProduct38, Matrix.add_apply] at halg ⊢
  linear_combination halg

end
end NlsGge.GK38.PoissonSpectral38
