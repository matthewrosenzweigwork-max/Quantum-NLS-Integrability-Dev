import NlsGge.GK38.GradFundamentalSpectralODE

/-! # K1: actual spectral adjugate variation-of-constants identity.
GK Chapter I, Proposition3.1. AC/ODE and integrability precede FTC and det-one recovery.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

def spectralVariationPrimitive38 (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  (ext38 (fundContP φ z) s).adjugate * ext38 (fundSpectralResolvent38 φ z) s

theorem ac_spectralVariationPrimitive38 (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => spectralVariationPrimitive38 φ z s i j) 0 1 :=
  ac_adjugate_mulEntry38 (ac_fundContP_entry38 φ z) (ac_fundSpectral_entry38 φ z) i j

theorem ae_hasDerivAt_spectralVariationPrimitive38 (φ : PotPair) (z : ℂ) 
    (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => spectralVariationPrimitive38 φ z r i j)
        (((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 * ext38 (fundContP φ z) s) i j) s := by
  filter_upwards [ae_hasDerivAt_fundContP_entry38 φ z 0 0,
    ae_hasDerivAt_fundContP_entry38 φ z 0 1, ae_hasDerivAt_fundContP_entry38 φ z 1 0,
    ae_hasDerivAt_fundContP_entry38 φ z 1 1,
    ae_hasDerivAt_fundSpectral_entry38 φ z 0 0, ae_hasDerivAt_fundSpectral_entry38 φ z 0 1,
    ae_hasDerivAt_fundSpectral_entry38 φ z 1 0, ae_hasDerivAt_fundSpectral_entry38 φ z 1 1]
      with s hm00 hm01 hm10 hm11 hw00 hw01 hw10 hw11 hs
  have hM (a b : Fin 2) : HasDerivAt (fun r => ext38 (fundContP φ z) r a b)
      ((zsCoeffPot38 φ z s * ext38 (fundContP φ z) s) a b) s := by
    fin_cases a <;> fin_cases b
    · exact hm00 hs
    · exact hm01 hs
    · exact hm10 hs
    · exact hm11 hs
  have hW (a b : Fin 2) : HasDerivAt (fun r => ext38 (fundSpectralResolvent38 φ z) r a b)
      ((zsCoeffPot38 φ z s * ext38 (fundSpectralResolvent38 φ z) s +
        spectralCoeff38 * ext38 (fundContP φ z) s) a b) s := by
    fin_cases a <;> fin_cases b
    · exact hw00 hs
    · exact hw01 hs
    · exact hw10 hs
    · exact hw11 hs
  have hD := hasDerivAt_adjugate_mulEntry38 hM hW i j
  have hc := adjugate_variation_cancel38 φ z s (ext38 (fundContP φ z) s)
    (ext38 (fundSpectralResolvent38 φ z) s) (spectralCoeff38 * ext38 (fundContP φ z) s)
  rw [← mul_assoc] at hc
  exact hD.congr_deriv (congrArg (fun A : PairMat38 => A i j) hc)

theorem spectralVariationPrimitive38_zero (φ : PotPair) (z : ℂ) :
    spectralVariationPrimitive38 φ z 0 = 0 := by
  unfold spectralVariationPrimitive38
  have he : ext38 (fundSpectralResolvent38 φ z) (0 : ℝ) =
      fundSpectralResolvent38 φ z ⟨0, le_rfl, zero_le_one⟩ :=
    ext38_of_mem _ (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  apply k1MatrixZeroTransport38
  intro i j
  have hz := congrArg (fun A : Fin 2 → Fin 2 → ℂ => A i j)
    (fundSpectral_zero_time38 φ z)
  simpa only [he, Pi.zero_apply] using hz


/-- Each adjugate primitive equals its independently specified integral. -/
theorem spectralVariationPrimitive38_integral (φ : PotPair) (z : ℂ) 
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    spectralVariationPrimitive38 φ z t i j = ∫ s in (0 : ℝ)..(t : ℝ),
      ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 * ext38 (fundContP φ z) s) i j := by
  have hint := intervalIntegrable_fundSpectralKer38 φ z ⟨1, zero_le_one, le_rfl⟩ i j
  have hftc := ac_integral_eq_sub38 (ac_spectralVariationPrimitive38 φ z i j) hint
    (ae_hasDerivAt_spectralVariationPrimitive38 φ z i j) t
  rw [spectralVariationPrimitive38_zero, Matrix.zero_apply, sub_zero] at hftc
  exact hftc.symm

/-- The actual spectral derivative has the approved adjugate VOC expression. -/
theorem fundSpectralResolvent38_voc (φ : PotPair) (z : ℂ) 
    (t : Icc (0 : ℝ) 1) :
    fundSpectralResolvent38 φ z t = fundSpectralIntegral38 φ z t := by
  let Wt : PairMat38 := fundSpectralResolvent38 φ z t
  change Wt = fundSpectralIntegral38 φ z t
  have hJ : (fundPair φ z t).adjugate * Wt =
      Matrix.of (fun i j => ∫ s in (0 : ℝ)..(t : ℝ),
        ((ext38 (fundContP φ z) s).adjugate * spectralCoeff38 * ext38 (fundContP φ z) s) i j) := by
    ext i j
    have hj := spectralVariationPrimitive38_integral φ z t i j
    change ((ext38 (fundContP φ z) t).adjugate *
      ext38 (fundSpectralResolvent38 φ z) t) i j = _ at hj
    rw [k1FundContEndpoint38, ext38_of_mem _ t.2] at hj
    exact hj
  have hInv : fundPair φ z t * (fundPair φ z t).adjugate = 1 := by
    rw [Matrix.mul_adjugate, det_fundPair38, one_smul]
  calc
    Wt = 1 * Wt := (one_mul _).symm
    _ = (fundPair φ z t * (fundPair φ z t).adjugate) *
        Wt := by rw [hInv]
    _ = fundPair φ z t * ((fundPair φ z t).adjugate *
        Wt) := mul_assoc _ _ _
    _ = fundSpectralIntegral38 φ z t := by rw [hJ]; rfl

end
end NlsGge.GK38
