import NlsGge.GK38.PairVolterra

/-! Physical sign conjugacy for the actual L2 fundamental solution.
GK I.5 Neumann boundary normalization, using I.1 Volterra uniqueness. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def gaugeJ38 : PairMat38 := !![1, 0; 0, -1]

def gaugeSign38 (i : Fin 2) : ℂ := if i = 0 then 1 else -1

theorem gaugeJ38_sq : gaugeJ38 * gaugeJ38 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaugeJ38, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem gaugeJ38_conj_apply (M : PairMat38) (i j : Fin 2) :
    (gaugeJ38 * M * gaugeJ38) i j = gaugeSign38 i * M i j * gaugeSign38 j := by
  fin_cases i <;> fin_cases j <;>
    simp [gaugeJ38, gaugeSign38, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem coverRep38_neg_ae (f : PhysicalL2) :
    ∀ᵐ t : ℝ, coverRep38 (-f) t = -coverRep38 f t := by
  simpa only [neg_one_smul, neg_one_mul] using coverRep38_smul_ae (-1) f

theorem potCoeff38_neg_gauge_ae (φ : PotPair) :
    ∀ᵐ s : ℝ, potCoeff38 (-φ) s = gaugeJ38 * potCoeff38 φ s * gaugeJ38 := by
  have hneg : ∀ᵐ s : ℝ, potCoeff38 (-φ) s = -potCoeff38 φ s := by
    simpa only [neg_one_smul] using potCoeff38_smul_ae (-1) φ
  filter_upwards [hneg] with s hs
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeJ38, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

theorem zsCoeffPot38_neg_gauge_ae (φ : PotPair) (z : ℂ) :
    ∀ᵐ t : ℝ, zsCoeffPot38 (-φ) z t = gaugeJ38 * zsCoeffPot38 φ z t * gaugeJ38 := by
  filter_upwards [potCoeff38_neg_gauge_ae φ] with t ht
  rw [zsCoeffPot38_eq, zsCoeffPot38_eq, ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeJ38, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem freeE_gauge38 (z : ℂ) (t : ℝ) :
    gaugeJ38 * freeE z t * gaugeJ38 = freeE z t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeJ38, freeE, Matrix.mul_apply, Fin.sum_univ_two]

def gaugeFundCont38 (φ : PotPair) (z : ℂ) : C(Icc (0 : ℝ) 1, PairMat38) :=
  ⟨fun t => gaugeJ38 * fundCont φ z t * gaugeJ38,
    (continuous_const.mul (fundCont φ z).continuous).mul continuous_const⟩

theorem ext_gaugeFundCont38 (φ : PotPair) (z : ℂ) (s : ℝ) :
    ext38 (gaugeFundCont38 φ z) s = gaugeJ38 * ext38 (fundContP φ z) s * gaugeJ38 := rfl

theorem gauge_volterra_integrand38 (φ : PotPair) (z : ℂ) (t s : ℝ)
    (h : potCoeff38 (-φ) s = gaugeJ38 * potCoeff38 φ s * gaugeJ38) :
    freeE z (t - s) * potCoeff38 (-φ) s * ext38 (gaugeFundCont38 φ z) s =
      gaugeJ38 * (freeE z (t - s) * potCoeff38 φ s * ext38 (fundContP φ z) s) * gaugeJ38 := by
  rw [h, ext_gaugeFundCont38]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaugeJ38, freeE, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem gaugeFundCont38_integral_eq (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    gaugeFundCont38 φ z t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 (-φ) s *
        IccExtend zero_le_one (gaugeFundCont38 φ z) s) i j := by
  have hK : Continuous (fun s : ℝ => freeE z (t - s)) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have hInt := intervalIntegrable_triple_entry_of_mem φ hK
    (continuous_ext38 (fundContP φ z)) t.property i j
  have hNegInt := intervalIntegrable_triple_entry_of_mem (-φ) hK
    (continuous_ext38 (gaugeFundCont38 φ z)) t.property i j
  have hI : (∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 (-φ) s *
        ext38 (gaugeFundCont38 φ z) s) i j) =
      gaugeSign38 i * (∫ s in (0 : ℝ)..t,
        (freeE z (t - s) * potCoeff38 φ s * ext38 (fundContP φ z) s) i j) * gaugeSign38 j := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [potCoeff38_neg_gauge_ae φ] with s hs _
    rw [gauge_volterra_integrand38 φ z t s hs, gaugeJ38_conj_apply]
  have hE : gaugeSign38 i * freeE z t i j * gaugeSign38 j = freeE z t i j := by
    rw [← gaugeJ38_conj_apply, freeE_gauge38]
  calc gaugeFundCont38 φ z t i j = gaugeSign38 i * fundPair φ z t i j * gaugeSign38 j :=
      gaugeJ38_conj_apply _ i j
    _ = gaugeSign38 i * freeE z t i j * gaugeSign38 j +
        gaugeSign38 i * (∫ s in (0 : ℝ)..t,
          (freeE z (t - s) * potCoeff38 φ s * ext38 (fundContP φ z) s) i j) * gaugeSign38 j := by
      rw [fundPair_integral_eq]
      simp only [mul_add, add_mul]
      rfl
    _ = _ := by rw [hE, ← hI]; rfl

theorem fundPair_neg_gauge38 (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    fundPair (-φ) z t = gaugeJ38 * fundPair φ z t * gaugeJ38 := by
  have h := fundCont_unique (-φ) z (gaugeFundCont38 φ z)
    (gaugeFundCont38_integral_eq φ z)
  rw [fundPair_eq, ← h]
  rfl

theorem monodromyPair_neg_gauge38 (φ : PotPair) (z : ℂ) :
    monodromyPair (-φ) z = gaugeJ38 * monodromyPair φ z * gaugeJ38 := by
  simpa only [monodromyPair_eq_fundPair] using
    fundPair_neg_gauge38 φ z ⟨1, zero_le_one, le_rfl⟩

end
end NlsGge.GK38
