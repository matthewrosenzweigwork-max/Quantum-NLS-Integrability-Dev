import NlsGge.GK38.TauGammaL2Realization
import NlsGge.GK38.Lib.EntireProductsParamd

/-! The exterior factor is a convergent symmetric product of two accepted omitted products. -/
set_option autoImplicit false
open Filter Topology Set Metric SummationFilter
namespace NlsGge.GK38
noncomputable section

def periodicPlusDeviation38 (φ : PotPair) : Lib.L2Seq :=
  l2SequenceOf38 (fun n => lamPlus φ n - (n : ℂ) * (Real.pi : ℂ))

def periodicMinusDeviation38 (φ : PotPair) : Lib.L2Seq :=
  l2SequenceOf38 (fun n => lamMinus φ n - (n : ℂ) * (Real.pi : ℂ))

theorem periodicPlus_sigma38 (φ : PotPair) (n : ℤ) :
    Lib.sigmaOf (periodicPlusDeviation38 φ) n = lamPlus φ n := by
  unfold Lib.sigmaOf periodicPlusDeviation38
  rw [l2SequenceOf_apply38 _ (periodic_plus_summable38 φ)]
  ring

theorem periodicMinus_sigma38 (φ : PotPair) (n : ℤ) :
    Lib.sigmaOf (periodicMinusDeviation38 φ) n = lamMinus φ n := by
  unfold Lib.sigmaOf periodicMinusDeviation38
  rw [l2SequenceOf_apply38 _ (periodic_minus_summable38 φ)]
  ring

theorem excludedPairedFactors_eq_mul38 (φ : PotPair) (n : ℤ) (z : ℂ) :
    excludedPairedFactors38 φ n z = fun m =>
      Lib.omitFactor n (periodicPlusDeviation38 φ) z m *
        Lib.omitFactor n (periodicMinusDeviation38 φ) z m := by
  funext m
  by_cases hm : m = n
  · simp [excludedPairedFactors38, Lib.omitFactor, hm]
  · simp only [excludedPairedFactors38, Lib.omitFactor, hm, ite_false,
      pairedFactors_eq_mul38, Lib.prodFactor, periodicPlus_sigma38, periodicMinus_sigma38]

theorem exterior_multipliable38 (φ : PotPair) (n : ℤ) (z : ℂ) :
    Multipliable (excludedPairedFactors38 φ n z) (symmetricIcc ℤ) := by
  rw [excludedPairedFactors_eq_mul38]
  exact (Lib.multipliable_omit n (periodicPlusDeviation38 φ) z).mul
    (Lib.multipliable_omit n (periodicMinusDeviation38 φ) z)

theorem exterior_eq_omitProducts38 (φ : PotPair) (n : ℤ) (z : ℂ) :
    exteriorFactor38 φ n z = Lib.omitProd n (periodicPlusDeviation38 φ) z *
      Lib.omitProd n (periodicMinusDeviation38 φ) z := by
  have hp := Lib.multipliable_omit n (periodicPlusDeviation38 φ) z
  have hm := Lib.multipliable_omit n (periodicMinusDeviation38 φ) z
  have hall := exterior_multipliable38 φ n z
  unfold exteriorFactor38
  rw [excludedPairedFactors_eq_mul38]
  simp only [Lib.omitFactor]
  rw [hp.tprod_mul hm]
  unfold Lib.omitProd
  simp only [one_div]
  ring

theorem exterior_entire38 (φ : PotPair) (n : ℤ) :
    AnalyticOnNhd ℂ (exteriorFactor38 φ n) univ := by
  have he : exteriorFactor38 φ n = fun z =>
      Lib.omitProd n (periodicPlusDeviation38 φ) z * Lib.omitProd n (periodicMinusDeviation38 φ) z :=
    funext (exterior_eq_omitProducts38 φ n)
  rw [he]
  intro z _
  exact (Lib.analyticAt_omitProd_line n (periodicPlusDeviation38 φ) z).mul
    (Lib.analyticAt_omitProd_line n (periodicMinusDeviation38 φ) z)

theorem exterior_perChar_factor38 (φ : PotPair) (n : ℤ) (z : ℂ) :
    perChar φ z = -4 * (lamPlus φ n - z) * (lamMinus φ n - z) * exteriorFactor38 φ n z := by
  have hp : singleProduct38 (lamPlus φ) z =
      (lamPlus φ n - z) * Lib.omitProd n (periodicPlusDeviation38 φ) z := by
    simpa only [Lib.prodFactor, periodicPlus_sigma38, singleProduct38] using
      Lib.entProd_eq_mul_omitProd n (periodicPlusDeviation38 φ) z
  have hm : singleProduct38 (lamMinus φ) z =
      (lamMinus φ n - z) * Lib.omitProd n (periodicMinusDeviation38 φ) z := by
    simpa only [Lib.prodFactor, periodicMinus_sigma38, singleProduct38] using
      Lib.entProd_eq_mul_omitProd n (periodicMinusDeviation38 φ) z
  rw [perChar_eq_periodicProduct38]
  change -4 * pairedProduct38 φ z = _
  rw [pairedProduct_eq_mul38, hp, hm, exterior_eq_omitProducts38]
  ring

theorem exterior_nonzero_in_disc38 (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hf : IsolatingFamily38 φ C R) (n : ℤ) (z : ℂ) (hz : z ∈ ball (C n) (R n)) :
    exteriorFactor38 φ n z ≠ 0 := by
  obtain ⟨c, N, hg, hs⟩ := hf
  have hA (m : ℤ) : lamMinus φ m ∈ ball (C m) (R m) :=
    (hs.1 m).1 (left_mem_segment ℝ _ _)
  have hB (m : ℤ) : lamPlus φ m ∈ ball (C m) (R m) :=
    (hs.1 m).1 (right_mem_segment ℝ _ _)
  have hd := isolating_geometry_disjoint38 C R c N hg
  rw [exterior_eq_omitProducts38]
  apply mul_ne_zero
  · intro he
    obtain ⟨m, hmn, heq⟩ := (Lib.omitProd_eq_zero_iff n (periodicPlusDeviation38 φ) z).mp he
    rw [periodicPlus_sigma38] at heq
    exact (Set.disjoint_left.mp (hd hmn)) (heq ▸ hB m) hz
  · intro he
    obtain ⟨m, hmn, heq⟩ := (Lib.omitProd_eq_zero_iff n (periodicMinusDeviation38 φ) z).mp he
    rw [periodicMinus_sigma38] at heq
    exact (Set.disjoint_left.mp (hd hmn)) (heq ▸ hA m) hz

end
end NlsGge.GK38
