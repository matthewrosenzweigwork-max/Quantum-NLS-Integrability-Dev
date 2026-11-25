import NlsGge.GK38.PairAnalytic

/-! # F6: the small-interval L2 estimate for the Volterra primitive

Source: GK, Chapter I, Proposition 1.2. All interval integrability is
established before the integral comparison or the primitive subtraction.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
open NlsGge.Pilot
noncomputable section

/-- L2 bounds give a square-root modulus for the L1 mass of a subinterval. -/
theorem integral_coverRep38_small38 (f : PhysicalL2) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ s in a..b, ‖coverRep38 f s‖ ≤ Real.sqrt (b - a) * ‖f‖ := by
  have hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc ha hb
  have hi := (intervalIntegrable_coverRep38_sq_one f).mono_set hsub
  have hs : (∫ s in a..b, ‖coverRep38 f s‖ ^ 2) ≤ ‖f‖ ^ 2 := by
    rw [← integral_sq_coverRep38_one]
    exact intervalIntegral.integral_mono_interval ha hab hb
      (Eventually.of_forall fun s => sq_nonneg _) (intervalIntegrable_coverRep38_sq_one f)
  refine (integral_norm_le_sqrt_mul hab
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable hi).trans ?_
  gcongr
  simpa only [Real.sqrt_sq (norm_nonneg f)] using Real.sqrt_le_sqrt hs

/-- The sum of the two potential components has the same modulus, with factor two. -/
theorem integral_potW38_small38 (φ : PotPair) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ s in a..b, potW38 φ s ≤ 2 * ‖φ‖ * Real.sqrt (b - a) := by
  have hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc ha hb
  simp only [potW38, potRepFst38, potRepSnd38]
  rw [intervalIntegral.integral_add
    ((intervalIntegrable_norm_coverRep38_one φ.1).mono_set hsub)
    ((intervalIntegrable_norm_coverRep38_one φ.2).mono_set hsub)]
  have h1 := integral_coverRep38_small38 φ.1 ha hab hb
  have h2 := integral_coverRep38_small38 φ.2 ha hab hb
  have h3 := norm_fst_le φ
  have h4 := norm_snd_le φ
  have hs := Real.sqrt_nonneg (b - a)
  change (∫ s in a..b, ‖coverRep38 φ.1 s‖) +
    (∫ s in a..b, ‖coverRep38 φ.2 s‖) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left h3 hs, mul_le_mul_of_nonneg_left h4 hs]

/-- Every entry of the zero-spectral Volterra primitive has a common time modulus. -/
theorem norm_volterraZero_time_sub38 (φ : PotPair) (N : PairCont38)
    (s t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖volterraP φ 0 N t i j - volterraP φ 0 N s i j‖ ≤
      2 * ‖N‖ * ‖φ‖ * Real.sqrt |(t : ℝ) - s| := by
  suffices h : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ≤ t →
      ‖volterraP φ 0 N t i j - volterraP φ 0 N s i j‖ ≤
        2 * ‖N‖ * ‖φ‖ * Real.sqrt ((t : ℝ) - s) by
    rcases le_total (s : ℝ) t with hst | hts
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using h s t hst
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h t s hts
  intro s t hst
  let g : ℝ → ℂ := fun r => (potCoeff38 φ r * ext38 N r) i j
  have hi : IntervalIntegrable g volume 0 1 := by
    simpa only [freeE_zero_potential, one_mul] using
      intervalIntegrable_triple_entry φ (continuous_freeE 0) (continuous_ext38 N) i j
  have his : IntervalIntegrable g volume 0 (s : ℝ) := hi.mono_set (uIcc_zero_subset s.2)
  have hit : IntervalIntegrable g volume 0 (t : ℝ) := hi.mono_set (uIcc_zero_subset t.2)
  have hsub : Set.uIcc (s : ℝ) (t : ℝ) ⊆ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le hst, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc s.2.1 t.2.2
  have hw := ((intervalIntegrable_potW38 φ).mono_set hsub).mul_const ‖N‖
  simp only [volterraP_apply, volterraFun_apply, freeE_zero_potential, one_mul]
  change ‖(∫ r in (0 : ℝ)..(t : ℝ), g r) - ∫ r in (0 : ℝ)..(s : ℝ), g r‖ ≤ _
  rw [intervalIntegral.integral_interval_sub_left hit his]
  calc
    ‖∫ r in (s : ℝ)..(t : ℝ), g r‖ ≤ ∫ r in (s : ℝ)..(t : ℝ), potW38 φ r * ‖N‖ := by
      refine intervalIntegral.norm_integral_le_of_norm_le hst
        (Eventually.of_forall fun r hr => ?_) hw
      have hr' : r ∈ Set.Icc (0 : ℝ) 1 := ⟨s.2.1.trans hr.1.le, hr.2.trans t.2.2⟩
      have H := norm_triple_entry_le 0 (r := 0) le_rfl φ r (ext38 N r)
        (fun a b => norm_ext38_entry_le N hr' a b) i j
      simpa only [freeE_zero_potential, one_mul, Complex.zero_im, abs_zero,
        zero_mul, Real.exp_zero, one_mul] using H
    _ = (∫ r in (s : ℝ)..(t : ℝ), potW38 φ r) * ‖N‖ :=
      intervalIntegral.integral_mul_const _ _
    _ ≤ (2 * ‖φ‖ * Real.sqrt ((t : ℝ) - s)) * ‖N‖ :=
      mul_le_mul_of_nonneg_right (integral_potW38_small38 φ s.2.1 hst t.2.2) (norm_nonneg _)
    _ = _ := by ring

end
end NlsGge.GK38
