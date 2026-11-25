import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.GK38.EigenvalueCompactnessStrong
import NlsGge.GK38.RealTypeSpectrumConstant
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Spectral.ActualGapHeightHolderE02_38

set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.AblowitzLadik
open NlsGge.HierarchyRiccati.Core NlsGge.Analysis
namespace NlsGge.GK38
noncomputable section
local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- Exact full finite-plane half trace, before selecting any labelled endpoint. -/
theorem planeWave_halfTrace_cos38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N)
    (t : ℝ) (z κ : ℂ) (hκ : κ ^ 2 = (z + Real.pi * k) ^ 2 - (t : ℂ) ^ 2) :
    actualPhysicalUnitHalfTrace32 (planeL2 N (planeWaveCoeff38 N k t)) z =
      (-1 : ℂ) ^ k * Complex.cos κ := by
  obtain ⟨c, d, hcd, hc, hd, h1⟩ := cd_exists38 (κ * Complex.I)
  have hσ : (κ * Complex.I) ^ 2 = (t : ℂ) ^ 2 - (z + Real.pi * k) ^ 2 := by
    rw [mul_pow, Complex.I_sq, hκ]
    ring
  unfold actualPhysicalUnitHalfTrace32
  rw [actualComplexZsDysonTsum_eq_of_ae_eq _ (planeReal N (planeWaveCoeff38 N k t)) z
      (planeReal_cover_ae38 N (planeWaveCoeff38 N k t)) 1 (by norm_num),
    planeReal_planeWave38 N k hk t,
    planeDyson38 k t z (z + Real.pi * k) (κ * Complex.I) rfl hσ c d hcd hc hd,
    planeFund_trace38, h1, Complex.cosh_mul_I]
  ring

/-- Every actual real plane-wave characteristic root has integer squared shifted frequency. -/
theorem planeWave_root_frequency38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t x : ℝ)
    (hx : perChar (realSlice (planeL2 N (planeWaveCoeff38 N k t))) (x : ℂ) = 0) :
    ∃ m : ℤ, (x + Real.pi * k) ^ 2 - t ^ 2 = ((m : ℝ) * Real.pi) ^ 2 := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq
    (((x : ℂ) + Real.pi * k) ^ 2 - (t : ℂ) ^ 2) (n := 2) (by norm_num)
  have hs : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
    calc
      _ = (-1 : ℂ) ^ (k * 2 : ℤ) := by simpa using (zpow_mul (-1 : ℂ) k 2).symm
      _ = ((-1 : ℂ) ^ (2 : ℤ)) ^ k := by rw [Int.mul_comm k 2, zpow_mul]
      _ = 1 := by norm_num
  rw [perChar_realSlice, planeWave_halfTrace_cos38 N k hk t (x : ℂ) κ hκ,
    mul_pow, hs, one_mul] at hx
  have hc : Complex.cos κ ^ 2 = 1 := by linear_combination hx / 4
  have hsin : Complex.sin κ = 0 := by
    have hzero : Complex.sin κ ^ 2 = 0 := by
      linear_combination Complex.sin_sq_add_cos_sq κ - hc
    exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hzero
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp hsin
  refine ⟨m, ?_⟩
  have he : ((x : ℂ) + Real.pi * k) ^ 2 - (t : ℂ) ^ 2 = ((m : ℂ) * Real.pi) ^ 2 := by
    rw [← hκ, hm]
  exact_mod_cast he

/-- Amplitude scaling is scalar multiplication in the actual L2 realization. -/
theorem planeWave_L2_smul38 (N : ℕ) (k : ℤ) (s t : ℝ) :
    planeL2 N (planeWaveCoeff38 N k (s * t)) = s • planeL2 N (planeWaveCoeff38 N k t) := by
  have h : planeContinuous N (planeWaveCoeff38 N k (s * t)) =
      (s : ℂ) • planeContinuous N (planeWaveCoeff38 N k t) := by
    ext x
    simp only [planeContinuous, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      planeField, planeWaveCoeff38, Complex.ofReal_mul, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    funext i
    split_ifs <;> ring
  change ContinuousMap.toLp 2 spatialMeasure ℂ _ = _
  rw [h, map_smul]
  exact_mod_cast rfl

/-- Actual normalized quasimomentum-level endpoints retain their integer square along amplitude. -/
theorem planeWave_endpoint_square38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N)
    (t : ℝ) (n : ℤ) (upper : Bool) :
    (periodicEndpoint38 (planeL2 N (planeWaveCoeff38 N k t)) n upper + Real.pi * k) ^ 2 - t ^ 2 =
      (((n + k : ℤ) : ℝ) * Real.pi) ^ 2 := by
  let u : PhysicalL2 := planeL2 N (planeWaveCoeff38 N k t)
  let x : ℝ → ℝ := fun s => periodicEndpoint38 (s • u) n upper
  let q : ℝ → ℝ := fun s => ((x s + Real.pi * k) ^ 2 - (s * t) ^ 2) / Real.pi ^ 2
  have hxcont : ContinuousOn x (Icc 0 1) := by
    cases upper
    · exact gapLower_norm_path_continuous38 u n
    · exact gapUpper_norm_path_continuous38 u n
  have hqcont : ContinuousOn q (Icc 0 1) :=
    (((hxcont.add continuous_const.continuousOn).pow 2).sub
      ((continuous_id.mul continuous_const).continuousOn.pow 2)).div_const (Real.pi ^ 2)
  have hgrid (s : ℝ) (_hs : s ∈ Icc 0 1) : ∃ m : ℤ, q s = (m : ℝ) := by
    have hroot : perChar (realSlice (s • u)) (x s : ℂ) = 0 := by
      cases upper
      · exact (gap_endpoint_roots38 (s • u) n).1
      · exact (gap_endpoint_roots38 (s • u) n).2
    have hroot' : perChar (realSlice (planeL2 N (planeWaveCoeff38 N k (s * t)))) (x s : ℂ) = 0 := by
      simpa only [planeWave_L2_smul38, u] using hroot
    obtain ⟨m, hm⟩ := planeWave_root_frequency38 N k hk (s * t) (x s) hroot'
    refine ⟨m ^ 2, ?_⟩
    dsimp only [q]
    rw [hm]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hsub : q '' Icc 0 1 ⊆ range ((↑) : ℤ → ℝ) := by
    rintro y ⟨s, hs, rfl⟩
    obtain ⟨m, hm⟩ := hgrid s hs
    exact ⟨m, hm.symm⟩
  have hd : IsDiscrete (q '' Icc 0 1) :=
    Real.isClosedEmbedding_intCast.isInducing.isDiscrete_range.mono hsub
  have hsingle := (isPreconnected_Icc.image q hqcont).isDiscrete_iff_subsingleton.mp hd
  have he := hsingle (mem_image_of_mem q (by norm_num : (1 : ℝ) ∈ Icc 0 1))
    (mem_image_of_mem q (by norm_num : (0 : ℝ) ∈ Icc 0 1))
  have hx0 : x 0 = (n : ℝ) * Real.pi := by
    simp only [x, zero_smul, periodicEndpoint_zero38]
  have hx1 : x 1 = periodicEndpoint38 u n upper := by simp only [x, one_smul]
  dsimp only [q] at he
  rw [hx0, hx1] at he
  have hpi : Real.pi ^ 2 ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have he' : (periodicEndpoint38 u n upper + Real.pi * k) ^ 2 - t ^ 2 =
      ((n : ℝ) * Real.pi + Real.pi * k) ^ 2 := by
    simpa only [one_mul, zero_mul, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      (div_left_inj' hpi).mp he
  rw [he']
  push_cast
  ring

/-- The exact positive support of the actual height, retaining every real amplitude. -/
theorem planeWave_height_pos_iff38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t x : ℝ) :
    0 < actualGapHeightE02_38 (planeL2 N (planeWaveCoeff38 N k t)) x ↔
      -Real.pi * k - |t| < x ∧ x < -Real.pi * k + |t| := by
  rw [actualGapHeight_planeWave38 N k hk t x, planeGapCont38, Real.sqrt_pos,
    lt_max_iff]
  simp only [lt_self_iff_false, false_or, sub_pos]
  rw [sq_lt_sq, abs_lt]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- A genuine actual labelled interval containing the plane-wave center has the exact support ends.
The proof uses interior semicircle positivity and actual endpoint height zero. -/
theorem planeWave_endpoints_of_center38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) (n : ℤ)
    (hcenter : -Real.pi * k ∈ Set.Ioo
      (actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n)
      (actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n)) :
    actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n = -Real.pi * k - |t| ∧
    actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n = -Real.pi * k + |t| := by
  let u : PhysicalL2 := planeL2 N (planeWaveCoeff38 N k t)
  let a := actualGapLowerAllE02_38 u n
  let b := actualGapUpperAllE02_38 u n
  have hca : a < -Real.pi * k := hcenter.1
  have hcb : -Real.pi * k < b := hcenter.2
  have hinterior : ∀ x ∈ Set.Ioo a b, -Real.pi * k - |t| < x ∧
      x < -Real.pi * k + |t| := by
    intro x hx
    exact (planeWave_height_pos_iff38 N k hk t x).mp
      (NlsGge.Birkhoff.actualGapHeight_pos_of_mem_Ioo38 u n x hx)
  have hleft : -Real.pi * k - |t| ≤ a := by
    by_contra h
    have ha : a < -Real.pi * k - |t| := lt_of_not_ge h
    have hmid := hinterior ((a + (-Real.pi * k - |t|)) / 2)
      ⟨by linarith, by linarith [abs_nonneg t]⟩
    linarith [hmid.1]
  have hright : b ≤ -Real.pi * k + |t| := by
    by_contra h
    have hb : -Real.pi * k + |t| < b := lt_of_not_ge h
    have hmid := hinterior ((-Real.pi * k + |t| + b) / 2)
      ⟨by linarith [abs_nonneg t], by linarith⟩
    linarith [hmid.2]
  obtain ⟨hazero, hbzero⟩ := gapHeight_endpoint_zero_E02_38 u n
  have haeq : a = -Real.pi * k - |t| := by
    refine le_antisymm (le_of_not_gt ?_) hleft
    intro ha
    have hpos := (planeWave_height_pos_iff38 N k hk t a).mpr
      ⟨ha, by linarith [abs_nonneg t]⟩
    change 0 < actualGapHeightE02_38 u a at hpos
    rw [hazero] at hpos
    exact (lt_irrefl 0) hpos
  have hbeq : b = -Real.pi * k + |t| := by
    refine le_antisymm hright (le_of_not_gt ?_)
    intro hb
    have hpos := (planeWave_height_pos_iff38 N k hk t b).mpr
      ⟨by linarith [abs_nonneg t], hb⟩
    change 0 < actualGapHeightE02_38 u b at hpos
    rw [hbzero] at hpos
    exact (lt_irrefl 0) hpos
  exact ⟨haeq, hbeq⟩

/-- Both actual endpoints at the active label, for all signed and zero real amplitudes. -/
theorem planeWaveOpenEndpoints38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) :
    actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) =
        -Real.pi * k - |t| ∧
    actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) =
        -Real.pi * k + |t| := by
  by_cases ht : t = 0
  · subst t
    have hu : planeL2 N (planeWaveCoeff38 N k 0) = 0 := by
      simpa using planeWave_L2_smul38 N k 0 1
    rw [hu]
    obtain ⟨ha, hb⟩ := gap_zero38 (-k)
    constructor
    · rw [ha]
      simp only [abs_zero, sub_zero, Int.cast_neg]
      ring
    · rw [hb]
      simp only [abs_zero, add_zero, Int.cast_neg]
      ring
  · have hpos : 0 < actualGapHeightE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-Real.pi * k) := by
      apply (planeWave_height_pos_iff38 N k hk t _).mpr
      have ha := abs_pos.mpr ht
      constructor <;> linarith
    obtain ⟨n, hcenter⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38
      (planeL2 N (planeWaveCoeff38 N k t)) (-Real.pi * k) (ne_of_gt hpos)
    obtain ⟨ha, hb⟩ := planeWave_endpoints_of_center38 N k hk t n hcenter
    have hinvariant := planeWave_endpoint_square38 N k hk t n false
    change (actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n + Real.pi * k) ^ 2 - t ^ 2 =
      (((n + k : ℤ) : ℝ) * Real.pi) ^ 2 at hinvariant
    rw [ha] at hinvariant
    have hzero : (((n + k : ℤ) : ℝ) * Real.pi) ^ 2 = 0 := by
      nlinarith [sq_abs t]
    have hprod : ((n + k : ℤ) : ℝ) * Real.pi = 0 :=
      (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hzero
    have hsum : n + k = 0 := by
      exact_mod_cast (mul_eq_zero.mp hprod).resolve_right Real.pi_ne_zero
    have hn : n = -k := by omega
    subst n
    exact ⟨ha, hb⟩
/-- Every other actual labelled interval is closed, using disjoint actual quasimomentum levels. -/
theorem planeWave_other_closed38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) (n : ℤ)
    (hn : n ≠ -k) :
    actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n =
      actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n := by
  let u : PhysicalL2 := planeL2 N (planeWaveCoeff38 N k t)
  have hnotopen : ¬actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
    intro hopen
    let x := (actualGapLowerAllE02_38 u n + actualGapUpperAllE02_38 u n) / 2
    have hx : x ∈ Set.Ioo (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
      ⟨by dsimp [x]; linarith, by dsimp [x]; linarith⟩
    have hpos := NlsGge.Birkhoff.actualGapHeight_pos_of_mem_Ioo38 u n x hx
    have hactive := (planeWave_height_pos_iff38 N k hk t x).mp hpos
    obtain ⟨ha, hb⟩ := planeWaveOpenEndpoints38 N k hk t
    have hp_n : actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
      have hm : x ∈ actualGapLevelSetE02_38 u n := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]
        exact ⟨hx.1.le, hx.2.le⟩
      exact hm
    have hp_active : actualQuasimomentumRealPartE02_38 u x = ((-k : ℤ) : ℝ) * Real.pi := by
      have hm : x ∈ actualGapLevelSetE02_38 u (-k) := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u (-k)).2]
        change actualGapLowerAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) ≤ x ∧
          x ≤ actualGapUpperAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k)
        rw [ha, hb]
        exact ⟨hactive.1.le, hactive.2.le⟩
      exact hm
    exact hn (gap_level_index_unique38 (hp_n.symm.trans hp_active))
  exact le_antisymm (NlsGge.Birkhoff.actualGapLower_le_upper38 u n) (not_lt.mp hnotopen)

/-- Exact active action, with integrability earned before the semicircle integral identity. -/
theorem planeWave_active_action38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) :
    actualGapActionAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) (-k) = t ^ 2 := by
  let u : PhysicalL2 := planeL2 N (planeWaveCoeff38 N k t)
  let a : ℝ := -Real.pi * k - |t|
  let b : ℝ := -Real.pi * k + |t|
  obtain ⟨ha, hb⟩ := planeWaveOpenEndpoints38 N k hk t
  have hab : a ≤ b := by dsimp [a, b]; linarith [abs_nonneg t]
  have hheight : IntervalIntegrable (actualGapHeightE02_38 u) volume a b := by
    simpa only [u, ha, hb, a, b] using gapAction_intervalIntegrable_L2_38 u (-k)
  have hsemi : IntervalIntegrable (gapSemicircle a b) volume a b := by
    have hc : Continuous (gapSemicircle a b) := by unfold gapSemicircle; fun_prop
    exact hc.intervalIntegrable _ _
  have hprofile : ∀ x ∈ Set.Icc a b, actualGapHeightE02_38 u x = gapSemicircle a b x := by
    intro x hx
    have hbound : |x + Real.pi * k| ≤ |t| := by
      apply abs_le.mpr
      constructor <;> dsimp [a, b] at hx <;> linarith [hx.1, hx.2]
    have hrad : 0 ≤ t ^ 2 - (x + Real.pi * k) ^ 2 := by
      nlinarith [(sq_le_sq).mpr hbound]
    rw [actualGapHeight_planeWave38 N k hk t x, planeGapCont38, max_eq_right hrad]
    unfold gapSemicircle
    congr 1
    dsimp [a, b]
    nlinarith [sq_abs t]
  have hint : (∫ x in a..b, actualGapHeightE02_38 u x) = ∫ x in a..b, gapSemicircle a b x := by
    exact intervalIntegral.integral_congr (fun x hx => hprofile x (by
      simpa only [Set.uIcc_of_le hab] using hx))
  change (2 / Real.pi) * (∫ x in actualGapLowerAllE02_38 u (-k)..actualGapUpperAllE02_38 u (-k),
    actualGapHeightE02_38 u x) = t ^ 2
  rw [ha, hb]
  change (2 / Real.pi) * (∫ x in a..b, actualGapHeightE02_38 u x) = t ^ 2
  rw [hint, integral_gapSemicircle a b hab]
  dsimp [a, b]
  field_simp [Real.pi_ne_zero]
  nlinarith [sq_abs t]

/-- Every finite representation and every signed real amplitude has exactly the active action t². -/
theorem planeWaveActionProbe38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) (n : ℤ) :
    actualGapActionAllE02_38 (planeL2 N (planeWaveCoeff38 N k t)) n =
      if n = -k then t ^ 2 else 0 := by
  split_ifs with hn
  · subst n
    exact planeWave_active_action38 N k hk t
  · have hclosed := planeWave_other_closed38 N k hk t n hn
    have _height_integrable := gapAction_intervalIntegrable_L2_38
      (planeL2 N (planeWaveCoeff38 N k t)) n
    simp only [actualGapActionAllE02_38, hclosed, intervalIntegral.integral_same, mul_zero]

end
end NlsGge.GK38
