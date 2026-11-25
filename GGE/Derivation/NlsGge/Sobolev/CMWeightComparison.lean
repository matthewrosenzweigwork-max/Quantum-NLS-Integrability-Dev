import NlsGge.Sobolev.SourceEmbeddings

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

variable {lower upper : ℝ}

/-- The real Cameron--Martin norm weight carries the source variance factor two. -/
abbrev cmModeWeight (c : BoundedCoefficients lower upper) : ℤ → ℝ :=
  fun n => 2 * sourceRate c n

theorem cmModeWeight_pos (c : BoundedCoefficients lower upper) (n : ℤ) :
    0 < cmModeWeight c n := by
  exact mul_pos (by norm_num) (sourceRate_pos c n)

instance cmModeWeightPositive (c : BoundedCoefficients lower upper) :
    Fact (∀ n : ℤ, 0 < cmModeWeight c n) :=
  ⟨fun n => cmModeWeight_pos c n⟩

/-- The target E_s weight is at most half the CM weight for nonnegative s. -/
theorem fullModeWeight_le_half_cmModeWeight (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    fullModeWeight c s n ≤ (1 / 2 : ℝ) * cmModeWeight c n := by
  rw [fullModeWeight, cmModeWeight]
  have hpow : Real.rpow (japaneseBracket n) (-2 * s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (japaneseBracket_one_le n) (by linarith)
  calc
    sourceRate c n * Real.rpow (japaneseBracket n) (-2 * s) ≤
        sourceRate c n * 1 :=
      mul_le_mul_of_nonneg_left hpow (sourceRate_pos c n).le
    _ = (1 / 2 : ℝ) * (2 * sourceRate c n) := by ring

/-- The identity on Fourier sequences as a real continuous linear map from the
CM-weighted carrier into the unchanged source E_s carrier. -/
def cmToFullWeightedHilbert (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : 0 ≤ s) :
    WeightedRealHilbert (cmModeWeight c) →L[ℝ] FullWeightedHilbert c s :=
  weightedRealComparisonContinuous (cmModeWeight c) (fullModeWeight c s)
    (1 / 2 : ℝ) (by norm_num)
    (fullModeWeight_le_half_cmModeWeight c s hs)

theorem cmToFullWeightedHilbert_apply (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : 0 ≤ s) (x : WeightedRealHilbert (cmModeWeight c)) (n : ℤ) :
    (show WeightedHilbert (fullModeWeight c s) from
      cmToFullWeightedHilbert c s hs x) n =
    (show WeightedHilbert (cmModeWeight c) from x) n := rfl

theorem cmToFullWeightedHilbert_norm_le (c : BoundedCoefficients lower upper)
    (s : ℝ) (hs : 0 ≤ s) (x : WeightedRealHilbert (cmModeWeight c)) :
    ‖cmToFullWeightedHilbert c s hs x‖ ≤ Real.sqrt (1 / 2 : ℝ) * ‖x‖ :=
  weightedRealComparison_norm_le (cmModeWeight c) (fullModeWeight c s)
    (1 / 2 : ℝ) (by norm_num)
    (fullModeWeight_le_half_cmModeWeight c s hs) x

end NlsGge.Pilot
