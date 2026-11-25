import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Sobolev.CMWeightComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter
open scoped Topology

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- For `|m| > n`, `⟨n+1⟩ ≤ ⟨m⟩`. -/
theorem japaneseBracket_succ_le_of_not_mem (n : ℕ) (m : ℤ) (hm : m ∉ symmetricModes n) :
    japaneseBracket ((n : ℤ) + 1) ≤ japaneseBracket m := by
  have h1 : (n : ℤ) + 1 ≤ |m| := by
    simp only [symmetricModes, Finset.mem_Icc, not_and_or, not_le] at hm
    rcases hm with h | h
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  have h2 : (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    have : ((n : ℤ) + 1) ^ 2 ≤ m ^ 2 := by
      rw [← sq_abs m]; exact pow_le_pow_left₀ (by omega) h1 2
    exact_mod_cast this
  unfold japaneseBracket
  exact Real.sqrt_le_sqrt (by linarith)

/-- Weight comparison on the tail: `fullModeWeight c s m ≤ (⟨n+1⟩^{-2s}/2) · cmModeWeight c m`
for `|m| > n`. -/
theorem fullModeWeight_le_tail (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n : ℕ) (m : ℤ) (hm : m ∉ symmetricModes n) :
    fullModeWeight c s m ≤
      (Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2) * cmModeWeight c m := by
  have hb : 0 < japaneseBracket ((n : ℤ) + 1) := by
    unfold japaneseBracket; positivity
  have hp : Real.rpow m.natAbs.cast 0 = 1 := by simp
  have hpow : Real.rpow (japaneseBracket m) (-2 * s) ≤
      Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) :=
    Real.rpow_le_rpow_of_nonpos hb (japaneseBracket_succ_le_of_not_mem n m hm) (by linarith)
  rw [fullModeWeight, cmModeWeight]
  have := sourceRate_pos c m
  calc sourceRate c m * Real.rpow (japaneseBracket m) (-2 * s)
      ≤ sourceRate c m * Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) :=
        mul_le_mul_of_nonneg_left hpow this.le
    _ = _ := by ring

theorem norm_incl_sub_trunc_sq_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n : ℕ) (h : ActualCM c) :
    ‖cmToFullWeightedHilbert c s hs0 h -
        cmToFullWeightedHilbert c s hs0 ((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖ ^ 2 ≤
      (Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2) * ‖h‖ ^ 2 := by
  set d : ActualCM c := h - ((cmTrunc c n h : actualCMHead c n) : ActualCM c) with hd
  have hsub : cmToFullWeightedHilbert c s hs0 h -
      cmToFullWeightedHilbert c s hs0 ((cmTrunc c n h : actualCMHead c n) : ActualCM c) =
      cmToFullWeightedHilbert c s hs0 d := by rw [hd, map_sub]
  rw [hsub]
  have hcoord : ∀ m, cmCoord d m = if m ∈ symmetricModes n then 0 else cmCoord h m := by
    intro m
    have : cmCoord d m = cmCoord h m -
        cmCoord ((cmTrunc c n h : actualCMHead c n) : ActualCM c) m := rfl
    rw [this, cmCoord_cmTrunc]
    split_ifs <;> simp
  have hE := weightedHilbert_hasSum (fullModeWeight c s)
    (show WeightedHilbert (fullModeWeight c s) from cmToFullWeightedHilbert c s hs0 d)
  have hH := weightedHilbert_hasSum (cmModeWeight c)
    (show WeightedHilbert (cmModeWeight c) from h)
  have hH' := hH.mul_left (Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2)
  refine hasSum_le (fun m => ?_) hE hH'
  have e1 : (show WeightedHilbert (fullModeWeight c s) from cmToFullWeightedHilbert c s hs0 d)
      m = cmCoord d m := rfl
  have e2 : (show WeightedHilbert (cmModeWeight c) from h) m = cmCoord h m := rfl
  simp only [e1, e2]
  rw [hcoord m]
  by_cases hm : m ∈ symmetricModes n
  · have hb : 0 < japaneseBracket ((n : ℤ) + 1) := by unfold japaneseBracket; positivity
    have hr := Real.rpow_pos_of_pos hb (-2 * s)
    have hcm := cmModeWeight_pos c m
    simp only [hm, ite_true, norm_zero]
    have : 0 ≤ Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2 *
        (cmModeWeight c m * ‖cmCoord h m‖ ^ 2) := by positivity
    simpa using this
  · simp only [hm, ite_false]
    have := fullModeWeight_le_tail c s hs0 n m hm
    calc fullModeWeight c s m * ‖cmCoord h m‖ ^ 2
        ≤ (Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2 * cmModeWeight c m) *
            ‖cmCoord h m‖ ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring

theorem exists_tail_small (c : BoundedCoefficients lower upper) (s : ℝ) (hs : 0 < s)
    (d ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ h : ActualCM c, ‖h‖ < d →
      ‖cmToFullWeightedHilbert c s hs.le h -
        cmToFullWeightedHilbert c s hs.le
          ((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖ < ε / 2 := by
  have hjb : Tendsto (fun n : ℕ => japaneseBracket ((n : ℤ) + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    show ((n + 1 : ℕ) : ℝ) ≤ _
    unfold japaneseBracket
    apply Real.le_sqrt_of_sq_le
    push_cast; nlinarith
  have hrp : Tendsto (fun n : ℕ => Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s)) atTop
      (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 2 * s) (by linarith)).comp hjb
    refine this.congr (fun n => ?_)
    simp only [Function.comp, Real.rpow_eq_pow]
    rw [show -2 * s = -(2 * s) by ring]
  have hlim : Tendsto (fun n : ℕ => Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2 *
      (d ^ 2)) atTop (𝓝 (0 / 2 * d ^ 2)) := (hrp.div_const 2).mul_const _
  rw [zero_div, zero_mul] at hlim
  have hpos : 0 < (ε / 2) ^ 2 := by positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨n₀, fun n hn h hh => ?_⟩
  have hd : 0 < d := lt_of_le_of_lt (norm_nonneg h) hh
  have h1 := norm_incl_sub_trunc_sq_le c s hs.le n h
  have hC : 0 ≤ Real.rpow (japaneseBracket ((n : ℤ) + 1)) (-2 * s) / 2 := by
    have : 0 < japaneseBracket ((n : ℤ) + 1) := by unfold japaneseBracket; positivity
    have := Real.rpow_pos_of_pos this (-2 * s)
    positivity
  have h2 : ‖h‖ ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (norm_nonneg h) hh.le 2
  have h3 := hn₀ n hn
  have h4 : ‖cmToFullWeightedHilbert c s hs.le h -
        cmToFullWeightedHilbert c s hs.le
          ((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖ ^ 2 < (ε / 2) ^ 2 :=
    lt_of_le_of_lt (h1.trans (mul_le_mul_of_nonneg_left h2 hC)) h3
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h4

end NlsGge.Ramer
