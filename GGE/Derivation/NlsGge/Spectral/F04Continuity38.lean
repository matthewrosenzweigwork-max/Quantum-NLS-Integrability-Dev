import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Spectral.F04LiteralBounds38
import NlsGge.Spectral.UniformTailsTannery38
import NlsGge.Spectral.F04MomentTightness38
import NlsGge.Spectral.ActualGapActionContinuityE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # Q4: F04.04, continuity of the spectral remainder on `H^{m-1}`

Conditional on `NonlinRiccatiSmoothBound38 (m-1)`. Fixed-gap continuity (E03-cont), uniform weighted
tails of the actions (Q3 plus gap localization), the pointwise bound F04.03 (Q1), and Tannery with
uniformly small tails (Q2). -/

/-! ## Pointwise comparison of the bracket-weighted action with the weighted height integral -/

theorem bracket_action_le_setIntegral38 (k : ℕ) (u : PhysicalL2) (K : ℝ) (hK : 0 < K)
    (hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |l - (n:ℝ) * Real.pi| ≤ K / japaneseBracket n) (n : ℤ) :
    japaneseBracket n ^ (2*k) * actualGapActionAllE02_38 u n ≤
      (((1 + K)^(2*k) * 2^(2*k)) * (2 / Real.pi)) *
        ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
          momentDensity38 k u x := by
  have hpi := Real.pi_pos
  set Cb : ℝ := (1 + K)^(2*k) * 2^(2*k) with hCb
  have hab := actualGapLower_le_upper_F04_38 u n
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hIn : actualGapActionAllE02_38 u n =
      (2 / Real.pi) * ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x := by
    unfold actualGapActionAllE02_38
    congr 1
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hvon : IntegrableOn (actualGapHeightE02_38 u)
      (Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :=
    hvc.integrableOn_Icc
  have hfon : IntegrableOn (momentDensity38 k u)
      (Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :=
    (continuous_momentDensity38 k u).integrableOn_Icc
  have hle : ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x ≤
      ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
        Cb * momentDensity38 k u x := by
    refine setIntegral_mono_on (hvon.const_mul _) (hfon.const_mul _) measurableSet_Icc
      (fun x hx => ?_)
    have h1 := bracket_pow_le_on_gap38 k K hK n x (hloc n x hx)
    have h2 := actualGapHeightE02_38_nonneg u x
    calc japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x
        ≤ (Cb * (1 + (2*x)^(2*k))) * actualGapHeightE02_38 u x :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Cb * momentDensity38 k u x := by unfold momentDensity38; ring
  rw [hIn]
  calc japaneseBracket n ^ (2*k) * ((2 / Real.pi) * ∫ x in
        Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x)
      = (2 / Real.pi) * ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
          japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x := by
        rw [integral_const_mul]; ring
    _ ≤ (2 / Real.pi) * ∫ x in Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
          Cb * momentDensity38 k u x := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (Cb * (2 / Real.pi)) * ∫ x in Icc (actualGapLowerAllE02_38 u n)
          (actualGapUpperAllE02_38 u n), momentDensity38 k u x := by
        rw [integral_const_mul]; ring

/-- Summability of the tail-truncated bracket-weighted action. -/
theorem summable_ite_bracket_action38 (k : ℕ) (hk : 1 ≤ k) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k:ℝ) (physicalFourier u)) (N : ℕ) :
    Summable (fun n : ℤ => if (N:ℤ) < |n| then
      japaneseBracket n ^ (2*k) * actualGapActionAllE02_38 u n else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_bracket_action38 k hk u hu)
  · split_ifs
    · exact mul_nonneg (by have := japaneseBracket_pos n; positivity) (actualGapAction_nonneg_F04_38 u n)
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact mul_nonneg (by have := japaneseBracket_pos n; positivity) (actualGapAction_nonneg_F04_38 u n)

/-! ## Uniform weighted tails of the actions -/

theorem actionTails_uniform_aux38 (k : ℕ) (hk : 1 ≤ k) (hR3c : NonlinRiccatiSmoothBound38 k)
    (y : ℕ → SobolevHilbert (k : ℝ)) (yLim : SobolevHilbert (k : ℝ))
    (hy : Tendsto y atTop (𝓝 yLim)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∑' n : ℤ, (if (N:ℤ) < |n| then japaneseBracket n ^ (2*k) *
        actualGapActionAllE02_38 (sobolevToL2_38 k (y j)) n else 0) ≤ ε := by
  intro ε hε
  have hpi := Real.pi_pos
  set B : ℝ := ‖yLim‖ + 1 with hB
  have hB1 : 1 ≤ B := by have := norm_nonneg yLim; linarith
  obtain ⟨K, hK, hlocB⟩ := actualGapLocalization_E02_38 B hB1
  have hev : ∀ᶠ j in atTop, ‖y j‖ ≤ B :=
    (hy.norm.eventually (gt_mem_nhds (by linarith : ‖yLim‖ < B))).mono fun j h => h.le
  obtain ⟨j₂, hj₂⟩ := eventually_atTop.mp hev
  set Cb : ℝ := (1 + K)^(2*k) * 2^(2*k) with hCb
  have hCbpos : 0 < Cb := by positivity
  set c : ℝ := Cb * (2 / Real.pi) with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨L, hL, j₁, hj₁⟩ := moment_tight38 k hk hR3c y yLim hy (ε / c) (by positivity)
  obtain ⟨N0, hN0⟩ := exists_nat_ge (L + K)
  refine ⟨N0, max j₁ j₂, fun j hj => ?_⟩
  have hjj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hjj₂ : j₂ ≤ j := le_trans (le_max_right _ _) hj
  set u : PhysicalL2 := sobolevToL2_38 k (y j) with hu
  have hloc : ∀ n : ℤ, ∀ l ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |l - (n:ℝ) * Real.pi| ≤ K / japaneseBracket n := by
    intro n l hl
    have := hlocB (sobolevToH1_38 k hk (y j))
      ((norm_sobolevToH1_38_le k hk (y j)).trans (hj₂ j hjj₂)) n l
    rw [carrier_sobolevToH1_38] at this
    exact this hl
  have hfi : Integrable (momentDensity38 k u) := (fullMoment38 k hk hR3c (y j)).1
  have hf0 : ∀ x, 0 ≤ momentDensity38 k u x := momentDensity38_nonneg k u
  have hsu : SobolevSquareSummable (k:ℝ) (physicalFourier u) := sobolevToL2_38_sobolev k (y j)
  -- the restricted gap sets
  set s' : ℤ → Set ℝ := fun n => if (N0:ℤ) < |n|
    then Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) else ∅ with hs'
  have hm' : ∀ n, MeasurableSet (s' n) := by
    intro n; simp only [hs']; split_ifs
    · exact measurableSet_Icc
    · exact MeasurableSet.empty
  have hd' : Pairwise (Function.onFun Disjoint s') := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hxn hxm => hnm ?_
    have hxn' : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
      simp only [hs'] at hxn; split_ifs at hxn with h
      · exact hxn
      · exact absurd hxn (Set.notMem_empty x)
    have hxm' : x ∈ Icc (actualGapLowerAllE02_38 u m) (actualGapUpperAllE02_38 u m) := by
      simp only [hs'] at hxm; split_ifs at hxm with h
      · exact hxm
      · exact absurd hxm (Set.notMem_empty x)
    have e1 : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := by
      have : x ∈ actualGapLevelSetE02_38 u n := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]; exact hxn'
      exact this
    have e2 : actualQuasimomentumRealPartE02_38 u x = (m:ℝ) * Real.pi := by
      have : x ∈ actualGapLevelSetE02_38 u m := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u m).2]; exact hxm'
      exact this
    have : (n:ℝ) = m := mul_right_cancel₀ Real.pi_pos.ne' (e1.symm.trans e2)
    exact_mod_cast this
  have hsub : (⋃ n, s' n) ⊆ (Icc (-L) L)ᶜ := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    have hnN : (N0:ℤ) < |n| := by
      by_contra h
      simp only [hs', h, ite_false] at hxn
      exact Set.notMem_empty x hxn
    have hxI : x ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
      simp only [hs', hnN, ite_true] at hxn; exact hxn
    have h1 := hloc n x hxI
    have hjb := japaneseBracket_one_le n
    have h2 : |x - (n:ℝ) * Real.pi| ≤ K := h1.trans (div_le_self hK.le hjb)
    have hn1 : (N0:ℝ) + 1 ≤ |(n:ℝ)| := by
      have : (N0:ℤ) + 1 ≤ |n| := hnN
      have h' : ((N0:ℤ) + 1 : ℤ) ≤ |n| := this
      have := (Int.cast_le (R := ℝ)).mpr h'
      simpa [Int.cast_abs] using this
    have h3 : |(n:ℝ) * Real.pi| ≤ |x| + K := by
      have := abs_sub_abs_le_abs_sub ((n:ℝ) * Real.pi) x
      rw [abs_sub_comm] at this
      linarith
    rw [abs_mul, abs_of_pos hpi] at h3
    have h4 := Real.pi_gt_three
    have hN0' : (0:ℝ) ≤ N0 := Nat.cast_nonneg N0
    have h5 : L < |x| := by nlinarith [abs_nonneg (n:ℝ)]
    intro hxI'
    have := abs_le.mpr ⟨hxI'.1, hxI'.2⟩
    linarith
  have hU := hasSum_integral_iUnion hm' hd' hfi.integrableOn
  have hmono : ∫ x in ⋃ n, s' n, momentDensity38 k u x ≤ ∫ x in (Icc (-L) L)ᶜ, momentDensity38 k u x :=
    setIntegral_mono_set hfi.integrableOn (Eventually.of_forall hf0) hsub.eventuallyLE
  have hterm : ∀ n : ℤ, (if (N0:ℤ) < |n| then japaneseBracket n ^ (2*k) *
      actualGapActionAllE02_38 u n else 0) ≤ c * ∫ x in s' n, momentDensity38 k u x := by
    intro n
    by_cases hn : (N0:ℤ) < |n|
    · simp only [hn, ite_true, hs']
      exact bracket_action_le_setIntegral38 k u K hK hloc n
    · simp only [hn, ite_false, hs', Measure.restrict_empty, integral_zero_measure, mul_zero]
      exact le_rfl
  have hsum1 := summable_ite_bracket_action38 k hk u hsu N0
  calc ∑' n : ℤ, (if (N0:ℤ) < |n| then japaneseBracket n ^ (2*k) *
        actualGapActionAllE02_38 u n else 0)
      ≤ ∑' n : ℤ, c * ∫ x in s' n, momentDensity38 k u x :=
        Summable.tsum_le_tsum hterm hsum1 (hU.summable.mul_left c)
    _ = c * ∫ x in ⋃ n, s' n, momentDensity38 k u x := by rw [tsum_mul_left, hU.tsum_eq]
    _ ≤ c * ∫ x in (Icc (-L) L)ᶜ, momentDensity38 k u x := mul_le_mul_of_nonneg_left hmono hcpos.le
    _ ≤ c * (ε / c) := mul_le_mul_of_nonneg_left (hj₁ j hjj₁) hcpos.le
    _ = ε := by field_simp

/-- uniform weighted tails (the v2 sentence "weighted square tails are uniformly small") -/
theorem actionTails_uniform38 (m : ℕ) (hm : 2 ≤ m) (hR3c : NonlinRiccatiSmoothBound38 (m - 1))
    (y : ℕ → SobolevHilbert ((m - 1 : ℕ) : ℝ)) (yLim : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hy : Tendsto y atTop (𝓝 yLim)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∑' n : ℤ, (if (N:ℤ) < |n| then japaneseBracket n ^ (2*(m-1)) *
        actualGapActionAllE02_38 (sobolevToL2_38 (m-1) (y j)) n else 0) ≤ ε :=
  actionTails_uniform_aux38 (m - 1) (by omega) hR3c y yLim hy

/-! ## Fixed-gap continuity -/

theorem gapRemainderTerm_eq38 (W : ℝ → ℝ) (hW : Continuous W) (u : PhysicalL2) (n : ℤ) :
    gapRemainderTermE02_38 W u n =
      (2 / Real.pi) * (∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        W (2 * x) * actualGapHeightE02_38 u x) - W (2 * Real.pi * n) * actualGapActionAllE02_38 u n := by
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have h1 : IntervalIntegrable (fun x => W (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((hW.comp (continuous_const.mul continuous_id)).mul hvc).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => W (2 * Real.pi * n) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (continuous_const.mul hvc).intervalIntegrable _ _
  unfold gapRemainderTermE02_38 actualGapActionAllE02_38
  have : (fun x => (W (2 * x) - W (2 * Real.pi * n)) * actualGapHeightE02_38 u x) =
      fun x => W (2 * x) * actualGapHeightE02_38 u x -
        W (2 * Real.pi * n) * actualGapHeightE02_38 u x := by
    funext x; ring
  rw [this, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  ring

theorem continuous_finiteWeight38 (m : ℕ) (β : ℕ → ℝ) : Continuous (finiteWeightE02_38 m β) := by
  unfold finiteWeightE02_38
  fun_prop

theorem continuous_gapRemainderTerm38 (k : ℕ) (hk : 1 ≤ k) (W : ℝ → ℝ) (hW : Continuous W) (n : ℤ) :
    Continuous (fun y : SobolevHilbert (k : ℝ) =>
      gapRemainderTermE02_38 W (sobolevToL2_38 k y) n) := by
  have hc1 := (actualGapAction_continuous_E02_38 n W hW).comp (continuous_sobolevToH1_38 k hk)
  have hc2 := (actualGapAction_continuous_E02_38 n (fun _ => (1:ℝ)) continuous_const).comp
    (continuous_sobolevToH1_38 k hk)
  refine (hc1.sub (hc2.const_mul (W (2 * Real.pi * n)))).congr (fun y => ?_)
  simp only [Function.comp_apply, Pi.sub_apply, carrier_sobolevToH1_38]
  rw [gapRemainderTerm_eq38 W hW]
  unfold actualGapActionAllE02_38
  simp only [one_mul]

/-! ## Pointwise bound and tails of the remainder terms -/

theorem remainderBound38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ), ‖y‖ ≤ B → ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) y) n| ≤
        C * (japaneseBracket n ^ (2*(m-1)) *
          actualGapActionAllE02_38 (sobolevToL2_38 (m - 1) y) n) := by
  obtain ⟨C, hC, hb⟩ := gapRemainderTerm_le_action38 m hm β hβ B hB
  refine ⟨C, hC, fun y hy n => ?_⟩
  have := hb (sobolevToH1_38 (m - 1) (by omega) y)
    ((norm_sobolevToH1_38_le (m - 1) (by omega) y).trans hy) n
  rw [carrier_sobolevToH1_38] at this
  have he : 2 * m - 2 = 2 * (m - 1) := by omega
  rw [he] at this
  rw [← mul_assoc]
  exact this

theorem gapRemainder_summable38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ =>
      gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) y) n) := by
  obtain ⟨C, hC, hb⟩ := remainderBound38 m hm β hβ (max 1 ‖y‖) (le_max_left _ _)
  refine Summable.of_norm_bounded
    ((summable_bracket_action38 (m - 1) (by omega) (sobolevToL2_38 (m - 1) y)
      (sobolevToL2_38_sobolev (m - 1) y)).mul_left C) (fun n => ?_)
  rw [Real.norm_eq_abs]
  exact hb y (le_max_right _ _) n

theorem remainderTails_uniform38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (hR3c : NonlinRiccatiSmoothBound38 (m - 1))
    (y : ℕ → SobolevHilbert ((m - 1 : ℕ) : ℝ)) (yLim : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hy : Tendsto y atTop (𝓝 yLim)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∑' n : ℤ, (if (N:ℤ) < |n| then
        |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) (y j)) n| else 0) ≤ ε := by
  intro ε hε
  have hk : 1 ≤ m - 1 := by omega
  set B : ℝ := ‖yLim‖ + 1 with hB
  have hB1 : 1 ≤ B := by have := norm_nonneg yLim; linarith
  obtain ⟨C, hC, hb⟩ := remainderBound38 m hm β hβ B hB1
  have hev : ∀ᶠ j in atTop, ‖y j‖ ≤ B :=
    (hy.norm.eventually (gt_mem_nhds (by linarith : ‖yLim‖ < B))).mono fun j h => h.le
  obtain ⟨j₂, hj₂⟩ := eventually_atTop.mp hev
  obtain ⟨N, j₁, hN⟩ := actionTails_uniform38 m hm hR3c y yLim hy (ε / (C + 1)) (by positivity)
  refine ⟨N, max j₁ j₂, fun j hj => ?_⟩
  have hjj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hjj₂ : j₂ ≤ j := le_trans (le_max_right _ _) hj
  have hs := summable_ite_bracket_action38 (m - 1) hk (sobolevToL2_38 (m - 1) (y j))
    (sobolevToL2_38_sobolev (m - 1) (y j)) N
  have hpt : ∀ n : ℤ, (if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) (y j)) n| else 0) ≤
      C * (if (N:ℤ) < |n| then japaneseBracket n ^ (2*(m-1)) *
        actualGapActionAllE02_38 (sobolevToL2_38 (m - 1) (y j)) n else 0) := by
    intro n
    split_ifs
    · exact hb (y j) (hj₂ j hjj₂) n
    · simp
  have hnn : ∀ n : ℤ, 0 ≤ (if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) (y j)) n| else 0) := by
    intro n; split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hsum : Summable (fun n : ℤ => if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) (y j)) n| else 0) :=
    Summable.of_nonneg_of_le hnn hpt (hs.mul_left C)
  calc _ ≤ ∑' n : ℤ, C * (if (N:ℤ) < |n| then japaneseBracket n ^ (2*(m-1)) *
        actualGapActionAllE02_38 (sobolevToL2_38 (m - 1) (y j)) n else 0) :=
        Summable.tsum_le_tsum hpt hsum (hs.mul_left C)
    _ = C * ∑' n : ℤ, (if (N:ℤ) < |n| then japaneseBracket n ^ (2*(m-1)) *
        actualGapActionAllE02_38 (sobolevToL2_38 (m - 1) (y j)) n else 0) := tsum_mul_left
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (hN j hjj₁) hC
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- F04.04 (B:lem:spectral, continuity), conditional on R3c at k = m - 1. -/
theorem spectralRemainder_continuous38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (hR3c : NonlinRiccatiSmoothBound38 (m - 1)) :
    Continuous (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) =>
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) y) n) := by
  have hk : 1 ≤ m - 1 := by omega
  rw [continuous_iff_seqContinuous]
  intro y yLim hy
  refine tendsto_tsum_of_uniform_tails38
    (fun j n => gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) (y j)) n)
    (fun n => gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) yLim) n)
    (fun j => gapRemainder_summable38 m hm β hβ (y j))
    (gapRemainder_summable38 m hm β hβ yLim) ?_
    (remainderTails_uniform38 m hm β hβ hR3c y yLim hy) ?_
  · intro n
    exact ((continuous_gapRemainderTerm38 (m - 1) hk _ (continuous_finiteWeight38 m β) n).tendsto
      yLim).comp hy
  · intro ε hε
    obtain ⟨N, j₀, h⟩ := remainderTails_uniform38 m hm β hβ hR3c (fun _ => yLim) yLim
      tendsto_const_nhds ε hε
    exact ⟨N, h j₀ le_rfl⟩

end NlsGge.SpectralFoundations
end
