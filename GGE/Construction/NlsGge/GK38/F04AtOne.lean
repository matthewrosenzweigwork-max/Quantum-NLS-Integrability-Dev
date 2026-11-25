import NlsGge.GK38.MolnarMoments
import NlsGge.Spectral.F04Continuity38

/-!
# H0a: the `m = 1` versions of the F04-type results (no S7)

Piece H0 of the E01 plan (`campaign/E01_PLAN.md` section 6.13, rev. 4.1), the part that does not need
the `L^2` continuity of the gap endpoints (S7).  The repository has the F04-type results only for
`2 ≤ m`: `gapRemainderTerm_le_action38`, `spectralRemainder_F04_E02_38`,
`spectralRemainder_continuous_all38`, `energyIdentity_spectral_all38`.  Here:

* `gapRemainderTerm_le_action38_of_one_le`: `gapRemainderTerm_le_action38` with `2 ≤ m` weakened to
  `1 ≤ m` (same proof; `2 ≤ m` was used only to factor `⟨n⟩^{2m} = ⟨n⟩^{2m-2}⟨n⟩^2`);
* `gapRemainderTerm_le_action_one`: its `m = 1` instance, `|term_n| ≤ C I_n` on `H^1` balls;
* `weightedAction_summable_one`: `Σ W_1(2πn) I_n` converges on `H^1`;
* `spectralRemainder_one_nonneg_summable`: `Σ |term_n| < ∞` and `R_1 ≥ 0`;
* `energyIdentity_one`: `E_1(y) = Σ W_1(2πn) I_n + R_1(y)` on `H^1`;
* `spectralRemainder_one_continuous`: `R_1` is continuous on `H^1` (tails argument as in
  `actionTails_uniform_aux38` at `k = 1`; no `L^2` continuity of the endpoints is needed).

Deviation from the plan text: the Sobolev index is written `((1 : ℕ) : ℝ)` (the form the
repository's `sobolevToL2_38 1`, `energySobolev38 1` and `SobolevHilbert ((m : ℕ) : ℝ)` use), and the
positivity hypothesis is `hβ : 0 < β 0 ∧ 0 < β 1` as in the plan.  The sequence statement
`spectralRemainder_one_tendsto` is H0b and is not here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Topology Interval

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38

noncomputable section

/-- `gapRemainderTerm_le_action38` for `1 ≤ m`: `|term_n| ≤ C ⟨n⟩^{2m-2} I_n` on `H^1` balls. -/
theorem gapRemainderTerm_le_action38_of_one_le (m : ℕ) (hm : 1 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : WeightedHilbert (sobolevModeWeight (1:ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (physicalH1ComplexCarrierToL2Actual22 w) n| ≤
        C * japaneseBracket n ^ (2*m-2) *
          actualGapActionAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n := by
  have hβ0 : ∀ j ≤ m, 0 ≤ β j := fun j hj => (hβ j hj).le
  obtain ⟨C₂, hC₂, hC₂b⟩ := finiteWeight_gap_rel_le38 m β hβ B hB
  set c₃ : ℝ := ∑ j ∈ Finset.range (m + 1), β j * (2 * Real.pi)^(2*j) with hc₃
  have hc₃nn : 0 ≤ c₃ := Finset.sum_nonneg fun j hj => mul_nonneg (hβ0 j (by simp at hj; omega))
    (by positivity)
  refine ⟨C₂ * c₃, by positivity, fun w hw n => ?_⟩
  set u := physicalH1ComplexCarrierToL2Actual22 w with hu
  have hjb := japaneseBracket_pos n
  have hjb1 := japaneseBracket_one_le n
  set a : ℝ := finiteWeightE02_38 m β (2*Real.pi*n) with ha
  have ha_le : a ≤ c₃ * japaneseBracket n ^ (2*m) := finiteWeight_le_bracket_pow38 m β hβ0 n
  have hann : 0 ≤ a := finiteWeight_nonneg38 m β hβ0 _
  have hpow : japaneseBracket n ^ (2*m) = japaneseBracket n ^ (2*m-2) * japaneseBracket n ^ 2 := by
    rw [← pow_add]; congr 1; omega
  -- the sup bound `C₂ a / ⟨n⟩² ≤ C₂ c₃ ⟨n⟩^{2m-2}`
  have hsup : C₂ * a / japaneseBracket n ^ 2 ≤ C₂ * c₃ * japaneseBracket n ^ (2*m-2) := by
    rw [div_le_iff₀ (by positivity)]
    calc C₂ * a ≤ C₂ * (c₃ * japaneseBracket n ^ (2*m)) := mul_le_mul_of_nonneg_left ha_le hC₂
      _ = _ := by rw [hpow]; ring
  have hab := actualGapLower_le_upper_F04_38 u n
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hII : IntervalIntegrable (actualGapHeightE02_38 u) volume (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n) := hvc.intervalIntegrable _ _
  have hbd : ‖∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (finiteWeightE02_38 m β (2*x) - a) * actualGapHeightE02_38 u x‖ ≤
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (C₂ * a / japaneseBracket n ^ 2) * actualGapHeightE02_38 u x := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun x hx => ?_) (hII.const_mul _)
    have hxI : x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
      ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (actualGapHeightE02_38_nonneg u x)]
    exact mul_le_mul_of_nonneg_right (hC₂b w hw n x hxI) (actualGapHeightE02_38_nonneg u x)
  unfold gapRemainderTermE02_38
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / Real.pi)]
  have h1 : (2 / Real.pi) * |∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (finiteWeightE02_38 m β (2*x) - a) * actualGapHeightE02_38 u x| ≤
      (2 / Real.pi) * ((C₂ * a / japaneseBracket n ^ 2) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← intervalIntegral.integral_const_mul]
    simpa [Real.norm_eq_abs] using hbd
  have hIn : actualGapActionAllE02_38 u n = (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x := rfl
  have hI0 := actualGapAction_nonneg_F04_38 u n
  calc _ ≤ (2 / Real.pi) * ((C₂ * a / japaneseBracket n ^ 2) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x) := h1
    _ = (C₂ * a / japaneseBracket n ^ 2) * actualGapActionAllE02_38 u n := by rw [hIn]; ring
    _ ≤ (C₂ * c₃ * japaneseBracket n ^ (2*m-2)) * actualGapActionAllE02_38 u n :=
        mul_le_mul_of_nonneg_right hsup hI0


/-- **H0, bound at `m = 1`.** With `W_1(r) = β₀ + β₁ r²`, on every `H^1` ball of radius `B ≥ 1`
there is a constant `C ≥ 0` with `|R_{1,n}(w)| ≤ C I_n(w)` for all gaps `n`
(`⟨n⟩^{2m-2} = 1`). -/
theorem gapRemainderTerm_le_action_one (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : WeightedHilbert (sobolevModeWeight (1:ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (physicalH1ComplexCarrierToL2Actual22 w) n| ≤
        C * actualGapActionAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n := by
  obtain ⟨C, hC, hb⟩ := gapRemainderTerm_le_action38_of_one_le 1 le_rfl β
    (fun j hj => by
      interval_cases j
      · exact hβ.1
      · exact hβ.2) B hB
  refine ⟨C, hC, fun w hw n => ?_⟩
  have := hb w hw n
  simpa using this

/-- `W_1 = β₀ + β₁ r²` in closed form. -/
theorem finiteWeight_one_eq38 (β : ℕ → ℝ) :
    finiteWeightE02_38 1 β = fun r => β 0 + β 1 * r ^ 2 := by
  funext r; simp [finiteWeightE02_38, Finset.sum_range_succ]

/-- **H0, summability of the weighted action at `m = 1`:** `Σ_n W_1(2πn) I_n(u) < ∞` for `u ∈ H^1`. -/
theorem weightedAction_summable_one (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => finiteWeightE02_38 1 β (2 * Real.pi * n) * actualGapActionAllE02_38 u n) := by
  have hβ' : ∀ j ≤ 1, 0 < β j := fun j hj => by
    interval_cases j
    · exact hβ.1
    · exact hβ.2
  have hs := summable_bracket_action38 1 le_rfl u (by exact_mod_cast hu)
  refine (hs.mul_left (∑ j ∈ Finset.range (1 + 1), β j * (2 * Real.pi)^(2*j))).of_nonneg_of_le
    (fun n => mul_nonneg (finiteWeight_nonneg38 1 β (fun j hj => (hβ' j hj).le) _)
      (actualGapAction_nonneg_F04_38 u n)) (fun n => ?_)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (finiteWeight_le_bracket_pow38 1 β (fun j hj => (hβ' j hj).le) n)
    (actualGapAction_nonneg_F04_38 u n)

/-- **H0, `R_1 ≥ 0` with absolute convergence** (the `m = 1` analogue of
`spectralRemainder_F04_E02_38`; `H^1 = H^{m}`, not `H^{m-1}`: the remainder needs `u ∈ H^1`). -/
theorem spectralRemainder_one_nonneg_summable (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) u n|) ∧
    0 ≤ ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 1 β) u n := by
  have h0 := hβ.1
  have h1 := hβ.2
  have hW := finiteWeight_one_eq38 β
  refine gapRemainder_F04_E02_38 _ 1 (2 * β 1) u ⟨?_, ?_, le_rfl, by positivity, ?_, by exact_mod_cast hu⟩
  · rw [hW]; exact contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2))
  · rw [hW]
    have := ((even_two_mul 1).convexOn_pow).smul h1.le
    have h2 := (convexOn_const (β 0) convex_univ).add this
    convert h2 using 1
  · intro y
    rw [hW]
    have : deriv (fun r : ℝ => β 0 + β 1 * r ^ 2) y = 2 * β 1 * y := by
      have := ((hasDerivAt_pow 2 y).const_mul (β 1)).const_add (β 0)
      rw [this.deriv]; simp; ring
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * β 1)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    show |y| ≤ 1 + |y| ^ 3
    have ha := abs_nonneg y
    rcases le_total |y| 1 with hy | hy <;>
      nlinarith [pow_nonneg ha 3, mul_nonneg ha ha, mul_nonneg (mul_nonneg ha ha) ha]

/-- **H0, the spectral energy identity at `m = 1`** (the `m = 1` analogue of
`energyIdentity_spectral_all38`): for `y ∈ H^1`,
`E_1(y) = Σ_n W_1(2πn) I_n + R_1`, both series being summable (proved above) so the `tsum`s are
the honest sums. -/
theorem energyIdentity_one (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1) (y : SobolevHilbert ((1:ℕ):ℝ)) :
    energySobolev38 1 β y =
      ∑' n : ℤ, finiteWeightE02_38 1 β (2 * Real.pi * (n : ℝ)) *
          actualGapActionAllE02_38 ((sobolevToL2_38 1) y) n +
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 1 β) ((sobolevToL2_38 1) y) n := by
  have hβ' : ∀ j ≤ 1, 0 < β j := fun j hj => by
    interval_cases j
    · exact hβ.1
    · exact hβ.2
  have hu : SobolevSquareSummable 1 (physicalFourier (sobolevToL2_38 1 y)) := by
    simpa using sobolevToL2_38_sobolev 1 y
  have hs1 := weightedAction_summable_one β hβ _ hu
  have hs2 := (spectralRemainder_one_nonneg_summable β hβ _ hu).1.of_abs
  exact (weightedMomentSum_split38 1 le_rfl β y).unique (hs1.hasSum.add hs2.hasSum)

/-! ## Continuity of `R_1` on `H^1` -/

/-- The bound `|R_{1,n}| ≤ C I_n` transported to `y ∈ H^1` (Sobolev carrier). -/
theorem remainderBound_one38 (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : SobolevHilbert ((1:ℕ):ℝ), ‖y‖ ≤ B → ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 y) n| ≤
        C * actualGapActionAllE02_38 (sobolevToL2_38 1 y) n := by
  obtain ⟨C, hC, hb⟩ := gapRemainderTerm_le_action_one β hβ B hB
  refine ⟨C, hC, fun y hy n => ?_⟩
  have := hb (sobolevToH1_38 1 le_rfl y) ((norm_sobolevToH1_38_le 1 le_rfl y).trans hy) n
  rwa [carrier_sobolevToH1_38] at this

/-- Uniform tails of `|R_{1,n}|` along an `H^1`-convergent sequence: dominated by `C I_n ≤ C ⟨n⟩² I_n`
and `actionTails_uniform_aux38` at `k = 1`. -/
theorem remainderTails_uniform_one38 (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1)
    (y : ℕ → SobolevHilbert ((1:ℕ):ℝ)) (yLim : SobolevHilbert ((1:ℕ):ℝ))
    (hy : Tendsto y atTop (𝓝 yLim)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∑' n : ℤ, (if (N:ℤ) < |n| then
        |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 (y j)) n| else 0) ≤ ε := by
  intro ε hε
  set B : ℝ := ‖yLim‖ + 1 with hB
  have hB1 : 1 ≤ B := by have := norm_nonneg yLim; linarith
  obtain ⟨C, hC, hb⟩ := remainderBound_one38 β hβ B hB1
  have hev : ∀ᶠ j in atTop, ‖y j‖ ≤ B :=
    (hy.norm.eventually (gt_mem_nhds (by linarith : ‖yLim‖ < B))).mono fun j h => h.le
  obtain ⟨j₂, hj₂⟩ := eventually_atTop.mp hev
  obtain ⟨N, j₁, hN⟩ := actionTails_uniform_aux38 1 le_rfl (nonlinRiccatiSmoothBound38_all 1 le_rfl)
    y yLim hy (ε / (C + 1)) (by positivity)
  refine ⟨N, max j₁ j₂, fun j hj => ?_⟩
  have hjj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hjj₂ : j₂ ≤ j := le_trans (le_max_right _ _) hj
  have hs := summable_ite_bracket_action38 1 le_rfl (sobolevToL2_38 1 (y j))
    (sobolevToL2_38_sobolev 1 (y j)) N
  have hpt : ∀ n : ℤ, (if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 (y j)) n| else 0) ≤
      C * (if (N:ℤ) < |n| then japaneseBracket n ^ (2*1) *
        actualGapActionAllE02_38 (sobolevToL2_38 1 (y j)) n else 0) := by
    intro n
    split_ifs
    · have h1 := hb (y j) (hj₂ j hjj₂) n
      have h2 := actualGapAction_nonneg_F04_38 (sobolevToL2_38 1 (y j)) n
      have h3 : (1:ℝ) ≤ japaneseBracket n ^ (2*1) := one_le_pow₀ (japaneseBracket_one_le n)
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h2 h3) hC
    · simp
  have hnn : ∀ n : ℤ, 0 ≤ (if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 (y j)) n| else 0) := by
    intro n; split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hsum : Summable (fun n : ℤ => if (N:ℤ) < |n| then
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 (y j)) n| else 0) :=
    Summable.of_nonneg_of_le hnn hpt (hs.mul_left C)
  calc _ ≤ ∑' n : ℤ, C * (if (N:ℤ) < |n| then japaneseBracket n ^ (2*1) *
        actualGapActionAllE02_38 (sobolevToL2_38 1 (y j)) n else 0) :=
        Summable.tsum_le_tsum hpt hsum (hs.mul_left C)
    _ = C * ∑' n : ℤ, (if (N:ℤ) < |n| then japaneseBracket n ^ (2*1) *
        actualGapActionAllE02_38 (sobolevToL2_38 1 (y j)) n else 0) := tsum_mul_left
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (hN j hjj₁) hC
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

/-- **H0, continuity of `R_1` on `H^1`** (the `m = 1` analogue of `spectralRemainder_continuous_all38`).
Tannery with uniformly small tails: each term is continuous on `H^1` (`continuous_gapRemainderTerm38`),
the tails are uniformly small by `actionTails_uniform_aux38` at `k = 1`.  Only `H^1` convergence is
used; the stronger statement for `H^1`-bounded, `L^2`-convergent sequences is H0b. -/
theorem spectralRemainder_one_continuous (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1) :
    Continuous fun y : SobolevHilbert ((1:ℕ):ℝ) =>
      ∑' n : ℤ, gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 y) n := by
  rw [continuous_iff_seqContinuous]
  intro y yLim hy
  have hsum : ∀ z : SobolevHilbert ((1:ℕ):ℝ), Summable
      (fun n : ℤ => gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 z) n) :=
    fun z => (spectralRemainder_one_nonneg_summable β hβ _
      (by simpa using sobolevToL2_38_sobolev 1 z)).1.of_abs
  refine tendsto_tsum_of_uniform_tails38
    (fun j n => gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 (y j)) n)
    (fun n => gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (sobolevToL2_38 1 yLim) n)
    (fun j => hsum (y j)) (hsum yLim) ?_ (remainderTails_uniform_one38 β hβ y yLim hy) ?_
  · intro n
    exact ((continuous_gapRemainderTerm38 1 le_rfl _ (continuous_finiteWeight38 1 β) n).tendsto
      yLim).comp hy
  · intro ε hε
    obtain ⟨N, j₀, h⟩ := remainderTails_uniform_one38 β hβ (fun _ => yLim) yLim
      tendsto_const_nhds ε hε
    exact ⟨N, h j₀ le_rfl⟩

end

end NlsGge.GK38
