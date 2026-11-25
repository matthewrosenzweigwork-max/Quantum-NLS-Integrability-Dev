import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB13Local

/-! # Track B: approved contract 17 `continuous_l2Flow`

Statement copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).
* `l2Flow_neg`: time reversal `l2Flow (-t) a = conj (l2Flow t (conj a))` (`isDuhSol_rev`, `duh_unique`);
* `flow_lip_iter`: Lipschitz bound `L^n` on `[0, nδ]` for data of norm `≤ M` (local Lipschitz bound of
  `PdeB13Local` on `[0,δ]`, group law (contract 15) and mass conservation (contract 16));
* `flow_lip_sym`: the same on `[-nδ, nδ]` (time reversal);
* contract 17: joint continuity from the locally uniform Lipschitz bound and continuity in time
  (contract 12).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

open Filter Topology

/-- Time reversal of the flow. -/
theorem l2Flow_neg (t : ℝ) (a : PhysicalL2) : l2Flow (-t) a = conjL2 (l2Flow t (conjL2 a)) := by
  have h0 : (fun s => l2Flow s a) 0 = revL2 (fun s => l2Flow s (conjL2 a)) 0 := by
    simp only [revL2, neg_zero, (l2Flow_solution _).2, conjL2_conjL2]
  have h := duh_unique (isDuhSol_l2Flow a) (isDuhSol_rev (isDuhSol_l2Flow (conjL2 a))) h0
  have := congrFun h (-t)
  simp only [revL2, neg_neg] at this
  exact this

theorem flow_lip_iter (M : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, 1 ≤ L ∧ ∀ n : ℕ, ∀ a b : PhysicalL2,
    ‖a‖ ≤ M → ‖b‖ ≤ M → ∀ t ∈ Set.Icc 0 (n * δ),
      ‖l2Flow t a - l2Flow t b‖ ≤ L ^ n * ‖a - b‖ := by
  obtain ⟨δ, R, Kd, Cf, D⟩ := locData_exists M
  refine ⟨δ, D.hδ, 1 + Cf, by linarith [D.hCf], fun n => ?_⟩
  induction n with
  | zero =>
    intro a b _ _ t ht
    have ht0 : t = 0 := by
      have := ht.2; simp only [Nat.cast_zero, zero_mul] at this; exact le_antisymm this ht.1
    rw [ht0, (l2Flow_solution a).2, (l2Flow_solution b).2, pow_zero, one_mul]
  | succ n ih =>
    intro a b ha hb t ht
    have hL : 1 ≤ 1 + Cf := by linarith [D.hCf]
    rcases le_total t (n * δ) with htn | htn
    · refine (ih a b ha hb t ⟨ht.1, htn⟩).trans ?_
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (Nat.le_succ n)) (norm_nonneg _)
    · have hs : t - n * δ ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith, by
        have := ht.2; push_cast at this; linarith⟩
      have e : ∀ c : PhysicalL2, l2Flow t c = l2Flow (t - n * δ) (l2Flow (n * δ) c) := fun c => by
        rw [← l2Flow_add, sub_add_cancel]
      rw [e a, e b]
      have h1 := D.l2Flow_lip (a := l2Flow (n * δ) a) (b := l2Flow (n * δ) b) (by rw [l2Flow_norm]; exact ha) (by rw [l2Flow_norm]; exact hb)
        ⟨t - n * δ, hs⟩
      have h2 := ih a b ha hb (n * δ) ⟨by have := D.hδ.le; positivity, le_rfl⟩
      calc ‖l2Flow (t - n * δ) (l2Flow (n * δ) a) - l2Flow (t - n * δ) (l2Flow (n * δ) b)‖
          ≤ (1 + Cf) * ‖l2Flow (n * δ) a - l2Flow (n * δ) b‖ := h1
        _ ≤ (1 + Cf) * ((1 + Cf) ^ n * ‖a - b‖) :=
            mul_le_mul_of_nonneg_left h2 (by linarith [D.hCf])
        _ = (1 + Cf) ^ (n + 1) * ‖a - b‖ := by ring

theorem flow_lip_sym (M : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ, ∀ n : ℕ, ∀ a b : PhysicalL2,
    ‖a‖ ≤ M → ‖b‖ ≤ M → ∀ t : ℝ, |t| ≤ n * δ →
      ‖l2Flow t a - l2Flow t b‖ ≤ L ^ n * ‖a - b‖ := by
  obtain ⟨δ, hδ, L, -, h⟩ := flow_lip_iter M
  refine ⟨δ, hδ, L, fun n a b ha hb t ht => ?_⟩
  rcases le_total 0 t with h0 | h0
  · exact h n a b ha hb t ⟨h0, (le_abs_self t).trans ht⟩
  · obtain ⟨s, rfl⟩ : ∃ s : ℝ, t = -s := ⟨-t, (neg_neg t).symm⟩
    rw [l2Flow_neg, l2Flow_neg, conjL2_sub, norm_conjL2]
    rw [abs_neg] at ht
    have h1 := h n (conjL2 a) (conjL2 b) (by rw [norm_conjL2]; exact ha)
      (by rw [norm_conjL2]; exact hb) s ⟨by linarith, (le_abs_self s).trans ht⟩
    rwa [conjL2_sub, norm_conjL2] at h1

/-! ### Approved contract 17 -/

theorem continuous_l2Flow : Continuous fun p : ℝ × PhysicalL2 => l2Flow p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, a₀⟩
  obtain ⟨δ, hδ, L, hlip⟩ := flow_lip_sym (‖a₀‖ + 1)
  obtain ⟨n, hn⟩ := exists_nat_gt ((|t₀| + 1) / δ)
  rw [div_lt_iff₀ hδ] at hn
  have h1 : ∀ᶠ p : ℝ × PhysicalL2 in 𝓝 (t₀, a₀), |p.1| < |t₀| + 1 :=
    (isOpen_lt continuous_fst.abs continuous_const).mem_nhds (by simp)
  have h2 : ∀ᶠ p : ℝ × PhysicalL2 in 𝓝 (t₀, a₀), ‖p.2‖ < ‖a₀‖ + 1 :=
    (isOpen_lt continuous_snd.norm continuous_const).mem_nhds (by simp)
  have hev : ∀ᶠ p : ℝ × PhysicalL2 in 𝓝 (t₀, a₀),
      ‖l2Flow p.1 p.2 - l2Flow p.1 a₀‖ ≤ L ^ n * ‖p.2 - a₀‖ := by
    filter_upwards [h1, h2] with p hp1 hp2
    exact hlip n p.2 a₀ hp2.le (by linarith) p.1 (by linarith)
  have hlim : Tendsto (fun p : ℝ × PhysicalL2 => l2Flow p.1 p.2 - l2Flow p.1 a₀) (𝓝 (t₀, a₀))
      (𝓝 0) := by
    refine squeeze_zero_norm' hev ?_
    have hc : Continuous fun p : ℝ × PhysicalL2 => L ^ n * ‖p.2 - a₀‖ :=
      continuous_const.mul (continuous_snd.sub continuous_const).norm
    have := hc.tendsto (t₀, a₀)
    simpa only [sub_self, norm_zero, mul_zero] using this
  have hc : Tendsto (fun p : ℝ × PhysicalL2 => l2Flow p.1 a₀) (𝓝 (t₀, a₀)) (𝓝 (l2Flow t₀ a₀)) :=
    (((l2Flow_solution a₀).1.1).comp continuous_fst).tendsto (t₀, a₀)
  have := hlim.add hc
  simp only [sub_add_cancel, zero_add] at this
  exact this

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
