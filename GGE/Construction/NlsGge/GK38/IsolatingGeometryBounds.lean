import NlsGge.GK38.IsolatingDistance

/-! Quantitative all-integer separation from strict closure separation and
exact lattice tails. Finite exceptional and mixed pairs are bounded explicitly. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem isolating_finite_pos_lower38 {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ a : ℝ, 0 < a ∧ ∀ i ∈ S, a ≤ f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨a, ha, haf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min a (f i), lt_min ha (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (haf j hj)

theorem isolating_deviation_bound38 (C : ℤ → ℂ) (R : ℤ → ℝ) (N : ℕ)
    (hTail : ∀ n : ℤ, (N : ℤ) < |n| → C n = countingCenter38 n ∧ R n = Real.pi / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℤ, ‖C n - countingCenter38 n‖ + R n ≤ K := by
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hfin : ((fun n : ℤ => ‖C n - countingCenter38 n‖ + R n) '' (S : Set ℤ)).Finite :=
    S.finite_toSet.image _
  obtain ⟨K₀, hK₀⟩ := hfin.bddAbove
  let K : ℝ := max K₀ (Real.pi / 4) + 1
  have hK : 0 < K := by dsimp [K]; nlinarith [le_max_right K₀ (Real.pi / 4), Real.pi_pos]
  refine ⟨K, hK, fun n => ?_⟩
  by_cases hn : |n| ≤ (N : ℤ)
  · have hnS : n ∈ S := Finset.mem_Icc.mpr (abs_le.mp hn)
    have hh : ‖C n - countingCenter38 n‖ + R n ≤ K₀ := hK₀ ⟨n, hnS, rfl⟩
    dsimp [K]
    linarith [le_max_left K₀ (Real.pi / 4)]
  · obtain ⟨hc, hr⟩ := hTail n (lt_of_not_ge hn)
    rw [hc, hr, sub_self, norm_zero, zero_add]
    dsimp [K]
    linarith [le_max_right K₀ (Real.pi / 4)]

theorem isolating_lattice_dist38 (m n : ℤ) :
    dist (countingCenter38 m) (countingCenter38 n) = Real.pi * |((m - n : ℤ) : ℝ)| := by
  rw [dist_eq_norm, countingCenter_sub38, norm_countingCenter38, mul_comm]

theorem isolating_distance_positive38 (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ n : ℤ, 0 < R n)
    (hsep : ∀ m n : ℤ, m ≠ n → R m + R n < dist (C m) (C n))
    (m n : ℤ) (hmn : m ≠ n) : 0 < ballDistance38 (C m) (C n) (R m) (R n) := by
  rw [ballDistance38_eq _ _ (hR m) (hR n), max_eq_right (by linarith [hsep m n hmn])]
  linarith [hsep m n hmn]

theorem isolating_distance_deviation38 (C : ℤ → ℂ) (R : ℤ → ℝ) (K : ℝ)
    (hR : ∀ n : ℤ, 0 < R n)
    (hK : ∀ n : ℤ, ‖C n - countingCenter38 n‖ + R n ≤ K)
    (m n : ℤ) :
    Real.pi * |((m - n : ℤ) : ℝ)| - 2 * K ≤ ballDistance38 (C m) (C n) (R m) (R n) ∧
      ballDistance38 (C m) (C n) (R m) (R n) ≤ Real.pi * |((m - n : ℤ) : ℝ)| + 2 * K := by
  constructor
  · have ht := dist_triangle4 (countingCenter38 m) (C m) (C n) (countingCenter38 n)
    rw [isolating_lattice_dist38] at ht
    have hl := (le_max_right 0 (dist (C m) (C n) - R m - R n)).trans
      (ballDistance38_lower (C m) (C n) (hR m) (hR n))
    have hem : dist (countingCenter38 m) (C m) = ‖C m - countingCenter38 m‖ := by
      rw [dist_comm, dist_eq_norm]
    have hen : dist (C n) (countingCenter38 n) = ‖C n - countingCenter38 n‖ := dist_eq_norm _ _
    rw [hem, hen] at ht
    nlinarith [hK m, hK n]
  · have ht := dist_triangle4 (C m) (countingCenter38 m) (countingCenter38 n) (C n)
    have hem : dist (C m) (countingCenter38 m) = ‖C m - countingCenter38 m‖ := dist_eq_norm _ _
    rw [isolating_lattice_dist38, hem] at ht
    have hen : dist (countingCenter38 n) (C n) = ‖C n - countingCenter38 n‖ := by
      rw [dist_comm, dist_eq_norm]
    rw [hen] at ht
    have hl := ballDistance38_le_pair (C m) (C n) (R m) (R n)
      (mem_ball_self (hR m)) (mem_ball_self (hR n))
    nlinarith [hK m, hK n, hR m, hR n]

theorem isolating_tail_distance38 (m n : ℤ) (hmn : m ≠ n) :
    ballDistance38 (countingCenter38 m) (countingCenter38 n) (Real.pi / 4) (Real.pi / 4) =
      Real.pi * |((m - n : ℤ) : ℝ)| - Real.pi / 2 := by
  have hD : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    exact_mod_cast ((show (1 : ℤ) ≤ |m - n| from by have hp := abs_pos.mpr (sub_ne_zero.mpr hmn); omega))
  rw [ballDistance38_eq _ _ (by positivity) (by positivity), isolating_lattice_dist38]
  rw [max_eq_right (by nlinarith [Real.pi_pos])]
  ring

theorem tail_comparable_geometry38 (C : ℤ → ℂ) (R : ℤ → ℝ) (N : ℕ)
    (hCR : ∀ n : ℤ, 0 < R n ∧ (C n).im = 0)
    (hmono : StrictMono (fun n => (C n).re))
    (hsep : ∀ m n : ℤ, m ≠ n → R m + R n < dist (C m) (C n))
    (hTail : ∀ n : ℤ, (N : ℤ) < |n| → C n = countingCenter38 n ∧ R n = Real.pi / 4) :
    ∃ c : ℝ, IsolatingGeometry38 C R c N := by
  have hR : ∀ n : ℤ, 0 < R n := fun n => (hCR n).1
  obtain ⟨K, hK, hdev⟩ := isolating_deviation_bound38 C R N hTail
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * K / Real.pi)
  have hMπ : 4 * K < (M : ℝ) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp hM
  let B : ℕ := N + M
  let E : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ Finset.Icc (-(B : ℤ)) (B : ℤ)).filter (fun p => p.1 ≠ p.2)
  let F : ℤ × ℤ → ℝ := fun p => ballDistance38 (C p.1) (C p.2) (R p.1) (R p.2) /
    |((p.1 - p.2 : ℤ) : ℝ)|
  have hF : ∀ p ∈ E, 0 < F p := by
    intro p hp
    have hne := (Finset.mem_filter.mp hp).2
    have hD : 0 < |((p.1 - p.2 : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hne)
    exact div_pos (isolating_distance_positive38 C R hR hsep p.1 p.2 hne) hD
  obtain ⟨a, ha, haF⟩ := isolating_finite_pos_lower38 E F hF
  let γ : ℝ := min a (Real.pi / 2)
  have hγ : 0 < γ := lt_min ha (by positivity)
  have hlinear : ∀ m n : ℤ, m ≠ n → γ * |((m - n : ℤ) : ℝ)| ≤
      ballDistance38 (C m) (C n) (R m) (R n) := by
    intro m n hmn
    let D : ℝ := |((m - n : ℤ) : ℝ)|
    have hD : (1 : ℝ) ≤ D := by
      dsimp [D]
      exact_mod_cast (show (1 : ℤ) ≤ |m - n| from by have hp := abs_pos.mpr (sub_ne_zero.mpr hmn); omega)
    have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
    have hγπ : γ ≤ Real.pi / 2 := min_le_right _ _
    by_cases hlarge : 4 * K ≤ Real.pi * D
    · have hl := (isolating_distance_deviation38 C R K hR hdev m n).1
      nlinarith
    · by_cases htails : (N : ℤ) < |m| ∧ (N : ℤ) < |n|
      · obtain ⟨hcm, hrm⟩ := hTail m htails.1
        obtain ⟨hcn, hrn⟩ := hTail n htails.2
        rw [hcm, hrm, hcn, hrn, isolating_tail_distance38 m n hmn]
        nlinarith [Real.pi_pos]
      · have hsmall : |m - n| ≤ (M : ℤ) := by
          have hDr : D < (M : ℝ) := by nlinarith [Real.pi_pos]
          have hcast : (|(m - n : ℤ)| : ℝ) < (M : ℝ) := by simpa only [Int.cast_abs] using hDr
          exact_mod_cast hcast.le
        have hmB : |m| ≤ (B : ℤ) ∧ |n| ≤ (B : ℤ) := by
          have hmnabs : |m| ≤ |n| + |m - n| := by
            calc |m| = |n + (m - n)| := by congr 1; ring
              _ ≤ _ := abs_add_le _ _
          have hnmabs : |n| ≤ |m| + |m - n| := by
            calc |n| = |m + (n - m)| := by congr 1; ring
              _ ≤ |m| + |n - m| := abs_add_le _ _
              _ = _ := by rw [abs_sub_comm]
          dsimp [B]
          push_cast
          omega
        have he : (m, n) ∈ E := Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp hmB.1),
            Finset.mem_Icc.mpr (abs_le.mp hmB.2)⟩, hmn⟩
        have hfin : a * D ≤ ballDistance38 (C m) (C n) (R m) (R n) :=
          (le_div_iff₀ hDpos).mp (haF (m, n) he)
        exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hDpos.le).trans hfin
  let c : ℝ := max 1 (max (Real.pi + 2 * K) (1 / γ))
  have hc : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hcb : Real.pi + 2 * K ≤ c := (le_max_left _ _).trans (le_max_right _ _)
  have hcg : 1 / γ ≤ c := (le_max_right _ _).trans (le_max_right _ _)
  have hcγ : c⁻¹ ≤ γ := (inv_le_iff_one_le_mul₀' hcpos).mpr ((div_le_iff₀ hγ).mp hcg)
  refine ⟨c, hCR, hmono, hc, ?_, ?_⟩
  · intro m n hmn
    have hD : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |m - n| from by have hp := abs_pos.mpr (sub_ne_zero.mpr hmn); omega)
    refine ⟨(mul_le_mul_of_nonneg_right hcγ (abs_nonneg _)).trans (hlinear m n hmn), ?_⟩
    have hu := (isolating_distance_deviation38 C R K hR hdev m n).2
    calc ballDistance38 (C m) (C n) (R m) (R n) ≤
        (Real.pi + 2 * K) * |((m - n : ℤ) : ℝ)| := by nlinarith
      _ ≤ c * |((m - n : ℤ) : ℝ)| := mul_le_mul_of_nonneg_right hcb (abs_nonneg _)
  · intro n hn
    obtain ⟨hc, hr⟩ := hTail n hn
    exact ⟨hc, hr, by rw [hc, hr]⟩

end
end NlsGge.GK38
