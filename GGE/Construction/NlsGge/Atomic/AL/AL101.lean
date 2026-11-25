import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.ALPlaneConsistency38

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations

theorem al101_mesh_cast (N : ℕ) :
    alMeshStep38 N = (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
  simp [alMeshStep38]

theorem al101_mesh_tendsto : Tendsto (fun N : ℕ => alMeshStep38 N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have h2 := tendsto_inv_atTop_zero.comp h1
  refine h2.congr fun N => ?_
  simp [alMeshStep38, Function.comp_apply, one_div]

theorem al101_T : Tendsto (fun N : ℕ => alMeshStep38 N) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨al101_mesh_tendsto,
    Eventually.of_forall fun N => show (0 : ℝ) < alMeshStep38 N by
      unfold alMeshStep38; positivity⟩

theorem al101_lt (h x c : ℝ) (hh : 0 < h) : x < c ↔ h * x < h * c :=
  ⟨fun H => mul_lt_mul_of_pos_left H hh, fun H => lt_of_mul_lt_mul_left H hh.le⟩

theorem al101_le (h x c : ℝ) (hh : 0 < h) : x ≤ c ↔ h * x ≤ h * c :=
  ⟨fun H => mul_le_mul_of_nonneg_left H hh.le, fun H => le_of_mul_le_mul_left H hh⟩

theorem al101_vh (k : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (N : ℕ) (h : ℝ)
    (hdef : h = (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) (hht : h * t < 1) (lam : ℝ) :
    alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam =
      h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * lam - Real.pi * (k : ℝ) * h)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2))) := by
  unfold alVh38
  exact alPlaneWave_gap38 (2 * N + 1) k hdef ht0 hht lam

theorem al101_key (h t : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t < 1) (x : ℝ) :
    (1 - h ^ 2 * t ^ 2 < Real.cos x ^ 2 ↔ |Real.sin x| < h * t) := by
  have hs0 : 0 ≤ h * t := mul_nonneg hh.le ht0
  have hid := Real.sin_sq_add_cos_sq x
  have e : |Real.sin x| ^ 2 = Real.sin x ^ 2 := sq_abs _
  rw [← sq_lt_sq₀ (abs_nonneg (Real.sin x)) hs0, e, mul_pow]
  constructor <;> intro H <;> linarith

theorem al101_pos_iff (k : ℤ) (t : ℝ) (ht0 : 0 ≤ t) (N : ℕ) (h : ℝ)
    (hdef : h = (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ)) (hh : 0 < h) (hht : h * t < 1) (lam : ℝ) :
    0 < alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam ↔
      |Real.sin (h * lam - Real.pi * (k : ℝ) * h)| < h * t := by
  rw [al101_vh k t ht0 N h hdef hht lam, mul_pos_iff_of_pos_left (inv_pos.2 hh)]
  have hQ : 0 < 1 - h ^ 2 * t ^ 2 := by
    have hs0 : 0 ≤ h * t := mul_nonneg hh.le ht0
    nlinarith
  have hA : 0 < Real.arcosh (max 1 (|Real.cos (h * lam - Real.pi * (k : ℝ) * h)| /
      Real.sqrt (1 - h ^ 2 * t ^ 2))) ↔
      1 < |Real.cos (h * lam - Real.pi * (k : ℝ) * h)| / Real.sqrt (1 - h ^ 2 * t ^ 2) := by
    constructor
    · intro H
      by_contra hc
      push_neg at hc
      rw [max_eq_left hc, Real.arcosh_zero] at H
      exact lt_irrefl _ H
    · intro H
      exact Real.arcosh_pos (lt_max_of_lt_right H)
  rw [hA, one_lt_div (Real.sqrt_pos.2 hQ),
    ← Real.sqrt_sq_eq_abs (Real.cos (h * lam - Real.pi * (k : ℝ) * h)),
    Real.sqrt_lt_sqrt_iff hQ.le]
  exact al101_key h t hh ht0 hht _

theorem al101_arcsin_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Real.arcsin s ≤ 2 * s := by
  have hx0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 hs0
  have hx1 : Real.arcsin s ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  have hJ := Real.mul_le_sin hx0 hx1
  rw [Real.sin_arcsin (by linarith) hs1] at hJ
  have hπ := Real.pi_pos
  have hπ4 := Real.pi_le_four
  have h1 : Real.pi / 2 * (2 / Real.pi * Real.arcsin s) = Real.arcsin s := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hJ (by positivity : (0 : ℝ) ≤ Real.pi / 2)
  nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 4 - Real.pi)]

theorem al101_real (w a s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (ha : |a| ≤ Real.pi / 6) :
    ((-(Real.pi / 2) < w ∧ w ≤ Real.pi / 2) ∧ |Real.sin (w - a)| < s) ↔
      (-Real.arcsin s < w - a ∧ w - a < Real.arcsin s) := by
  have hπ := Real.pi_gt_three
  have hA2 : Real.arcsin s ≤ 2 * s := al101_arcsin_le s hs0 (by linarith)
  have hsA : Real.sin (Real.arcsin s) = s := Real.sin_arcsin (by linarith) (by linarith)
  have hAp : Real.arcsin s ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two s
  have hA1 : Real.arcsin s ≤ 1 := by linarith
  have hA0 : 0 ≤ Real.arcsin s := Real.arcsin_nonneg.2 hs0
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  constructor
  · rintro ⟨⟨hw1, hw2⟩, hsin⟩
    have hs_pos : 0 < s := lt_of_le_of_lt (abs_nonneg _) hsin
    have hu1 : -(2 * Real.pi / 3) < w - a := by linarith
    have hu2 : w - a ≤ 2 * Real.pi / 3 := by linarith
    have hsin_le := le_abs_self (Real.sin (w - a))
    have hneg_le := neg_le_abs (Real.sin (w - a))
    rcases le_or_gt 0 (w - a) with hu0 | hu0
    · rcases le_or_gt (w - a) (Real.pi / 2) with hu3 | hu3
      · have hsu : Real.sin (w - a) = |Real.sin (w - a)| :=
          (abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith))).symm
        have hlt : w - a < Real.arcsin s := by
          by_contra hc
          push_neg at hc
          have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.arcsin s) (y := w - a)
            (by linarith) hu3 hc
          linarith
        exact ⟨by linarith, hlt⟩
      · exfalso
        have h1 : Real.sin (w - a) = Real.sin (Real.pi - (w - a)) :=
          (Real.sin_pi_sub (w - a)).symm
        have h2 : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi - (w - a)) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
        rw [Real.sin_pi_div_six] at h2
        linarith
    · rcases le_or_gt (-(Real.pi / 2)) (w - a) with hu4 | hu4
      · have hsn : 0 ≤ Real.sin (-(w - a)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
        have e : Real.sin (-(w - a)) = -Real.sin (w - a) := Real.sin_neg _
        have hsu : |Real.sin (w - a)| = Real.sin (-(w - a)) := by
          rw [e, abs_of_nonpos (show Real.sin (w - a) ≤ 0 by linarith)]
        have hlt : -Real.arcsin s < w - a := by
          by_contra hc
          push_neg at hc
          have := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.arcsin s)
            (y := -(w - a)) (by linarith) (by linarith) (by linarith)
          linarith
        exact ⟨hlt, by linarith⟩
      · exfalso
        have e : Real.sin (-(w - a)) = -Real.sin (w - a) := Real.sin_neg _
        have h1 : Real.sin (-(w - a)) = Real.sin (Real.pi - -(w - a)) :=
          (Real.sin_pi_sub _).symm
        have h2 : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi - -(w - a)) :=
          Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
        rw [Real.sin_pi_div_six] at h2
        linarith
  · rintro ⟨hl, hr⟩
    have hab : |w - a| < Real.arcsin s := abs_lt.2 ⟨hl, hr⟩
    have hwa : |w| < Real.pi / 2 := by
      have := abs_add_le (w - a) a
      rw [show w - a + a = w by ring] at this
      linarith
    obtain ⟨hw1, hw2⟩ := abs_lt.1 hwa
    refine ⟨⟨hw1, hw2.le⟩, ?_⟩
    have hsl := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := w - a) (y := Real.arcsin s)
      (by linarith) hAp hr
    have hsr := Real.sin_lt_sin_of_lt_of_le_pi_div_two (x := -Real.arcsin s) (y := w - a)
      (by linarith) (by linarith) hl
    rw [Real.sin_neg, hsA] at hsr
    rw [hsA] at hsl
    exact abs_lt.2 ⟨by linarith, by linarith⟩

/-- AL-101: exact plane height and the one gap in the principal period (wrapper-level
conjunct 1 via `alPlaneWave_gap38`; conjunct 2 via the real window lemma `al101_real`). -/
theorem al101 (k : ℤ) (t : ℝ) (ht : 0 ≤ t) :
    (∀ N : ℕ, alMeshStep38 N * t < 1 → ∀ lam : ℝ,
      let h : ℝ := alMeshStep38 N
      let r : ℝ := |Real.cos (h * lam - Real.pi * (k : ℝ) * h)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2)
      alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam =
        if 1 < r then h⁻¹ * Real.arcosh r else 0) ∧
    ∀ᶠ N : ℕ in atTop,
      let h : ℝ := alMeshStep38 N
      let left : ℝ := Real.pi * (k : ℝ) - Real.arcsin (h * t) / h
      let right : ℝ := Real.pi * (k : ℝ) + Real.arcsin (h * t) / h
      h * t < 1 ∧
      {lam : ℝ | lam ∈ Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h)) ∧
        0 < alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam} = Ioo left right ∧
      Icc left right ⊆ Icc (Real.pi * (k : ℝ) - 2 * t)
        (Real.pi * (k : ℝ) + 2 * t) := by
  have ht0 : 0 ≤ t := ht
  refine ⟨?_, ?_⟩
  · intro N hN lam
    dsimp only
    have hcast := al101_mesh_cast N
    generalize alMeshStep38 N = h at hcast hN ⊢
    rw [al101_vh k t ht0 N h hcast hN lam]
    split_ifs with hr
    · rw [max_eq_right hr.le]
    · rw [max_eq_left (not_lt.1 hr), Real.arcosh_zero, mul_zero]
  · have hk6 : ∀ᶠ N : ℕ in atTop, |(k : ℝ)| * alMeshStep38 N < 1 / 6 := by
      have h0 : Tendsto (fun N : ℕ => |(k : ℝ)| * alMeshStep38 N) atTop (𝓝 0) := by
        simpa using al101_mesh_tendsto.const_mul |(k : ℝ)|
      exact h0.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [al101_T.eventually (eventually_small38 t ht0 k), hk6] with N hN hk
    dsimp only
    have hcast := al101_mesh_cast N
    generalize alMeshStep38 N = h at hcast hN hk ⊢
    obtain ⟨hh, hs, _⟩ := hN
    have hs0 : 0 ≤ h * t := mul_nonneg hh.le ht0
    have hht : h * t < 1 := by linarith
    have hne : h ≠ 0 := hh.ne'
    have hha : |Real.pi * (k : ℝ) * h| ≤ Real.pi / 6 := by
      have e1 : |(k : ℝ) * h| = |(k : ℝ)| * h := by rw [abs_mul, abs_of_pos hh]
      have e2 : Real.pi * (k : ℝ) * h = Real.pi * ((k : ℝ) * h) := by ring
      rw [e2, abs_mul, abs_of_pos Real.pi_pos, e1]
      have := mul_le_mul_of_nonneg_left hk.le Real.pi_pos.le
      linarith
    have hL : h * (-(Real.pi / (2 * h))) = -(Real.pi / 2) := by
      field_simp
    have hR : h * (Real.pi / (2 * h)) = Real.pi / 2 := by
      field_simp
    have hLf : h * (Real.pi * (k : ℝ) - Real.arcsin (h * t) / h) =
        Real.pi * (k : ℝ) * h - Real.arcsin (h * t) := by
      field_simp
    have hRf : h * (Real.pi * (k : ℝ) + Real.arcsin (h * t) / h) =
        Real.pi * (k : ℝ) * h + Real.arcsin (h * t) := by
      field_simp
    refine ⟨hht, ?_, ?_⟩
    · ext lam
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_Ioo]
      have e1 : (-(Real.pi / (2 * h)) < lam) ↔ (-(Real.pi / 2) < h * lam) :=
        (al101_lt h (-(Real.pi / (2 * h))) lam hh).trans (by rw [hL])
      have e2 : (lam ≤ Real.pi / (2 * h)) ↔ (h * lam ≤ Real.pi / 2) :=
        (al101_le h lam (Real.pi / (2 * h)) hh).trans (by rw [hR])
      have e3 : (Real.pi * (k : ℝ) - Real.arcsin (h * t) / h < lam) ↔
          (-Real.arcsin (h * t) < h * lam - Real.pi * (k : ℝ) * h) :=
        (al101_lt h _ lam hh).trans (by
          rw [hLf]; constructor <;> intro H <;> linarith)
      have e4 : (lam < Real.pi * (k : ℝ) + Real.arcsin (h * t) / h) ↔
          (h * lam - Real.pi * (k : ℝ) * h < Real.arcsin (h * t)) :=
        (al101_lt h lam _ hh).trans (by
          rw [hRf]; constructor <;> intro H <;> linarith)
      rw [al101_pos_iff k t ht0 N h hcast hh hht lam, e1, e2, e3, e4]
      exact al101_real (h * lam) (Real.pi * (k : ℝ) * h) (h * t) hs0 hs hha
    · intro x hx
      have hd : Real.arcsin (h * t) / h ≤ 2 * t := by
        rw [div_le_iff₀ hh]
        have := al101_arcsin_le (h * t) hs0 (by linarith)
        nlinarith
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

end NlsGge.ThirdConsultation.AL
