import NlsGge.Hierarchy.ALNegativeQuartic38
import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.ALFreeFields38

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Weights

theorem al102_arcsin_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Real.arcsin s ≤ 2 * s := by
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

theorem al102_arcsin_abs (x : ℝ) (hx : |x| ≤ 1) : |Real.arcsin x| ≤ 2 * |x| := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.arcsin_nonneg.2 h)]
    exact al102_arcsin_le x h (abs_le.mp hx).2
  · have hx' : 0 ≤ -x := by linarith
    have e : Real.arcsin x = -Real.arcsin (-x) := by rw [Real.arcsin_neg, neg_neg]
    rw [e, abs_neg, abs_of_nonneg (Real.arcsin_nonneg.2 hx'), abs_of_nonpos h]
    exact al102_arcsin_le (-x) hx' (by linarith [(abs_le.mp hx).1])

theorem al102_half_le_sqrt {x : ℝ} (hx : 3 / 4 ≤ x) : 1 / 2 ≤ Real.sqrt x := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sqrt_nonneg x]

theorem al102_inv_le_two {s : ℝ} (hs : 1 / 2 ≤ s) : s⁻¹ ≤ 2 := by
  rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith

theorem al102_vh (L : ℕ) [NeZero L] (k : ℤ) {t h q : ℝ} (hh : h = 1 / (L : ℝ))
    (ht0 : 0 ≤ t) (hht : h * t ≤ 1 / 2) (hq : |q| ≤ t) :
    alVh38 h (alPlaneWave38 L k t) (Real.pi * k + Real.arcsin (h * q) / h) =
      alGq38 (fun _ => 1) h t 0 q * Real.sqrt (1 - h ^ 2 * q ^ 2) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hhpos : 0 < h := by rw [hh]; positivity
  have hgap := alPlaneWave_gap38 L k hh ht0 (by linarith) (Real.pi * k + Real.arcsin (h * q) / h)
  have harg : h * (Real.pi * k + Real.arcsin (h * q) / h) - Real.pi * k * h =
      Real.arcsin (h * q) := by
    field_simp; ring
  rw [harg] at hgap
  have hhq : |h * q| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hhpos]; exact le_trans (mul_le_mul_of_nonneg_left hq hhpos.le) hht
  have hhq1 : |h * q| ≤ 1 := le_trans hhq (by norm_num)
  have hcos : Real.cos (Real.arcsin (h * q)) = Real.sqrt (1 - h ^ 2 * q ^ 2) := by
    rw [Real.cos_arcsin, mul_pow]
  have hsin : Real.sin (Real.arcsin (h * q)) = h * q :=
    Real.sin_arcsin (abs_le.mp hhq1).1 (abs_le.mp hhq1).2
  unfold alVh38
  rw [hgap]
  rcases eq_or_lt_of_le ht0 with ht | ht
  · subst ht
    have hq0 : q = 0 := abs_nonpos_iff.mp hq
    subst hq0
    have h1 : Real.arcosh 1 = 0 := by rw [arcosh_eq_arsinh38 le_rfl]; norm_num
    simp [alGq38, h1]
  · have hmid := mid_identity38 (fun _ => (1 : ℝ)) (θ := 0) (φ := Real.arcsin (h * q))
      hhpos ht hht (Real.cos_arcsin_nonneg _)
      (by rw [hsin, abs_mul, abs_of_pos hhpos]; exact mul_le_mul_of_nonneg_left hq hhpos.le)
    have hqq : h * q / h = q := by field_simp
    simp only [hsin, one_mul, hqq] at hmid
    rw [← hcos]
    exact hmid

theorem al102_alGq_eq {h t q : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (hht : h * t ≤ 1 / 2)
    (hq2 : q ^ 2 ≤ t ^ 2) :
    alGq38 (fun _ => 1) h t 0 q * Real.sqrt (1 - h ^ 2 * q ^ 2) =
      h⁻¹ * Real.arsinh (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) := by
  have hA2 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht]
  have hB2 : h ^ 2 * q ^ 2 ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hq2 (sq_nonneg h)) hA2
  have hB : 0 < Real.sqrt (1 - h ^ 2 * q ^ 2) := Real.sqrt_pos.2 (by linarith)
  unfold alGq38
  simp only [one_mul]
  field_simp

theorem al102_alGq_bounds {h t q : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (hht : h * t ≤ 1 / 2)
    (hq2 : q ^ 2 ≤ t ^ 2) :
    0 ≤ alGq38 (fun _ => 1) h t 0 q ∧
      alGq38 (fun _ => 1) h t 0 q ≤ 4 * Real.sqrt (t ^ 2 - q ^ 2) := by
  have hA2 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht]
  have hB2 : h ^ 2 * q ^ 2 ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left hq2 (sq_nonneg h)) hA2
  have hAp : 0 < Real.sqrt (1 - h ^ 2 * t ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hAinv := al102_inv_le_two (al102_half_le_sqrt (x := 1 - h ^ 2 * t ^ 2) (by linarith))
  have hBinv := al102_inv_le_two (al102_half_le_sqrt (x := 1 - h ^ 2 * q ^ 2) (by linarith))
  have hX0 : 0 ≤ h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2) :=
    div_nonneg (mul_nonneg hh.le (Real.sqrt_nonneg _)) hAp.le
  have hs0 := Real.sqrt_nonneg (t ^ 2 - q ^ 2)
  have hT0 : 0 ≤ h⁻¹ * Real.arsinh (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) :=
    mul_nonneg (inv_nonneg.2 hh.le) (Real.arsinh_nonneg_iff.2 hX0)
  have hT1 : h⁻¹ * Real.arsinh (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) ≤
      2 * Real.sqrt (t ^ 2 - q ^ 2) := by
    calc h⁻¹ * Real.arsinh (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2))
        ≤ h⁻¹ * (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) :=
          mul_le_mul_of_nonneg_left (arsinh_le_self38 hX0) (inv_nonneg.2 hh.le)
      _ = Real.sqrt (t ^ 2 - q ^ 2) * (Real.sqrt (1 - h ^ 2 * t ^ 2))⁻¹ := by
          field_simp
      _ ≤ Real.sqrt (t ^ 2 - q ^ 2) * 2 := mul_le_mul_of_nonneg_left hAinv hs0
      _ = 2 * Real.sqrt (t ^ 2 - q ^ 2) := by ring
  have hBi0 : 0 ≤ (Real.sqrt (1 - h ^ 2 * q ^ 2))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  unfold alGq38
  simp only [one_mul]
  refine ⟨mul_nonneg hT0 hBi0, ?_⟩
  have := mul_le_mul hT1 hBinv hBi0 (by positivity)
  linarith

theorem al102 (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ, ∀ᶠ N : ℕ in atTop,
      let h : ℝ := alMeshStep38 N
      let lamOfQ : ℝ → ℝ := fun q => Real.pi * (k : ℝ) + Real.arcsin (h * q) / h
      let qOfLam : ℝ → ℝ := fun lam =>
        Real.sin (h * lam - Real.pi * (k : ℝ) * h) / h
      h * t < 1 ∧
      (∀ q ∈ Icc (-t) t,
        lamOfQ q ∈ Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h)) ∧
        qOfLam (lamOfQ q) = q ∧
        HasDerivAt lamOfQ (1 / Real.sqrt (1 - h ^ 2 * q ^ 2)) q ∧
        alVh38 h (alPlaneWave38 (2 * N + 1) k t) (lamOfQ q) =
          h⁻¹ * Real.arsinh
            (h * Real.sqrt (t ^ 2 - q ^ 2) / Real.sqrt (1 - h ^ 2 * t ^ 2)) ∧
        alVh38 h (alPlaneWave38 (2 * N + 1) k t) (lamOfQ q) ≤
          C * Real.sqrt (t ^ 2 - q ^ 2) ∧
        0 ≤ alGq38 (fun _ => 1) h t 0 q ∧
        alGq38 (fun _ => 1) h t 0 q ≤ C * Real.sqrt (t ^ 2 - q ^ 2)) ∧
      (∀ lam ∈ Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h)),
        0 < alVh38 h (alPlaneWave38 (2 * N + 1) k t) lam →
          qOfLam lam ∈ Icc (-t) t ∧ lamOfQ (qOfLam lam) = lam) := by
  refine ⟨4, by norm_num, fun k => ?_⟩
  have hT := alMeshStep_tendsto38.mul_const (Real.pi * (|(k : ℝ)| + t + 1))
  rw [zero_mul] at hT
  filter_upwards [hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with N hN
  intro h lamOfQ qOfLam
  have hNZ : NeZero (2 * N + 1) := ⟨by omega⟩
  have hh : 0 < h := by
    show 0 < alMeshStep38 N
    unfold alMeshStep38; positivity
  have hL : h = 1 / ((2 * N + 1 : ℕ) : ℝ) := by
    show alMeshStep38 N = _
    unfold alMeshStep38; push_cast; ring
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hmono : ∀ a : ℝ, 0 ≤ a → a ≤ Real.pi * (|(k : ℝ)| + t + 1) → h * a < 1 / 2 :=
    fun a ha hle => lt_of_le_of_lt (mul_le_mul_of_nonneg_left hle hh.le) hN
  have hht6 : h * t < 1 / 6 := by
    have := hmono (Real.pi * t) (mul_nonneg hpi.le ht)
      (by nlinarith [mul_nonneg hpi.le (abs_nonneg (k : ℝ))])
    nlinarith [mul_nonneg hh.le ht]
  have hk1 : h * (Real.pi * |(k : ℝ)|) < 1 / 2 :=
    hmono _ (mul_nonneg hpi.le (abs_nonneg _)) (by nlinarith [mul_nonneg hpi.le ht])
  have hwin : 2 * (h * (Real.pi * |(k : ℝ)|)) + 4 * (h * t) < Real.pi := by linarith
  have hht : h * t < 1 := by linarith
  have hhtH : h * t ≤ 1 / 2 := by linarith
  have hA2 : h ^ 2 * t ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hh.le ht]
  have hAp : 0 < Real.sqrt (1 - h ^ 2 * t ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hAfact := al102_half_le_sqrt (x := 1 - h ^ 2 * t ^ 2) (by linarith)
  have hsq : Real.sqrt (1 - h ^ 2 * t ^ 2) ^ 2 = 1 - h ^ 2 * t ^ 2 :=
    Real.sq_sqrt (by linarith)
  have hwq : ∀ q : ℝ, |q| ≤ t → |h * q| ≤ h * t := fun q hq => by
    rw [abs_mul, abs_of_pos hh]; exact mul_le_mul_of_nonneg_left hq hh.le
  have harc : ∀ q : ℝ, |q| ≤ t → |Real.arcsin (h * q) / h| ≤ 2 * t := fun q hq => by
    rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]
    have h1 := al102_arcsin_abs (h * q) (le_trans (hwq q hq) (by linarith))
    nlinarith [hwq q hq]
  have hlamQ_in : ∀ q : ℝ, |q| ≤ t →
      Real.pi * (k : ℝ) + Real.arcsin (h * q) / h ∈
        Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h)) := by
    intro q hq
    have hA := abs_le.mp (harc q hq)
    have hQ : Real.pi * |(k : ℝ)| + 2 * t < Real.pi / (2 * h) := by
      rw [lt_div_iff₀ (mul_pos two_pos hh)]; nlinarith
    have e1 : Real.pi * (k : ℝ) ≤ Real.pi * |(k : ℝ)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hpi.le
    have e2 : -(Real.pi * |(k : ℝ)|) ≤ Real.pi * (k : ℝ) := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le _) hpi.le
    rw [Set.mem_Ioc]
    constructor <;> linarith [hA.1, hA.2]
  have hkh : |Real.pi * (k : ℝ) * h| < 1 / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hpi, abs_of_pos hh]
    linarith [hk1]
  refine ⟨by linarith, fun q hq => ?_, fun lam hlam hpos => ?_⟩
  · obtain ⟨hq1, hq2⟩ := hq
    have hqa : |q| ≤ t := abs_le.mpr ⟨hq1, hq2⟩
    have hq2' : q ^ 2 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg q) hqa 2
      rwa [sq_abs] at this
    have hG := al102_alGq_bounds hh ht hhtH hq2'
    have hV := al102_vh (2 * N + 1) k hL ht hhtH hqa
    have hE := al102_alGq_eq hh ht hhtH hq2'
    have hB1 : Real.sqrt (1 - h ^ 2 * q ^ 2) ≤ 1 :=
      (Real.sqrt_le_sqrt (sub_le_self 1 (by positivity))).trans Real.sqrt_one.le
    have hVle : alVh38 h (alPlaneWave38 (2 * N + 1) k t)
        (Real.pi * (k : ℝ) + Real.arcsin (h * q) / h) ≤ 4 * Real.sqrt (t ^ 2 - q ^ 2) := by
      rw [hV]; exact (mul_le_of_le_one_right hG.1 hB1).trans hG.2
    have hx1 : |h * q| ≤ 1 := le_trans (hwq q hqa) (by linarith)
    have hsin := Real.sin_arcsin (abs_le.mp hx1).1 (abs_le.mp hx1).2
    have hmem : h * q ∈ Set.Ioo (-1 : ℝ) 1 :=
      abs_lt.mp (lt_of_le_of_lt (hwq q hqa) (by linarith))
    have hd : HasDerivAt (fun x : ℝ => h * x) (h * 1) q := (hasDerivAt_id' q).const_mul h
    have h1' : h * q ≠ -1 := ne_of_gt hmem.1
    have h2' : h * q ≠ 1 := ne_of_lt hmem.2
    have hdF := (((HasDerivAt.comp q (Real.hasDerivAt_arcsin h1' h2') hd).div_const h).const_add
      (Real.pi * (k : ℝ)))
    refine ⟨hlamQ_in q hqa, ?_, ?_, hV.trans hE, hVle, hG.1, hG.2⟩
    · show Real.sin (h * (Real.pi * k + Real.arcsin (h * q) / h) - Real.pi * k * h) / h = q
      have harg2 : h * (Real.pi * k + Real.arcsin (h * q) / h) - Real.pi * k * h =
          Real.arcsin (h * q) := by
        field_simp; ring
      rw [harg2, hsin]; field_simp
    · refine HasDerivAt.congr_deriv hdF ?_
      rw [mul_pow, mul_one]; field_simp
  · obtain ⟨hl1, hl2⟩ := hlam
    have hkey : Real.pi / (2 * h) * (2 * h) = Real.pi := div_mul_cancel₀ _ (mul_pos two_pos hh).ne'
    have hA1 : h * lam ≤ Real.pi / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hl2 (mul_pos two_pos hh).le]
    have hA2' : -(Real.pi / 2) < h * lam := by
      nlinarith [mul_lt_mul_of_pos_right hl1 (mul_pos two_pos hh)]
    unfold alVh38 at hpos
    rw [alPlaneWave_gap38 (2 * N + 1) k hL ht hht lam] at hpos
    have har : 0 < Real.arcosh (max 1 (|Real.cos (h * lam - Real.pi * k * h)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2))) := pos_of_mul_pos_right hpos (inv_nonneg.2 hh.le)
    have hmax : 1 < max 1 (|Real.cos (h * lam - Real.pi * k * h)| /
        Real.sqrt (1 - h ^ 2 * t ^ 2)) := by
      by_contra hc
      push_neg at hc
      have he : max 1 (|Real.cos (h * lam - Real.pi * k * h)| /
          Real.sqrt (1 - h ^ 2 * t ^ 2)) = 1 := le_antisymm hc (le_max_left _ _)
      rw [he, arcosh_eq_arsinh38 le_rfl] at har
      norm_num at har
    have hr : 1 < |Real.cos (h * lam - Real.pi * k * h)| / Real.sqrt (1 - h ^ 2 * t ^ 2) :=
      (lt_max_iff.1 hmax).resolve_left (lt_irrefl 1)
    have hAlt : Real.sqrt (1 - h ^ 2 * t ^ 2) < |Real.cos (h * lam - Real.pi * k * h)| :=
      (one_lt_div hAp).1 hr
    have hsin2 : (Real.sin (h * lam - Real.pi * k * h)) ^ 2 < (h * t) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq (h * lam - Real.pi * k * h),
        mul_self_lt_mul_self hAp.le hAlt, abs_mul_abs_self (Real.cos (h * lam - Real.pi * k * h))]
    have hsinabs : |Real.sin (h * lam - Real.pi * k * h)| < h * t :=
      abs_lt_of_sq_lt_sq hsin2 (mul_nonneg hh.le ht)
    have hqmem : |Real.sin (h * lam - Real.pi * k * h) / h| ≤ t := by
      rw [abs_div, abs_of_pos hh, div_le_iff₀ hh]; linarith
    have hsin_back : h * (Real.sin (h * lam - Real.pi * k * h) / h) =
        Real.sin (h * lam - Real.pi * k * h) := by field_simp
    have hφ : |h * lam - Real.pi * k * h| ≤ Real.pi / 2 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = |h * lam - Real.pi * k * h| - Real.pi / 2 := ⟨_, rfl⟩
      have hψpos : 0 < ψ := by rw [hψ]; linarith
      have hψle : ψ ≤ 1 / 2 := by
        rw [hψ]
        have hu : h * lam - Real.pi * k * h ≤ Real.pi / 2 + 1 / 2 := by
          linarith [(abs_lt.mp hkh).1]
        have hl : -(Real.pi / 2 + 1 / 2) ≤ h * lam - Real.pi * k * h := by
          linarith [(abs_lt.mp hkh).2]
        linarith [abs_le.mpr ⟨hl, hu⟩]
      have e : |h * lam - Real.pi * k * h| = ψ + Real.pi / 2 := by linarith
      have hcosψ : |Real.cos (h * lam - Real.pi * k * h)| ≤ ψ := by
        rw [← Real.cos_abs (h * lam - Real.pi * k * h), e, Real.cos_add_pi_div_two, abs_neg]
        exact Real.abs_sin_le_abs.trans (abs_of_pos hψpos).le
      linarith
    have hasin := Real.arcsin_sin (abs_le.mp hφ).1 (abs_le.mp hφ).2
    refine ⟨⟨by linarith [(abs_le.mp hqmem).1], (abs_le.mp hqmem).2⟩, ?_⟩
    show Real.pi * (k : ℝ) + Real.arcsin (h * (Real.sin (h * lam - Real.pi * k * h) / h)) / h = lam
    rw [hsin_back, hasin]
    field_simp
    ring

end NlsGge.ThirdConsultation.AL
