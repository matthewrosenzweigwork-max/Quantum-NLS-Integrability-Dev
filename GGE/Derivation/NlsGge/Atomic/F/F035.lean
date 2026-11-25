import Mathlib
import NlsGge.Atomic.F.F034
import NlsGge.Hierarchy.RiccatiQ6CuspNegative38

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology ContDiff
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F
noncomputable section
namespace F035Aux

theorem dens_even (η : ℝ → ℝ) (hη : IsCuspCutoff η) (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : |x| < 1 / 8) :
    cutoffCuspDensity η ε (-x) = cutoffCuspDensity η ε x := by
  obtain ⟨hC, hsupp, hone⟩ := hη
  obtain ⟨a0, a1, a2⟩ := cusp_deriv_closed_values η hsupp hone ε hε x hx
  obtain ⟨b0, b1, b2⟩ := cusp_deriv_closed_values η hsupp hone ε hε (-x) (by simpa using hx)
  unfold cutoffCuspDensity
  rw [a0, a1, a2, b0, b1, b2]
  simp only [neg_sq]
  ring

theorem core_bound (η : ℝ → ℝ) (hη : IsCuspCutoff η) (ε : ℝ) (hε : 0 < ε) (hε8 : ε < 1 / 8)
    (x : ℝ) (hx : |x| ≤ ε) : |cutoffCuspDensity η ε x| ≤ 12 / ε := by
  obtain ⟨hC, hsupp, hone⟩ := hη
  obtain ⟨a0, a1, a2⟩ := cusp_deriv_closed_values η hsupp hone ε hε x (hx.trans_lt hε8)
  unfold cutoffCuspDensity
  rw [a0, a1, a2]
  have hx2 : x ^ 2 ≤ ε ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le hx) (le_of_abs_le hx)
    exact this
  have hu0 : 0 < x ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg x) (pow_pos hε 2)
  set u : ℝ := x ^ 2 + ε ^ 2 with hu
  have hε2 : ε ^ 2 ≤ u := by rw [hu]; linarith [sq_nonneg x]
  have e1 : (u ^ ((3 : ℝ) / 8)) ^ 2 = u ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have e2 : (u ^ (-(13 : ℝ) / 8)) ^ 2 = u ^ (-(13 : ℝ) / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have e3 : (u ^ (-(5 : ℝ) / 8)) ^ 4 = u ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have e4 : u ^ ((3 : ℝ) / 4) * u ^ (-(13 : ℝ) / 4) = u ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_add hu0]; norm_num
  set w : ℝ := u ^ (-(5 : ℝ) / 2) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hu0 _
  have hwle : w ≤ (ε ^ 5)⁻¹ := by
    have h1 : u ^ (-(5 : ℝ) / 2) ≤ (ε ^ 2) ^ (-(5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos (pow_pos hε 2) hε2 (by norm_num)
    have h2 : (ε ^ 2) ^ (-(5 : ℝ) / 2) = (ε ^ 5)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, show ((2 : ℕ) : ℝ) * (-(5 : ℝ) / 2) = -((5 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hε.le, Real.rpow_natCast]
    rw [hw]; exact h1.trans h2.le
  have hdens : 14 * (u ^ ((3 : ℝ) / 8)) ^ 2 * ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * u ^ (-(13 : ℝ) / 8)) ^ 2 -
      7 * ((3 : ℝ) / 4 * x * u ^ (-(5 : ℝ) / 8)) ^ 4 =
      (14 * (9 / 256) * (4 * ε ^ 2 - x ^ 2) ^ 2) * w - (7 * (81 / 256) * x ^ 4) * w := by
    have : 14 * (u ^ ((3 : ℝ) / 8)) ^ 2 * ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * u ^ (-(13 : ℝ) / 8)) ^ 2 =
        14 * (9 / 256) * (4 * ε ^ 2 - x ^ 2) ^ 2 * (u ^ ((3 : ℝ) / 4) * u ^ (-(13 : ℝ) / 4)) := by
      rw [mul_pow, mul_pow, e1, e2]; ring
    rw [this, e4, mul_pow, mul_pow, e3]; ring
  rw [hdens]
  have hA : 0 ≤ 14 * (9 / 256) * (4 * ε ^ 2 - x ^ 2) ^ 2 := by positivity
  have hB : 0 ≤ 7 * (81 / 256) * x ^ 4 := by positivity
  have hAle : 14 * (9 / 256) * (4 * ε ^ 2 - x ^ 2) ^ 2 ≤ 8 * ε ^ 4 := by
    have h0 : 0 ≤ 4 * ε ^ 2 - x ^ 2 := by linarith [sq_nonneg ε]
    have h1 : 4 * ε ^ 2 - x ^ 2 ≤ 4 * ε ^ 2 := by linarith [sq_nonneg x]
    have h2 := pow_le_pow_left₀ h0 h1 2
    have h3 : (4 * ε ^ 2) ^ 2 = 16 * ε ^ 4 := by ring
    rw [h3] at h2
    have h4 : 0 ≤ ε ^ 4 := by positivity
    linarith
  have hBle : 7 * (81 / 256) * x ^ 4 ≤ 3 * ε ^ 4 := by
    have h2 := pow_le_pow_left₀ (sq_nonneg x) hx2 2
    have e5 : (x ^ 2) ^ 2 = x ^ 4 := by ring
    have e6 : (ε ^ 2) ^ 2 = ε ^ 4 := by ring
    rw [e5, e6] at h2
    have h4 : 0 ≤ ε ^ 4 := by positivity
    linarith
  have hε5 : ε ^ 4 * (ε ^ 5)⁻¹ = 1 / ε := by
    field_simp
  have hAw := mul_le_mul_of_nonneg_right hAle hw0.le
  have hBw := mul_le_mul_of_nonneg_right hBle hw0.le
  have hAw0 := mul_nonneg hA hw0.le
  have hBw0 := mul_nonneg hB hw0.le
  have hε4w : ε ^ 4 * w ≤ 1 / ε := by
    calc ε ^ 4 * w ≤ ε ^ 4 * (ε ^ 5)⁻¹ := mul_le_mul_of_nonneg_left hwle (by positivity)
      _ = 1 / ε := hε5
  have hpos : 0 ≤ ε ^ 4 * w := by positivity
  have hinv : 0 ≤ 1 / ε := by positivity
  have h12 : 12 / ε = 12 * (1 / ε) := by ring
  rw [abs_le, h12]
  constructor <;> linarith

theorem cusp_local (η : ℝ → ℝ) (hsupp : Function.support η ⊆ Set.Ioo (-(1 : ℝ) / 4) (1 / 4))
    (ε y : ℝ) (hy : |y| < 3 / 4) :
    cutoffCusp η ε y = η y * (y ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := by
  unfold cutoffCusp
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have := Int.one_le_abs hk
      exact_mod_cast this
    have h1 := abs_sub_abs_le_abs_sub (k : ℝ) y
    rw [abs_sub_comm] at h1
    have hfar : 1 / 4 ≤ |y - (k : ℝ)| := by linarith
    rw [eta_zero_of_far η hsupp _ hfar, zero_mul]

theorem rpow_bound (r : ℝ) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 8 → ∀ y : ℝ, 1 / 8 ≤ |y| → |y| ≤ 1 / 2 →
      |(y ^ 2 + ε ^ 2) ^ r| ≤ B := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) (1 / 8) ×ˢ {y : ℝ | 1 / 8 ≤ |y| ∧ |y| ≤ 1 / 2}
  have hcl : IsClosed {y : ℝ | 1 / 8 ≤ |y| ∧ |y| ≤ 1 / 2} :=
    (isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const)
  have hsub : {y : ℝ | 1 / 8 ≤ |y| ∧ |y| ≤ 1 / 2} ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    intro y hy
    exact abs_le.1 hy.2
  have hKc : IsCompact K :=
    isCompact_Icc.prod (IsCompact.of_isClosed_subset isCompact_Icc hcl hsub)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.2 ^ 2 + p.1 ^ 2) ^ r) K := by
    refine ContinuousOn.rpow_const (by fun_prop) (fun p hp => Or.inl ?_)
    have h1 : (1 : ℝ) / 8 ≤ |p.2| := hp.2.1
    have h2 : (0 : ℝ) < p.2 ^ 2 := by
      have : 0 < |p.2| := by linarith
      have hne : p.2 ≠ 0 := abs_pos.1 this
      positivity
    exact (add_pos_of_pos_of_nonneg h2 (sq_nonneg _)).ne'
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨B, fun ε h0 h1 y h2 h3 => ?_⟩
  have := hB (ε, y) ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
  simpa using this

theorem bdd_of_vanish (h : ℝ → ℝ) (hc : Continuous h) (hz : ∀ y : ℝ, 1 / 4 < |y| → h y = 0) :
    ∃ M : ℝ, ∀ y : ℝ, |h y| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-(1 / 4) : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn
    hc.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨M, fun y => ?_⟩
  by_cases hy : |y| ≤ 1 / 4
  · exact hM y (abs_le.1 hy)
  · push_neg at hy
    rw [hz y hy, abs_zero]; exact hM0

theorem eta_bounds (η : ℝ → ℝ) (hη : IsCuspCutoff η) :
    ∃ M : ℝ, ∀ y : ℝ, |η y| ≤ M ∧ |deriv η y| ≤ M ∧ |deriv (deriv η) y| ≤ M := by
  obtain ⟨hC, hsupp, hone⟩ := hη
  have hopen : ∀ y : ℝ, 1 / 4 < |y| → {z : ℝ | 1 / 4 < |z|} ∈ 𝓝 y := fun y hy =>
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) hy
  have hz0 : ∀ y : ℝ, 1 / 4 < |y| → η y = 0 := fun y hy =>
    eta_zero_of_far η hsupp y hy.le
  have hev0 : ∀ y : ℝ, 1 / 4 < |y| → η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := fun y hy => by
    filter_upwards [hopen y hy] with z hz using hz0 z hz
  have hz1 : ∀ y : ℝ, 1 / 4 < |y| → deriv η y = 0 := fun y hy => by
    rw [(hev0 y hy).deriv_eq]; simp
  have hev1 : ∀ y : ℝ, 1 / 4 < |y| → deriv η =ᶠ[𝓝 y] fun _ => (0 : ℝ) := fun y hy => by
    filter_upwards [hopen y hy] with z hz using hz1 z hz
  have hz2 : ∀ y : ℝ, 1 / 4 < |y| → deriv (deriv η) y = 0 := fun y hy => by
    rw [(hev1 y hy).deriv_eq]; simp
  obtain ⟨M0, h0⟩ := bdd_of_vanish η hC.continuous hz0
  have hC1 : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.1 hC).2
  have hC2 : ContDiff ℝ ∞ (deriv (deriv η)) := (contDiff_infty_iff_deriv.1 hC1).2
  obtain ⟨M1, h1⟩ := bdd_of_vanish (deriv η) hC1.continuous hz1
  obtain ⟨M2, h2⟩ := bdd_of_vanish (deriv (deriv η)) hC2.continuous hz2
  refine ⟨max M0 (max M1 M2), fun y => ⟨?_, ?_, ?_⟩⟩
  · exact (h0 y).trans (le_max_left _ _)
  · exact (h1 y).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h2 y).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem abs_mul_le' {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

theorem dens_alg {f f1 f2 F0 F1 F2 : ℝ} (h0 : |f| ≤ F0) (h1 : |f1| ≤ F1) (h2 : |f2| ≤ F2) :
    |14 * f ^ 2 * f2 ^ 2 - 7 * f1 ^ 4| ≤ 14 * F0 ^ 2 * F2 ^ 2 + 7 * F1 ^ 4 := by
  have a1 : f ^ 2 ≤ F0 ^ 2 := by
    rw [← sq_abs f]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have a2 : f2 ^ 2 ≤ F2 ^ 2 := by
    rw [← sq_abs f2]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have a3' : f1 ^ 2 ≤ F1 ^ 2 := by
    rw [← sq_abs f1]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a3 : f1 ^ 4 ≤ F1 ^ 4 := by
    have := pow_le_pow_left₀ (sq_nonneg f1) a3' 2
    have e1 : (f1 ^ 2) ^ 2 = f1 ^ 4 := by ring
    have e2 : (F1 ^ 2) ^ 2 = F1 ^ 4 := by ring
    rw [e1, e2] at this; exact this
  have hP : f ^ 2 * f2 ^ 2 ≤ F0 ^ 2 * F2 ^ 2 := mul_le_mul a1 a2 (sq_nonneg _) (le_trans (sq_nonneg _) a1)
  have hP0 : 0 ≤ f ^ 2 * f2 ^ 2 := by positivity
  have hQ0 : 0 ≤ f1 ^ 4 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [hP, hP0, hQ0, a3]

theorem region_bound (η : ℝ → ℝ) (hη : IsCuspCutoff η) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ∀ x : ℝ, 1 / 8 ≤ |x| → |x| ≤ 1 / 2 →
      |cutoffCuspDensity η ε x| ≤ B := by
  obtain ⟨hC, hsupp, hone⟩ := hη
  obtain ⟨M, hM⟩ := eta_bounds η ⟨hC, hsupp, hone⟩
  obtain ⟨B1, hB1⟩ := rpow_bound ((3 : ℝ) / 8)
  obtain ⟨B2, hB2⟩ := rpow_bound (-(5 : ℝ) / 8)
  obtain ⟨B3, hB3⟩ := rpow_bound (-(13 : ℝ) / 8)
  have hC1 : ContDiff ℝ ∞ (deriv η) := (contDiff_infty_iff_deriv.1 hC).2
  have hd0 : Differentiable ℝ η := (contDiff_infty_iff_deriv.1 hC).1
  have hd1 : Differentiable ℝ (deriv η) := (contDiff_infty_iff_deriv.1 hC1).1
  refine ⟨14 * (M * B1) ^ 2 * (M * B1 + 2 * (M * (1 * B2)) + M * (1 * B3)) ^ 2 + 7 * (M * B1 + M * (1 * B2)) ^ 4, ?_⟩
  intro ε hε hε8 x hx1 hx2
  have hxlt : |x| < 3 / 4 := by linarith
  have hev : cutoffCusp η ε =ᶠ[𝓝 x] fun y => η y * (y ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hxlt] with y hy
    exact cusp_local η hsupp ε y hy
  have hg : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8))
      ((3 : ℝ) / 4 * y * (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) y := hasDerivAt_closed ε hε
  have hg2 : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (3 : ℝ) / 4 * z * (z ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))
      ((3 : ℝ) / 16 * (4 * ε ^ 2 - y ^ 2) * (y ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) y :=
    hasDerivAt_second ε hε
  have hη1 : ∀ y : ℝ, HasDerivAt η (deriv η y) y := fun y => (hd0 y).hasDerivAt
  have hη2 : ∀ y : ℝ, HasDerivAt (deriv η) (deriv (deriv η) y) y := fun y => (hd1 y).hasDerivAt
  have hGd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => η z * (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8))
      (deriv η y * (y ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) +
        η y * ((3 : ℝ) / 4 * y * (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))) y :=
    fun y => (hη1 y).mul (hg y)
  have hderiv : deriv (fun z : ℝ => η z * (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) =
      fun y => deriv η y * (y ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) +
        η y * ((3 : ℝ) / 4 * y * (y ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) :=
    funext fun y => (hGd y).deriv
  have e0 : cutoffCusp η ε x = η x * (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) := hev.self_of_nhds
  have e1 : deriv (cutoffCusp η ε) x = deriv η x * (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) +
      η x * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)) := by
    rw [hev.deriv_eq, hderiv]
  have e2 : iteratedDeriv 2 (cutoffCusp η ε) x =
      deriv (deriv η) x * (x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8) +
        2 * (deriv η x * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))) +
        η x * ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hd : deriv (cutoffCusp η ε) =ᶠ[𝓝 x]
        deriv (fun z : ℝ => η z * (z ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)) := hev.deriv
    rw [hd.deriv_eq, hderiv]
    have := ((hη2 x).mul (hg x)).add ((hη1 x).mul (hg2 x))
    exact this.deriv.trans (by ring)
  -- bounds
  have b1 : |(x ^ 2 + ε ^ 2) ^ ((3 : ℝ) / 8)| ≤ B1 := hB1 ε hε.le hε8.le x hx1 hx2
  have b2 : |(x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8)| ≤ B2 := hB2 ε hε.le hε8.le x hx1 hx2
  have b3 : |(x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8)| ≤ B3 := hB3 ε hε.le hε8.le x hx1 hx2
  obtain ⟨m0, m1, m2⟩ := hM x
  have c1 : |(3 : ℝ) / 4 * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]; linarith
  have c2 : |(3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2)| ≤ 1 := by
    have hx4 : x ^ 2 ≤ 1 / 4 := by
      have := sq_le_sq' (neg_le_of_abs_le hx2) (le_of_abs_le hx2)
      linarith
    have he4 : ε ^ 2 ≤ 1 / 64 := by nlinarith
    have h4 : |4 * ε ^ 2 - x ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg x, sq_nonneg ε]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 16)]
    linarith
  have hf : |cutoffCusp η ε x| ≤ M * B1 := by rw [e0]; exact abs_mul_le' m0 b1
  have hga : |η x * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))| ≤ M * (1 * B2) :=
    abs_mul_le' m0 (abs_mul_le' c1 b2)
  have hgb : |deriv η x * ((3 : ℝ) / 4 * x * (x ^ 2 + ε ^ 2) ^ (-(5 : ℝ) / 8))| ≤ M * (1 * B2) :=
    abs_mul_le' m1 (abs_mul_le' c1 b2)
  have hgc : |η x * ((3 : ℝ) / 16 * (4 * ε ^ 2 - x ^ 2) * (x ^ 2 + ε ^ 2) ^ (-(13 : ℝ) / 8))| ≤
      M * (1 * B3) := abs_mul_le' m0 (abs_mul_le' c2 b3)
  have hf1 : |deriv (cutoffCusp η ε) x| ≤ M * B1 + M * (1 * B2) := by
    rw [e1]
    exact (abs_add_le _ _).trans (add_le_add (abs_mul_le' m1 b1) hga)
  have hf2 : |iteratedDeriv 2 (cutoffCusp η ε) x| ≤
      M * B1 + 2 * (M * (1 * B2)) + M * (1 * B3) := by
    rw [e2]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (abs_mul_le' m2 b1) ?_)) hgc)
    rw [abs_mul, abs_two]
    linarith
  unfold cutoffCuspDensity
  exact dens_alg hf hf1 hf2

theorem periodic_deriv {f : ℝ → ℝ} (hf : Function.Periodic f 1) : Function.Periodic (deriv f) 1 := by
  intro x
  have h : (fun y : ℝ => f (y + 1)) = f := funext hf
  have := deriv_comp_add_const (f := f) (a := (1 : ℝ)) (x := x)
  rw [h] at this
  exact this.symm

theorem int_bound (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hε8 : ε < 1 / 8) (F : ℝ → ℝ)
    (hF : ContinuousOn F (Icc ε (1 / 8)))
    (hb : ∀ x ∈ Ioo ε (1 / 8), |F x| ≤ C * ε ^ 2 / x ^ 3) :
    ∫ x in ε..(1 / 8), |F x| ≤ C / 2 := by
  have hle : ε ≤ 1 / 8 := hε8.le
  have hint1 : IntervalIntegrable (fun x => |F x|) MeasureTheory.volume ε (1 / 8) :=
    hF.abs.intervalIntegrable_of_Icc hle
  have hne : ∀ x ∈ Icc ε (1 / 8), x ≠ 0 := fun x hx => by
    have := hx.1; exact (lt_of_lt_of_le hε this).ne'
  have hint2 : IntervalIntegrable (fun x : ℝ => C * ε ^ 2 * x ^ (-3 : ℤ)) MeasureTheory.volume ε (1 / 8) := by
    refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
    exact continuousOn_const.mul (continuousOn_id.zpow₀ (-3) (fun x hx => Or.inl (hne x hx)))
  have hmono : ∫ x in ε..(1 / 8), |F x| ≤ ∫ x in ε..(1 / 8), C * ε ^ 2 * x ^ (-3 : ℤ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hle hint1 hint2 (fun x hx => ?_)
    have h1 := hb x hx
    have e : C * ε ^ 2 / x ^ 3 = C * ε ^ 2 * x ^ (-3 : ℤ) := by
      rw [div_eq_mul_inv, zpow_neg]; norm_cast
    rw [e] at h1; exact h1
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  have h0 : (0 : ℝ) ∉ Set.uIcc ε (1 / 8) := by
    rw [Set.uIcc_of_le hle]; intro h0; linarith [h0.1]
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  have e2 : ε ^ 2 * ε ^ (-2 : ℤ) = 1 := by
    rw [zpow_neg, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; field_simp
  have e3 : ((1 : ℝ) / 8) ^ (-3 + 1 : ℤ) = 64 := by norm_num
  have e4 : ε ^ (-3 + 1 : ℤ) = ε ^ (-2 : ℤ) := by norm_num
  rw [e3, e4]
  have hεpos : 0 ≤ ε ^ 2 := by positivity
  have : C * ε ^ 2 * ((64 - ε ^ (-2 : ℤ)) / ((-3 : ℤ) + 1 : ℝ)) = C / 2 * (1 - 64 * ε ^ 2) := by
    have e5 : (((-3 : ℤ) : ℝ) + 1) = -2 := by norm_num
    rw [e5]
    have : C * ε ^ 2 * ((64 - ε ^ (-2 : ℤ)) / (-2)) = C / 2 * (ε ^ 2 * ε ^ (-2 : ℤ) - 64 * ε ^ 2) := by ring
    rw [this, e2]
  rw [this]
  nlinarith [mul_nonneg hC hεpos]

theorem main_est (η : ℝ → ℝ) (hη : IsCuspCutoff η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 8 →
      |∫ x in (-ε)..ε, cutoffCuspDensity η ε x| ≤ C ∧
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < (1 : ℝ) / 8},
        |cutoffCuspDensity η ε x + (441 / 256 : ℝ) / (|x|)|) ≤ C ∧
      (∫ x in {x : ℝ | (1 : ℝ) / 8 ≤ |x| ∧ |x| ≤ (1 : ℝ) / 2},
        |cutoffCuspDensity η ε x|) ≤ C ∧
      |q6QuarticF38 (cutoffCusp η ε) + (441 / 128 : ℝ) * Real.log (1 / ε)| ≤ C := by
  obtain ⟨C0, hC0, hf⟩ := f034 η hη
  obtain ⟨B, hB⟩ := region_bound η hη
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  refine ⟨24 + C0 + 2 * |B| + (441 / 128) * Real.log 8, by positivity, ?_⟩
  intro ε hε hε8
  obtain ⟨_, hcd, hper, hloc, hann⟩ := hf ε hε hε8
  have hle : ε ≤ 1 / 8 := hε8.le
  -- continuity of the density
  have hid : iteratedDeriv 2 (cutoffCusp η ε) = deriv (deriv (cutoffCusp η ε)) := by
    funext x; rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hc1 : ContDiff ℝ ∞ (deriv (cutoffCusp η ε)) := (contDiff_infty_iff_deriv.1 hcd).2
  have hc2 : ContDiff ℝ ∞ (deriv (deriv (cutoffCusp η ε))) := (contDiff_infty_iff_deriv.1 hc1).2
  have hDc : Continuous (cutoffCuspDensity η ε) := by
    unfold cutoffCuspDensity
    rw [hid]
    have := hcd.continuous; have := hc1.continuous; have := hc2.continuous
    fun_prop
  have hDint : ∀ a b : ℝ, IntervalIntegrable (cutoffCuspDensity η ε) MeasureTheory.volume a b :=
    fun a b => hDc.intervalIntegrable a b
  -- the corrected integrand and its bounds
  set g : ℝ → ℝ := fun x => cutoffCuspDensity η ε x + (441 / 256 : ℝ) / |x| with hg
  have hgc : ∀ a b : ℝ, 0 < a → a ≤ b → ContinuousOn g (Icc a b) := by
    intro a b ha hab
    refine hDc.continuousOn.add (continuousOn_const.div (continuous_abs.continuousOn) ?_)
    intro x hx
    have : 0 < x := lt_of_lt_of_le ha hx.1
    exact (abs_pos.2 this.ne').ne'
  have hgcn : ∀ a b : ℝ, b < 0 → a ≤ b → ContinuousOn g (Icc a b) := by
    intro a b hb hab
    refine hDc.continuousOn.add (continuousOn_const.div (continuous_abs.continuousOn) ?_)
    intro x hx
    have : x < 0 := lt_of_le_of_lt hx.2 hb
    exact (abs_pos.2 this.ne).ne'
  have hbp : ∫ x in ε..(1 / 8), |g x| ≤ C0 / 2 := by
    refine int_bound C0 ε hC0 hε hε8 g (hgc ε (1 / 8) hε hle) (fun x hx => ?_)
    have hxp : 0 < x := lt_trans hε hx.1
    have := (hann x (by rw [abs_of_pos hxp]; exact hx.1) (by rw [abs_of_pos hxp]; exact hx.2)).2.2
    rw [abs_of_pos hxp] at this
    show |cutoffCuspDensity η ε x + (441 / 256 : ℝ) / (|x|)| ≤ _
    rw [abs_of_pos hxp]
    exact this
  have hbm : ∫ x in ε..(1 / 8), |g (-x)| ≤ C0 / 2 := by
    refine int_bound C0 ε hC0 hε hε8 (fun x => g (-x)) ?_ (fun x hx => ?_)
    · have h1 := hgcn (-(1 / 8)) (-ε) (by linarith) (by linarith)
      have h2 : ContinuousOn (fun x : ℝ => -x) (Icc ε (1 / 8)) := continuous_neg.continuousOn
      refine h1.comp h2 (fun x hx => ?_)
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    · have hxp : 0 < x := lt_trans hε hx.1
      have habs : |-x| = x := by rw [abs_neg, abs_of_pos hxp]
      have := (hann (-x) (by rw [habs]; exact hx.1) (by rw [habs]; exact hx.2)).2.2
      rw [habs] at this
      show |cutoffCuspDensity η ε (-x) + (441 / 256 : ℝ) / (|-x|)| ≤ _
      rw [habs]
      exact this
  have hA : |∫ x in (-ε)..ε, cutoffCuspDensity η ε x| ≤ 24 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -ε) (b := ε)
      (f := cutoffCuspDensity η ε) (C := 12 / ε) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hx' : |x| ≤ ε := abs_le.2 ⟨hx.1.le, hx.2⟩
        simpa using core_bound η hη ε hε hε8 x hx')
    have e : 12 / ε * |ε - -ε| = 24 := by
      rw [show ε - -ε = 2 * ε by ring, abs_of_pos (by positivity)]; field_simp; ring
    rw [e] at h
    exact Real.norm_eq_abs _ ▸ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a)
    have : (24 : ℝ) ≤ 24 + C0 + 2 * |B| + (441 / 128) * Real.log 8 := by
      have := abs_nonneg B; nlinarith
    exact hA.trans this
  · -- (b)
    show ∫ x in {x : ℝ | ε < |x| ∧ |x| < (1 : ℝ) / 8}, |g x| ≤ _
    have hS : {x : ℝ | ε < |x| ∧ |x| < (1 : ℝ) / 8} = Ioo (-(1 / 8)) (-ε) ∪ Ioo ε (1 / 8) := by
      ext x
      simp only [mem_setOf_eq, mem_union, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_abs.1 h1 with h | h
        · right; exact ⟨h, (le_abs_self x).trans_lt h2⟩
        · left; exact ⟨(abs_lt.1 h2).1, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨?_, ?_⟩
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact ⟨h1, h2⟩
    have hdisj : Disjoint (Ioo (-(1 / 8) : ℝ) (-ε)) (Ioo ε (1 / 8)) :=
      Set.disjoint_left.2 fun x h1 h2 => by linarith [h1.2, h2.1]
    have hI1 : MeasureTheory.IntegrableOn (fun x => |g x|) (Ioo (-(1 / 8) : ℝ) (-ε)) :=
      ((hgcn (-(1 / 8)) (-ε) (by linarith) (by linarith)).abs.integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
    have hI2 : MeasureTheory.IntegrableOn (fun x => |g x|) (Ioo ε (1 / 8)) :=
      ((hgc ε (1 / 8) hε hle).abs.integrableOn_Icc).mono_set Ioo_subset_Icc_self
    rw [hS, MeasureTheory.setIntegral_union hdisj measurableSet_Ioo hI1 hI2]
    have e1 : ∫ x in Ioo ε (1 / 8), |g x| = ∫ x in ε..(1 / 8), |g x| := by
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have e2 : ∫ x in Ioo (-(1 / 8) : ℝ) (-ε), |g x| = ∫ x in ε..(1 / 8), |g (-x)| := by
      rw [intervalIntegral.integral_comp_neg (fun x => |g x|) (a := ε) (b := 1 / 8),
        intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [e1, e2]
    have : (C0 : ℝ) ≤ 24 + C0 + 2 * |B| + (441 / 128) * Real.log 8 := by
      have := abs_nonneg B; nlinarith
    linarith
  · -- (c)
    set S : Set ℝ := {x : ℝ | (1 : ℝ) / 8 ≤ |x| ∧ |x| ≤ (1 : ℝ) / 2} with hS
    have hsub : S ⊆ Icc (-(1 / 2) : ℝ) (1 / 2) := fun x hx => abs_le.1 hx.2
    have hvol : MeasureTheory.volume S < ⊤ := (MeasureTheory.measure_mono hsub).trans_lt (by simp)
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (f := fun x => |cutoffCuspDensity η ε x|) (C := |B|) hvol
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (hB ε hε hε8 x hx.1 hx.2).trans (le_abs_self B))
    have hvr : MeasureTheory.volume.real S ≤ 1 := by
      have := MeasureTheory.measureReal_mono (μ := MeasureTheory.volume) hsub (by simp)
      have e : MeasureTheory.volume.real (Icc (-(1 / 2) : ℝ) (1 / 2)) = 1 := by
        rw [Real.volume_real_Icc_of_le (by norm_num)]; norm_num
      linarith
    have hnn : ∫ x in S, |cutoffCuspDensity η ε x| ≤ |B| * MeasureTheory.volume.real S :=
      (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact h)
    have : |B| * MeasureTheory.volume.real S ≤ |B| := by
      have := abs_nonneg B
      nlinarith
    have hB0 := abs_nonneg B
    show ∫ x in S, |cutoffCuspDensity η ε x| ≤ _
    nlinarith
  · -- (d)
    have hpd1 := periodic_deriv hper
    have hpd2 := periodic_deriv hpd1
    have hperD : Function.Periodic (cutoffCuspDensity η ε) 1 := by
      intro x
      unfold cutoffCuspDensity
      rw [hid, hper x, hpd1 x, hpd2 x]
    have hq : q6QuarticF38 (cutoffCusp η ε) = ∫ x in (0 : ℝ)..1, cutoffCuspDensity η ε x := rfl
    have hshift : ∫ x in (0 : ℝ)..1, cutoffCuspDensity η ε x =
        ∫ x in (-(1 / 2) : ℝ)..(1 / 2), cutoffCuspDensity η ε x := by
      have h := hperD.intervalIntegral_add_eq 0 (-(1 / 2) : ℝ)
      have e : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
      rw [zero_add, e] at h
      exact h
    set D : ℝ → ℝ := cutoffCuspDensity η ε with hD
    have s1 := (intervalIntegral.integral_add_adjacent_intervals (hDint (-(1 / 2)) (-(1 / 8)))
      (hDint (-(1 / 8)) (1 / 2)))
    have s2 := (intervalIntegral.integral_add_adjacent_intervals (hDint (-(1 / 8)) (-ε)) (hDint (-ε) (1 / 2)))
    have s3 := (intervalIntegral.integral_add_adjacent_intervals (hDint (-ε) ε) (hDint ε (1 / 2)))
    have s4 := (intervalIntegral.integral_add_adjacent_intervals (hDint ε (1 / 8)) (hDint (1 / 8) (1 / 2)))
    -- far pieces
    have hP1 : |∫ x in (1 / 8 : ℝ)..(1 / 2), D x| ≤ |B| * (3 / 8) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 / 8) (b := 1 / 2) (f := D)
        (C := |B|) (fun x hx => by
          rw [Set.uIoc_of_le (by norm_num)] at hx
          have hxp : 0 < x := by linarith [hx.1]
          rw [Real.norm_eq_abs]
          exact (hB ε hε hε8 x (by rw [abs_of_pos hxp]; exact hx.1.le) (by rw [abs_of_pos hxp]; exact hx.2)).trans
            (le_abs_self B))
      rw [Real.norm_eq_abs] at h
      have e : |(1 / 2 : ℝ) - 1 / 8| = 3 / 8 := by norm_num [abs_of_pos]
      rw [e] at h; exact h
    have hP5 : |∫ x in (-(1 / 2) : ℝ)..(-(1 / 8)), D x| ≤ |B| * (3 / 8) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -(1 / 2)) (b := -(1 / 8)) (f := D)
        (C := |B|) (fun x hx => by
          rw [Set.uIoc_of_le (by norm_num)] at hx
          have hxn : x < 0 := by linarith [hx.2]
          rw [Real.norm_eq_abs]
          exact (hB ε hε hε8 x (by rw [abs_of_neg hxn]; linarith [hx.2]) (by rw [abs_of_neg hxn]; linarith [hx.1])).trans
            (le_abs_self B))
      rw [Real.norm_eq_abs] at h
      have e : |(-(1 / 8) : ℝ) - -(1 / 2)| = 3 / 8 := by norm_num [abs_of_pos]
      rw [e] at h; exact h
    -- near pieces
    have hcgp : IntervalIntegrable (fun x : ℝ => (441 / 256 : ℝ) / |x|) MeasureTheory.volume ε (1 / 8) := by
      refine ContinuousOn.intervalIntegrable_of_Icc hle (continuousOn_const.div continuous_abs.continuousOn ?_)
      intro x hx
      exact (abs_pos.2 (lt_of_lt_of_le hε hx.1).ne').ne'
    have hcgn : IntervalIntegrable (fun x : ℝ => (441 / 256 : ℝ) / |x|) MeasureTheory.volume (-(1 / 8)) (-ε) := by
      refine ContinuousOn.intervalIntegrable_of_Icc (by linarith) (continuousOn_const.div continuous_abs.continuousOn ?_)
      intro x hx
      exact (abs_pos.2 (lt_of_le_of_lt hx.2 (by linarith)).ne).ne'
    have hgp : IntervalIntegrable g MeasureTheory.volume ε (1 / 8) :=
      (hgc ε (1 / 8) hε hle).intervalIntegrable_of_Icc hle
    have hgm : IntervalIntegrable g MeasureTheory.volume (-(1 / 8)) (-ε) :=
      (hgcn (-(1 / 8)) (-ε) (by linarith) (by linarith)).intervalIntegrable_of_Icc (by linarith)
    have hDg : ∀ x, D x = g x - (441 / 256 : ℝ) / |x| := fun x => by simp [hg, hD]
    have Dp : ∫ x in ε..(1 / 8), D x = (∫ x in ε..(1 / 8), g x) - ∫ x in ε..(1 / 8), (441 / 256 : ℝ) / |x| := by
      rw [← intervalIntegral.integral_sub hgp hcgp]
      exact intervalIntegral.integral_congr (fun x _ => hDg x)
    have Dm : ∫ x in (-(1 / 8))..(-ε), D x = (∫ x in (-(1 / 8))..(-ε), g x) -
        ∫ x in (-(1 / 8))..(-ε), (441 / 256 : ℝ) / |x| := by
      rw [← intervalIntegral.integral_sub hgm hcgn]
      exact intervalIntegral.integral_congr (fun x _ => hDg x)
    have Lp : ∫ x in ε..(1 / 8), (441 / 256 : ℝ) / |x| = (441 / 256 : ℝ) * Real.log ((1 / 8) / ε) := by
      have : ∫ x in ε..(1 / 8), (441 / 256 : ℝ) / |x| = ∫ x in ε..(1 / 8), (441 / 256 : ℝ) * x⁻¹ := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le hle] at hx
        have : 0 < x := lt_of_lt_of_le hε hx.1
        simp only [abs_of_pos this, div_eq_mul_inv]
      rw [this, intervalIntegral.integral_const_mul, integral_inv_of_pos hε (by norm_num)]
    have Lm : ∫ x in (-(1 / 8))..(-ε), (441 / 256 : ℝ) / |x| =
        -((441 / 256 : ℝ) * Real.log ((-ε) / (-(1 / 8)))) := by
      have : ∫ x in (-(1 / 8))..(-ε), (441 / 256 : ℝ) / |x| =
          ∫ x in (-(1 / 8))..(-ε), -((441 / 256 : ℝ) * x⁻¹) := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le (by linarith)] at hx
        have : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
        simp only [abs_of_neg this, div_neg, div_eq_mul_inv]
        rw [inv_neg]; ring
      rw [this, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
        integral_inv_of_neg (by linarith) (by linarith)]
    have hGp : |∫ x in ε..(1 / 8), g x| ≤ C0 / 2 := by
      have := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := g) hle
      simp only [Real.norm_eq_abs] at this
      exact this.trans hbp
    have hGm : |∫ x in (-(1 / 8))..(-ε), g x| ≤ C0 / 2 := by
      have h1 : ∫ x in ε..(1 / 8), g (-x) = ∫ x in (-(1 / 8))..(-ε), g x :=
        intervalIntegral.integral_comp_neg (fun x => g x) (a := ε) (b := 1 / 8)
      rw [← h1]
      have := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := fun x => g (-x)) hle
      simp only [Real.norm_eq_abs] at this
      exact this.trans hbm
    have l1 : Real.log ((1 / 8) / ε) = -Real.log 8 - Real.log ε := by
      rw [Real.log_div (by norm_num) hε.ne', one_div, Real.log_inv]
    have l2 : Real.log ((-ε) / (-(1 / 8))) = Real.log 8 + Real.log ε := by
      have : (-ε) / (-(1 / 8) : ℝ) = 8 * ε := by field_simp
      rw [this, Real.log_mul (by norm_num) hε.ne']
    have l3 : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
    rw [hq, hshift, l3]
    have htot : ∫ x in (-(1 / 2) : ℝ)..(1 / 2), D x =
        (∫ x in (-(1 / 2) : ℝ)..(-(1 / 8)), D x) + (∫ x in (-(1 / 8) : ℝ)..(-ε), D x) +
          (∫ x in (-ε)..ε, D x) + (∫ x in ε..(1 / 8), D x) + ∫ x in (1 / 8 : ℝ)..(1 / 2), D x := by
      linarith [s1, s2, s3, s4]
    rw [htot, Dp, Dm, Lp, Lm, l1, l2]
    have hlog := hlog8
    have habsB := abs_nonneg B
    rw [abs_le] at hP1 hP5 hA hGp hGm
    rw [abs_le]
    constructor <;> linarith [hP1.1, hP1.2, hP5.1, hP5.2, hA.1, hA.2, hGp.1, hGp.2, hGm.1, hGm.2]

end F035Aux

open F035Aux in
theorem f035 (η : ℝ → ℝ) (hη : IsCuspCutoff η) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 8 →
      |∫ x in (-ε)..ε, cutoffCuspDensity η ε x| ≤ C ∧
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < (1 : ℝ) / 8},
        |cutoffCuspDensity η ε x + (441 / 256 : ℝ) / (|x|)|) ≤ C ∧
      (∫ x in {x : ℝ | (1 : ℝ) / 8 ≤ |x| ∧ |x| ≤ (1 : ℝ) / 2},
        |cutoffCuspDensity η ε x|) ≤ C ∧
      |q6QuarticF38 (cutoffCusp η ε) + (441 / 128 : ℝ) * Real.log (1 / ε)| ≤ C) ∧
    (∃ ε : ℝ, 0 < ε ∧ ε < (1 : ℝ) / 8 ∧
      q6QuarticF38 (cutoffCusp η ε) < 0) ∧
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ q6QuarticF38 f < 0 := by
  obtain ⟨C, hC0, hC⟩ := main_est η hη
  obtain ⟨C0, hC00, hf⟩ := f034 η hη
  have hex : ∃ ε : ℝ, 0 < ε ∧ ε < (1 : ℝ) / 8 ∧ q6QuarticF38 (cutoffCusp η ε) < 0 := by
    set T : ℝ := 128 * C / 441 + 1 with hT
    have hT0 : 0 ≤ T := by rw [hT]; positivity
    have hε : 0 < (1 / 16 : ℝ) * Real.exp (-T) := by positivity
    have hexp : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hε8 : (1 / 16 : ℝ) * Real.exp (-T) < 1 / 8 := by nlinarith
    refine ⟨(1 / 16 : ℝ) * Real.exp (-T), hε, hε8, ?_⟩
    have h := (hC _ hε hε8).2.2.2
    rw [abs_le] at h
    have hl : Real.log (1 / ((1 / 16 : ℝ) * Real.exp (-T))) = Real.log 16 + T := by
      have : 1 / ((1 / 16 : ℝ) * Real.exp (-T)) = 16 * Real.exp T := by
        rw [Real.exp_neg]; field_simp
      rw [this, Real.log_mul (by norm_num) (Real.exp_pos T).ne', Real.log_exp]
    rw [hl] at h
    have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have hTe : (441 / 128 : ℝ) * T = C + 441 / 128 := by rw [hT]; ring
    nlinarith [h.2]
  refine ⟨⟨C, hC0, fun ε hε hε8 => hC ε hε hε8⟩, hex, ?_⟩
  obtain ⟨ε, hε, hε8, hq⟩ := hex
  obtain ⟨_, hcd, hper, _⟩ := hf ε hε hε8
  exact ⟨cutoffCusp η ε, hcd, hper, hq⟩


end
end NlsGge.ThirdConsultation.F
