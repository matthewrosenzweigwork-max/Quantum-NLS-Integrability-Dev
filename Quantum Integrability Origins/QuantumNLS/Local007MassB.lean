import Mathlib
import QuantumNLS.Local007MassA
import QuantumNLS.Local007Zeros
import QuantumNLS.RootGapLevelSets

/-! LOCAL-007 stage M2: the mass of the free cell `(-π/L, π/L)` as a semicircle transform.

If `Δ_v² - 4 = ((z-α)² - t²) H` with `H` entire, real on `ℝ`, `|H + L²| ≤ L²/4` on `|z| ≤ 3d`
(`d = 1/(16L)`), `|α|+t ≤ d/40`, and `|Re Δ_v(x) - 2cos(Lx/2)| ≤ 1/400` for `|x| ≤ π/L`, then
`μ_v((-π/L, π/L)) = (L t²/(4κ)) Re Phi(F, α, t²)` for any `F` with `F θ = Δ_v(c e^{iθ})`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Interval
namespace QuantumNLS.Local007MassB
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Zeros (Dl real_of_re)
open QuantumNLS.Local007AlgB (cOm Phi A)
open QuantumNLS.Local007EvalT (OmC sqF Dtrue Phi_eval)
open QuantumNLS.RootDensity (hfun)
open QuantumNLS.RootDensityIdentification (dens)
variable {L κ : ℝ}

/-- The real series `Ω(s)`. -/
def Omr (s : ℝ) : ℝ := ∑' j : ℕ, cOm j * s ^ j

theorem OmC_ofReal (s : ℝ) : OmC (s : ℂ) = ((Omr s : ℝ) : ℂ) := by
  unfold OmC Omr
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  push_cast; ring

/-- The real-axis form of `D`: for real `h ≤ 0` and real `s ∈ [0,1)`. -/
theorem Dtrue_real {H f : ℂ → ℂ} {x : ℝ} {h s : ℝ} (hh : H (x : ℂ) = (h : ℂ)) (hf : f (x : ℂ) / 4 = (s : ℂ))
    (hneg : h ≤ 0) :
    Dtrue L H f (x : ℂ) = (((L / 2) * Real.sqrt (-h / L ^ 2) * Omr s : ℝ) : ℂ) := by
  unfold Dtrue sqF
  rw [hh, hf, OmC_ofReal]
  have e : (((-(L ^ 2)⁻¹ : ℝ) : ℂ) * (h : ℂ)) = ((-h / L ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hnn : 0 ≤ -h / L ^ 2 := by
    have : 0 ≤ -h := by linarith
    positivity
  rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hnn,
    ← Real.sqrt_eq_rpow]
  push_cast; ring


/-! ### Real-axis facts for the cofactor -/

theorem H_real_bounds {L : ℝ} (hL : 0 < L) {H : ℂ → ℂ} (hHre : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) {x : ℝ}
    (hx : |x| ≤ 3 * (1 / (16 * L))) :
    H (x : ℂ) = (((H (x : ℂ)).re : ℝ) : ℂ) ∧ -(5 / 4) * L ^ 2 ≤ (H (x : ℂ)).re ∧ (H (x : ℂ)).re ≤ -(3 / 4) * L ^ 2 := by
  have hr : H (x : ℂ) = (((H (x : ℂ)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hHre x)
  refine ⟨hr, ?_⟩
  have h1 := hHb (x : ℂ) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [hr] at h1
  have e : (((H (x : ℂ)).re : ℝ) : ℂ) + (L : ℂ) ^ 2 = (((H (x : ℂ)).re + L ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h1
  have := abs_le.1 h1
  constructor <;> linarith [this.1, this.2]

theorem real_eq {Δ H : ℂ → ℂ} {α t : ℝ}
    (hfH : ∀ z, Δ z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z) (hΔr : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    {x h : ℝ} (hh : H (x : ℂ) = (h : ℂ)) :
    (Δ (x : ℂ)).re ^ 2 - 4 = ((x - α) ^ 2 - t ^ 2) * h := by
  have hD : Δ (x : ℂ) = (((Δ (x : ℂ)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hΔr x)
  have := hfH (x : ℂ)
  rw [hD, hh] at this
  have h2 : (((Δ (x : ℂ)).re ^ 2 - 4 : ℝ) : ℂ) = ((((x - α) ^ 2 - t ^ 2) * h : ℝ) : ℂ) := by
    push_cast; rw [← this]
  exact_mod_cast h2

theorem hfun_zero_of_lt {r : ℝ} (hr : r < 2) : hfun r = 0 := by
  unfold hfun; rw [if_neg (not_lt.2 hr.le)]


theorem gap_id {L : ℝ} (hL : 0 < L) {Δ H : ℂ → ℂ} {α t : ℝ} (ht : 0 ≤ t)
    (hαt : |α| + t ≤ (1 / (16 * L)) / 40)
    (hfH : ∀ z, Δ z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z) (hΔr : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    (hHre : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4) {x : ℝ}
    (hx : |x - α| ≤ t) :
    ∃ r : ℝ, Dtrue L H (fun z => Δ z ^ 2 - 4) (x : ℂ) = (r : ℂ) ∧
      hfun |(Δ (x : ℂ)).re| = Real.sqrt (t ^ 2 - (x - α) ^ 2) * r := by
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hL2d2 : L ^ 2 * d ^ 2 = 1 / 256 := by
    have : L * d = 1 / 16 := by rw [hd]; field_simp
    calc L ^ 2 * d ^ 2 = (L * d) ^ 2 := by ring
      _ = 1 / 256 := by rw [this]; norm_num
  have hx3 : |x| ≤ 3 * d := by
    have h1 : |x| ≤ |x - α| + |α| := by
      calc |x| = |(x - α) + α| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    nlinarith [abs_nonneg α]
  obtain ⟨hhr, hlo, hhi⟩ := H_real_bounds hL hHre hHb hx3
  set h : ℝ := (H (x : ℂ)).re with hh
  set D : ℝ := (Δ (x : ℂ)).re with hD
  have hDc : Δ (x : ℂ) = (D : ℂ) := Complex.ext (by simp [hD]) (by simpa [hD] using hΔr x)
  have heq := real_eq hfH hΔr hhr
  rw [← hD] at heq
  set g : ℝ := t ^ 2 - (x - α) ^ 2 with hg
  have hg0 : 0 ≤ g := by
    have : (x - α) ^ 2 ≤ t ^ 2 := by
      have := abs_le.1 hx
      nlinarith [this.1, this.2]
    linarith
  set m : ℝ := -h with hm
  have hm0 : 0 ≤ m := by linarith [hhi, sq_nonneg L]
  have hm1 : m ≤ (5 / 4) * L ^ 2 := by linarith
  set s : ℝ := g * m / 4 with hs
  have hs0 : 0 ≤ s := by positivity
  have hDs : D ^ 2 = 4 + 4 * s := by rw [hs]; nlinarith [heq]
  have hs1 : s < 1 := by
    have hgt : g ≤ (d / 40) ^ 2 := by
      have : t ≤ d / 40 := by linarith [abs_nonneg α]
      have : t ^ 2 ≤ (d / 40) ^ 2 := pow_le_pow_left₀ ht this 2
      nlinarith [sq_nonneg (x - α)]
    have : s ≤ (d / 40) ^ 2 * ((5 / 4) * L ^ 2) / 4 := by
      rw [hs]; gcongr
    have h2 : (d / 40) ^ 2 * ((5 / 4) * L ^ 2) / 4 = (1 / 5120) * (L ^ 2 * d ^ 2) := by ring
    rw [h2, hL2d2] at this
    linarith
  -- the density value
  have hfunD : hfun |D| = Real.arsinh (Real.sqrt s) := by
    unfold hfun
    by_cases h2 : 2 < |D|
    · rw [if_pos h2]
      have hD2 : |D| / 2 = Real.sqrt (1 + s) := by
        have h3 : (|D| / 2) ^ 2 = 1 + s := by rw [div_pow, sq_abs]; rw [hDs]; ring
        rw [← h3, Real.sqrt_sq (by positivity)]
      rw [hD2, QuantumNLS.Local007MassA.arcosh_sqrt hs0]
    · rw [if_neg h2]
      have hs00 : s = 0 := by
        have : |D| ^ 2 ≤ 4 := by nlinarith [abs_nonneg D]
        rw [sq_abs] at this
        nlinarith
      rw [hs00]; simp
  refine ⟨(L / 2) * Real.sqrt (-h / L ^ 2) * Omr s, ?_, ?_⟩
  · refine Dtrue_real hhr ?_ (by linarith [hhi, sq_nonneg L])
    show (Δ (x : ℂ) ^ 2 - 4) / 4 = (s : ℂ)
    rw [hDc]
    have e : (D : ℂ) ^ 2 - 4 = ((D ^ 2 - 4 : ℝ) : ℂ) := by push_cast; ring
    rw [e, show D ^ 2 - 4 = 4 * s by linarith]
    push_cast; ring
  · show hfun |D| = _
    rw [hfunD, QuantumNLS.Local007MassA.arsinh_om hs0 hs1]
    have h1 : Real.sqrt s = Real.sqrt g * ((L / 2) * Real.sqrt (m / L ^ 2)) := by
      have e1 : s = g * (m / 4) := by rw [hs]; ring
      have e2 : m / 4 = (L / 2) ^ 2 * (m / L ^ 2) := by field_simp; ring
      rw [e1, Real.sqrt_mul hg0, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [h1]
    unfold Omr
    ring


theorem cos_three_thirtytwo : Real.cos (3 / 32) ≤ 996 / 1000 := by
  have h := Real.cos_bound (x := 3 / 32) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have := (abs_le.1 h).2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 32)] at this
  norm_num at this ⊢
  linarith

theorem hfun_zero_outside {L : ℝ} (hL : 0 < L) {Δ H : ℂ → ℂ} {α t : ℝ} (ht : 0 ≤ t)
    (hαt : |α| + t ≤ (1 / (16 * L)) / 40)
    (hfH : ∀ z, Δ z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z) (hΔr : ∀ x : ℝ, (Δ (x : ℂ)).im = 0)
    (hHre : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4)
    (hcl : ∀ x : ℝ, |x| ≤ Real.pi / L → |(Δ (x : ℂ)).re - 2 * Real.cos (L * x / 2)| ≤ 1 / 400)
    {x : ℝ} (hxw : |x| ≤ Real.pi / L) (hxg : t < |x - α|) : hfun |(Δ (x : ℂ)).re| = 0 := by
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hLd : L * d = 1 / 16 := by rw [hd]; field_simp
  apply hfun_zero_of_lt
  rw [abs_lt]
  by_cases hnear : |x| ≤ 3 * d
  · obtain ⟨hhr, hlo, hhi⟩ := H_real_bounds hL hHre hHb hnear
    have heq := real_eq hfH hΔr hhr
    have h1 : t ^ 2 < (x - α) ^ 2 := by
      have := pow_lt_pow_left₀ hxg ht (by norm_num : (2 : ℕ) ≠ 0)
      rwa [sq_abs] at this
    have h2 : (Δ (x : ℂ)).re ^ 2 < 4 := by
      have hneg : ((x - α) ^ 2 - t ^ 2) * (H (x : ℂ)).re < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by nlinarith [sq_nonneg L])
      linarith
    constructor <;> nlinarith [sq_nonneg ((Δ (x : ℂ)).re + 2), sq_nonneg ((Δ (x : ℂ)).re - 2)]
  · push Not at hnear
    have hcl' := abs_le.1 (hcl x hxw)
    have hy : 3 / 32 < L * |x| / 2 := by nlinarith
    have hy2 : L * |x| / 2 ≤ Real.pi / 2 := by
      have : L * |x| ≤ Real.pi := by
        have := mul_le_mul_of_nonneg_left hxw hL.le
        rwa [mul_div_cancel₀ _ hL.ne'] at this
      linarith
    have hcos : Real.cos (L * x / 2) = Real.cos (L * |x| / 2) := by
      rw [← Real.cos_abs (L * x / 2), abs_div, abs_mul, abs_of_pos hL]; norm_num
    have hc1 : Real.cos (L * |x| / 2) ≤ Real.cos (3 / 32) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three]) hy.le
    have hc2 : 0 ≤ Real.cos (L * |x| / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [abs_nonneg x, Real.pi_pos], hy2⟩
    have := cos_three_thirtytwo
    rw [hcos] at hcl'
    constructor <;> nlinarith [hcl'.1, hcl'.2]


theorem cell_mass [Fact (0 < L)] (hκ : 0 < κ) (v : L2T L) {c : ℝ} (hc : c = 1 / (8 * L)) {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) {α t : ℝ} (ht : 0 ≤ t) (hαt : |α| + t ≤ (1 / (16 * L)) / 40)
    (hfH : ∀ z, Dl κ v z ^ 2 - 4 = ((z - α) ^ 2 - (t : ℂ) ^ 2) * H z)
    (hHre : ∀ x : ℝ, (H (x : ℂ)).im = 0)
    (hHb : ∀ z : ℂ, ‖z‖ ≤ 3 * (1 / (16 * L)) → ‖H z + (L : ℂ) ^ 2‖ ≤ L ^ 2 / 4)
    (hcl : ∀ x : ℝ, |x| ≤ Real.pi / L → |(Dl κ v (x : ℂ)).re - 2 * Real.cos (L * x / 2)| ≤ 1 / 400)
    (F : A) (hF : ∀ θ, F θ = Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) :
    (QuantumNLS.PhysicalQuantumMeasure.measure hκ v (Ioo (-(Real.pi / L)) (Real.pi / L))).toReal =
      (L * t ^ 2 / (4 * κ)) * (Phi c L F α (t ^ 2)).re := by
  have hL : 0 < L := Fact.out
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hLd : L * d = 1 / 16 := by rw [hd]; field_simp
  have hΔr : ∀ x : ℝ, (Dl κ v (x : ℂ)).im = 0 := fun x =>
    QuantumNLS.L2DiscriminantRegularity.discriminant_real κ v x
  have hΔ : Differentiable ℂ (Dl κ v) := QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ v
  have hPhi := Phi_eval hL hc hΔ hH ht hαt hfH hHb F hF
  have hdπ : d < Real.pi / L := by
    rw [lt_div_iff₀ hL]; nlinarith [Real.pi_gt_three]
  -- measure as an integral of the density
  have hA : (QuantumNLS.PhysicalQuantumMeasure.measure hκ v (Ioo (-(Real.pi / L)) (Real.pi / L))).toReal =
      ∫ x in Ioo (-(Real.pi / L)) (Real.pi / L), dens κ v x := by
    rw [QuantumNLS.RootGapLevelSets.measure_eq_dens hκ v, withDensity_apply _ measurableSet_Ioo]
    rw [integral_eq_lintegral_of_nonneg_ae]
    · exact Filter.Eventually.of_forall fun x => QuantumNLS.RootDensityIdentification.dens_nonneg hκ v x
    · exact (QuantumNLS.RootDensityIdentification.continuous_dens κ v).aestronglyMeasurable
  have hsub : Icc (α - t) (α + t) ⊆ Ioo (-(Real.pi / L)) (Real.pi / L) := by
    intro x hx
    constructor <;> nlinarith [abs_nonneg α, neg_abs_le α, le_abs_self α, hx.1, hx.2]
  have hB : ∫ x in Ioo (-(Real.pi / L)) (Real.pi / L), dens κ v x = ∫ x in Icc (α - t) (α + t), dens κ v x := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hsub ?_
    intro x hx
    have hxw : |x| ≤ Real.pi / L := by
      rw [abs_le]; constructor <;> linarith [hx.1.1, hx.1.2]
    have hxg : t < |x - α| := by
      by_contra hcon
      push Not at hcon
      apply hx.2
      have := abs_le.1 hcon
      constructor <;> linarith [this.1, this.2]
    have := hfun_zero_outside hL ht hαt hfH hΔr hHre hHb hcl hxw hxg
    unfold dens
    rw [this, mul_zero]
  rw [hA, hB]
  rcases ht.eq_or_lt with ht0 | htpos
  · subst ht0
    simp
  -- t > 0 : change of variables
  have hgap : ∀ x : ℝ, |x - α| ≤ t → ∃ r : ℝ, Dtrue L H (fun z => Dl κ v z ^ 2 - 4) (x : ℂ) = (r : ℂ) ∧
      hfun |(Dl κ v (x : ℂ)).re| = Real.sqrt (t ^ 2 - (x - α) ^ 2) * r := fun x hx =>
    gap_id hL ht hαt hfH hΔr hHre hHb hx
  set rf : ℝ → ℝ := fun x => (Dtrue L H (fun z => Dl κ v z ^ 2 - 4) (x : ℂ)).re with hrf
  have hgap' : ∀ x : ℝ, |x - α| ≤ t → Dtrue L H (fun z => Dl κ v z ^ 2 - 4) (x : ℂ) = (rf x : ℂ) ∧
      hfun |(Dl κ v (x : ℂ)).re| = Real.sqrt (t ^ 2 - (x - α) ^ 2) * rf x := by
    intro x hx
    obtain ⟨r, hr1, hr2⟩ := hgap x hx
    have : rf x = r := by simp [hrf, hr1]
    rw [this]; exact ⟨hr1, hr2⟩
  have hint1 : ∫ x in Icc (α - t) (α + t), dens κ v x =
      ∫ x in (α - t)..(α + t), (Real.pi * κ)⁻¹ * (Real.sqrt (t ^ 2 - (x - α) ^ 2) * rf x) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    have hx' : |x - α| ≤ t := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    change (Real.pi * κ)⁻¹ * hfun |(Dl κ v (x : ℂ)).re| = _
    rw [(hgap' x hx').2]
  rw [hint1]
  have hcv := intervalIntegral.integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => (Real.pi * κ)⁻¹ * (Real.sqrt (t ^ 2 - (x - α) ^ 2) * rf x)) htpos.ne' α
  have hb1 : t * (-1 : ℝ) + α = α - t := by ring
  have hb2 : t * (1 : ℝ) + α = α + t := by ring
  rw [hb1, hb2] at hcv
  have hI : ∫ x in (α - t)..(α + t), (Real.pi * κ)⁻¹ * (Real.sqrt (t ^ 2 - (x - α) ^ 2) * rf x) =
      t * ∫ s in (-1 : ℝ)..1, (Real.pi * κ)⁻¹ * (Real.sqrt (t ^ 2 - (t * s + α - α) ^ 2) * rf (t * s + α)) := by
    rw [hcv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul]
  rw [hI]
  have hI2 : ∫ s in (-1 : ℝ)..1, (Real.pi * κ)⁻¹ * (Real.sqrt (t ^ 2 - (t * s + α - α) ^ 2) * rf (t * s + α)) =
      (Real.pi * κ)⁻¹ * t * ∫ s in (-1 : ℝ)..1, Real.sqrt (1 - s ^ 2) * rf (α + t * s) := by
    rw [mul_assoc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    have e1 : t ^ 2 - (t * s + α - α) ^ 2 = t ^ 2 * (1 - s ^ 2) := by ring
    rw [e1, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq htpos.le, show t * s + α = α + t * s by ring]
    ring
  rw [hI2]
  -- link with the complex integral
  have hcomplex : ∫ s in (-1 : ℝ)..1, ((Real.sqrt (1 - s ^ 2) : ℝ) : ℂ) *
        Dtrue L H (fun z => Dl κ v z ^ 2 - 4) ((α : ℂ) + (t : ℂ) * (s : ℂ)) =
      (((∫ s in (-1 : ℝ)..1, Real.sqrt (1 - s ^ 2) * rf (α + t * s) : ℝ)) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (by norm_num)] at hs
    have hx' : |(α + t * s) - α| ≤ t := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg ht]
      have : |s| ≤ 1 := abs_le.2 ⟨hs.1, hs.2⟩
      nlinarith [abs_nonneg s]
    have := (hgap' (α + t * s) hx').1
    have e : (((α + t * s : ℝ)) : ℂ) = (α : ℂ) + (t : ℂ) * (s : ℂ) := by push_cast; ring
    rw [e] at this
    rw [this]; push_cast; ring
  rw [hcomplex] at hPhi
  have hre : (Phi c L F α (t ^ 2)).re = 4 / (Real.pi * L) * ∫ s in (-1 : ℝ)..1, Real.sqrt (1 - s ^ 2) * rf (α + t * s) := by
    rw [hPhi, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre]
  field_simp

end QuantumNLS.Local007MassB
#print axioms QuantumNLS.Local007MassB.cell_mass
