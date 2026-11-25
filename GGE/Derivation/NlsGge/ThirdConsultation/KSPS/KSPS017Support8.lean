import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support4
import NlsGge.ThirdConsultation.KSPS.KSPS017Support7
import NlsGge.ThirdConsultation.KSPS.KSPS011Support11

/- KSPS-017 SUPPORT8 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS017Support8.lean.
   S017-2 core, generic form: if g is holomorphic on z != 0 and |g - Pdiag| <= C/|z|^2 on the strip
   {|z| >= L, |Im z| <= a + 1}, where Pdiag is the explicit core_decomp principal part
     Pdiag(z) = -u1 (2 i mu)^-1 endpointOsc mu c + e^{-i mu} (2 i mu)^-1 (J + Tz c d mu),   mu = sigma z,
   then indexWeight n * |g'(xi_n) + i (-1)^n J / (2 i xi_n)| is square summable along every admissible xi.
   Route (KSPS017_ROUTE.md item 3): fixed radius-1 Cauchy estimate for g - Pdiag (O(1/n^2)); exact derivative of
   Pdiag (hasDerivAt_endpointOsc, hasDerivAt_Tz); Bessel along xi (osc_sq_seq, Tz_seq_sq_summable);
   e^{-i sigma xi_n} = (-1)^n + O(1/n) (exp_lip, exp_neg_I_pi_int). Pdiag is a support-local literal abbreviation. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

/-- The explicit diagonal principal part (right side of KSPS012Support6.core_decomp, product form). -/
def Pdiag (σ : ℤ) (c d : ℝ → ℂ) (u1 J : ℂ) (z : ℂ) : ℂ :=
  -u1 * ((2 * Complex.I * ((σ : ℂ) * z))⁻¹ * KSPSWKB.endpointOsc ((σ : ℂ) * z) c) +
    Complex.exp (-(Complex.I * ((σ : ℂ) * z))) * (2 * Complex.I * ((σ : ℂ) * z))⁻¹ *
      (J + NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * z))

theorem hasDerivAt_Pdiag (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) {c d : ℝ → ℂ} (hc : IntervalIntegrable c volume 0 1)
    (hd : IntervalIntegrable d volume 0 1) (u1 J : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (Pdiag σ c d u1 J)
      (-u1 * ((-(2 * Complex.I * ((σ : ℂ) * z))⁻¹ * z⁻¹) * KSPSWKB.endpointOsc ((σ : ℂ) * z) c +
          (2 * Complex.I * ((σ : ℂ) * z))⁻¹ *
            (KSPSWKB.endpointOsc ((σ : ℂ) * z) (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * c t) * ((σ : ℂ) * 1))) +
        ((Complex.exp (-(Complex.I * ((σ : ℂ) * z))) * (-(Complex.I * ((σ : ℂ) * 1)))) *
            (2 * Complex.I * ((σ : ℂ) * z))⁻¹ +
          Complex.exp (-(Complex.I * ((σ : ℂ) * z))) * (-(2 * Complex.I * ((σ : ℂ) * z))⁻¹ * z⁻¹)) *
          (J + NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * z)) +
        Complex.exp (-(Complex.I * ((σ : ℂ) * z))) * (2 * Complex.I * ((σ : ℂ) * z))⁻¹ *
          ((2 * Complex.I * (NlsGge.ThirdConsultation.KSPS012Support5.Tz c (fun s => (s : ℂ) * d s) ((σ : ℂ) * z) -
            NlsGge.ThirdConsultation.KSPS012Support5.Tz (fun t => (t : ℂ) * c t) d ((σ : ℂ) * z))) * ((σ : ℂ) * 1))) z := by
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hm : HasDerivAt (fun w : ℂ => (σ : ℂ) * w) ((σ : ℂ) * 1) z := (hasDerivAt_id z).const_mul _
  have hne : 2 * Complex.I * ((σ : ℂ) * z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (mul_ne_zero hσ0 hz)
  have hρ : HasDerivAt (fun w : ℂ => (2 * Complex.I * ((σ : ℂ) * w))⁻¹)
      (-(2 * Complex.I * ((σ : ℂ) * z))⁻¹ * z⁻¹) z := by
    refine ((hm.const_mul (2 * Complex.I)).inv hne).congr_deriv ?_
    field_simp
  have hO := (hasDerivAt_endpointOsc hc ((σ : ℂ) * z)).comp z hm
  have hT := (hasDerivAt_Tz hc hd ((σ : ℂ) * z)).comp z hm
  have he : HasDerivAt (fun w : ℂ => Complex.exp (-(Complex.I * ((σ : ℂ) * w))))
      (Complex.exp (-(Complex.I * ((σ : ℂ) * z))) * (-(Complex.I * ((σ : ℂ) * 1)))) z :=
    (hm.const_mul Complex.I).neg.cexp
  have h := ((hρ.mul hO).const_mul (-u1)).add ((he.mul hρ).mul (hT.const_add J))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => ?_))).congr_deriv ?_
  · simp only [Pdiag, Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  · simp only [Pi.mul_apply, Function.comp_apply] <;> ring

theorem diag_pure (w X EA A Nn C : ℝ) (u1 J O OH T Ta Tb e eneg ρ ρ' σ ξ Ed D : ℂ)
    (hw : 0 < w) (hwX : w ≤ X) (hX1 : 1 ≤ X) (hNn : 0 < Nn) (hNX : Nn ≤ X) (hNw : Nn ≤ w)
    (hEA : 0 ≤ EA) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hξ : ‖ξ‖ = X) (hρn : ‖ρ‖ = 1 / (2 * X)) (hρ'n : ‖ρ'‖ ≤ 1 / (2 * X ^ 2)) (he : ‖e‖ ≤ EA) (hσ : ‖σ‖ = 1)
    (hρσ : σ * ρ = (2 * Complex.I * ξ)⁻¹)
    (hlead : ‖e - eneg‖ ≤ 2 * A / w) (hEd : ‖Ed‖ ≤ 4 * C / X ^ 2)
    (hD : D = Ed + (-u1 * (ρ' * O + ρ * (OH * (σ * 1))) +
        ((e * (-(Complex.I * (σ * 1)))) * ρ + e * ρ') * (J + T) +
        e * ρ * ((2 * Complex.I * (Ta - Tb)) * (σ * 1))) -
      -Complex.I * eneg / (2 * Complex.I * ξ) * J) :
    w * ‖D‖ ≤ ‖u1‖ * (‖O‖ + ‖OH‖) + 2 * EA * (‖T‖ + 2 * (‖Ta‖ + ‖Tb‖)) +
      (4 * C + EA * ‖J‖ + A * ‖J‖) * (1 / Nn) := by
  have hX0 : 0 < X := by linarith
  have hsplit : D = Ed + (-u1 * (ρ' * O + ρ * (OH * σ))) +
      (-Complex.I * (e - eneg) * (2 * Complex.I * ξ)⁻¹ * J) + e * ρ' * J +
      ((e * (-(Complex.I * σ))) * ρ + e * ρ') * T + e * ρ * ((2 * Complex.I * (Ta - Tb)) * σ) := by
    rw [hD]
    linear_combination (-Complex.I * e * J) * hρσ
  have hTd : ‖2 * Complex.I * (Ta - Tb)‖ ≤ 2 * (‖Ta‖ + ‖Tb‖) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
  have hρle : ‖ρ‖ ≤ 1 / (2 * X) := le_of_eq hρn
  have hwX2 : w / (2 * X) ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hiX : 1 / X ≤ 1 / Nn := one_div_le_one_div_of_le hNn hNX
  -- the six pieces, each times w
  have p1 : w * ‖Ed‖ ≤ 4 * C * (1 / Nn) := by
    calc w * ‖Ed‖ ≤ X * (4 * C / X ^ 2) := mul_le_mul hwX hEd (norm_nonneg _) hX0.le
      _ = 4 * C * (1 / X) := by field_simp
      _ ≤ 4 * C * (1 / Nn) := mul_le_mul_of_nonneg_left hiX (by positivity)
  have p2 : w * ‖-u1 * (ρ' * O + ρ * (OH * σ))‖ ≤ ‖u1‖ * (‖O‖ + ‖OH‖) := by
    have hρ'1 : ‖ρ'‖ ≤ 1 / (2 * X) := hρ'n.trans (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    have h1 : ‖ρ' * O + ρ * (OH * σ)‖ ≤ 1 / (2 * X) * (‖O‖ + ‖OH‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_mul, hσ, mul_one, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hρ'1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hρle (norm_nonneg _))
    rw [norm_mul, norm_neg]
    calc w * (‖u1‖ * ‖ρ' * O + ρ * (OH * σ)‖) ≤ w * (‖u1‖ * (1 / (2 * X) * (‖O‖ + ‖OH‖))) := by gcongr
      _ = ‖u1‖ * (w / (2 * X)) * (‖O‖ + ‖OH‖) := by ring
      _ ≤ ‖u1‖ * 1 * (‖O‖ + ‖OH‖) := by gcongr; linarith
      _ = ‖u1‖ * (‖O‖ + ‖OH‖) := by ring
  have p3 : w * ‖-Complex.I * (e - eneg) * (2 * Complex.I * ξ)⁻¹ * J‖ ≤ A * ‖J‖ * (1 / Nn) := by
    have hn : ‖(2 * Complex.I * ξ)⁻¹‖ = 1 / (2 * X) := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, hξ, one_div]
    rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, hn]
    calc w * (‖e - eneg‖ * (1 / (2 * X)) * ‖J‖) ≤ w * (2 * A / w * (1 / (2 * X)) * ‖J‖) := by gcongr
      _ = A * ‖J‖ * (1 / X) := by field_simp
      _ ≤ A * ‖J‖ * (1 / Nn) := mul_le_mul_of_nonneg_left hiX (by positivity)
  have p4 : w * ‖e * ρ' * J‖ ≤ EA * ‖J‖ * (1 / Nn) := by
    rw [norm_mul, norm_mul]
    calc w * (‖e‖ * ‖ρ'‖ * ‖J‖) ≤ X * (EA * (1 / (2 * X ^ 2)) * ‖J‖) := by gcongr
      _ = EA * ‖J‖ * (1 / X) / 2 := by field_simp
      _ ≤ EA * ‖J‖ * (1 / Nn) := by
        have := mul_le_mul_of_nonneg_left hiX (by positivity : 0 ≤ EA * ‖J‖)
        have h0 : 0 ≤ EA * ‖J‖ * (1 / X) := by positivity
        linarith
  have p5 : w * ‖((e * (-(Complex.I * σ))) * ρ + e * ρ') * T‖ ≤ EA * ‖T‖ := by
    have hρ'1 : ‖ρ'‖ ≤ 1 / (2 * X) := hρ'n.trans (by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
    have h1 : ‖(e * (-(Complex.I * σ))) * ρ + e * ρ'‖ ≤ EA * (1 / X) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I, hσ, mul_one, mul_one, norm_mul]
      have k1 := mul_le_mul he hρle (norm_nonneg _) hEA
      have k2 := mul_le_mul he hρ'1 (norm_nonneg _) hEA
      have : EA * (1 / (2 * X)) + EA * (1 / (2 * X)) = EA * (1 / X) := by field_simp; ring
      linarith
    rw [norm_mul]
    calc w * (‖(e * (-(Complex.I * σ))) * ρ + e * ρ'‖ * ‖T‖) ≤ X * (EA * (1 / X) * ‖T‖) := by gcongr
      _ = EA * ‖T‖ := by field_simp
  have p6 : w * ‖e * ρ * ((2 * Complex.I * (Ta - Tb)) * σ)‖ ≤ EA * (2 * (‖Ta‖ + ‖Tb‖)) := by
    rw [norm_mul, norm_mul, norm_mul, hσ, mul_one]
    calc w * (‖e‖ * ‖ρ‖ * ‖2 * Complex.I * (Ta - Tb)‖) ≤ X * (EA * (1 / (2 * X)) * (2 * (‖Ta‖ + ‖Tb‖))) := by
          gcongr
      _ = EA * (2 * (‖Ta‖ + ‖Tb‖)) / 2 := by field_simp
      _ ≤ EA * (2 * (‖Ta‖ + ‖Tb‖)) := by
        have : 0 ≤ EA * (2 * (‖Ta‖ + ‖Tb‖)) := by positivity
        linarith
  have hn : ‖D‖ ≤ ‖Ed‖ + ‖-u1 * (ρ' * O + ρ * (OH * σ))‖ +
      ‖-Complex.I * (e - eneg) * (2 * Complex.I * ξ)⁻¹ * J‖ + ‖e * ρ' * J‖ +
      ‖((e * (-(Complex.I * σ))) * ρ + e * ρ') * T‖ + ‖e * ρ * ((2 * Complex.I * (Ta - Tb)) * σ)‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  have hwn := mul_le_mul_of_nonneg_left hn hw.le
  have hT0 : 0 ≤ EA * ‖T‖ := by positivity
  have hTab : 0 ≤ EA * (2 * (‖Ta‖ + ‖Tb‖)) := by positivity
  have e1 : 2 * EA * (‖T‖ + 2 * (‖Ta‖ + ‖Tb‖)) = 2 * (EA * ‖T‖) + 2 * (EA * (2 * (‖Ta‖ + ‖Tb‖))) := by ring
  have e2 : (4 * C + EA * ‖J‖ + A * ‖J‖) * (1 / Nn) =
      4 * C * (1 / Nn) + EA * ‖J‖ * (1 / Nn) + A * ‖J‖ * (1 / Nn) := by ring
  rw [e1, e2]
  linarith [hwn, p1, p2, p3, p4, p5, p6]


theorem sq8_add {f g : ℤ → ℝ} (hf : Summable (fun n => f n ^ 2)) (hg : Summable (fun n => g n ^ 2)) :
    Summable (fun n => (f n + g n) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hf.mul_left 2).add (hg.mul_left 2))
  nlinarith [sq_nonneg (f n - g n)]

theorem sq8_mul {f : ℤ → ℝ} (K : ℝ) (hf : Summable (fun n => f n ^ 2)) :
    Summable (fun n => (K * f n) ^ 2) := by
  simp_rw [mul_pow]
  exact hf.mul_left _

theorem exp_neg_I_pi_int8 (σ n : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (-(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))) = (-1 : ℂ) ^ n := by
  have e : -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))) =
      ((-(σ * n) : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rcases hσ with rfl | rfl
  · rw [show -((1 : ℤ) * n) = -n by ring, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  · simp

/-- S017-2, generic form. -/
theorem diag_deriv_generic (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) {c d : ℝ → ℂ}
    (hcmem : MemLp c 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) (hcm : AEStronglyMeasurable c volume)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1) (hd : IntervalIntegrable d volume 0 1)
    (u1 J : ℂ) (a : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * Real.pi‖ ≤ a / indexWeight n)
    (g : ℂ → ℂ) (hgd : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ g z)
    (hstrip : ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ z : ℂ, z ≠ 0 → L ≤ ‖z‖ → |z.im| ≤ a + 1 →
      ‖g z - Pdiag σ c d u1 J z‖ ≤ C / ‖z‖ ^ 2) :
    Summable (fun n : ℤ => (indexWeight n *
      ‖deriv g (xi n) - -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * J‖) ^ 2) := by
  obtain ⟨C, L, hC, hL, happ⟩ := hstrip
  have hc1 : IntervalIntegrable c volume 0 1 := KSPSWKB.intervalIntegrable_of_memLp hcmem
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  have hσ0 : (σ : ℂ) ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  set H' : ℝ → ℂ := fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ) * c t with hH'def
  have hH'mem : MemLp H' 2 NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd c (fun t => Complex.I * ((1 - 2 * t : ℝ) : ℂ))
      hcmem (Continuous.continuousOn (by fun_prop))
  set ds : ℝ → ℂ := fun s => (s : ℂ) * d s with hdsdef
  set tc : ℝ → ℂ := fun t => (t : ℂ) * c t with htcdef
  have hds : IntervalIntegrable ds volume 0 1 :=
    hd.continuousOn_mul (by fun_prop : Continuous fun s : ℝ => (s : ℂ)).continuousOn
  have htcm : AEStronglyMeasurable tc volume :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).aestronglyMeasurable.mul hcm
  have htc1 : IntervalIntegrable tc volume 0 1 :=
    hc1.continuousOn_mul (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).continuousOn
  have htc2 : IntervalIntegrable (fun t => ‖tc t‖ ^ 2) volume 0 1 := by
    refine hc2.mono_fun ((htcm.norm.pow 2).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le zero_le_one] at ht
    simp only [htcdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
    have h1 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    calc t ^ 2 * ‖c t‖ ^ 2 ≤ 1 * ‖c t‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = ‖c t‖ ^ 2 := one_mul _
  -- square-summable sequences
  have SO := KSPSWKB.osc_sq_seq hcmem a ha xi hxi σ hσ
  have SOH := KSPSWKB.osc_sq_seq hH'mem a ha xi hxi σ hσ
  have ST := Tz_seq_sq_summable hcm hc1 hc2 hd a ha xi hxi σ hσ
  have STa := Tz_seq_sq_summable hcm hc1 hc2 hds a ha xi hxi σ hσ
  have STb := Tz_seq_sq_summable htcm htc1 htc2 hd a ha xi hxi σ hσ
  have S1 : Summable (fun n : ℤ => (1 / |(n : ℝ)|) ^ 2) := by
    have h0 := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    refine h0.congr (fun n => ?_)
    rw [div_pow, one_pow, sq_abs]
  set EA : ℝ := Real.exp a with hEA
  set K' : ℝ := 4 * C + EA * ‖J‖ + a * ‖J‖ with hK'
  have Stot : Summable (fun n : ℤ => (‖u1‖ * (‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c‖ +
      ‖KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H'‖) +
      2 * EA * (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n)‖ +
        2 * (‖NlsGge.ThirdConsultation.KSPS012Support5.Tz c ds ((σ : ℂ) * xi n)‖ +
          ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz tc d ((σ : ℂ) * xi n)‖)) +
      K' * (1 / |(n : ℝ)|)) ^ 2) :=
    sq8_add (sq8_add (sq8_mul _ (sq8_add SO SOH))
      (sq8_mul _ (sq8_add ST (sq8_mul 2 (sq8_add STa STb))))) (sq8_mul _ S1)
  set n0 : ℕ := ⌈a + L + 2⌉₊ with hn0
  refine Summable.of_norm_bounded_eventually Stot ?_
  filter_upwards [KSPSWKB.eventually_cofinite_natAbs n0] with n hn
  have hn0' : a + L + 2 ≤ (n0 : ℝ) := Nat.le_ceil _
  have hnabs : a + L + 2 ≤ |(n : ℝ)| := by
    have h1 : ((n0 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := Int.cast_le.2 hn
    rw [Int.cast_abs] at h1
    simp only [Int.cast_natCast] at h1
    linarith
  have hw1 := NlsGge.ThirdConsultation.KSPS.one_le_indexWeight n
  have hδ0 := hxi n
  have hπ : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hm0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hδa : a / indexWeight n ≤ a := div_le_self ha hw1
  have hX : |(n : ℝ)| + L + 2 ≤ ‖xi n‖ := by
    have h1 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
    rw [norm_sub_rev, hnpi] at h1
    have : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hπ hm0
    linarith
  have himξ : |(xi n).im| ≤ a := by
    have : (xi n).im = (xi n - (n : ℂ) * Real.pi).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans (hδ0.trans hδa)
  have hn1 : 1 ≤ |(n : ℝ)| := by linarith
  have hNn : 0 < |(n : ℝ)| := by linarith
  have hNw : |(n : ℝ)| ≤ indexWeight n := by
    unfold indexWeight; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n : ℝ)])
  have hwle : indexWeight n ≤ |(n : ℝ)| + 1 := by
    unfold indexWeight
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
    rw [this]; nlinarith
  have hwX : indexWeight n ≤ ‖xi n‖ := by linarith
  have hw0 : 0 < indexWeight n := by linarith
  have hX1 : 1 ≤ ‖xi n‖ := by linarith
  have hX2 : 2 ≤ ‖xi n‖ := by linarith
  have hz : xi n ≠ 0 := by intro h; rw [h, norm_zero] at hX2; norm_num at hX2
  -- Cauchy estimate for E = g - Pdiag
  set E : ℂ → ℂ := fun w => g w - Pdiag σ c d u1 J w with hEdef
  have hball : ∀ z ∈ Metric.closedBall (xi n) 1, ‖xi n‖ - 1 ≤ ‖z‖ ∧ |z.im| ≤ a + 1 := by
    intro z hzb
    rw [Metric.mem_closedBall, dist_eq_norm] at hzb
    have h1 := norm_sub_norm_le (xi n) z
    have h4 : ‖xi n - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hzb
    have h2 : |z.im - (xi n).im| ≤ ‖z - xi n‖ := by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
    have h3 := abs_sub_abs_le_abs_sub z.im (xi n).im
    constructor <;> linarith
  have hEdb : ∀ z ∈ Metric.closedBall (xi n) 1, DifferentiableAt ℂ E z := by
    intro z hzb
    have h := (hball z hzb).1
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h; linarith
    exact (hgd z hz0).sub (hasDerivAt_Pdiag σ hσ hc1 hd u1 J hz0).differentiableAt
  have hEs : ∀ z ∈ Metric.sphere (xi n) 1, ‖E z‖ ≤ 4 * C / ‖xi n‖ ^ 2 := by
    intro z hzs
    obtain ⟨h1, h2⟩ := hball z (Metric.sphere_subset_closedBall hzs)
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; linarith
    refine (happ z hz0 (by linarith) h2).trans ?_
    have hzpos : 0 < ‖z‖ := by linarith
    have hhalf : ‖xi n‖ / 2 ≤ ‖z‖ := by linarith
    have hsq : (‖xi n‖ / 2) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (by positivity) hhalf 2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 4 * C * ‖z‖ ^ 2 - C * ‖xi n‖ ^ 2 = 4 * C * (‖z‖ ^ 2 - (‖xi n‖ / 2) ^ 2) := by ring
    nlinarith [mul_nonneg hC (sub_nonneg.2 hsq)]
  have hcauchy := norm_deriv_le_of_sphere one_pos hEdb hEs
  rw [div_one] at hcauchy
  have hP := hasDerivAt_Pdiag σ hσ hc1 hd u1 J hz
  have h1 := ((hgd (xi n) hz).hasDerivAt.sub hP)
  have hE' : deriv E (xi n) = deriv g (xi n) - _ := h1.deriv
  -- facts for diag_pure
  have hρn : ‖(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹‖ = 1 / (2 * ‖xi n‖) := by
    rw [norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, hσn, mul_one, one_mul,
      one_div]
  have hρ'n : ‖-(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ * (xi n)⁻¹‖ ≤ 1 / (2 * ‖xi n‖ ^ 2) := by
    rw [norm_mul, norm_neg, hρn, norm_inv]
    apply le_of_eq; field_simp
  have hEAn : ‖Complex.exp (-(Complex.I * ((σ : ℂ) * xi n)))‖ ≤ EA := by
    rw [Complex.norm_exp, hEA]
    refine Real.exp_le_exp.2 ?_
    have hre : (-(Complex.I * ((σ : ℂ) * xi n))).re = ((σ : ℂ) * xi n).im := by simp
    rw [hre]
    have : |((σ : ℂ) * xi n).im| ≤ a := by rcases hσ with rfl | rfl <;> simpa using himξ
    exact (le_abs_self _).trans this
  have hρσ : (σ : ℂ) * (2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ = (2 * Complex.I * xi n)⁻¹ := by
    rcases hσ with rfl | rfl
    · simp
    · push_cast
      simp only [neg_one_mul, mul_neg, inv_neg, neg_neg]
  have hlead : ‖Complex.exp (-(Complex.I * ((σ : ℂ) * xi n))) - (-1 : ℂ) ^ n‖ ≤ 2 * a / indexWeight n := by
    rw [← exp_neg_I_pi_int8 σ n hσ]
    have hz0n : ‖Complex.exp (-(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))))‖ = 1 := by
      rw [exp_neg_I_pi_int8 σ n hσ, norm_zpow, norm_neg, norm_one, one_zpow]
    have hdiff : ‖-(Complex.I * ((σ : ℂ) * xi n)) - -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ)))‖ =
        ‖xi n - (n : ℂ) * Real.pi‖ := by
      have e : -(Complex.I * ((σ : ℂ) * xi n)) - -(Complex.I * (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))) =
          (-(Complex.I * (σ : ℂ))) * (xi n - (n : ℂ) * Real.pi) := by push_cast; ring
      rw [e, norm_mul, norm_neg, norm_mul, Complex.norm_I, hσn, one_mul, one_mul]
    have hle1 : ‖xi n - (n : ℂ) * Real.pi‖ ≤ 1 := by
      refine hδ0.trans ?_
      rw [div_le_one hw0]; linarith
    refine (NlsGge.ThirdConsultation.KSPS012Support5.exp_lip hz0n (by rw [hdiff]; exact hle1)).trans ?_
    rw [hdiff]
    have := mul_le_mul_of_nonneg_left hδ0 (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * ‖xi n - (n : ℂ) * Real.pi‖ ≤ 2 * (a / indexWeight n) := this
      _ = 2 * a / indexWeight n := by ring
  have key := diag_pure (indexWeight n) ‖xi n‖ EA a |(n : ℝ)| C u1 J
    (KSPSWKB.endpointOsc ((σ : ℂ) * xi n) c) (KSPSWKB.endpointOsc ((σ : ℂ) * xi n) H')
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz c d ((σ : ℂ) * xi n))
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz c ds ((σ : ℂ) * xi n))
    (NlsGge.ThirdConsultation.KSPS012Support5.Tz tc d ((σ : ℂ) * xi n))
    (Complex.exp (-(Complex.I * ((σ : ℂ) * xi n)))) ((-1 : ℂ) ^ n)
    (2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ (-(2 * Complex.I * ((σ : ℂ) * xi n))⁻¹ * (xi n)⁻¹) (σ : ℂ) (xi n)
    (deriv E (xi n)) (deriv g (xi n) - -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * J)
    hw0 hwX hX1 hNn (by linarith) hNw (by positivity) ha hC rfl hρn hρ'n hEAn hσn hρσ hlead hcauchy
    (by rw [hE']; ring)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (by positivity) key 2

end
end NlsGge.ThirdConsultation.KSPS017W
