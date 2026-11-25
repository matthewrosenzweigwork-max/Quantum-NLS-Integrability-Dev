import NlsGge.Spectral.ActualQuasimomentumWindowUniformE02_38
import NlsGge.Spectral.ActualCouplingSobolevUniformBox38
import NlsGge.Spectral.ActualQuasimomentumBoundaryFunctionE02_38
import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import NlsGge.Herglotz38.HalfPlaneCauchyRepresentationE02_38
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # HD (campaign 38): decay `‖k(w) - w‖ ≤ C/√(1+‖w‖)` on the closed upper half-plane (H¹ u) -/

/-- Pointwise logarithm bound: if `‖g‖ ≤ 3/4` and `exp(i g)` is `1/2`-close to `1`, then
`‖g‖ ≤ (3/2)‖exp(i g) - 1‖`. -/
theorem norm_le_of_exp_mul_I_pointwise_E02_38 (g : ℂ) (hg : ‖g‖ ≤ 3/4)
    (hw : ‖Complex.exp (Complex.I * g) - 1‖ ≤ 1/2) :
    ‖g‖ ≤ (3/2) * ‖Complex.exp (Complex.I * g) - 1‖ := by
  set w := Complex.exp (Complex.I * g)
  have hL := Complex.norm_log_one_add_half_le_self (z := w - 1) hw
  simp only [add_sub_cancel] at hL
  have he : Complex.exp (Complex.log w) = Complex.exp (Complex.I * g) := by
    rw [Complex.exp_log (Complex.exp_ne_zero _)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hm0 : m = 0 := by
    by_contra hne
    have h1 : (1:ℝ) ≤ |(m:ℝ)| := by
      have : (1:ℤ) ≤ |m| := Int.one_le_abs hne
      exact_mod_cast this
    have hmn : ‖(m:ℂ) * (2*Real.pi*Complex.I)‖ = |(m:ℝ)| * (2*Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, norm_mul, Complex.norm_I, mul_one,
        show (2*(Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]
    have htri : ‖(m:ℂ) * (2*Real.pi*Complex.I)‖ ≤ ‖Complex.log w‖ + ‖Complex.I * g‖ := by
      have : (m:ℂ) * (2*Real.pi*Complex.I) = Complex.log w - Complex.I * g := by
        rw [hm]; ring
      rw [this]; exact norm_sub_le _ _
    rw [hmn, norm_mul, Complex.norm_I, one_mul] at htri
    nlinarith [Real.pi_gt_three, norm_nonneg (w - 1)]
  rw [hm0] at hm
  simp only [Int.cast_zero, zero_mul, add_zero] at hm
  have : ‖g‖ = ‖Complex.log w‖ := by
    rw [hm, norm_mul, Complex.norm_I, one_mul]
  rw [this]; exact hL

/-- Pointwise closeness of `exp(i(k-z))` to one from the normalized coupled error at `z`. -/
theorem norm_exp_sub_one_le_of_normalized_E02_38 (u : PhysicalL2) (z : ℂ) (hzi : 0 < z.im)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/20000)
    (hτ : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      ‖Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z -
        (1 + Complex.exp (2*Complex.I*z))/2‖ ≤ ε) :
    ‖Complex.exp (Complex.I * (actualQuasimomentumE02_38 u z - z)) - 1‖ ≤
      max (3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε)) (8*ε) := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1u : (((1:ℝ):ℂ) • u) = u := by simp
  have hexp_neg : ‖Complex.exp (-(Complex.I*z))‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have hexp : ‖Complex.exp (Complex.I*z)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  have hfac : Complex.exp (Complex.I * (k z - z)) - 1 =
      (Complex.exp (Complex.I * k z) - Complex.exp (Complex.I * z)) *
        Complex.exp (-(Complex.I*z)) := by
    rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    ring_nf
  rcases le_or_gt z.im 1 with hY | hY
  · have htr : ∀ τ ∈ Set.Icc (0:ℝ) 1,
        ‖actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z‖ ≤ Real.exp 1 * ε := by
      intro τ hτ'
      have h := hτ τ hτ'
      have heq : actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - Complex.cos z =
          Complex.exp (-(Complex.I*z)) * (Complex.exp (Complex.I*z) *
            actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z - (1 + Complex.exp (2*Complex.I*z))/2) := by
        rw [← exp_I_mul_cos_E02_38, ← mul_sub, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
          Complex.exp_zero, one_mul]
      rw [heq, norm_mul, hexp_neg]
      exact mul_le_mul (Real.exp_le_exp.mpr hY) h (norm_nonneg _) he0.le
    have hc := norm_exp_actualQuasimomentum_sub_le_E02_38 u z hzi _ (by positivity) htr
    rw [hfac, norm_mul, hexp_neg]
    calc ‖Complex.exp (Complex.I * k z) - Complex.exp (Complex.I * z)‖ * Real.exp z.im
        ≤ 3 * Real.sqrt (2 * (Real.exp 1 * ε)) * Real.exp 1 :=
          mul_le_mul hc (Real.exp_le_exp.mpr hY) (Real.exp_pos _).le (by positivity)
      _ = 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε) := by ring_nf
      _ ≤ _ := le_max_left _ _
  · set w := Complex.exp (Complex.I * k z)
    set ζ := Complex.exp (Complex.I * z)
    have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
    have hζ : ‖ζ‖ ≤ Real.exp (-1) := by rw [hexp]; exact Real.exp_le_exp.mpr (by linarith)
    have hroot : w^2 - 2*actualPhysicalUnitHalfTrace32 u z*w + 1 = 0 := by
      rw [← hk.2.1 z hzi, Complex.cos]
      have he : w * Complex.exp (-(Complex.I*k z)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      rw [show k z*Complex.I = Complex.I*k z by ring, show -k z*Complex.I = -(Complex.I*k z) by ring]
      linear_combination -he
    have hw : ‖w‖ < 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (hk.2.2.1 z hzi))
    have hnorm : ζ * (actualPhysicalUnitHalfTrace32 u z - (ζ + ζ⁻¹)/2) =
        Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 u z -
          (1 + Complex.exp (2*Complex.I*z))/2 := by
      have h2 : ζ^2 = Complex.exp (2*Complex.I*z) := by
        rw [← Complex.exp_nat_mul]; push_cast; ring_nf
      rw [← h2]; field_simp; ring
    have hst := hτ 1 (by simp)
    rw [h1u, ← hnorm] at hst
    have hr := root_ratio_close_of_separated_E02_38 w ζ _ hζ0 hζ hroot hw ε hst (by linarith)
    have hq : Complex.exp (Complex.I * (k z - z)) = w/ζ := by
      rw [mul_sub, Complex.exp_sub]
    rw [hq]
    exact hr.trans (le_max_right _ _)


/-- Per-`u` normalized half-trace bound in `‖z‖`, uniform in the coupling `τ ∈ [0,1]` and all
heights (from the Schur normal-form estimate `uniformBox_normalized_bound_of_rep38`). -/
theorem exists_normalized_bound_norm_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ z : ℂ, 0 ≤ z.im → K ≤ ‖z‖ →
      ‖Complex.exp (Complex.I*z) * actualPhysicalUnitHalfTrace32 ((τ:ℂ) • u) z -
        (1 + Complex.exp (2*Complex.I*z))/2‖ ≤ C / ‖z‖ := by
  obtain ⟨Ci, C1, hCi, hC1, hrep⟩ := NlsGge.Schur.actualH1ACRepresentativeUniformBox38V1
  set R := ‖physicalSobolevL2 1 u hu‖
  set A := Ci * R
  set a := C1 * R
  have hA0 : 0 ≤ A := by positivity
  have ha0 : 0 ≤ a := by positivity
  refine ⟨4*(A + A^2 + a) + 1, (4/3)*(A + A^2 + a) + 1, by positivity, by positivity, ?_⟩
  intro τ hτ z hz hzK
  have hu' := sobolevSquareSummable_smul38 (τ:ℂ) u hu
  obtain ⟨f, f', hfac, hf'i, hder, hae, hfb, hf'b⟩ := hrep ((τ:ℂ) • u) hu'
  have hnorm : ‖physicalSobolevL2 1 ((τ:ℂ) • u) hu'‖ ≤ R := by
    rw [physicalSobolevL2_smul_norm38 (τ:ℂ) u hu hu']
    have : ‖(τ:ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ.1]; exact hτ.2
    nlinarith [norm_nonneg (physicalSobolevL2 1 u hu)]
  have hfb' : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t‖ ≤ A := fun t ht =>
    (hfb t ht).trans (mul_le_mul_of_nonneg_left hnorm hCi.le)
  have hf'b' : ∫ t in (0:ℝ)..1, ‖f' t‖ ≤ a := hf'b.trans (mul_le_mul_of_nonneg_left hnorm hC1.le)
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hzK
  have hden : 0 < 2 * ‖z‖ := by positivity
  have hβ : A / (2 * ‖z‖) ≤ 1/4 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg A]
  have hη : (A^2 + a) / (2 * ‖z‖) ≤ 1/8 := by
    rw [div_le_iff₀ hden]; nlinarith [sq_nonneg A]
  have h := uniformBox_normalized_bound_of_rep38 ((τ:ℂ) • u) f f' A a hfac hf'i hder hae hfb'
    hf'b' z hz hz0 hβ hη
  refine h.trans ?_
  rw [show 8 / 3 * (A / (2 * ‖z‖) + (A ^ 2 + a) / (2 * ‖z‖)) =
    (4/3)*(A + A^2 + a) / ‖z‖ by field_simp; ring]
  apply div_le_div_of_nonneg_right (by linarith) hz0.le


theorem isPreconnected_upperExterior_E02_38 (R : ℝ) (hR : 0 ≤ R) :
    IsPreconnected {z : ℂ | 0 < z.im ∧ R < ‖z‖} := by
  let f : ℝ × ℝ → ℂ := fun p => (p.1:ℂ) * Complex.exp ((p.2:ℂ) * Complex.I)
  have hf : Continuous f := by fun_prop
  have himg : f '' (Set.Ioi R ×ˢ Set.Ioo 0 Real.pi) = {z : ℂ | 0 < z.im ∧ R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
      have hr0 : 0 < r := lt_of_le_of_lt hR hr
      constructor
      · simp only [f]
        rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        exact mul_pos hr0 (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
      · simp only [f]
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr0]
        exact hr
    · rintro ⟨him, hn⟩
      refine ⟨(‖z‖, Complex.arg z), ⟨hn, ?_, ?_⟩, Complex.norm_mul_exp_arg_mul_I z⟩
      · rcases (Complex.arg_nonneg_iff.mpr him.le).lt_or_eq with h | h
        · exact h
        · exfalso
          have := Complex.arg_eq_zero_iff.mp h.symm
          linarith [this.2]
      · exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))
  rw [← himg]
  exact (isPreconnected_Ioi.prod isPreconnected_Ioo).image f hf.continuousOn

/-- HD: decay of `k(w) - w` on the closed upper half-plane for H¹ potentials; on the real axis
`k` means its boundary value `extendFrom`. -/
theorem actualQuasimomentum_decay_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 0 ≤ w.im →
      ‖extendFrom {z : ℂ | 0 < z.im} (actualQuasimomentumE02_38 u) w - w‖ ≤
        C / Real.sqrt (1 + ‖w‖) := by
  obtain ⟨K, C₀, hK, hC₀, hnb⟩ := exists_normalized_bound_norm_E02_38 u hu
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u
  set U : Set ℂ := {z : ℂ | 0 < z.im}
  set kb := extendFrom U k
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hkb : ∀ z ∈ U, kb z = k z := extendFrom_extends hk.1.continuousOn
  have hkbc : ContinuousOn kb {z : ℂ | 0 ≤ z.im} := continuousOn_extend_actualQuasimomentumE02_38 u
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set R₁ : ℝ := max K (20000 * C₀) + 1
  have hR₁ : 1 ≤ R₁ := by
    have : 0 ≤ max K (20000 * C₀) := le_trans hK.le (le_max_left _ _)
    linarith
  set D : ℝ := 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) + 8 * C₀
  have hD : 0 ≤ D := by positivity
  -- pointwise exponential closeness on the exterior region
  have hφ : ∀ z : ℂ, 0 < z.im → R₁ < ‖z‖ →
      ‖Complex.exp (Complex.I * (k z - z)) - 1‖ ≤ D / Real.sqrt ‖z‖ ∧
      ‖Complex.exp (Complex.I * (k z - z)) - 1‖ ≤ 1/6 := by
    intro z hzi hzR
    have hz1 : 1 ≤ ‖z‖ := le_trans hR₁ hzR.le
    have hzpos : 0 < ‖z‖ := by linarith
    set ε := C₀ / ‖z‖
    have hε0 : 0 ≤ ε := by positivity
    have hε : ε ≤ 1/20000 := by
      rw [div_le_iff₀ hzpos]
      have : 20000 * C₀ ≤ R₁ := le_trans (le_max_right _ _) (by linarith)
      linarith
    have hKz : K ≤ ‖z‖ := le_trans (le_trans (le_max_left _ _) (by linarith)) hzR.le
    have h := norm_exp_sub_one_le_of_normalized_E02_38 u z hzi ε hε0 hε
      (fun τ hτ => hnb τ hτ z hzi.le hKz)
    have hsz : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr hzpos
    constructor
    · refine h.trans (max_le ?_ ?_)
      · have : Real.sqrt (2 * Real.exp 1 * ε) = Real.sqrt (2 * Real.exp 1 * C₀) / Real.sqrt ‖z‖ := by
          rw [show 2 * Real.exp 1 * ε = (2 * Real.exp 1 * C₀) / ‖z‖ by simp only [ε]; ring,
            Real.sqrt_div' _ hzpos.le]
        rw [this, mul_div_assoc']
        apply div_le_div_of_nonneg_right _ hsz.le
        linarith [show 0 ≤ 8 * C₀ by positivity]
      · have hsle : Real.sqrt ‖z‖ ≤ ‖z‖ := by
          calc Real.sqrt ‖z‖ ≤ Real.sqrt (‖z‖^2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = ‖z‖ := Real.sqrt_sq hzpos.le
        have h8 : 8 * ε ≤ 8 * C₀ / Real.sqrt ‖z‖ := by
          simp only [ε]
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_left (by positivity) hsz hsle
        have h3 : 0 ≤ 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * C₀) := by positivity
        refine h8.trans (div_le_div_of_nonneg_right ?_ hsz.le)
        simp only [D]; linarith
    · refine h.trans (max_le ?_ ?_)
      · have h1 : 2 * Real.exp 1 * ε ≤ 6/20000 := by nlinarith
        have h2 : Real.sqrt (2 * Real.exp 1 * ε) ≤ Real.sqrt (6/20000) := Real.sqrt_le_sqrt h1
        have h3 : Real.sqrt (6/20000) < 1/57 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have h5 : 3 * Real.exp 1 * Real.sqrt (2 * Real.exp 1 * ε) ≤ 3 * 3 * (1/57) :=
          mul_le_mul (by linarith) (h2.trans h3.le) (Real.sqrt_nonneg _) (by norm_num)
        linarith
      · linarith
  -- integer fixed on the connected exterior region
  set S : Set ℂ := {z : ℂ | 0 < z.im ∧ R₁ < ‖z‖}
  have hS : IsPreconnected S := isPreconnected_upperExterior_E02_38 R₁ (by linarith)
  obtain ⟨Rh, hRh, hhigh⟩ := hk.2.2.2 1 one_pos
  set Y₁ : ℝ := max Rh (R₁ + 1)
  let z₁ : ℂ := ((0:ℝ):ℂ) + Complex.I * ((Y₁:ℝ):ℂ)
  have hY₁ : R₁ + 1 ≤ Y₁ := le_max_right _ _
  have hz₁ : z₁ ∈ S := by
    constructor
    · simp [z₁]; linarith
    · have : ‖z₁‖ = Y₁ := by
        simp only [z₁, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_pos (by linarith)
      rw [this]; linarith
  have hz₁s : ‖k z₁ - z₁‖ < 1 := hhigh Y₁ (le_max_left _ _) 0
  have hcontS : ContinuousOn (fun z => k z - z) S :=
    (hk.1.continuousOn.mono (fun z hz => hz.1)).sub continuousOn_id
  have hunif := norm_le_of_exp_mul_I_near_one_E02_38 S hS _ hcontS (1/2) le_rfl
    (fun z hz => (hφ z hz.1 hz.2).2.trans (by norm_num)) z₁ hz₁ hz₁s
  have hext : ∀ z : ℂ, 0 < z.im → R₁ < ‖z‖ → ‖k z - z‖ ≤ (3/2) * D / Real.sqrt ‖z‖ := by
    intro z hzi hzR
    have hp := norm_le_of_exp_mul_I_pointwise_E02_38 (k z - z)
      (by have := hunif z ⟨hzi, hzR⟩; linarith) ((hφ z hzi hzR).2.trans (by norm_num))
    rw [mul_div_assoc]
    exact hp.trans (mul_le_mul_of_nonneg_left (hφ z hzi hzR).1 (by norm_num))
  -- compact part
  have hcomp : IsCompact ({z : ℂ | 0 ≤ z.im} ∩ Metric.closedBall 0 (R₁ + 1)) :=
    (isCompact_closedBall 0 (R₁ + 1)).inter_left (isClosed_le continuous_const Complex.continuous_im)
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn
    ((hkbc.sub continuousOn_id).mono Set.inter_subset_left)
  set C : ℝ := (3/2) * D * Real.sqrt 2 + |M| * Real.sqrt (2 + R₁) + 1
  refine ⟨C, by positivity, ?_⟩
  -- bound in the open half-plane
  have hopen : ∀ z : ℂ, 0 < z.im → ‖kb z - z‖ ≤ C / Real.sqrt (1 + ‖z‖) := by
    intro z hzi
    have hs1 : 0 < Real.sqrt (1 + ‖z‖) := Real.sqrt_pos.mpr (by positivity)
    rw [le_div_iff₀ hs1]
    rcases le_or_gt ‖z‖ R₁ with hzR | hzR
    · have hb := hM z ⟨hzi.le, by rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩
      have hsq : Real.sqrt (1 + ‖z‖) ≤ Real.sqrt (2 + R₁) := Real.sqrt_le_sqrt (by linarith)
      calc ‖kb z - z‖ * Real.sqrt (1 + ‖z‖) ≤ |M| * Real.sqrt (2 + R₁) :=
            mul_le_mul (hb.trans (le_abs_self M)) hsq (Real.sqrt_nonneg _) (abs_nonneg M)
        _ ≤ C := by have : 0 ≤ (3/2) * D * Real.sqrt 2 := by positivity
                    simp only [C]; linarith
    · rw [hkb z hzi]
      have hb := hext z hzi hzR
      have hzpos : 0 < ‖z‖ := by linarith
      have hsz : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr hzpos
      have hsq : Real.sqrt (1 + ‖z‖) ≤ Real.sqrt 2 * Real.sqrt ‖z‖ := by
        rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
      calc ‖k z - z‖ * Real.sqrt (1 + ‖z‖) ≤ ((3/2) * D / Real.sqrt ‖z‖) * (Real.sqrt 2 * Real.sqrt ‖z‖) :=
            mul_le_mul hb hsq (Real.sqrt_nonneg _) (by positivity)
        _ = (3/2) * D * Real.sqrt 2 := by field_simp
        _ ≤ C := by have : 0 ≤ |M| * Real.sqrt (2 + R₁) := by positivity
                    simp only [C]; linarith
  intro w hw
  rcases lt_or_eq_of_le hw with hpos | hzero
  · exact hopen w hpos
  · -- boundary point: pass to the limit from the open half-plane
    have hNe : (𝓝[U] w).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 hw)
    have hcw : ContinuousWithinAt (fun z => ‖kb z - z‖ - C / Real.sqrt (1 + ‖z‖))
        {z : ℂ | 0 ≤ z.im} w := by
      apply ContinuousWithinAt.sub
      · exact ((hkbc w hw).sub continuousWithinAt_id).norm
      · apply ContinuousWithinAt.div continuousWithinAt_const
        · exact (Real.continuous_sqrt.comp (continuous_const.add continuous_norm)).continuousWithinAt
        · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsub : U ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz => le_of_lt (show (0:ℝ) < z.im from hz)
    have hlim := (hcw.mono hsub).tendsto
    have hle : (‖kb w - w‖ - C / Real.sqrt (1 + ‖w‖)) ≤ 0 := by
      apply le_of_tendsto hlim
      filter_upwards [self_mem_nhdsWithin] with z hz
      linarith [hopen z hz]
    linarith


/-- E02.04 (Herglotz representation, every H¹ potential):
`k(z) = z + (1/π) ∫ v(t)/(t - z) dt` on the upper half-plane, with the integral absolutely
convergent. -/
theorem actualQuasimomentum_herglotz_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∀ z : ℂ, 0 < z.im →
      Integrable (fun t : ℝ => (actualGapHeightE02_38 u t : ℂ) / ((t:ℂ) - z)) ∧
      actualQuasimomentumE02_38 u z = z +
        (1/Real.pi : ℂ) * ∫ t : ℝ, (actualGapHeightE02_38 u t : ℂ) / ((t:ℂ) - z) := by
  obtain ⟨C, hC, hdec⟩ := actualQuasimomentum_decay_E02_38 u hu
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set U : Set ℂ := {z : ℂ | 0 < z.im}
  set kb := extendFrom U (actualQuasimomentumE02_38 u)
  have hkb : ∀ z ∈ U, kb z = actualQuasimomentumE02_38 u z :=
    extendFrom_extends hk.1.continuousOn
  let F : ℂ → ℂ := fun w => kb w - w
  have hFd : DifferentiableOn ℂ F U := by
    intro z hz
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
    have h1 : DifferentiableAt ℂ (fun w => actualQuasimomentumE02_38 u w - w) z :=
      (hk.1 z hz).differentiableAt.sub differentiableAt_id
    apply (h1.congr_of_eventuallyEq _).differentiableWithinAt
    filter_upwards [hUo.mem_nhds hz] with w hw
    simp only [F, hkb w hw]
  have hFc : ContinuousOn F {z : ℂ | 0 ≤ z.im} :=
    (continuousOn_extend_actualQuasimomentumE02_38 u).sub continuousOn_id
  have hIm : ∀ t : ℝ, (F (t:ℂ)).im = actualGapHeightE02_38 u t := by
    intro t
    have h := boundaryLimit_im_E02_38 u t _ (tendsto_actualQuasimomentumBoundaryE02_38 u t)
    simp only [F, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact h
  intro z hz
  obtain ⟨hint, heq⟩ := halfPlane_herglotz_of_decay_E02_38 F C hFd hFc
    (fun w hw => hdec w hw) z hz
  simp only [hIm] at hint heq
  refine ⟨hint, ?_⟩
  have : F z = actualQuasimomentumE02_38 u z - z := by simp only [F, hkb z hz]
  rw [this] at heq
  linear_combination heq

end NlsGge.SpectralFoundations
end
