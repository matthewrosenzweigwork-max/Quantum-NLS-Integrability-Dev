import Mathlib
import NlsGge.Atomic.G2.G2037
import NlsGge.Atomic.G1.G1037
import NlsGge.Atomic.G1.G1034
import NlsGge.Atomic.G1.G1086
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.GK38.ActionBranchDerivative
import NlsGge.GK38.PairCompact
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Sobolev.PeriodicBridge

                                                                                             
                                                                                           
                                                                                                     
                                                                                                            
                                                                                                        
                                                                
set_option autoImplicit false
open Filter Topology

namespace NlsGge.G2044S
noncomputable section

/-- An analytic function that is `O(w^N)` along a positive sequence tending to `0`
has vanishing iterated derivatives of order `< N` at `0`. -/
theorem iteratedDeriv_eq_zero_of_small (q : ℂ → ℂ) (hq : AnalyticAt ℂ q 0) (N : ℕ) (C : ℝ)
    (w : ℕ → ℝ) (hw0 : ∀ n, 0 < w n) (hwt : Tendsto w atTop (𝓝 0))
    (hb : ∀ᶠ n in atTop, ‖q (w n)‖ ≤ C * w n ^ N) :
    ∀ i < N, iteratedDeriv i q 0 = 0 := by
  refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hq).1 ?_
  by_cases htop : analyticOrderAt q 0 = ⊤
  · rw [htop]; exact le_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← hm]
  by_contra hlt
  have hmN : m < N := by
    have : ¬ (N : ℕ∞) ≤ (m : ℕ∞) := hlt
    exact_mod_cast not_le.1 this
  obtain ⟨g, hg, hg0, hfg⟩ := (hq.analyticOrderAt_eq_natCast).1 hm.symm
  have hwc : Tendsto (fun n => (w n : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hwt
    rw [Complex.ofReal_zero] at this
    exact this
  have h1 : ∀ᶠ n in atTop, q (w n : ℂ) = ((w n : ℂ) - 0) ^ m • g (w n : ℂ) :=
    hwc.eventually hfg
  have hgc : Tendsto (fun n => g (w n : ℂ)) atTop (𝓝 (g 0)) := hg.continuousAt.tendsto.comp hwc
  have h2 : ∀ᶠ n in atTop, ‖g 0‖ / 2 < ‖g (w n : ℂ)‖ := by
    have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 hg0
    exact (hgc.norm).eventually (lt_mem_nhds (by linarith))
  have hlim : Tendsto (fun n => C * w n ^ (N - m)) atTop (𝓝 0) := by
    have : Tendsto (fun n => w n ^ (N - m)) atTop (𝓝 0) := by
      simpa [zero_pow (by omega : N - m ≠ 0)] using hwt.pow (N - m)
    simpa using this.const_mul C
  have h3 : ∀ᶠ n in atTop, ‖g 0‖ / 2 ≤ C * w n ^ (N - m) := by
    filter_upwards [hb, h1, h2] with n hbn h1n h2n
    have hwn := hw0 n
    have hnorm : ‖q (w n : ℂ)‖ = w n ^ m * ‖g (w n : ℂ)‖ := by
      rw [h1n, norm_smul, norm_pow, sub_zero, Complex.norm_real, Real.norm_of_nonneg hwn.le]
    have hNm : w n ^ N = w n ^ m * w n ^ (N - m) := by
      rw [← pow_add]; congr 1; omega
    rw [hnorm, hNm, mul_left_comm] at hbn
    have hpm : 0 < w n ^ m := pow_pos hwn m
    have := le_of_mul_le_mul_left hbn hpm
    linarith
  have := ge_of_tendsto hlim h3
  have hpos : 0 < ‖g 0‖ := norm_pos_iff.2 hg0
  linarith


theorem sinh_lower : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, ‖y‖ < δ → ‖y‖ ≤ 2 * ‖Complex.sinh y‖ := by
  have h := (hasDerivAt_iff_isLittleO_nhds_zero.1 (Complex.hasDerivAt_sinh (0 : ℂ)))
  have h2 := h.def (c := 1 / 2) (by norm_num)
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨δ, hδ, hy⟩ := h2
  refine ⟨δ, hδ, fun y hyδ => ?_⟩
  have := hy (y := y) (by simpa using hyδ)
  simp only [zero_add, Complex.sinh_zero, sub_zero, Complex.cosh_zero, smul_eq_mul, mul_one] at this
  have h3 : ‖y‖ - ‖Complex.sinh y‖ ≤ ‖Complex.sinh y - y‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have h4 : ‖y‖ - ‖Complex.sinh y‖ ≤ 1 / 2 * ‖y‖ := h3.trans this
  linarith

theorem cosh_sub_cosh_c (A B : ℂ) :
    Complex.cosh A - Complex.cosh B =
      2 * Complex.sinh ((A + B) / 2) * Complex.sinh ((A - B) / 2) := by
  have key : ∀ a b : ℂ, Complex.cosh (a + b) - Complex.cosh (a - b) =
      2 * Complex.sinh a * Complex.sinh b := by
    intro a b; rw [Complex.cosh_add, Complex.cosh_sub]; ring
  have := key ((A + B) / 2) ((A - B) / 2)
  rwa [show (A + B) / 2 + (A - B) / 2 = A by ring,
    show (A + B) / 2 - (A - B) / 2 = B by ring] at this

theorem sinh_im_c (y : ℂ) : (Complex.sinh y).im = Real.cosh y.re * Real.sin y.im := by
  have hy : y = (y.re : ℂ) + (y.im : ℂ) * Complex.I := by
    rw [Complex.re_add_im]
  conv_lhs => rw [hy, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
  simp [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, mul_comm]


theorem norm_sinh_add_int (q : ℂ) (j : ℤ) :
    ‖Complex.sinh (q + (j : ℂ) * Real.pi * Complex.I)‖ = ‖Complex.sinh q‖ := by
  induction j using Int.induction_on with
  | zero => simp
  | succ i ih =>
    have : q + ((i + 1 : ℤ) : ℂ) * Real.pi * Complex.I =
        (q + ((i : ℤ) : ℂ) * Real.pi * Complex.I) + Real.pi * Complex.I := by push_cast; ring
    rw [this, Complex.sinh_add_pi_mul_I, norm_neg, ih]
  | pred i ih =>
    have : q + ((-(i : ℤ) - 1 : ℤ) : ℂ) * Real.pi * Complex.I + Real.pi * Complex.I =
        q + ((-(i : ℤ) : ℤ) : ℂ) * Real.pi * Complex.I := by push_cast; ring
    have h2 := Complex.sinh_add_pi_mul_I (q + ((-(i : ℤ) - 1 : ℤ) : ℂ) * Real.pi * Complex.I)
    rw [this] at h2
    rw [← norm_neg, ← h2, ih]

theorem sinh_eq_zero_c (y : ℂ) (h : Complex.sinh y = 0) :
    ∃ j : ℤ, y = (j : ℂ) * Real.pi * Complex.I := by
  have h1 : Complex.sin (y * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, h, zero_mul]
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 h1
  refine ⟨-k, ?_⟩
  have : y * Complex.I * Complex.I = (k : ℂ) * Real.pi * Complex.I := by rw [hk]
  have h3 : y * Complex.I * Complex.I = -y := by
    rw [mul_assoc, Complex.I_mul_I]; ring
  rw [h3] at this
  push_cast
  linear_combination -this

/-- Core asymptotic-uniqueness lemma. -/
theorem coeff_match (N : ℕ) (hN : 1 ≤ N) (s : ℕ → ℂ) (g1 : ℂ → ℂ) (hg : AnalyticAt ℂ g1 0)
    (C Λ : ℝ)
    (h : ∀ x : ℝ, Λ ≤ x →
      ‖2 * Complex.cosh (-Complex.I * (x : ℂ) + g1 ((x : ℂ)⁻¹)) -
        2 * Complex.cosh (-Complex.I * (x : ℂ) +
          ∑ j ∈ Finset.Icc 1 N, s j * ((x : ℂ)⁻¹) ^ j)‖ ≤ C / x ^ N) :
    ∀ j : ℕ, 1 ≤ j → j < N → iteratedDeriv j g1 0 = (j.factorial : ℂ) * s j := by
  set p : ℂ → ℂ := fun w => ∑ j ∈ Finset.Icc 1 N, s j * w ^ j with hpdef
  have hp : AnalyticAt ℂ p 0 := by
    simp only [hpdef]
    exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul (analyticAt_id.pow j)
  set e : ℂ → ℂ := fun w => (g1 w - p w) / 2 with hedef
  set m : ℂ → ℂ := fun w => (g1 w + p w) / 2 with hmdef
  have he : AnalyticAt ℂ e 0 := (hg.sub hp).div analyticAt_const (by norm_num)
  have hm : AnalyticAt ℂ m 0 := (hg.add hp).div analyticAt_const (by norm_num)
  have hid : ∀ x : ℝ, 2 * Complex.cosh (-Complex.I * (x : ℂ) + g1 ((x : ℂ)⁻¹)) -
        2 * Complex.cosh (-Complex.I * (x : ℂ) +
          ∑ j ∈ Finset.Icc 1 N, s j * ((x : ℂ)⁻¹) ^ j) =
      4 * Complex.sinh (-Complex.I * (x : ℂ) + m ((x : ℂ)⁻¹)) * Complex.sinh (e ((x : ℂ)⁻¹)) := by
    intro x
    have := cosh_sub_cosh_c (-Complex.I * (x : ℂ) + g1 ((x : ℂ)⁻¹))
      (-Complex.I * (x : ℂ) + p ((x : ℂ)⁻¹))
    have e1 : (-Complex.I * (x : ℂ) + g1 ((x : ℂ)⁻¹) + (-Complex.I * (x : ℂ) + p ((x : ℂ)⁻¹))) / 2
        = -Complex.I * (x : ℂ) + m ((x : ℂ)⁻¹) := by simp only [hmdef]; ring
    have e2 : (-Complex.I * (x : ℂ) + g1 ((x : ℂ)⁻¹) - (-Complex.I * (x : ℂ) + p ((x : ℂ)⁻¹))) / 2
        = e ((x : ℂ)⁻¹) := by simp only [hedef]; ring
    rw [e1, e2] at this
    simp only [hpdef] at this ⊢
    linear_combination 2 * this
  -- the sequence
  set θ : ℝ := (m 0).im with hθ
  set M : ℝ := max Λ 1 with hM
  set n0 : ℕ := ⌈(M - θ - Real.pi / 2) / Real.pi⌉₊ with hn0
  set X : ℕ → ℝ := fun n => θ + Real.pi / 2 + ((n + n0 : ℕ) : ℝ) * Real.pi with hX
  have hpi : 0 < Real.pi := Real.pi_pos
  have hXge : ∀ n, M ≤ X n := by
    intro n
    have h1 : (M - θ - Real.pi / 2) / Real.pi ≤ ((n + n0 : ℕ) : ℝ) := by
      calc (M - θ - Real.pi / 2) / Real.pi ≤ (n0 : ℝ) := Nat.le_ceil _
        _ ≤ ((n + n0 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left n0 n
    have h2 := (div_le_iff₀ hpi).1 h1
    simp only [hX]; linarith
  have hXtop : Tendsto X atTop atTop := by
    simp only [hX]
    refine tendsto_atTop_add_const_left _ _ ?_
    refine Tendsto.atTop_mul_const hpi ?_
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat n0)
  have hM1 : 1 ≤ M := le_max_right _ _
  have hXpos : ∀ n, 0 < X n := fun n => by linarith [hXge n]
  set w : ℕ → ℝ := fun n => (X n)⁻¹ with hw
  have hw0 : ∀ n, 0 < w n := fun n => inv_pos.2 (hXpos n)
  have hwt : Tendsto w atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hXtop
  have hwc : Tendsto (fun n => (w n : ℂ)) atTop (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp hwt
    rw [Complex.ofReal_zero] at this
    exact this
  have hcast : ∀ n, ((X n : ℂ))⁻¹ = (w n : ℂ) := fun n => by simp [hw]
  -- lower bound for sinh of the first factor
  have hδ : Tendsto (fun n => (m (w n : ℂ)).im - θ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => m (w n : ℂ)) atTop (𝓝 (m 0)) :=
      hm.continuousAt.tendsto.comp hwc
    have h2 := (Complex.continuous_im.tendsto (m 0)).comp h1
    simpa [hθ] using h2.sub_const θ
  have hδ1 : ∀ᶠ n in atTop, |(m (w n : ℂ)).im - θ| ≤ 1 := by
    have := (hδ.abs).eventually (ge_mem_nhds (by simp : |(0:ℝ)| < 1))
    filter_upwards [this] with n hn using hn
  have hlow : ∀ᶠ n in atTop,
      (1 : ℝ) / 2 ≤ ‖Complex.sinh (-Complex.I * (X n : ℂ) + m (w n : ℂ))‖ := by
    filter_upwards [hδ1] with n hn
    set y : ℂ := -Complex.I * (X n : ℂ) + m (w n : ℂ) with hy
    have him : y.im = ((m (w n : ℂ)).im - θ) - Real.pi / 2 - ((n + n0 : ℕ) : ℝ) * Real.pi := by
      simp only [hy, hX]
      simp [Complex.add_im, Complex.mul_im]
      ring
    have hs : |Real.sin y.im| = Real.cos ((m (w n : ℂ)).im - θ) := by
      rw [him, Real.sin_sub_nat_mul_pi, Real.sin_sub_pi_div_two, abs_mul, abs_pow, abs_neg,
        abs_one, one_pow, one_mul, abs_neg, abs_of_nonneg]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by
        have := abs_le.1 hn; linarith [Real.pi_gt_three]) (by
        have := abs_le.1 hn; linarith [Real.pi_gt_three])
    have hc : (1 : ℝ) / 2 ≤ Real.cos ((m (w n : ℂ)).im - θ) := by
      have := Real.one_sub_sq_div_two_le_cos (x := (m (w n : ℂ)).im - θ)
      have h2 : ((m (w n : ℂ)).im - θ) ^ 2 ≤ 1 := by
        have := abs_le.1 hn
        nlinarith
      linarith
    calc (1 : ℝ) / 2 ≤ |Real.sin y.im| := by rw [hs]; exact hc
      _ ≤ Real.cosh y.re * |Real.sin y.im| :=
          le_mul_of_one_le_left (abs_nonneg _) (Real.one_le_cosh _)
      _ = |(Complex.sinh y).im| := by
          rw [sinh_im_c, abs_mul, abs_of_pos (Real.cosh_pos _)]
      _ ≤ ‖Complex.sinh y‖ := Complex.abs_im_le_norm _
  -- bound on sinh e
  have hsin : ∀ᶠ n in atTop, ‖Complex.sinh (e (w n : ℂ))‖ ≤ (C / 2) * w n ^ N := by
    filter_upwards [hlow] with n hn
    have hx := h (X n) (le_trans (le_max_left _ _) (hXge n))
    rw [hid, hcast] at hx
    rw [norm_mul, norm_mul] at hx
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4] at hx
    have hCw : C / X n ^ N = C * w n ^ N := by simp [hw, inv_pow, div_eq_mul_inv]
    rw [hCw] at hx
    have hnn : 0 ≤ ‖Complex.sinh (e (w n : ℂ))‖ := norm_nonneg _
    have : 4 * (1 / 2) * ‖Complex.sinh (e (w n : ℂ))‖ ≤ C * w n ^ N := by
      calc 4 * (1 / 2) * ‖Complex.sinh (e (w n : ℂ))‖
          ≤ 4 * ‖Complex.sinh (-Complex.I * (X n : ℂ) + m (w n : ℂ))‖ *
            ‖Complex.sinh (e (w n : ℂ))‖ := by
            apply mul_le_mul_of_nonneg_right _ hnn; linarith
        _ ≤ _ := hx
    linarith
  -- e 0 is a multiple of pi I
  have hecont : Tendsto (fun n => Complex.sinh (e (w n : ℂ))) atTop
      (𝓝 (Complex.sinh (e 0))) :=
    (Complex.continuous_sinh.continuousAt.tendsto).comp (he.continuousAt.tendsto.comp hwc)
  have hzero : Tendsto (fun n => Complex.sinh (e (w n : ℂ))) atTop (𝓝 0) := by
    have hbd : Tendsto (fun n => (C / 2) * w n ^ N) atTop (𝓝 0) := by
      have : Tendsto (fun n => w n ^ N) atTop (𝓝 0) := by
        simpa [zero_pow (by omega : N ≠ 0)] using hwt.pow N
      simpa using this.const_mul (C / 2)
    exact squeeze_zero_norm' hsin hbd
  have hse : Complex.sinh (e 0) = 0 := tendsto_nhds_unique hecont hzero
  obtain ⟨j0, hj0⟩ := sinh_eq_zero_c _ hse
  set q : ℂ → ℂ := fun z => (-(e 0)) + e z with hq
  have hqa : AnalyticAt ℂ q 0 := analyticAt_const.add he
  have hq0 : q 0 = 0 := by simp [hq]
  have hsq : ∀ z, ‖Complex.sinh (q z)‖ = ‖Complex.sinh (e z)‖ := by
    intro z
    have : e z = q z + (j0 : ℂ) * Real.pi * Complex.I := by
      rw [← hj0]; simp [hq]
    rw [this, norm_sinh_add_int]
  obtain ⟨δ0, hδ0, hsl⟩ := sinh_lower
  have hqt : Tendsto (fun n => q (w n : ℂ)) atTop (𝓝 0) := by
    have := hqa.continuousAt.tendsto.comp hwc
    rw [hq0] at this
    exact this
  have hqsmall : ∀ᶠ n in atTop, ‖q (w n : ℂ)‖ < δ0 := by
    have := hqt.norm
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ0)
  have hqb : ∀ᶠ n in atTop, ‖q (w n : ℂ)‖ ≤ C * w n ^ N := by
    filter_upwards [hsin, hqsmall] with n h1 h2
    have := hsl _ h2
    rw [hsq] at this
    linarith
  have hqd := iteratedDeriv_eq_zero_of_small q hqa N C w hw0 hwt hqb
  -- translate to g1
  intro j hj1 hjN
  have h0 := hqd j hjN
  have hcg : ContDiffAt ℂ j g1 0 := hg.contDiffAt
  have hcp : ContDiffAt ℂ j p 0 := hp.contDiffAt
  have hd1 : iteratedDeriv j q 0 = (1 / 2 : ℂ) * (iteratedDeriv j g1 0 - iteratedDeriv j p 0) := by
    have hq' : q = fun z => (-(e 0)) + (1 / 2 : ℂ) * (g1 z - p z) := by
      funext z; simp only [hq, hedef]; ring
    rw [hq', iteratedDeriv_const_add (by omega : 0 < j)]
    rw [iteratedDeriv_const_mul (1 / 2 : ℂ) (hcg.sub hcp), iteratedDeriv_fun_sub hcg hcp]
  have hd2 : iteratedDeriv j p 0 = (j.factorial : ℂ) * s j := by
    simp only [hpdef]
    rw [iteratedDeriv_fun_sum (fun i _ =>
      (by fun_prop : ContDiffAt ℂ (j : ℕ) (fun z : ℂ => s i * z ^ i) 0))]
    have : ∀ i ∈ Finset.Icc 1 N, iteratedDeriv j (fun z => s i * z ^ i) 0 =
        if j = i then s i * (i.factorial : ℂ) else 0 := by
      intro i _
      have hc : ContDiffAt ℂ (j : ℕ) (fun z : ℂ => z ^ i) 0 := by fun_prop
      rw [iteratedDeriv_const_mul (s i) hc, iteratedDeriv_fun_pow_zero]
      by_cases hji : j = i <;> simp [hji]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_Icc.2 ⟨hj1, hjN.le⟩)]
    ring
  rw [hd1, hd2] at h0
  have : iteratedDeriv j g1 0 - (j.factorial : ℂ) * s j = 0 := by
    have h5 : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.1 h0).resolve_left h5
  linear_combination this



end
end NlsGge.G2044S

namespace NlsGge.GKDefinitionDesign
noncomputable section

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

open NlsGge.G2044S

theorem g2044_physicalSobolev_star (r : ℝ) (u : PhysicalL2) (h : physicalSobolev r u) :
    physicalSobolev r (star u : PhysicalL2) := by
  unfold physicalSobolev SobolevSquareSummable at h ⊢
  have h' := (Equiv.neg ℤ).summable_iff.mpr h
  refine h'.congr (fun j => ?_)
  have hr : ‖reflectedFourierL2 (star u : PhysicalL2) j‖ = ‖reflectedFourierL2 u (-j)‖ := by
    rw [reflectedFourierL2_apply, reflectedFourierL2_apply]
    unfold reflectedFourier
    rw [NlsGge.Schur.physicalFourier_star38, norm_neg, norm_neg, norm_star, neg_neg]
  simp only [Function.comp, Equiv.neg_apply, hr, neg_neg]
  have : Real.rpow (japaneseBracket (-j)) (2 * r) = Real.rpow (japaneseBracket j) (2 * r) := by
    unfold japaneseBracket; simp
  rw [this]

/-- Step A: on the real ray the discriminant is `2 cosh (f - c)`. -/
theorem g2044_cosh (u : PhysicalL2) (S : Finset ℤ)
    (hG : ∀ z : ℂ, (realSlice u, z) ∈ rootDomain38 →
      deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
        finiteGapDifferential u S z)
    (R : ℝ) (f : ℂ → ℂ)
    (hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (finiteGapDifferential u S z) z) :
    ∃ c : ℂ, ∀ x : ℝ, R < x → discrim (realSlice u) (x : ℂ) = 2 * Complex.cosh (f x - c) := by
  set κ := actualQuasimomentumE02_38 u with hκ
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set V : Set ℂ := {z : ℂ | R < z.re ∧ 0 < z.im} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hVc : Convex ℝ V := (convex_halfSpace_re_gt R).inter (convex_halfSpace_im_gt 0)
  have hVp : IsPreconnected V := hVc.isPreconnected
  have hnorm : ∀ z ∈ V, R < ‖z‖ := fun z hz =>
    lt_of_lt_of_le hz.1 ((Complex.re_le_norm z))
  have hdκ : ∀ z ∈ V, HasDerivAt κ (deriv κ z) z := fun z hz =>
    ((hk.1 z hz.2).differentiableAt).hasDerivAt
  have hderF : ∀ z ∈ V, HasDerivAt (fun z => f z + Complex.I * κ z) 0 z := by
    intro z hz
    have h1 := hf z (hnorm z hz)
    have h2 := (hdκ z hz).const_mul Complex.I
    have h3 := NlsGge.GK38.ActionBranch.discrim_deriv_div_root_upper u z hz.2
    rw [hG z (NlsGge.GK38.ActionBranch.root_domain u z hz.2)] at h3
    have := h1.add h2
    rw [h3] at this
    convert this using 1
    ring
  have hdiff : DifferentiableOn ℂ (fun z => f z + Complex.I * κ z) V :=
    fun z hz => (hderF z hz).differentiableAt.differentiableWithinAt
  have hz0 : ((R + 1 : ℝ) : ℂ) + Complex.I ∈ V := by
    simp [hV]
  set c0 : ℂ := f (((R + 1 : ℝ) : ℂ) + Complex.I) + Complex.I * κ (((R + 1 : ℝ) : ℂ) + Complex.I)
    with hc0
  have hconst : ∀ z ∈ V, f z + Complex.I * κ z = c0 := fun z hz =>
    hVo.is_const_of_deriv_eq_zero hVp hdiff (fun y hy => (hderF y hy).deriv) hz hz0
  have heq : Set.EqOn (discrim (realSlice u)) (fun z => 2 * Complex.cosh (f z - c0)) V := by
    intro z hz
    have h1 : discrim (realSlice u) z = 2 * Complex.cos (κ z) := by
      rw [NlsGge.GK38.discrim_realSlice, hk.2.1 z hz.2]
    have h2 : κ z = (f z - c0) * Complex.I := by
      have := hconst z hz
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination (-Complex.I) * this + κ z * hI
    simp only [h1, h2, Complex.cos_mul_I]
  set T : Set ℂ := {z : ℂ | R < z.re ∧ 0 ≤ z.im} with hT
  have hcont_f : ContinuousOn f T := fun z hz =>
    (hf z (lt_of_lt_of_le hz.1 (Complex.re_le_norm z))).continuousAt.continuousWithinAt
  have hcont_Δ : ContinuousOn (discrim (realSlice u)) T := by
    have hemb : Continuous (fun z : ℂ => (realSlice u, z)) :=
      continuous_const.prodMk continuous_id
    have hc : Continuous (fun p : PotPair × ℂ => discrim p.1 p.2) := discrim_L2_continuous
    exact (Continuous.comp (g := fun p : PotPair × ℂ => discrim p.1 p.2)
      (f := fun z : ℂ => (realSlice u, z)) hc hemb).continuousOn
  have hcl : T ⊆ closure V := by
    intro z hz
    have ht : Filter.Tendsto (fun n : ℕ => z + Complex.I * (1 / ((n : ℂ) + 1))) Filter.atTop
        (nhds z) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℂ) + 1))) Filter.atTop (nhds 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa using this
      simpa using (h1.const_mul Complex.I).const_add z
    refine mem_closure_of_tendsto ht (Filter.Eventually.of_forall fun n => ?_)
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hV, Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    have e1 : ((1 : ℂ) / ((n : ℂ) + 1)).re = 1 / ((n : ℝ) + 1) := by
      have : ((1 : ℂ) / ((n : ℂ) + 1)) = (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_re]
    have e2 : ((1 : ℂ) / ((n : ℂ) + 1)).im = 0 := by
      have : ((1 : ℂ) / ((n : ℂ) + 1)) = (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ) := by push_cast; rfl
      rw [this, Complex.ofReal_im]
    rw [e1, e2]
    constructor
    · simpa using hz.1
    · simp only [zero_mul, mul_zero, sub_zero, zero_add, one_mul]
      linarith [hz.2]
  have hVT : V ⊆ T := fun z hz => ⟨hz.1, hz.2.le⟩
  have hcont_g : ContinuousOn (fun z => 2 * Complex.cosh (f z - c0)) T :=
    continuousOn_const.mul (Complex.continuous_cosh.comp_continuousOn
      (hcont_f.sub continuousOn_const))
  have heq2 := Set.EqOn.of_subset_closure heq hcont_Δ hcont_g hVT hcl
  refine ⟨c0, fun x hx => ?_⟩
  exact heq2 (show (x : ℂ) ∈ T from ⟨by simpa using hx, by simp⟩)


theorem g2044_sigma_eq (N : ℕ) (hN : 1 ≤ N) (φ : PotPair) (l : ℂ) (hl : l ≠ 0) :
    wkbSigma N l φ = -Complex.I * l + ∑ j ∈ Finset.Icc 1 N,
      (if j = 1 then -(hierarchyHamiltonian 1 φ) / (2 * Complex.I)
        else hierarchyHamiltonian j φ / (2 * Complex.I) ^ j) * (l⁻¹) ^ j := by
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  unfold wkbSigma
  rw [hIcc, Finset.sum_insert h1, if_pos rfl]
  have hsum : ∑ j ∈ Finset.Icc 2 N, (if j = 1 then -(hierarchyHamiltonian 1 φ) / (2 * Complex.I)
        else hierarchyHamiltonian j φ / (2 * Complex.I) ^ j) * (l⁻¹) ^ j =
      ∑ j ∈ Finset.Icc 2 N, hierarchyHamiltonian j φ / (2 * Complex.I * l) ^ j := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj2 := (Finset.mem_Icc.1 hj).1
    rw [if_neg (by omega), mul_pow, inv_pow]
    have : (2 * Complex.I) ^ j ≠ 0 := pow_ne_zero _ (by simp)
    have : l ^ j ≠ 0 := pow_ne_zero _ hl
    field_simp
    ring
  rw [hsum]
  have : (2 * Complex.I) ≠ 0 := by simp
  field_simp
  ring

/-- Core of G2-044, parametrized by the three LANDED theorems it consumes (G2-037, G1-086 first
conjunct, G1-037); the head `G2_044` below instantiates them. -/
theorem g2044_core
    (h037 : ∀ u : PhysicalL2, NlsGge.ThirdConsultation.finiteGap u →
      ∃ S : Finset ℤ,
      (∀ n : ℤ, n ∈ S ↔
        actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) ∧
      AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
      (∀ z : ℂ, (realSlice u,z) ∈ rootDomain38 →
        deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
          finiteGapDifferential u S z) ∧
      (∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R →
        ∀ n : ℤ, CircleIntegrable (finiteGapDifferential u S) (C n) (R n) ∧
          circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0) ∧
      ∃ R : ℝ, 0 < R ∧ finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R ∧
        ∃ f g : ℂ → ℂ,
          AnalyticOnNhd ℂ f (finiteGapCuts u S)ᶜ ∧
          (∀ z : ℂ, z ∉ finiteGapCuts u S →
            HasDerivAt f (finiteGapDifferential u S z) z) ∧
          AnalyticAt ℂ g 0 ∧
          (∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹))
    (h086 : ∀ u : PhysicalL2, NlsGge.ThirdConsultation.finiteGap u →
      ∀ m : ℕ, physicalSobolev (m : ℝ) u)
    (hnn : ∀ (N : ℕ) (φ : PotPair), 0 ≤ pairSobolevNorm (N : ℝ) φ)
    (h1037 : ∀ (N : ℕ) (hN : 1 ≤ N) (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ),
    ∃ C Λ : ℝ, 0 < C ∧ 1 ≤ Λ ∧
      ∀ φ : PotPair, pairSobolev (N : ℝ) φ →
        pairSobolevNorm (N : ℝ) φ ≤ B →
      ∀ l : ℂ, |l.im| ≤ τ → Λ ≤ ‖l‖ →
        ‖discrim φ l - 2 * Complex.cosh (wkbSigma N l φ)‖ ≤
          C / ‖l‖^N)
    (u : PhysicalL2)
    (hu : NlsGge.ThirdConsultation.KO.SmoothPhysical u)
    (hfg : NlsGge.ThirdConsultation.finiteGap u)
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔
      actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (R : ℝ) (hR : 0 < R)
    (hcuts : finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R)
    (f g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (finiteGapDifferential u S z) z)
    (hexp : ∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹)
    (k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv k g 0 / (Nat.factorial k : ℂ) =
      hierarchyHamiltonian k (realSlice u) / (2*Complex.I)^k := by
  obtain ⟨S', hS', -, h3, -⟩ := h037 u hfg
  have hSS : S = S' := Finset.ext fun n => (hS n).trans (hS' n).symm
  subst hSS
  obtain ⟨c, hc⟩ := g2044_cosh u S h3 R f hf
  set N : ℕ := k + 1 with hNdef
  have hN : 1 ≤ N := by omega
  have hφ : pairSobolev (N : ℝ) (realSlice u) := by
    have h1 : physicalSobolev (N : ℝ) u := h086 u hfg N
    exact ⟨h1, g2044_physicalSobolev_star _ u h1⟩
  set B : ℝ := pairSobolevNorm (N : ℝ) (realSlice u) with hB
  obtain ⟨C, Λ, hC, hΛ, hbd⟩ := h1037 N hN B 0 (hnn N (realSlice u)) le_rfl
  set s : ℕ → ℂ := fun j => if j = 1 then -(hierarchyHamiltonian 1 (realSlice u)) / (2 * Complex.I)
    else hierarchyHamiltonian j (realSlice u) / (2 * Complex.I) ^ j with hs
  have hmain := coeff_match N hN s (fun w => g w - c) (hg.sub analyticAt_const) C (max Λ (R + 1))
    (by
      intro x hx
      have hx1 : R + 1 ≤ x := le_trans (le_max_right _ _) hx
      have hx2 : Λ ≤ x := le_trans (le_max_left _ _) hx
      have hxpos : 0 < x := by linarith
      have hxn : ‖(x : ℂ)‖ = x := by
        rw [Complex.norm_real, Real.norm_of_nonneg hxpos.le]
      have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hxpos.ne'
      have hΔ := hc x (by linarith)
      have hfx := hexp (x : ℂ) (by rw [hxn]; linarith)
      have hb := hbd (realSlice u) hφ le_rfl (x : ℂ) (by simp) (by rw [hxn]; exact hx2)
      rw [g2044_sigma_eq N hN _ _ hxc, hΔ, hxn] at hb
      have : -Complex.I * (x : ℂ) + (g ((x : ℂ)⁻¹) - c) = f x - c := by rw [hfx]; ring
      rw [this]
      exact hb)
  have h1 := hmain k (by omega) (by omega)
  have h2 : iteratedDeriv k (fun w => g w - c) 0 = iteratedDeriv k g 0 := by
    have : (fun w => g w - c) = fun w => (-c) + g w := by funext w; ring
    rw [this, iteratedDeriv_const_add (by omega : 0 < k)]
  rw [h2] at h1
  have hsk : s k = hierarchyHamiltonian k (realSlice u) / (2 * Complex.I) ^ k := by
    simp only [hs]; rw [if_neg (by omega)]
  rw [hsk] at h1
  have hkf : (Nat.factorial k : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [h1]
  field_simp


/-- **G2-044.** -/
theorem G2_044 (u : PhysicalL2)
    (hu : NlsGge.ThirdConsultation.KO.SmoothPhysical u)
    (hfg : NlsGge.ThirdConsultation.finiteGap u)
    (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔
      actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n)
    (R : ℝ) (hR : 0 < R)
    (hcuts : finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R)
    (f g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (finiteGapDifferential u S z) z)
    (hexp : ∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹)
    (k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv k g 0 / (Nat.factorial k : ℂ) =
      hierarchyHamiltonian k (realSlice u) / (2*Complex.I)^k :=
  g2044_core G2_037 (G1_086).1 (fun N φ => (pairSobolevNorm_ge N φ).1) G1_037 u hu hfg S hS R hR hcuts f g hg hf hexp k hk

end
end NlsGge.GKDefinitionDesign
