import NlsGge.Weights.Regularity
/-! Source W02 concrete twice-differentiated series. Actual second convergence
precedes termwise differentiation, real restriction and moment identities. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

def complexWeightTermSecondDerivative (c : ℕ → ℝ) (z : ℂ) (j : ℕ) : ℂ :=
  (coefficient c j : ℂ) * ((2*j : ℕ) : ℂ) * ((2*j-1 : ℕ) : ℂ) * z^(2*j-2)

def weightTermSecondDerivative (c : ℕ → ℝ) (r : ℝ) (j : ℕ) : ℝ :=
  coefficient c j * ((2*j : ℕ) : ℝ) * ((2*j-1 : ℕ) : ℝ) * r^(2*j-2)

lemma complexWeightTermDerivative_hasDerivAt (c : ℕ → ℝ) (z : ℂ) (j : ℕ) :
    HasDerivAt (fun w : ℂ => complexWeightTermDerivative c w j)
      (complexWeightTermSecondDerivative c z j) z := by
  convert (hasDerivAt_pow (2*j-1) z).const_mul
    ((coefficient c j : ℂ) * ((2*j : ℕ) : ℂ)) using 1
  · rfl
  · simp only [complexWeightTermSecondDerivative, Nat.sub_sub]
    ring

lemma complexWeightTermSecondDerivative_norm_le (lower : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (j : ℕ) :
    ‖complexWeightTermSecondDerivative c z j‖ ≤ 4*(j : ℝ)^4*weightTerm c R j := by
  have hc := (coefficient_pos lower c hlower hbound j).le
  have hj2 : (j : ℝ)^2 ≤ (j : ℝ)^4 := by
    by_cases hj : j = 0
    · simp [hj]
    · exact pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj) (by omega : 2 ≤ 4)
  have hsub : ((2*j-1 : ℕ) : ℝ) ≤ 2*(j : ℝ) := by exact_mod_cast Nat.sub_le (2*j) 1
  have hzpow : ‖z‖^(2*j-2) ≤ R^(2*j) :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans (pow_le_pow_right₀ hR (Nat.sub_le (2*j) 2))
  simp only [complexWeightTermSecondDerivative, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (coefficient_pos lower c hlower hbound j),
    Complex.norm_natCast, Nat.cast_mul, Nat.cast_ofNat, Complex.norm_two, Real.norm_two]
  calc
    coefficient c j * (2*(j : ℝ)) * ((2*j-1 : ℕ) : ℝ) * ‖z‖^(2*j-2) ≤
      coefficient c j * (2*(j : ℝ)) * (2*(j : ℝ)) * R^(2*j) := by gcongr
    _ = coefficient c j * (4*(j : ℝ)^2) * R^(2*j) := by ring
    _ ≤ coefficient c j * (4*(j : ℝ)^4) * R^(2*j) := by gcongr
    _ = 4*(j : ℝ)^4*weightTerm c R j := by unfold weightTerm; ring

lemma complexWeightSecondDerivative_majorant_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) :
    Summable (fun j : ℕ => 4*(j : ℝ)^4*weightTerm c R j) := by
  simpa only [mul_assoc] using (fourthMoment_summable lower upper c hlower hbound hupper R).mul_left 4

lemma complexWeightTermSecondDerivative_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) :
    Summable (complexWeightTermSecondDerivative c z) := by
  apply Summable.of_norm
  exact (complexWeightSecondDerivative_majorant_summable lower upper c hlower hbound hupper
    (max 1 ‖z‖)).of_nonneg_of_le (fun j => norm_nonneg _)
    (complexWeightTermSecondDerivative_norm_le lower c hlower hbound (max 1 ‖z‖)
      (le_max_left _ _) z (le_max_right _ _))

lemma complexWeightSecondDerivativeSeries_tendstoUniformlyOn (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTermSecondDerivative c z j)
      (fun z : ℂ => ∑' j, complexWeightTermSecondDerivative c z j)
      Filter.atTop (Metric.closedBall (0 : ℂ) R) := by
  apply tendstoUniformlyOn_tsum_nat
    (complexWeightSecondDerivative_majorant_summable lower upper c hlower hbound hupper (max 1 R))
  intro j z hz
  have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact complexWeightTermSecondDerivative_norm_le lower c hlower hbound (max 1 R)
    (le_max_left _ _) z (hzR.trans (le_max_right _ _)) j

lemma complexWeightSecondDerivativeSeries_tendstoUniformlyOn_compact
    (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper)
    (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∑ j ∈ Finset.range N, complexWeightTermSecondDerivative c z j)
      (fun z : ℂ => ∑' j, complexWeightTermSecondDerivative c z j) Filter.atTop K := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  apply (complexWeightSecondDerivativeSeries_tendstoUniformlyOn lower upper c hlower hbound hupper R hR.le).mono
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hKR z hz

lemma complexWeight_derivativeSeries_hasDerivAt (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∑' j, complexWeightTermDerivative c w j)
      (∑' j, complexWeightTermSecondDerivative c z j) z := by
  let R : ℝ := max 1 (‖z‖+1)
  have hR : 1 ≤ R := le_max_left _ _
  have hzR : ‖z‖ < R := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hz : z ∈ Metric.ball (0 : ℂ) R := by simpa only [Metric.mem_ball, dist_zero_right] using hzR
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (complexWeightSecondDerivative_majorant_summable lower upper c hlower hbound hupper R)
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun j w hw => complexWeightTermDerivative_hasDerivAt c w j) _ hzero
    (complexWeightTermDerivative_summable lower upper c hlower hbound hupper 0) hz
  intro j w hw
  have hwR : ‖w‖ ≤ R := (by simpa only [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < R).le
  exact complexWeightTermSecondDerivative_norm_le lower c hlower hbound R hR w hwR j

lemma complexWeightTermSecondDerivative_ofReal (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    complexWeightTermSecondDerivative c (r : ℂ) j = (weightTermSecondDerivative c r j : ℂ) := by
  simp [complexWeightTermSecondDerivative, weightTermSecondDerivative]

lemma weightTermSecondDerivative_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) : Summable (weightTermSecondDerivative c r) := by
  apply Complex.summable_ofReal.mp
  exact (complexWeightTermSecondDerivative_summable lower upper c hlower hbound hupper (r : ℂ)).congr
    (fun j => complexWeightTermSecondDerivative_ofReal c r j)

lemma weight_deriv_hasDerivAt (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    HasDerivAt (deriv (weight c)) (∑' j, weightTermSecondDerivative c r j) r := by
  have hc := complexWeightTermSecondDerivative_summable lower upper c hlower hbound hupper (r : ℂ)
  have hr := (complexWeight_derivativeSeries_hasDerivAt lower upper c hlower hbound hupper (r : ℂ)).real_of_complex
  have hfun (x : ℝ) : (∑' j, complexWeightTermDerivative c (x : ℂ) j).re = deriv (weight c) x := by
    rw [Complex.re_tsum (complexWeightTermDerivative_summable lower upper c hlower hbound hupper (x : ℂ)),
      (weight_hasDerivAt lower upper c hlower hbound hupper x).deriv]
    apply tsum_congr
    intro j
    simp only [complexWeightTermDerivative_ofReal, Complex.ofReal_re]
  have hsum : (∑' j, complexWeightTermSecondDerivative c (r : ℂ) j).re =
      ∑' j, weightTermSecondDerivative c r j := by
    rw [Complex.re_tsum hc]
    apply tsum_congr
    intro j
    simp only [complexWeightTermSecondDerivative_ofReal, Complex.ofReal_re]
  simpa only [hfun, hsum] using hr

lemma weightTermSecondDerivative_mul (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    r^2 * weightTermSecondDerivative c r j =
      (2*(j : ℝ))*(2*(j : ℝ)-1)*weightTerm c r j := by
  cases j with
  | zero => simp [weightTermSecondDerivative]
  | succ j =>
    unfold weightTermSecondDerivative weightTerm
    rw [show 2*(j+1) = 2*j+2 by omega,
      show 2*j+2-1 = 2*j+1 by omega, show 2*j+2-2 = 2*j by omega]
    have hp : r^2 * r^(2*j) = r^(2*j+2) := by rw [← pow_add]; congr 1; omega
    calc
      r^2 * (coefficient c (j+1)*((2*j+2 : ℕ) : ℝ)*((2*j+1 : ℕ) : ℝ)*r^(2*j)) =
        coefficient c (j+1)*((2*j+2 : ℕ) : ℝ)*((2*j+1 : ℕ) : ℝ)*(r^2*r^(2*j)) := by ring
      _ = _ := by rw [hp]; push_cast; ring

lemma weight_secondDerivative_mul (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    r^2 * deriv (deriv (weight c)) r =
      ∑' j : ℕ, (2*(j : ℝ))*(2*(j : ℝ)-1)*weightTerm c r j := by
  have hs := weightTermSecondDerivative_summable lower upper c hlower hbound hupper r
  have hm : Summable (fun j : ℕ => (2*(j : ℝ))*(2*(j : ℝ)-1)*weightTerm c r j) :=
    (hs.mul_left (r^2)).congr (fun j => weightTermSecondDerivative_mul c r j)
  rw [(weight_deriv_hasDerivAt lower upper c hlower hbound hupper r).deriv, ← hs.tsum_mul_left]
  exact tsum_congr (fun j => weightTermSecondDerivative_mul c r j)

end NlsGge.Weights
