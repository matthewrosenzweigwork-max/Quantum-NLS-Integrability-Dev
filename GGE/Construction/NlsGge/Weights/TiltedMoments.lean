import NlsGge.Weights.PoissonQuantitative
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

lemma weightedPoissonFourth_uniform_bounds (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ t : ℝ, 4 ≤ t →
        L*t^(-3/2 : ℝ) ≤ (∑' j : ℕ, c j*(poissonTerm t j)^4) ∧
        (∑' j : ℕ, c j*(poissonTerm t j)^4) ≤ U*t^(-3/2 : ℝ) := by
  obtain ⟨L, U, hL, hU, hsum⟩ := poissonFourth_sum_bounds
  refine ⟨lower*L, upper*U, mul_pos hlower hL,
    mul_pos (hlower.trans_le hlower_upper) hU, ?_⟩
  intro c hbound hupper t ht
  have ht0 : 0 ≤ t := by linarith
  have hs := poissonTerm_fourth_summable t ht0
  have hw := weightedPoissonFourth_summable lower upper c hlower hbound hupper t ht0
  constructor
  · calc
      lower*L*t^(-3/2 : ℝ) ≤ lower*(∑' j : ℕ, (poissonTerm t j)^4) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hsum t ht).1 hlower.le
      _ = ∑' j : ℕ, lower*(poissonTerm t j)^4 := (hs.tsum_mul_left lower).symm
      _ ≤ ∑' j : ℕ, c j*(poissonTerm t j)^4 := (hs.mul_left lower).tsum_le_tsum
        (fun j => mul_le_mul_of_nonneg_right (hbound j) (pow_nonneg (poissonTerm_nonneg t ht0 j) _)) hw
  · calc
      (∑' j : ℕ, c j*(poissonTerm t j)^4) ≤ ∑' j : ℕ, upper*(poissonTerm t j)^4 :=
        hw.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right (hupper j)
          (pow_nonneg (poissonTerm_nonneg t ht0 j) _)) (hs.mul_left upper)
      _ = upper*(∑' j : ℕ, (poissonTerm t j)^4) := hs.tsum_mul_left upper
      _ ≤ upper*U*t^(-3/2 : ℝ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hsum t ht).2
          (hlower.trans_le hlower_upper).le

lemma weightedCenteredPoissonFourth_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4)) := by
  apply ((poissonTerm_centeredSecondMoment_hasSum t ht).summable.mul_left upper).of_nonneg_of_le
    (fun j => mul_nonneg (sq_nonneg _) (mul_nonneg (hlower.trans_le (hbound j)).le
      (pow_nonneg (poissonTerm_nonneg t ht j) _)))
  intro j
  have hp3 : (poissonTerm t j)^3 ≤ 1 := by
    simpa using pow_le_pow_left₀ (poissonTerm_nonneg t ht j) (poissonTerm_le_one t ht j) 3
  have hp4 : (poissonTerm t j)^4 ≤ poissonTerm t j := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp3 (poissonTerm_nonneg t ht j)
  have hu : 0 ≤ upper := (hlower.trans_le ((hbound 0).trans (hupper 0))).le
  calc
    ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4) ≤
      ((j : ℝ)-t)^2*(upper*poissonTerm t j) := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right (hupper j) (pow_nonneg (poissonTerm_nonneg t ht j) _)).trans
          (mul_le_mul_of_nonneg_left hp4 hu)) (sq_nonneg _)
    _ = upper*(((j : ℝ)-t)^2*poissonTerm t j) := by ring

lemma probabilityTerm_secondMoment_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (r : ℝ) :
    Summable (fun j : ℕ => (j : ℝ)^2*probabilityTerm c r j) := by
  apply (probabilityTerm_fourthMoment_summable lower upper c hlower hbound hupper r).of_nonneg_of_le
    (fun j => mul_nonneg (sq_nonneg _) (probabilityTerm_nonneg lower upper c hlower hbound hupper r j))
  intro j
  have hjpow : (j : ℝ)^2 ≤ (j : ℝ)^4 := by
    by_cases hj : j = 0
    · simp [hj]
    · exact pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj) (by norm_num : 2 ≤ 4)
  exact mul_le_mul_of_nonneg_right hjpow (probabilityTerm_nonneg lower upper c hlower hbound hupper r j)

lemma probabilityTerm_centeredSecondMoment_summable (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) := by
  have hs := (weightedCenteredPoissonFourth_summable lower upper c hlower hbound hupper t ht).div_const
    (∑' j : ℕ, c j*(poissonTerm t j)^4)
  apply hs.congr
  intro j
  rw [probabilityTerm_poissonFourth_identity lower upper c hlower hbound hupper t ht j]
  exact mul_div_assoc _ _ _

lemma probabilityTerm_centeredSecondMoment_identity (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) =
      (∑' j : ℕ, ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4)) /
        (∑' j : ℕ, c j*(poissonTerm t j)^4) := by
  have hd := weightedPoissonFourth_pos lower upper c hlower hbound hupper t ht
  have hs := (weightedCenteredPoissonFourth_summable lower upper c hlower hbound hupper t ht).hasSum.div_const
    (∑' j : ℕ, c j*(poissonTerm t j)^4)
  exact (hs.congr_fun (fun j => by
    rw [probabilityTerm_poissonFourth_identity lower upper c hlower hbound hupper t ht j]
    exact (mul_div_assoc _ _ _).symm)).tsum_eq

lemma probabilityTerm_uniform_centeredSecondMoment (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ t : ℝ, 4 ≤ t →
        (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) ≤ C*t := by
  obtain ⟨L, U, hL, hU, hweighted⟩ := weightedPoissonFourth_uniform_bounds lower upper hlower hlower_upper
  obtain ⟨C, hC, hmax⟩ := poisson_uniform_upper
  have hu : 0 < upper := hlower.trans_le hlower_upper
  refine ⟨upper*C^3/L, div_pos (mul_pos hu (pow_pos hC _)) hL, ?_⟩
  intro c hbound hupper t ht
  have ht0 : 0 < t := by linarith
  have hd := weightedPoissonFourth_pos lower upper c hlower hbound hupper t ht0.le
  have hs := weightedCenteredPoissonFourth_summable lower upper c hlower hbound hupper t ht0.le
  have hmajor := (poissonTerm_centeredSecondMoment_hasSum t ht0.le).summable.mul_left
    (upper*(C*t^(-1/2 : ℝ))^3)
  have hpoint (j : ℕ) : ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4) ≤
      (upper*(C*t^(-1/2 : ℝ))^3)*(((j : ℝ)-t)^2*poissonTerm t j) := by
    have hp := pow_le_pow_left₀ (poissonTerm_nonneg t ht0.le j) (hmax t (by linarith) j) 3
    have h4 : (poissonTerm t j)^4 ≤ (C*t^(-1/2 : ℝ))^3*poissonTerm t j := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right hp (poissonTerm_nonneg t ht0.le j)
    calc
      ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4) ≤
        ((j : ℝ)-t)^2*(upper*((C*t^(-1/2 : ℝ))^3*poissonTerm t j)) :=
          mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right (hupper j) (pow_nonneg (poissonTerm_nonneg t ht0.le j) _)).trans
              (mul_le_mul_of_nonneg_left h4 hu.le)) (sq_nonneg _)
      _ = _ := by ring
  have hn := hs.tsum_le_tsum hpoint hmajor
  rw [(poissonTerm_centeredSecondMoment_hasSum t ht0.le).summable.tsum_mul_left,
    (poissonTerm_centeredSecondMoment_hasSum t ht0.le).tsum_eq] at hn
  have hp : (C*t^(-1/2 : ℝ))^3 = C^3*t^(-3/2 : ℝ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast ht0.le]
    norm_num
  rw [hp] at hn
  rw [probabilityTerm_centeredSecondMoment_identity lower upper c hlower hbound hupper t ht0.le]
  apply (div_le_iff₀ hd).mpr
  calc
    (∑' j : ℕ, ((j : ℝ)-t)^2*(c j*(poissonTerm t j)^4)) ≤
      upper*(C^3*t^(-3/2 : ℝ))*t := hn
    _ = (upper*C^3/L*t)*(L*t^(-3/2 : ℝ)) := by field_simp [hL.ne']
    _ ≤ (upper*C^3/L*t)*(∑' j : ℕ, c j*(poissonTerm t j)^4) :=
      mul_le_mul_of_nonneg_left (hweighted c hbound hupper t ht).1 (by positivity)

lemma probabilityTerm_centeredFirstMoment_holder (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    Summable (fun j : ℕ => |(j : ℝ)-t| *probabilityTerm c (t^2) j) ∧
      (∑' j : ℕ, |(j : ℝ)-t| *probabilityTerm c (t^2) j) ≤
        Real.sqrt (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) := by
  let b := probabilityTerm c (t^2)
  let f := fun j : ℕ => |(j : ℝ)-t| *Real.sqrt (b j)
  let g := fun j : ℕ => Real.sqrt (b j)
  have hb (j : ℕ) : 0 ≤ b j := probabilityTerm_nonneg lower upper c hlower hbound hupper (t^2) j
  have hf (j : ℕ) : 0 ≤ f j := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hg (j : ℕ) : 0 ≤ g j := Real.sqrt_nonneg _
  have hF (j : ℕ) : f j^(2 : ℝ) = ((j : ℝ)-t)^2*b j := by
    dsimp [f]
    rw [Real.rpow_ofNat, mul_pow, sq_abs, Real.sq_sqrt (hb j)]
  have hG (j : ℕ) : g j^(2 : ℝ) = b j := by
    dsimp [g]
    rw [Real.rpow_ofNat, Real.sq_sqrt (hb j)]
  have hprod (j : ℕ) : f j*g j = |(j : ℝ)-t| *b j := by
    dsimp [f, g]
    rw [mul_assoc, Real.mul_self_sqrt (hb j)]
  have hpq : Real.HolderConjugate (2 : ℝ) 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have hFsum : Summable (fun j : ℕ => f j^(2 : ℝ)) := by
    simp only [hF]
    exact probabilityTerm_centeredSecondMoment_summable lower upper c hlower hbound hupper t ht
  have hGsum : Summable (fun j : ℕ => g j^(2 : ℝ)) := by
    simp only [hG]
    exact probabilityTerm_summable lower upper c hlower hbound hupper (t^2)
  have hbsum : (∑' j : ℕ, b j) = 1 := (probabilityTerm_hasSum lower upper c hlower hbound hupper (t^2)).tsum_eq
  have hh := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf hg hFsum hGsum
  constructor
  · simpa only [hprod] using hh.1
  · simpa only [hprod, hF, hG, hbsum, Real.one_rpow, mul_one, Real.sqrt_eq_rpow] using hh.2

lemma probabilityTerm_centeredFirstMoment_identity (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => ((j : ℝ)-t)*probabilityTerm c (t^2) j)
      ((∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t) := by
  have hs := (probabilityTerm_firstMoment_holder lower upper c hlower hbound hupper (t^2)).1.hasSum.sub
    ((probabilityTerm_hasSum lower upper c hlower hbound hupper (t^2)).mul_left t)
  simpa only [mul_one] using hs.congr_fun (fun j => by ring)

lemma probabilityTerm_firstMoment_centered_le (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    |(∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t| ≤
      Real.sqrt (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) := by
  have hh := probabilityTerm_centeredFirstMoment_holder lower upper c hlower hbound hupper t ht
  have hb (j : ℕ) := probabilityTerm_nonneg lower upper c hlower hbound hupper (t^2) j
  have hnorm_eq (j : ℕ) : ‖((j : ℝ)-t)*probabilityTerm c (t^2) j‖ =
      |(j : ℝ)-t| *probabilityTerm c (t^2) j := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb j)]
  have hn : Summable (fun j : ℕ => ‖((j : ℝ)-t)*probabilityTerm c (t^2) j‖) :=
    hh.1.congr (fun j => (hnorm_eq j).symm)
  have hi := (probabilityTerm_centeredFirstMoment_identity lower upper c hlower hbound hupper t ht).tsum_eq
  have hnorm := norm_tsum_le_tsum_norm hn
  rw [hi] at hnorm
  have habs : |(∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t| ≤
      (∑' j : ℕ, |(j : ℝ)-t| *probabilityTerm c (t^2) j) := by
    simpa only [Real.norm_eq_abs, hnorm_eq] using hnorm
  exact habs.trans hh.2

lemma probabilityTerm_secondMoment_centered_identity (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) (t : ℝ) (ht : 0 ≤ t) :
    (∑' j : ℕ, (j : ℝ)^2*probabilityTerm c (t^2) j)-t^2 =
      (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) +
        2*t*((∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t) := by
  have hs := ((probabilityTerm_secondMoment_summable lower upper c hlower hbound hupper (t^2)).hasSum.sub
    ((probabilityTerm_firstMoment_holder lower upper c hlower hbound hupper (t^2)).1.hasSum.mul_left (2*t))).add
    ((probabilityTerm_hasSum lower upper c hlower hbound hupper (t^2)).mul_left (t^2))
  have hi : (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) =
      (∑' j : ℕ, (j : ℝ)^2*probabilityTerm c (t^2) j) -
        (2*t)*(∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j) + t^2*1 :=
    (hs.congr_fun (fun j => by ring)).tsum_eq
  rw [hi]
  ring

lemma probabilityTerm_uniform_firstSecondMoments (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℕ → ℝ,
      (∀ j : ℕ, lower ≤ c j) → (∀ j : ℕ, c j ≤ upper) →
      ∀ t : ℝ, 4 ≤ t →
        |(∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t| ≤ C*Real.sqrt t ∧
        |(∑' j : ℕ, (j : ℝ)^2*probabilityTerm c (t^2) j)-t^2| ≤ C*t^(3/2 : ℝ) := by
  obtain ⟨V, hV, hvariance⟩ := probabilityTerm_uniform_centeredSecondMoment lower upper hlower hlower_upper
  let C : ℝ := 2*Real.sqrt V+V+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro c hbound hupper t ht
  have ht0 : 0 ≤ t := by linarith
  have hsqrt : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr (by linarith)
  have hv := hvariance c hbound hupper t ht
  have hmean : |(∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t| ≤ Real.sqrt V*Real.sqrt t := by
    calc
      _ ≤ Real.sqrt (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) :=
        probabilityTerm_firstMoment_centered_le lower upper c hlower hbound hupper t ht0
      _ ≤ Real.sqrt (V*t) := Real.sqrt_le_sqrt hv
      _ = _ := Real.sqrt_mul hV.le t
  have hp : t*Real.sqrt t = t^(3/2 : ℝ) := by
    calc
      t*Real.sqrt t = t^(1 : ℝ)*t^(1/2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = t^((1 : ℝ)+1/2) := (Real.rpow_add (by linarith : 0 < t) 1 (1/2)).symm
      _ = t^(3/2 : ℝ) := by congr 1; norm_num
  constructor
  · exact hmean.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Real.sqrt_nonneg V])
      (Real.sqrt_nonneg t))
  · rw [probabilityTerm_secondMoment_centered_identity lower upper c hlower hbound hupper t ht0]
    have hv0 : 0 ≤ (∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j) :=
      tsum_nonneg (fun j => mul_nonneg (sq_nonneg _) (probabilityTerm_nonneg lower upper c hlower hbound hupper (t^2) j))
    calc
      _ ≤ |(∑' j : ℕ, ((j : ℝ)-t)^2*probabilityTerm c (t^2) j)| +
        |2*t*((∑' j : ℕ, (j : ℝ)*probabilityTerm c (t^2) j)-t)| := abs_add_le _ _
      _ ≤ V*t+(2*t)*(Real.sqrt V*Real.sqrt t) := by
        rw [abs_of_nonneg hv0, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*t)]
        exact add_le_add hv (mul_le_mul_of_nonneg_left hmean (by positivity))
      _ ≤ (2*Real.sqrt V+V)*(t*Real.sqrt t) := by
        have hvscale := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hV.le ht0)
        nlinarith
      _ ≤ C*(t*Real.sqrt t) := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
        (mul_nonneg ht0 (Real.sqrt_nonneg t))
      _ = C*t^(3/2 : ℝ) := by rw [hp]

end NlsGge.Weights
