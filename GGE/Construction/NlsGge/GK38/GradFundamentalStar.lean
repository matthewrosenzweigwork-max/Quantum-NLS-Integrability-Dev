import NlsGge.GK38.GradFundamentalDefs

/-! # K1: star identity for solutions with two independent complex potentials.
GK Chapter I, Lemma 8.2. The primitive comparison uses absolute continuity,
a.e. differential equations and an integrable right-hand side.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

-- Adapter1: use Mathlib's generated pointwise derivative API.
theorem k1PointwiseSub38 {f g : ℝ → ℂ} {a b : ℂ} {x : ℝ}
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    HasDerivAt (fun y => f y - g y) (a - b) x :=
  hf.fun_sub hg

-- Adapter2: evaluate the primitive difference explicitly before normalization.
theorem k1PrimitiveZero38 {f g : ℝ → ℂ} {C : ℂ}
    (h : (f - fun x => ∫ r in (0 : ℝ)..x, g r) 0 = C) : f 0 = C := by
  change f 0 - (∫ r in (0 : ℝ)..0, g r) = C at h
  simpa only [intervalIntegral.integral_same, sub_zero] using h

-- Adapter3: explicit interval and pointwise continuity APIs.
theorem k1IntervalProductContinuous38 {a b c d : ℝ → ℂ}
    (ha : ContinuousOn a (Set.uIcc (0 : ℝ) 1))
    (hb : ContinuousOn b (Set.uIcc (0 : ℝ) 1))
    (hc : ContinuousOn c (Set.uIcc (0 : ℝ) 1))
    (hd : ContinuousOn d (Set.uIcc (0 : ℝ) 1)) :
    ContinuousOn (fun s => a s * b s - c s * d s) (Set.Icc (0 : ℝ) 1) := by
  rw [← Set.uIcc_of_le zero_le_one]
  exact (ha.fun_mul hb).fun_sub (hc.fun_mul hd)


/-- Componentwise absolutely continuous solution of the accepted ZS coefficient. -/
def IsPairSolution38 (φ : PotPair) (z : ℂ) (f : ℝ → PairVec38) : Prop :=
  (∀ i, AbsolutelyContinuousOnInterval (fun s => f s i) 0 1) ∧
  ∀ i, ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
    HasDerivAt (fun r => f r i) ((zsCoeffPot38 φ z s).mulVec (f s) i) s

/-- Complex AC fundamental theorem with an independently specified integrable derivative. -/
theorem ac_integral_eq_sub38 {f g : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hd : ∀ᵐ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → HasDerivAt f (g x) x)
    (t : Set.Icc (0 : ℝ) 1) : (∫ s in (0 : ℝ)..(t : ℝ), g s) = f t - f 0 := by
  have hp := ac_primitive38 hg (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 1)
  have hdiff : ∀ᵐ x : ℝ, x ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun y => f y - ∫ s in (0 : ℝ)..y, g s) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral] with x hdx hpx hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using hx
    simpa only [sub_self] using k1PointwiseSub38 (hdx hx') (hpx hx 0 Set.left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hf.sub hp).const_of_ae_hasDerivAt_zero hdiff
  have h0 := hC 0 Set.left_mem_uIcc
  have ht := hC t (by simpa [Set.uIcc_of_le zero_le_one] using t.2)
  have h0' : f 0 = C := k1PrimitiveZero38 h0
  rw [← h0'] at ht
  change f t - (∫ s in (0 : ℝ)..(t : ℝ), g s) = f 0 at ht
  linear_combination -ht

theorem ac_pairBracket38 {a b : ℝ → PairVec38}
    (ha : ∀ i, AbsolutelyContinuousOnInterval (fun s => a s i) 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (fun s => b s i) 0 1) :
    AbsolutelyContinuousOnInterval (fun s => pairBracket38 (a s) (b s)) 0 1 :=
  ((ha 0).smul (hb 1)).sub ((ha 1).smul (hb 0))

/-- Pointwise algebra after all eight component derivatives have been established. -/
theorem hasDerivAt_starIdentity38 (φ ψ : PotPair) (μ ν : ℂ)
    (a b c d : ℝ → PairVec38) (s : ℝ)
    (ha : ∀ i, HasDerivAt (fun r => a r i) ((zsCoeffPot38 φ μ s).mulVec (a s) i) s)
    (hb : ∀ i, HasDerivAt (fun r => b r i) ((zsCoeffPot38 φ ν s).mulVec (b s) i) s)
    (hc : ∀ i, HasDerivAt (fun r => c r i) ((zsCoeffPot38 ψ μ s).mulVec (c s) i) s)
    (hd : ∀ i, HasDerivAt (fun r => d r i) ((zsCoeffPot38 ψ ν s).mulVec (d s) i) s) :
    HasDerivAt (fun r => pairBracket38 (a r) (b r) * pairBracket38 (c r) (d r))
      (2 * Complex.I * (μ - ν) * pairBracket38 (starProd38 (a s) (c s))
        (starProd38 (b s) (d s))) s := by
  have hab := ((ha 0).mul (hb 1)).sub ((ha 1).mul (hb 0))
  have hcd := ((hc 0).mul (hd 1)).sub ((hc 1).mul (hd 0))
  convert hab.mul hcd using 1
  · funext r
    rfl
  · simp [pairBracket38, starProd38, zsCoeffPot38, zsCoeffPair, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Pi.mul_apply, Pi.sub_apply]
    ring

/-- A.e. star identity; φ and ψ remain independent. -/
theorem ae_hasDerivAt_starIdentity38 {φ ψ : PotPair} {μ ν : ℂ}
    {a b c d : ℝ → PairVec38}
    (ha : IsPairSolution38 φ μ a) (hb : IsPairSolution38 φ ν b)
    (hc : IsPairSolution38 ψ μ c) (hd : IsPairSolution38 ψ ν d) :
    ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => pairBracket38 (a r) (b r) * pairBracket38 (c r) (d r))
        (2 * Complex.I * (μ - ν) * pairBracket38 (starProd38 (a s) (c s))
          (starProd38 (b s) (d s))) s := by
  filter_upwards [ha.2 0, ha.2 1, hb.2 0, hb.2 1, hc.2 0, hc.2 1, hd.2 0, hd.2 1]
    with s ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 hs
  apply hasDerivAt_starIdentity38 φ ψ μ ν a b c d s
  · intro i; fin_cases i; exact ha0 hs; exact ha1 hs
  · intro i; fin_cases i; exact hb0 hs; exact hb1 hs
  · intro i; fin_cases i; exact hc0 hs; exact hc1 hs
  · intro i; fin_cases i; exact hd0 hs; exact hd1 hs

theorem intervalIntegrable_starBracket38 {φ ψ : PotPair} {μ ν : ℂ}
    {a b c d : ℝ → PairVec38}
    (ha : IsPairSolution38 φ μ a) (hb : IsPairSolution38 φ ν b)
    (hc : IsPairSolution38 ψ μ c) (hd : IsPairSolution38 ψ ν d) :
    IntervalIntegrable (fun s => pairBracket38 (starProd38 (a s) (c s))
      (starProd38 (b s) (d s))) volume 0 1 := by
  have hac (i : Fin 2) := (ha.1 i).continuousOn
  have hbc (i : Fin 2) := (hb.1 i).continuousOn
  have hcc (i : Fin 2) := (hc.1 i).continuousOn
  have hdc (i : Fin 2) := (hd.1 i).continuousOn
  simp only [pairBracket38, starProd38, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hcont : ContinuousOn (fun s => a s 1 * c s 1 * (b s 0 * d s 0) -
      a s 0 * c s 0 * (b s 1 * d s 1)) (Set.Icc (0 : ℝ) 1) :=
    k1IntervalProductContinuous38 ((hac 1).fun_mul (hcc 1))
      ((hbc 0).fun_mul (hdc 0)) ((hac 0).fun_mul (hcc 0))
      ((hbc 1).fun_mul (hdc 1))
  exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one hcont

theorem integrated_starIdentity38 {φ ψ : PotPair} {μ ν : ℂ}
    {a b c d : ℝ → PairVec38}
    (ha : IsPairSolution38 φ μ a) (hb : IsPairSolution38 φ ν b)
    (hc : IsPairSolution38 ψ μ c) (hd : IsPairSolution38 ψ ν d)
    (t : Set.Icc (0 : ℝ) 1) :
    pairBracket38 (a t) (b t) * pairBracket38 (c t) (d t) -
      pairBracket38 (a 0) (b 0) * pairBracket38 (c 0) (d 0) =
      2 * Complex.I * (μ - ν) * ∫ s in (0 : ℝ)..(t : ℝ),
        pairBracket38 (starProd38 (a s) (c s)) (starProd38 (b s) (d s)) := by
  have hint := (intervalIntegrable_starBracket38 ha hb hc hd).const_mul
    (2 * Complex.I * (μ - ν))
  have h := ac_integral_eq_sub38
    ((ac_pairBracket38 ha.1 hb.1).smul (ac_pairBracket38 hc.1 hd.1)) hint
    (ae_hasDerivAt_starIdentity38 ha hb hc hd) t
  rw [intervalIntegral.integral_const_mul] at h
  exact h.symm


/-- The division form of GK Lemma8.2, with its nonzero spectral difference. -/
theorem integrated_starIdentity_div38 {φ ψ : PotPair} {μ ν : ℂ} (hμν : μ ≠ ν)
    {a b c d : ℝ → PairVec38}
    (ha : IsPairSolution38 φ μ a) (hb : IsPairSolution38 φ ν b)
    (hc : IsPairSolution38 ψ μ c) (hd : IsPairSolution38 ψ ν d)
    (t : Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..(t : ℝ),
      pairBracket38 (starProd38 (a s) (c s)) (starProd38 (b s) (d s))) =
      (pairBracket38 (a t) (b t) * pairBracket38 (c t) (d t) -
        pairBracket38 (a 0) (b 0) * pairBracket38 (c 0) (d 0)) /
          (2 * Complex.I * (μ - ν)) := by
  have hn : 2 * Complex.I * (μ - ν) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (sub_ne_zero.mpr hμν)
  apply (eq_div_iff hn).mpr
  simpa only [mul_comm] using (integrated_starIdentity38 ha hb hc hd t).symm

end
end NlsGge.GK38
