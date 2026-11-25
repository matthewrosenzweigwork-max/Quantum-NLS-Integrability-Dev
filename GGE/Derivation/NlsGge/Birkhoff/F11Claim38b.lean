import NlsGge.Birkhoff.F11Claim38

/-! # NEW-F11 (`F:cor:charge`), file 2: the free-normalizer product `D_{p,N}` (NEW-F11.02), `B`-free

Source: `paper/v2.tex` l.1809-1812: "The product `D_{p,N} = ∏_{|n|≤N}(1 - p(2πn)/a_n)` converges to a positive
limit: its factors are uniformly bounded away from zero and `Σ_n p(2πn)/a_n < ∞`."

`tiltX38 c J t n = p(2πn)/a_n`, `tiltDet38 c J t N = ∏_{|n|≤N} (1 - tiltX38 c J t n)` (product over
`modeIndex N i`, `i : Fin (2N+1)`, as in `freeNormalizer38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.HierarchyRiccati.Core Filter Topology
open scoped Real

section Det

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (J : ℕ) (t : ℕ → ℝ)

/-- `p(2πn)/a_n`. -/
def tiltX38 (n : ℤ) : ℝ :=
  tiltPoly38 J t (2 * Real.pi * (n : ℝ)) / fullWeightRate c.val n

/-- `D_{p,N} = ∏_{|n|≤N} (1 - p(2πn)/a_n)` (v2 l.1810). -/
def tiltDet38 (N : ℕ) : ℝ :=
  ∏ i : Fin (2 * N + 1), (1 - tiltX38 c J t (modeIndex N i))

variable {c J t}

theorem one_sub_tiltX38 (ht : TiltAdmissible38 c J t) (n : ℤ) :
    1 - tiltX38 c J t n =
      fullWeightRate (tiltCoeff38 c.val J t) n / fullWeightRate c.val n := by
  have ha := fullWeightRate_pos38 c n
  unfold tiltX38
  have h : fullWeightRate (tiltCoeff38 c.val J t) n =
      fullWeightRate c.val n - tiltPoly38 J t (2 * Real.pi * (n : ℝ)) := by
    unfold fullWeightRate
    exact weight_tilt38 c ht _
  rw [h]
  field_simp

theorem tiltX38_nonneg (ht : TiltAdmissible38 c J t) (n : ℤ) : 0 ≤ tiltX38 c J t n :=
  div_nonneg (tiltPoly38_nonneg J t (fun j hj => (ht j hj).1) _) (fullWeightRate_pos38 c n).le

/-- With `ε` as in `exists_tiltRatio38`: every factor `1 - x_n` lies in `[ε, 1]`. -/
theorem tiltFactor_ge38 (ht : TiltAdmissible38 c J t) {ε : ℝ}
    (hε : ∀ r : ℝ, ε * weight c.val r ≤ weight (tiltCoeff38 c.val J t) r) (n : ℤ) :
    ε ≤ 1 - tiltX38 c J t n := by
  rw [one_sub_tiltX38 ht n, le_div_iff₀ (fullWeightRate_pos38 c n)]
  exact hε _

theorem tiltFactor_le38 (ht : TiltAdmissible38 c J t) (n : ℤ) : 1 - tiltX38 c J t n ≤ 1 := by
  linarith [tiltX38_nonneg ht n]

theorem tiltFactor_pos38 (ht : TiltAdmissible38 c J t) (n : ℤ) : 0 < 1 - tiltX38 c J t n := by
  rw [one_sub_tiltX38 ht n]
  exact div_pos (fullWeightRate_pos38 (tiltedCoefficients38 c ht) n) (fullWeightRate_pos38 c n)

/-- `Σ_n p(2πn)/a_n < ∞` (v2 l.1811). -/
theorem summable_tiltX38 (ht : TiltAdmissible38 c J t) : Summable (tiltX38 c J t) := by
  have hl := c.property.1
  set κ : ℝ := NlsGge.coefficient c.val (J + 1) with hκ
  have hκpos : 0 < κ := by
    have := hl.trans_le (c.property.2.2 (J + 1)).1
    rw [hκ]; unfold NlsGge.coefficient; positivity
  set T : ℝ := ∑ j ∈ Finset.range (J + 1), t j with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun j hj => (ht j (by simpa [Nat.lt_succ_iff] using hj)).1
  have hsum : Summable (fun n : ℤ => T / (κ * (2 * Real.pi) ^ 2) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.2 (by norm_num)).mul_left _
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hev := (Set.finite_singleton (0 : ℤ)).eventually_cofinite_notMem
  filter_upwards [hev] with n hn
  have hn0 : n ≠ 0 := by simpa using hn
  set r : ℝ := 2 * Real.pi * (n : ℝ) with hr
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast this
  have hr1 : 1 ≤ r ^ 2 := by
    have h2 : (1 : ℝ) ≤ |r| := by
      rw [hr, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    nlinarith [sq_abs r]
  have hrpos : 0 < r ^ 2 := by linarith
  -- bound the polynomial
  have hp : tiltPoly38 J t r ≤ T * (r ^ 2) ^ J := by
    unfold tiltPoly38
    rw [hT, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjJ : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 hjJ) (ht j hjJ).1
  -- bound the weight from below by a single term
  have hw : κ * (r ^ 2) ^ (J + 1) ≤ fullWeightRate c.val n := by
    have hs := weightTerm_summable lower upper c.val hl (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2) r
    have := hs.le_tsum (J + 1) (fun j _ => by
      unfold NlsGge.weightTerm
      exact mul_nonneg (coefficient_nonneg_F11_38 c j) (by rw [pow_mul]; positivity))
    unfold NlsGge.weightTerm at this
    rw [pow_mul] at this
    exact this
  rw [Real.norm_eq_abs, abs_of_nonneg (tiltX38_nonneg ht n)]
  unfold tiltX38
  have hapos := fullWeightRate_pos38 c n
  calc tiltPoly38 J t (2 * Real.pi * (n : ℝ)) / fullWeightRate c.val n
      ≤ (T * (r ^ 2) ^ J) / (κ * (r ^ 2) ^ (J + 1)) := by
        rw [← hr]
        exact div_le_div₀ (by positivity) hp (by positivity) hw
    _ = T / (κ * (2 * Real.pi) ^ 2) * (1 / (n : ℝ) ^ 2) := by
        have h2 : r ^ 2 = (2 * Real.pi) ^ 2 * (n : ℝ) ^ 2 := by rw [hr]; ring
        have hn2 : (n : ℝ) ^ 2 ≠ 0 := by
          have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
          positivity
        rw [pow_succ (r ^ 2) J, h2]
        have : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
        have hJ0 : ((2 * Real.pi) ^ 2 * (n : ℝ) ^ 2) ^ J ≠ 0 := by positivity
        have hκ0 := hκpos.ne'
        field_simp

/-- For `0 < ε ≤ y ≤ 1`: `y ≥ exp(-(1 - y)/ε)`. -/
theorem exp_neg_le_of_ge38 {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) (hy1 : y ≤ 1) :
    Real.exp (-((1 - y) / ε)) ≤ y := by
  have hy0 : 0 < y := hε.trans_le hy
  have h1 := Real.one_sub_inv_le_log_of_pos hy0
  have h2 : -((1 - y) / ε) ≤ 1 - y⁻¹ := by
    have : 1 - y⁻¹ = -((1 - y) / y) := by field_simp; ring
    rw [this, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by linarith) hε hy
  calc Real.exp (-((1 - y) / ε)) ≤ Real.exp (Real.log y) := Real.exp_le_exp.2 (h2.trans h1)
    _ = y := Real.exp_log hy0

theorem prod_modeIndex_eq38 (N : ℕ) (f : ℤ → ℝ) :
    ∏ i : Fin (2 * N + 1), f (modeIndex N i) = ∏ n ∈ symmetricModes N, f n := by
  rw [NlsGge.Ramer.symmetricModes_eq_image, Finset.prod_image (fun i _ j _ h => modeIndex_injective N h)]

theorem sum_modeIndex_eq38 (N : ℕ) (f : ℤ → ℝ) :
    ∑ i : Fin (2 * N + 1), f (modeIndex N i) = ∑ n ∈ symmetricModes N, f n := by
  rw [NlsGge.Ramer.symmetricModes_eq_image, Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]

theorem tiltDet_eq_prod38 (N : ℕ) :
    tiltDet38 c J t N = ∏ n ∈ symmetricModes N, (1 - tiltX38 c J t n) :=
  prod_modeIndex_eq38 N (fun n => 1 - tiltX38 c J t n)

theorem tiltDet_pos38 (ht : TiltAdmissible38 c J t) (N : ℕ) : 0 < tiltDet38 c J t N :=
  Finset.prod_pos fun i _ => tiltFactor_pos38 ht _

theorem tiltDet_le_one38 (ht : TiltAdmissible38 c J t) (N : ℕ) : tiltDet38 c J t N ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => (tiltFactor_pos38 ht _).le) fun i _ => tiltFactor_le38 ht _

/-- **NEW-F11.02 (uniform positivity).** `D_{p,N} ≥ δ > 0` for every `N`. -/
theorem tiltDet_lower38 (ht : TiltAdmissible38 c J t) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, δ ≤ tiltDet38 c J t N := by
  obtain ⟨ε, hε0, hε1, hε⟩ := exists_tiltRatio38 c ht
  have hsum := summable_tiltX38 ht
  set S : ℝ := ∑' n, tiltX38 c J t n with hS
  refine ⟨Real.exp (-(S / ε)), Real.exp_pos _, fun N => ?_⟩
  have hfac : ∀ n : ℤ, Real.exp (-(tiltX38 c J t n / ε)) ≤ 1 - tiltX38 c J t n := fun n => by
    have := exp_neg_le_of_ge38 hε0 (tiltFactor_ge38 ht hε n) (tiltFactor_le38 ht n)
    simpa using this
  rw [tiltDet_eq_prod38]
  calc Real.exp (-(S / ε)) ≤ Real.exp (-(∑ n ∈ symmetricModes N, tiltX38 c J t n / ε)) := by
        refine Real.exp_le_exp.2 ?_
        rw [neg_le_neg_iff, ← Finset.sum_div]
        refine div_le_div_of_nonneg_right ?_ hε0.le
        exact hsum.sum_le_tsum _ (fun n _ => tiltX38_nonneg ht n)
    _ = ∏ n ∈ symmetricModes N, Real.exp (-(tiltX38 c J t n / ε)) := by
        rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun n _ => (Real.exp_pos _).le) fun n _ => hfac n

theorem tiltDet_antitone38 (ht : TiltAdmissible38 c J t) : Antitone (tiltDet38 c J t) := by
  intro N M hNM
  have hsub : symmetricModes N ⊆ symmetricModes M := by
    intro n hn
    simp only [symmetricModes, Finset.mem_Icc] at hn ⊢
    have : (N : ℤ) ≤ M := by exact_mod_cast hNM
    omega
  rw [tiltDet_eq_prod38, tiltDet_eq_prod38, ← Finset.prod_sdiff hsub]
  have h1 : ∏ n ∈ symmetricModes M \ symmetricModes N, (1 - tiltX38 c J t n) ≤ 1 :=
    Finset.prod_le_one₀ (fun n _ => (tiltFactor_pos38 ht n).le) fun n _ => tiltFactor_le38 ht n
  have h2 : 0 ≤ ∏ n ∈ symmetricModes N, (1 - tiltX38 c J t n) :=
    Finset.prod_nonneg fun n _ => (tiltFactor_pos38 ht n).le
  nlinarith

/-- **NEW-F11.02.** `D_{p,N}` converges, as `N → ∞`, to a positive limit. -/
theorem tiltDet_tendsto38 (ht : TiltAdmissible38 c J t) :
    ∃ D : ℝ, 0 < D ∧ Tendsto (tiltDet38 c J t) atTop (𝓝 D) := by
  obtain ⟨δ, hδ, hlow⟩ := tiltDet_lower38 ht
  have hbdd : BddBelow (Set.range (tiltDet38 c J t)) := ⟨δ, by rintro _ ⟨N, rfl⟩; exact hlow N⟩
  refine ⟨⨅ N, tiltDet38 c J t N, ?_, tendsto_atTop_ciInf (tiltDet_antitone38 ht) hbdd⟩
  exact lt_of_lt_of_le hδ (le_ciInf hlow)

end Det

end NlsGge.Birkhoff
end
