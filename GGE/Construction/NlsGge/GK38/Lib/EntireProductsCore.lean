import NlsGge.GK38.Lib.SymmPair

/-!
# L4a, part 2: `∏'[symmetricIcc ℤ] (σ_m - z)/π_m` is entire (GKP Lemma 20.1; book Lemma C.1)

For `σ = σ° + σ̃` with `σ̃ ∈ ℓ²` (here `prodDev σ n = σ n - nπ`), the factors satisfy
`f_m f_{-m} = 1 + b_m(z)` with `‖b_m(z)‖ ≤ u_R(m)` on `‖z‖ ≤ R`, `u_R` summable (book proof of
Lemma C.1, with `a_m + a_{-m}` and `a_m a_{-m}`).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- Deviation `σ_n - nπ`. -/
def prodDev (σ : ℤ → ℂ) (n : ℤ) : ℂ := σ n - (n : ℂ) * (Real.pi : ℂ)

/-- The `m`-th factor `(σ_m - z)/π_m`. -/
def prodFactor (σ : ℤ → ℂ) (z : ℂ) (m : ℤ) : ℂ := (σ m - z) / (piN m : ℂ)

/-- Deviation of the paired factor from `1`. -/
def pairTerm (σ : ℤ → ℂ) (z : ℂ) (m : ℕ) : ℂ :=
  prodFactor σ z ((m : ℤ) + 1) * prodFactor σ z (-((m : ℤ) + 1)) - 1

theorem pairTerm_eq (σ : ℤ → ℂ) (z : ℂ) (m : ℕ) :
    pairTerm σ z m
      = (prodDev σ ((m : ℤ) + 1) - prodDev σ (-((m : ℤ) + 1))) / (((m : ℂ) + 1) * (Real.pi : ℂ))
        - (prodDev σ ((m : ℤ) + 1) - z) * (prodDev σ (-((m : ℤ) + 1)) - z)
          / (((m : ℂ) + 1) * (Real.pi : ℂ)) ^ 2 := by
  have h1 : ((m : ℤ) + 1) ≠ 0 := by omega
  have h2 : (-((m : ℤ) + 1)) ≠ 0 := by omega
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  unfold pairTerm prodFactor prodDev
  rw [piN_of_ne h1, piN_of_ne h2]
  push_cast
  field_simp
  ring

/-- Real inequality behind the bound. -/
theorem real_pair_bound (x y R k : ℝ) (hk : 1 ≤ k) :
    (x + y) / (k * Real.pi) + (x + R) * (y + R) / (k * Real.pi) ^ 2
      ≤ (1 / Real.pi) * (x ^ 2 + y ^ 2 + 1 / k ^ 2)
        + (x ^ 2 + y ^ 2) / Real.pi ^ 2 + 2 * R ^ 2 / (Real.pi ^ 2 * k ^ 2) := by
  have hpi := Real.pi_pos
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have e1 : (x + y) / k ≤ x ^ 2 + y ^ 2 + 1 / k ^ 2 := by
    have : x / k ≤ (x ^ 2 + 1 / k ^ 2) / 2 := by
      have : (x - 1 / k) ^ 2 ≥ 0 := sq_nonneg _
      have h : 1 / k ^ 2 = (1 / k) ^ 2 := by rw [one_div_pow]
      rw [h]; nlinarith [div_eq_mul_one_div x k]
    have : y / k ≤ (y ^ 2 + 1 / k ^ 2) / 2 := by
      have : (y - 1 / k) ^ 2 ≥ 0 := sq_nonneg _
      have h : 1 / k ^ 2 = (1 / k) ^ 2 := by rw [one_div_pow]
      rw [h]; nlinarith [div_eq_mul_one_div y k]
    have h3 : 0 ≤ 1 / k ^ 2 := by positivity
    have : (x + y) / k = x / k + y / k := add_div _ _ _
    nlinarith
  have e2 : (x + y) / (k * Real.pi) ≤ (1 / Real.pi) * (x ^ 2 + y ^ 2 + 1 / k ^ 2) := by
    have : (x + y) / (k * Real.pi) = ((x + y) / k) * (1 / Real.pi) := by
      field_simp
    rw [this, mul_comm]
    exact mul_le_mul_of_nonneg_left e1 (by positivity)
  have e3 : (x + R) * (y + R) / (k * Real.pi) ^ 2
      ≤ (x ^ 2 + y ^ 2) / Real.pi ^ 2 + 2 * R ^ 2 / (Real.pi ^ 2 * k ^ 2) := by
    have hnum : (x + R) * (y + R) ≤ (x ^ 2 + y ^ 2) + 2 * R ^ 2 := by
      nlinarith [sq_nonneg (x - R), sq_nonneg (y - R), sq_nonneg (x - y)]
    have hd : 0 < (k * Real.pi) ^ 2 := by positivity
    calc (x + R) * (y + R) / (k * Real.pi) ^ 2
        ≤ ((x ^ 2 + y ^ 2) + 2 * R ^ 2) / (k * Real.pi) ^ 2 :=
          div_le_div_of_nonneg_right hnum hd.le
      _ = (x ^ 2 + y ^ 2) / (k * Real.pi) ^ 2 + 2 * R ^ 2 / (Real.pi ^ 2 * k ^ 2) := by
          rw [add_div]; congr 2; ring
      _ ≤ (x ^ 2 + y ^ 2) / Real.pi ^ 2 + 2 * R ^ 2 / (Real.pi ^ 2 * k ^ 2) := by
          gcongr
          nlinarith [sq_nonneg x, sq_nonneg y]
  linarith

theorem norm_pairTerm_le (σ : ℤ → ℂ) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (m : ℕ) :
    ‖pairTerm σ z m‖ ≤
      (‖prodDev σ ((m : ℤ) + 1)‖ + ‖prodDev σ (-((m : ℤ) + 1))‖) / (((m : ℝ) + 1) * Real.pi)
      + (‖prodDev σ ((m : ℤ) + 1)‖ + R) * (‖prodDev σ (-((m : ℤ) + 1))‖ + R)
          / (((m : ℝ) + 1) * Real.pi) ^ 2 := by
  rw [pairTerm_eq]
  set k : ℝ := (m : ℝ) + 1 with hkdef
  have hk : 0 < k := by positivity
  have hkc : ((m : ℂ) + 1) = (k : ℂ) := by simp [hkdef]
  rw [hkc]
  have hnk : ‖((k : ℂ) * (Real.pi : ℂ))‖ = k * Real.pi := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hk.le,
      Real.norm_of_nonneg Real.pi_pos.le]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, hnk]
    gcongr
    exact (norm_sub_le _ _)
  · rw [norm_div, norm_pow, hnk, norm_mul]
    have hR : 0 ≤ R := (norm_nonneg z).trans hz
    have h1 : ‖prodDev σ ((m : ℤ) + 1) - z‖ ≤ ‖prodDev σ ((m : ℤ) + 1)‖ + R :=
      (norm_sub_le _ _).trans (by linarith)
    have h2 : ‖prodDev σ (-((m : ℤ) + 1)) - z‖ ≤ ‖prodDev σ (-((m : ℤ) + 1))‖ + R :=
      (norm_sub_le _ _).trans (by linarith)
    exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _)
      (by have := norm_nonneg (prodDev σ ((m : ℤ) + 1)); linarith)) (by positivity)

theorem summable_dev_sq {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) :
    Summable (fun m : ℕ => ‖prodDev σ ((m : ℤ) + 1)‖ ^ 2) ∧
      Summable (fun m : ℕ => ‖prodDev σ (-((m : ℤ) + 1))‖ ^ 2) := by
  constructor
  · refine hσ.comp_injective (i := fun m : ℕ => (m : ℤ) + 1) ?_
    intro a b h; simpa using h
  · refine hσ.comp_injective (i := fun m : ℕ => -((m : ℤ) + 1)) ?_
    intro a b h; simpa using h

theorem summable_inv_sq_succ : Summable fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  simpa using this

/-- Uniform summable majorant of the paired terms on `‖z‖ ≤ R`. -/
theorem exists_pairBound {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (R : ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ m : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ‖pairTerm σ z m‖ ≤ u m := by
  obtain ⟨hs1, hs2⟩ := summable_dev_sq hσ
  refine ⟨fun m => (1 / Real.pi) * (‖prodDev σ ((m : ℤ) + 1)‖ ^ 2 + ‖prodDev σ (-((m : ℤ) + 1))‖ ^ 2
      + 1 / ((m : ℝ) + 1) ^ 2) + (‖prodDev σ ((m : ℤ) + 1)‖ ^ 2 + ‖prodDev σ (-((m : ℤ) + 1))‖ ^ 2)
        / Real.pi ^ 2 + 2 * |R| ^ 2 / (Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2), ?_, ?_⟩
  · refine Summable.add (Summable.add ?_ ?_) ?_
    · exact ((hs1.add hs2).add summable_inv_sq_succ).mul_left _
    · exact (hs1.add hs2).div_const _
    · have := summable_inv_sq_succ.mul_left (2 * |R| ^ 2 / Real.pi ^ 2)
      refine this.congr fun m => ?_
      field_simp
  · intro m z hz
    have hz' : ‖z‖ ≤ |R| := hz.trans (le_abs_self R)
    refine (norm_pairTerm_le σ hz' m).trans ?_
    exact real_pair_bound _ _ _ _
      (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)

/-! ### Multipliability and the value of the product -/

theorem summable_norm_pairTerm {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (z : ℂ) :
    Summable fun m : ℕ => ‖pairTerm σ z m‖ := by
  obtain ⟨u, hu, hb⟩ := exists_pairBound hσ ‖z‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => hb m z le_rfl

theorem multipliable_prodFactor {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (z : ℂ) :
    Multipliable (prodFactor σ z) (symmetricIcc ℤ) :=
  multipliable_symm_pair (summable_norm_pairTerm hσ z)

theorem tprod_prodFactor {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (z : ℂ) :
    ∏'[symmetricIcc ℤ] m, prodFactor σ z m
      = prodFactor σ z 0 * ∏' m : ℕ, (1 + pairTerm σ z m) := by
  rw [tprod_symm_pair (summable_norm_pairTerm hσ z)]
  congr 2
  funext m
  simp [pairTerm]

theorem multipliable_one_add_pairTerm {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2)
    (z : ℂ) : Multipliable fun m : ℕ => 1 + pairTerm σ z m :=
  multipliable_one_add_of_summable (summable_norm_pairTerm hσ z)

/-! ### Differentiability -/

theorem differentiableOn_tprod_one_add {b : ℕ → ℂ → ℂ} (hb : ∀ m, Differentiable ℂ (b m))
    {R : ℝ} {u : ℕ → ℝ} (hu : Summable u) (hbd : ∀ m z, ‖z‖ ≤ R → ‖b m z‖ ≤ u m) :
    DifferentiableOn ℂ (fun z => ∏' m, (1 + b m z)) (Metric.ball 0 R) := by
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add (f := b) (K := Metric.ball (0 : ℂ) R)
    Metric.isOpen_ball hu
    (Filter.Eventually.of_forall fun m z hz => hbd m z (mem_ball_zero_iff.mp hz).le)
    (fun m => (hb m).continuous.continuousOn)
  refine TendstoLocallyUniformlyOn.differentiableOn h (Filter.Eventually.of_forall fun s => ?_)
    Metric.isOpen_ball
  exact DifferentiableOn.fun_finsetProd fun i _ => ((hb i).const_add 1).differentiableOn

theorem differentiable_pairTerm (σ : ℤ → ℂ) (m : ℕ) : Differentiable ℂ fun z => pairTerm σ z m := by
  unfold pairTerm prodFactor
  fun_prop

theorem differentiable_prodFactor (σ : ℤ → ℂ) (n : ℤ) : Differentiable ℂ fun z => prodFactor σ z n := by
  unfold prodFactor
  fun_prop

theorem differentiable_tail {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (M : ℕ) :
    Differentiable ℂ fun z => ∏' m : ℕ, (1 + pairTerm σ z (m + M)) := by
  intro z
  obtain ⟨u, hu, hb⟩ := exists_pairBound hσ (‖z‖ + 1)
  have hd := differentiableOn_tprod_one_add (b := fun m z => pairTerm σ z (m + M))
    (fun m => differentiable_pairTerm σ _) ((summable_nat_add_iff M).mpr hu)
    (fun m w hw => hb _ w hw)
  refine (hd.differentiableAt (Metric.isOpen_ball.mem_nhds ?_))
  simp

theorem differentiable_entProd {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) :
    Differentiable ℂ fun z => ∏'[symmetricIcc ℤ] m, prodFactor σ z m := by
  have h := differentiable_tail hσ 0
  have e : (fun z => ∏'[symmetricIcc ℤ] m, prodFactor σ z m)
      = fun z => prodFactor σ z 0 * ∏' m : ℕ, (1 + pairTerm σ z (m + 0)) := by
    funext z
    rw [tprod_prodFactor hσ]
    simp
  rw [e]
  exact (differentiable_prodFactor σ 0).mul h

end

end NlsGge.GK38.Lib
