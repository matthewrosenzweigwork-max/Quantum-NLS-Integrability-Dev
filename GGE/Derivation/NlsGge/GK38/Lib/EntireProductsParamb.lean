import NlsGge.GK38.Lib.EntireProductsParama
import NlsGge.GK38.Lib.WeaklyAnalytic

/-!
# L4c, part 1b: uniform estimates for the paired terms on `ℓ²`-balls

Book Lemma C.1 (proof) needs the paired terms `b_m = a_m + a_{-m} + a_m a_{-m}` of
`∏ (σ_m - λ)/π_m` to be controlled by a summable majorant *locally uniformly in `σ̃ ∈ ℓ²`*.
A single pointwise majorant independent of `σ̃` does not exist on an `ℓ²`-ball (take `σ̃ = R e_m`),
but the total mass is uniformly bounded, which is what local boundedness needs; along a line
`σ̃ + ζ h̃` there is a pointwise summable majorant (`2|σ̃_n|² + 2|h̃_n|²`), which is what the
one-variable Weierstrass theorem needs.  Both come from the same pointwise estimate:

`pairTerm_le_maj`: if `‖σ_n - nπ‖² ≤ d_n` and `‖z‖ ≤ R` then
`‖pairTerm σ z m‖ ≤ c₁ (d_{m+1} + d_{-(m+1)}) + c₂ / (m+1)²`, `c₁ = 1/π + 1/π²`, `c₂ = 1/π + 2R²/π²`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The constants `c₁ = 1/π + 1/π²`. -/
def majC1 : ℝ := 1 / Real.pi + 1 / Real.pi ^ 2

/-- The constant `c₂(R) = 1/π + 2R²/π²`. -/
def majC2 (R : ℝ) : ℝ := 1 / Real.pi + 2 * R ^ 2 / Real.pi ^ 2

theorem majC1_nonneg : 0 ≤ majC1 := by unfold majC1; positivity

theorem majC2_nonneg (R : ℝ) : 0 ≤ majC2 R := by unfold majC2; positivity

/-- The majorant of the `m`-th paired term. -/
def pairMaj (d : ℤ → ℝ) (R : ℝ) (m : ℕ) : ℝ :=
  majC1 * (d ((m : ℤ) + 1) + d (-((m : ℤ) + 1))) + majC2 R * (1 / ((m : ℝ) + 1) ^ 2)

theorem pairTerm_le_maj {σ : ℤ → ℂ} {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) {d : ℤ → ℝ}
    (hd : ∀ n, ‖prodDev σ n‖ ^ 2 ≤ d n) (m : ℕ) : ‖pairTerm σ z m‖ ≤ pairMaj d R m := by
  refine (norm_pairTerm_le σ hz m).trans ?_
  have hk : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  refine (real_pair_bound _ _ R _ hk).trans ?_
  have h1 := hd ((m : ℤ) + 1)
  have h2 := hd (-((m : ℤ) + 1))
  have hpi := Real.pi_pos
  unfold pairMaj majC1 majC2
  have e : (1 / Real.pi + 1 / Real.pi ^ 2) * (d ((m : ℤ) + 1) + d (-((m : ℤ) + 1)))
      + (1 / Real.pi + 2 * R ^ 2 / Real.pi ^ 2) * (1 / ((m : ℝ) + 1) ^ 2)
      = (1 / Real.pi) * (d ((m : ℤ) + 1) + d (-((m : ℤ) + 1)) + 1 / ((m : ℝ) + 1) ^ 2)
        + (d ((m : ℤ) + 1) + d (-((m : ℤ) + 1))) / Real.pi ^ 2
        + 2 * R ^ 2 / (Real.pi ^ 2 * ((m : ℝ) + 1) ^ 2) := by
    field_simp
    ring
  rw [e]
  have hsum : ‖prodDev σ ((m : ℤ) + 1)‖ ^ 2 + ‖prodDev σ (-((m : ℤ) + 1))‖ ^ 2
      ≤ d ((m : ℤ) + 1) + d (-((m : ℤ) + 1)) := add_le_add h1 h2
  have hk0 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) ^ 2 := by positivity
  gcongr

theorem summable_pairMaj {d : ℤ → ℝ} (hd : Summable d) (R : ℝ) : Summable (pairMaj d R) := by
  have h1 : Summable fun m : ℕ => d ((m : ℤ) + 1) :=
    hd.comp_injective (i := fun m : ℕ => (m : ℤ) + 1) (fun a b h => by simpa using h)
  have h2 : Summable fun m : ℕ => d (-((m : ℤ) + 1)) :=
    hd.comp_injective (i := fun m : ℕ => -((m : ℤ) + 1)) (fun a b h => by simpa using h)
  exact ((h1.add h2).mul_left _).add (summable_inv_sq_succ.mul_left _)

/-- `T = Σ_{m ≥ 0} 1/(m+1)²`. -/
def sumInvSq : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2

theorem sumInvSq_nonneg : 0 ≤ sumInvSq := tsum_nonneg fun _ => by positivity

/-- Uniform bound of the total mass of the majorant: `Σ_m pairMaj ≤ 2 c₁ D + c₂ T` with
`D = Σ d`. -/
theorem tsum_pairMaj_le {d : ℤ → ℝ} (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n) (R : ℝ) :
    ∑' m, pairMaj d R m ≤ 2 * majC1 * (∑' n, d n) + majC2 R * sumInvSq := by
  have h1 : Summable fun m : ℕ => d ((m : ℤ) + 1) :=
    hd.comp_injective (i := fun m : ℕ => (m : ℤ) + 1) (fun a b h => by simpa using h)
  have h2 : Summable fun m : ℕ => d (-((m : ℤ) + 1)) :=
    hd.comp_injective (i := fun m : ℕ => -((m : ℤ) + 1)) (fun a b h => by simpa using h)
  have e1 : ∑' m : ℕ, d ((m : ℤ) + 1) ≤ ∑' n, d n :=
    tsum_comp_le_tsum_of_inj hd hd0 (i := fun m : ℕ => (m : ℤ) + 1) (fun a b h => by simpa using h)
  have e2 : ∑' m : ℕ, d (-((m : ℤ) + 1)) ≤ ∑' n, d n :=
    tsum_comp_le_tsum_of_inj hd hd0 (i := fun m : ℕ => -((m : ℤ) + 1))
      (fun a b h => by simpa using h)
  unfold pairMaj
  rw [Summable.tsum_add (((h1.add h2).mul_left _)) (summable_inv_sq_succ.mul_left _),
    tsum_mul_left, tsum_mul_left, Summable.tsum_add h1 h2]
  have := majC1_nonneg
  have hT : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 = sumInvSq := rfl
  rw [hT]
  nlinarith [majC1_nonneg]

/-! ### `ℓ²` facts -/

theorem hasSum_sq_l2 (s : L2Seq) : HasSum (fun n : ℤ => ‖s n‖ ^ 2) (‖s‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ENNReal)) (E := fun _ : ℤ => ℂ) (by simp) s
  simpa using h

theorem norm_coord_le (s : L2Seq) (n : ℤ) : ‖s n‖ ≤ ‖s‖ :=
  lp.norm_apply_le_norm (by simp) s n

/-! ### Uniform bound on balls -/

/-- `‖∏' (1 + c)‖ ≤ exp(Σ ‖c‖)`. -/
theorem norm_tprod_one_add_le {ι : Type*} {c : ι → ℂ} (hc : Summable fun i => ‖c i‖) :
    ‖∏' i, (1 + c i)‖ ≤ Real.exp (∑' i, ‖c i‖) := by
  have h := norm_tprod_one_add_sub_one_le hc
  have h2 : ‖∏' i, (1 + c i)‖ ≤ ‖(∏' i, (1 + c i)) - 1‖ + 1 := by
    have := norm_le_norm_add_norm_sub' (∏' i, (1 + c i)) 1
    simp only [norm_one] at this
    linarith
  linarith

/-- Uniform bound of the full product on `‖z‖ ≤ R`, `‖s‖ ≤ R`. -/
theorem norm_entProd_le {R : ℝ} {z : ℂ} {s : L2Seq} (hz : ‖z‖ ≤ R) (hs : ‖s‖ ≤ R) :
    ‖∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m‖
      ≤ 2 * R * Real.exp (2 * majC1 * R ^ 2 + majC2 R * sumInvSq) := by
  have hσ := summable_dev_sigmaOf s
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  rw [tprod_prodFactor hσ, norm_mul]
  have hd : ∀ n, ‖prodDev (sigmaOf s) n‖ ^ 2 ≤ ‖s n‖ ^ 2 := fun n => by rw [dev_sigmaOf]
  have hdS : Summable fun n : ℤ => ‖s n‖ ^ 2 := (hasSum_sq_l2 s).summable
  have hsum : Summable fun m : ℕ => ‖pairTerm (sigmaOf s) z m‖ := summable_norm_pairTerm hσ z
  have hb : ∀ m, ‖pairTerm (sigmaOf s) z m‖ ≤ pairMaj (fun n => ‖s n‖ ^ 2) R m :=
    fun m => pairTerm_le_maj hz hd m
  have hK : ∑' m, ‖pairTerm (sigmaOf s) z m‖ ≤ 2 * majC1 * R ^ 2 + majC2 R * sumInvSq := by
    refine (Summable.tsum_le_tsum hb hsum (summable_pairMaj hdS R)).trans ?_
    refine (tsum_pairMaj_le hdS (fun n => by positivity) R).trans ?_
    rw [(hasSum_sq_l2 s).tsum_eq]
    have : ‖s‖ ^ 2 ≤ R ^ 2 := by gcongr
    have := majC1_nonneg
    nlinarith
  have hT : ‖∏' m : ℕ, (1 + pairTerm (sigmaOf s) z m)‖
      ≤ Real.exp (2 * majC1 * R ^ 2 + majC2 R * sumInvSq) :=
    (norm_tprod_one_add_le hsum).trans (Real.exp_le_exp.mpr hK)
  have h0 : ‖prodFactor (sigmaOf s) z 0‖ ≤ 2 * R := by
    have : prodFactor (sigmaOf s) z 0 = s 0 - z := by
      simp [prodFactor, sigmaOf, piN_zero]
    rw [this]
    calc ‖s 0 - z‖ ≤ ‖s 0‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith [norm_coord_le s 0]
  exact mul_le_mul h0 hT (norm_nonneg _) (by linarith)

end

end NlsGge.GK38.Lib
