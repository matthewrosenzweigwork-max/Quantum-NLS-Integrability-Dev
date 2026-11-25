import NlsGge.Hierarchy.RelativePartition38
import NlsGge.Spectral.ReservedEnergyCoercivity38V1

/-!
# Auxiliary pieces for `F:thm:partition` (NEW-F07): shift `W_* = W - εB`, exact energy split,
free-normalizer ratio, convergence of the shell series.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure MeasureTheory

/-- `ε = c₋/(4c₊)`. -/
def shiftEps38 (lo up : ℝ) : ℝ := lo / (4 * up)

/-- Numerators of `W_* = W - εB`: `c_j - ε c_{j+1}/(j+1)^4`. -/
def shiftedSeq38 (lo up : ℝ) (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  c j - shiftEps38 lo up * c (j + 1) / ((j : ℝ) + 1) ^ 4

theorem shiftEps38_pos {lo up : ℝ} (hl : 0 < lo) (hlu : lo ≤ up) : 0 < shiftEps38 lo up := by
  unfold shiftEps38
  have : 0 < up := hl.trans_le hlu
  positivity

theorem shiftEps38_le {lo up : ℝ} (hl : 0 < lo) (hlu : lo ≤ up) :
    shiftEps38 lo up ≤ 1 / 4 := by
  unfold shiftEps38
  have : 0 < up := hl.trans_le hlu
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem shiftEps38_mul_le {lo up : ℝ} (hl : 0 < lo) (hlu : lo ≤ up) :
    shiftEps38 lo up * up = lo / 4 := by
  unfold shiftEps38
  have : 0 < up := hl.trans_le hlu
  field_simp

/-- NEW-F07.02: the shifted numerators lie in `[3c₋/4, c₊]`. -/
theorem shiftedSeq38_admitted {lo up : ℝ} (c : BoundedCoefficients lo up) :
    AdmittedCoefficients (3 * lo / 4) up (shiftedSeq38 lo up c.val) := by
  have hl : 0 < lo := c.property.1
  have hlu : lo ≤ up := c.property.2.1
  have hε := shiftEps38_pos hl hlu
  have hεu := shiftEps38_mul_le hl hlu
  refine ⟨by linarith, by linarith, fun j => ?_⟩
  have h1 := (c.property.2.2 j).1
  have h2 := (c.property.2.2 j).2
  have h3 := (c.property.2.2 (j + 1)).1
  have h4 := (c.property.2.2 (j + 1)).2
  have hp : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 4 := one_le_pow₀ (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)])
  have hq : 0 ≤ shiftEps38 lo up * c.val (j + 1) / ((j : ℝ) + 1) ^ 4 := by
    have : 0 ≤ c.val (j + 1) := by linarith
    positivity
  have hq2 : shiftEps38 lo up * c.val (j + 1) / ((j : ℝ) + 1) ^ 4 ≤ lo / 4 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hε.le]
  unfold shiftedSeq38
  constructor <;> linarith

/-- `W_*` as an admitted coefficient sequence in the class `[3c₋/4, c₊]`. -/
def shiftedCoefficients38 {lo up : ℝ} (c : BoundedCoefficients lo up) :
    BoundedCoefficients (3 * lo / 4) up :=
  ⟨shiftedSeq38 lo up c.val, shiftedSeq38_admitted c⟩

theorem coefficient_shifted38 {lo up : ℝ} (c : BoundedCoefficients lo up) (j : ℕ) :
    NlsGge.coefficient (shiftedCoefficients38 c).val j =
      NlsGge.coefficient c.val j - shiftEps38 lo up * NlsGge.coefficient c.val (j + 1) := by
  show NlsGge.coefficient (shiftedSeq38 lo up c.val) j = _
  unfold NlsGge.coefficient shiftedSeq38
  have hf : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * (j.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((j : ℝ) + 1) ≠ 0 := by positivity
  rw [hf]
  field_simp

/-- NEW-F07.03: exact energy split `E_W = E_{W_*} + ε E_B` on every plane. -/
theorem fullEnergy38_split {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ)
    (z : FourierPlane N) :
    fullEnergy38 c N z =
      fullEnergy38 (shiftedCoefficients38 c) N z + shiftEps38 lo up * reservedEnergy38 c N z := by
  have hs := fullEnergy38_summable c N z
  have hr := reservedEnergy38_summable c N z
  have key : ∀ j, (shiftedCoefficients38 c).val j / ((j.factorial : ℝ)) ^ 4 *
        localCharge38 (planeReal N z) j =
      c.val j / ((j.factorial : ℝ)) ^ 4 * localCharge38 (planeReal N z) j -
        shiftEps38 lo up * (NlsGge.coefficient c.val (j + 1) *
          localCharge38 (planeReal N z) j) := by
    intro j
    have := coefficient_shifted38 c j
    unfold NlsGge.coefficient at this ⊢
    rw [this]; ring
  unfold fullEnergy38 reservedEnergy38
  simp_rw [key]
  rw [Summable.tsum_sub hs (hr.mul_left _), tsum_mul_left]
  ring


/-! ### Free-normalizer ratio -/

/-- `B(r) = Σ_j β_{j+1} r^{2j}`. -/
def reservedSymbol38 (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑' j : ℕ, NlsGge.coefficient c (j + 1) * r ^ (2 * j)

section Free
variable {lo up : ℝ} (c : BoundedCoefficients lo up) (r : ℝ)

theorem coefficient_nonneg_c38 (j : ℕ) : 0 ≤ NlsGge.coefficient c.val j :=
  coefficient_nonneg38 c j

theorem weightTerm_nonneg_c38 (j : ℕ) : 0 ≤ NlsGge.weightTerm c.val r j := by
  unfold NlsGge.weightTerm
  exact mul_nonneg (coefficient_nonneg_c38 c j) (by rw [pow_mul]; positivity)

theorem weightTerm_summable_c38 : Summable (NlsGge.weightTerm c.val r) :=
  NlsGge.Weights.weightTerm_summable lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) r

theorem reservedTerm_le38 (j : ℕ) :
    NlsGge.coefficient c.val (j + 1) * r ^ (2 * j) ≤
      (up / lo) * NlsGge.weightTerm c.val r j := by
  unfold NlsGge.weightTerm
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (NlsGge.Weights.coefficient_succ_le38 lo up c.val c.property.1
      (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2) j)
    (by rw [pow_mul]; positivity)

theorem reservedTerm_nonneg38 (j : ℕ) : 0 ≤ NlsGge.coefficient c.val (j + 1) * r ^ (2 * j) :=
  mul_nonneg (coefficient_nonneg_c38 c _) (by rw [pow_mul]; positivity)

theorem reservedTerm_summable38 :
    Summable fun j : ℕ => NlsGge.coefficient c.val (j + 1) * r ^ (2 * j) :=
  Summable.of_nonneg_of_le (reservedTerm_nonneg38 c r) (reservedTerm_le38 c r)
    ((weightTerm_summable_c38 c r).mul_left _)

theorem reservedSymbol38_nonneg : 0 ≤ reservedSymbol38 c.val r :=
  tsum_nonneg (reservedTerm_nonneg38 c r)

theorem reservedSymbol38_le_weight :
    reservedSymbol38 c.val r ≤ (up / lo) * NlsGge.Weights.weight c.val r := by
  unfold reservedSymbol38 NlsGge.Weights.weight
  rw [← tsum_mul_left]
  exact (reservedTerm_summable38 c r).tsum_le_tsum (reservedTerm_le38 c r)
    ((weightTerm_summable_c38 c r).mul_left _)

theorem weight_shifted38 :
    NlsGge.Weights.weight (shiftedCoefficients38 c).val r =
      NlsGge.Weights.weight c.val r - shiftEps38 lo up * reservedSymbol38 c.val r := by
  unfold NlsGge.Weights.weight reservedSymbol38
  have key : ∀ j, NlsGge.weightTerm (shiftedCoefficients38 c).val r j =
      NlsGge.weightTerm c.val r j - shiftEps38 lo up *
        (NlsGge.coefficient c.val (j + 1) * r ^ (2 * j)) := by
    intro j
    unfold NlsGge.weightTerm
    rw [coefficient_shifted38]; ring
  simp_rw [key]
  rw [Summable.tsum_sub (weightTerm_summable_c38 c r) ((reservedTerm_summable38 c r).mul_left _),
    tsum_mul_left]

theorem sq_mul_reservedSymbol38 :
    r ^ 2 * reservedSymbol38 c.val r =
      NlsGge.Weights.weight c.val r - NlsGge.coefficient c.val 0 := by
  unfold reservedSymbol38 NlsGge.Weights.weight
  rw [← tsum_mul_left, (weightTerm_summable_c38 c r).tsum_eq_zero_add]
  have : ∀ j : ℕ, r ^ 2 * (NlsGge.coefficient c.val (j + 1) * r ^ (2 * j)) =
      NlsGge.weightTerm c.val r (j + 1) := by
    intro j; unfold NlsGge.weightTerm; ring
  simp_rw [this]
  simp [NlsGge.weightTerm]

theorem weight_pos_c38 : 0 < NlsGge.Weights.weight c.val r :=
  NlsGge.Weights.weight_pos lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) r

/-- The ratio `t = ε B(r)/W(r)`. -/
def modeT38 : ℝ := shiftEps38 lo up * reservedSymbol38 c.val r / NlsGge.Weights.weight c.val r

theorem modeT38_nonneg : 0 ≤ modeT38 c r :=
  div_nonneg (mul_nonneg (shiftEps38_pos c.property.1 c.property.2.1).le
    (reservedSymbol38_nonneg c r)) (weight_pos_c38 c r).le

theorem modeT38_le : modeT38 c r ≤ 1 / 4 := by
  have hl := c.property.1
  have hlu := c.property.2.1
  have hw := weight_pos_c38 c r
  unfold modeT38
  rw [div_le_iff₀ hw]
  have h1 := reservedSymbol38_le_weight c r
  have h2 := shiftEps38_mul_le hl hlu
  have h3 := shiftEps38_pos hl hlu
  have : shiftEps38 lo up * reservedSymbol38 c.val r ≤
      shiftEps38 lo up * ((up / lo) * NlsGge.Weights.weight c.val r) :=
    mul_le_mul_of_nonneg_left h1 h3.le
  have e : shiftEps38 lo up * ((up / lo) * NlsGge.Weights.weight c.val r) =
      (shiftEps38 lo up * up) / lo * NlsGge.Weights.weight c.val r := by ring
  rw [e, h2] at this
  have : lo / 4 / lo = 1 / 4 := by field_simp
  nlinarith [this, ‹shiftEps38 lo up * reservedSymbol38 c.val r ≤ _›]

theorem modeT38_le_sq (hr : r ≠ 0) : modeT38 c r ≤ shiftEps38 lo up / r ^ 2 := by
  have hl := c.property.1
  have hlu := c.property.2.1
  have hw := weight_pos_c38 c r
  have h3 := shiftEps38_pos hl hlu
  have hr2 : 0 < r ^ 2 := by positivity
  have h := sq_mul_reservedSymbol38 c r
  have hb0 : 0 ≤ NlsGge.coefficient c.val 0 := coefficient_nonneg_c38 c 0
  unfold modeT38
  rw [div_le_iff₀ hw, div_mul_eq_mul_div, le_div_iff₀ hr2]
  nlinarith [mul_le_mul_of_nonneg_left (show r ^ 2 * reservedSymbol38 c.val r ≤
      NlsGge.Weights.weight c.val r by linarith) h3.le]

theorem weight_shifted_eq38 :
    NlsGge.Weights.weight (shiftedCoefficients38 c).val r =
      (1 - modeT38 c r) * NlsGge.Weights.weight c.val r := by
  rw [weight_shifted38]
  unfold modeT38
  have := (weight_pos_c38 c r).ne'
  field_simp

/-- `a/a_* ≤ exp(2t)`. -/
theorem weight_ratio_le38 :
    NlsGge.Weights.weight c.val r / NlsGge.Weights.weight (shiftedCoefficients38 c).val r ≤
      Real.exp (2 * modeT38 c r) := by
  have ht0 := modeT38_nonneg c r
  have ht1 := modeT38_le c r
  have hw := weight_pos_c38 c r
  rw [weight_shifted_eq38]
  have h1 : (0 : ℝ) < 1 - modeT38 c r := by linarith
  rw [show NlsGge.Weights.weight c.val r / ((1 - modeT38 c r) * NlsGge.Weights.weight c.val r)
      = 1 / (1 - modeT38 c r) by field_simp]
  rw [div_le_iff₀ h1]
  have h2 : 1 + 2 * modeT38 c r ≤ Real.exp (2 * modeT38 c r) := by
    linarith [Real.add_one_le_exp (2 * modeT38 c r)]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1)]

end Free


/-- Summable majorant of the mode ratios. -/
def modeBound38 (m : ℤ) : ℝ := 1 / 4 * (1 / (m : ℝ) ^ 2 + if m = 0 then 1 else 0)

theorem modeBound38_nonneg (m : ℤ) : 0 ≤ modeBound38 m := by
  unfold modeBound38; split_ifs <;> positivity

theorem modeBound38_summable : Summable modeBound38 := by
  have h1 : Summable fun m : ℤ => 1 / (m : ℝ) ^ 2 :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  have h2 : Summable fun m : ℤ => if m = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  exact (h1.add h2).mul_left (1 / 4)

/-- The mode ratio at `r = 2πm` is bounded by `modeBound38 m`, uniformly in the class. -/
theorem modeT38_le_bound {lo up : ℝ} (c : BoundedCoefficients lo up) (m : ℤ) :
    modeT38 c (2 * Real.pi * (m : ℝ)) ≤ modeBound38 m := by
  by_cases hm : m = 0
  · subst hm
    have := modeT38_le c (2 * Real.pi * ((0 : ℤ) : ℝ))
    simpa [modeBound38] using this
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hr : 2 * Real.pi * (m : ℝ) ≠ 0 := by positivity
    have h1 := modeT38_le_sq c _ hr
    have hε := shiftEps38_le c.property.1 c.property.2.1
    have hm2 : 0 < (m : ℝ) ^ 2 := by positivity
    have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
    have h2 : shiftEps38 lo up / (2 * Real.pi * (m : ℝ)) ^ 2 ≤ 1 / 4 * (1 / (m : ℝ) ^ 2) := by
      rw [mul_pow, div_le_iff₀ (by positivity)]
      have : 1 / 4 * (1 / (m : ℝ) ^ 2) * ((2 * Real.pi) ^ 2 * (m : ℝ) ^ 2) =
          (2 * Real.pi) ^ 2 / 4 := by field_simp
      rw [this]
      nlinarith
    refine h1.trans (h2.trans ?_)
    unfold modeBound38
    simp [hm]

theorem modeIndex_injective38 (N : ℕ) : Function.Injective (modeIndex N) := by
  intro i j h
  unfold modeIndex at h
  exact Fin.ext (by omega)

/-- NEW-F07.04: bounded change of the free Gaussian normalizer. The constant is
absolute (independent of `c₋, c₊`, of `c`, and of `N`). -/
theorem freeNormalizer_shifted_le38 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (lo up : ℝ) (c : BoundedCoefficients lo up) (N : ℕ),
      freeNormalizer38 (shiftedCoefficients38 c) N ≤ C₀ * freeNormalizer38 c N := by
  refine ⟨Real.exp (2 * ∑' m : ℤ, modeBound38 m), Real.exp_pos _, fun lo up c N => ?_⟩
  unfold freeNormalizer38
  have hpt : ∀ i : Fin (2 * N + 1),
      Real.pi / fullWeightRate (shiftedCoefficients38 c).val (modeIndex N i) ≤
        Real.pi / fullWeightRate c.val (modeIndex N i) *
          Real.exp (2 * modeT38 c (2 * Real.pi * ((modeIndex N i : ℤ) : ℝ))) := by
    intro i
    have hrat := weight_ratio_le38 c (2 * Real.pi * ((modeIndex N i : ℤ) : ℝ))
    have hs := fullWeightRate_pos38 (shiftedCoefficients38 c) (modeIndex N i)
    have ha := fullWeightRate_pos38 c (modeIndex N i)
    unfold fullWeightRate at hs ha ⊢
    have aux : ∀ p a b : ℝ, a ≠ 0 → b ≠ 0 → p / b = p / a * (a / b) := by
      intro p a b ha hb; field_simp
    rw [aux Real.pi _ _ ha.ne' hs.ne']
    exact mul_le_mul_of_nonneg_left hrat (by positivity)
  calc ∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate (shiftedCoefficients38 c).val (modeIndex N i)
      ≤ ∏ i : Fin (2 * N + 1), (Real.pi / fullWeightRate c.val (modeIndex N i) *
          Real.exp (2 * modeT38 c (2 * Real.pi * ((modeIndex N i : ℤ) : ℝ)))) :=
        Finset.prod_le_prod₀ (fun i _ => div_nonneg Real.pi_pos.le
          (fullWeightRate_pos38 (shiftedCoefficients38 c) _).le) (fun i _ => hpt i)
    _ = (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) *
          Real.exp (∑ i : Fin (2 * N + 1),
            2 * modeT38 c (2 * Real.pi * ((modeIndex N i : ℤ) : ℝ))) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i)) *
          Real.exp (2 * ∑' m : ℤ, modeBound38 m) := by
        gcongr
        · exact Finset.prod_nonneg fun i _ => div_nonneg Real.pi_pos.le
            (fullWeightRate_pos38 _ _).le
        rw [← Finset.mul_sum]
        gcongr
        calc ∑ i : Fin (2 * N + 1), modeT38 c (2 * Real.pi * ((modeIndex N i : ℤ) : ℝ))
            ≤ ∑ i : Fin (2 * N + 1), modeBound38 (modeIndex N i) :=
              Finset.sum_le_sum fun i _ => modeT38_le_bound c _
          _ = ∑ m ∈ (Finset.univ : Finset (Fin (2 * N + 1))).image (modeIndex N), modeBound38 m := by
              rw [Finset.sum_image (fun i _ j _ h => modeIndex_injective38 N h)]
          _ ≤ ∑' m : ℤ, modeBound38 m :=
              modeBound38_summable.sum_le_tsum _ (fun m _ => modeBound38_nonneg m)
    _ = Real.exp (2 * ∑' m : ℤ, modeBound38 m) *
          ∏ i : Fin (2 * N + 1), Real.pi / fullWeightRate c.val (modeIndex N i) := by ring


/-! ### Convergence of the shell series -/

/-- `ℓ(k) = 0` for `k < R₀`, `ℓ(k) = g exp(g k^{1/4})` otherwise. -/
def shellLevel38 (g R₀ : ℝ) (k : ℕ) : ℝ :=
  if R₀ ≤ (k : ℝ) then g * Real.exp (g * (k : ℝ) ^ (1 / 4 : ℝ)) else 0

theorem shellLevel38_nonneg {g : ℝ} (R₀ : ℝ) (hg : 0 < g) (k : ℕ) : 0 ≤ shellLevel38 g R₀ k := by
  unfold shellLevel38; split_ifs <;> positivity

/-- NEW-F07.07/.08: `Σ_k exp[C(k+2)⁹ - ε ℓ(k)]` converges. -/
theorem shellSeries_summable38 {C g ε : ℝ} (R₀ : ℝ) (hC : 0 ≤ C) (hg : 0 < g) (hε : 0 < ε) :
    Summable fun k : ℕ => Real.exp (C * ((k : ℝ) + 2) ^ 9 - ε * shellLevel38 g R₀ k) := by
  set κ : ℝ := ε * g ^ 41 / (Nat.factorial 40 : ℝ) with hκ
  have hκpos : 0 < κ := by positivity
  set K : ℕ := max (max 1 ⌈R₀⌉₊) ⌈(3 ^ 9 * C + 1) / κ⌉₊ with hK
  have hbound : ∀ k : ℕ, K ≤ k →
      Real.exp (C * ((k : ℝ) + 2) ^ 9 - ε * shellLevel38 g R₀ k) ≤ Real.exp (-1) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
    have hkR : R₀ ≤ (k : ℝ) := by
      have : ⌈R₀⌉₊ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
      exact (Nat.le_ceil R₀).trans (by exact_mod_cast this)
    have hkκ : (3 ^ 9 * C + 1) / κ ≤ (k : ℝ) := by
      have : ⌈(3 ^ 9 * C + 1) / κ⌉₊ ≤ k := le_trans (le_max_right _ _) hk
      exact (Nat.le_ceil _).trans (by exact_mod_cast this)
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    rw [← Real.exp_nat_mul, show (k : ℝ) * (-1) = -(k : ℝ) by ring]
    apply Real.exp_le_exp.mpr
    unfold shellLevel38
    simp only [hkR, ite_true]
    -- lower bound for the exponential
    have hy : 0 ≤ g * (k : ℝ) ^ (1 / 4 : ℝ) := by positivity
    have hexp := Real.pow_div_factorial_le_exp (g * (k : ℝ) ^ (1 / 4 : ℝ)) hy 40
    have hy40 : (g * (k : ℝ) ^ (1 / 4 : ℝ)) ^ 40 = g ^ 40 * (k : ℝ) ^ 10 := by
      rw [mul_pow, ← Real.rpow_natCast ((k : ℝ) ^ (1 / 4 : ℝ)) 40, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hy40] at hexp
    have hlow : κ * (k : ℝ) ^ 10 ≤ ε * (g * Real.exp (g * (k : ℝ) ^ (1 / 4 : ℝ))) := by
      have h1 : g * (g ^ 40 * (k : ℝ) ^ 10 / (Nat.factorial 40 : ℝ)) ≤
          g * Real.exp (g * (k : ℝ) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hexp hg.le
      have h2 := mul_le_mul_of_nonneg_left h1 hε.le
      calc κ * (k : ℝ) ^ 10 = ε * (g * (g ^ 40 * (k : ℝ) ^ 10 / (Nat.factorial 40 : ℝ))) := by
            rw [hκ]; ring
        _ ≤ _ := h2
    have hpoly : C * ((k : ℝ) + 2) ^ 9 + k ≤ κ * (k : ℝ) ^ 10 := by
      have h3 : ((k : ℝ) + 2) ^ 9 ≤ 3 ^ 9 * (k : ℝ) ^ 9 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) 9
      have h4 : (k : ℝ) ≤ (k : ℝ) ^ 9 := by
        calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (k : ℝ) ^ 9 := pow_le_pow_right₀ hk1' (by norm_num)
      have h5 : (3 ^ 9 * C + 1) * (k : ℝ) ^ 9 ≤ κ * (k : ℝ) ^ 10 := by
        have := (div_le_iff₀ hκpos).mp hkκ
        calc (3 ^ 9 * C + 1) * (k : ℝ) ^ 9 ≤ ((k : ℝ) * κ) * (k : ℝ) ^ 9 :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ = κ * (k : ℝ) ^ 10 := by ring
      nlinarith [mul_le_mul_of_nonneg_left h3 hC]
    linarith
  have hgeo : Summable fun k : ℕ => Real.exp (-1) ^ k :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by norm_num))
  rw [← summable_nat_add_iff K]
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun k => ?_)
    ((summable_nat_add_iff K).mpr hgeo)
  exact hbound (k + K) (by omega)

end NlsGge.HierarchyRiccati.Core

end
