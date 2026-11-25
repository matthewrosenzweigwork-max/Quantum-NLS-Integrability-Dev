import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA5Diff2
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA4Cauchy

/-! # Track A, step A5 (generic, part 2): the iterated derivative at a stronger-space center
maps the stronger space into itself, with an explicit bound

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

Setting: base exponent `r`, `0 < σ < 1`, inclusion `ι : h^{r+σ} → h^r`, a real-analytic map
`g : h^r → h^r` commuting with every rotation `S_θ`, and a center `v0 ∈ h^{r+σ}`.  Given
Cauchy-type bounds `‖D^k g(ι v0 + y)‖ ≤ C k! ρ^{-k}` (`‖y‖ ≤ ρ`) and `δ ∈ (0, π]` with
`‖S_θ ι v0 - ι v0‖ ≤ ρ` for `θ ∈ (0, δ]`, the vector `y = D^k g(ι v0)[ι h_1, …, ι h_k]`
satisfies

  `diffSemi r σ y ≤ (∏‖h_i‖)² · Q_k`,
  `Q_k = (k+1) κ (L_k² ‖v0‖² + k ‖A_k‖²) + 4 ‖A_k‖² δ^{-2σ}/(2σ)`,

with `A_k = D^k g(ι v0)`, `L_k = C (k+1)! ρ^{-(k+1)}`, `κ = kernelUp σ`.  Mechanism (Pro report
"Local complex bounds", real form): for small angles
`S_θ y - y = (D^k g(S_θ ι v0) - D^k g(ι v0))[S_θ ι h] + (A_k[S_θ ι h] - A_k[ι h])`
by the differentiated equivariance; the first term by the mean-value bound for `D^k g`, the
second by multilinearity; large angles by the isometry bound only. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ENNReal Nat

namespace NlsGge.ALLS.TransA

/-- The carriers are complete (same instance as `NlsGge.Birkhoff.carrierCompleteSpace38`). -/
local instance carrierCompleteSpaceA5 (r : ℝ) : CompleteSpace (SobolevCarrier38 r) :=
  inferInstanceAs (CompleteSpace (SobolevHilbert r))

/-- Product of the norms of all entries except the `i`-th. -/
def prodExcept {k : ℕ} {X : Type*} [Norm X] (h : Fin k → X) (i : Fin k) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, ‖h j‖

theorem prodExcept_nonneg {k : ℕ} {X : Type*} [SeminormedAddCommGroup X] (h : Fin k → X)
    (i : Fin k) : 0 ≤ prodExcept h i :=
  Finset.prod_nonneg fun j _ => norm_nonneg _

theorem norm_mul_prodExcept {k : ℕ} {X : Type*} [Norm X] (h : Fin k → X) (i : Fin k) :
    ‖h i‖ * prodExcept h i = ∏ j, ‖h j‖ :=
  Finset.mul_prod_erase Finset.univ (fun j => ‖h j‖) (Finset.mem_univ i)

/-- The product in the precise multilinear difference bound, specialized to rotations. -/
theorem prod_ite_rot_le {r s : ℝ} (hrs : r ≤ s) {k : ℕ} (θ : ℝ) (h : Fin k → SobolevCarrier38 s)
    (i : Fin k) :
    (∏ j, if j = i then ‖rotC38 r θ (carrierIncl38 hrs (h i)) - carrierIncl38 hrs (h i)‖
      else max ‖rotC38 r θ (carrierIncl38 hrs (h j))‖ ‖carrierIncl38 hrs (h j)‖) ≤
      ‖rotC38 r θ (carrierIncl38 hrs (h i)) - carrierIncl38 hrs (h i)‖ * prodExcept h i := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), ite_eq_left_iff.2 (fun h => (h rfl).elim)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine Finset.prod_le_prod₀ (fun j _ => ?_) (fun j hj => ?_)
  · split_ifs <;> positivity
  · rw [if_neg (Finset.ne_of_mem_erase hj), norm_rotC38, max_self]
    exact norm_carrierIncl38_le hrs _

/-- Pointwise small-angle domination of the rotation difference of `y = A_k[ι h]`. -/
theorem rot_sub_coeff_le {r σ : ℝ} (hrs : r ≤ r + σ)
    {g : SobolevCarrier38 r → SobolevCarrier38 r} (han : AnalyticOnNhd ℝ g Set.univ)
    (hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 r), g (rotC38 r θ x) = rotC38 r θ (g x))
    (v0 : SobolevCarrier38 (r + σ)) {C ρ : ℝ}
    (hb : ∀ (k : ℕ) (y : SobolevCarrier38 r), ‖y‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0 + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k)
    {θ : ℝ} (hθ : ‖rotC38 r θ (carrierIncl38 hrs v0) - carrierIncl38 hrs v0‖ ≤ ρ) (hρ : 0 ≤ ρ)
    (k : ℕ) (h : Fin k → SobolevCarrier38 (r + σ)) :
    ‖rotC38 r θ (iteratedFDeriv ℝ k g (carrierIncl38 hrs v0) (fun i => carrierIncl38 hrs (h i))) -
        iteratedFDeriv ℝ k g (carrierIncl38 hrs v0) (fun i => carrierIncl38 hrs (h i))‖ ≤
      C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * (∏ i, ‖h i‖) *
          ‖rotC38 r θ (carrierIncl38 hrs v0) - carrierIncl38 hrs v0‖ +
        ∑ i, ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0)‖ * prodExcept h i *
          ‖rotC38 r θ (carrierIncl38 hrs (h i)) - carrierIncl38 hrs (h i)‖ := by
  set x0 := carrierIncl38 hrs v0 with hx0
  set A := iteratedFDeriv ℝ k g x0 with hA
  set A' := iteratedFDeriv ℝ k g (rotC38 r θ x0) with hA'
  set m : Fin k → SobolevCarrier38 r := fun i => carrierIncl38 hrs (h i) with hm
  set m' : Fin k → SobolevCarrier38 r := fun i => rotC38 r θ (m i) with hm'
  have heq : rotC38 r θ (A m) = A' m' := (iteratedFDeriv_rot han hcomm θ k x0 m).symm
  have hsplit : rotC38 r θ (A m) - A m = (A' - A) m' + (A m' - A m) := by
    rw [heq, ContinuousMultilinearMap.sub_apply]; abel
  have hprod : ∏ i, ‖m' i‖ ≤ ∏ i, ‖h i‖ := by
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
    rw [hm', norm_rotC38]
    exact norm_carrierIncl38_le hrs _
  have hlip : ‖A' - A‖ ≤ C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * ‖rotC38 r θ x0 - x0‖ := by
    have := iteratedFDeriv_lipschitz_on_ball han hb k (y := rotC38 r θ x0 - x0) (y' := 0) hθ
      (by simpa using hρ)
    simpa [add_sub_cancel] using this
  have hL : 0 ≤ C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * ‖rotC38 r θ x0 - x0‖ :=
    (norm_nonneg _).trans hlip
  have h1 : ‖(A' - A) m'‖ ≤ C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * (∏ i, ‖h i‖) *
      ‖rotC38 r θ x0 - x0‖ := by
    calc ‖(A' - A) m'‖ ≤ ‖A' - A‖ * ∏ i, ‖m' i‖ := (A' - A).le_opNorm m'
      _ ≤ (C * (k + 1)! * (ρ⁻¹) ^ (k + 1) * ‖rotC38 r θ x0 - x0‖) * ∏ i, ‖h i‖ :=
          mul_le_mul hlip hprod (Finset.prod_nonneg fun i _ => norm_nonneg _) hL
      _ = _ := by ring
  have h2 : ‖A m' - A m‖ ≤ ∑ i, ‖A‖ * prodExcept h i * ‖rotC38 r θ (m i) - m i‖ := by
    refine (A.norm_image_sub_le' m' m).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := prod_ite_rot_le hrs θ h i
    calc ‖A‖ * ∏ j, (if j = i then ‖m' i - m i‖ else max ‖m' j‖ ‖m j‖)
        ≤ ‖A‖ * (‖rotC38 r θ (m i) - m i‖ * prodExcept h i) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- `(a + Σ_i b_i)² ≤ (k+1) (a² + Σ_i b_i²)`. -/
theorem sq_add_sum_le {k : ℕ} (a : ℝ) (b : Fin k → ℝ) :
    (a + ∑ i, b i) ^ 2 ≤ (k + 1) * (a ^ 2 + ∑ i, b i ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Option (Fin k))))
    (f := fun o => Option.elim o a b)
  simp only [Fintype.sum_option, Option.elim, Finset.card_univ, Fintype.card_option,
    Fintype.card_fin] at h
  push_cast at h
  exact h

/-- **Coefficient seminorm estimate.** -/
theorem diffSemi_coeff_le {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hrs : r ≤ r + σ)
    {g : SobolevCarrier38 r → SobolevCarrier38 r} (han : AnalyticOnNhd ℝ g Set.univ)
    (hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 r), g (rotC38 r θ x) = rotC38 r θ (g x))
    (v0 : SobolevCarrier38 (r + σ)) {C ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hb : ∀ (k : ℕ) (y : SobolevCarrier38 r), ‖y‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0 + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k)
    (hδ : ∀ θ ∈ Ioc 0 δ, ‖rotC38 r θ (carrierIncl38 hrs v0) - carrierIncl38 hrs v0‖ ≤ ρ)
    (k : ℕ) (h : Fin k → SobolevCarrier38 (r + σ)) :
    diffSemi r σ (iteratedFDeriv ℝ k g (carrierIncl38 hrs v0) (fun i => carrierIncl38 hrs (h i))) ≤
      ENNReal.ofReal ((∏ i, ‖h i‖) ^ 2 *
        ((k + 1) * kernelUp σ * ((C * (k + 1)! * (ρ⁻¹) ^ (k + 1)) ^ 2 * ‖v0‖ ^ 2 +
            k * ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0)‖ ^ 2) +
          4 * ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0)‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ)))) := by
  set x0 := carrierIncl38 hrs v0 with hx0
  set A := iteratedFDeriv ℝ k g x0 with hA
  set L := C * (k + 1)! * (ρ⁻¹) ^ (k + 1) with hLdef
  set P := ∏ i, ‖h i‖ with hP
  set y := A (fun i => carrierIncl38 hrs (h i)) with hy
  set κ := kernelUp σ with hκ
  have hκ0 : 0 < κ := kernelUp_pos hσ0 hσ1
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
  -- weights of the domination
  let c : Option (Fin k) → ℝ := fun o => Option.elim o ((k + 1) * L ^ 2 * P ^ 2)
    (fun i => (k + 1) * ‖A‖ ^ 2 * prodExcept h i ^ 2)
  let u : Option (Fin k) → SobolevCarrier38 r := fun o => Option.elim o x0
    (fun i => carrierIncl38 hrs (h i))
  have hc : ∀ o, 0 ≤ c o := by
    intro o; cases o <;> simp only [c, Option.elim] <;> positivity
  have hsmall : ∀ θ ∈ Ioc 0 δ, ‖rotC38 r θ y - y‖ ^ 2 ≤
      ∑ o ∈ Finset.univ, c o * ‖rotC38 r θ (u o) - u o‖ ^ 2 := by
    intro θ hθ
    have hpt := rot_sub_coeff_le hrs han hcomm v0 hb (hδ θ hθ) hρ k h
    simp only [← hx0, ← hA, ← hLdef, ← hP] at hpt
    have h0 : 0 ≤ ‖rotC38 r θ y - y‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ h0 hpt 2
    refine hsq.trans ((sq_add_sum_le _ _).trans (le_of_eq ?_))
    simp only [Fintype.sum_option, c, u, Option.elim]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
  have hD := diffSemi_le_of_small hσ0 hδ0 hδπ y Finset.univ c hc u hsmall
  have hu : ∀ o, diffSemi r σ (u o) ≤ ENNReal.ofReal (κ * (Option.elim o ‖v0‖ (fun i => ‖h i‖)) ^ 2) := by
    intro o; cases o with
    | none => exact diffSemi_incl_le hσ0 hσ1 v0
    | some i => exact diffSemi_incl_le hσ0 hσ1 (h i)
  have hyA : ‖y‖ ≤ ‖A‖ * P := A.le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_carrierIncl38_le hrs _))
    (norm_nonneg _))
  have hsum : ∑ o ∈ Finset.univ, ENNReal.ofReal (c o) * diffSemi r σ (u o) ≤
      ENNReal.ofReal (∑ o ∈ Finset.univ, c o * (κ * (Option.elim o ‖v0‖ (fun i => ‖h i‖)) ^ 2)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => by
      have := hc o; positivity)]
    refine Finset.sum_le_sum fun o _ => ?_
    rw [ENNReal.ofReal_mul (hc o)]
    gcongr
    exact hu o
  have hval : ∑ o ∈ Finset.univ, c o * (κ * (Option.elim o ‖v0‖ (fun i => ‖h i‖)) ^ 2) =
      P ^ 2 * ((k + 1) * κ * (L ^ 2 * ‖v0‖ ^ 2 + k * ‖A‖ ^ 2)) := by
    simp only [Fintype.sum_option, c, Option.elim]
    have hi : ∀ i : Fin k, (k + 1) * ‖A‖ ^ 2 * prodExcept h i ^ 2 * (κ * ‖h i‖ ^ 2) =
        (k + 1) * κ * ‖A‖ ^ 2 * P ^ 2 := by
      intro i
      rw [hP, ← norm_mul_prodExcept h i]; ring
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hlast : 4 * ‖y‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ)) ≤
      4 * ‖A‖ ^ 2 * P ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ)) := by
    have hD0 : 0 ≤ δ ^ (-(2 * σ)) / (2 * σ) := by
      have := Real.rpow_nonneg hδ0.le (-(2 * σ)); positivity
    have : ‖y‖ ^ 2 ≤ (‖A‖ * P) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyA 2
    nlinarith
  calc diffSemi r σ y
      ≤ ∑ o ∈ Finset.univ, ENNReal.ofReal (c o) * diffSemi r σ (u o) +
          ENNReal.ofReal (4 * ‖y‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))) := hD
    _ ≤ ENNReal.ofReal (P ^ 2 * ((k + 1) * κ * (L ^ 2 * ‖v0‖ ^ 2 + k * ‖A‖ ^ 2))) +
          ENNReal.ofReal (4 * ‖A‖ ^ 2 * P ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))) := by
        rw [← hval]; exact add_le_add hsum (ENNReal.ofReal_le_ofReal hlast)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by
          have := Real.rpow_nonneg hδ0.le (-(2 * σ)); positivity)]
        congr 1; ring

end NlsGge.ALLS.TransA
