import NlsGge.Spectral.RTreeBorn38
import NlsGge.Spectral.R3cUniformRiccati38
import NlsGge.Spectral.R3cResolventL2_38
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # RTree piece T8: Born truncation at degree `2L+1`

For `U = planeReal N z` with `‖U‖_∞ ≤ A`, `η ≥ max (4A) 1` and a continuous periodic solution `Γ` of the
Riccati equation with `‖Γ - R Ū‖_∞ ≤ A³/(4η³)` (as produced by `riccati_exists_uniform38`), the
remainder after the Born terms `G₁ + ... + G_{2L+1}` (= `Σ_{ℓ ≤ L} bornG38 η N z ℓ`) is bounded by
`C(L,A) η^{-(2L+3)}` in sup norm. The proof is the induction of the design review (item 3):
`‖G_{2ℓ+1}‖ ≤ Cat_ℓ r^{2ℓ+1}` with `r = A/(2η) ≤ 1/8` (T7),
`Δ_L = -R(U[(Γ-S_{L-1})(Γ+S_{L-1}) + Σ_{a+b ≥ L} G_a G_b])` and `‖R g‖ ≤ ‖g‖/(2η)`.
The threshold on `η` enters only through the uniform Riccati solution and `r ≤ 1`. -/

/-- Square of a partial sum: the antidiagonal Cauchy part plus the far-corner part. -/
theorem sq_diag_split38 (g : ℕ → ℂ) (L : ℕ) :
    (∑ a ∈ Finset.range (L+1), g a) ^ 2 =
      ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1), g a * g (n - a) +
        ∑ a ∈ Finset.range (L+1), g a * ∑ b ∈ Finset.Ico (L+1-a) (L+1), g b := by
  rw [Finset.sum_range_diag_flip (L+1) (fun a b => g a * g b), sq, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' : a < L + 1 := Finset.mem_range.mp ha
  have := Finset.sum_range_add_sum_Ico g (show L + 1 - a ≤ L + 1 by omega)
  rw [← this, mul_add, Finset.mul_sum]

/-- far-corner bound -/
theorem far_corner_norm_le38 (g : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (L : ℕ)
    (hg : ∀ a, ‖g a‖ ≤ (catalan a : ℝ) * r ^ (2 * a + 1)) :
    ‖∑ a ∈ Finset.range (L+1), g a * ∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖ ≤
      (∑ a ∈ Finset.range (L+1), (catalan a : ℝ)) ^ 2 * r ^ (2 * L + 4) := by
  have key : ∀ a ∈ Finset.range (L+1), ‖g a * ∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖ ≤
      (catalan a : ℝ) * (∑ b ∈ Finset.range (L+1), (catalan b : ℝ)) * r ^ (2 * L + 4) := by
    intro a ha
    have ha' : a < L + 1 := Finset.mem_range.mp ha
    rw [norm_mul]
    have h1 : ‖∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖ ≤
        ∑ b ∈ Finset.Ico (L+1-a) (L+1), (catalan b : ℝ) * r ^ (2 * b + 1) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hg b)
    have h2 : ∑ b ∈ Finset.Ico (L+1-a) (L+1), (catalan b : ℝ) * r ^ (2 * b + 1) ≤
        (∑ b ∈ Finset.range (L+1), (catalan b : ℝ)) * r ^ (2 * (L - a) + 3) := by
      rw [Finset.sum_mul]
      calc ∑ b ∈ Finset.Ico (L+1-a) (L+1), (catalan b : ℝ) * r ^ (2 * b + 1)
          ≤ ∑ b ∈ Finset.Ico (L+1-a) (L+1), (catalan b : ℝ) * r ^ (2 * (L - a) + 3) := by
            refine Finset.sum_le_sum fun b hb => ?_
            have hb' := Finset.mem_Ico.mp hb
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hr0 hr1 (by omega)) (Nat.cast_nonneg _)
        _ ≤ ∑ b ∈ Finset.range (L+1), (catalan b : ℝ) * r ^ (2 * (L - a) + 3) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
            intro b hb
            have := Finset.mem_Ico.mp hb
            exact Finset.mem_range.mpr (by omega)
    calc ‖g a‖ * ‖∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖
        ≤ ((catalan a : ℝ) * r ^ (2 * a + 1)) *
          ((∑ b ∈ Finset.range (L+1), (catalan b : ℝ)) * r ^ (2 * (L - a) + 3)) :=
          mul_le_mul (hg a) (h1.trans h2) (norm_nonneg _) (by positivity)
      _ = (catalan a : ℝ) * (∑ b ∈ Finset.range (L+1), (catalan b : ℝ)) * r ^ (2 * L + 4) := by
          have : 2 * L + 4 = (2 * a + 1) + (2 * (L - a) + 3) := by omega
          rw [this, pow_add]; ring
  calc ‖∑ a ∈ Finset.range (L+1), g a * ∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖
      ≤ ∑ a ∈ Finset.range (L+1), ‖g a * ∑ b ∈ Finset.Ico (L+1-a) (L+1), g b‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.range (L+1), (catalan a : ℝ) * (∑ b ∈ Finset.range (L+1), (catalan b : ℝ)) *
          r ^ (2 * L + 4) := Finset.sum_le_sum key
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring


/-- the Catalan partial sums `Σ_{a<n} Cat_a` -/
def catSum38 (n : ℕ) : ℝ := ∑ a ∈ Finset.range n, (catalan a : ℝ)

/-- the Born truncation constant: `‖Γ - Σ_{ℓ≤L} G_ℓ‖ ≤ bornConst38 L (A/(2η))^{2L+3}`. -/
def bornConst38 : ℕ → ℝ
  | 0 => 2
  | L+1 => bornConst38 L * (2 * catSum38 (L+1) + bornConst38 L) + catSum38 (L+1) ^ 2

theorem catSum38_nonneg (n : ℕ) : 0 ≤ catSum38 n :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem bornConst38_nonneg (L : ℕ) : 0 ≤ bornConst38 L := by
  induction L with
  | zero => simp [bornConst38]
  | succ L ih =>
    have := catSum38_nonneg (L+1)
    simp only [bornConst38]
    positivity

theorem periodic_sum38 {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, Function.Periodic (f i) 1) : Function.Periodic (fun x => ∑ i ∈ s, f i x) 1 :=
  fun x => Finset.sum_congr rfl fun i hi => h i hi x

/-- abstract Born truncation: exact identity for the remainder -/
theorem born_remainder_identity38 {η : ℝ} (hη : 0 < η) (U Γ : ℝ → ℂ) (G : ℕ → ℝ → ℂ)
    (hUc : Continuous U) (hUp : Function.Periodic U 1)
    (hGc : ∀ a, Continuous (G a)) (hGp : ∀ a, Function.Periodic (G a) 1)
    (hΓc : Continuous Γ) (hΓp : Function.Periodic Γ 1)
    (hGrec : ∀ ℓ x, G (ℓ+1) x = -resolv38 η (fun y => U y *
      ∑ a ∈ Finset.range (ℓ+1), G a y * G (ℓ - a) y) x)
    (hΔ0 : ∀ x, Γ x - G 0 x = -resolv38 η (fun y => U y * Γ y ^ 2) x) (L : ℕ) :
    ∀ x, Γ x - ∑ a ∈ Finset.range (L+1), G a x =
      -resolv38 η (fun y => U y * (Γ y ^ 2 -
        ∑ n ∈ Finset.range L, ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y)) x := by
  induction L with
  | zero => intro x; simpa using hΔ0 x
  | succ L ih =>
    intro x
    have hPc : Continuous (fun y => ∑ a ∈ Finset.range (L+1), G a y * G (L - a) y) :=
      continuous_finsetSum _ fun a _ => (hGc a).mul (hGc _)
    have hPp : Function.Periodic (fun y => ∑ a ∈ Finset.range (L+1), G a y * G (L - a) y) 1 :=
      periodic_sum38 _ _ fun a _ y => by simp only [hGp a y, hGp (L - a) y]
    have hFc : ∀ M, Continuous (fun y => Γ y ^ 2 -
        ∑ n ∈ Finset.range M, ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y) := fun M =>
      (hΓc.pow 2).sub (continuous_finsetSum _ fun n _ =>
        continuous_finsetSum _ fun a _ => (hGc a).mul (hGc _))
    have hFp : ∀ M, Function.Periodic (fun y => Γ y ^ 2 -
        ∑ n ∈ Finset.range M, ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y) 1 := fun M y => by
      beta_reduce
      rw [hΓp y]
      congr 1
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ => by
        rw [hGp a y, hGp (n - a) y]
    have hsplit : (fun y => U y * (Γ y ^ 2 -
        ∑ n ∈ Finset.range L, ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y)) =
        fun y => U y * (Γ y ^ 2 -
        ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y) +
        U y * ∑ a ∈ Finset.range (L+1), G a y * G (L - a) y := by
      funext y
      rw [Finset.sum_range_succ]
      ring
    have hadd := resolv38_add_cp38 hη (f := fun y => U y * (Γ y ^ 2 -
        ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y))
      (g := fun y => U y * ∑ a ∈ Finset.range (L+1), G a y * G (L - a) y)
      (hUc.mul (hFc (L+1))) (fun y => by simp only [hUp y, hFp (L+1) y])
      (hUc.mul hPc) (fun y => by simp only [hUp y, hPp y]) x
    rw [Finset.sum_range_succ, ← sub_sub, ih x, hGrec L x, hsplit, hadd]
    ring

/-- abstract Born truncation, sup bound with the explicit constant -/
theorem born_truncation_core38 {η A : ℝ} (U Γ : ℝ → ℂ) (G : ℕ → ℝ → ℂ)
    (hUc : Continuous U) (hUp : Function.Periodic U 1) (hA0 : 0 ≤ A) (hA : ∀ x, ‖U x‖ ≤ A)
    (hη : max (4*A) 1 ≤ η)
    (hGc : ∀ a, Continuous (G a)) (hGp : ∀ a, Function.Periodic (G a) 1)
    (hGb : ∀ a x, ‖G a x‖ ≤ (catalan a : ℝ) * (A / (2 * η)) ^ (2 * a + 1))
    (hΓc : Continuous Γ) (hΓp : Function.Periodic Γ 1)
    (hGrec : ∀ ℓ x, G (ℓ+1) x = -resolv38 η (fun y => U y *
      ∑ a ∈ Finset.range (ℓ+1), G a y * G (ℓ - a) y) x)
    (hΔ0 : ∀ x, Γ x - G 0 x = -resolv38 η (fun y => U y * Γ y ^ 2) x)
    (hΓb : ∀ x, ‖Γ x - G 0 x‖ ≤ A ^ 3 / (4 * η ^ 3)) (L : ℕ) :
    ∀ x, ‖Γ x - ∑ a ∈ Finset.range (L+1), G a x‖ ≤ bornConst38 L * (A / (2 * η)) ^ (2 * L + 3) := by
  have hη1 : 1 ≤ η := (le_max_right _ _).trans hη
  have hη4 : 4 * A ≤ η := (le_max_left _ _).trans hη
  have hηpos : 0 < η := by linarith
  set r : ℝ := A / (2 * η) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]; linarith
  have hAr : A / (2 * η) * (2 * η) = A := by field_simp
  induction L with
  | zero =>
    intro x
    have e : A ^ 3 / (4 * η ^ 3) = 2 * r ^ 3 := by rw [hr]; field_simp; ring
    simp only [bornConst38, Finset.sum_range_one, zero_add, Nat.mul_zero]
    rw [← e]
    exact hΓb x
  | succ L ih =>
    intro x
    set c : ℝ := catSum38 (L+1) with hc
    set D : ℝ := bornConst38 L with hD
    have hc0 : 0 ≤ c := catSum38_nonneg _
    have hD0 : 0 ≤ D := bornConst38_nonneg L
    have hS : ∀ y, ‖∑ a ∈ Finset.range (L+1), G a y‖ ≤ c * r := fun y => by
      refine (norm_sum_le _ _).trans ?_
      rw [hc, catSum38, Finset.sum_mul]
      refine Finset.sum_le_sum fun a _ => (hGb a y).trans ?_
      exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hr0 hr1 (by omega)) (Nat.cast_nonneg _)
    have hΔ : ∀ y, ‖Γ y - ∑ a ∈ Finset.range (L+1), G a y‖ ≤ D * r ^ (2 * L + 3) := ih
    have hΔ' : ∀ y, ‖Γ y - ∑ a ∈ Finset.range (L+1), G a y‖ ≤ D * r := fun y =>
      (hΔ y).trans (mul_le_mul_of_nonneg_left (pow_le_of_le_one hr0 hr1 (by omega)) hD0)
    have hFid : ∀ y, Γ y ^ 2 - ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1),
        G a y * G (n - a) y =
        (Γ y - ∑ a ∈ Finset.range (L+1), G a y) * (Γ y + ∑ a ∈ Finset.range (L+1), G a y) +
        ∑ a ∈ Finset.range (L+1), G a y * ∑ b ∈ Finset.Ico (L+1-a) (L+1), G b y := fun y => by
      have := sq_diag_split38 (fun a => G a y) L
      simp only at this
      linear_combination this
    have hM : ∀ y, ‖Γ y ^ 2 - ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1),
        G a y * G (n - a) y‖ ≤ (D * (2 * c + D) + c ^ 2) * r ^ (2 * L + 4) := fun y => by
      rw [hFid y]
      have hsum : ‖Γ y + ∑ a ∈ Finset.range (L+1), G a y‖ ≤ (2 * c + D) * r := by
        have e : Γ y + ∑ a ∈ Finset.range (L+1), G a y =
            (Γ y - ∑ a ∈ Finset.range (L+1), G a y) + 2 * ∑ a ∈ Finset.range (L+1), G a y := by
          ring
        rw [e]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul]
        have h2 : ‖(2:ℂ)‖ = 2 := by simp
        rw [h2]
        have := hΔ' y
        have := hS y
        nlinarith
      have hQ := far_corner_norm_le38 (fun a => G a y) r hr0 hr1 L (fun a => hGb a y)
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have h1 : ‖Γ y - ∑ a ∈ Finset.range (L+1), G a y‖ *
          ‖Γ y + ∑ a ∈ Finset.range (L+1), G a y‖ ≤
          (D * r ^ (2 * L + 3)) * ((2 * c + D) * r) :=
        mul_le_mul (hΔ y) hsum (norm_nonneg _) (by positivity)
      have e1 : (D * r ^ (2 * L + 3)) * ((2 * c + D) * r) = D * (2 * c + D) * r ^ (2 * L + 4) := by
        ring
      have e2 : (∑ a ∈ Finset.range (L+1), (catalan a : ℝ)) ^ 2 = c ^ 2 := rfl
      rw [e2] at hQ
      nlinarith
    rw [born_remainder_identity38 hηpos U Γ G hUc hUp hGc hGp hΓc hΓp hGrec hΔ0 (L+1) x, norm_neg]
    have hFc : Continuous (fun y => U y * (Γ y ^ 2 -
        ∑ n ∈ Finset.range (L+1), ∑ a ∈ Finset.range (n+1), G a y * G (n - a) y)) :=
      hUc.mul ((hΓc.pow 2).sub (continuous_finsetSum _ fun n _ =>
        continuous_finsetSum _ fun a _ => (hGc a).mul (hGc _)))
    have hb := resolv38_bound hηpos hFc (B := A * ((D * (2 * c + D) + c ^ 2) * r ^ (2 * L + 4)))
      (fun y => by
        rw [norm_mul]
        exact mul_le_mul (hA y) (hM y) (norm_nonneg _) hA0) x
    refine hb.trans (le_of_eq ?_)
    simp only [bornConst38]
    rw [← hD, ← hc]
    have : 2 * (L + 1) + 3 = (2 * L + 4) + 1 := by ring
    rw [this, pow_succ, hr]
    ring

theorem leafU38_zero_eq (N : ℕ) (z : FourierPlane N) : leafU38 N z 0 = planeReal N z := rfl

/-- T8: Born truncation, general `L` (generalizes `born_core_r3c`). `G₁ + ... + G_{2L+1}` is
`Σ_{ℓ ∈ range (L+1)} bornG38 η N z ℓ`; the constant depends on `(L, A)` only. -/
theorem born_truncation38 (L : ℕ) (A : ℝ) (hA0 : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : ℝ} (N : ℕ) (z : FourierPlane N) (Γ : ℝ → ℂ),
      (∀ x, ‖planeReal N z x‖ ≤ A) → max (4 * A) 1 ≤ η →
      Continuous Γ → Function.Periodic Γ 1 →
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (planeReal N z x) -
        planeReal N z x * Γ x ^ 2) x) →
      (∀ x, ‖Γ x - resolv38 η (fun y => star (planeReal N z y)) x‖ ≤ A ^ 3 / (4 * η ^ 3)) →
      ∀ x, ‖Γ x - ∑ ℓ ∈ Finset.range (L+1), bornG38 η N z ℓ x‖ ≤ C / η ^ (2 * L + 3) := by
  refine ⟨bornConst38 L * (A / 2) ^ (2 * L + 3),
    mul_nonneg (bornConst38_nonneg L) (pow_nonneg (by positivity) _), ?_⟩
  intro η N z Γ hA hη hΓc hΓp hΓd hΓb x
  have hηpos : 0 < η := by
    have := (le_max_right (4 * A) 1).trans hη
    linarith
  have hU := perC1_leafU38 N z 0
  have hUc : Continuous (planeReal N z) := hU.cont
  have hUp : Function.Periodic (planeReal N z) 1 := hU.per
  have hrem := (born_remainder38 (planeReal N z) Γ hUc hUp hA0 hA hη hΓc hΓp hΓd hΓb).1
  have h := born_truncation_core38 (planeReal N z) Γ (fun ℓ => bornG38 η N z ℓ) hUc hUp hA0 hA hη
    (fun a => (bornG38_cont_per hηpos N z a).1) (fun a => (bornG38_cont_per hηpos N z a).2)
    (fun a y => bornG38_norm_le hηpos N z hA a y) hΓc hΓp
    (fun ℓ y => by
      have := congrFun (bornG38_rec hηpos N z ℓ) y
      simpa [leafU38_zero_eq] using this)
    (fun y => by
      have := hrem y
      rw [bornG38_zero]
      exact this)
    (fun y => by
      rw [bornG38_zero]
      exact hΓb y) L x
  refine h.trans (le_of_eq ?_)
  have e : A / (2 * η) = (A / 2) / η := by field_simp
  rw [e, div_pow, mul_div_assoc]



/-- Pairing with `U` of the Born remainder: `|⟪U, Γ - Σ_{ℓ ≤ L} G_ℓ⟫| ≤ A · C / η^{2L+3}`. -/
theorem pair_born_truncation38 (L : ℕ) (A : ℝ) (hA0 : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {η : ℝ} (N : ℕ) (z : FourierPlane N) (Γ : ℝ → ℂ),
      (∀ x, ‖planeReal N z x‖ ≤ A) → max (4 * A) 1 ≤ η →
      Continuous Γ → Function.Periodic Γ 1 →
      (∀ x, HasDerivAt Γ (-(2 * η) * Γ x + star (planeReal N z x) -
        planeReal N z x * Γ x ^ 2) x) →
      (∀ x, ‖Γ x - resolv38 η (fun y => star (planeReal N z y)) x‖ ≤ A ^ 3 / (4 * η ^ 3)) →
      ‖pair38 (planeReal N z)
        (fun x => Γ x - ∑ ℓ ∈ Finset.range (L+1), bornG38 η N z ℓ x)‖ ≤ A * C / η ^ (2 * L + 3) := by
  obtain ⟨C, hC0, hC⟩ := born_truncation38 L A hA0
  refine ⟨C, hC0, ?_⟩
  intro η N z Γ hA hη hΓc hΓp hΓd hΓb
  have hηpos : 0 < η := by
    have := (le_max_right (4 * A) 1).trans hη
    linarith
  have hb := hC N z Γ hA hη hΓc hΓp hΓd hΓb
  have hgc : Continuous (fun x => Γ x - ∑ ℓ ∈ Finset.range (L+1), bornG38 η N z ℓ x) :=
    hΓc.sub (continuous_finsetSum _ fun ℓ _ => (bornG38_cont_per hηpos N z ℓ).1)
  have h1 := norm_pair38_le_sup (perC1_leafU38 N z 0).cont hgc hA
  have h2 : Real.sqrt (l2sq38 (fun x => Γ x - ∑ ℓ ∈ Finset.range (L+1), bornG38 η N z ℓ x)) ≤
      C / η ^ (2 * L + 3) := by
    have hC0' : 0 ≤ C / η ^ (2 * L + 3) := by positivity
    calc _ ≤ Real.sqrt ((C / η ^ (2 * L + 3)) ^ 2) :=
          Real.sqrt_le_sqrt (l2sq38_le_sup hgc hb)
      _ = _ := Real.sqrt_sq hC0'
  have h3 := mul_le_mul_of_nonneg_left h2 hA0
  rw [mul_div_assoc]
  exact (h1.trans h3)

end NlsGge.SpectralFoundations
end
