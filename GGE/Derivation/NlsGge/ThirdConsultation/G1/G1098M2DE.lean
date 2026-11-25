import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098M2C
import NlsGge.ThirdConsultation.G1.G1098M2CT

/-! # G1-098 M2d/M2e, proof development (AUTHOR; not reviewed).
M2d: the first coordinate of the complex mixed kernel is a product of Dirichlet and terminal
state values (`complexMixedKernel_false_fst`, `complexMixedKernel_true_fst`, both `rfl`). The
mixed-product expansion `ab - a₀b₀ = (a-a₀)b + a₀(b-b₀)` with the sup bounds
`‖b‖ ≤ B`, `‖a₀‖ ≤ A` gives `‖ab - a₀b₀‖² ≤ 2B²‖a-a₀‖² + 2A²‖b-b₀‖²`. Vacuum sup bounds:
`‖complexDirState 0‖ ≤ 2`, `‖complexTerminalState 0‖ ≤ 4`; state sup bounds from the square-sum
bounds via `‖x‖ ≤ 1 + ‖x‖²`.
M2e: the pointwise bound `‖(K_p - K_0) t 0‖² ≤ K·Σ(four state-error squares)` with
`K = 2MD² + 4MT² + 16`, and for each finite `T ⊆ ℤ × Bool` the sum over `T` is at most twice the
sum over `n` (`finset_bool_sum_le`), hence bounded uniformly in `T`, `t`, `φ`, `ψ`.
No hypothesis beyond the M2c square-sum bounds is added. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.Elementwise
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.G1098M2C NlsGge.ThirdConsultation.G1098M2CT
namespace NlsGge.ThirdConsultation.G1098M2DE
noncomputable section

/-- `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` in any normed additive group. -/
theorem sq_norm_add_le_two' {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  calc ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
    _ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Mixed-product expansion: `‖ab - a₀b₀‖² ≤ 2B²‖a-a₀‖² + 2A²‖b-b₀‖²` when `‖b‖ ≤ B`, `‖a₀‖ ≤ A`. -/
theorem sq_norm_mul_sub_mul_le {a a0 b b0 : ℂ} {A B : ℝ} (hb : ‖b‖ ≤ B) (ha0 : ‖a0‖ ≤ A) :
    ‖a * b - a0 * b0‖ ^ 2 ≤ 2 * B ^ 2 * ‖a - a0‖ ^ 2 + 2 * A ^ 2 * ‖b - b0‖ ^ 2 := by
  have key : a * b - a0 * b0 = (a - a0) * b + a0 * (b - b0) := by ring
  have h1 : ‖a * b - a0 * b0‖ ≤ ‖a - a0‖ * B + A * ‖b - b0‖ := by
    rw [key]
    calc ‖(a - a0) * b + a0 * (b - b0)‖ ≤ ‖(a - a0) * b‖ + ‖a0 * (b - b0)‖ := norm_add_le _ _
      _ = ‖a - a0‖ * ‖b‖ + ‖a0‖ * ‖b - b0‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a - a0‖ * B + A * ‖b - b0‖ := by
          have e1 := mul_le_mul_of_nonneg_left hb (norm_nonneg (a - a0))
          have e2 := mul_le_mul_of_nonneg_right ha0 (norm_nonneg (b - b0))
          linarith
  have hnn : 0 ≤ ‖a * b - a0 * b0‖ := norm_nonneg _
  calc ‖a * b - a0 * b0‖ ^ 2 ≤ (‖a - a0‖ * B + A * ‖b - b0‖) ^ 2 :=
        pow_le_pow_left₀ hnn h1 2
    _ ≤ 2 * B ^ 2 * ‖a - a0‖ ^ 2 + 2 * A ^ 2 * ‖b - b0‖ ^ 2 := by
        nlinarith [sq_nonneg (‖a - a0‖ * B - A * ‖b - b0‖)]

theorem complexMixedKernel_false_fst (φ ψ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexMixedKernel φ ψ n false t 0 = complexDirState φ n t 1 * complexDirState ψ n t 1 :=
  rfl

theorem complexMixedKernel_true_fst (φ ψ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    complexMixedKernel φ ψ n true t 0 =
      Complex.I * (complexDirState φ n t 1 * complexTerminalState ψ n t 1 +
        complexDirState ψ n t 1 * complexTerminalState φ n t 1) :=
  rfl

/-- Vacuum Dirichlet state is bounded by `2` (two free-solution entries of modulus one). -/
theorem complexDirState_zero_norm_le (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    ‖complexDirState 0 n t 1‖ ≤ 2 := by
  rw [complexDirState_zero_apply_one]
  calc ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 0 + freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 1‖
      ≤ ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 0‖ + ‖freeFund ((n : ℂ) * (Real.pi : ℂ)) t 1 1‖ :=
        norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add (freeFund_nPi_entry_le n t 1 0) (freeFund_nPi_entry_le n t 1 1)
    _ = 2 := by norm_num

theorem norm_terminal_comb_le (X Y Z W : ℂ) (hX : ‖X‖ ≤ 2) (hY : ‖Y‖ ≤ 1) (hZ : ‖Z‖ ≤ 2)
    (hW : ‖W‖ ≤ 1) : ‖X * Y + (-Z) * W‖ ≤ 4 := by
  calc ‖X * Y + (-Z) * W‖ ≤ ‖X * Y‖ + ‖(-Z) * W‖ := norm_add_le _ _
    _ = ‖X‖ * ‖Y‖ + ‖Z‖ * ‖W‖ := by rw [norm_mul, norm_mul, norm_neg]
    _ ≤ 2 * 1 + 2 * 1 :=
        add_le_add (mul_le_mul hX hY (norm_nonneg _) (by norm_num))
          (mul_le_mul hZ hW (norm_nonneg _) (by norm_num))
    _ = 4 := by norm_num

/-- Vacuum terminal state is bounded by `4`. -/
theorem complexTerminalState_zero_norm_le (n : ℤ) (t : Set.Icc (0 : ℝ) 1) :
    ‖complexTerminalState 0 n t 1‖ ≤ 4 := by
  rw [complexTerminalState_apply_one 0 n t, muSeq_zero_nPi, terminalSeed_eq_fundPair]
  simp only [fundPair_zero_eq_freeFund, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact norm_terminal_comb_le _ _ _ _ (freeFund_nPi_col_sum_le n tOneIcc 1)
    (freeFund_nPi_entry_le n t 1 0) (freeFund_nPi_col_sum_le n tOneIcc 0)
    (freeFund_nPi_entry_le n t 1 1)

/-- A state error with square at most `C` has modulus at most `1 + C`. -/
theorem norm_le_one_add_of_sq_le (x : ℂ) (C : ℝ) (h : ‖x‖ ^ 2 ≤ C) : ‖x‖ ≤ 1 + C := by
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

/-- Plus column, pointwise in `n` and `t`. -/
theorem plus_diff_sq_le (φ ψ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (MD : ℝ)
    (hψ : ‖complexDirState ψ n t 1‖ ≤ MD) :
    ‖(complexMixedKernel φ ψ n false - complexMixedKernel 0 0 n false) t 0‖ ^ 2 ≤
      2 * MD ^ 2 * ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
        8 * ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 := by
  have h := sq_norm_mul_sub_mul_le (a := complexDirState φ n t 1)
    (a0 := complexDirState 0 n t 1) (b := complexDirState ψ n t 1)
    (b0 := complexDirState 0 n t 1) (A := 2) (B := MD) hψ (complexDirState_zero_norm_le n t)
  rw [ContinuousMap.sub_apply, Pi.sub_apply, complexMixedKernel_false_fst,
    complexMixedKernel_false_fst]
  linarith

/-- Minus column, pointwise in `n` and `t`. -/
theorem minus_diff_sq_le (φ ψ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (MT : ℝ)
    (hφT : ‖complexTerminalState φ n t 1‖ ≤ MT) (hψT : ‖complexTerminalState ψ n t 1‖ ≤ MT) :
    ‖(complexMixedKernel φ ψ n true - complexMixedKernel 0 0 n true) t 0‖ ^ 2 ≤
      2 * (2 * MT ^ 2 * ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
        8 * ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) +
      2 * (2 * MT ^ 2 * ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
        8 * ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) := by
  have hD0 := complexDirState_zero_norm_le n t
  have h1 := sq_norm_mul_sub_mul_le (a := complexDirState φ n t 1)
    (a0 := complexDirState 0 n t 1) (b := complexTerminalState ψ n t 1)
    (b0 := complexTerminalState 0 n t 1) (A := 2) (B := MT) hψT hD0
  have h2 := sq_norm_mul_sub_mul_le (a := complexDirState ψ n t 1)
    (a0 := complexDirState 0 n t 1) (b := complexTerminalState φ n t 1)
    (b0 := complexTerminalState 0 n t 1) (A := 2) (B := MT) hφT hD0
  have hsum := sq_norm_add_le_two'
    (complexDirState φ n t 1 * complexTerminalState ψ n t 1 -
      complexDirState 0 n t 1 * complexTerminalState 0 n t 1)
    (complexDirState ψ n t 1 * complexTerminalState φ n t 1 -
      complexDirState 0 n t 1 * complexTerminalState 0 n t 1)
  have hdiff : (complexMixedKernel φ ψ n true - complexMixedKernel 0 0 n true) t 0 =
      Complex.I * ((complexDirState φ n t 1 * complexTerminalState ψ n t 1 -
          complexDirState 0 n t 1 * complexTerminalState 0 n t 1) +
        (complexDirState ψ n t 1 * complexTerminalState φ n t 1 -
          complexDirState 0 n t 1 * complexTerminalState 0 n t 1)) := by
    rw [ContinuousMap.sub_apply, Pi.sub_apply, complexMixedKernel_true_fst,
      complexMixedKernel_true_fst]
    ring
  rw [hdiff, norm_mul, Complex.norm_I, one_mul]
  linarith

/-- Uniform pointwise bound on the first-coordinate kernel difference, both columns. -/
theorem mixed_diff_sq_le (φ ψ : PotPair) (n : ℤ) (t : Set.Icc (0 : ℝ) 1) (MD MT : ℝ)
    (hφD : ‖complexDirState φ n t 1‖ ≤ MD) (hψD : ‖complexDirState ψ n t 1‖ ≤ MD)
    (hφT : ‖complexTerminalState φ n t 1‖ ≤ MT) (hψT : ‖complexTerminalState ψ n t 1‖ ≤ MT)
    (b : Bool) :
    ‖(complexMixedKernel φ ψ n b - complexMixedKernel 0 0 n b) t 0‖ ^ 2 ≤
      (2 * MD ^ 2 + 4 * MT ^ 2 + 16) *
        (‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
          ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
          ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 +
          ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) := by
  have x1 := sq_nonneg ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖
  have x2 := sq_nonneg ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖
  have x3 := sq_nonneg ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖
  have x4 := sq_nonneg ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖
  have m1 := sq_nonneg MD
  have m2 := sq_nonneg MT
  cases b with
  | false =>
    have h := plus_diff_sq_le φ ψ n t MD hψD
    nlinarith [mul_nonneg m1 x2, mul_nonneg m1 x3, mul_nonneg m1 x4,
      mul_nonneg m2 x1, mul_nonneg m2 x2, mul_nonneg m2 x3, mul_nonneg m2 x4]
  | true =>
    have h := minus_diff_sq_le φ ψ n t MT hφT hψT
    nlinarith [mul_nonneg m1 x1, mul_nonneg m1 x2, mul_nonneg m1 x3, mul_nonneg m1 x4,
      mul_nonneg m2 x1, mul_nonneg m2 x2, mul_nonneg m2 x3, mul_nonneg m2 x4]

/-- Each finite set of pairs, summed over the first index with multiplicity at most two. -/
theorem finset_bool_sum_le (f : ℤ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f)
    (T : Finset (ℤ × Bool)) : ∑ j ∈ T, f j.1 ≤ 2 * ∑' n, f n := by
  have hsub : T ⊆ (T.image Prod.fst) ×ˢ (Finset.univ : Finset Bool) := by
    intro j hj
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem Prod.fst hj, Finset.mem_univ _⟩
  calc ∑ j ∈ T, f j.1 ≤ ∑ j ∈ (T.image Prod.fst) ×ˢ (Finset.univ : Finset Bool), f j.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hf0 j.1)
    _ = ∑ n ∈ T.image Prod.fst, ∑ _b : Bool, f n := by
        rw [Finset.sum_product]
    _ = ∑ n ∈ T.image Prod.fst, 2 * f n := by
        apply Finset.sum_congr rfl
        intro n _
        simp [Finset.sum_const, Fintype.card_bool]
    _ = 2 * ∑ n ∈ T.image Prod.fst, f n := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑' n, f n :=
        mul_le_mul_of_nonneg_left (hf.sum_le_tsum _ (fun n _ => hf0 n)) (by norm_num)

/-- M2e: uniform finite-sum bound for the first coordinate of the kernel differences, at each
time, with constants depending only on the square-sum bounds `CD`, `CT`. -/
theorem mixed_finite_sum_bound (φ ψ : PotPair) (t : Set.Icc (0 : ℝ) 1) (CD CT : ℝ)
    (hdφ : Summable (fun n : ℤ => ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2) ∧
      (∑' n : ℤ, ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2) ≤ CD)
    (hdψ : Summable (fun n : ℤ => ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2) ∧
      (∑' n : ℤ, ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2) ≤ CD)
    (htφ : Summable (fun n : ℤ =>
      ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ∧
      (∑' n : ℤ, ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ≤ CT)
    (htψ : Summable (fun n : ℤ =>
      ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ∧
      (∑' n : ℤ, ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) ≤ CT)
    (T : Finset (ℤ × Bool)) :
    ∑ j ∈ T, ‖(complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) t 0‖ ^ 2 ≤
      2 * ((2 * (3 + CD) ^ 2 + 4 * (5 + CT) ^ 2 + 16) * (2 * CD + 2 * CT)) := by
  -- sup bounds on the states, uniform in `n`
  have hsupD : ∀ (χ : PotPair), (∀ n : ℤ, ‖complexDirState χ n t 1 - complexDirState 0 n t 1‖ ^ 2 ≤ CD) →
      ∀ n : ℤ, ‖complexDirState χ n t 1‖ ≤ 3 + CD := by
    intro χ hχ n
    have e : complexDirState 0 n t 1 + (complexDirState χ n t 1 - complexDirState 0 n t 1) =
        complexDirState χ n t 1 := by ring
    have h1 := norm_add_le (complexDirState 0 n t 1)
      (complexDirState χ n t 1 - complexDirState 0 n t 1)
    rw [e] at h1
    have h2 := norm_le_one_add_of_sq_le _ CD (hχ n)
    have h3 := complexDirState_zero_norm_le n t
    linarith
  have hsupT : ∀ (χ : PotPair),
      (∀ n : ℤ, ‖complexTerminalState χ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 ≤ CT) →
      ∀ n : ℤ, ‖complexTerminalState χ n t 1‖ ≤ 5 + CT := by
    intro χ hχ n
    have e : complexTerminalState 0 n t 1 +
        (complexTerminalState χ n t 1 - complexTerminalState 0 n t 1) =
        complexTerminalState χ n t 1 := by ring
    have h1 := norm_add_le (complexTerminalState 0 n t 1)
      (complexTerminalState χ n t 1 - complexTerminalState 0 n t 1)
    rw [e] at h1
    have h2 := norm_le_one_add_of_sq_le _ CT (hχ n)
    have h3 := complexTerminalState_zero_norm_le n t
    linarith
  have hD_φ : ∀ n : ℤ, ‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 ≤ CD :=
    fun n => (hdφ.1.le_tsum n (fun j _ => sq_nonneg _)).trans hdφ.2
  have hD_ψ : ∀ n : ℤ, ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 ≤ CD :=
    fun n => (hdψ.1.le_tsum n (fun j _ => sq_nonneg _)).trans hdψ.2
  have hT_φ : ∀ n : ℤ, ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 ≤ CT :=
    fun n => (htφ.1.le_tsum n (fun j _ => sq_nonneg _)).trans htφ.2
  have hT_ψ : ∀ n : ℤ, ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 ≤ CT :=
    fun n => (htψ.1.le_tsum n (fun j _ => sq_nonneg _)).trans htψ.2
  set K : ℝ := 2 * (3 + CD) ^ 2 + 4 * (5 + CT) ^ 2 + 16 with hK
  let G : ℤ → ℝ := fun n => K * (‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
    ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
    ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 +
    ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hG0 : ∀ n, 0 ≤ G n := fun n => mul_nonneg hK0 (by positivity)
  have hGs : Summable G := by
    have := ((hdφ.1.add hdψ.1).add htφ.1).add htψ.1
    exact this.mul_left K
  have hGsum : ∑' n, G n ≤ K * (2 * CD + 2 * CT) := by
    have e : ∀ n, G n = K * (‖complexDirState φ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
        ‖complexDirState ψ n t 1 - complexDirState 0 n t 1‖ ^ 2 +
        ‖complexTerminalState φ n t 1 - complexTerminalState 0 n t 1‖ ^ 2 +
        ‖complexTerminalState ψ n t 1 - complexTerminalState 0 n t 1‖ ^ 2) := fun n => rfl
    rw [tsum_congr e, tsum_mul_left,
      Summable.tsum_add ((hdφ.1.add hdψ.1).add htφ.1) htψ.1,
      Summable.tsum_add (hdφ.1.add hdψ.1) htφ.1,
      Summable.tsum_add hdφ.1 hdψ.1]
    have := mul_le_mul_of_nonneg_left (add_le_add
      (add_le_add (add_le_add hdφ.2 hdψ.2) htφ.2) htψ.2) hK0
    linarith
  have hpt : ∀ j : ℤ × Bool,
      ‖(complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) t 0‖ ^ 2 ≤ G j.1 := by
    intro j
    exact mixed_diff_sq_le φ ψ j.1 t (3 + CD) (5 + CT)
      (hsupD φ hD_φ j.1) (hsupD ψ hD_ψ j.1) (hsupT φ hT_φ j.1) (hsupT ψ hT_ψ j.1) j.2
  calc ∑ j ∈ T, ‖(complexMixedKernel φ ψ j.1 j.2 - complexMixedKernel 0 0 j.1 j.2) t 0‖ ^ 2
      ≤ ∑ j ∈ T, G j.1 := Finset.sum_le_sum fun j _ => hpt j
    _ ≤ 2 * ∑' n, G n := finset_bool_sum_le G hG0 hGs T
    _ ≤ 2 * (K * (2 * CD + 2 * CT)) := mul_le_mul_of_nonneg_left hGsum (by norm_num)
    _ = 2 * ((2 * (3 + CD) ^ 2 + 4 * (5 + CT) ^ 2 + 16) * (2 * CD + 2 * CT)) := by rw [hK]

end
end NlsGge.ThirdConsultation.G1098M2DE
