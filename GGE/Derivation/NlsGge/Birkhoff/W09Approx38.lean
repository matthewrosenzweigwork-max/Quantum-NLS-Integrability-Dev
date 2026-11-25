import NlsGge.Birkhoff.W08Compact38b
import NlsGge.Birkhoff.W04WeightedSmoothing38c

/-! # W09 (Birkhoff wave C3), file 1: B-free Galerkin-Newton core and the Fourier projection on `E_s`

Claim `W09` (`D:lem:localinverse`, v2 l.1616-1633), blueprint `blueprint/claims/W09.md`.
This file contains only declarations that do not mention `BirkhoffInput38`:

* `galerkin_newton_W09`: an abstract Newton/contraction argument.  Let `K` be `C¹` on a Banach space
  `X`, `x ∈ X` with `Id + DK(x)` invertible, `P_N` contractive idempotents with `P_N x → x` and
  `‖(Id - P_N) DK(x)‖ → 0`.  Then for all large `N` there is `x_N = P_N x_N` with
  `x_N + P_N K(x_N) = P_N (x + K x)` and `x_N → x`.  (The derivative is frozen at the fixed base
  point `x`, which makes the uniform inverse bounds of the paper automatic; see the departure note
  in `W09_GAP.md`.)
* the Fourier projection `P_N` on `E_s` (`projE38`), contractive, idempotent, strongly convergent;
* the tail factor `‖ι - P_N ι‖ ≤ ⟨N⟩⁻¹` of the inclusion `ι : E_{s-1} ↪ E_s` (the mechanism
  behind v2's "`DK(x)` is compact, by its factorization through `E_{s-1}`").
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Composition
open Filter Topology Metric
open scoped NNReal

/-! ## Abstract Galerkin-Newton step -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **W09.05 (abstract).**  See the file header. -/
theorem galerkin_newton_W09 (P : ℕ → X →L[ℝ] X) (hP1 : ∀ N, ‖P N‖ ≤ 1)
    (hPP : ∀ N y, P N (P N y) = P N y)
    (K : X → X) (hKd : ∀ y, DifferentiableAt ℝ K y) (x : X)
    (hKc : ContinuousAt (fun y => fderiv ℝ K y) x)
    (e : X ≃L[ℝ] X) (he : (e : X →L[ℝ] X) = 1 + fderiv ℝ K x)
    (hPx : Tendsto (fun N => P N x) atTop (𝓝 x))
    (hDK : Tendsto (fun N => ‖fderiv ℝ K x - (P N).comp (fderiv ℝ K x)‖) atTop (𝓝 0)) :
    ∃ xN : ℕ → X, Tendsto xN atTop (𝓝 x) ∧
      ∀ᶠ N in atTop, P N (xN N) = xN N ∧ xN N + P N (K (xN N)) = P N (x + K x) := by
  classical
  set M : ℝ≥0 := ‖(e.symm : X →L[ℝ] X)‖₊ + 1 with hMdef
  have hM0 : (0 : ℝ) < (M : ℝ) := by rw [hMdef]; push_cast; positivity
  set c : ℝ≥0 := (2 * M)⁻¹ with hcdef
  have hc0 : (0 : ℝ) < (c : ℝ) := by
    rw [hcdef]; push_cast; positivity
  let f'symm : (e : X →L[ℝ] X).NonlinearRightInverse :=
    { toFun := e.symm
      nnnorm := M
      bound' := fun y => by
        calc ‖e.symm y‖ ≤ ‖(e.symm : X →L[ℝ] X)‖ * ‖y‖ :=
              (e.symm : X →L[ℝ] X).le_opNorm y
          _ ≤ (M : ℝ) * ‖y‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              rw [hMdef]; push_cast; linarith
      right_inv' := fun y => e.apply_symm_apply y }
  -- a neighbourhood of `x` on which `DK` varies by at most `c/2`
  obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ closedBall x ρ,
      ‖fderiv ℝ K y - fderiv ℝ K x‖ ≤ (c : ℝ) / 2 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hKc ((c : ℝ) / 2) (by positivity)
    refine ⟨δ / 2, by positivity, fun y hy => ?_⟩
    have : dist y x < δ := by
      rw [mem_closedBall] at hy; linarith
    have h := hδ' this
    rw [dist_eq_norm] at h
    exact h.le
  let ε : ℕ → ℝ := fun N => 2 * M * ‖x - P N x‖
  have hε0 : ∀ N, 0 ≤ ε N := fun N => by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ‖x - P N x‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hPx)
      simpa [norm_sub_rev] using this
    have := h1.const_mul (2 * (M : ℝ))
    rw [mul_zero] at this
    refine this.congr (fun N => ?_)
    simp [ε, mul_assoc]
  have hev : ∀ᶠ N in atTop, ‖fderiv ℝ K x - (P N).comp (fderiv ℝ K x)‖ ≤ (c : ℝ) / 2 ∧ ε N ≤ ρ := by
    have h1 : ∀ᶠ N in atTop, ‖fderiv ℝ K x - (P N).comp (fderiv ℝ K x)‖ < (c : ℝ) / 2 :=
      hDK.eventually (gt_mem_nhds (by positivity))
    have h2 : ∀ᶠ N in atTop, ε N < ρ := hεlim.eventually (gt_mem_nhds hρ0)
    filter_upwards [h1, h2] with N h1 h2 using ⟨h1.le, h2.le⟩
  -- for large `N` a solution exists in the ball of radius `ε N`
  have hex : ∀ᶠ N in atTop, ∃ y ∈ closedBall x (ε N), y + P N (K y) = P N (x + K x) := by
    filter_upwards [hev] with N ⟨hN1, hN2⟩
    set f : X → X := fun y => y + P N (K y) with hf
    have happ : ApproximatesLinearOn f (e : X →L[ℝ] X) (closedBall x ρ) c := by
      intro y hy y' hy'
      have hder : ∀ z ∈ closedBall x ρ, HasFDerivWithinAt
          (fun w => P N (K w) - fderiv ℝ K x w)
          ((P N).comp (fderiv ℝ K z) - fderiv ℝ K x) (closedBall x ρ) z := by
        intro z _
        have h1 : HasFDerivAt (fun w => P N (K w)) ((P N).comp (fderiv ℝ K z)) z :=
          (P N).hasFDerivAt.comp z (hKd z).hasFDerivAt
        exact (h1.sub (fderiv ℝ K x).hasFDerivAt).hasFDerivWithinAt
      have hb : ∀ z ∈ closedBall x ρ, ‖(P N).comp (fderiv ℝ K z) - fderiv ℝ K x‖ ≤ (c : ℝ) := by
        intro z hz
        have e1 : (P N).comp (fderiv ℝ K z) - fderiv ℝ K x =
            (P N).comp (fderiv ℝ K z - fderiv ℝ K x) -
              (fderiv ℝ K x - (P N).comp (fderiv ℝ K x)) := by
          ext v; simp
        rw [e1]
        refine (norm_sub_le _ _).trans ?_
        have e2 : ‖(P N).comp (fderiv ℝ K z - fderiv ℝ K x)‖ ≤ (c : ℝ) / 2 :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            ((mul_le_mul (hP1 N) (hρ z hz) (norm_nonneg _) zero_le_one).trans (by linarith))
        linarith
      have key := (convex_closedBall x ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb hy' hy
      have e3 : f y - f y' - (e : X →L[ℝ] X) (y - y') =
          (P N (K y) - fderiv ℝ K x y) - (P N (K y') - fderiv ℝ K x y') := by
        rw [he]
        simp only [hf, add_apply, one_apply_eq_self, map_sub]
        abel
      rw [e3]
      exact key
    have hsub : closedBall x (ε N) ⊆ closedBall x ρ := closedBall_subset_closedBall hN2
    have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse f'symm (hε0 N) hsub
    have hmem : P N (x + K x) ∈ closedBall (f x) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε N) := by
      rw [mem_closedBall, dist_eq_norm]
      have e4 : P N (x + K x) - f x = P N x - x := by
        simp only [hf, map_add]; abel
      rw [e4, norm_sub_rev]
      have e5 : ((f'symm.nnnorm : ℝ)⁻¹ - c) * ε N = ‖x - P N x‖ := by
        show (((M : ℝ))⁻¹ - (c : ℝ)) * (2 * M * ‖x - P N x‖) = _
        rw [hcdef]; push_cast
        field_simp
        ring
      rw [e5]
    obtain ⟨y, hy, hfy⟩ := hsurj hmem
    exact ⟨y, hy, hfy⟩
  -- choose the branch
  let xN : ℕ → X := fun N =>
    if h : ∃ y ∈ closedBall x (ε N), y + P N (K y) = P N (x + K x) then h.choose else x
  have hxN : ∀ᶠ N in atTop, xN N ∈ closedBall x (ε N) ∧ xN N + P N (K (xN N)) = P N (x + K x) := by
    filter_upwards [hex] with N hN
    have : xN N = hN.choose := by
      show (if h : ∃ y ∈ closedBall x (ε N), y + P N (K y) = P N (x + K x) then h.choose else x) = _
      split_ifs
      rfl
    rw [this]
    exact hN.choose_spec
  refine ⟨xN, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hεlim
    filter_upwards [hxN] with N hN
    have := hN.1
    rwa [mem_closedBall, dist_eq_norm] at this
  · filter_upwards [hxN] with N hN
    refine ⟨?_, hN.2⟩
    have h1 : P N (xN N) + P N (K (xN N)) = P N (x + K x) := by
      have := congrArg (P N) hN.2
      rwa [map_add, hPP, hPP] at this
    exact add_right_cancel (h1.trans hN.2.symm)

end Abstract

/-! ## The Fourier projection `P_N` on `E_s` -/

section EProj

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

/-- `(P_N x)_n = x_n` for `|n| ≤ N` and `0` otherwise, on `E_σ`. -/
def PmapE38 (σ : ℝ) (N : ℕ) (x : ECarrier38 c σ) : ECarrier38 c σ :=
  eMk38 c σ (fun n => if n ∈ symmetricModes N then eCoe38 c σ x n else 0) (by
    rw [mem_seqE38_iff]
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (fullModeWeight_pos c σ n).le (sq_nonneg _)) (fun n => ?_)
      ((mem_seqE38_iff c σ _).1 (eCoe38_mem c σ x))
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (fullModeWeight_pos c σ n).le (sq_nonneg _))

@[simp] theorem eCoe38_PmapE38 (σ : ℝ) (N : ℕ) (x : ECarrier38 c σ) (n : ℤ) :
    eCoe38 c σ (PmapE38 c σ N x) n = if n ∈ symmetricModes N then eCoe38 c σ x n else 0 := rfl

theorem norm_PmapE38_le (σ : ℝ) (N : ℕ) (x : ECarrier38 c σ) : ‖PmapE38 c σ N x‖ ≤ ‖x‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_sq_eCarrier38, norm_sq_eCarrier38]
  have hs : ∀ y : ECarrier38 c σ,
      Summable fun n : ℤ => fullModeWeight c σ n * ‖eCoe38 c σ y n‖ ^ 2 :=
    fun y => (mem_seqE38_iff c σ _).1 (eCoe38_mem c σ y)
  refine Summable.tsum_le_tsum (fun n => ?_) (hs _) (hs _)
  rw [eCoe38_PmapE38]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (fullModeWeight_pos c σ n).le (sq_nonneg _)

/-- `P_N` as a real-linear map on `E_σ`. -/
def projLinE38 (σ : ℝ) (N : ℕ) : ECarrier38 c σ →ₗ[ℝ] ECarrier38 c σ where
  toFun := PmapE38 c σ N
  map_add' x y := eExt38 c σ (funext fun n => by
    show (if n ∈ symmetricModes N then eCoe38 c σ (x + y) n else 0) =
      eCoe38 c σ (PmapE38 c σ N x) n + eCoe38 c σ (PmapE38 c σ N y) n
    simp only [eAdd_apply38, eCoe38_PmapE38]
    split_ifs <;> simp)
  map_smul' a x := eExt38 c σ (funext fun n => by
    show (if n ∈ symmetricModes N then eCoe38 c σ (a • x) n else 0) =
      eCoe38 c σ (a • PmapE38 c σ N x) n
    simp only [eSmul_apply38, eCoe38_PmapE38]
    split_ifs <;> simp)

/-- The Fourier projection `P_N` on `E_σ` as a continuous real-linear map. -/
def projE38 (σ : ℝ) (N : ℕ) : ECarrier38 c σ →L[ℝ] ECarrier38 c σ :=
  (projLinE38 c σ N).mkContinuous 1 (fun x => by rw [one_mul]; exact norm_PmapE38_le c σ N x)

@[simp] theorem eCoe38_projE38 (σ : ℝ) (N : ℕ) (x : ECarrier38 c σ) (n : ℤ) :
    eCoe38 c σ (projE38 c σ N x) n = if n ∈ symmetricModes N then eCoe38 c σ x n else 0 := rfl

theorem norm_projE38_le (σ : ℝ) (N : ℕ) : ‖projE38 c σ N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    rw [one_mul]; exact norm_PmapE38_le c σ N x)

theorem projE38_idem (σ : ℝ) (N : ℕ) (x : ECarrier38 c σ) :
    projE38 c σ N (projE38 c σ N x) = projE38 c σ N x := by
  refine eExt38 c σ (funext fun n => ?_)
  simp only [eCoe38_projE38]
  split_ifs <;> rfl

/-- `P_N x → x` in `E_σ`. -/
theorem tendsto_projE38 (σ : ℝ) (x : ECarrier38 c σ) :
    Tendsto (fun N : ℕ => projE38 c σ N x) atTop (𝓝 x) := by
  have h := weightedProjection_tendsto (fullModeWeight c σ)
    (show WeightedHilbert (fullModeWeight c σ) from x)
  have e : ∀ N : ℕ, projE38 c σ N x =
      (show ECarrier38 c σ from
        (show WeightedHilbert (fullModeWeight c σ) from
          weightedProjection (fullModeWeight c σ) (symmetricModes N)
            (show WeightedHilbert (fullModeWeight c σ) from x))) := fun N =>
    eExt38 c σ (funext fun n => by
      rw [eCoe38_projE38]
      exact (weightedProjection_apply _ _ _ n).symm)
  simp only [e]
  exact h

/-! ### The tail factor of the inclusion `E_{σ-1} ↪ E_σ` -/

theorem japaneseBracket_sq38 (n : ℤ) : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
  unfold japaneseBracket
  rw [Real.sq_sqrt (by positivity)]

theorem fullModeWeight_pred38 (σ : ℝ) (n : ℤ) :
    fullModeWeight c σ n = fullModeWeight c (σ - 1) n * (1 + (n : ℝ) ^ 2)⁻¹ := by
  unfold fullModeWeight
  have hj : 0 < japaneseBracket n := japaneseBracket_pos n
  have h1 : Real.rpow (japaneseBracket n) (-2 * σ) =
      Real.rpow (japaneseBracket n) (-2 * (σ - 1)) * (1 + (n : ℝ) ^ 2)⁻¹ := by
    have : (-2 * σ) = (-2 * (σ - 1)) + (-2 : ℝ) := by ring
    show japaneseBracket n ^ (-2 * σ) = japaneseBracket n ^ (-2 * (σ - 1)) * (1 + (n : ℝ) ^ 2)⁻¹
    rw [this, Real.rpow_add hj, Real.rpow_neg hj.le, Real.rpow_two, japaneseBracket_sq38]
  rw [h1]; ring

/-- `‖(1 - P_N) ι y‖_{E_σ} ≤ ⟨N⟩⁻¹ ‖y‖_{E_{σ-1}}` for the inclusion `ι : E_{σ-1} ↪ E_σ`
(the `E`-version of W08's tail factor; v2: `DK(x)` is compact "by its factorization through
`E_{s-1}`"). -/
theorem norm_tail_eIncl_le38 (σ : ℝ) (N : ℕ) :
    ‖eInclCLM38 c (by linarith : σ - 1 ≤ σ) -
        (projE38 c σ N).comp (eInclCLM38 c (by linarith : σ - 1 ≤ σ))‖ ≤ tailFactor38 N := by
  refine ContinuousLinearMap.opNorm_le_bound _ (tailFactor38_nonneg N) (fun y => ?_)
  set a := (eInclCLM38 c (by linarith : σ - 1 ≤ σ) -
        (projE38 c σ N).comp (eInclCLM38 c (by linarith : σ - 1 ≤ σ))) y with ha
  have hB : (japaneseBracket (N : ℤ)) ^ 2 = 1 + (N : ℝ) ^ 2 := by
    rw [japaneseBracket_sq38]; push_cast; ring
  have hcoe : ∀ n, eCoe38 c σ a n =
      if n ∈ symmetricModes N then 0 else eCoe38 c (σ - 1) y n := by
    intro n
    have e1 : eCoe38 c σ a n = eCoe38 c σ (eInclCLM38 c (by linarith : σ - 1 ≤ σ) y) n -
        eCoe38 c σ (projE38 c σ N (eInclCLM38 c (by linarith : σ - 1 ≤ σ) y)) n := rfl
    rw [e1, eCoe38_projE38, eCoe38_eInclCLM38]
    split_ifs <;> simp
  have hsy : Summable fun n : ℤ => fullModeWeight c (σ - 1) n * ‖eCoe38 c (σ - 1) y n‖ ^ 2 :=
    (mem_seqE38_iff c (σ - 1) _).1 (eCoe38_mem c (σ - 1) y)
  have hsa : Summable fun n : ℤ => fullModeWeight c σ n * ‖eCoe38 c σ a n‖ ^ 2 :=
    (mem_seqE38_iff c σ _).1 (eCoe38_mem c σ a)
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (tailFactor38_nonneg N) (norm_nonneg _))).1 ?_
  rw [norm_sq_eCarrier38, mul_pow, norm_sq_eCarrier38 c (σ - 1) y]
  have hsum : Summable fun n : ℤ => tailFactor38 N ^ 2 *
      (fullModeWeight c (σ - 1) n * ‖eCoe38 c (σ - 1) y n‖ ^ 2) := hsy.mul_left _
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) hsa hsum
  rw [hcoe n]
  split_ifs with hn
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (fullModeWeight_pos c _ n).le (sq_nonneg _))
  · rw [fullModeWeight_pred38 c σ n]
    have hn' : (N : ℝ) + 1 ≤ |(n : ℝ)| := by
      have : (N : ℤ) + 1 ≤ |n| := by
        unfold symmetricModes at hn
        rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
        rcases hn with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      exact_mod_cast this
    have hsq : 1 + (N : ℝ) ^ 2 ≤ 1 + (n : ℝ) ^ 2 := by
      have : (N : ℝ) ^ 2 ≤ |(n : ℝ)| ^ 2 := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
      rw [sq_abs] at this
      linarith
    have hinv : (1 + (n : ℝ) ^ 2)⁻¹ ≤ tailFactor38 N ^ 2 := by
      have : tailFactor38 N ^ 2 = (1 + (N : ℝ) ^ 2)⁻¹ := by
        unfold tailFactor38; rw [inv_pow, hB]
      rw [this]
      exact inv_anti₀ (by positivity) hsq
    have ht : 0 ≤ fullModeWeight c (σ - 1) n * ‖eCoe38 c (σ - 1) y n‖ ^ 2 :=
      mul_nonneg (fullModeWeight_pos c _ n).le (sq_nonneg _)
    calc fullModeWeight c (σ - 1) n * (1 + (n : ℝ) ^ 2)⁻¹ * ‖eCoe38 c (σ - 1) y n‖ ^ 2
        = (1 + (n : ℝ) ^ 2)⁻¹ * (fullModeWeight c (σ - 1) n * ‖eCoe38 c (σ - 1) y n‖ ^ 2) := by ring
      _ ≤ tailFactor38 N ^ 2 * (fullModeWeight c (σ - 1) n * ‖eCoe38 c (σ - 1) y n‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hinv ht

end EProj

end NlsGge.Birkhoff
