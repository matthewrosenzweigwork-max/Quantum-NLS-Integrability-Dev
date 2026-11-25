import NlsGge.Ramer.RamerStep8Bridge
import NlsGge.Ramer.LinearDecomposition

/-!
# D2, part 1: Step 8 hypotheses for the linear small map `S = I + iA` and for `S⁻¹ = I + iM`

`A = (I - P_n) ∘ K̃` and `M = -A ∘ S⁻¹` are tail-valued continuous linear maps `E → H` with
`‖B ∘ i‖ ≤ 1/7 < 1/2` (D1).  For tail-valued `B` (`P_n B = 0`), the R5 weight bound gives
`‖i (B y)‖ < ε/2` and `‖i (P_k B y)‖ < ε/2` for all `k`, once `n` is large (depending on `ε` and
a bound `D` for `‖B y‖` on the ball).  Then `Step8Hyp` holds and `step8c_ramerJac` applies.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot


section AbstractGe

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `linear_decomposition` (D1) with `n` chosen `≥ n₀` (the tail bound holds for all large `n`). -/
theorem linear_decomposition_ge {ι : Type*} (i : H →L[ℝ] E) (b : HilbertBasis ι ℝ H)
    (hi : Summable fun p => ‖i (b p)‖ ^ 2) (K : E →L[ℝ] H) (T : E ≃L[ℝ] E)
    (hT : ∀ x, T x = x + i (K x)) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (R : ℕ → H →L[ℝ] H) (hR : ∀ n x, R n x = x - P n x) (n₀ : ℕ) :
    ∃ (n : ℕ) (S Pi : E ≃L[ℝ] E) (M : E →L[ℝ] H), n₀ ≤ n ∧
      (∀ h, ‖((R n).comp K) (i h)‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + i (((R n).comp K) x)) ∧
      (∀ x, S.symm x = x + i (M x)) ∧
      (∀ x, M x = -(((R n).comp K) (S.symm x))) ∧
      (∀ h, ‖M (i h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = i (P n (K (S.symm x)))) := by
  have hB := (hs_comp_left i b hi K).1
  obtain ⟨N, hN⟩ := exists_tail_opNorm_lt (K.comp i) b hB P hP hlim (1 / 8) (by norm_num)
  have hlt := hN (max N n₀) (le_max_left _ _)
  set n := max N n₀ with hn
  have hRe : R n = ContinuousLinearMap.id ℝ H - P n := by
    ext x; simp [hR]
  have hA : ((R n).comp K).comp i = (R n).comp (K.comp i) := rfl
  rw [hRe] at hA
  rw [← hA, ← hRe] at hlt
  obtain ⟨S, M, hS, hSs, hM, hMn⟩ :=
    exists_neumann_equiv i ((R n).comp K) (1 / 8) hlt.le (by norm_num)
  refine ⟨n, S, S.symm.trans T, M, le_max_right _ _,
    fun h => ((((R n).comp K).comp i).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _)),
    hS, hSs, hM, fun h => ((M.comp i).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hMn (norm_nonneg _)), fun x => rfl, fun x => ?_⟩
  have h1 : (S.symm.trans T) x = T (S.symm x) := rfl
  rw [h1, hT]
  have := hS (S.symm x)
  rw [S.apply_symm_apply] at this
  generalize S.symm x = y at this ⊢
  rw [this]
  simp only [ContinuousLinearMap.comp_apply, hR, map_sub]
  abel

end AbstractGe

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The conclusion of `step8c_ramerJac`, as a named proposition. -/
def Step8Concl (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) (ε : ℝ) : Prop :=
  (∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
        x ∈ closedBall (0 : FullWeightedHilbert c s) ε → 0 < ramerJac c s hs L x) ∧
      (∀ M : Set (FullWeightedHilbert c s), M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M,
          ENNReal.ofReal (ramerJac c s hs L x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
        NlsGge.Measure.fullWeightedSequenceGaussian c s M) ∧
      (∀ M : Set (FullWeightedHilbert c s), MeasurableSet M →
        M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        NlsGge.Measure.fullWeightedSequenceGaussian c s M = 0 →
        NlsGge.Measure.fullWeightedSequenceGaussian c s
          (closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M) = 0)

theorem step8Concl_of_hyp (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hyp : Step8Hyp c s hs L ε) : Step8Concl c s hs L ε :=
  step8c_ramerJac c s hs L hyp

/-- Coordinates of `P_k (I - P_n) h`. -/
theorem cmCoord_headProj_tailProj (k n : ℕ) (h : ActualCM c) (m : ℤ) :
    cmCoord (headProj c k (tailProj c n h)) m =
      if m ∈ symmetricModes k then
        (if m ∈ symmetricModes n then 0 else cmCoord h m) else 0 := by
  rw [headProj_apply, cmCoord_cmTrunc, tailProj_apply, headProj_apply]
  have e : cmCoord (h - ((cmTrunc c n h : actualCMHead c n) : ActualCM c)) m =
      cmCoord h m - cmCoord ((cmTrunc c n h : actualCMHead c n) : ActualCM c) m := rfl
  rw [e, cmCoord_cmTrunc]
  split_ifs <;> simp

theorem headProj_tailProj_of_le {k n : ℕ} (hkn : k ≤ n) (h : ActualCM c) :
    headProj c k (tailProj c n h) = 0 := by
  apply cmCoord_ext
  intro m
  rw [cmCoord_headProj_tailProj]
  have : m ∈ symmetricModes k → m ∈ symmetricModes n := by
    intro hm
    simp only [symmetricModes, Finset.mem_Icc] at hm ⊢
    omega
  by_cases h1 : m ∈ symmetricModes k
  · simp [h1, this h1]; rfl
  · simp [h1]; rfl

theorem norm_tailProj_le (n : ℕ) (h : ActualCM c) : ‖tailProj c n h‖ ≤ 2 * ‖h‖ := by
  rw [tailProj_apply, headProj_apply]
  have := norm_cmTrunc_le c n h
  calc ‖h - ((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖
      ≤ ‖h‖ + ‖((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖ := norm_sub_le _ _
    _ ≤ 2 * ‖h‖ := by
        have h2 : ‖((cmTrunc c n h : actualCMHead c n) : ActualCM c)‖ ≤ ‖h‖ := this
        linarith

theorem norm_headProj_le (n : ℕ) (h : ActualCM c) : ‖headProj c n h‖ ≤ ‖h‖ := by
  rw [headProj_apply]; exact norm_cmTrunc_le c n h

/-- R5 for a tail-valued vector `g` (`P_n g = 0`): `‖i g‖ < ε/2` and `‖i (P_k g)‖ < ε/2` for
every `k`, provided `n` satisfies the R5 bound for the radius `D` with `ε/2`. -/
theorem small_of_tail (hs : (1 : ℝ) / 2 < s) (ε D : ℝ) (n : ℕ)
    (hn : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < D →
      ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2)
    (g : ActualCM c) (hg : headProj c n g = 0) (hgD : ‖g‖ < D) :
    ‖inclE c s hs g‖ < ε / 2 ∧ ∀ k : ℕ, ‖inclE c s hs (headProj c k g)‖ < ε / 2 := by
  have h0 : ‖inclE c s hs g‖ < ε / 2 / 2 := by
    have := hn n le_rfl g hgD
    have e : ((cmTrunc c n g : actualCMHead c n) : ActualCM c) = 0 := hg
    rw [e, map_zero, sub_zero] at this
    exact this
  refine ⟨by linarith [h0, norm_nonneg (inclE c s hs g)], fun k => ?_⟩
  have hε : 0 < ε / 2 / 2 := lt_of_le_of_lt (norm_nonneg _) h0
  by_cases hk : k ≤ n
  · have : headProj c k g = 0 := by
      have e : g = tailProj c n g := by
        rw [tailProj_apply, hg, sub_zero]
      rw [e]; exact headProj_tailProj_of_le c hk g
    rw [this, map_zero, norm_zero]; linarith
  · have hk' : n ≤ k := (not_le.1 hk).le
    have h1 := hn k hk' g hgD
    have e : inclE c s hs (headProj c k g) =
        inclE c s hs g - (cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) g -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c k g : actualCMHead c k) : ActualCM c)) := by
      rw [headProj_apply]; show _ = _ - (_ - _); abel
    rw [e]
    calc _ ≤ ‖inclE c s hs g‖ + ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) g -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c k g : actualCMHead c k) : ActualCM c)‖ := norm_sub_le _ _
      _ < ε / 2 := by linarith

/-- `Step8Hyp` for a tail-valued continuous linear field `B : E → H` with `‖B ∘ i‖ ≤ r ≤ 1/2`. -/
theorem step8Hyp_of_tail (hs : (1 : ℝ) / 2 < s) (B : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (n : ℕ) (hB : ∀ y, headProj c n (B y) = 0) (r : ℝ) (hr : r ≤ 1 / 2)
    (hBi : ∀ h : ActualCM c, ‖B (inclE c s hs h)‖ ≤ r * ‖h‖) (ε D : ℝ) (hε : 0 < ε)
    (hD : ∀ y : FullWeightedHilbert c s, ‖y‖ ≤ ε → ‖B y‖ < D)
    (hn : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < D →
      ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2) :
    Step8Hyp c s hs (fun y => B y) ε := by
  have hsm : ∀ y : FullWeightedHilbert c s, ‖y‖ ≤ ε →
      ‖inclE c s hs (B y)‖ < ε / 2 ∧ ∀ k : ℕ, ‖inclE c s hs (headProj c k (B y))‖ < ε / 2 :=
    fun y hy => small_of_tail c s hs ε D n hn (B y) (hB y) (hD y hy)
  refine ⟨B.contDiff, ⟨hε, fun y _ => B.differentiableAt, fun y hy => ?_, fun y _ => ?_⟩,
    fun k => ⟨hε, fun y _ => ((headProj c k).comp B).differentiableAt, fun y hy => ?_,
      fun y _ => ?_⟩⟩
  · exact (hsm y (mem_closedBall_zero_iff.1 hy)).1
  · have e : fderiv ℝ (fun y => B y) y = B := B.fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => B y) y (inclE c s hs h)‖ ≤ _
    rw [e]
    exact (hBi h).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  · exact (hsm y (mem_closedBall_zero_iff.1 hy)).2 k
  · have e : fderiv ℝ (fun y => headProj c k (B y)) y = (headProj c k).comp B :=
      ((headProj c k).comp B).fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => headProj c k (B y)) y (inclE c s hs h)‖ ≤ _
    rw [e]
    exact ((norm_headProj_le c k _).trans (hBi h)).trans
      (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

/-- **Step 8 for `S = I + iA`**, `A = (I - P_n) K̃`: all hypotheses of `step8c` hold on `B̄_ε`,
hence (**) and null-set preservation on `B_{ε/2}`, stated with `ramerJac A`. -/
theorem linearSmall_step8_S (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2) :
    Step8Hyp c s hs (fun y => tailProj c n (K y)) ε ∧
      Step8Concl c s hs (fun y => tailProj c n (K y)) ε := by
  have hyp : Step8Hyp c s hs (fun y => tailProj c n (K y)) ε := by
    refine step8Hyp_of_tail c s hs ((tailProj c n).comp K) n
      (fun y => headProj_tailProj_of_le c le_rfl _) (1 / 8) (by norm_num) hAi ε
      (3 * κ * ε + 1) hε (fun y hy => ?_) hn
    have h1 : ‖tailProj c n (K y)‖ ≤ 2 * ‖K y‖ := norm_tailProj_le c n _
    have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
    have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
    show ‖tailProj c n (K y)‖ < _
    nlinarith
  exact ⟨hyp, step8Concl_of_hyp c s hs _ hyp⟩

/-- **Step 8 for `S⁻¹ = I + iM`**, `M = -A ∘ S⁻¹` (tail-valued, `‖M ∘ i‖ ≤ 1/7`). -/
theorem linearSmall_step8_Sinv (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (S : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (M : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖)
    (hSs : ∀ x, S.symm x = x + inclE c s hs (M x))
    (hM : ∀ x, M x = -(tailProj c n (K (S.symm x))))
    (hMi : ∀ h : ActualCM c, ‖M (inclE c s hs h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s (zero_le_of_half_lt hs) h -
        cmToFullWeightedHilbert c s (zero_le_of_half_lt hs)
          ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2) :
    Step8Hyp c s hs (fun y => M y) ε ∧ Step8Concl c s hs (fun y => M y) ε := by
  have hyp : Step8Hyp c s hs (fun y => M y) ε := by
    refine step8Hyp_of_tail c s hs M n (fun y => ?_) ((1 / 8) / (1 - 1 / 8)) (by norm_num) hMi ε
      (3 * κ * ε + 1) hε (fun y hy => ?_) hn
    · rw [hM y, map_neg, headProj_tailProj_of_le c le_rfl, neg_zero]
    · have e : M y = -(tailProj c n (K y)) - tailProj c n (K (inclE c s hs (M y))) := by
        conv_lhs => rw [hM y, hSs y]
        rw [map_add, map_add]; abel
      have h1 : ‖tailProj c n (K y)‖ ≤ 2 * ‖K y‖ := norm_tailProj_le c n _
      have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
      have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
      have h5 : ‖M y‖ ≤ ‖tailProj c n (K y)‖ + (1 / 8) * ‖M y‖ := by
        calc ‖M y‖ ≤ ‖-(tailProj c n (K y))‖ + ‖tailProj c n (K (inclE c s hs (M y)))‖ := by
              exact (congrArg norm e).le.trans (norm_sub_le _ _)
          _ ≤ _ := by rw [norm_neg]; linarith [hAi (M y)]
      nlinarith
  exact ⟨hyp, step8Concl_of_hyp c s hs _ hyp⟩

/-- **Combined form, with `n` enlarged.**  For `K̃ : E →L H` with `T = I + iK̃` invertible, and any
`ε > 0`, there is `n` (so large that the R5 tail bounds hold) with the D1 decomposition
`T̃ = Π ∘ S`, `S = I + iA`, `S⁻¹ = I + iM`, and Step 8 applies to `A` and to `M`. -/
theorem linearSmall_step8 (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + inclE c s hs (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (S Pi : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
      (M : FullWeightedHilbert c s →L[ℝ] ActualCM c),
      (∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + inclE c s hs (tailProj c n (K x))) ∧
      (∀ x, S.symm x = x + inclE c s hs (M x)) ∧
      (∀ x, M x = -(tailProj c n (K (S.symm x)))) ∧
      (∀ h : ActualCM c, ‖M (inclE c s hs h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = inclE c s hs (headProj c n (K (S.symm x)))) ∧
      (∀ x, SameTail c s n (Pi x) x) ∧
      Step8Hyp c s hs (fun y => tailProj c n (K y)) ε ∧
      Step8Concl c s hs (fun y => tailProj c n (K y)) ε ∧
      Step8Hyp c s hs (fun y => M y) ε ∧ Step8Concl c s hs (fun y => M y) ε := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (ActualCM c)
  have hi := cmToFullWeightedHilbert_hs c s hs b
  obtain ⟨n₀, hn₀⟩ := exists_tail_small c s (by linarith : 0 < s) (3 * κ * ε + 1) (ε / 2) (by linarith)
  obtain ⟨n, S, Pi, M, hnn, hAi', hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge (inclE c s hs) b hi K T hT (headProj c)
      (fun n x => norm_cmTrunc_le c n x) (headProj_tendsto c)
      (tailProj c) (tailProj_apply c) n₀
  have hAi : ∀ h : ActualCM c, ‖tailProj c n (K (inclE c s hs h))‖ ≤ (1 / 8) * ‖h‖ := hAi'
  have hMi : ∀ h : ActualCM c, ‖M (inclE c s hs h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖ := hMi
  have hn' : ∀ m ≥ n, ∀ h : ActualCM c, ‖h‖ < 3 * κ * ε + 1 →
      ‖cmToFullWeightedHilbert c s hs0 h - cmToFullWeightedHilbert c s hs0
        ((cmTrunc c m h : actualCMHead c m) : ActualCM c)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hS' : ∀ x, S x = x + inclE c s hs (tailProj c n (K x)) := hS
  have hM' : ∀ x, M x = -(tailProj c n (K (S.symm x))) := hM
  have h7 : ∀ x, Pi x - x = inclE c s hs (headProj c n (K (S.symm x))) := hPi2
  have hfix : ∀ x, SameTail c s n (Pi x) x := by
    intro x m hm
    have e : coordE c s (Pi x - x) m = 0 := by
      rw [h7 x]; exact coordE_incl_headProj c s hs0 n (K (S.symm x)) m hm
    rw [coordE_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨hyA, hcA⟩ := linearSmall_step8_S c s hs K κ hκ hK n hAi ε hε hn'
  obtain ⟨hyM, hcM⟩ := linearSmall_step8_Sinv c s hs K S M κ hκ hK n hAi hSs hM' hMi ε hε hn'
  exact ⟨n, S, Pi, M, hAi, hS', hSs, hM', hMi, hPi, h7, hfix, hyA, hcA,
    hyM, hcM⟩

end NlsGge.Ramer
