import Mathlib
import NlsGge.Ramer.General.RamerStep8BridgeG
import NlsGge.Ramer.General.LinearDecompositionG

/-!
# D2, part 1: Step 8 hypotheses for the linear small map, generalized (GE1)

Adapted from `NlsGge/Ramer/LinearSmallStep8.lean`.  Dictionary: `c, s, hs ↦ S`,
`inclE ↦ S.incl`, `cmToFullWeightedHilbert ↦ S.incl`, `cmTrunc ↦ S.headProj`,
`headProj c ↦ S.headProj`, `tailProj c ↦ S.tailProj`, `ramerJac ↦ S.ramerJac`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `SameTail c s ↦ S.SameTail`.

Anisotropy check (`small_of_tail`): the old proof is a pure norm/triangle-inequality argument
about the vectors `incl g - incl (P_m g)`; the R5 tail bound enters only through the hypothesis
`hn` (supplied by `Gen.exists_tail_small`, i.e. `S.tail_bound`).  No isotropy of `E` is used and
all constants (`1/8`, `1/7`, `2`) are unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section AbstractGe

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `linear_decomposition` (D1) with `n` chosen `≥ n₀` (the tail bound holds for all large `n`).
(Old: `NlsGge.Ramer.linear_decomposition_ge`.) -/
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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer.Gen NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- The conclusion of `step8c_ramerJac`, as a named proposition. (Old: `Step8Concl`.) -/
def Step8Concl (L : S.E → S.H) (ε : ℝ) : Prop :=
  (∀ᵐ x ∂S.γE, x ∈ closedBall (0 : S.E) ε → 0 < S.ramerJac L x) ∧
      (∀ M : Set S.E, M ⊆ ball (0 : S.E) (ε / 2) →
        ∫⁻ x in closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M,
          ENNReal.ofReal (S.ramerJac L x) ∂S.γE ≤ S.γE M) ∧
      (∀ M : Set S.E, MeasurableSet M → M ⊆ ball (0 : S.E) (ε / 2) →
        S.γE M = 0 →
        S.γE (closedBall (0 : S.E) ε ∩ (fun y => y + S.incl (L y)) ⁻¹' M) = 0)

/-- (Old: `step8Concl_of_hyp`.) -/
theorem step8Concl_of_hyp (L : S.E → S.H) {ε : ℝ} (hyp : S.Step8Hyp L ε) :
    S.Step8Concl L ε :=
  S.step8c_ramerJac L hyp

/-- Coordinates of `P_k (I - P_n) h`. (Old: `cmCoord_headProj_tailProj`.) -/
theorem hcoord_headProj_tailProj (k n : ℕ) (h : S.H) (m : ℤ) :
    S.hcoord (S.headProj k (S.tailProj n h)) m =
      if m ∈ symmetricModes k then
        (if m ∈ symmetricModes n then 0 else S.hcoord h m) else 0 := by
  rw [S.hcoord_headProj, S.tailProj_apply]
  have e : S.hcoord (h - S.headProj n h) m = S.hcoord h m - S.hcoord (S.headProj n h) m := rfl
  rw [e, S.hcoord_headProj]
  split_ifs <;> simp

/-- (Old: `headProj_tailProj_of_le`.) -/
theorem headProj_tailProj_of_le {k n : ℕ} (hkn : k ≤ n) (h : S.H) :
    S.headProj k (S.tailProj n h) = 0 := by
  apply S.hcoord_ext
  intro m
  rw [S.hcoord_headProj_tailProj]
  have : m ∈ symmetricModes k → m ∈ symmetricModes n := by
    intro hm
    simp only [symmetricModes, Finset.mem_Icc] at hm ⊢
    omega
  by_cases h1 : m ∈ symmetricModes k
  · simp [h1, this h1]; rfl
  · simp [h1]; rfl

/-- (Old: `norm_tailProj_le`.) -/
theorem norm_tailProj_le (n : ℕ) (h : S.H) : ‖S.tailProj n h‖ ≤ 2 * ‖h‖ := by
  rw [S.tailProj_apply]
  calc ‖h - S.headProj n h‖ ≤ ‖h‖ + ‖S.headProj n h‖ := norm_sub_le _ _
    _ ≤ 2 * ‖h‖ := by linarith [S.norm_headProj_le n h]

/-- R5 for a tail-valued vector `g` (`P_n g = 0`): `‖i g‖ < ε/2` and `‖i (P_k g)‖ < ε/2` for
every `k`, provided `n` satisfies the R5 bound for the radius `D` with `ε/2`.
(Old: `small_of_tail`.) -/
theorem small_of_tail (ε D : ℝ) (n : ℕ)
    (hn : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < D →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2)
    (g : S.H) (hg : S.headProj n g = 0) (hgD : ‖g‖ < D) :
    ‖S.incl g‖ < ε / 2 ∧ ∀ k : ℕ, ‖S.incl (S.headProj k g)‖ < ε / 2 := by
  have h0 : ‖S.incl g‖ < ε / 2 / 2 := by
    have := hn n le_rfl g hgD
    rw [hg, map_zero, sub_zero] at this
    exact this
  refine ⟨by linarith [h0, norm_nonneg (S.incl g)], fun k => ?_⟩
  have hε : 0 < ε / 2 / 2 := lt_of_le_of_lt (norm_nonneg _) h0
  by_cases hk : k ≤ n
  · have : S.headProj k g = 0 := by
      have e : g = S.tailProj n g := by
        rw [S.tailProj_apply, hg, sub_zero]
      rw [e]; exact S.headProj_tailProj_of_le hk g
    rw [this, map_zero, norm_zero]; linarith
  · have hk' : n ≤ k := (not_le.1 hk).le
    have h1 := hn k hk' g hgD
    have e : S.incl (S.headProj k g) =
        S.incl g - (S.incl g - S.incl (S.headProj k g)) := by abel
    rw [e]
    calc _ ≤ ‖S.incl g‖ + ‖S.incl g - S.incl (S.headProj k g)‖ := norm_sub_le _ _
      _ < ε / 2 := by linarith

/-- `Step8Hyp` for a tail-valued continuous linear field `B : E → H` with `‖B ∘ i‖ ≤ r ≤ 1/2`.
(Old: `step8Hyp_of_tail`.) -/
theorem step8Hyp_of_tail (B : S.E →L[ℝ] S.H)
    (n : ℕ) (hB : ∀ y, S.headProj n (B y) = 0) (r : ℝ) (hr : r ≤ 1 / 2)
    (hBi : ∀ h : S.H, ‖B (S.incl h)‖ ≤ r * ‖h‖) (ε D : ℝ) (hε : 0 < ε)
    (hD : ∀ y : S.E, ‖y‖ ≤ ε → ‖B y‖ < D)
    (hn : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < D →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2) :
    S.Step8Hyp (fun y => B y) ε := by
  have hsm : ∀ y : S.E, ‖y‖ ≤ ε →
      ‖S.incl (B y)‖ < ε / 2 ∧ ∀ k : ℕ, ‖S.incl (S.headProj k (B y))‖ < ε / 2 :=
    fun y hy => S.small_of_tail ε D n hn (B y) (hB y) (hD y hy)
  refine ⟨B.contDiff, ⟨hε, fun y _ => B.differentiableAt, fun y hy => ?_, fun y _ => ?_⟩,
    fun k => ⟨hε, fun y _ => ((S.headProj k).comp B).differentiableAt, fun y hy => ?_,
      fun y _ => ?_⟩⟩
  · exact (hsm y (mem_closedBall_zero_iff.1 hy)).1
  · have e : fderiv ℝ (fun y => B y) y = B := B.fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => B y) y (S.incl h)‖ ≤ _
    rw [e]
    exact (hBi h).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  · exact (hsm y (mem_closedBall_zero_iff.1 hy)).2 k
  · have e : fderiv ℝ (fun y => S.headProj k (B y)) y = (S.headProj k).comp B :=
      ((S.headProj k).comp B).fderiv
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun h => ?_)
    show ‖fderiv ℝ (fun y => S.headProj k (B y)) y (S.incl h)‖ ≤ _
    rw [e]
    exact ((S.norm_headProj_le k _).trans (hBi h)).trans
      (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

/-- **Step 8 for `S = I + iA`**, `A = (I - P_n) K̃`: all hypotheses of `step8c` hold on `B̄_ε`,
hence (**) and null-set preservation on `B_{ε/2}`, stated with `ramerJac A`.
(Old: `linearSmall_step8_S`.) -/
theorem linearSmall_step8_S (K : S.E →L[ℝ] S.H)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2) :
    S.Step8Hyp (fun y => S.tailProj n (K y)) ε ∧
      S.Step8Concl (fun y => S.tailProj n (K y)) ε := by
  have hyp : S.Step8Hyp (fun y => S.tailProj n (K y)) ε := by
    refine S.step8Hyp_of_tail ((S.tailProj n).comp K) n
      (fun y => S.headProj_tailProj_of_le le_rfl _) (1 / 8) (by norm_num) hAi ε
      (3 * κ * ε + 1) hε (fun y hy => ?_) hn
    have h1 : ‖S.tailProj n (K y)‖ ≤ 2 * ‖K y‖ := S.norm_tailProj_le n _
    have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
    have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
    show ‖S.tailProj n (K y)‖ < _
    nlinarith
  exact ⟨hyp, S.step8Concl_of_hyp _ hyp⟩

/-- **Step 8 for `S⁻¹ = I + iM`**, `M = -A ∘ S⁻¹` (tail-valued, `‖M ∘ i‖ ≤ 1/7`).
(Old: `linearSmall_step8_Sinv`.) -/
theorem linearSmall_step8_Sinv
    (K : S.E →L[ℝ] S.H)
    (S' : S.E ≃L[ℝ] S.E)
    (M : S.E →L[ℝ] S.H)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖) (n : ℕ)
    (hAi : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖)
    (hSs : ∀ x, S'.symm x = x + S.incl (M x))
    (hM : ∀ x, M x = -(S.tailProj n (K (S'.symm x))))
    (hMi : ∀ h : S.H, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖)
    (ε : ℝ) (hε : 0 < ε)
    (hn : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2) :
    S.Step8Hyp (fun y => M y) ε ∧ S.Step8Concl (fun y => M y) ε := by
  have hyp : S.Step8Hyp (fun y => M y) ε := by
    refine S.step8Hyp_of_tail M n (fun y => ?_) ((1 / 8) / (1 - 1 / 8)) (by norm_num) hMi ε
      (3 * κ * ε + 1) hε (fun y hy => ?_) hn
    · rw [hM y, map_neg, S.headProj_tailProj_of_le le_rfl, neg_zero]
    · have e : M y = -(S.tailProj n (K y)) - S.tailProj n (K (S.incl (M y))) := by
        conv_lhs => rw [hM y, hSs y]
        rw [map_add, map_add]; abel
      have h1 : ‖S.tailProj n (K y)‖ ≤ 2 * ‖K y‖ := S.norm_tailProj_le n _
      have h2 : ‖K y‖ ≤ κ * ‖y‖ := hK y
      have h3 : κ * ‖y‖ ≤ κ * ε := mul_le_mul_of_nonneg_left hy hκ
      have h5 : ‖M y‖ ≤ ‖S.tailProj n (K y)‖ + (1 / 8) * ‖M y‖ := by
        calc ‖M y‖ ≤ ‖-(S.tailProj n (K y))‖ + ‖S.tailProj n (K (S.incl (M y)))‖ := by
              exact (congrArg norm e).le.trans (norm_sub_le _ _)
          _ ≤ _ := by rw [norm_neg]; linarith [hAi (M y)]
      nlinarith
  exact ⟨hyp, S.step8Concl_of_hyp _ hyp⟩

/-- **Combined form, with `n` enlarged.**  For `K̃ : E →L H` with `T = I + iK̃` invertible, and any
`ε > 0`, there is `n` (so large that the R5 tail bounds hold) with the D1 decomposition
`T̃ = Π ∘ S`, `S = I + iA`, `S⁻¹ = I + iM`, and Step 8 applies to `A` and to `M`.
(Old: `linearSmall_step8`.) -/
theorem linearSmall_step8
    (K : S.E →L[ℝ] S.H)
    (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (S' Pi : S.E ≃L[ℝ] S.E)
      (M : S.E →L[ℝ] S.H),
      (∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S' x = x + S.incl (S.tailProj n (K x))) ∧
      (∀ x, S'.symm x = x + S.incl (M x)) ∧
      (∀ x, M x = -(S.tailProj n (K (S'.symm x)))) ∧
      (∀ h : S.H, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S'.symm x)) ∧
      (∀ x, Pi x - x = S.incl (S.headProj n (K (S'.symm x)))) ∧
      (∀ x, S.SameTail n (Pi x) x) ∧
      S.Step8Hyp (fun y => S.tailProj n (K y)) ε ∧
      S.Step8Concl (fun y => S.tailProj n (K y)) ε ∧
      S.Step8Hyp (fun y => M y) ε ∧ S.Step8Concl (fun y => M y) ε := by
  obtain ⟨κ0, hκ0, hK0⟩ := K.bound
  set κ := max κ0 0 with hκdef
  have hκ : 0 ≤ κ := le_max_right _ _
  have hK : ∀ y, ‖K y‖ ≤ κ * ‖y‖ := fun y =>
    (hK0 y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ S.H
  have hi := S.incl_hs b
  obtain ⟨n₀, hn₀⟩ := Gen.exists_tail_small S (3 * κ * ε + 1) (ε / 2) (by linarith)
  obtain ⟨n, S', Pi, M, hnn, hAi', hS, hSs, hM, hMi, hPi, hPi2⟩ :=
    linear_decomposition_ge S.incl b hi K T hT (S.headProj)
      (fun n x => S.norm_headProj_le n x) S.headProj_tendsto
      (S.tailProj) (S.tailProj_apply) n₀
  have hAi : ∀ h : S.H, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖ := hAi'
  have hMi : ∀ h : S.H, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖ := hMi
  have hn' : ∀ m ≥ n, ∀ h : S.H, ‖h‖ < 3 * κ * ε + 1 →
      ‖S.incl h - S.incl (S.headProj m h)‖ < (ε / 2) / 2 :=
    fun m hm h hh => hn₀ m (le_trans hnn hm) h hh
  have hS' : ∀ x, S' x = x + S.incl (S.tailProj n (K x)) := hS
  have hM' : ∀ x, M x = -(S.tailProj n (K (S'.symm x))) := hM
  have h7 : ∀ x, Pi x - x = S.incl (S.headProj n (K (S'.symm x))) := hPi2
  have hfix : ∀ x, S.SameTail n (Pi x) x := by
    intro x m hm
    have e : S.coord m (Pi x - x) = 0 := by
      rw [h7 x]; exact S.coord_incl_headProj n (K (S'.symm x)) m hm
    rw [S.coord_sub] at e
    exact sub_eq_zero.1 e
  obtain ⟨hyA, hcA⟩ := S.linearSmall_step8_S K κ hκ hK n hAi ε hε hn'
  obtain ⟨hyM, hcM⟩ := S.linearSmall_step8_Sinv K S' M κ hκ hK n hAi hSs hM' hMi ε hε hn'
  exact ⟨n, S', Pi, M, hAi, hS', hSs, hM', hMi, hPi, h7, hfix, hyA, hcA,
    hyM, hcM⟩

end NlsGge.Ramer.General.RamerSetting
