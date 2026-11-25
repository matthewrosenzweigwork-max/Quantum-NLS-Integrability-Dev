import NlsGge.Ramer.RamerStep5
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Ramer.RamerDensity
import NlsGge.Ramer.SpaceTransfer
import NlsGge.Ramer.CylindricalChangeOfVariables

/-!
# Linear decomposition `T̃ = Π ∘ S` (Option D, D1)

See `LinearDecomposition.md`.  Part A: abstract Hilbert-space lemmas.  Part B: the concrete
instantiation `E = E_s`, `H = ActualCM c`, `P_n = cmTrunc`, and the fibre statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter
open scoped Topology

namespace NlsGge.Ramer

open NlsGge.Analysis.RegularizedDeterminant

section Abstract

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Operator norm is bounded by the square root of the sum of squared images of a basis. -/
theorem opNorm_le_sqrt_tsum {ι : Type*} (Q : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (hs : Summable fun p => ‖Q (b p)‖ ^ 2) :
    ‖Q‖ ≤ Real.sqrt (∑' p, ‖Q (b p)‖ ^ 2) := by
  set hQ := HilbertSchmidt.ofCLM Q (isHilbertSchmidt_of_summable b hs) with hQdef
  have htc : hQ.toCLM = Q := rfl
  have h1 := HilbertSchmidt.opNorm_le hQ
  rw [htc] at h1
  have h2 := (HilbertSchmidt.hasSum_basis_sq hQ b)
  simp only [htc] at h2
  have h3 : ‖hQ‖ = Real.sqrt (∑' p, ‖Q (b p)‖ ^ 2) := by
    rw [h2.tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  rw [← h3]; exact h1

/-- Item 1 (abstract): the tail `(I - P_n) B` of a Hilbert–Schmidt operator tends to `0` in
operator norm. -/
theorem tendsto_tail_opNorm {ι : Type*} (B : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (hB : Summable fun p => ‖B (b p)‖ ^ 2) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    Tendsto (fun n => ‖(ContinuousLinearMap.id ℝ H - P n).comp B‖) atTop (𝓝 0) := by
  set Q : ℕ → H →L[ℝ] H := fun n => (ContinuousLinearMap.id ℝ H - P n).comp B with hQ
  have hQb : ∀ n p, ‖Q n (b p)‖ ^ 2 ≤ 4 * ‖B (b p)‖ ^ 2 := by
    intro n p
    have : ‖Q n (b p)‖ ≤ 2 * ‖B (b p)‖ := by
      simp only [hQ, ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply]
      calc _ ≤ ‖B (b p)‖ + ‖P n (B (b p))‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hP n (B (b p))]
    calc ‖Q n (b p)‖ ^ 2 ≤ (2 * ‖B (b p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have hsum : ∀ n, Summable fun p => ‖Q n (b p)‖ ^ 2 := fun n =>
    Summable.of_nonneg_of_le (fun p => by positivity) (hQb n) (hB.mul_left 4)
  have hlim2 : Tendsto (fun n => ∑' p, ‖Q n (b p)‖ ^ 2) atTop (𝓝 (∑' p : ι, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (hB.mul_left 4) ?_
      (Eventually.of_forall fun n p => ?_)
    · intro p
      have h := ((hlim (B (b p))).const_sub (B (b p))).norm.pow 2
      simpa [hQ] using h
    · rw [Real.norm_of_nonneg (by positivity)]; exact hQb n p
  simp only [tsum_zero] at hlim2
  have hlim3 := (hlim2.sqrt)
  simp only [Real.sqrt_zero] at hlim3
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => opNorm_le_sqrt_tsum (Q n) b (hsum n))
    hlim3

/-- Item 1: eventually small tail. -/
theorem exists_tail_opNorm_lt {ι : Type*} (B : H →L[ℝ] H) (b : HilbertBasis ι ℝ H)
    (hB : Summable fun p => ‖B (b p)‖ ^ 2) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ‖(ContinuousLinearMap.id ℝ H - P n).comp B‖ < ε := by
  have := (tendsto_tail_opNorm B b hB P hP hlim).eventually (gt_mem_nhds hε)
  exact eventually_atTop.1 this


/-- Item 2 (abstract): if `‖A ∘ i‖ ≤ r < 1` then `S = I + i ∘ A` is invertible on `E` with
inverse `I + i ∘ M'`, `M' = -A ∘ S⁻¹`, and `‖M' ∘ i‖ ≤ r/(1-r)`. -/
theorem exists_neumann_equiv (i : H →L[ℝ] E) (A : E →L[ℝ] H) (r : ℝ)
    (hr : ‖A.comp i‖ ≤ r) (hr1 : r < 1) :
    ∃ (S : E ≃L[ℝ] E) (M : E →L[ℝ] H),
      (∀ x, S x = x + i (A x)) ∧ (∀ x, S.symm x = x + i (M x)) ∧
      (∀ x, M x = -A (S.symm x)) ∧ ‖M.comp i‖ ≤ r / (1 - r) := by
  set N : H →L[ℝ] H := A.comp i with hN
  have hn : ‖-N‖ < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hr hr1
  set u := Units.oneSub (-N) hn with hu
  set Q : H →L[ℝ] H := ↑u⁻¹ with hQ
  have hQ1 : Q * (1 + N) = 1 := by
    have h := u.inv_mul
    have h2 : (u : H →L[ℝ] H) = 1 + N := by simp [hu, Units.val_oneSub]
    rw [h2] at h; exact h
  have hQ2 : (1 + N) * Q = 1 := by
    have h := u.mul_inv
    have h2 : (u : H →L[ℝ] H) = 1 + N := by simp [hu, Units.val_oneSub]
    rw [h2] at h; exact h
  have hQ1' : ∀ h, Q h + Q (N h) = h := fun h => by
    have := congrArg (fun F : H →L[ℝ] H => F h) hQ1
    simpa using this
  have hQ2' : ∀ h, Q h + N (Q h) = h := fun h => by
    have := congrArg (fun F : H →L[ℝ] H => F h) hQ2
    simpa using this
  -- norm bound on Q
  have hQb : ∀ y, (1 - r) * ‖Q y‖ ≤ ‖y‖ := by
    intro y
    have h1 : Q y = y - N (Q y) := eq_sub_of_add_eq (hQ2' y)
    have h2 : ‖N (Q y)‖ ≤ r * ‖Q y‖ := by
      calc ‖N (Q y)‖ ≤ ‖N‖ * ‖Q y‖ := N.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    have h3 : ‖Q y‖ ≤ ‖y‖ + ‖N (Q y)‖ := by
      calc ‖Q y‖ = ‖y - N (Q y)‖ := by rw [← h1]
        _ ≤ ‖y‖ + ‖N (Q y)‖ := norm_sub_le _ _
    nlinarith
  set Sinv : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - i.comp (Q.comp A) with hSinv
  set S0 : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + i.comp A with hS0
  have hSi : ∀ x, S0 (Sinv x) = x := by
    intro x
    simp only [hSinv, hS0, sub_apply, add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    have h := hQ2' (A x)
    have : i (A x) - i (Q (A x)) - i (A (i (Q (A x)))) = 0 := by
      rw [← map_sub, ← map_sub]
      have : A (i (Q (A x))) = N (Q (A x)) := rfl
      rw [this]
      have h' : A x - Q (A x) - N (Q (A x)) = 0 := by rw [sub_sub]; exact sub_eq_zero.2 h.symm
      rw [h', map_zero]
    linear_combination (norm := abel) this
  have hSi' : ∀ x, Sinv (S0 x) = x := by
    intro x
    simp only [hSinv, hS0, sub_apply, add_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_add]
    have h := hQ1' (A x)
    have : i (A x) - i (Q (A x)) - i (Q (A (i (A x)))) = 0 := by
      rw [← map_sub, ← map_sub]
      have : A (i (A x)) = N (A x) := rfl
      rw [this]
      have h' : A x - Q (A x) - Q (N (A x)) = 0 := by rw [sub_sub]; exact sub_eq_zero.2 h.symm
      rw [h', map_zero]
    linear_combination (norm := abel) this
  refine ⟨ContinuousLinearEquiv.equivOfInverse S0 Sinv hSi' hSi, -(A.comp Sinv), ?_, ?_, ?_, ?_⟩
  · intro x; simp [hS0]
  · intro x
    have := hSi x
    simp only [hS0, add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at this
    show Sinv x = x + i (-(A (Sinv x)))
    rw [map_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq this
  · intro x; rfl
  · have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hr
    have hSiQ : ∀ h, Sinv (i h) = i (Q h) := by
      intro h
      simp only [hSinv, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
      rw [← map_sub]
      congr 1
      have := hQ1' h
      change h - Q (N h) = Q h
      exact sub_eq_iff_eq_add.2 this.symm
    refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hr0 (by linarith)) (fun h => ?_)
    have e : (-(A.comp Sinv)).comp i h = -N (Q h) := by
      simp [hSiQ, hN]
    rw [e, norm_neg]
    have h1 : ‖N (Q h)‖ ≤ r * ‖Q h‖ :=
      (N.le_opNorm _).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
    have h2 := hQb h
    have h3 : ‖Q h‖ ≤ ‖h‖ / (1 - r) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    calc ‖N (Q h)‖ ≤ r * ‖Q h‖ := h1
      _ ≤ r * (‖h‖ / (1 - r)) := mul_le_mul_of_nonneg_left h3 hr0
      _ = _ := by ring


/-- **Linear decomposition (abstract form).**  For `K : E → H` with `T x = x + i (K x)` a
continuous linear automorphism of `E`, and `i` Hilbert–Schmidt, there is `n` such that, with
`A = (I - P_n) K`, `S = I + i A` is invertible with `S⁻¹ = I + i M'`,
`‖(I-P_n) K i‖ < 1/8`, `‖M' i‖ ≤ (1/8)/(1-1/8)`, and `Π := T ∘ S⁻¹` satisfies
`Π x - x = i (P_n (K (S⁻¹ x)))`. -/
theorem linear_decomposition {ι : Type*} (i : H →L[ℝ] E) (b : HilbertBasis ι ℝ H)
    (hi : Summable fun p => ‖i (b p)‖ ^ 2) (K : E →L[ℝ] H) (T : E ≃L[ℝ] E)
    (hT : ∀ x, T x = x + i (K x)) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (R : ℕ → H →L[ℝ] H) (hR : ∀ n x, R n x = x - P n x) :
    ∃ (n : ℕ) (S Pi : E ≃L[ℝ] E) (M : E →L[ℝ] H),
      ‖((R n).comp K).comp i‖ < 1 / 8 ∧
      (∀ h, ‖((R n).comp K) (i h)‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + i (((R n).comp K) x)) ∧
      (∀ x, S.symm x = x + i (M x)) ∧
      (∀ x, M x = -(((R n).comp K) (S.symm x))) ∧
      ‖M.comp i‖ ≤ (1 / 8) / (1 - 1 / 8) ∧
      (∀ h, ‖M (i h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = i (P n (K (S.symm x)))) := by
  have hB := (hs_comp_left i b hi K).1
  obtain ⟨N, hN⟩ := exists_tail_opNorm_lt (K.comp i) b hB P hP hlim (1 / 8) (by norm_num)
  have hlt := hN N le_rfl
  have hRe : R N = ContinuousLinearMap.id ℝ H - P N := by
    ext x; simp [hR]
  have hA : ((R N).comp K).comp i = (R N).comp (K.comp i) := rfl
  rw [hRe] at hA
  rw [← hA, ← hRe] at hlt
  obtain ⟨S, M, hS, hSs, hM, hMn⟩ :=
    exists_neumann_equiv i ((R N).comp K) (1 / 8) hlt.le (by norm_num)
  refine ⟨N, S, S.symm.trans T, M, hlt,
    fun h => ((((R N).comp K).comp i).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg _)),
    hS, hSs, hM, hMn, fun h => ((M.comp i).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hMn (norm_nonneg _)), fun x => rfl, fun x => ?_⟩
  have h1 : (S.symm.trans T) x = T (S.symm x) := rfl
  rw [h1, hT]
  have := hS (S.symm x)
  rw [S.apply_symm_apply] at this
  generalize S.symm x = y at this ⊢
  rw [this]
  simp only [ContinuousLinearMap.comp_apply, hR, map_sub]
  abel

end Abstract


section Concrete

variable {lower upper : ℝ}
open NlsGge.Pilot

/-- The coordinate projection `P_n : H → H` onto the head, as an endomorphism of `H`. -/
def headProj (c : BoundedCoefficients lower upper) (n : ℕ) : ActualCM c →L[ℝ] ActualCM c :=
  LinearMap.mkContinuous
    { toFun := fun h => ((cmTrunc c n h : actualCMHead c n) : ActualCM c)
      map_add' := fun x y => by simp
      map_smul' := fun r x => congrArg Subtype.val ((cmTrunc c n).map_smul r x) }
    1 (fun x => by rw [one_mul]; exact norm_cmTrunc_le c n x)

theorem headProj_apply (c : BoundedCoefficients lower upper) (n : ℕ) (h : ActualCM c) :
    headProj c n h = ((cmTrunc c n h : actualCMHead c n) : ActualCM c) := rfl


theorem headProj_tendsto (c : BoundedCoefficients lower upper) (h : ActualCM c) :
    Tendsto (fun n : ℕ => headProj c n h) atTop (𝓝 h) := by
  have := tendsto_cmTrunc_comp c 0 (fun _ => h) continuous_const (fun _ => 0) 0 tendsto_const_nhds
  exact this

/-- Two points of `E_s` lie in the same fibre of the head/tail decomposition at level `n`
iff their tail coordinates (modes `∉ symmetricModes n`) agree. -/
def SameTail (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℕ)
    (x y : FullWeightedHilbert c s) : Prop :=
  ∀ m ∉ symmetricModes n, coordE c s x m = coordE c s y m

theorem coordE_sub (c : BoundedCoefficients lower upper) (s : ℝ) (x y : FullWeightedHilbert c s)
    (m : ℤ) : coordE c s (x - y) m = coordE c s x m - coordE c s y m := rfl

theorem coordE_add (c : BoundedCoefficients lower upper) (s : ℝ) (x y : FullWeightedHilbert c s)
    (m : ℤ) : coordE c s (x + y) m = coordE c s x m + coordE c s y m := rfl

/-- The image of a head vector in `E_s` has vanishing tail coordinates. -/
theorem coordE_incl_headProj (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n : ℕ) (h : ActualCM c) (m : ℤ) (hm : m ∉ symmetricModes n) :
    coordE c s (cmToFullWeightedHilbert c s hs0 (headProj c n h)) m = 0 := by
  have h1 := cmCoord_cmTrunc c n h m
  have h2 : cmCoord ((cmTrunc c n h : actualCMHead c n) : ActualCM c) m = 0 := by
    rw [h1]; simp [hm]
  exact h2

/-- A bijection of `E` that fixes tail coordinates is a bijection of every fibre. -/
theorem bijOn_fibre (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℕ)
    (Pi : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hfix : ∀ x, SameTail c s n (Pi x) x) (x₀ : FullWeightedHilbert c s) :
    Set.BijOn Pi {x | SameTail c s n x x₀} {x | SameTail c s n x x₀} := by
  refine ⟨fun x hx m hm => ?_, Pi.injective.injOn, fun y hy => ?_⟩
  · exact (hfix x m hm).trans (hx m hm)
  · refine ⟨Pi.symm y, fun m hm => ?_, Pi.apply_symm_apply y⟩
    have := hfix (Pi.symm y) m hm
    rw [Pi.apply_symm_apply] at this
    exact this.symm.trans (hy m hm)

/-- The complementary tail projection `I - P_n` on `H`. -/
def tailProj (c : BoundedCoefficients lower upper) (n : ℕ) : ActualCM c →L[ℝ] ActualCM c :=
  LinearMap.mkContinuous
    { toFun := fun h => h - headProj c n h
      map_add' := fun x y => by rw [map_add]; abel
      map_smul' := fun r x => by rw [map_smul, smul_sub]; rfl }
    2 (fun x => by
      calc ‖x - headProj c n x‖ ≤ ‖x‖ + ‖headProj c n x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖x‖ := by
          have : ‖((cmTrunc c n x : actualCMHead c n) : ActualCM c)‖ ≤ ‖x‖ :=
            norm_cmTrunc_le c n x
          rw [headProj_apply]; linarith)

theorem tailProj_apply (c : BoundedCoefficients lower upper) (n : ℕ) (h : ActualCM c) :
    tailProj c n h = h - headProj c n h := rfl

/-- **Linear decomposition for the actual spaces.**  `E = E_s` (`1/2 < s`), `H = ActualCM c`,
`i = cmToFullWeightedHilbert`, `P_n = headProj c n`, `I - P_n = tailProj c n`.  (Operator-norm
bounds are stated pointwise, because of the `RestrictScalars` instance diamond on `ActualCM`.) -/
theorem linear_decomposition_cm (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s →L[ℝ] ActualCM c)
    (T : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
    (hT : ∀ x, T x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (K x)) :
    ∃ (n : ℕ) (S Pi : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
      (M : FullWeightedHilbert c s →L[ℝ] ActualCM c),
      (∀ h, ‖tailProj c n (K (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h))‖
          ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
          (tailProj c n (K x))) ∧
      (∀ x, S.symm x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (M x)) ∧
      (∀ x, M x = -(tailProj c n (K (S.symm x)))) ∧
      (∀ h, ‖M (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h)‖ ≤
          ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S.symm x)) ∧
      (∀ x, Pi x - x = cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
          (headProj c n (K (S.symm x)))) ∧
      (∀ x, ∃ v : actualCMHead c n, Pi x - x =
          cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (v : ActualCM c)) ∧
      (∀ x, SameTail c s n (Pi x) x) ∧
      (∀ x₀, Set.BijOn Pi {x | SameTail c s n x x₀} {x | SameTail c s n x x₀}) := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : 0 < s)
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ (ActualCM c)
  have hi := cmToFullWeightedHilbert_hs c s hs b
  obtain ⟨n, S, Pi, M, -, h1, h2, h3, h4, -, h5, h6, h7⟩ :=
    linear_decomposition (cmToFullWeightedHilbert c s hs0) b hi K T hT (headProj c)
      (fun n x => norm_cmTrunc_le c n x) (headProj_tendsto c)
      (tailProj c) (tailProj_apply c)
  have hfix : ∀ x, SameTail c s n (Pi x) x := by
    intro x m hm
    have e : coordE c s (Pi x - x) m = 0 := by
      rw [h7 x]; exact coordE_incl_headProj c s hs0 n (K (S.symm x)) m hm
    rw [coordE_sub] at e
    exact sub_eq_zero.1 e
  exact ⟨n, S, Pi, M, h1, h2, h3, h4, h5, h6, h7,
    fun x => ⟨cmTrunc c n (K (S.symm x)), h7 x⟩, hfix, bijOn_fibre c s n Pi hfix⟩

end Concrete

end NlsGge.Ramer
