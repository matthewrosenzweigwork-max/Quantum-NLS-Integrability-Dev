import NlsGge.Ramer.General.RamerStep5G
import NlsGge.Ramer.General.TruncatedFieldConvergenceG
import NlsGge.Ramer.General.HypothesisBridgeG
import NlsGge.Ramer.General.SpaceTransferG
import NlsGge.Ramer.General.CylindricalChangeOfVariablesG
import NlsGge.Hierarchy.RiccatiWeightedRealProjectionTendstoPrerequisite

/-!
# Linear decomposition `T̃ = Π ∘ S`, generalized (GD3)

Generalization of `NlsGge/Ramer/LinearDecomposition.lean` to an arbitrary `RamerSetting`.
Part A (abstract Hilbert-space lemmas, generic) is copied into `NlsGge.Ramer.Gen`.  Part B is the
concrete instantiation `E = S.E`, `H = S.H`, `P_n = S.headProj n`, `i = S.incl`.

Anisotropy check: the tail operator-norm bounds use only `H`-norms (`‖P_n‖ ≤ 1` on `H`,
`P_n → id` strongly on `H`, and Hilbert–Schmidt-ness of `i`).  The constants `1/8` and `1/7`
are unchanged; no isotropy of `E` is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Filter
open scoped Topology

namespace NlsGge.Ramer.Gen

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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer.Gen
variable (S : RamerSetting)

theorem coord_sub (x y : S.E) (m : ℤ) : S.coord m (x - y) = S.coord m x - S.coord m y :=
  map_sub (S.coord m) x y

theorem norm_headProj_le (n : ℕ) (x : S.H) : ‖S.headProj n x‖ ≤ ‖x‖ :=
  weightedRealProjection_norm_le S.cmWeight (symmetricModes n) x

theorem headProj_tendsto (h : S.H) :
    Tendsto (fun n : ℕ => S.headProj n h) atTop (𝓝 h) :=
  weightedRealProjection_tendsto_actual (w := S.cmWeight) h

/-- Two points of `E` lie in the same fibre of the head/tail decomposition at level `n`
iff their tail coordinates (modes `∉ symmetricModes n`) agree. -/
def SameTail (n : ℕ) (x y : S.E) : Prop :=
  ∀ m ∉ symmetricModes n, S.coord m x = S.coord m y

/-- The image of a head vector in `E` has vanishing tail coordinates. -/
theorem coord_incl_headProj (n : ℕ) (h : S.H) (m : ℤ) (hm : m ∉ symmetricModes n) :
    S.coord m (S.incl (S.headProj n h)) = 0 := by
  rw [S.coord_incl, S.hcoord_headProj]; simp [hm]

/-- A bijection of `E` that fixes tail coordinates is a bijection of every fibre. -/
theorem bijOn_fibre (n : ℕ) (Pi : S.E ≃L[ℝ] S.E)
    (hfix : ∀ x, S.SameTail n (Pi x) x) (x₀ : S.E) :
    Set.BijOn Pi {x | S.SameTail n x x₀} {x | S.SameTail n x x₀} := by
  refine ⟨fun x hx m hm => ?_, Pi.injective.injOn, fun y hy => ?_⟩
  · exact (hfix x m hm).trans (hx m hm)
  · refine ⟨Pi.symm y, fun m hm => ?_, Pi.apply_symm_apply y⟩
    have := hfix (Pi.symm y) m hm
    rw [Pi.apply_symm_apply] at this
    exact this.symm.trans (hy m hm)

/-- The complementary tail projection `I - P_n` on `H`. -/
def tailProj (n : ℕ) : S.H →L[ℝ] S.H :=
  LinearMap.mkContinuous
    { toFun := fun h => h - S.headProj n h
      map_add' := fun x y => by rw [map_add]; abel
      map_smul' := fun r x => by rw [map_smul, smul_sub]; rfl }
    2 (fun x => by
      calc ‖x - S.headProj n x‖ ≤ ‖x‖ + ‖S.headProj n x‖ := norm_sub_le _ _
        _ ≤ 2 * ‖x‖ := by linarith [S.norm_headProj_le n x])

theorem tailProj_apply (n : ℕ) (h : S.H) : S.tailProj n h = h - S.headProj n h := rfl

/-- **Linear decomposition for a `RamerSetting`.**  `E = S.E`, `H = S.H`, `i = S.incl`,
`P_n = S.headProj n`, `I - P_n = S.tailProj n`. -/
theorem linear_decomposition_cm (K : S.E →L[ℝ] S.H) (T : S.E ≃L[ℝ] S.E)
    (hT : ∀ x, T x = x + S.incl (K x)) :
    ∃ (n : ℕ) (S' Pi : S.E ≃L[ℝ] S.E) (M : S.E →L[ℝ] S.H),
      (∀ h, ‖S.tailProj n (K (S.incl h))‖ ≤ (1 / 8) * ‖h‖) ∧
      (∀ x, S' x = x + S.incl (S.tailProj n (K x))) ∧
      (∀ x, S'.symm x = x + S.incl (M x)) ∧
      (∀ x, M x = -(S.tailProj n (K (S'.symm x)))) ∧
      (∀ h, ‖M (S.incl h)‖ ≤ ((1 / 8) / (1 - 1 / 8)) * ‖h‖) ∧
      (∀ x, Pi x = T (S'.symm x)) ∧
      (∀ x, Pi x - x = S.incl (S.headProj n (K (S'.symm x)))) ∧
      (∀ x, ∃ v : S.head n, Pi x - x = S.incl (v : S.H)) ∧
      (∀ x, S.SameTail n (Pi x) x) ∧
      (∀ x₀, Set.BijOn Pi {x | S.SameTail n x x₀} {x | S.SameTail n x x₀}) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ S.H
  have hi := S.incl_hs b
  obtain ⟨n, S', Pi, M, -, h1, h2, h3, h4, -, h5, h6, h7⟩ :=
    linear_decomposition S.incl b hi K T hT (S.headProj) (fun n x => S.norm_headProj_le n x)
      S.headProj_tendsto S.tailProj S.tailProj_apply
  have hfix : ∀ x, S.SameTail n (Pi x) x := by
    intro x m hm
    have e : S.coord m (Pi x - x) = 0 := by
      rw [h7 x]; exact S.coord_incl_headProj n (K (S'.symm x)) m hm
    rw [S.coord_sub] at e
    exact sub_eq_zero.1 e
  exact ⟨n, S', Pi, M, h1, h2, h3, h4, h5, h6, h7,
    fun x => ⟨⟨S.headProj n (K (S'.symm x)), S.headProj_mem_head _ _⟩, h7 x⟩, hfix, S.bijOn_fibre n Pi hfix⟩

end NlsGge.Ramer.General.RamerSetting
