import QuantumNLS.Local013ProductLimit
import QuantumNLS.PhaseQuotientBracket

/-!
# LOCAL-013 `reset:principal-calculus`, stage L4: the single-overlap commutator symbol
(`source-text/chapters/local/quantum_periods.tex:141-162`)

Source: "The single-overlap contraction has precisely the first Poisson bracket symbol. ... Thus
`−iN[Q(A),Q(B)]` has limiting symbol `2pq Im⟨α,β⟩ = {a,b}`. Homogeneity gives the identity at
arbitrary `v`, and decomposition into self-adjoint real and imaginary parts gives complex
bilinearity."

Route. On the unit sphere the identity is the uniqueness of the limit in the frozen accepted
`RootOverlapLimit.root_overlap_limit` (which contains the self-adjoint contraction computation
`2pq Im⟨α,β⟩ = {a,b}` and the real/imaginary decomposition): the same sequence
`−iN⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩` is expanded with the frozen LOCAL-011
fixed-degree commutator expansion (`genericU_commutator_eq_positiveOverlapExpansion`) and the
unit product expectation, and its limit is `−i pq ⟨u^{⊗n}, K_1^{[·,·]}(A,B) u^{⊗n}⟩`
(`N c_{N,p,q,1} → pq`, `N c_{N,p,q,s} → 0` for `s ≥ 2`). Homogeneity (proved here for both sides:
`kps_real_smul`, `pbC_homog`) extends it to every `v`.

Proved here (standard axioms only):
* `kps_real_smul`: `⟨(tw)^{⊗n}, K (tw)^{⊗n}⟩ = t^{2n} ⟨w^{⊗n}, K w^{⊗n}⟩` for real `t`.
* `fderiv_homog`, `gradient_homog`, `hamField_homog`, `pbR_homog`, `pbC_homog`: homogeneity of the
  DEF-015 bracket.
* `pbC_eq_commSymbol`: for `p, q ≥ 1`, every `v : H` and all bounded kernels,
  `{a, b}(v) = −i p q ⟨v^{⊗n}, K_1^{[·,·]}(A,B) v^{⊗n}⟩`, `n = p + q − 1`, where
  `K_1^{[·,·]} = overlapCommutatorKernel` is the frozen single-overlap commutator kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace BigOperators ComplexConjugate
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementProduct QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixAlignedTransport QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.SymplecticBracket QuantumNLS.Local013ProductLimit

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Local013PoissonSymbol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Homogeneity of the kernel symbols -/

theorem kps_real_smul {n : ℕ} (K : BoundedSymmetricKernel H n) (t : ℝ) (w : H) :
    kernelProductSymbol K (t • w) = ((t ^ (2 * n) : ℝ) : ℂ) * kernelProductSymbol K w := by
  set c : ℂ := (t : ℂ) with hc
  have hv : (t • w : H) = c • w := (Complex.coe_smul t w).symm
  have hpow : (htpow n (t • w) : HilbertTensorPower ℂ H n) = c ^ n • htpow n w := by
    rw [hv]; exact QuantumNLS.PhaseQuotientBracket.htpow_smul' n c w
  have hx : (⟨htpow n (t • w), htpow_mem_symSector n (t • w)⟩ : SymSector ℂ H n) =
      (c ^ n) • (⟨htpow n w, htpow_mem_symSector n w⟩ : SymSector ℂ H n) := Subtype.ext hpow
  have hcc : (starRingEnd ℂ) (c ^ n) * c ^ n = ((t ^ (2 * n) : ℝ) : ℂ) := by
    rw [map_pow, hc, Complex.conj_ofReal, ← mul_pow, pow_mul]
    push_cast
    ring
  have key : ∀ x y : HilbertTensorPower ℂ H n,
      ⟪(c ^ n) • x, (c ^ n) • y⟫_ℂ = ((t ^ (2 * n) : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
    intro x y
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hcc]
  unfold kernelProductSymbol
  rw [hx, map_smul, hpow]
  exact key (htpow n w) ((K ⟨htpow n w, htpow_mem_symSector n w⟩ : SymSector ℂ H n) :
    HilbertTensorPower ℂ H n)

theorem kps_re_smul {n : ℕ} (K : BoundedSymmetricKernel H n) (t : ℝ) (w : H) :
    (kernelProductSymbol K (t • w)).re = t ^ (2 * n) * (kernelProductSymbol K w).re := by
  rw [kps_real_smul, Complex.re_ofReal_mul]

theorem kps_im_smul {n : ℕ} (K : BoundedSymmetricKernel H n) (t : ℝ) (w : H) :
    (kernelProductSymbol K (t • w)).im = t ^ (2 * n) * (kernelProductSymbol K w).im := by
  rw [kps_real_smul, Complex.im_ofReal_mul]

/-! ### Homogeneity of the DEF-015 bracket -/

theorem fderiv_homog {F : H → ℝ} {k : ℕ} (hF : ∀ (t : ℝ) (w : H), F (t • w) = t ^ k * F w)
    {t : ℝ} (ht : t ≠ 0) {u : H} (hu : DifferentiableAt ℝ F u)
    (htu : DifferentiableAt ℝ F (t • u)) :
    fderiv ℝ F (t • u) = (t ^ k * t⁻¹) • fderiv ℝ F u := by
  have hcomp : (fun w => F (t • w)) = fun w => t ^ k * F w := funext (hF t)
  have hs : HasFDerivAt (fun w : H => t • w) (t • ContinuousLinearMap.id ℝ H) u :=
    (hasFDerivAt_id u).const_smul t
  have h1 : HasFDerivAt (fun w => F (t • w))
      ((fderiv ℝ F (t • u)).comp (t • ContinuousLinearMap.id ℝ H)) u :=
    htu.hasFDerivAt.comp u hs
  have h2 : HasFDerivAt (fun w => t ^ k * F w) ((t ^ k) • fderiv ℝ F u) u :=
    hu.hasFDerivAt.const_mul (t ^ k)
  rw [hcomp] at h1
  have heq := h1.unique h2
  ext h
  have key : fderiv ℝ F (t • u) h = t ^ k * fderiv ℝ F u (t⁻¹ • h) := by
    have := congrArg (fun L : H →L[ℝ] ℝ => L (t⁻¹ • h)) heq
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_inv_smul₀ ht, smul_eq_mul] using this
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul, key, map_smul, smul_eq_mul]
  ring

theorem gradient_homog {F : H → ℝ} {k : ℕ} (hF : ∀ (t : ℝ) (w : H), F (t • w) = t ^ k * F w)
    {t : ℝ} (ht : t ≠ 0) {u : H} (hu : DifferentiableAt ℝ F u)
    (htu : DifferentiableAt ℝ F (t • u)) :
    QuantumNLS.SymplecticBracket.gradient F (t • u) =
      (t ^ k * t⁻¹) • QuantumNLS.SymplecticBracket.gradient F u := by
  unfold QuantumNLS.SymplecticBracket.gradient
  rw [fderiv_homog hF ht hu htu, map_smul, smul_comm]

theorem hamField_homog {F : H → ℝ} {k : ℕ} (hF : ∀ (t : ℝ) (w : H), F (t • w) = t ^ k * F w)
    {t : ℝ} (ht : t ≠ 0) {u : H} (hu : DifferentiableAt ℝ F u)
    (htu : DifferentiableAt ℝ F (t • u)) :
    hamField F (t • u) = (t ^ k * t⁻¹) • hamField F u := by
  unfold hamField
  rw [gradient_homog hF ht hu htu, smul_comm]

theorem pbR_homog {F G : H → ℝ} {k l : ℕ}
    (hF : ∀ (t : ℝ) (w : H), F (t • w) = t ^ k * F w)
    (hG : ∀ (t : ℝ) (w : H), G (t • w) = t ^ l * G w)
    {t : ℝ} (ht : t ≠ 0) {u : H}
    (hFd : ∀ w, DifferentiableAt ℝ F w) (hGd : ∀ w, DifferentiableAt ℝ G w) :
    pbR F G (t • u) = (t ^ k * t⁻¹) * (t ^ l * t⁻¹) * pbR F G u := by
  unfold pbR
  rw [fderiv_homog hF ht (hFd u) (hFd _), hamField_homog hG ht (hGd u) (hGd _),
    ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem pbC_homog {F G : H → ℂ} {k l : ℕ}
    (hFr : ∀ (t : ℝ) (w : H), (F (t • w)).re = t ^ k * (F w).re)
    (hFi : ∀ (t : ℝ) (w : H), (F (t • w)).im = t ^ k * (F w).im)
    (hGr : ∀ (t : ℝ) (w : H), (G (t • w)).re = t ^ l * (G w).re)
    (hGi : ∀ (t : ℝ) (w : H), (G (t • w)).im = t ^ l * (G w).im)
    (hFrd : ∀ w, DifferentiableAt ℝ (fun v => (F v).re) w)
    (hFid : ∀ w, DifferentiableAt ℝ (fun v => (F v).im) w)
    (hGrd : ∀ w, DifferentiableAt ℝ (fun v => (G v).re) w)
    (hGid : ∀ w, DifferentiableAt ℝ (fun v => (G v).im) w)
    {t : ℝ} (ht : t ≠ 0) (u : H) :
    pbC F G (t • u) = (((t ^ k * t⁻¹) * (t ^ l * t⁻¹) : ℝ) : ℂ) * pbC F G u := by
  unfold pbC
  rw [pbR_homog hFr hGr ht hFrd hGrd, pbR_homog hFi hGi ht hFid hGid,
    pbR_homog hFi hGr ht hFid hGrd, pbR_homog hFr hGi ht hFrd hGid]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    ring

/-- `{a, b}` for two kernel symbols scales with `t^{2p-1} t^{2q-1}`. -/
theorem pbC_kps_homog {p q : ℕ} (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    {t : ℝ} (ht : t ≠ 0) (u : H) :
    pbC (kernelProductSymbol A) (kernelProductSymbol B) (t • u) =
      (((t ^ (2 * p) * t⁻¹) * (t ^ (2 * q) * t⁻¹) : ℝ) : ℂ) *
        pbC (kernelProductSymbol A) (kernelProductSymbol B) u :=
  pbC_homog (kps_re_smul A) (kps_im_smul A) (kps_re_smul B) (kps_im_smul B)
    (QuantumNLS.PhaseQuotientBracket.differentiableAt_kps_re A)
    (QuantumNLS.PhaseQuotientBracket.differentiableAt_kps_im A)
    (QuantumNLS.PhaseQuotientBracket.differentiableAt_kps_re B)
    (QuantumNLS.PhaseQuotientBracket.differentiableAt_kps_im B) ht u

/-! ### The identity on the unit sphere (uniqueness of the `root_overlap_limit` limit) -/

section Unit

variable {p q : ℕ}

/-- The overlap-`s` contribution `c_{N,p,q,s} ⟨u^{⊗n}, K_s^{[·,·]}(A,B) u^{⊗n}⟩` (zero unless
`1 ≤ s ≤ min p q`). -/
def gTerm (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (N s : ℕ) : ℂ :=
  if h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q then
    ((overlapCoefficient N p q s : ℝ) : ℂ) *
      kernelProductSymbol (overlapCommutatorKernel h.2.1 h.2.2 A B) u
  else 0

theorem ExN_eq (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (hu : ‖u‖ = 1) {N : ℕ} (hN : p + q ≤ N) (hpN : p ≤ N) (hqN : q ≤ N) :
    QuantumNLS.RootOverlapLimit.ExN N p q hpN hqN A B u =
      ∑ s ∈ range (min p q + 1), gTerm A B u N s := by
  unfold QuantumNLS.RootOverlapLimit.ExN QuantumNLS.RootOverlapLimit.CommQ
  rw [QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41.genericU_commutator_eq_positiveOverlapExpansion
    hpN hqN A B, _root_.sum_apply, Submodule.coe_sum, inner_sum]
  trans ∑ s : FeasibleOverlapIndex N p q, gTerm A B u N s.1.1
  · apply Finset.sum_congr rfl
    intro s _
    have hsp : s.1.1 ≤ p := le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _)
    have hsq : s.1.1 ≤ q := le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)
    unfold gTerm
    by_cases hs : 1 ≤ s.1.1
    · rw [dif_pos hs, dif_pos ⟨hs, hsp, hsq⟩, ContinuousLinearMap.smul_apply, Submodule.coe_smul,
        inner_smul_right, QuantumNLS.LocalPlacement.inner_genericU_N_r_product_of_unit _ _ _ _ u hu]
    · rw [dif_neg hs, dif_neg (fun h => hs h.1)]
      simp
  · apply sum_comp_inj (fun s : FeasibleOverlapIndex N p q => s.1.1)
    · intro a b hab
      exact Subtype.ext (Fin.ext hab)
    · intro s hs
      exact absurd (Finset.mem_range.mpr s.1.2) hs
    · intro n hn hnot
      exfalso
      have hn' := Finset.mem_range.mp hn
      have hnp : n ≤ p := le_trans (Nat.lt_succ_iff.mp hn') (min_le_left _ _)
      exact hnot ⟨⟨n, hn'⟩, by show unionSize p q n ≤ N; unfold unionSize; omega⟩ rfl

theorem limSeq_eq (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (hu : ‖u‖ = 1) {N : ℕ} (hN : p + q ≤ N) :
    QuantumNLS.RootOverlapLimit.limSeq p q A B u N =
      ∑ s ∈ range (min p q + 1), (-Complex.I) * (N : ℂ) * gTerm A B u N s := by
  have hpN : p ≤ N := by omega
  have hqN : q ≤ N := by omega
  unfold QuantumNLS.RootOverlapLimit.limSeq
  rw [dif_pos ⟨hpN, hqN⟩, ExN_eq A B u hu hN hpN hqN, Finset.mul_sum]

/-- The limit of the overlap-`s` contribution: only `s = 1` survives, with weight `p q`. -/
def gLim (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H) (s : ℕ) : ℂ :=
  if h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q then
    (if s = 1 then (-Complex.I) * (((p : ℝ) * q : ℝ) : ℂ) *
      kernelProductSymbol (overlapCommutatorKernel h.2.1 h.2.2 A B) u else 0)
  else 0

theorem tendsto_gTerm (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (s : ℕ) :
    Tendsto (fun N : ℕ => (-Complex.I) * (N : ℂ) * gTerm A B u N s) atTop
      (𝓝 (gLim A B u s)) := by
  unfold gTerm gLim
  by_cases h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q
  · simp only [dif_pos h]
    rcases eq_or_ne s 1 with hs1 | hs1
    · subst hs1
      rw [if_pos rfl]
      have hc : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q 1 : ℝ) : ℂ)) atTop
          (𝓝 (((p : ℝ) * q : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (QuantumNLS.OverlapMoments.tendsto_N_c_one p q)
      have ht := (hc.const_mul (-Complex.I)).mul_const
        (kernelProductSymbol (overlapCommutatorKernel h.2.1 h.2.2 A B) u)
      refine ht.congr (fun N => ?_)
      push_cast
      ring
    · rw [if_neg hs1]
      have hs2 : 2 ≤ s := by omega
      have hc : Tendsto (fun N : ℕ => (((N : ℝ) * overlapCoefficient N p q s : ℝ) : ℂ)) atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp
          (QuantumNLS.TerraMultiRound19ScaledTerms.scaled_multiple_overlap_limit p q s hs2 h.2.2)
      have ht := (hc.const_mul (-Complex.I)).mul_const
        (kernelProductSymbol (overlapCommutatorKernel h.2.1 h.2.2 A B) u)
      rw [Complex.ofReal_zero, mul_zero, zero_mul] at ht
      refine ht.congr (fun N => ?_)
      push_cast
      ring
  · simp only [dif_neg h, mul_zero]
    exact tendsto_const_nhds

theorem sum_gLim (hp : 1 ≤ p) (hq : 1 ≤ q) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) :
    ∑ s ∈ range (min p q + 1), gLim A B u s =
      (-Complex.I) * (((p : ℝ) * q : ℝ) : ℂ) *
        kernelProductSymbol (overlapCommutatorKernel hp hq A B) u := by
  rw [Finset.sum_eq_single 1]
  · unfold gLim
    rw [dif_pos ⟨le_refl 1, hp, hq⟩, if_pos rfl]
  · intro s _ hs
    unfold gLim
    by_cases h : 1 ≤ s ∧ s ≤ p ∧ s ≤ q
    · rw [dif_pos h, if_neg hs]
    · rw [dif_neg h]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (by have := le_min hp hq; omega))

/-- **The single-overlap symbol identity on the unit sphere.** -/
theorem pbC_eq_commSymbol_unit (hp : 1 ≤ p) (hq : 1 ≤ q) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : H) (hu : ‖u‖ = 1) :
    pbC (kernelProductSymbol A) (kernelProductSymbol B) u =
      (-Complex.I) * (((p : ℝ) * q : ℝ) : ℂ) *
        kernelProductSymbol (overlapCommutatorKernel hp hq A B) u := by
  have h1 := QuantumNLS.RootOverlapLimit.root_overlap_limit p q A B u hu
  have h2 : Tendsto (QuantumNLS.RootOverlapLimit.limSeq p q A B u) atTop
      (𝓝 ((-Complex.I) * (((p : ℝ) * q : ℝ) : ℂ) *
        kernelProductSymbol (overlapCommutatorKernel hp hq A B) u)) := by
    rw [← sum_gLim hp hq A B u]
    have hsum := tendsto_finset_sum (range (min p q + 1)) (fun s _ => tendsto_gTerm A B u s)
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (p + q)] with N hN
    exact (limSeq_eq A B u hu hN).symm
  exact tendsto_nhds_unique h1 h2

end Unit

/-! ### Every profile, by homogeneity -/

theorem exp_identity {t : ℝ} (ht : t ≠ 0) (p q : ℕ) (hq : 1 ≤ q) :
    (t ^ (2 * p) * t⁻¹) * (t ^ (2 * q) * t⁻¹) = t ^ (2 * unionSize p q 1) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  unfold unionSize
  rw [Nat.add_sub_cancel, show 2 * (q' + 1) = 2 * q' + 1 + 1 by ring, pow_succ, pow_succ,
    show 2 * (p + q') = 2 * p + 2 * q' by ring, pow_add]
  field_simp

theorem eq_zero_of_scale (z : ℂ) {n : ℕ} (hn : 1 ≤ n) (h : z = (((2 : ℝ) ^ (2 * n) : ℝ) : ℂ) * z) :
    z = 0 := by
  have hne : (((2 : ℝ) ^ (2 * n) : ℝ) : ℂ) ≠ 1 := by
    rw [Ne, ← Complex.ofReal_one, Complex.ofReal_inj]
    have : (2 : ℝ) ^ 2 ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this
    linarith
  have h2 : ((((2 : ℝ) ^ (2 * n) : ℝ) : ℂ) - 1) * z = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · exact h3

/-- **LOCAL-013, single-overlap Poisson identity** ("The single-overlap contraction has
precisely the first Poisson bracket symbol"): for `p, q ≥ 1`, all bounded kernels and EVERY
`v : H`, `{a, b}(v) = −i p q ⟨v^{⊗n}, K_1^{[·,·]}(A,B) v^{⊗n}⟩`, `n = p + q − 1`. -/
theorem pbC_eq_commSymbol {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (v : H) :
    pbC (kernelProductSymbol A) (kernelProductSymbol B) v =
      (-Complex.I) * (((p : ℝ) * q : ℝ) : ℂ) *
        kernelProductSymbol (overlapCommutatorKernel hp hq A B) v := by
  have hn : 1 ≤ unionSize p q 1 := by unfold unionSize; omega
  rcases eq_or_ne v 0 with rfl | hv
  · have hk : kernelProductSymbol (overlapCommutatorKernel hp hq A B) (0 : H) = 0 := by
      apply eq_zero_of_scale _ hn
      have := kps_real_smul (overlapCommutatorKernel hp hq A B) 2 (0 : H)
      rwa [smul_zero] at this
    have hb : pbC (kernelProductSymbol A) (kernelProductSymbol B) (0 : H) = 0 := by
      apply eq_zero_of_scale _ hn
      have := pbC_kps_homog A B (t := 2) two_ne_zero (0 : H)
      rwa [smul_zero, exp_identity two_ne_zero p q hq] at this
    rw [hk, hb, mul_zero]
  · set t : ℝ := ‖v‖ with htdef
    have ht : t ≠ 0 := norm_ne_zero_iff.mpr hv
    set u : H := t⁻¹ • v with hudef
    have hu : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, htdef, norm_norm, inv_mul_cancel₀ ht]
    have hv' : v = t • u := by rw [hudef, smul_inv_smul₀ ht]
    rw [hv', pbC_kps_homog A B ht u, kps_real_smul, pbC_eq_commSymbol_unit hp hq A B u hu,
      exp_identity ht p q hq]
    ring

end QuantumNLS.Local013PoissonSymbol

#print axioms QuantumNLS.Local013PoissonSymbol.kps_real_smul
#print axioms QuantumNLS.Local013PoissonSymbol.pbC_homog
#print axioms QuantumNLS.Local013PoissonSymbol.pbC_kps_homog
#print axioms QuantumNLS.Local013PoissonSymbol.ExN_eq
#print axioms QuantumNLS.Local013PoissonSymbol.tendsto_gTerm
#print axioms QuantumNLS.Local013PoissonSymbol.pbC_eq_commSymbol_unit
#print axioms QuantumNLS.Local013PoissonSymbol.pbC_eq_commSymbol
