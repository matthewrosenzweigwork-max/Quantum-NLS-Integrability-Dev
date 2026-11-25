import QuantumNLS.RootComplexInterchange
import QuantumNLS.RootBracketScalars
import QuantumNLS.RootSymbolFrechet
import QuantumNLS.RootInvolutionLimit
import QuantumNLS.RootInvolutionConj

/-!
# R-C4F43CA8 `thm:root-involution`, part (2C-b2): the four real zero brackets of the product symbols

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` (the conclusion: all real and imaginary parts of
`s_z`, `s_w` have zero reduced Poisson bracket, from `{s_z,s_w} = 0` and `{s_z, s̄_w} = 0`).

Realized inputs (frozen): `RootComplexInterchange.pbC_hasSum_tsum`, `RootBracketScalars` (constants, real scalars),
`RootSymbolFrechet` (`symFun`, `physA`, `physW`, `symbolTerm_eq_symFun`, `contDiff_symFun'`, `norm_fderiv_symFun_le`,
`summable_bound`), `RootInvolutionLimit.double_limit_zero`, `RootInvolutionConj.double_limit_conj_symbol`,
`kernelProductSymbol_adjoint`, `summable_aux2`, accepted `root_overlap_limit`, `norm_limSeq_le`.

Proved here (standard axioms only):
* `radius_exists`: a radius `ρ` with `κ(1+ρ)² < min(Im z, Im w)`.
* `kps_eq_symFun`, `symFun_norm_le`, and differentiability of the real and imaginary parts of `kernelProductSymbol`.
* `series_data`: derivatives, bounds and pointwise summability of the symbol series on a ball.
* `norm_pbC_kps_le`: `‖pbC (kps A) (kps B) u‖ ≤ 2pq‖A‖‖B‖` (limit of the N-uniform bound).
* `bracket_A`: `pbC (productSymbol · z) (productSymbol · w) u = 0`.
* `bracket_B`: `pbC (productSymbol · z) (conj ∘ productSymbol · w) u = 0`.
* `real_zero_brackets`: the four real brackets `{Re s_z,Re s_w}`, `{Im s_z,Im s_w}`, `{Im s_z,Re s_w}`, `{Re s_z,Im s_w}` vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootSymbolBrackets

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.NormalizedTransfer QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator
  QuantumNLS.RootInvolutionLimit QuantumNLS.RootInvolutionConj QuantumNLS.RootSymbolFrechet
  QuantumNLS.RootComplexInterchange QuantumNLS.RootBracketScalars QuantumNLS.SymplecticBracket
  QuantumNLS.RootPlacementBound QuantumNLS.TensorPlacements QuantumNLS.HighMomentsRank

variable (L : ℝ) [Fact (0 < L)]

theorem radius_exists (κ a b : ℝ) (hκ : 0 < κ) (ha : κ < a) (hb : κ < b) :
    ∃ ρ : ℝ, 0 < ρ ∧ κ * (1 + ρ) ^ 2 < a ∧ κ * (1 + ρ) ^ 2 < b := by
  set δ := min (a - κ) (b - κ) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδa : δ ≤ a - κ := min_le_left _ _
  have hδb : δ ≤ b - κ := min_le_right _ _
  set ρ := min 1 (δ / (4 * κ + 4)) with hρdef
  have hρ0 : 0 < ρ := lt_min one_pos (div_pos hδ (by linarith))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρδ : ρ ≤ δ / (4 * κ + 4) := min_le_right _ _
  have hρδ' : ρ * (4 * κ + 4) ≤ δ := (le_div_iff₀ (by linarith)).mp hρδ
  have h2 : 4 * κ * ρ ≤ δ := by nlinarith
  have hsq : ρ ^ 2 ≤ ρ := by nlinarith
  have h1 : κ * (1 + ρ) ^ 2 ≤ κ + 3 * κ * ρ := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hκ.le]
  refine ⟨ρ, hρ0, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem kps_eq_symFun (z : ℂ) (j : ℕ) (u : L2T L) :
    kernelProductSymbol (orderedKernel L (j + 1) z) u = symFun (j + 1) (physA L z j) u := by
  unfold symFun kernelProductSymbol physA
  rw [extend_htpow]
  rfl

theorem symFun_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (n : ℕ) (A : HilbertTensorPower ℂ E n →L[ℂ] HilbertTensorPower ℂ E n) (y : E) :
    ‖symFun n A y‖ ≤ ‖A‖ * ‖y‖ ^ n * ‖y‖ ^ n := by
  unfold symFun
  set x : HilbertTensorPower ℂ E n := (htpow n y : HilbertTensorPower ℂ E n) with hx
  have hxn : ‖x‖ = ‖y‖ ^ n := norm_htpow n y
  have hAx : ‖A x‖ ≤ ‖A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  calc ‖⟪x, A x⟫_ℂ‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left hAx (norm_nonneg _)
    _ = ‖A‖ * ‖y‖ ^ n * ‖y‖ ^ n := by rw [hxn]; ring

theorem re_diffAt {f : L2T L → ℂ} {u : L2T L} (h : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun v => (f v).re) u :=
  (Complex.reCLM.hasFDerivAt.comp u h.hasFDerivAt).differentiableAt

theorem im_diffAt {f : L2T L → ℂ} {u : L2T L} (h : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun v => (f v).im) u :=
  (Complex.imCLM.hasFDerivAt.comp u h.hasFDerivAt).differentiableAt

theorem symFun_differentiableAt (j : ℕ) (z : ℂ) (u : L2T L) :
    DifferentiableAt ℝ (symFun (j + 1) (physA L z j)) u :=
  ((contDiff_symFun' (j + 1) (physA L z j)).differentiable one_ne_zero) u

theorem kps_re_im_diff (z : ℂ) (j : ℕ) (u : L2T L) :
    DifferentiableAt ℝ (fun v => (kernelProductSymbol (orderedKernel L (j + 1) z) v).re) u ∧
      DifferentiableAt ℝ (fun v => (kernelProductSymbol (orderedKernel L (j + 1) z) v).im) u := by
  simp only [kps_eq_symFun L z j]
  exact ⟨re_diffAt L (symFun_differentiableAt L j z u), im_diffAt L (symFun_differentiableAt L j z u)⟩

theorem physA_norm_le (z : ℂ) (hη : 0 < z.im) (j : ℕ) :
    ‖physA L z j‖ ≤ 2 * (z.im)⁻¹ ^ (j + 1) :=
  (norm_extendSymKernel_le _).trans (norm_physicalKernel_le (L := L) (by omega) z hη)

theorem physW_norm (κ : ℝ) (hκ : 0 ≤ κ) (j : ℕ) : ‖physW κ j‖ = κ ^ (j + 1) := by
  unfold physW
  rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ _)]

/-- The key scalar estimate `κ^{j+1} ‖A_j‖ R^{2(j+1)} ≤ 2 q^{j+1}`, `q = κR²/Im z`. -/
theorem key_scalar (κ : ℝ) (hκ : 0 ≤ κ) (z : ℂ) (hη : 0 < z.im) (R : ℝ) (hR : 0 ≤ R) (j : ℕ) :
    κ ^ (j + 1) * (‖physA L z j‖ * R ^ (j + 1) * R ^ (j + 1)) ≤ 2 * (κ * R ^ 2 / z.im) ^ (j + 1) := by
  have hA := physA_norm_le L z hη j
  have hRpow : 0 ≤ R ^ (j + 1) := pow_nonneg hR _
  calc κ ^ (j + 1) * (‖physA L z j‖ * R ^ (j + 1) * R ^ (j + 1))
      ≤ κ ^ (j + 1) * (2 * (z.im)⁻¹ ^ (j + 1) * R ^ (j + 1) * R ^ (j + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκ _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hRpow) hRpow
    _ = 2 * (κ * R ^ 2 / z.im) ^ (j + 1) := by
        rw [div_eq_mul_inv]; ring

/-- Summable majorant and derivative/value data for the symbol series `F_n(y) = symbolTerm y z (n+1)` on a ball. -/
theorem series_data (κ : ℝ) (hκ : 0 ≤ κ) (z : ℂ) (hη : 0 < z.im) (u : L2T L) (ρ R : ℝ)
    (hR : 0 < R) (hball : ∀ x ∈ ball u ρ, ‖x‖ ≤ R) (hq : κ * R ^ 2 < z.im) :
    ∃ a : ℕ → ℝ, Summable a ∧
      (∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => symbolTerm L κ y z (n + 1))
        (physW κ n • fderiv ℝ (symFun (n + 1) (physA L z n)) x) x) ∧
      (∀ n, ∀ x ∈ ball u ρ, ‖physW κ n • fderiv ℝ (symFun (n + 1) (physA L z n)) x‖ ≤ a n) ∧
      (∀ y ∈ ball u ρ, Summable fun n => symbolTerm L κ y z (n + 1)) := by
  have hR0 : 0 ≤ R := hR.le
  have hRp : ∀ k : ℕ, 0 ≤ R ^ k := fun k => pow_nonneg hR0 k
  have hq0 : 0 ≤ κ * R ^ 2 / z.im := div_nonneg (mul_nonneg hκ (sq_nonneg _)) hη.le
  have hq1 : κ * R ^ 2 / z.im < 1 := (div_lt_one hη).mpr hq
  set q := κ * R ^ 2 / z.im with hqdef
  set a : ℕ → ℝ := fun n => (2 + 4 * ((n : ℝ) + 1) / R) * q ^ (n + 1) with ha_def
  have hsa : Summable a := summable_bound q R hq0 hq1
  have hkey : ∀ n, κ ^ (n + 1) * (‖physA L z n‖ * R ^ (n + 1) * R ^ (n + 1)) ≤ 2 * q ^ (n + 1) :=
    fun n => key_scalar L κ hκ z hη R hR0 n
  have hpos4 : ∀ n : ℕ, 2 * q ^ (n + 1) ≤ a n := by
    intro n
    have h0 : 0 ≤ 4 * ((n : ℝ) + 1) / R * q ^ (n + 1) :=
      mul_nonneg (div_nonneg (by positivity) hR0) (pow_nonneg hq0 _)
    have e : a n = 2 * q ^ (n + 1) + 4 * ((n : ℝ) + 1) / R * q ^ (n + 1) := by
      simp only [ha_def]; ring
    rw [e]; linarith
  refine ⟨a, hsa, ?_, ?_, ?_⟩
  · intro n x _hx
    have hd : HasFDerivAt (symFun (n + 1) (physA L z n))
        (fderiv ℝ (symFun (n + 1) (physA L z n)) x) x :=
      (symFun_differentiableAt L n z x).hasFDerivAt
    have hc : HasFDerivAt (fun y => (physW κ n) * symFun (n + 1) (physA L z n) y)
        ((physW κ n) • fderiv ℝ (symFun (n + 1) (physA L z n)) x) x := hd.const_mul (physW κ n)
    have hfun : (fun y => symbolTerm L κ y z (n + 1)) =
        fun y => (physW κ n) * symFun (n + 1) (physA L z n) y :=
      funext fun y => symbolTerm_eq_symFun L κ z n y
    rw [hfun]
    exact hc
  · intro n x hx
    have hxR : ‖x‖ ≤ R := hball x hx
    have hD := norm_fderiv_symFun_le n (physA L z n) x
    rw [norm_smul, physW_norm κ hκ n]
    have hXX : ‖x‖ ^ (n + 1) * ‖x‖ ^ n ≤ R ^ (n + 1) * R ^ n :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxR _) (pow_le_pow_left₀ (norm_nonneg _) hxR _)
        (pow_nonneg (norm_nonneg _) _) (hRp _)
    have step1 : κ ^ (n + 1) * ‖fderiv ℝ (symFun (n + 1) (physA L z n)) x‖ ≤
        κ ^ (n + 1) * (2 * ((n : ℝ) + 1) * ‖physA L z n‖ * (R ^ (n + 1) * R ^ n)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκ _)
      calc ‖fderiv ℝ (symFun (n + 1) (physA L z n)) x‖
          ≤ 2 * ((n : ℝ) + 1) * ‖physA L z n‖ * ‖x‖ ^ (n + 1) * ‖x‖ ^ n := hD
        _ = 2 * ((n : ℝ) + 1) * ‖physA L z n‖ * (‖x‖ ^ (n + 1) * ‖x‖ ^ n) := by ring
        _ ≤ 2 * ((n : ℝ) + 1) * ‖physA L z n‖ * (R ^ (n + 1) * R ^ n) :=
          mul_le_mul_of_nonneg_left hXX (by positivity)
    have step2 : κ ^ (n + 1) * (2 * ((n : ℝ) + 1) * ‖physA L z n‖ * (R ^ (n + 1) * R ^ n)) =
        (2 * ((n : ℝ) + 1) / R) * (κ ^ (n + 1) * (‖physA L z n‖ * R ^ (n + 1) * R ^ (n + 1))) := by
      field_simp
      ring
    have step3 : (2 * ((n : ℝ) + 1) / R) * (κ ^ (n + 1) * (‖physA L z n‖ * R ^ (n + 1) * R ^ (n + 1)))
        ≤ (2 * ((n : ℝ) + 1) / R) * (2 * q ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left (hkey n) (div_nonneg (by positivity) hR0)
    have step4 : (2 * ((n : ℝ) + 1) / R) * (2 * q ^ (n + 1)) ≤ a n := by
      have e : (2 * ((n : ℝ) + 1) / R) * (2 * q ^ (n + 1)) = 4 * ((n : ℝ) + 1) / R * q ^ (n + 1) := by
        ring
      have h0 : 0 ≤ 2 * q ^ (n + 1) := by have := pow_nonneg hq0 (n + 1); linarith
      have e2 : a n = 2 * q ^ (n + 1) + 4 * ((n : ℝ) + 1) / R * q ^ (n + 1) := by
        simp only [ha_def]; ring
      rw [e, e2]; linarith
    calc κ ^ (n + 1) * ‖fderiv ℝ (symFun (n + 1) (physA L z n)) x‖
        ≤ _ := step1
      _ = _ := step2
      _ ≤ _ := step3
      _ ≤ a n := step4
  · intro y hy
    have hyR : ‖y‖ ≤ R := hball y hy
    refine Summable.of_norm_bounded (g := a) hsa (fun n => ?_)
    rw [symbolTerm_eq_symFun L κ z n y, norm_mul, physW_norm κ hκ n]
    have hS := symFun_norm_le (n + 1) (physA L z n) y
    have hyy : ‖y‖ ^ (n + 1) * ‖y‖ ^ (n + 1) ≤ R ^ (n + 1) * R ^ (n + 1) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hyR _) (pow_le_pow_left₀ (norm_nonneg _) hyR _)
        (pow_nonneg (norm_nonneg _) _) (hRp _)
    calc κ ^ (n + 1) * ‖symFun (n + 1) (physA L z n) y‖
        ≤ κ ^ (n + 1) * (‖physA L z n‖ * ‖y‖ ^ (n + 1) * ‖y‖ ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hS (pow_nonneg hκ _)
      _ ≤ κ ^ (n + 1) * (‖physA L z n‖ * (R ^ (n + 1) * R ^ (n + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκ _)
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hyy (norm_nonneg _)
      _ = κ ^ (n + 1) * (‖physA L z n‖ * R ^ (n + 1) * R ^ (n + 1)) := by ring
      _ ≤ 2 * q ^ (n + 1) := hkey n
      _ ≤ a n := hpos4 n

theorem norm_conjCLM_comp_le {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (M : H →L[ℝ] ℂ) :
    ‖Complex.conjCLE.toContinuousLinearMap.comp M‖ ≤ ‖M‖ := by
  have h1 : ‖(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
      rw [one_mul]
      simp)
  calc ‖Complex.conjCLE.toContinuousLinearMap.comp M‖
      ≤ ‖(Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)‖ * ‖M‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖M‖ := one_mul _

theorem norm_ordKernel_le (z : ℂ) (hη : 0 < z.im) (j : ℕ) :
    ‖orderedKernel L (j + 1) z‖ ≤ 2 * (z.im)⁻¹ ^ (j + 1) :=
  norm_physicalKernel_le (L := L) (by omega) z hη

/-- **Norm bound for the kernel bracket:** `‖pbC (s_A) (s_B) u‖ ≤ 2pq‖A‖‖B‖` (limit of the N-uniform bound). -/
theorem norm_pbC_kps_le (p q : ℕ) (A : BoundedSymmetricKernel (L2T L) p)
    (B : BoundedSymmetricKernel (L2T L) q) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖pbC (kernelProductSymbol A) (kernelProductSymbol B) u‖ ≤ 2 * ((p : ℝ) * q) * ‖A‖ * ‖B‖ := by
  have hT := root_overlap_limit p q A B u hu
  refine le_of_tendsto hT.norm ?_
  filter_upwards [eventually_ge_atTop (p + q)] with N hN
  exact norm_limSeq_le L N p q (by omega) (by omega) A B u hu

/-- Summability of a pairwise family with the bound of the double series (as in `RootInvolutionLimit`). -/
theorem summable_pair (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im)
    (f : ℕ × ℕ → ℂ)
    (hf : ∀ nm : ℕ × ℕ, ‖f nm‖ ≤
      8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) * (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1)))) :
    Summable f := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ.le hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ.le hw
  have hr : 0 ≤ κ / z.im := div_nonneg hκ.le hη.le
  have hr' : 0 ≤ κ / w.im := div_nonneg hκ.le hη'.le
  have hr1 : κ / z.im < 1 := (div_lt_one hη).mpr hz
  have hr1' : κ / w.im < 1 := (div_lt_one hη').mpr hw
  have hsf := summable_aux2 (κ / z.im) hr hr1
  have hsg := summable_aux2 (κ / w.im) hr' hr1'
  have hsum : Summable (fun nm : ℕ × ℕ => 8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
      (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1)))) :=
    ((hsf.mul_of_nonneg hsg
      (fun n => mul_nonneg (by positivity) (pow_nonneg hr _))
      (fun m => mul_nonneg (by positivity) (pow_nonneg hr' _))).mul_left 8)
  exact Summable.of_norm_bounded (g := fun nm : ℕ × ℕ => 8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
      (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1)))) hsum hf

/-- Scalar part of the term bound: `κ^{n+1} κ^{m+1} · 2(n+1)(m+1)·‖K‖‖K'‖ ≤ 8(...)(...)`. -/
theorem term_scalar_bound (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im)
    (n m : ℕ) (X : ℝ) (hX : 0 ≤ X)
    (hX' : X ≤ 2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) * (2 * (z.im)⁻¹ ^ (n + 1)) *
        (2 * (w.im)⁻¹ ^ (m + 1))) :
    ((κ ^ (n + 1) : ℝ) * (κ ^ (m + 1) : ℝ)) * X ≤
      8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) * (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ.le hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ.le hw
  have e1 : (κ / z.im) ^ (n + 1) = κ ^ (n + 1) * (z.im)⁻¹ ^ (n + 1) := by
    rw [div_eq_mul_inv, mul_pow]
  have e2 : (κ / w.im) ^ (m + 1) = κ ^ (m + 1) * (w.im)⁻¹ ^ (m + 1) := by
    rw [div_eq_mul_inv, mul_pow]
  have hc : 0 ≤ (κ ^ (n + 1) : ℝ) * (κ ^ (m + 1) : ℝ) :=
    mul_nonneg (pow_nonneg hκ.le _) (pow_nonneg hκ.le _)
  calc ((κ ^ (n + 1) : ℝ) * (κ ^ (m + 1) : ℝ)) * X
      ≤ ((κ ^ (n + 1) : ℝ) * (κ ^ (m + 1) : ℝ)) *
          (2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) * (2 * (z.im)⁻¹ ^ (n + 1)) *
            (2 * (w.im)⁻¹ ^ (m + 1))) := mul_le_mul_of_nonneg_left hX' hc
    _ = 8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) * (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by
        rw [e1, e2]; push_cast; ring

/-- Term bound for the `A`-series term `κ^{n+1}κ^{m+1} pbC(s_{n,z}, s_{m,w})(u)`. -/
theorem term_bound_A (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) (u : L2T L)
    (hu : ‖u‖ = 1) (n m : ℕ) :
    ‖((κ ^ (n + 1) : ℝ) : ℂ) * ((κ ^ (m + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
          (kernelProductSymbol (orderedKernel L (m + 1) w)) u‖ ≤
      8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) * (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ.le hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ.le hw
  have hP := norm_pbC_kps_le L (n + 1) (m + 1) (orderedKernel L (n + 1) z)
    (orderedKernel L (m + 1) w) u hu
  have hKz := norm_ordKernel_le L z hη n
  have hKw := norm_ordKernel_le L w hη' m
  have hcast : ∀ j : ℕ, ‖((κ ^ (j + 1) : ℝ) : ℂ)‖ = κ ^ (j + 1) := fun j => by
    rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ.le _)]
  have hX : 0 ≤ ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
      (kernelProductSymbol (orderedKernel L (m + 1) w)) u‖ := norm_nonneg _
  have hX' : ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
      (kernelProductSymbol (orderedKernel L (m + 1) w)) u‖ ≤
      2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) * (2 * (z.im)⁻¹ ^ (n + 1)) *
        (2 * (w.im)⁻¹ ^ (m + 1)) := by
    refine hP.trans ?_
    have hpq : 0 ≤ 2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) := by positivity
    apply mul_le_mul (mul_le_mul_of_nonneg_left hKz hpq) hKw (by positivity)
      (mul_nonneg hpq (mul_nonneg zero_le_two (pow_nonneg (inv_nonneg.mpr hη.le) _)))
  rw [norm_mul, norm_mul, hcast, hcast]
  have := term_scalar_bound κ hκ z w hz hw n m _ hX hX'
  calc κ ^ (n + 1) * κ ^ (m + 1) * ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
        (kernelProductSymbol (orderedKernel L (m + 1) w)) u‖
      = (κ ^ (n + 1) * κ ^ (m + 1)) * ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
        (kernelProductSymbol (orderedKernel L (m + 1) w)) u‖ := by ring
    _ ≤ _ := this

/-- Term bound for the conjugate-pair term `κ^{n+1}κ^{m+1} pbC(s_{n,z}, conj s_{m,w})(u)`. -/
theorem term_bound_B (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) (u : L2T L)
    (hu : ‖u‖ = 1) (n m : ℕ) :
    ‖((κ ^ (n + 1) : ℝ) : ℂ) * ((κ ^ (m + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
          (fun v => conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)) u‖ ≤
      8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) * (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by
  have hη : 0 < z.im := lt_of_le_of_lt hκ.le hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ.le hw
  have hfun : (fun v => conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)) =
      kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)) :=
    funext fun v => (kernelProductSymbol_adjoint _ v).symm
  rw [hfun]
  have hAdj : ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖ ≤ 2 * (w.im)⁻¹ ^ (m + 1) := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_ordKernel_le L w hη' m
  have hP := norm_pbC_kps_le L (n + 1) (m + 1) (orderedKernel L (n + 1) z)
    (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)) u hu
  have hKz := norm_ordKernel_le L z hη n
  have hcast : ∀ j : ℕ, ‖((κ ^ (j + 1) : ℝ) : ℂ)‖ = κ ^ (j + 1) := fun j => by
    rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ.le _)]
  have hX' : ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
      (kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w))) u‖ ≤
      2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) * (2 * (z.im)⁻¹ ^ (n + 1)) *
        (2 * (w.im)⁻¹ ^ (m + 1)) := by
    refine hP.trans ?_
    have hpq : 0 ≤ 2 * ((((n + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ)) := by positivity
    apply mul_le_mul (mul_le_mul_of_nonneg_left hKz hpq) hAdj (by positivity)
      (mul_nonneg hpq (mul_nonneg zero_le_two (pow_nonneg (inv_nonneg.mpr hη.le) _)))
  rw [norm_mul, norm_mul, hcast, hcast]
  have := term_scalar_bound κ hκ z w hz hw n m _ (norm_nonneg _) hX'
  calc κ ^ (n + 1) * κ ^ (m + 1) * ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
        (kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w))) u‖
      = (κ ^ (n + 1) * κ ^ (m + 1)) * ‖pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
        (kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w))) u‖ := by ring
    _ ≤ _ := this

theorem radius_for (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) :
    ∃ ρ : ℝ, 0 < ρ ∧ κ * (1 + ρ) ^ 2 < z.im ∧ κ * (1 + ρ) ^ 2 < w.im :=
  radius_exists κ z.im w.im hκ hz hw

theorem ball_bound (u : L2T L) (ρ : ℝ) (hu : ‖u‖ = 1) :
    ∀ x ∈ ball u ρ, ‖x‖ ≤ 1 + ρ := fun x hx => by
  have h1 : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
    have := norm_add_le u (x - u)
    simpa using this
  have h2 : ‖x - u‖ < ρ := by
    have := mem_ball.mp hx
    rwa [dist_eq_norm] at this
  rw [hu] at h1
  linarith

/-- **Bracket identity A:** `{s_z, s_w}(u) = 0` for unit `u`. -/
theorem bracket_A (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) (u : L2T L)
    (hu : ‖u‖ = 1) :
    pbC (fun v => productSymbol L κ v z) (fun v => productSymbol L κ v w) u = 0 := by
  obtain ⟨ρ, hρ, hρz, hρw⟩ := radius_for κ hκ z w hz hw
  have hR : 0 < 1 + ρ := by linarith
  have hball := ball_bound L u ρ hu
  obtain ⟨az, hsz, hFd, hFb, hFs⟩ :=
    series_data L κ hκ.le z (lt_of_le_of_lt hκ.le hz) u ρ (1 + ρ) hR hball hρz
  obtain ⟨aw, hsw, hGd, hGb, hGs⟩ :=
    series_data L κ hκ.le w (lt_of_le_of_lt hκ.le hw) u ρ (1 + ρ) hR hball hρw
  have hI := pbC_hasSum_tsum (fun n y => symbolTerm L κ y z (n + 1))
    (fun m y => symbolTerm L κ y w (m + 1))
    (fun n x => physW κ n • fderiv ℝ (symFun (n + 1) (physA L z n)) x)
    (fun m x => physW κ m • fderiv ℝ (symFun (m + 1) (physA L w m)) x) az aw u ρ hρ hFd hGd hFb hGb
    hsz hsw hFs hGs
  have hI' : ∑' n, ∑' m, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => symbolTerm L κ y w (m + 1)) u =
      pbC (fun y => ∑' n, symbolTerm L κ y z (n + 1)) (fun y => ∑' m, symbolTerm L κ y w (m + 1)) u :=
    hI.tsum_eq
  have hterm : ∀ n m : ℕ, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => symbolTerm L κ y w (m + 1)) u =
      ((κ ^ (n + 1) : ℝ) : ℂ) * ((κ ^ (m + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
          (kernelProductSymbol (orderedKernel L (m + 1) w)) u := by
    intro n m
    have e1 : (fun y => symbolTerm L κ y z (n + 1)) =
        fun y => ((κ ^ (n + 1) : ℝ) : ℂ) * kernelProductSymbol (orderedKernel L (n + 1) z) y := rfl
    have e2 : (fun y => symbolTerm L κ y w (m + 1)) =
        fun y => ((κ ^ (m + 1) : ℝ) : ℂ) * kernelProductSymbol (orderedKernel L (m + 1) w) y := rfl
    rw [e1, e2, pbC_real_scalar (κ ^ (n + 1)) (κ ^ (m + 1))
      (kernelProductSymbol (orderedKernel L (n + 1) z)) (kernelProductSymbol (orderedKernel L (m + 1) w)) u
      (kps_re_im_diff L z n u).1 (kps_re_im_diff L z n u).2
      (kps_re_im_diff L w m u).1 (kps_re_im_diff L w m u).2]
    push_cast
    ring
  have hsumA : Summable (fun nm : ℕ × ℕ => ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
      pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
        (kernelProductSymbol (orderedKernel L (nm.2 + 1) w)) u) :=
    summable_pair κ hκ z w hz hw _ (fun nm => term_bound_A L κ hκ z w hz hw u hu nm.1 nm.2)
  have hsplit : ∑' n, ∑' m, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => symbolTerm L κ y w (m + 1)) u =
      ∑' nm : ℕ × ℕ, ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
          (kernelProductSymbol (orderedKernel L (nm.2 + 1) w)) u := by
    simp only [hterm]
    exact hsumA.tsum_prod.symm
  have hS : pbC (fun v => productSymbol L κ v z) (fun v => productSymbol L κ v w) u =
      pbC (fun y => ∑' n, symbolTerm L κ y z (n + 1)) (fun y => ∑' m, symbolTerm L κ y w (m + 1)) u := by
    show pbC (fun v => (1 + Complex.exp (Complex.I * z * L)) + ∑' n, symbolTerm L κ v z (n + 1))
      (fun v => (1 + Complex.exp (Complex.I * w * L)) + ∑' m, symbolTerm L κ v w (m + 1)) u = _
    rw [pbC_const_add_left, pbC_const_add_right]
  rw [hS, ← hI', hsplit]
  exact double_limit_zero L κ hκ z w hz hw u hu

/-- **Bracket identity B:** `{s_z, s̄_w}(u) = 0` for unit `u`. -/
theorem bracket_B (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) (u : L2T L)
    (hu : ‖u‖ = 1) :
    pbC (fun v => productSymbol L κ v z) (fun v => conj (productSymbol L κ v w)) u = 0 := by
  obtain ⟨ρ, hρ, hρz, hρw⟩ := radius_for κ hκ z w hz hw
  have hR : 0 < 1 + ρ := by linarith
  have hball := ball_bound L u ρ hu
  obtain ⟨az, hsz, hFd, hFb, hFs⟩ :=
    series_data L κ hκ.le z (lt_of_le_of_lt hκ.le hz) u ρ (1 + ρ) hR hball hρz
  obtain ⟨aw, hsw, hGd, hGb, hGs⟩ :=
    series_data L κ hκ.le w (lt_of_le_of_lt hκ.le hw) u ρ (1 + ρ) hR hball hρw
  have hGd' : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => conj (symbolTerm L κ y w (m + 1)))
      (Complex.conjCLE.toContinuousLinearMap.comp (physW κ m • fderiv ℝ (symFun (m + 1) (physA L w m)) x)) x :=
    fun m x hx => (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt).comp x (hGd m x hx)
  have hGb' : ∀ m, ∀ x ∈ ball u ρ,
      ‖Complex.conjCLE.toContinuousLinearMap.comp (physW κ m • fderiv ℝ (symFun (m + 1) (physA L w m)) x)‖ ≤ aw m :=
    fun m x hx => (norm_conjCLM_comp_le _).trans (hGb m x hx)
  have hGs' : ∀ y ∈ ball u ρ, Summable fun m => conj (symbolTerm L κ y w (m + 1)) := fun y hy => by
    simpa using Complex.conjCLE.toContinuousLinearMap.summable (hGs y hy)
  have hI2 := pbC_hasSum_tsum (fun n y => symbolTerm L κ y z (n + 1))
    (fun m y => conj (symbolTerm L κ y w (m + 1)))
    (fun n x => physW κ n • fderiv ℝ (symFun (n + 1) (physA L z n)) x)
    (fun m x => Complex.conjCLE.toContinuousLinearMap.comp
      (physW κ m • fderiv ℝ (symFun (m + 1) (physA L w m)) x)) az aw u ρ hρ hFd hGd' hFb hGb'
    hsz hsw hFs hGs'
  have hI2' : ∑' n, ∑' m, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => conj (symbolTerm L κ y w (m + 1))) u =
      pbC (fun y => ∑' n, symbolTerm L κ y z (n + 1)) (fun y => ∑' m, conj (symbolTerm L κ y w (m + 1))) u :=
    hI2.tsum_eq
  have hterm : ∀ n m : ℕ, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => conj (symbolTerm L κ y w (m + 1))) u =
      ((κ ^ (n + 1) : ℝ) : ℂ) * ((κ ^ (m + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (n + 1) z))
          (fun v => conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)) u := by
    intro n m
    have e1 : (fun y => symbolTerm L κ y z (n + 1)) =
        fun y => ((κ ^ (n + 1) : ℝ) : ℂ) * kernelProductSymbol (orderedKernel L (n + 1) z) y := rfl
    have e2 : (fun y => conj (symbolTerm L κ y w (m + 1))) =
        fun y => ((κ ^ (m + 1) : ℝ) : ℂ) * conj (kernelProductSymbol (orderedKernel L (m + 1) w) y) := by
      funext y
      simp [symbolTerm, map_mul, Complex.conj_ofReal]
    have hg1 : DifferentiableAt ℝ (fun v => (conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)).re) u := by
      simpa only [Complex.conj_re] using (kps_re_im_diff L w m u).1
    have hg2 : DifferentiableAt ℝ (fun v => (conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)).im) u := by
      simp only [Complex.conj_im]
      exact (kps_re_im_diff L w m u).2.neg
    rw [e1, e2, pbC_real_scalar (κ ^ (n + 1)) (κ ^ (m + 1))
      (kernelProductSymbol (orderedKernel L (n + 1) z))
      (fun v => conj (kernelProductSymbol (orderedKernel L (m + 1) w) v)) u
      (kps_re_im_diff L z n u).1 (kps_re_im_diff L z n u).2 hg1 hg2]
    push_cast
    ring
  have hsumB : Summable (fun nm : ℕ × ℕ => ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
      pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
        (fun v => conj (kernelProductSymbol (orderedKernel L (nm.2 + 1) w) v)) u) :=
    summable_pair κ hκ z w hz hw _ (fun nm => term_bound_B L κ hκ z w hz hw u hu nm.1 nm.2)
  have hsplit : ∑' n, ∑' m, pbC (fun y => symbolTerm L κ y z (n + 1))
      (fun y => conj (symbolTerm L κ y w (m + 1))) u =
      ∑' nm : ℕ × ℕ, ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
          (fun v => conj (kernelProductSymbol (orderedKernel L (nm.2 + 1) w) v)) u := by
    simp only [hterm]
    exact hsumB.tsum_prod.symm
  have e3 : (fun v => conj (productSymbol L κ v w)) =
      fun v => conj (1 + Complex.exp (Complex.I * w * L)) + ∑' m, conj (symbolTerm L κ v w (m + 1)) := by
    funext v
    show conj ((1 + Complex.exp (Complex.I * w * L)) + ∑' m, symbolTerm L κ v w (m + 1)) = _
    rw [map_add, Complex.conj_tsum]
  have hS : pbC (fun v => productSymbol L κ v z) (fun v => conj (productSymbol L κ v w)) u =
      pbC (fun y => ∑' n, symbolTerm L κ y z (n + 1)) (fun y => ∑' m, conj (symbolTerm L κ y w (m + 1))) u := by
    rw [e3]
    show pbC (fun v => (1 + Complex.exp (Complex.I * z * L)) + ∑' n, symbolTerm L κ v z (n + 1))
      (fun v => conj (1 + Complex.exp (Complex.I * w * L)) + ∑' m, conj (symbolTerm L κ v w (m + 1))) u = _
    rw [pbC_const_add_left, pbC_const_add_right]
  rw [hS, ← hI2', hsplit]
  exact double_limit_conj_symbol L κ hκ z w hz hw u hu

/-- **The four real zero brackets** of the real and imaginary parts of `s_z`, `s_w` (unit `u`). -/
theorem real_zero_brackets (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im) (u : L2T L)
    (hu : ‖u‖ = 1) :
    pbR (fun v => (productSymbol L κ v z).re) (fun v => (productSymbol L κ v w).re) u = 0 ∧
    pbR (fun v => (productSymbol L κ v z).im) (fun v => (productSymbol L κ v w).im) u = 0 ∧
    pbR (fun v => (productSymbol L κ v z).im) (fun v => (productSymbol L κ v w).re) u = 0 ∧
    pbR (fun v => (productSymbol L κ v z).re) (fun v => (productSymbol L κ v w).im) u = 0 := by
  have hA := Complex.ext_iff.mp (bracket_A L κ hκ z w hz hw u hu)
  have hB := Complex.ext_iff.mp (bracket_B L κ hκ z w hz hw u hu)
  simp only [pbC, Complex.zero_re, Complex.zero_im, Complex.conj_re, Complex.conj_im,
    pbR_neg_right] at hA hB
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end QuantumNLS.RootSymbolBrackets

#print axioms QuantumNLS.RootSymbolBrackets.bracket_A
#print axioms QuantumNLS.RootSymbolBrackets.bracket_B
#print axioms QuantumNLS.RootSymbolBrackets.real_zero_brackets
