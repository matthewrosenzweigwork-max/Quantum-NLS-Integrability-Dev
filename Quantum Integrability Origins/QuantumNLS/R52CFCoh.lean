import QuantumNLS.R52CFBudget
import QuantumNLS.R52CFHartree
import QuantumNLS.R52CFPieces
import QuantumNLS.R52CFDeriv
import QuantumNLS.RootProductSymbolAnalytic

/-!
# R-52CF5DA1 stage 8a: the coherent energy of the frozen-contour kernels and its differential

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "The limiting Hamiltonian is the
corresponding linear functional of the classical transfer with denominator frozen at `v`."

For a compact finite-measure parameter space `Θ`, a continuous contour path `z(θ)` in a strip `|Im z| ≤ h` and a
continuous weight `g(θ)`, the frozen-contour kernels `A_j = κ^{j+1} Re ∫ g K_{j+1}(z(θ)) dν` (stage 4 `kerA`) have
* `cohTerm_kerA`: `Re⟨u^{⊗(j+1)}, A_j u^{⊗(j+1)}⟩ = Re ∫ g(θ) κ^{j+1}⟨u^{⊗(j+1)},K_{j+1}(z(θ))u^{⊗(j+1)}⟩ dν`;
* **`coh_eq`**: the coherent energy is the linear functional of the classical transfer,
  `E_A(u) = Re ∫ g(θ) (s(z(θ);u) - 1 - e^{i z(θ) L}) dν` for EVERY `u ∈ L²` (no norm restriction);
* **`coh_rect`**: on the concatenated fixed rectangles of stage 6 with real weights `t_i` and a fixed denominator
  `D` (`g = u_θ / D(z_θ)`), `E_A(u) = Σ_i t_i · (-(2πκ)⁻¹) Re ∮_{Γ_i} (s(z;u) - 1 - e^{izL}) / D(z) dz`;
* **`lam_hasFDerivAt`**: each rectangle functional is differentiable at every `u` with
  `d[-(2πκ)⁻¹ Re ∮_Γ (s(z;·) - 1 - e^{izL})/D](u)[k] = -(2πκ)⁻¹ Re ∮_Γ ∂_u s(z;u)[k] / D(z) dz`
  (accepted uniform contour analyticity of the discriminant, `DEF014UniformDiscriminant.analyticAt_discriminant_contour`,
  and `s = e^{izL/2}·discriminant`, accepted R-C4F43CA8).
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.R52CFCoh

open TensorCarrier KernelDefinition QuantumNLS.R52CFKernels QuantumNLS.R52CFBudget
open QuantumNLS.MixedQuadratures (reOp)
open LabelExactPeriod (rectIntegral)
open PhysicalTensor (L2T)

/-! ### Generic inner product of a frozen-contour kernel -/

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
  (ν : Measure Θ) [IsFiniteMeasure ν]

theorem re_inner_reOp (c : ℝ) (X : E →L[ℂ] E) (y : E) :
    (⟪y, ((c : ℂ) • reOp X) y⟫_ℂ).re = c * (⟪y, X y⟫_ℂ).re := by
  have h1 : ⟪y, ((c : ℂ) • reOp X) y⟫_ℂ =
      (c : ℂ) * ((1 / 2 : ℂ) * (⟪y, X y⟫_ℂ + conj ⟪y, X y⟫_ℂ)) := by
    simp only [reOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, inner_smul_right,
      inner_add_right, ContinuousLinearMap.adjoint_inner_right]
    rw [← inner_conj_symm (X y) y]
  rw [h1, Complex.add_conj]
  rw [show ((c : ℂ) * ((1 / 2 : ℂ) * ((2 * (⟪y, X y⟫_ℂ).re : ℝ) : ℂ))) = ((c * (⟪y, X y⟫_ℂ).re : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re]

theorem inner_integral_apply (g : Θ → ℂ) (K : Θ → E →L[ℂ] E) (hg : Continuous g) (hK : Continuous K)
    (y : E) :
    ⟪y, (∫ θ, g θ • K θ ∂ν) y⟫_ℂ = ∫ θ, g θ * ⟪y, K θ y⟫_ℂ ∂ν := by
  have hint : Integrable (fun θ => g θ • K θ) ν := integrable_of_cont ν (hg.smul hK)
  rw [ContinuousLinearMap.integral_apply hint]
  have hint2 : Integrable (fun θ => (g θ • K θ) y) ν :=
    integrable_of_cont ν ((ContinuousLinearMap.apply ℂ E y).continuous.comp (hg.smul hK))
  have hc := (innerSL ℂ y).integral_comp_comm hint2
  simp only [innerSL_apply_apply] at hc
  rw [← hc]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

end Generic

/-! ### The physical coherent energy -/

section Physical
variable {L : ℝ} [Fact (0 < L)]
variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
  (ν : Measure Θ) [IsFiniteMeasure ν]

/-- `y_r(u) = u^{⊗r}` as a vector of the symmetric sector. -/
abbrev yv (r : ℕ) (u : L2T L) : SymSector ℂ (L2T L) r := ⟨htpow r u, htpow_mem_symSector r u⟩

theorem kps_eq {r : ℕ} (A : BoundedSymmetricKernel (L2T L) r) (u : L2T L) :
    kernelProductSymbol A u = ⟪yv r u, A (yv r u)⟫_ℂ := by
  unfold kernelProductSymbol
  rfl

theorem norm_yv (r : ℕ) (u : L2T L) : ‖yv r u‖ = ‖u‖ ^ r := by
  change ‖(htpow r u : HilbertTensorPower ℂ (L2T L) r)‖ = _
  exact norm_htpow r u

theorem norm_kps_le {r : ℕ} (A : BoundedSymmetricKernel (L2T L) r) (u : L2T L) :
    ‖kernelProductSymbol A u‖ ≤ ‖A‖ * ‖u‖ ^ (2 * r) := by
  rw [kps_eq]
  refine (norm_inner_le_norm _ _).trans ?_
  have h1 := A.le_opNorm (yv r u)
  rw [norm_yv] at h1 ⊢
  calc ‖u‖ ^ r * ‖A (yv r u)‖ ≤ ‖u‖ ^ r * (‖A‖ * ‖u‖ ^ r) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖A‖ * ‖u‖ ^ (2 * r) := by ring

set_option synthInstance.maxHeartbeats 4000000 in
theorem continuous_kps (z : Θ → ℂ) (hz : Continuous z) (j : ℕ) (u : L2T L) :
    Continuous (fun θ => kernelProductSymbol (physK (L := L) z j θ) u) := by
  simp_rw [kps_eq]
  have hc := physK_continuous (L := L) z hz j
  exact continuous_const.inner ((ContinuousLinearMap.apply ℂ _ (yv (j + 1) u)).continuous.comp hc)

set_option synthInstance.maxHeartbeats 4000000 in
theorem cohTerm_kerA (κ : ℝ) (g z : Θ → ℂ) (hg : Continuous g) (hz : Continuous z) (u : L2T L) (j : ℕ) :
    R52CFHartree.cohTerm (kerA ν κ g (physK (L := L) z) j) u =
      (∫ θ, g θ * NormalizedTransfer.symbolTerm L κ u (z θ) (j + 1) ∂ν).re := by
  unfold R52CFHartree.cohTerm kerA
  rw [kps_eq, re_inner_reOp, inner_integral_apply ν g (physK (L := L) z j) hg
    (physK_continuous (L := L) z hz j)]
  have he : (fun θ => g θ * NormalizedTransfer.symbolTerm L κ u (z θ) (j + 1)) =
      fun θ => ((κ ^ (j + 1) : ℝ) : ℂ) * (g θ * ⟪yv (j + 1) u, physK (L := L) z j θ (yv (j + 1) u)⟫_ℂ) := by
    funext θ
    unfold NormalizedTransfer.symbolTerm physK
    rw [kps_eq]
    ring
  rw [he, integral_const_mul, Complex.re_ofReal_mul]

/-- The factorial majorant is summable against every geometric weight. -/
theorem beta_geom_summable (κ h x : ℝ) (hx : 0 ≤ x) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j * (beta L κ h j * x ^ (j + 1))) := by
  have hL : 0 < L := Fact.out
  have hs := (majorant_summable (|κ| * L * x) (by positivity)).mul_left (2 * Real.exp (L * h))
  refine hs.congr fun j => ?_
  unfold beta
  rw [mul_pow, mul_pow]
  ring

theorem beta_pow_summable (κ h x : ℝ) (hx : 0 ≤ x) :
    Summable (fun j : ℕ => beta L κ h j * x ^ (j + 1)) := by
  have hL : 0 < L := Fact.out
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (beta_nonneg L κ h hL j) (by positivity))
    (fun j => ?_) (beta_geom_summable (L := L) κ h x hx)
  have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j := by
    have ha : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by norm_cast; omega)
    have hb : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (by positivity)
    nlinarith
  have h2 : 0 ≤ beta L κ h j * x ^ (j + 1) := mul_nonneg (beta_nonneg L κ h hL j) (by positivity)
  nlinarith

set_option synthInstance.maxHeartbeats 4000000 in
/-- **The coherent energy is the linear functional of the classical transfer**, at every `u`. -/
theorem coh_eq (κ : ℝ) (g z : Θ → ℂ) (hg : Continuous g) (hz : Continuous z) {h W : ℝ}
    (hzh : ∀ θ, |(z θ).im| ≤ h) (hgW : ∀ θ, ‖g θ‖ ≤ W) (u : L2T L) :
    R52CFHartree.coh (kerA ν κ g (physK (L := L) z)) u =
      (∫ θ, g θ * (NormalizedTransfer.productSymbol L κ u (z θ) - 1 -
        Complex.exp (Complex.I * z θ * L)) ∂ν).re := by
  have hL : 0 < L := Fact.out
  let Fj : ℕ → Θ → ℂ := fun j θ => g θ * NormalizedTransfer.symbolTerm L κ u (z θ) (j + 1)
  have hcont : ∀ j, Continuous (Fj j) := by
    intro j
    refine hg.mul ?_
    unfold NormalizedTransfer.symbolTerm
    exact continuous_const.mul (continuous_kps (L := L) z hz j u)
  have hbd : ∀ j θ, ‖Fj j θ‖ ≤ W * (beta L κ h j * (‖u‖ ^ 2) ^ (j + 1)) := by
    intro j θ
    dsimp [Fj]
    rw [norm_mul]
    refine mul_le_mul (hgW θ) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hgW θ))
    unfold NormalizedTransfer.symbolTerm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow]
    have h1 := norm_kps_le (NormalizedTransfer.orderedKernel L (j + 1) (z θ)) u
    have h2 := physK_bound (L := L) κ z hzh j θ
    have h3 : (‖u‖ ^ 2) ^ (j + 1) = ‖u‖ ^ (2 * (j + 1)) := by rw [← pow_mul]
    rw [h3]
    calc |κ| ^ (j + 1) * ‖kernelProductSymbol (NormalizedTransfer.orderedKernel L (j + 1) (z θ)) u‖
        ≤ |κ| ^ (j + 1) * (‖NormalizedTransfer.orderedKernel L (j + 1) (z θ)‖ * ‖u‖ ^ (2 * (j + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (|κ| ^ (j + 1) * ‖physK (L := L) z j θ‖) * ‖u‖ ^ (2 * (j + 1)) := by
          unfold physK; ring
      _ ≤ beta L κ h j * ‖u‖ ^ (2 * (j + 1)) := mul_le_mul_of_nonneg_right h2 (by positivity)
  have hint : ∀ j, Integrable (Fj j) ν := fun j => integrable_of_cont ν (hcont j)
  have hsumI : Summable (fun j => ∫ θ, ‖Fj j θ‖ ∂ν) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun θ => norm_nonneg _) (fun j => ?_)
      (((beta_pow_summable (L := L) κ h (‖u‖ ^ 2) (by positivity)).mul_left W).mul_left (ν.real univ))
    calc ∫ θ, ‖Fj j θ‖ ∂ν ≤ ∫ _θ, W * (beta L κ h j * (‖u‖ ^ 2) ^ (j + 1)) ∂ν :=
          integral_mono (hint j).norm (integrable_const _) (fun θ => hbd j θ)
      _ = ν.real univ * (W * (beta L κ h j * (‖u‖ ^ 2) ^ (j + 1))) := by
          rw [integral_const, smul_eq_mul]
  have hsum : Summable (fun j => ∫ θ, Fj j θ ∂ν) :=
    Summable.of_norm_bounded hsumI (fun j => norm_integral_le_integral_norm _)
  have hc : ∀ j, R52CFHartree.cohTerm (kerA ν κ g (physK (L := L) z) j) u = (∫ θ, Fj j θ ∂ν).re :=
    fun j => cohTerm_kerA ν κ g z hg hz u j
  have hre := Complex.reCLM.map_tsum hsum
  simp only [Complex.reCLM_apply] at hre
  unfold R52CFHartree.coh
  simp_rw [hc]
  rw [← hre]
  congr 1
  rw [integral_tsum_of_summable_integral_norm hint hsumI]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  show ∑' j, g θ * NormalizedTransfer.symbolTerm L κ u (z θ) (j + 1) = _
  rw [tsum_mul_left]
  congr 1
  unfold NormalizedTransfer.productSymbol
  ring

/-! ### The concatenated fixed rectangles -/

theorem rect4_mem {a b h : ℝ} (c : ℂ) (hab : a ≤ b) (hh : 0 ≤ h) (j : Fin 4) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ ≤ 1) : (R52CFPieces.rect4 a b h c j).γ τ ∈ PeriodReconstruction.Gam a b h := by
  fin_cases j
  · show (R52CFPieces.rect4 a b h c 0).γ τ ∈ PeriodReconstruction.Gam a b h
    have e : (R52CFPieces.rect4 a b h c 0).γ τ =
        ((a : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) - h * I) - ((a : ℂ) - h * I)) := rfl
    have hre : ((R52CFPieces.rect4 a b h c 0).γ τ).re = a + τ * (b - a) := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    have him : ((R52CFPieces.rect4 a b h c 0).γ τ).im = -h := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    exact Or.inl ⟨⟨by rw [hre]; nlinarith, by rw [hre]; nlinarith⟩, Or.inl him⟩
  · show (R52CFPieces.rect4 a b h c 1).γ τ ∈ PeriodReconstruction.Gam a b h
    have e : (R52CFPieces.rect4 a b h c 1).γ τ =
        ((b : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) + h * I) - ((b : ℂ) - h * I)) := rfl
    have hre : ((R52CFPieces.rect4 a b h c 1).γ τ).re = b := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    have him : ((R52CFPieces.rect4 a b h c 1).γ τ).im = -h + τ * (2 * h) := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    exact Or.inr ⟨⟨by rw [him]; nlinarith, by rw [him]; nlinarith⟩, Or.inr hre⟩
  · show (R52CFPieces.rect4 a b h c 2).γ τ ∈ PeriodReconstruction.Gam a b h
    have e : (R52CFPieces.rect4 a b h c 2).γ τ =
        ((b : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) + h * I) - ((b : ℂ) + h * I)) := rfl
    have hre : ((R52CFPieces.rect4 a b h c 2).γ τ).re = b + τ * (a - b) := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    have him : ((R52CFPieces.rect4 a b h c 2).γ τ).im = h := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    exact Or.inl ⟨⟨by rw [hre]; nlinarith, by rw [hre]; nlinarith⟩, Or.inr him⟩
  · show (R52CFPieces.rect4 a b h c 3).γ τ ∈ PeriodReconstruction.Gam a b h
    have e : (R52CFPieces.rect4 a b h c 3).γ τ =
        ((a : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) - h * I) - ((a : ℂ) + h * I)) := rfl
    have hre : ((R52CFPieces.rect4 a b h c 3).γ τ).re = a := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    have him : ((R52CFPieces.rect4 a b h c 3).γ τ).im = h - τ * (2 * h) := by
      rw [e]; simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im, Complex.add_im]; ring
    exact Or.inr ⟨⟨by rw [him]; nlinarith, by rw [him]; nlinarith⟩, Or.inl hre⟩

/-- The points of the concatenated rectangle family lie on the corresponding rectangle. -/
theorem zθ_mem {m : ℕ} (a b hh : Fin m → ℝ) (c : Fin m → ℂ) (hab : ∀ i, a i ≤ b i)
    (hh0 : ∀ i, 0 ≤ hh i) (θ : MPContour.ThetaSpace (m * 4)) :
    MPContour.zθ (R52CFPieces.rectFam a b hh c) θ ∈
      PeriodReconstruction.Gam (a (finProdFinEquiv.symm θ.1).1) (b (finProdFinEquiv.symm θ.1).1)
        (hh (finProdFinEquiv.symm θ.1).1) :=
  rect4_mem _ (hab _) (hh0 _) _ θ.2.2.1 θ.2.2.2

theorem Gam_abs_im_le {a b h : ℝ} (hh : 0 ≤ h) {z : ℂ} (hz : z ∈ PeriodReconstruction.Gam a b h) :
    |z.im| ≤ h := by
  rcases hz with ⟨-, h2 | h2⟩ | ⟨h1, -⟩
  · rw [h2, abs_neg, abs_of_nonneg hh]
  · rw [h2, abs_of_nonneg hh]
  · exact abs_le.mpr h1

theorem zθ_im_le {m : ℕ} (a b hh : Fin m → ℝ) (c : Fin m → ℂ) (hab : ∀ i, a i ≤ b i)
    (hh0 : ∀ i, 0 ≤ hh i) {H : ℝ} (hH : ∀ i, hh i ≤ H) (θ : MPContour.ThetaSpace (m * 4)) :
    |(MPContour.zθ (R52CFPieces.rectFam a b hh c) θ).im| ≤ H :=
  (Gam_abs_im_le (hh0 _) (zθ_mem a b hh c hab hh0 θ)).trans (hH _)

theorem continuous_productSymbol (κ : ℝ) (hκ : 0 ≤ κ) (u : L2T L) :
    Continuous (fun z : ℂ => NormalizedTransfer.productSymbol L κ u z) :=
  continuous_iff_continuousAt.mpr fun z =>
    (RootProductSymbolAnalytic.analyticAt_productSymbol_z L κ hκ u z).continuousAt

/-- The fixed-rectangle, fixed-denominator functional `-(2πκ)⁻¹ Re ∮_Γ (s(z;u) - 1 - e^{izL}) / D(z) dz`. -/
def lam (κ : ℝ) (Dz : ℂ → ℂ) (a b h : ℝ) (u : L2T L) : ℝ :=
  -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => (NormalizedTransfer.productSymbol L κ u z - 1 -
    Complex.exp (Complex.I * z * L)) / Dz z) a b h).re

/-- **The differential of a fixed-rectangle functional**, at every `u ∈ L²`. -/
theorem lam_hasFDerivAt (κ : ℝ) (hκ : 0 ≤ κ) (Dz : ℂ → ℂ) {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hD : ContinuousOn (fun z => (Dz z)⁻¹) (PeriodReconstruction.Gam a b h)) (u : L2T L) :
    HasFDerivAt (lam (L := L) κ Dz a b h) (fderiv ℝ (lam (L := L) κ Dz a b h) u) u ∧
      ∀ k : L2T L, fderiv ℝ (lam (L := L) κ Dz a b h) u k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Dz z)
          a b h).re := by
  let Bd := Prop010RectangleDifferentialR17.Boundary a b h
  let Z : C(Bd, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨D, hDa, hDe⟩ := DEF014UniformDiscriminant.analyticAt_discriminant_contour (L := L) κ Z u
  have hDi : Continuous (fun z : Bd => (Dz z.1)⁻¹) := hD.restrict
  let Ei : C(Bd, ℂ) := ⟨fun z => Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) * (Dz z.1)⁻¹,
    (by fun_prop : Continuous (fun z : Bd => Complex.exp (Complex.I * z.1 * (L : ℂ) / 2))).mul hDi⟩
  let c0 : C(Bd, ℂ) := ⟨fun z => (1 + Complex.exp (Complex.I * z.1 * L)) * (Dz z.1)⁻¹,
    (by fun_prop : Continuous (fun z : Bd => 1 + Complex.exp (Complex.I * z.1 * L))).mul hDi⟩
  let T := Prop010RectangleDifferentialR17.boundaryIntegral hab hh
  let M : C(Bd, ℂ) →L[ℝ] C(Bd, ℂ) := ContinuousLinearMap.mul ℝ C(Bd, ℂ) Ei
  let ℓ : C(Bd, ℂ) →L[ℝ] ℝ := (-(2 * Real.pi * κ)⁻¹) • (Complex.reCLM.comp (T.comp M))
  let C0 : ℝ := (2 * Real.pi * κ)⁻¹ * (T c0).re
  have hsym : ∀ (w : L2T L) (z : Bd), NormalizedTransfer.productSymbol L κ w z.1 =
      Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) * D w z := by
    intro w z
    rw [hDe w z, RootProductSymbolAnalytic.productSymbol_eq_exp_mul_discriminant L κ hκ]
    rfl
  have hrep : lam (L := L) κ Dz a b h = fun w => ℓ (D w) + C0 := by
    funext w
    have hT : rectIntegral (fun z => (NormalizedTransfer.productSymbol L κ w z - 1 -
        Complex.exp (Complex.I * z * L)) / Dz z) a b h = T (M (D w) - c0) := by
      symm
      apply Prop010RectangleDifferentialR17.boundaryIntegral_eq hab hh
      intro z
      rw [hsym w z]
      simp only [M, Ei, c0, ContinuousMap.sub_apply, ContinuousLinearMap.mul_apply',
        ContinuousMap.mul_apply, ContinuousMap.coe_mk]
      rw [div_eq_mul_inv]
      ring
    unfold lam
    rw [hT, map_sub]
    simp only [ℓ, C0, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
      smul_eq_mul, Complex.sub_re]
    ring
  have hD' : HasFDerivAt D (fderiv ℝ D u) u := hDa.differentiableAt.hasFDerivAt
  have hL : HasFDerivAt (lam (L := L) κ Dz a b h) (ℓ.comp (fderiv ℝ D u)) u := by
    rw [hrep]
    exact (ℓ.hasFDerivAt.comp u hD').add_const C0
  refine ⟨hL.differentiableAt.hasFDerivAt, fun k => ?_⟩
  rw [hL.fderiv]
  have hpt : ∀ z : Bd, fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z.1) u k =
      Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) * fderiv ℝ D u k z := by
    intro z
    have he : (fun w : L2T L => RootScalarPeriodR10.symbol κ w z.1) =
        fun w => Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) * ContinuousMap.evalCLM ℝ z (D w) := by
      funext w
      exact hsym w z
    have hd : HasFDerivAt (fun w => Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) * ContinuousMap.evalCLM ℝ z (D w))
        (Complex.exp (Complex.I * z.1 * (L : ℂ) / 2) • ((ContinuousMap.evalCLM ℝ z).comp (fderiv ℝ D u))) u :=
      ((ContinuousMap.evalCLM ℝ z).hasFDerivAt.comp u hD').const_mul
        (Complex.exp (Complex.I * z.1 * (L : ℂ) / 2))
    rw [he, hd.fderiv]
    rfl
  have hT : T (M (fderiv ℝ D u k)) = rectIntegral
      (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Dz z) a b h := by
    apply Prop010RectangleDifferentialR17.boundaryIntegral_eq hab hh
    intro z
    rw [hpt z]
    simp only [M, Ei, ContinuousLinearMap.mul_apply', ContinuousMap.mul_apply, ContinuousMap.coe_mk]
    rw [div_eq_mul_inv]
    ring
  simp only [ℓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, Complex.reCLM_apply,
    smul_eq_mul]
  rw [hT]

/-- **The coherent energy on the concatenated fixed rectangles** with real weights and a fixed denominator. -/
theorem coh_rect (κ : ℝ) (hκ : 0 ≤ κ) {m : ℕ} (a b hh : Fin m → ℝ) (t : Fin m → ℝ) (Dz : ℂ → ℂ)
    (hdc : Continuous (fun θ => (Dz (MPContour.zθ (R52CFPieces.rectFam a b hh (fun i => (t i : ℂ))) θ))⁻¹))
    {H : ℝ} (hzh : ∀ θ, |(MPContour.zθ (R52CFPieces.rectFam a b hh (fun i => (t i : ℂ))) θ).im| ≤ H)
    (u : L2T L) :
    R52CFHartree.coh (kerA (MPContour.nu (m * 4)) κ
      (fun θ => MPContour.uθ κ (R52CFPieces.rectFam a b hh (fun i => (t i : ℂ))) θ *
        (Dz (MPContour.zθ (R52CFPieces.rectFam a b hh (fun i => (t i : ℂ))) θ))⁻¹)
      (physK (L := L) (MPContour.zθ (R52CFPieces.rectFam a b hh (fun i => (t i : ℂ)))))) u =
      ∑ i : Fin m, t i * lam (L := L) κ Dz (a i) (b i) (hh i) u := by
  set P := R52CFPieces.rectFam a b hh (fun i => (t i : ℂ)) with hP
  have hg : Continuous (fun θ => MPContour.uθ κ P θ * (Dz (MPContour.zθ P θ))⁻¹) :=
    (MPContour.continuous_uθ κ P).mul hdc
  obtain ⟨W, hW⟩ := (isCompact_univ (X := MPContour.ThetaSpace (m * 4))).exists_bound_of_continuousOn
    hg.continuousOn
  rw [coh_eq (MPContour.nu (m * 4)) κ _ (MPContour.zθ P) hg (MPContour.continuous_zθ P) hzh
    (fun θ => hW θ (mem_univ θ)) u]
  let f : ℂ → ℂ := fun z => (NormalizedTransfer.productSymbol L κ u z - 1 -
    Complex.exp (Complex.I * z * L)) / Dz z
  have hcont : Continuous (fun θ => MPContour.uθ κ P θ * f (MPContour.zθ P θ)) := by
    have he : (fun θ => MPContour.uθ κ P θ * f (MPContour.zθ P θ)) = fun θ => MPContour.uθ κ P θ *
        ((NormalizedTransfer.productSymbol L κ u (MPContour.zθ P θ) - 1 -
          Complex.exp (Complex.I * MPContour.zθ P θ * L)) * (Dz (MPContour.zθ P θ))⁻¹) := by
      funext θ; simp only [f, div_eq_mul_inv]
    rw [he]
    have hz := MPContour.continuous_zθ P
    refine (MPContour.continuous_uθ κ P).mul (Continuous.mul ?_ hdc)
    exact (((continuous_productSymbol (L := L) κ hκ u).comp hz).sub continuous_const).sub
      (by fun_prop)
  have hint : (∫ θ, MPContour.uθ κ P θ * (Dz (MPContour.zθ P θ))⁻¹ *
      (NormalizedTransfer.productSymbol L κ u (MPContour.zθ P θ) - 1 -
        Complex.exp (Complex.I * MPContour.zθ P θ * L)) ∂(MPContour.nu (m * 4))) =
      ∫ θ, MPContour.uθ κ P θ * f (MPContour.zθ P θ) ∂(MPContour.nu (m * 4)) := by
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [f, div_eq_mul_inv]
    ring
  rw [hint, hP, R52CFPieces.integral_rectFam κ a b hh _ f hcont, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lam
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, f]
  ring

end Physical

end QuantumNLS.R52CFCoh

#print axioms QuantumNLS.R52CFCoh.coh_eq
#print axioms QuantumNLS.R52CFCoh.coh_rect
#print axioms QuantumNLS.R52CFCoh.lam_hasFDerivAt
#print axioms QuantumNLS.R52CFCoh.zθ_mem
