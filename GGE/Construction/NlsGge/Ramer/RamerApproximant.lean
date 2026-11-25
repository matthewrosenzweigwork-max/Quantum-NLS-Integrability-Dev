import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Sobolev.RealBasis
import NlsGge.Ramer.DivergenceIdentification

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### Generic `L²` dominated convergence -/

/-- `L²` dominated convergence for real-valued functions: pointwise a.e. convergence to `0`
with an `L²` majorant gives convergence to `0` of `eLpNorm _ 2`. -/
theorem tendsto_eLpNorm_two_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hFm : ∀ N, AEStronglyMeasurable (F N) μ) (D : α → ℝ)
    (hD : Integrable (fun z => D z ^ 2) μ)
    (hbd : ∀ N, ∀ᵐ z ∂μ, ‖F N z‖ ≤ D z)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => F N z) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (F N) 2 μ) atTop (𝓝 0) := by
  have hint : ∀ N, eLpNorm (F N) 2 μ = (∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hFm N)]
    simp
  have hlim2 : ∀ᵐ z ∂μ, Tendsto (fun N => ‖F N z‖ₑ ^ (2 : ℝ)) atTop
      (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hlim] with z hz
    have h0 : Tendsto (fun N => ‖F N z‖ₑ) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal (tendsto_norm_zero.comp hz)
      rw [ENNReal.ofReal_zero] at h
      exact h.congr (fun N => ofReal_norm _)
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have hDfin : ∫⁻ z, ENNReal.ofReal (D z ^ 2) ∂μ ≠ ∞ := by
    have := hD.hasFiniteIntegral
    unfold HasFiniteIntegral at this
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun z => ?_) this)
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  have hDCT : Tendsto (fun N => ∫⁻ z, ‖F N z‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun N z => ‖F N z‖ₑ ^ (2 : ℝ)) (f := fun _ => 0)
      (fun z => ENNReal.ofReal (D z ^ 2))
      (fun N => (hFm N).enorm.pow_const _)
      (fun N => by
        filter_upwards [hbd N] with z hz
        have h1 : ‖F N z‖ₑ ≤ ENNReal.ofReal (D z) := by
          rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hz
        have hD0 : 0 ≤ D z := (norm_nonneg _).trans hz
        calc ‖F N z‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (D z) ^ (2 : ℝ) :=
              ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal (D z ^ 2) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hD0 (by norm_num)]
              norm_cast)
      hDfin hlim2
    simpa using this
  simp only [hint]
  have h := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hDCT
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h


/-! ### Coordinate basis of `H` -/

/-- The real coordinate basis index set at level `n`: `W n = symmetricModes n × Fin 2`. -/
abbrev basisIndex (n : ℕ) : Finset (ℤ × Fin 2) :=
  (symmetricModes n) ×ˢ (Finset.univ : Finset (Fin 2))

/-- Pairing against a basis vector depends only on the coordinate at its frequency. -/
theorem inner_basis_congr (c : BoundedCoefficients lower upper) (p : ℤ × Fin 2)
    {x y : ActualCM c} (h : cmCoord x p.1 = cmCoord y p.1) :
    ⟪weightedRealHilbertBasis (cmModeWeight c) p, x⟫ =
      ⟪weightedRealHilbertBasis (cmModeWeight c) p, y⟫ := by
  rw [weightedRealHilbertBasis_apply, weightedRealBasisVector_inner,
    weightedRealBasisVector_inner, weightedIsometry_apply, weightedIsometry_apply]
  have h' : (show WeightedHilbert (cmModeWeight c) from x) p.1 =
      (show WeightedHilbert (cmModeWeight c) from y) p.1 := h
  simp only [weightedCoordinates]
  rw [show ((show WeightedHilbert (cmModeWeight c) from x : WeightedHilbert (cmModeWeight c)) :
      ℤ → ℂ) p.1 = (show WeightedHilbert (cmModeWeight c) from y : ℤ → ℂ) p.1 from h']

/-- The truncation `P_n` acts on the pairing with a basis vector by killing frequencies
outside `-n..n`. -/
theorem inner_basis_cmTrunc (c : BoundedCoefficients lower upper) (n : ℕ) (p : ℤ × Fin 2)
    (y : ActualCM c) :
    ⟪weightedRealHilbertBasis (cmModeWeight c) p, ((cmTrunc c n y : actualCMHead c n) : ActualCM c)⟫ =
      if p.1 ∈ symmetricModes n then ⟪weightedRealHilbertBasis (cmModeWeight c) p, y⟫ else 0 := by
  split_ifs with hp
  · apply inner_basis_congr
    rw [cmCoord_cmTrunc]; simp only [hp, ↓reduceIte]
  · have h0 : cmCoord (((cmTrunc c n y : actualCMHead c n) : ActualCM c)) p.1 =
        cmCoord (0 : ActualCM c) p.1 := by
      rw [cmCoord_cmTrunc]; simp only [hp, ↓reduceIte]; rfl
    rw [inner_basis_congr c p h0]; exact inner_zero_right _

theorem cmCoord_basis_ne (c : BoundedCoefficients lower upper) (p : ℤ × Fin 2) (m : ℤ)
    (hm : m ≠ p.1) : cmCoord (weightedRealHilbertBasis (cmModeWeight c) p) m = 0 := by
  rw [weightedRealHilbertBasis_apply]
  change (show WeightedHilbert (cmModeWeight c) from
    weightedRealBasisVector (cmModeWeight c) p) m = 0
  rw [weightedRealBasisVector_apply]
  simp [hm]

theorem ramerBasis_mem_actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ) (p : ℤ × Fin 2)
    (hp : p.1 ∈ symmetricModes N) :
    weightedRealHilbertBasis (cmModeWeight c) p ∈ actualCMHead c N := by
  intro m hm
  exact cmCoord_basis_ne c p m (fun h => hm (h ▸ hp))

theorem norm_basis (c : BoundedCoefficients lower upper) (p : ℤ × Fin 2) :
    ‖weightedRealHilbertBasis (cmModeWeight c) p‖ = 1 :=
  (weightedRealHilbertBasis (cmModeWeight c)).orthonormal.1 p

/-! ### An orthonormal basis of the head `V_N` from the coordinate basis -/

/-- The coordinate basis vector `b p`, `p ∈ W N`, viewed in the head `V_N`. -/
def headBasisVec (c : BoundedCoefficients lower upper) (N : ℕ) (p : basisIndex N) :
    actualCMHead c N :=
  ⟨weightedRealHilbertBasis (cmModeWeight c) p.1,
    ramerBasis_mem_actualCMHead c N p.1 (Finset.mem_product.1 p.2).1⟩

theorem coe_headBasisVec (c : BoundedCoefficients lower upper) (N : ℕ) (p : basisIndex N) :
    ((headBasisVec c N p : actualCMHead c N) : ActualCM c) =
      weightedRealHilbertBasis (cmModeWeight c) p.1 := rfl

theorem headBasisVec_orthonormal (c : BoundedCoefficients lower upper) (N : ℕ) :
    Orthonormal ℝ (headBasisVec c N) := by
  classical
  rw [orthonormal_iff_ite]
  intro p q
  have h := orthonormal_iff_ite.1 (weightedRealHilbertBasis (cmModeWeight c)).orthonormal p.1 q.1
  change ⟪weightedRealHilbertBasis (cmModeWeight c) p.1,
    weightedRealHilbertBasis (cmModeWeight c) q.1⟫ = _
  rw [h]
  simp only [Subtype.ext_iff]

theorem card_basisIndex (N : ℕ) : Fintype.card (basisIndex N) = 2 * (2 * N + 1) := by
  rw [Fintype.card_coe, Finset.card_product, Finset.card_univ, Fintype.card_fin]
  simp [symmetricModes]
  omega

theorem finrank_actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ) :
    Module.finrank ℝ (actualCMHead c N) = 2 * (2 * N + 1) := by
  rw [(actualCMHeadCoord c N).finrank_eq, Module.finrank_pi_fintype]
  simp
  ring

/-- The orthonormal basis of `V_N` given by the coordinate basis vectors of `W N`. -/
def ramerHeadBasis (c : BoundedCoefficients lower upper) (N : ℕ) :
    OrthonormalBasis (basisIndex N) ℝ (actualCMHead c N) :=
  OrthonormalBasis.mk (headBasisVec_orthonormal c N)
    ((headBasisVec_orthonormal c N).linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [card_basisIndex, finrank_actualCMHead])).ge

theorem ramerHeadBasis_apply (c : BoundedCoefficients lower upper) (N : ℕ) (p : basisIndex N) :
    ramerHeadBasis c N p = headBasisVec c N p := by
  simp [ramerHeadBasis]

/-! ### The two approximants -/

/-- **Ramer's approximant** `a_n(x) = ⟨P_n K x, x⟩ - tr(P_n D K(x))` for `K = G : E_s → H`,
evaluated at the realization of the sample `z`, in the coordinate basis of `H`:
`Σ_{p ∈ W n} (⟨x_n(z), b_p⟩ ⟨b_p, G(ξ z)⟩ - ⟨b_p, DG(ξ z)(i b_p)⟩)`, where `x_n(z)` is the
head point, `ξ` the realization in `E_s`, and `i : H → E_s` the inclusion. -/
def ramerA (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (z : ℤ → ℂ) : ℝ :=
  ∑ p ∈ basisIndex n,
    (⟪(headPt c n z : ActualCM c), weightedRealHilbertBasis (cmModeWeight c) p⟫ *
      ⟪weightedRealHilbertBasis (cmModeWeight c) p,
        G (NlsGge.Measure.fullWeightedSequenceRealization c s z)⟫ -
      ⟪weightedRealHilbertBasis (cmModeWeight c) p,
        fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
          (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))⟫)

/-- The level-`N` cylindrical field `v ↦ P_n G(v)` (`v ∈ V_N`, `v` viewed in `E_s`), `n ≤ N`,
with values in `V_n ⊆ V_N`: range projected, argument not projected beyond level `N`. -/
def gRamer (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (v : actualCMHead c N) : actualCMHead c N :=
  levelIncl c h (cmTrunc c n (G (headToE c s N v)))

theorem fderiv_gRamer (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Differentiable ℝ G) (v : actualCMHead c N) :
    fderiv ℝ (gRamer c s h G) v =
      (levelIncl c h).comp ((cmTrunc c n).comp
        ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) := by
  have h1 := (headToE c s N).hasFDerivAt (x := v)
  have h2 := (hG (headToE c s N v)).hasFDerivAt.comp v h1
  have h3 := (cmTrunc c n).hasFDerivAt.comp v h2
  have h4 := (levelIncl c h).hasFDerivAt.comp v h3
  exact h4.fderiv

theorem headToE_headBasisVec (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (p : basisIndex N) :
    headToE c s N (headBasisVec c N p) =
      cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p.1) := by
  apply fullWeighted_ext
  intro m
  rw [headToE_coord, cmToFullWeightedHilbert_apply]
  rfl

/-! ### Goal 1: the finite identity -/

/-- **Finite identity** (`n ≤ N`): the divergence of the level-`N` cylindrical field
`P_n G(P_N ·)` is Ramer's approximant with `P_N x` in place of `x` in `G`, `DG`. -/
theorem cylDiv_gRamer (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) {n N : ℕ}
    (h : n ≤ N) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ) :
    cylDiv c N (gRamer c s h G) z =
      ∑ p ∈ basisIndex n,
        (⟪(headPt c n z : ActualCM c), weightedRealHilbertBasis (cmModeWeight c) p⟫ *
          ⟪weightedRealHilbertBasis (cmModeWeight c) p,
            G (headToE c s N (headPt c N z))⟫ -
          ⟪weightedRealHilbertBasis (cmModeWeight c) p,
            fderiv ℝ G (headToE c s N (headPt c N z))
              (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))⟫) := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  set x := headPt c N z with hx
  set b := weightedRealHilbertBasis (cmModeWeight c) with hb
  set i := cmToFullWeightedHilbert c s hs0 with hi
  -- the general term at `p`
  let T : ℤ × Fin 2 → ℝ := fun p =>
    ⟪(x : ActualCM c), b p⟫ * ⟪b p, ((cmTrunc c n (G (headToE c s N x)) : actualCMHead c n) :
        ActualCM c)⟫ -
      ⟪b p, ((cmTrunc c n (fderiv ℝ G (headToE c s N x) (i (b p))) : actualCMHead c n) :
        ActualCM c)⟫
  have hterm : ∀ p : basisIndex N,
      ⟪x, ramerHeadBasis c N p⟫ * ⟪ramerHeadBasis c N p, gRamer c s h G x⟫ -
        ⟪ramerHeadBasis c N p, fderiv ℝ (gRamer c s h G) x (ramerHeadBasis c N p)⟫ = T p.1 := by
    intro p
    rw [ramerHeadBasis_apply, fderiv_gRamer c s h G hGd]
    have e1 : ⟪x, headBasisVec c N p⟫ = ⟪(x : ActualCM c), b p.1⟫ := rfl
    have e2 : ⟪headBasisVec c N p, gRamer c s h G x⟫ =
        ⟪b p.1, ((cmTrunc c n (G (headToE c s N x)) : actualCMHead c n) : ActualCM c)⟫ := rfl
    have e3 : ⟪headBasisVec c N p, ((levelIncl c h).comp ((cmTrunc c n).comp
        ((fderiv ℝ G (headToE c s N x)).comp (headToE c s N)))) (headBasisVec c N p)⟫ =
        ⟪b p.1, ((cmTrunc c n (fderiv ℝ G (headToE c s N x) (i (b p.1))) : actualCMHead c n) :
          ActualCM c)⟫ := by
      rw [← headToE_headBasisVec c s hs0 N p]
      rfl
    rw [e1, e2, e3]
  unfold cylDiv
  rw [finiteGaussianDivergence_eq_sum_orthonormalBasis (ramerHeadBasis c N)]
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [Finset.sum_coe_sort (basisIndex N) T]
  have hsub : basisIndex n ⊆ basisIndex N := by
    intro p hp
    exact Finset.mem_product.2 ⟨symmetricModes_mono h (Finset.mem_product.1 hp).1,
      Finset.mem_univ _⟩
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hp1 : p.1 ∈ symmetricModes n := (Finset.mem_product.1 hp).1
    simp only [T]
    rw [inner_basis_cmTrunc, inner_basis_cmTrunc]
    simp only [hp1, ↓reduceIte]
    congr 2
    have hc : cmCoord (x : ActualCM c) p.1 = cmCoord (headPt c n z : ActualCM c) p.1 := by
      rw [hx, cmCoord_headPt, cmCoord_headPt]
      simp only [symmetricModes_mono h hp1, hp1, ↓reduceIte]
    exact (real_inner_comm _ _).symm.trans ((inner_basis_congr c p hc).trans (real_inner_comm _ _))
  · intro p hpN hpn
    have hp1 : p.1 ∉ symmetricModes n := fun h1 => hpn (Finset.mem_product.2 ⟨h1, Finset.mem_univ _⟩)
    simp only [T]
    rw [inner_basis_cmTrunc, inner_basis_cmTrunc]
    simp [hp1]

/-! ### The summand family `ramerSum` -/

/-- Ramer's sum with the point `x ∈ H` and the argument `y ∈ E_s` of `G`, `DG` kept separate:
`Σ_{p ∈ W n} (⟨x, b_p⟩ ⟨b_p, G y⟩ - ⟨b_p, DG(y)(i b_p)⟩)`. -/
def ramerSum (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (x : ActualCM c) (y : FullWeightedHilbert c s) :
    ℝ :=
  ∑ p ∈ basisIndex n,
    (⟪x, weightedRealHilbertBasis (cmModeWeight c) p⟫ *
      ⟪weightedRealHilbertBasis (cmModeWeight c) p, G y⟫ -
      ⟪weightedRealHilbertBasis (cmModeWeight c) p,
        fderiv ℝ G y (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))⟫)

theorem ramerA_eq (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (z : ℤ → ℂ) :
    ramerA c s hs0 n G z = ramerSum c s hs0 n G (headPt c n z : ActualCM c)
      (NlsGge.Measure.fullWeightedSequenceRealization c s z) := rfl

theorem cylDiv_gRamer_eq (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) {n N : ℕ}
    (h : n ≤ N) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ) :
    cylDiv c N (gRamer c s h G) z = ramerSum c s hs0 n G (headPt c n z : ActualCM c)
      (headToE c s N (headPt c N z)) :=
  cylDiv_gRamer c s hs0 h G hG z

theorem continuous_ramerSum (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (x : ActualCM c) :
    Continuous (fun y => ramerSum c s hs0 n G x y) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  unfold ramerSum
  refine continuous_finsetSum _ (fun p _ => ?_)
  exact (continuous_const.mul (continuous_const.inner hG.continuous)).sub
    (continuous_const.inner (hD.clm_apply continuous_const))

theorem norm_inclusion_basis_le_one (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (p : ℤ × Fin 2) :
    ‖cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)‖ ≤ 1 := by
  refine (cmToFullWeightedHilbert_norm_le c s hs0 _).trans ?_
  rw [norm_basis, mul_one]
  exact Real.sqrt_le_one.2 (by norm_num)

theorem abs_ramerSum_sub_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (x : ActualCM c) (y y' : FullWeightedHilbert c s) :
    |ramerSum c s hs0 n G x y - ramerSum c s hs0 n G x y'| ≤
      ((basisIndex n).card : ℝ) * (2 * B) * (1 + ‖x‖) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set i := cmToFullWeightedHilbert c s hs0 with hi
  set b := weightedRealHilbertBasis (cmModeWeight c) with hb
  unfold ramerSum
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (2 * B * (1 + ‖x‖)) (fun p _ => ?_)).trans ?_
  · have hbn : ‖b p‖ = 1 := norm_basis c p
    have h1 : |⟪x, b p⟫| ≤ ‖x‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, mul_one]
    have h2 : |⟪b p, G y⟫ - ⟪b p, G y'⟫| ≤ 2 * B := by
      have e : ⟪b p, G y⟫ - ⟪b p, G y'⟫ = ⟪b p, G y - G y'⟫ := (inner_sub_right _ _ _).symm
      rw [e]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, one_mul]
      refine (norm_sub_le _ _).trans ?_
      linarith [hB y, hB y']
    have h3 : |⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫| ≤ 2 * B := by
      have e : ⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫ =
          ⟪b p, fderiv ℝ G y (i (b p)) - fderiv ℝ G y' (i (b p))⟫ := (inner_sub_right _ _ _).symm
      rw [e]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hbn, one_mul]
      refine (norm_sub_le _ _).trans ?_
      have hib : ‖i (b p)‖ ≤ 1 := norm_inclusion_basis_le_one c s hs0 p
      have e1 : ‖fderiv ℝ G y (i (b p))‖ ≤ B :=
        ((fderiv ℝ G y).le_opNorm _).trans
          (by nlinarith [hDB y, norm_nonneg (i (b p)), norm_nonneg (fderiv ℝ G y)])
      have e2 : ‖fderiv ℝ G y' (i (b p))‖ ≤ B :=
        ((fderiv ℝ G y').le_opNorm _).trans
          (by nlinarith [hDB y', norm_nonneg (i (b p)), norm_nonneg (fderiv ℝ G y')])
      linarith
    have e : ⟪x, b p⟫ * ⟪b p, G y⟫ - ⟪b p, fderiv ℝ G y (i (b p))⟫ -
        (⟪x, b p⟫ * ⟪b p, G y'⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫) =
        ⟪x, b p⟫ * (⟪b p, G y⟫ - ⟪b p, G y'⟫) -
          (⟪b p, fderiv ℝ G y (i (b p))⟫ - ⟪b p, fderiv ℝ G y' (i (b p))⟫) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have hx0 := norm_nonneg x
    have : |⟪x, b p⟫| * |⟪b p, G y⟫ - ⟪b p, G y'⟫| ≤ ‖x‖ * (2 * B) :=
      mul_le_mul h1 h2 (abs_nonneg _) hx0
    nlinarith
  · rw [nsmul_eq_mul]
    nlinarith [norm_nonneg x]

theorem zero_le_of_half_lt {s : ℝ} (hs : (1:ℝ) / 2 < s) : 0 ≤ s := by linarith

theorem measurable_ramerSum_comp (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n : ℕ) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    {α : Type*} [MeasurableSpace α] (X : α → actualCMHead c n) (Y : α → FullWeightedHilbert c s)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun z => ramerSum c s hs0 n G ((X z : actualCMHead c n) : ActualCM c) (Y z)) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  unfold ramerSum
  refine Finset.measurable_sum _ (fun p _ => ?_)
  have f1 : Continuous (fun v : actualCMHead c n =>
      ⟪(v : ActualCM c), weightedRealHilbertBasis (cmModeWeight c) p⟫) :=
    continuous_subtype_val.inner continuous_const
  have f2 : Continuous (fun y : FullWeightedHilbert c s =>
      ⟪weightedRealHilbertBasis (cmModeWeight c) p, G y⟫) :=
    continuous_const.inner hG.continuous
  have f3 : Continuous (fun y : FullWeightedHilbert c s =>
      ⟪weightedRealHilbertBasis (cmModeWeight c) p, fderiv ℝ G y
        (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))⟫) :=
    continuous_const.inner (hD.clm_apply continuous_const)
  exact ((f1.measurable.comp hX).mul (f2.measurable.comp hY)).sub (f3.measurable.comp hY)

/-! ### Goal 2: `L²(γ)` convergence of the cylindrical divergences to Ramer's approximant -/

/-- **`cylDiv (P_n G(P_N ·)) → a_n(G)` in `L²(γ)`** as `N → ∞` (levels `N + n ≥ n`), for `G` of
class `C¹` from `E_s` to `H` with `G` and `DG` bounded by `B`. -/
theorem tendsto_eLpNorm_cylDiv_gRamer (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z =>
        cylDiv c (N + n) (gRamer c s (Nat.le_add_left n N) G) z -
          ramerA c s (zero_le_of_half_lt hs) n G z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have hs0 := zero_le_of_half_lt hs
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set K : ℝ := ((basisIndex n).card : ℝ) * (2 * B) with hK
  set D : (ℤ → ℂ) → ℝ := fun z => K * (1 + ‖headPt c n z‖) with hD
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z =>
    cylDiv c (N + n) (gRamer c s (Nat.le_add_left n N) G) z - ramerA c s hs0 n G z
  have hFeq : ∀ N z, F N z =
      ramerSum c s hs0 n G (headPt c n z : ActualCM c)
        (headToE c s (N + n) (headPt c (N + n) z)) -
      ramerSum c s hs0 n G (headPt c n z : ActualCM c) (R z) := by
    intro N z
    simp only [F]
    rw [cylDiv_gRamer_eq c s hs0 (Nat.le_add_left n N) G hG z, ramerA_eq]
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have e : F N = fun z => ramerSum c s hs0 n G (headPt c n z : ActualCM c)
        (headToE c s (N + n) (headPt c (N + n) z)) -
      ramerSum c s hs0 n G (headPt c n z : ActualCM c) (R z) := funext (hFeq N)
    rw [e]
    exact (measurable_ramerSum_comp c s hs0 n G hG _ _ (measurable_headPt c n)
      ((headToE c s (N + n)).continuous.measurable.comp (measurable_headPt c (N + n)))).sub
      (measurable_ramerSum_comp c s hs0 n G hG _ _ (measurable_headPt c n) hRm)
  have hDint : Integrable (fun z => D z ^ 2) γ := by
    have h1 : Integrable (fun v : actualCMHead c n => K ^ 2 * (1 + ‖v‖) ^ 2)
        (finiteStdGaussian (actualCMHead c n)) :=
      (integrable_pow_one_add_norm 2).const_mul (K ^ 2)
    have h2 := (integrable_comp_headPt_iff c n
      (fun v : actualCMHead c n => K ^ 2 * (1 + ‖v‖) ^ 2) (by fun_prop)).2 h1
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [hD]
    ring
  have hbd : ∀ N, ∀ᵐ z ∂γ, ‖F N z‖ ≤ D z := by
    intro N
    refine Eventually.of_forall fun z => ?_
    rw [hFeq, Real.norm_eq_abs]
    have := abs_ramerSum_sub_le c s hs0 n G B hB hDB (headPt c n z : ActualCM c)
      (headToE c s (N + n) (headPt c (N + n) z)) (R z)
    exact this
  have hae := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := tendsto_headToE_headPt c s z hz
    have h2 : Tendsto (fun N : ℕ => headToE c s (N + n) (headPt c (N + n) z)) atTop (𝓝 (R z)) :=
      h1.comp (tendsto_add_atTop_nat n)
    have h3 := ((continuous_ramerSum c s hs0 n G hG (headPt c n z : ActualCM c)).tendsto
      (R z)).comp h2
    have h4 := h3.sub_const (ramerSum c s hs0 n G (headPt c n z : ActualCM c) (R z))
    rw [sub_self] at h4
    refine h4.congr (fun N => ?_)
    rw [hFeq]
    rfl
  exact tendsto_eLpNorm_two_of_dominated F (fun N => (hFm N).aestronglyMeasurable) D hDint hbd hlim

/-! ### Goal 3: `L²(γ; H)` convergence of the cylindrical fields -/

/-- **`P_n G(P_N ·) → P_n G` in `L²(γ; H)`** as `N → ∞` (levels `N + n ≥ n`), for continuous
`G : E_s → H` bounded by `B`: the `H`-norm of `cylField (P_n G(P_N ·)) - P_n G(ξ)` tends to `0`
in `eLpNorm _ 2 γ`. -/
theorem tendsto_eLpNorm_cylField_gRamer (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => eLpNorm (fun z =>
        ‖cylField c (N + n) (gRamer c s (Nat.le_add_left n N) G) z -
          ((cmTrunc c n (G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :
            actualCMHead c n) : ActualCM c)‖) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let F : ℕ → (ℤ → ℂ) → ℝ := fun N z =>
    ‖cylField c (N + n) (gRamer c s (Nat.le_add_left n N) G) z -
      ((cmTrunc c n (G (R z)) : actualCMHead c n) : ActualCM c)‖
  have hfield : ∀ N z, cylField c (N + n) (gRamer c s (Nat.le_add_left n N) G) z =
      ((cmTrunc c n (G (headToE c s (N + n) (headPt c (N + n) z))) : actualCMHead c n) :
        ActualCM c) := by
    intro N z
    rfl
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    have h1 : Measurable (fun z => cylField c (N + n) (gRamer c s (Nat.le_add_left n N) G) z) := by
      have hc : Continuous (fun v : actualCMHead c (N + n) =>
          ((gRamer c s (Nat.le_add_left n N) G v : actualCMHead c (N + n)) : ActualCM c)) :=
        continuous_subtype_val.comp ((levelIncl c (Nat.le_add_left n N)).continuous.comp
          ((cmTrunc c n).continuous.comp (hG.comp (headToE c s (N + n)).continuous)))
      exact hc.measurable.comp (measurable_headPt c (N + n))
    have h2 : Measurable (fun z => ((cmTrunc c n (G (R z)) : actualCMHead c n) : ActualCM c)) :=
      (continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hG)).measurable.comp hRm
    exact (h1.sub h2).norm
  have hbd : ∀ N, ∀ᵐ z ∂γ, ‖F N z‖ ≤ 2 * B := by
    intro N
    refine Eventually.of_forall fun z => ?_
    simp only [F]
    rw [norm_norm, hfield]
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((cmTrunc c n (G (headToE c s (N + n) (headPt c (N + n) z))) :
        actualCMHead c n) : ActualCM c)‖ ≤ B := (norm_cmTrunc_le c n _).trans (hB _)
    have h2 : ‖((cmTrunc c n (G (R z)) : actualCMHead c n) : ActualCM c)‖ ≤ B :=
      (norm_cmTrunc_le c n _).trans (hB _)
    linarith
  have hae := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 0) := by
    filter_upwards [hae] with z hz
    have h1 := tendsto_headToE_headPt c s z hz
    have h2 : Tendsto (fun N : ℕ => headToE c s (N + n) (headPt c (N + n) z)) atTop (𝓝 (R z)) :=
      h1.comp (tendsto_add_atTop_nat n)
    have hcont : Continuous (fun y : FullWeightedHilbert c s =>
        ((cmTrunc c n (G y) : actualCMHead c n) : ActualCM c)) :=
      continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hG)
    have h3 := (hcont.tendsto (R z)).comp h2
    have h4 := tendsto_iff_norm_sub_tendsto_zero.1 h3
    refine h4.congr (fun N => ?_)
    simp only [F, Function.comp, hfield]
  have hDint : Integrable (fun _ : ℤ → ℂ => (2 * B) ^ 2) γ := integrable_const _
  exact tendsto_eLpNorm_two_of_dominated F (fun N => (hFm N).aestronglyMeasurable) (fun _ => 2 * B)
    hDint hbd hlim

end NlsGge.Ramer
