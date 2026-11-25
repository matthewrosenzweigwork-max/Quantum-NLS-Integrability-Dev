import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Sobolev.CMInclusionBasisIndependent
import NlsGge.Ramer.FiniteDivergenceL2

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### The truncation acts on the coordinate basis by `0` or the identity -/

theorem cmCoord_basis_of_ne (c : BoundedCoefficients lower upper) (p : ℤ × Fin 2) (n : ℤ)
    (hn : n ≠ p.1) :
    cmCoord (weightedRealHilbertBasis (cmModeWeight c) p) n = 0 := by
  rw [weightedRealHilbertBasis_apply]
  change (show WeightedHilbert (cmModeWeight c) from
    weightedRealBasisVector (cmModeWeight c) p) n = 0
  rw [weightedRealBasisVector_apply]
  simp [hn]

theorem cmTrunc_basis_of_mem (c : BoundedCoefficients lower upper) (N : ℕ) (p : ℤ × Fin 2)
    (hp : p.1 ∈ symmetricModes N) :
    ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) : actualCMHead c N) :
      ActualCM c) = weightedRealHilbertBasis (cmModeWeight c) p := by
  apply cmCoord_ext
  intro n
  rw [cmCoord_cmTrunc]
  split_ifs with hn
  · rfl
  · have hne : n ≠ p.1 := fun h => hn (h ▸ hp)
    rw [cmCoord_basis_of_ne c p n hne]

theorem cmTrunc_basis_of_not_mem (c : BoundedCoefficients lower upper) (N : ℕ) (p : ℤ × Fin 2)
    (hp : p.1 ∉ symmetricModes N) :
    ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) : actualCMHead c N) :
      ActualCM c) = 0 := by
  apply cmCoord_ext
  intro n
  rw [cmCoord_cmTrunc]
  split_ifs with hn
  · have hne : n ≠ p.1 := fun h => hp (h ▸ hn)
    rw [cmCoord_basis_of_ne c p n hne]
    rfl
  · rfl

theorem eventually_cmTrunc_basis_eq (c : BoundedCoefficients lower upper) (p : ℤ × Fin 2) :
    ∀ᶠ N : ℕ in atTop,
      ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) : actualCMHead c N) :
        ActualCM c) = weightedRealHilbertBasis (cmModeWeight c) p := by
  filter_upwards [eventually_ge_atTop p.1.natAbs] with N hN
  refine cmTrunc_basis_of_mem c N p ?_
  simp only [symmetricModes, Finset.mem_Icc]
  omega

/-- A truncated basis vector is `0` or the basis vector itself, so its image under any
linear map has norm at most that of the image of the basis vector. -/
theorem norm_map_cmTrunc_basis_le (c : BoundedCoefficients lower upper) (N : ℕ)
    (p : ℤ × Fin 2) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ActualCM c →L[ℝ] F) :
    ‖T ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) : actualCMHead c N) :
      ActualCM c)‖ ≤ ‖T (weightedRealHilbertBasis (cmModeWeight c) p)‖ := by
  by_cases hp : p.1 ∈ symmetricModes N
  · rw [cmTrunc_basis_of_mem c N p hp]
  · rw [cmTrunc_basis_of_not_mem c N p hp, map_zero, norm_zero]
    exact norm_nonneg _


/-- Pointwise (in the basis index `p`) convergence of the truncated derivative along a sample
whose realization has the sample as coordinates. -/
theorem tendsto_truncatedDeriv_apply_basis {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, (show WeightedHilbert (fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s z) n = z n) (p : ℤ × Fin 2) :
    Tendsto (fun N : ℕ =>
        ((cmTrunc c N (fderiv ℝ G (headToE c s N (headPt c N z))
            (cmToFullWeightedHilbert c s hs0
              ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) :
                actualCMHead c N) : ActualCM c))) : actualCMHead c N) : ActualCM c))
      atTop (𝓝 (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
        (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)))) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hcont : Continuous (fun x : FullWeightedHilbert c s =>
      fderiv ℝ G x (cmToFullWeightedHilbert c s hs0
        (weightedRealHilbertBasis (cmModeWeight c) p))) :=
    hD.clm_apply continuous_const
  have h1 := tendsto_cmTrunc_comp c s
    (fun x => fderiv ℝ G x (cmToFullWeightedHilbert c s hs0
        (weightedRealHilbertBasis (cmModeWeight c) p))) hcont _ _
    (tendsto_headToE_headPt c s z hz)
  refine h1.congr' ?_
  filter_upwards [eventually_cmTrunc_basis_eq c p] with N hN
  rw [hN]


/-- **Truncated-derivative convergence in Hilbert-Schmidt norm** (v2 ~l.579). The `H`-derivative
of `G_N(x) = P_N G(P_N x)` is `h ↦ P_N DG(P_N x)(i P_N h)`, where `i : H → E_s` is the
(Hilbert-Schmidt) inclusion. Its squared Hilbert-Schmidt distance, computed in the coordinate
basis `b` of `H` as a nonnegative extended-real sum, to `D_H G(x) = DG(x) ∘ i` at `x = ξ(z)`
tends to `0` in `L¹(γ)`. -/
theorem tendsto_lintegral_hs_truncatedDeriv {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs : (1:ℝ)/2 < s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (B : ℝ)
    (hB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖
        ((cmTrunc c N (fderiv ℝ G (headToE c s N (headPt c N z))
            (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
              ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) :
                actualCMHead c N) : ActualCM c))) : actualCMHead c N) : ActualCM c)
        - fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
            (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
              (weightedRealHilbertBasis (cmModeWeight c) p))‖ ^ 2)
      ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : 0 < s)
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  set b := weightedRealHilbertBasis (cmModeWeight c) with hb
  set i := cmToFullWeightedHilbert c s hs0 with hi
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- the summands
  let f : ℕ → (ℤ → ℂ) → ℤ × Fin 2 → ℝ := fun N z p => ‖
        ((cmTrunc c N (fderiv ℝ G (headToE c s N (headPt c N z))
            (i ((cmTrunc c N (b p) : actualCMHead c N) : ActualCM c))) : actualCMHead c N) :
          ActualCM c) - fderiv ℝ G (R z) (i (b p))‖ ^ 2
  -- summable bound
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let σ : ℤ × Fin 2 → ℝ := fun p => ‖i (b p)‖ ^ 2
  have hσ : Summable σ :=
    cmToFullWeightedHilbert_any_sourceBasis_square_summable c s hs b
  have hσ0 : ∀ p, 0 ≤ σ p := fun p => sq_nonneg _
  have hbd : ∀ N z p, f N z p ≤ 4 * B ^ 2 * σ p := by
    intro N z p
    have h1 : ‖((cmTrunc c N (fderiv ℝ G (headToE c s N (headPt c N z))
            (i ((cmTrunc c N (b p) : actualCMHead c N) : ActualCM c))) : actualCMHead c N) :
          ActualCM c)‖ ≤ B * ‖i (b p)‖ := by
      exact (norm_cmTrunc_le c N _).trans (((fderiv ℝ G _).le_opNorm _).trans
        (mul_le_mul (hB _) (norm_map_cmTrunc_basis_le c N p i) (norm_nonneg _) hB0))
    have h2 : ‖fderiv ℝ G (R z) (i (b p))‖ ≤ B * ‖i (b p)‖ :=
      ((fderiv ℝ G _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    have h3 : ‖((cmTrunc c N (fderiv ℝ G (headToE c s N (headPt c N z))
            (i ((cmTrunc c N (b p) : actualCMHead c N) : ActualCM c))) : actualCMHead c N) :
          ActualCM c) - fderiv ℝ G (R z) (i (b p))‖ ≤ 2 * B * ‖i (b p)‖ := by
      refine (norm_sub_le _ _).trans ?_
      linarith
    calc f N z p ≤ (2 * B * ‖i (b p)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 4 * B ^ 2 * σ p := by simp only [σ]; ring
  have hsumm : ∀ N z, Summable (f N z) := fun N z =>
    Summable.of_nonneg_of_le (fun p => sq_nonneg _) (hbd N z) (hσ.mul_left _)
  have hfm : ∀ N p, Measurable (fun z => f N z p) := by
    intro N p
    have hc : Continuous (fun v : actualCMHead c N =>
        ((cmTrunc c N (fderiv ℝ G (headToE c s N v)
            (i ((cmTrunc c N (b p) : actualCMHead c N) : ActualCM c))) : actualCMHead c N) :
          ActualCM c)) :=
      continuous_subtype_val.comp ((cmTrunc c N).continuous.comp
        ((hD.comp (headToE c s N).continuous).clm_apply continuous_const))
    have h1 := hc.measurable.comp (measurable_headPt c N)
    have hc2 : Continuous (fun x : FullWeightedHilbert c s => fderiv ℝ G x (i (b p))) :=
      hD.clm_apply continuous_const
    have h2 := hc2.measurable.comp hRm
    exact (h1.sub h2).norm.pow_const 2
  set F : ℕ → (ℤ → ℂ) → ℝ≥0∞ := fun N z => ∑' p : ℤ × Fin 2, ENNReal.ofReal (f N z p) with hF
  have hFm : ∀ N, Measurable (F N) := fun N =>
    Measurable.tsum (fun p => ENNReal.measurable_ofReal.comp (hfm N p))
  have hae := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have hlim : ∀ᵐ z ∂γ, Tendsto (fun N => F N z) atTop (𝓝 ((fun _ => (0:ℝ≥0∞)) z)) := by
    filter_upwards [hae] with z hz
    have hr : Tendsto (fun N => ∑' p, f N z p) atTop (𝓝 (∑' p : ℤ × Fin 2, (0:ℝ))) := by
      refine tendsto_tsum_of_dominated_convergence (hσ.mul_left (4 * B ^ 2)) ?_
        (Eventually.of_forall fun N p => ?_)
      · intro p
        have h1 := tendsto_truncatedDeriv_apply_basis c s hs0 G hG z hz p
        have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2
        simpa using h2
      · rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hbd N z p
    rw [tsum_zero] at hr
    have h := ENNReal.tendsto_ofReal hr
    rw [ENNReal.ofReal_zero] at h
    refine h.congr (fun N => ?_)
    rw [hF]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) (hsumm N z))
  have hFle : ∀ N z, F N z ≤ ENNReal.ofReal (∑' p, 4 * B ^ 2 * σ p) := by
    intro N z
    rw [hF]
    dsimp only
    rw [← ENNReal.ofReal_tsum_of_nonneg (f := f N z) (fun p => sq_nonneg _) (hsumm N z)]
    exact ENNReal.ofReal_le_ofReal
      ((hsumm N z).tsum_le_tsum (hbd N z) (hσ.mul_left _))
  show Tendsto (fun N => ∫⁻ z, F N z ∂γ) atTop (𝓝 0)
  have := tendsto_lintegral_of_dominated_convergence (μ := γ)
    (F := F) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal (∑' p, 4 * B ^ 2 * σ p)) hFm
    (fun N => Eventually.of_forall fun z => hFle N z)
    (by
      rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.ofReal_ne_top)
    hlim
  simpa using this


/-! ### Hilbert-Schmidt norm of the finite head in the coordinate basis -/

/-- Index set of the coordinate basis vectors lying in the head `P_N H`. -/
def headIndex (N : ℕ) : Finset (ℤ × Fin 2) := symmetricModes N ×ˢ (Finset.univ : Finset (Fin 2))

theorem mem_headIndex {N : ℕ} {p : ℤ × Fin 2} : p ∈ headIndex N ↔ p.1 ∈ symmetricModes N := by
  simp [headIndex]

theorem basis_mem_actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ) (p : ℤ × Fin 2)
    (hp : p.1 ∈ symmetricModes N) :
    weightedRealHilbertBasis (cmModeWeight c) p ∈ actualCMHead c N :=
  fun n hn => cmCoord_basis_of_ne c p n (fun h => hn (h ▸ hp))

theorem repr_basis_eq_zero_of_mem_head (c : BoundedCoefficients lower upper) (N : ℕ)
    (v : ActualCM c) (hv : v ∈ actualCMHead c N) (p : ℤ × Fin 2)
    (hp : p.1 ∉ symmetricModes N) :
    (weightedRealHilbertBasis (cmModeWeight c)).repr v p = 0 := by
  rw [HilbertBasis.repr_apply_apply, weightedRealHilbertBasis_apply,
    weightedRealBasisVector_inner]
  have h0 : (show WeightedHilbert (cmModeWeight c) from v) p.1 = 0 := hv p.1 hp
  have : (weightedIsometry (cmModeWeight c)) (show WeightedHilbert (cmModeWeight c) from v) p.1
      = 0 := by
    rw [weightedIsometry_apply]
    simp [weightedCoordinates, h0]
  rw [this]
  simp

/-- The coordinate basis vectors `b_p`, `p.1 ∈ {-N..N}`, form an orthonormal basis of the head
`P_N H`. -/
def headBasis (c : BoundedCoefficients lower upper) (N : ℕ) :
    OrthonormalBasis (headIndex N) ℝ (actualCMHead c N) :=
  OrthonormalBasis.mk (v := fun p : headIndex N =>
      (⟨weightedRealHilbertBasis (cmModeWeight c) p.1,
        basis_mem_actualCMHead c N p.1 (mem_headIndex.1 p.2)⟩ : actualCMHead c N))
    (by
      have h := ((weightedRealHilbertBasis (cmModeWeight c)).orthonormal.comp
        (fun p : headIndex N => p.1) Subtype.val_injective)
      exact Orthonormal.codRestrict h (actualCMHead c N)
        (fun p => basis_mem_actualCMHead c N p.1 (mem_headIndex.1 p.2)))
    (by
      intro x _
      set b := weightedRealHilbertBasis (cmModeWeight c) with hb
      have hsum : HasSum (fun p : ℤ × Fin 2 => b.repr (x : ActualCM c) p • b p)
          (x : ActualCM c) := b.hasSum_repr _
      have hfin : HasSum (fun p : ℤ × Fin 2 => b.repr (x : ActualCM c) p • b p)
          (∑ p ∈ headIndex N, b.repr (x : ActualCM c) p • b p) :=
        hasSum_sum_of_ne_finset_zero (fun p hp => by
          rw [repr_basis_eq_zero_of_mem_head c N _ x.2 p (fun h => hp (mem_headIndex.2 h)),
            zero_smul])
      have heq : (x : ActualCM c) = ∑ p ∈ headIndex N, b.repr (x : ActualCM c) p • b p :=
        hsum.unique hfin
      have hx : x = ∑ p : headIndex N, b.repr (x : ActualCM c) p.1 •
          (⟨b p.1, basis_mem_actualCMHead c N p.1 (mem_headIndex.1 p.2)⟩ : actualCMHead c N) := by
        apply Subtype.ext
        refine heq.trans ?_
        rw [Submodule.coe_sum]
        exact (Finset.sum_coe_sort (headIndex N)
          (fun p => b.repr (x : ActualCM c) p • b p)).symm
      rw [hx]
      exact Submodule.sum_mem _ (fun p _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self p))))


open scoped RealInnerProductSpace in
/-- The squared Hilbert-Schmidt norm of an endomorphism of a finite-dimensional real inner
product space is the sum of `‖A e_j‖²` over any orthonormal basis `e`. -/
theorem hsNormSq_eq_sum_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V)
    (A : V →L[ℝ] V) : hsNormSq A = ∑ j, ‖A (e j)‖ ^ 2 := by
  rw [← hsNormSq_eq e A, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← e.sum_sq_norm_inner_right (A (e j))]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

theorem headToE_basis (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (p : ℤ × Fin 2) (hp : p.1 ∈ symmetricModes N) :
    headToE c s N ⟨weightedRealHilbertBasis (cmModeWeight c) p,
        basis_mem_actualCMHead c N p hp⟩ =
      cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p) :=
  fullWeighted_ext c s (fun _ => rfl)

/-- **Hilbert-Schmidt norm on the head.** For `g_N(v) = P_N G(P_N v)` on the finite head,
`‖Dg_N(v)‖²_HS` (computed in any orthonormal basis of the head) is the real sum over the
coordinate basis `b` of `H` of `‖P_N DG(P_N v)(i P_N b_p)‖²`. The sum has finite support. -/
theorem hsNormSq_fderiv_truncatedField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c) (hG : Differentiable ℝ G)
    (N : ℕ) (v : actualCMHead c N) :
    hsNormSq (fderiv ℝ (fun w : actualCMHead c N => cmTrunc c N (G (headToE c s N w))) v) =
      ∑' p : ℤ × Fin 2, ‖cmTrunc c N (fderiv ℝ G (headToE c s N v)
        (cmToFullWeightedHilbert c s hs0
          ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) :
            actualCMHead c N) : ActualCM c)))‖ ^ 2 := by
  have hA : HasFDerivAt (fun w : actualCMHead c N => cmTrunc c N (G (headToE c s N w)))
      ((cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) v :=
    (cmTrunc c N).hasFDerivAt.comp v
      ((hG (headToE c s N v)).hasFDerivAt.comp v (headToE c s N).hasFDerivAt)
  rw [hA.fderiv, hsNormSq_eq_sum_norm_sq (headBasis c N)]
  rw [tsum_eq_sum (s := headIndex N)]
  · rw [← Finset.sum_coe_sort (headIndex N)]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq := mem_headIndex.1 q.2
    have hb : (headBasis c N q : actualCMHead c N) =
        ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c N q.1 hq⟩ := by
      exact congrFun (OrthonormalBasis.coe_mk _ _) q
    rw [hb]
    change ‖cmTrunc c N (fderiv ℝ G (headToE c s N v) (headToE c s N
      ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c N q.1 hq⟩))‖ ^ 2 = _
    rw [headToE_basis c s hs0 N q.1 hq, cmTrunc_basis_of_mem c N q.1 hq]
  · intro p hp
    rw [cmTrunc_basis_of_not_mem c N p (fun h => hp (mem_headIndex.2 h)),
      (cmToFullWeightedHilbert c s hs0).map_zero, (fderiv ℝ G (headToE c s N v)).map_zero,
      (cmTrunc c N).map_zero]
    simp

end NlsGge.Ramer
