import NlsGge.Ramer.RamerApproximant
import NlsGge.Ramer.TruncatedDerivConvergence

/-!
# Convergence of Ramer's approximants `a_n(G) → η` in `L²(γ)`

See `RamerApproximantLimit.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer
namespace ApproxLimit

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### Generic dominated convergence in `ℝ≥0∞` -/

/-- Dominated convergence for `∫⁻ ofReal (F N z)` with a constant bound. -/
theorem tendsto_lintegral_ofReal_of_dominated {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (F : ℕ → α → ℝ) (F0 : α → ℝ) (K : ℝ)
    (hFm : ∀ N, Measurable (F N)) (hbd : ∀ N z, ‖F N z‖ ≤ K)
    (hlim : ∀ᵐ z ∂μ, Tendsto (fun N => F N z) atTop (𝓝 (F0 z))) :
    Tendsto (fun N => ∫⁻ z, ENNReal.ofReal (F N z) ∂μ) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (F0 z) ∂μ)) := by
  refine tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun N z => ENNReal.ofReal (F N z)) (f := fun z => ENNReal.ofReal (F0 z))
    (fun _ => ENNReal.ofReal K)
    (fun N => ENNReal.measurable_ofReal.comp (hFm N))
    (fun N => Eventually.of_forall fun z =>
      ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hbd N z)))
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    ?_
  filter_upwards [hlim] with z hz
  exact ENNReal.tendsto_ofReal hz

/-- Dominated convergence for `∫⁻ ∑' p, ofReal (f N z p)` with a summable bound. -/
theorem tendsto_lintegral_tsum_ofReal_of_dominated {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] [Countable ι]
    (f : ℕ → α → ι → ℝ) (f0 : α → ι → ℝ) (σ : ι → ℝ) (hσ : Summable σ)
    (hf0 : ∀ N z p, 0 ≤ f N z p) (hbd : ∀ N z p, f N z p ≤ σ p)
    (hfm : ∀ N p, Measurable (fun z => f N z p))
    (hlim : ∀ᵐ z ∂μ, ∀ p, Tendsto (fun N => f N z p) atTop (𝓝 (f0 z p))) :
    Tendsto (fun N => ∫⁻ z, ∑' p, ENNReal.ofReal (f N z p) ∂μ) atTop
      (𝓝 (∫⁻ z, ∑' p, ENNReal.ofReal (f0 z p) ∂μ)) := by
  have hsumm : ∀ N z, Summable (f N z) := fun N z =>
    Summable.of_nonneg_of_le (hf0 N z) (hbd N z) hσ
  have hFm : ∀ N, Measurable (fun z => ∑' p, ENNReal.ofReal (f N z p)) := fun N =>
    Measurable.tsum (fun p => ENNReal.measurable_ofReal.comp (hfm N p))
  have hFle : ∀ N z, ∑' p, ENNReal.ofReal (f N z p) ≤ ENNReal.ofReal (∑' p, σ p) := by
    intro N z
    rw [← ENNReal.ofReal_tsum_of_nonneg (hf0 N z) (hsumm N z)]
    exact ENNReal.ofReal_le_ofReal ((hsumm N z).tsum_le_tsum (hbd N z) hσ)
  refine tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun N z => ∑' p, ENNReal.ofReal (f N z p))
    (f := fun z => ∑' p, ENNReal.ofReal (f0 z p))
    (fun _ => ENNReal.ofReal (∑' p, σ p)) hFm
    (fun N => Eventually.of_forall fun z => hFle N z)
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    ?_
  filter_upwards [hlim] with z hz
  have h0 : ∀ p, 0 ≤ f0 z p := fun p => ge_of_tendsto' (hz p) (fun N => hf0 N z p)
  have hle : ∀ p, f0 z p ≤ σ p := fun p => le_of_tendsto' (hz p) (fun N => hbd N z p)
  have hs0 : Summable (f0 z) := Summable.of_nonneg_of_le h0 hle hσ
  have hr : Tendsto (fun N => ∑' p, f N z p) atTop (𝓝 (∑' p, f0 z p)) := by
    refine tendsto_tsum_of_dominated_convergence hσ hz (Eventually.of_forall fun N p => ?_)
    rw [Real.norm_of_nonneg (hf0 N z p)]
    exact hbd N z p
  have h := ENNReal.tendsto_ofReal hr
  rw [ENNReal.ofReal_tsum_of_nonneg h0 hs0] at h
  refine h.congr (fun N => ?_)
  exact ENNReal.ofReal_tsum_of_nonneg (hf0 N z) (hsumm N z)

/-- `eLpNorm _ 2` of a real function as the `1/2` power of the lower integral of `ofReal (f²)`. -/
theorem eLpNorm_two_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ z, ENNReal.ofReal (f z ^ 2) ∂μ) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, ← sq_abs (f z)]


/-! ### Basic facts about the truncation and the head inclusion -/

theorem headToE_eq_cmToFull (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (N : ℕ) (v : actualCMHead c N) :
    headToE c s N v = cmToFullWeightedHilbert c s hs0 (v : ActualCM c) :=
  fullWeighted_ext c s (fun _ => rfl)

theorem norm_headToE_apply_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (N : ℕ) (v : actualCMHead c N) : ‖headToE c s N v‖ ≤ ‖v‖ := by
  rw [headToE_eq_cmToFull c s hs0]
  refine (cmToFullWeightedHilbert_norm_le c s hs0 _).trans ?_
  have h1 : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; norm_num
  calc Real.sqrt (1 / 2 : ℝ) * ‖(v : ActualCM c)‖ ≤ 1 * ‖(v : ActualCM c)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖v‖ := by rw [one_mul]; rfl

theorem norm_levelIncl_apply (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (v : actualCMHead c N) : ‖levelIncl c h v‖ = ‖v‖ := rfl

/-- `P_N b_p` is the basis vector argument of the `p`-th column. -/
def colArg (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (p : ℤ × Fin 2) : FullWeightedHilbert c s :=
  cmToFullWeightedHilbert c s hs0
    ((cmTrunc c N (weightedRealHilbertBasis (cmModeWeight c) p) : actualCMHead c N) :
      ActualCM c)

theorem norm_colArg_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (p : ℤ × Fin 2) :
    ‖colArg c s hs0 N p‖ ≤
      ‖cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)‖ :=
  norm_map_cmTrunc_basis_le c N p (cmToFullWeightedHilbert c s hs0)

theorem colArg_eq_zero (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ)
    (p : ℤ × Fin 2) (hp : p.1 ∉ symmetricModes N) : colArg c s hs0 N p = 0 := by
  unfold colArg
  rw [cmTrunc_basis_of_not_mem c N p hp, map_zero]

theorem eventually_colArg_eq (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (p : ℤ × Fin 2) :
    ∀ᶠ N : ℕ in atTop, colArg c s hs0 N p =
      cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p) := by
  filter_upwards [eventually_cmTrunc_basis_eq c p] with N hN
  unfold colArg
  rw [hN]

theorem tendsto_cmTrunc_self (c : BoundedCoefficients lower upper) (a : ActualCM c) :
    Tendsto (fun n : ℕ => ((cmTrunc c n a : actualCMHead c n) : ActualCM c)) atTop (𝓝 a) := by
  have h := tendsto_cmTrunc_comp c 0 (fun _ => a) continuous_const (fun _ => 0) 0
    tendsto_const_nhds
  exact h

/-! ### The difference field and its derivative -/

/-- v2's truncated field `G_N(x) = P_N G(P_N x)` on the finite head `V_N`. -/
def truncF (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (N : ℕ) :
    actualCMHead c N → actualCMHead c N :=
  fun v => cmTrunc c N (G (headToE c s N v))

/-- The level-`N` difference `P_n G(P_N ·) - P_N G(P_N ·)` of the two cylindrical fields. -/
def deltaF (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) : actualCMHead c N → actualCMHead c N :=
  fun v => gRamer c s h G v - truncF c s G N v

/-- The field part `P_n G(P_N v) - P_N G(P_N v)` of the difference, in `H`. -/
def fieldD (c : BoundedCoefficients lower upper) (s : ℝ) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (v : actualCMHead c N) : ActualCM c :=
  ((cmTrunc c n (G (headToE c s N v)) : actualCMHead c n) : ActualCM c) -
    ((cmTrunc c N (G (headToE c s N v)) : actualCMHead c N) : ActualCM c)

/-- The `p`-th column of the derivative of the difference field. -/
def colD (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (v : actualCMHead c N) (p : ℤ × Fin 2) :
    ActualCM c :=
  ((cmTrunc c n (fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)) : actualCMHead c n) :
      ActualCM c) -
    ((cmTrunc c N (fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)) : actualCMHead c N) :
      ActualCM c)

theorem colD_eq_zero (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (v : actualCMHead c N) (p : ℤ × Fin 2)
    (hp : p.1 ∉ symmetricModes N) : colD c s hs0 n N G v p = 0 := by
  unfold colD
  rw [colArg_eq_zero c s hs0 N p hp, (fderiv ℝ G (headToE c s N v)).map_zero,
    (cmTrunc c n).map_zero, (cmTrunc c N).map_zero]
  simp

theorem contDiff_deltaF (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (deltaF c s h G) := by
  have h1 : ContDiff ℝ 2 (gRamer c s h G) :=
    (levelIncl c h).contDiff.comp ((cmTrunc c n).contDiff.comp (hG.comp (headToE c s N).contDiff))
  have h2 : ContDiff ℝ 2 (truncF c s G N) :=
    (cmTrunc c N).contDiff.comp (hG.comp (headToE c s N).contDiff)
  exact h1.sub h2

theorem contDiff_truncF (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (truncF c s G N) :=
  (cmTrunc c N).contDiff.comp (hG.comp (headToE c s N).contDiff)

theorem contDiff_gRamer (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (gRamer c s h G) :=
  (levelIncl c h).contDiff.comp ((cmTrunc c n).contDiff.comp (hG.comp (headToE c s N).contDiff))

theorem fderiv_deltaF (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (v : actualCMHead c N) :
    fderiv ℝ (deltaF c s h G) v =
      (levelIncl c h).comp ((cmTrunc c n).comp
        ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) -
      (cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N)) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have h1 := (headToE c s N).hasFDerivAt (x := v)
  have h2 := (hGd (headToE c s N v)).hasFDerivAt.comp v h1
  have h3 := (cmTrunc c n).hasFDerivAt.comp v h2
  have h4 := (levelIncl c h).hasFDerivAt.comp v h3
  have h5 := (cmTrunc c N).hasFDerivAt.comp v h2
  exact (h4.sub h5).fderiv

theorem norm_deltaF_le (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B)
    (v : actualCMHead c N) : ‖deltaF c s h G v‖ ≤ 2 * B := by
  unfold deltaF gRamer truncF
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖levelIncl c h (cmTrunc c n (G (headToE c s N v)))‖ ≤ B :=
    (norm_cmTrunc_le c n _).trans (hB _)
  have h2 : ‖cmTrunc c N (G (headToE c s N v))‖ ≤ B := (norm_cmTrunc_le c N _).trans (hB _)
  linarith

theorem norm_fderiv_deltaF_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (v : actualCMHead c N) :
    ‖fderiv ℝ (deltaF c s h G) v‖ ≤ 2 * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  rw [fderiv_deltaF c s h G hG]
  refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun w => ?_)
  have hw : ‖fderiv ℝ G (headToE c s N v) (headToE c s N w)‖ ≤ B * ‖w‖ :=
    ((fderiv ℝ G _).le_opNorm _).trans
      (mul_le_mul (hDB _) (norm_headToE_apply_le c s hs0 N w) (norm_nonneg _) hB0)
  have h1 : ‖(levelIncl c h) (cmTrunc c n (fderiv ℝ G (headToE c s N v) (headToE c s N w)))‖ ≤
      B * ‖w‖ := (norm_cmTrunc_le c n _).trans hw
  have h2 : ‖cmTrunc c N (fderiv ℝ G (headToE c s N v) (headToE c s N w))‖ ≤ B * ‖w‖ :=
    (norm_cmTrunc_le c N _).trans hw
  calc ‖((levelIncl c h).comp ((cmTrunc c n).comp
        ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) -
      (cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) w‖
      = ‖(levelIncl c h) (cmTrunc c n (fderiv ℝ G (headToE c s N v) (headToE c s N w))) -
        cmTrunc c N (fderiv ℝ G (headToE c s N v) (headToE c s N w))‖ := rfl
    _ ≤ _ := (norm_sub_le _ _)
    _ ≤ 2 * B * ‖w‖ := by linarith

theorem cylField_deltaF (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (z : ℤ → ℂ) :
    cylField c N (deltaF c s h G) z = fieldD c s n N G (headPt c N z) := rfl

theorem cylDiv_deltaF (c : BoundedCoefficients lower upper) (s : ℝ) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (z : ℤ → ℂ) :
    cylDiv c N (deltaF c s h G) z =
      cylDiv c N (gRamer c s h G) z - cylDiv c N (truncF c s G N) z := by
  unfold cylDiv deltaF
  exact finiteGaussianDivergence_sub _ _ _
    ((contDiff_gRamer c s h G hG).differentiable (by norm_num) _)
    ((contDiff_truncF c s N G hG).differentiable (by norm_num) _)

/-- **Hilbert-Schmidt norm of the derivative of the difference field.** -/
theorem hsNormSq_fderiv_deltaF (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (v : actualCMHead c N) :
    hsNormSq (fderiv ℝ (deltaF c s h G) v) =
      ∑ p ∈ headIndex N, ‖colD c s hs0 n N G v p‖ ^ 2 := by
  rw [fderiv_deltaF c s h G hG, hsNormSq_eq_sum_norm_sq (headBasis c N)]
  rw [← Finset.sum_coe_sort (headIndex N)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq := mem_headIndex.1 q.2
  have hb : (headBasis c N q : actualCMHead c N) =
      ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c N q.1 hq⟩ :=
    congrFun (OrthonormalBasis.coe_mk _ _) q
  rw [hb]
  have e1 : headToE c s N ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
      basis_mem_actualCMHead c N q.1 hq⟩ = colArg c s hs0 N q.1 := by
    rw [headToE_basis c s hs0 N q.1 hq]
    unfold colArg
    rw [cmTrunc_basis_of_mem c N q.1 hq]
  have e2 : ‖(((levelIncl c h).comp ((cmTrunc c n).comp
        ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N))) -
      (cmTrunc c N).comp ((fderiv ℝ G (headToE c s N v)).comp (headToE c s N)))
        ⟨weightedRealHilbertBasis (cmModeWeight c) q.1,
      basis_mem_actualCMHead c N q.1 hq⟩)‖ =
      ‖colD c s hs0 n N G v q.1‖ := by
    change ‖(levelIncl c h) (cmTrunc c n (fderiv ℝ G (headToE c s N v) (headToE c s N
        ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c N q.1 hq⟩))) -
      cmTrunc c N (fderiv ℝ G (headToE c s N v) (headToE c s N
        ⟨weightedRealHilbertBasis (cmModeWeight c) q.1, basis_mem_actualCMHead c N q.1 hq⟩))‖ =
      _
    rw [e1]
    rfl
  rw [e2]

/-- The same in tsum form (finite support). -/
theorem ofReal_hsNormSq_fderiv_deltaF (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs0 : 0 ≤ s) {n N : ℕ} (h : n ≤ N)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G) (v : actualCMHead c N) :
    ENNReal.ofReal (hsNormSq (fderiv ℝ (deltaF c s h G) v)) =
      ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖colD c s hs0 n N G v p‖ ^ 2) := by
  rw [hsNormSq_fderiv_deltaF c s hs0 h G hG v,
    ENNReal.ofReal_sum_of_nonneg (fun p _ => sq_nonneg _)]
  rw [tsum_eq_sum (s := headIndex N)]
  intro p hp
  rw [colD_eq_zero c s hs0 n N G v p (fun h' => hp (mem_headIndex.2 h'))]
  simp


/-! ### The per-level `L²` estimate of the divergence of the difference field -/

theorem eLpNorm_cylDiv_deltaF_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n N : ℕ) (h : n ≤ N) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 2 G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    eLpNorm (fun z => cylDiv c N (deltaF c s h G) z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      ((∫⁻ z, ENNReal.ofReal (‖fieldD c s n N G (headPt c N z)‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖colD c s hs0 n N G (headPt c N z) p‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) ^ (1 / (2 : ℝ)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hΔ := contDiff_deltaF c s h G hG
  obtain ⟨i1, i2, i3, hle⟩ := integral_sq_cylDiv_le_of_growth c N (deltaF c s h G) hΔ (2 * B) 0
    (fun v => by rw [pow_zero, mul_one]; exact norm_deltaF_le c s h G B hB v)
    (fun v => by rw [pow_zero, mul_one]; exact norm_fderiv_deltaF_le c s hs0 h G hG B hDB v)
  have hmeas : AEStronglyMeasurable (fun z => cylDiv c N (deltaF c s h G) z) γ :=
    ((continuous_finiteGaussianDivergence (hΔ.of_le (by norm_num))).measurable.comp
      (measurable_headPt c N)).aestronglyMeasurable
  rw [eLpNorm_two_eq_lintegral _ hmeas]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have n1 : 0 ≤ᵐ[γ] fun z => (cylDiv c N (deltaF c s h G) z) ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have n2 : 0 ≤ᵐ[γ] fun z => ‖cylField c N (deltaF c s h G) z‖ ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have n3 : 0 ≤ᵐ[γ] fun z => hsNormSq (fderiv ℝ (deltaF c s h G) (headPt c N z)) :=
    Eventually.of_forall fun z => hsNormSq_nonneg _
  calc ∫⁻ z, ENNReal.ofReal (cylDiv c N (deltaF c s h G) z ^ 2) ∂γ
      = ENNReal.ofReal (∫ z, (cylDiv c N (deltaF c s h G) z) ^ 2 ∂γ) :=
        (ofReal_integral_eq_lintegral_ofReal i1 n1).symm
    _ ≤ ENNReal.ofReal (∫ z, ‖cylField c N (deltaF c s h G) z‖ ^ 2 ∂γ +
          ∫ z, hsNormSq (fderiv ℝ (deltaF c s h G) (headPt c N z)) ∂γ) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (∫ z, ‖cylField c N (deltaF c s h G) z‖ ^ 2 ∂γ) +
          ENNReal.ofReal (∫ z, hsNormSq (fderiv ℝ (deltaF c s h G) (headPt c N z)) ∂γ) :=
        ENNReal.ofReal_add (integral_nonneg_of_ae n2) (integral_nonneg_of_ae n3)
    _ = (∫⁻ z, ENNReal.ofReal (‖cylField c N (deltaF c s h G) z‖ ^ 2) ∂γ) +
          ∫⁻ z, ENNReal.ofReal (hsNormSq (fderiv ℝ (deltaF c s h G) (headPt c N z))) ∂γ := by
        rw [ofReal_integral_eq_lintegral_ofReal i2 n2, ofReal_integral_eq_lintegral_ofReal i3 n3]
    _ = _ := by
        congr 1
        refine lintegral_congr fun z => ?_
        exact ofReal_hsNormSq_fderiv_deltaF c s hs0 h G hG _


/-! ### Limits as the level `N → ∞` -/

/-- The limit of the field part: `P_n G(ξ) - G(ξ)`. -/
def fieldLim (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (z : ℤ → ℂ) : ActualCM c :=
  ((cmTrunc c n (G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :
      actualCMHead c n) : ActualCM c) - G (NlsGge.Measure.fullWeightedSequenceRealization c s z)

/-- The limit of the `p`-th column: `(P_n - I) DG(ξ)(i b_p)`. -/
def colLim (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (z : ℤ → ℂ) (p : ℤ × Fin 2) : ActualCM c :=
  ((cmTrunc c n (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
      (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))) :
      actualCMHead c n) : ActualCM c) -
    fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z)
      (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))

theorem norm_fieldD_le (c : BoundedCoefficients lower upper) (s : ℝ) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B)
    (v : actualCMHead c N) : ‖fieldD c s n N G v‖ ≤ 2 * B := by
  unfold fieldD
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((cmTrunc c n (G (headToE c s N v)) : actualCMHead c n) : ActualCM c)‖ ≤ B :=
    (norm_cmTrunc_le c n _).trans (hB _)
  have h2 : ‖((cmTrunc c N (G (headToE c s N v)) : actualCMHead c N) : ActualCM c)‖ ≤ B :=
    (norm_cmTrunc_le c N _).trans (hB _)
  linarith

theorem norm_colD_le (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (v : actualCMHead c N) (p : ℤ × Fin 2) :
    ‖colD c s hs0 n N G v p‖ ≤
      2 * B * ‖cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hw : ‖fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)‖ ≤
      B * ‖cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p)‖ :=
    ((fderiv ℝ G _).le_opNorm _).trans
      (mul_le_mul (hDB _) (norm_colArg_le c s hs0 N p) (norm_nonneg _) hB0)
  unfold colD
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((cmTrunc c n (fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)) :
      actualCMHead c n) : ActualCM c)‖ ≤ _ := (norm_cmTrunc_le c n _).trans hw
  have h2 : ‖((cmTrunc c N (fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)) :
      actualCMHead c N) : ActualCM c)‖ ≤ _ := (norm_cmTrunc_le c N _).trans hw
  linarith

theorem measurable_fieldD_headPt (c : BoundedCoefficients lower upper) (s : ℝ) (n N : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) :
    Measurable (fun z => ‖fieldD c s n N G (headPt c N z)‖ ^ 2) := by
  have hc : Continuous (fun v : actualCMHead c N => ‖fieldD c s n N G v‖ ^ 2) := by
    unfold fieldD
    refine Continuous.pow (Continuous.norm (Continuous.sub ?_ ?_)) 2
    · exact continuous_subtype_val.comp ((cmTrunc c n).continuous.comp
        (hG.comp (headToE c s N).continuous))
    · exact continuous_subtype_val.comp ((cmTrunc c N).continuous.comp
        (hG.comp (headToE c s N).continuous))
  exact hc.measurable.comp (measurable_headPt c N)

theorem measurable_colD_headPt (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s)
    (n N : ℕ) (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G)
    (p : ℤ × Fin 2) :
    Measurable (fun z => ‖colD c s hs0 n N G (headPt c N z) p‖ ^ 2) := by
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hc : Continuous (fun v : actualCMHead c N => ‖colD c s hs0 n N G v p‖ ^ 2) := by
    unfold colD
    have hc0 : Continuous (fun v : actualCMHead c N =>
        fderiv ℝ G (headToE c s N v) (colArg c s hs0 N p)) :=
      (hD.comp (headToE c s N).continuous).clm_apply continuous_const
    refine Continuous.pow (Continuous.norm (Continuous.sub ?_ ?_)) 2
    · exact continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hc0)
    · exact continuous_subtype_val.comp ((cmTrunc c N).continuous.comp hc0)
  exact hc.measurable.comp (measurable_headPt c N)

theorem tendsto_lintegral_fieldD (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (n : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : Continuous G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ENNReal.ofReal (‖fieldD c s n (N + n) G (headPt c (N + n) z)‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (‖fieldLim c s n G z‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val))) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  refine tendsto_lintegral_ofReal_of_dominated (μ := γ)
    (fun N z => ‖fieldD c s n (N + n) G (headPt c (N + n) z)‖ ^ 2)
    (fun z => ‖fieldLim c s n G z‖ ^ 2) ((2 * B) ^ 2)
    (fun N => measurable_fieldD_headPt c s n (N + n) G hG) ?_ ?_
  · intro N z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fieldD_le c s n (N + n) G B hB _) 2
  · filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
    have h1 := tendsto_headToE_headPt c s z hz
    have h2 := h1.comp (tendsto_add_atTop_nat n)
    have hcont : Continuous (fun y : FullWeightedHilbert c s =>
        ((cmTrunc c n (G y) : actualCMHead c n) : ActualCM c)) :=
      continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hG)
    have t1 := (hcont.tendsto _).comp h2
    have t2 := (tendsto_cmTrunc_comp c s G hG _ _ h1).comp (tendsto_add_atTop_nat n)
    exact (t1.sub t2).norm.pow 2

theorem tendsto_lintegral_colD (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (hs0 : 0 ≤ s) (n : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun N : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖colD c s hs0 n (N + n) G (headPt c (N + n) z) p‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop
      (𝓝 (∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖colLim c s hs0 n G z p‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val))) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  set b := weightedRealHilbertBasis (cmModeWeight c) with hb
  set i := cmToFullWeightedHilbert c s hs0 with hi
  have hσ : Summable (fun p : ℤ × Fin 2 => 4 * B ^ 2 * ‖i (b p)‖ ^ 2) :=
    (cmToFullWeightedHilbert_any_sourceBasis_square_summable c s hs b).mul_left _
  refine tendsto_lintegral_tsum_ofReal_of_dominated (μ := γ)
    (fun N z p => ‖colD c s hs0 n (N + n) G (headPt c (N + n) z) p‖ ^ 2)
    (fun z p => ‖colLim c s hs0 n G z p‖ ^ 2) _ hσ
    (fun N z p => sq_nonneg _) ?_
    (fun N p => measurable_colD_headPt c s hs0 n (N + n) G hG p) ?_
  · intro N z p
    calc ‖colD c s hs0 n (N + n) G (headPt c (N + n) z) p‖ ^ 2
        ≤ (2 * B * ‖i (b p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_colD_le c s hs0 n (N + n) G B hDB _ p) 2
      _ = 4 * B ^ 2 * ‖i (b p)‖ ^ 2 := by ring
  · filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz p
    have h1 := tendsto_headToE_headPt c s z hz
    have h2 := h1.comp (tendsto_add_atTop_nat n)
    -- `P_N`-part: the previously proved convergence of the truncated derivative
    have t2 := (tendsto_truncatedDeriv_apply_basis c s hs0 G hG z hz p).comp
      (tendsto_add_atTop_nat n)
    -- the untruncated part: `DG(y_N)(i P_N b_p) → DG(ξ)(i b_p)`
    have hcont : Continuous (fun x : FullWeightedHilbert c s => fderiv ℝ G x (i (b p))) :=
      hD.clm_apply continuous_const
    have t0 : Tendsto (fun N : ℕ => fderiv ℝ G (headToE c s (N + n) (headPt c (N + n) z))
        (colArg c s hs0 (N + n) p)) atTop
        (𝓝 (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p)))) := by
      refine ((hcont.tendsto _).comp h2).congr' ?_
      filter_upwards [(tendsto_add_atTop_nat n).eventually
        (eventually_colArg_eq c s hs0 p)] with N hN
      rw [hN]
      rfl
    have t1 := ((continuous_subtype_val.comp (cmTrunc c n).continuous).tendsto _).comp t0
    exact (t1.sub t2).norm.pow 2


/-! ### The tail terms tend to `0` as `n → ∞` -/

theorem measurable_fieldLim_sq (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) :
    Measurable (fun z => ‖fieldLim c s n G z‖ ^ 2) := by
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have h1 : Measurable (fun z => ((cmTrunc c n
      (G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) : actualCMHead c n) :
        ActualCM c)) :=
    (continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hG)).measurable.comp hRm
  have h2 : Measurable (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :=
    hG.measurable.comp hRm
  exact (h1.sub h2).norm.pow_const 2

theorem measurable_colLim_sq (c : BoundedCoefficients lower upper) (s : ℝ) (hs0 : 0 ≤ s) (n : ℕ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : ContDiff ℝ 1 G) (p : ℤ × Fin 2) :
    Measurable (fun z => ‖colLim c s hs0 n G z p‖ ^ 2) := by
  let _ : MeasurableSpace (ActualCM c) := borel _
  have _ : BorelSpace (ActualCM c) := ⟨rfl⟩
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hD : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hc : Continuous (fun x : FullWeightedHilbert c s =>
      fderiv ℝ G x (cmToFullWeightedHilbert c s hs0 (weightedRealHilbertBasis (cmModeWeight c) p))) :=
    hD.clm_apply continuous_const
  have h1 := (continuous_subtype_val.comp ((cmTrunc c n).continuous.comp hc)).measurable.comp hRm
  have h2 := hc.measurable.comp hRm
  exact (h1.sub h2).norm.pow_const 2

theorem tendsto_lintegral_fieldLim_zero (c : BoundedCoefficients lower upper) (s : ℝ)
    (G : FullWeightedHilbert c s → ActualCM c) (hG : Continuous G) (B : ℝ)
    (hB : ∀ x, ‖G x‖ ≤ B) :
    Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (‖fieldLim c s n G z‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have h := tendsto_lintegral_ofReal_of_dominated
    (μ := NlsGge.Measure.fullWeightSequenceGaussian c.val)
    (fun n z => ‖fieldLim c s n G z‖ ^ 2) (fun _ => (0 : ℝ)) ((2 * B) ^ 2)
    (fun n => measurable_fieldLim_sq c s n G hG) ?_ ?_
  · simpa using h
  · intro n z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    unfold fieldLim
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((cmTrunc c n (G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) :
        actualCMHead c n) : ActualCM c)‖ ≤ B := (norm_cmTrunc_le c n _).trans (hB _)
    linarith [hB (NlsGge.Measure.fullWeightedSequenceRealization c s z)]
  · refine Eventually.of_forall fun z => ?_
    have h1 := tendsto_cmTrunc_self c (G (NlsGge.Measure.fullWeightedSequenceRealization c s z))
    have h2 := (h1.sub_const (G (NlsGge.Measure.fullWeightedSequenceRealization c s z))).norm.pow 2
    simpa [fieldLim] using h2

theorem tendsto_lintegral_colLim_zero (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (hs0 : 0 ≤ s) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun n : ℕ => ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖colLim c s hs0 n G z p‖ ^ 2)
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  set b := weightedRealHilbertBasis (cmModeWeight c) with hb
  set i := cmToFullWeightedHilbert c s hs0 with hi
  have hσ : Summable (fun p : ℤ × Fin 2 => 4 * B ^ 2 * ‖i (b p)‖ ^ 2) :=
    (cmToFullWeightedHilbert_any_sourceBasis_square_summable c s hs b).mul_left _
  have h := tendsto_lintegral_tsum_ofReal_of_dominated
    (μ := NlsGge.Measure.fullWeightSequenceGaussian c.val)
    (fun n z p => ‖colLim c s hs0 n G z p‖ ^ 2) (fun _ _ => (0 : ℝ)) _ hσ
    (fun N z p => sq_nonneg _) ?_ (fun n p => measurable_colLim_sq c s hs0 n G hG p) ?_
  · simpa using h
  · intro n z p
    have hw : ‖fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p))‖ ≤
        B * ‖i (b p)‖ :=
      ((fderiv ℝ G _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hDB _) (norm_nonneg _))
    have h3 : ‖colLim c s hs0 n G z p‖ ≤ 2 * B * ‖i (b p)‖ := by
      unfold colLim
      refine (norm_sub_le _ _).trans ?_
      have h1 := (norm_cmTrunc_le c n
        (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p)))).trans hw
      have h1' : ‖((cmTrunc c n
        (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p))) :
          actualCMHead c n) : ActualCM c)‖ ≤ B * ‖i (b p)‖ := h1
      linarith
    calc ‖colLim c s hs0 n G z p‖ ^ 2 ≤ (2 * B * ‖i (b p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 4 * B ^ 2 * ‖i (b p)‖ ^ 2 := by ring
  · refine Eventually.of_forall fun z p => ?_
    have h1 := tendsto_cmTrunc_self c
      (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p)))
    have h2 := (h1.sub_const
      (fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) (i (b p)))).norm.pow 2
    simpa [colLim] using h2


/-! ### The bound for fixed `n` -/

/-- For each `n`, `‖a_n(G) - η‖_{L²(γ)}` is bounded by the square root of the `n`-th tail
`E‖(P_n - I) G(ξ)‖² + E ∑_p ‖(P_n - I) DG(ξ)(i b_p)‖²`, provided the divergences of the truncated
fields converge to `η` in `L²(γ)`. -/
theorem eLpNorm_ramerA_sub_le (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (n : ℕ) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ)
    (hηlim : Tendsto (fun N : ℕ => eLpNorm (fun z =>
        cylDiv c N (fun v => cmTrunc c N (G (headToE c s N v))) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    eLpNorm (fun z => ramerA c s (zero_le_of_half_lt hs) n G z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      ((∫⁻ z, ENNReal.ofReal (‖fieldLim c s n G z‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2,
          ENNReal.ofReal (‖colLim c s (zero_le_of_half_lt hs) n G z p‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) ^ (1 / (2 : ℝ)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hs0 := zero_le_of_half_lt hs
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  -- the three terms
  let a : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun z =>
    cylDiv c (N + n) (gRamer c s (Nat.le_add_left n N) G) z -
      ramerA c s hs0 n G z) 2 γ
  let Q : ℕ → ℝ≥0∞ := fun N =>
    (∫⁻ z, ENNReal.ofReal (‖fieldD c s n (N + n) G (headPt c (N + n) z)‖ ^ 2) ∂γ) +
      ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖colD c s hs0 n (N + n) G (headPt c (N + n) z) p‖ ^ 2) ∂γ
  let t : ℕ → ℝ≥0∞ := fun N => eLpNorm (fun z =>
    cylDiv c (N + n) (fun v => cmTrunc c (N + n) (G (headToE c s (N + n) v))) z - η z) 2 γ
  have hbound : ∀ N : ℕ, eLpNorm (fun z => ramerA c s hs0 n G z - η z) 2 γ ≤
      a N + (Q N) ^ (1 / (2 : ℝ)) + t N := by
    intro N
    have h := Nat.le_add_left n N
    have e : (fun z => ramerA c s hs0 n G z - η z) =
        (-(fun z => cylDiv c (N + n) (gRamer c s h G) z - ramerA c s hs0 n G z) +
          (fun z => cylDiv c (N + n) (deltaF c s h G) z)) +
        (fun z => cylDiv c (N + n) (fun v => cmTrunc c (N + n) (G (headToE c s (N + n) v))) z
          - η z) := by
      funext z
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [cylDiv_deltaF c s h G hG]
      change _ = -(cylDiv c (N + n) (gRamer c s h G) z - ramerA c s hs0 n G z) +
        (cylDiv c (N + n) (gRamer c s h G) z - cylDiv c (N + n) (truncF c s G (N + n)) z) +
        (cylDiv c (N + n) (truncF c s G (N + n)) z - η z)
      ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine add_le_add ((eLpNorm_add_le (by norm_num)).trans ?_) le_rfl
    refine add_le_add ?_ ?_
    · rw [eLpNorm_neg]
    · exact eLpNorm_cylDiv_deltaF_le c s hs0 n (N + n) h G hG B hB hDB
  have ha : Tendsto a atTop (𝓝 0) :=
    tendsto_eLpNorm_cylDiv_gRamer c s hs n G hG1 B hB hDB
  have ht : Tendsto t atTop (𝓝 0) := hηlim.comp (tendsto_add_atTop_nat n)
  have hQ : Tendsto Q atTop (𝓝 ((∫⁻ z, ENNReal.ofReal (‖fieldLim c s n G z‖ ^ 2) ∂γ) +
      ∫⁻ z, ∑' p : ℤ × Fin 2,
        ENNReal.ofReal (‖colLim c s hs0 n G z p‖ ^ 2) ∂γ)) :=
    (tendsto_lintegral_fieldD c s hs n G hG1.continuous B hB).add
      (tendsto_lintegral_colD c s hs hs0 n G hG1 B hDB)
  have hQ' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hQ
  have hT := (ha.add hQ').add ht
  rw [zero_add, add_zero] at hT
  exact ge_of_tendsto' hT hbound

/-- The tail `n ↦ E‖(P_n - I) G(ξ)‖² + E ∑_p ‖(P_n - I) DG(ξ)(i b_p)‖²` tends to `0`. -/
theorem tendsto_tail_zero (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1:ℝ) / 2 < s) (G : FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 1 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    Tendsto (fun n : ℕ =>
      ((∫⁻ z, ENNReal.ofReal (‖fieldLim c s n G z‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2,
          ENNReal.ofReal (‖colLim c s (zero_le_of_half_lt hs) n G z p‖ ^ 2)
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
  have h := (tendsto_lintegral_fieldLim_zero c s G hG.continuous B hB).add
    (tendsto_lintegral_colLim_zero c s hs (zero_le_of_half_lt hs) G hG B hDB)
  rw [add_zero] at h
  have h' := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h'
  exact h'

end ApproxLimit

/-! ### Main results -/

/-- **H2: Ramer's approximants converge in `L²(γ)`.** If `G : E_s → H` is `C²` with `G`, `DG`
bounded by `B`, and the divergences `δ_cyl(P_N G(P_N ·))` of the truncated fields converge to `η`
in `L²(γ)`, then Ramer's approximants `a_n(G) = ⟨P_n G, x_n⟩ - tr(P_n DG)` converge to `η` in
`L²(γ)`. -/
theorem tendsto_eLpNorm_ramerA {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1:ℝ) / 2 < s) (G : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c)
    (hG : ContDiff ℝ 2 G) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B)
    (η : (ℤ → ℂ) → ℝ)
    (hη : MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hηlim : Tendsto (fun N : ℕ => eLpNorm (fun z =>
        cylDiv c N (fun v => cmTrunc c N (G (headToE c s N v))) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm (fun z =>
        ramerA c s (zero_le_of_half_lt hs) n G z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  -- `hη` is not needed: `eLpNorm_add_le` carries no measurability hypothesis.
  have _ := hη
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ApproxLimit.tendsto_tail_zero c s hs G (hG.of_le (by norm_num)) B hB hDB)
    (fun _ => zero_le)
    (fun n => ApproxLimit.eLpNorm_ramerA_sub_le c s hs n G hG B hB hDB η hηlim)

/-- **H3: locality of Ramer's approximant.** If two fields agree on an open set `U` of `E_s`,
then `a_n(G)` and `a_n(K)` agree at every sample whose realization lies in `U`. -/
theorem ramerA_congr_of_eqOn {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs0 : 0 ≤ s) (G K : NlsGge.Pilot.FullWeightedHilbert c s → ActualCM c)
    {U : Set (NlsGge.Pilot.FullWeightedHilbert c s)} (hU : IsOpen U) (h : Set.EqOn G K U)
    (n : ℕ) (z : ℤ → ℂ)
    (hz : NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ U) :
    ramerA c s hs0 n G z = ramerA c s hs0 n K z := by
  have hev : G =ᶠ[𝓝 (NlsGge.Measure.fullWeightedSequenceRealization c s z)] K :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hz) h
  have hd : fderiv ℝ G (NlsGge.Measure.fullWeightedSequenceRealization c s z) =
      fderiv ℝ K (NlsGge.Measure.fullWeightedSequenceRealization c s z) := hev.fderiv_eq
  unfold ramerA
  rw [h hz, hd]

end NlsGge.Ramer
