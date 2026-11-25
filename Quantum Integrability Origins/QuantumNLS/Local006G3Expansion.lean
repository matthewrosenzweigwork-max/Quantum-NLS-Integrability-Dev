import QuantumNLS.Local006G3Asymp
import QuantumNLS.Local006CollectiveF
import QuantumNLS.Local006FirstCoefficientE

/-! LOCAL-006, gap LOCAL006-G3-IDENTIFICATION: the genuine cubic Taylor
coefficient of the actual chart `scalarG`, along every real line, is the
normalized source coefficient

  `factor · [K₃ − ½ (S₂ K₁ + K₁ S₂)]₁₀`,

where `S_k`, `K_k` are the actual LOCAL-005 contour-integrated source words of
the compression `S = E* P_n(u) E` and of the moment `K = E* D_n(u) E`.
Inputs: the frozen exact compression identity (`profile_compression`), the
accepted LOCAL-005 operator-norm degree series (`source_degree_series`), the
zero first projection coefficient, and the free values `S(0) = 1`, `K(0) = 0`.
The coefficient is identified through uniqueness of Taylor coefficients
(`G3Asymp.third_coeff_of_expansion`); no Taylor identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.G3Expansion
open QuantumNLS.LocalSpectral QuantumNLS.Local002Bridge QuantumNLS.PhysicalTensor
  QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.G3Asymp QuantumNLS.Local005 QuantumNLS.Local005.SourceC
  QuantumNLS.Local005.SourceD QuantumNLS.ResetFreeResolventLOCAL001
  QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L κ r : ℝ} [Fact (0 < L)]

lemma hsmall_of (hr2 : r < 2 * Real.pi / L) : r < spacing L / 2 := by
  have h : spacing L / 2 = 2 * Real.pi / L := by unfold spacing; ring
  rw [h]; exact hr2

lemma Fm_apply' (n : ℤ) (X : H2 L →L[ℂ] H2 L) :
    Fm L n X = ContinuousLinearMap.adjoint (embed L n) ∘L X ∘L embed L n := rfl

lemma embed_single (n : ℤ) (i : Fin 2) :
    embed L n (EuclideanSpace.single i (1 : ℂ)) = chi L n i := by
  fin_cases i <;> simp [embed_apply]

lemma adjoint_embed_apply (n : ℤ) (y : H2 L) (i : Fin 2) :
    (ContinuousLinearMap.adjoint (embed L n) y) i = ⟪chi L n i, y⟫_ℂ := by
  have h := EuclideanSpace.inner_single_left i (1 : ℂ) (ContinuousLinearMap.adjoint (embed L n) y)
  rw [ContinuousLinearMap.adjoint_inner_right, embed_single] at h
  simpa using h.symm

lemma entry_apply (n : ℤ) (i j : Fin 2) (X : H2 L →L[ℂ] H2 L) :
    entryFunctional n i j X = ⟪chi L n i, X (chi L n j)⟫_ℂ := rfl

/-- Matrix entries of the free compression are the actual source entry functionals. -/
lemma Fm_apply_apply (n : ℤ) (X : H2 L →L[ℂ] H2 L) (x : E2) (i : Fin 2) :
    (Fm L n X x) i = x 0 * entryFunctional n i 0 X + x 1 * entryFunctional n i 1 X := by
  rw [Fm_apply', ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    adjoint_embed_apply, embed_apply, map_add, map_smul, map_smul, inner_add_right,
    inner_smul_right, inner_smul_right, entry_apply, entry_apply]

lemma Fm_eq_zero (n : ℤ) (X : H2 L →L[ℂ] H2 L)
    (h : ∀ i j, entryFunctional n i j X = 0) : Fm L n X = 0 := by
  refine ContinuousLinearMap.ext fun x => PiLp.ext fun i => ?_
  rw [Fm_apply_apply, h, h]
  simp

/-- Both free projections act trivially under the free compression. -/
lemma Fm_free (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2) (n : ℤ)
    (X : H2 L →L[ℂ] H2 L) :
    Fm L n (freeProj L κ n r * X * freeProj L κ n r) = Fm L n X := by
  have hP := source_freeProj_eq (κ := κ) hL hr hs n
  have h1 : ∀ y, ContinuousLinearMap.adjoint (embed L n) (embed L n y) = y := fun y =>
    congrArg (fun T : E2 →L[ℂ] E2 => T y) (adjoint_embed_comp_embed hL n)
  refine ContinuousLinearMap.ext fun x => ?_
  rw [hP]
  simp only [Fm_apply', ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, h1]

lemma circleRep_zero_ae : circleRep (0 : L2T L) =ᵐ[μI L] fun _ => (0 : ℂ) := by
  have h := toInterval_coe L (0 : L2T L)
  rw [map_zero] at h
  exact h.symm.trans (Lp.coeFn_zero ℂ 2 (μI L))

/-- The actual compression `S(a) = E* P_n(a v) E` along the real line through `v`. -/
def Smat (L κ r : ℝ) [Fact (0 < L)] (v : L2T L) (n : ℤ) (a : ℝ) : Op2 :=
  compressionMatrix L κ (circleRep (a • v)) n r

/-- The actual moment `K(a) = E* D_n(a v) E` along the real line through `v`. -/
def Kmat (L κ r : ℝ) [Fact (0 < L)] (v : L2T L) (n : ℤ) (a : ℝ) : Op2 :=
  ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (circleRep (a • v)) n r ∘L
    embed L n

/-- The compressed LOCAL-005 source words of S. -/
def Sw (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2) (v : L2T L)
    (n : ℤ) (k : ℕ) : Op2 :=
  Fm L n (sourceWord hL hκ hr hs .projection (toInterval L v) n k)

/-- The compressed LOCAL-005 source words of K. -/
def Kw (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2) (v : L2T L)
    (n : ℤ) (k : ℕ) : Op2 :=
  Fm L n (sourceWord hL hκ hr hs .moment (toInterval L v) n k)

/-- The lower-left entry functional `T ↦ T₁₀`. -/
def ell : Op2 →L[ℂ] ℂ :=
  (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).comp (ContinuousLinearMap.apply ℂ E2 (vec2 1 0))

lemma ell_apply (T : Op2) : ell T = T (vec2 1 0) 1 := rfl

/-- The computed normalized source coefficient. -/
def cubicCoeff (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) : ℂ :=
  factor L κ * ell (Kw hL hκ hr hs v n 3 - (1 / 2 : ℂ) •
    (Sw hL hκ hr hs v n 2 * Kw hL hκ hr hs v n 1 + Kw hL hκ hr hs v n 1 * Sw hL hκ hr hs v n 2))

lemma smul_toInterval (v : L2T L) (a : ℝ) :
    (a • (toInterval L v : ScalarInterval L)) = (toInterval L (a • v) : ScalarInterval L) :=
  ((toIntervalR L).map_smul a v).symm

lemma smul_ae (v : L2T L) (a : ℝ) :
    (((a • (toInterval L v : ScalarInterval L) : ScalarInterval L)) : ℝ → ℂ) =ᵐ[μI L]
      circleRep (a • v) := by
  have h1 : (((a • (toInterval L v : ScalarInterval L) : ScalarInterval L)) : ℝ → ℂ) =
      ((toInterval L (a • v) : ScalarInterval L) : ℝ → ℂ) := by
    rw [smul_toInterval]
  rw [h1]
  exact toInterval_coe L (a • v)

theorem S_series (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) (a : ℝ)
    (ha : potentialConstant L r κ * ‖a • (toInterval L v : ScalarInterval L)‖ < 1) :
    HasSum (fun k : ℕ => (a : ℂ) ^ k • Sw hL hκ hr hs v n k) (Smat L κ r v n a) := by
  have h := (Fm L n).hasSum (source_degree_series hL hκ hr hs n (toInterval L v) a ha .projection)
  simp only [map_smul] at h
  have e : Fm L n (sourceCompressed (κ := κ) (r := r) .projection
      (a • (toInterval L v : ScalarInterval L)) n) = Smat L κ r v n a := by
    show Fm L n (freeProj L κ n r * perturbedProj L κ _ n r * freeProj L κ n r) = _
    rw [Fm_free hL hr hs]
    exact QuantumNLS.RB01Bridge.compressionMatrix_congr (smul_ae v a) n r
  rw [← e]
  exact h

theorem K_series (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) (a : ℝ)
    (ha : potentialConstant L r κ * ‖a • (toInterval L v : ScalarInterval L)‖ < 1) :
    HasSum (fun k : ℕ => (a : ℂ) ^ k • Kw hL hκ hr hs v n k) (Kmat L κ r v n a) := by
  have h := (Fm L n).hasSum (source_degree_series hL hκ hr hs n (toInterval L v) a ha .moment)
  simp only [map_smul] at h
  have e : Fm L n (sourceCompressed (κ := κ) (r := r) .moment
      (a • (toInterval L v : ScalarInterval L)) n) = Kmat L κ r v n a := by
    show Fm L n (freeProj L κ n r * dressedIntegral L κ _ n r * freeProj L κ n r) = _
    rw [Fm_free hL hr hs, Fm_apply', Kmat]
    exact congrArg (fun D : H2 L →L[ℂ] H2 L =>
      ContinuousLinearMap.adjoint (embed L n) ∘L D ∘L embed L n)
      (QuantumNLS.RB01Bridge.dressedIntegral_congr (smul_ae v a) n r)
  rw [← e]
  exact h

lemma coeff_zero_of_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℕ → E} {x : E} (h : HasSum (fun k : ℕ => ((0 : ℝ) : ℂ) ^ k • c k) x) : c 0 = x := by
  have h0 : HasSum (fun k : ℕ => ((0 : ℝ) : ℂ) ^ k • c k) (c 0) := by
    have hh := hasSum_single (f := fun k : ℕ => ((0 : ℝ) : ℂ) ^ k • c k) 0
      (fun k hk => by simp [zero_pow hk])
    simpa using hh
  exact h0.unique h

lemma Smat_zero (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2) (v : L2T L) (n : ℤ) :
    Smat L κ r v n 0 = 1 := by
  rw [Smat, zero_smul, QuantumNLS.RB01Bridge.compressionMatrix_congr circleRep_zero_ae n r]
  exact compressionMatrix_zero hL n r (source_freeProj_eq hL hr hs n)

lemma Kmat_zero (hL : 0 < L) (hr : 0 < r) (hs : r < spacing L / 2) (v : L2T L) (n : ℤ) :
    Kmat L κ r v n 0 = 0 := by
  rw [Kmat, zero_smul, QuantumNLS.RB01Bridge.dressedIntegral_congr circleRep_zero_ae n r]
  have hres : ∀ z : ℂ, ‖z - center L n‖ = r →
      ∃ R, IsResolvent L κ (fun _ => 0) (parity n) z R :=
    fun z hz => ⟨free L κ n z, free_isResolvent hL hr hs n hz⟩
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    dressedIntegral_free_embed hL n hr hres x, map_zero]
  rfl

lemma Sw_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) : Sw hL hκ hr hs v n 0 = 1 := by
  have h := S_series hL hκ hr hs v n 0 (by simp)
  rw [coeff_zero_of_hasSum h, Smat_zero hL hr hs]

lemma Kw_zero (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) : Kw hL hκ hr hs v n 0 = 0 := by
  have h := K_series hL hκ hr hs v n 0 (by simp)
  rw [coeff_zero_of_hasSum h, Kmat_zero hL hr hs]

lemma Sw_one (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hs : r < spacing L / 2)
    (v : L2T L) (n : ℤ) : Sw hL hκ hr hs v n 1 = 0 := by
  apply Fm_eq_zero
  intro i j
  have h := (QuantumNLS.Local006.FirstCoefficientE.first_projection_coefficient_zero hL hκ hr hs
    (fun _ : Fin 1 => (toInterval L v : ScalarInterval L)) n i j).1
  have e := orderedSourceWord_repeat hL hκ hr hs .projection (toInterval L v : ScalarInterval L) n 1
  exact (congrArg (entryFunctional n i j) e).symm.trans h

/-- The actual chart along a real line, with the proved remainder. -/
theorem line_expansion (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (hs : r < spacing L / 2) (v : L2T L) (n : ℤ) :
    (fun a : ℝ => scalarG L κ r (a • v) n -
      ((a : ℂ) * (factor L κ * ell (Kw hL hκ hr hs v n 1)) +
        (a : ℂ) ^ 2 * (factor L κ * ell (Kw hL hκ hr hs v n 2)) +
        (a : ℂ) ^ 3 * cubicCoeff hL hκ hr hs v n)) =O[𝓝 0] fun a : ℝ => a ^ 4 := by
  set K0 := potentialConstant L r κ with hK0
  set gR := goodRadius κ L r with hgR
  have hK0n : 0 ≤ K0 := potentialConstant_nonneg L r κ
  have hgRp : 0 < gR := goodRadius_pos κ L r
  set ρ0 : ℝ := min (1 / (K0 * ‖v‖ + 1)) (gR / (‖v‖ + 1)) with hρ0d
  have hρ0 : 0 < ρ0 := lt_min (by positivity) (by positivity)
  have hball : ∀ a : ℝ, |a| < ρ0 →
      K0 * ‖a • (toInterval L v : ScalarInterval L)‖ < 1 ∧ ‖a • v‖ < gR := by
    intro a ha
    have ha1 : |a| < 1 / (K0 * ‖v‖ + 1) := ha.trans_le (min_le_left _ _)
    have ha2 : |a| < gR / (‖v‖ + 1) := ha.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at ha1 ha2
    have hw : ‖a • (toInterval L v : ScalarInterval L)‖ = |a| * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      congr 1
      exact norm_toInterval L v
    have hv : ‖a • v‖ = |a| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    have hn : 0 ≤ ‖v‖ := norm_nonneg v
    have hab : 0 ≤ |a| := abs_nonneg a
    constructor
    · rw [hw]; nlinarith [mul_nonneg hK0n (mul_nonneg hab hn)]
    · rw [hv]; nlinarith
  have hS : ∀ a : ℝ, |a| < ρ0 →
      HasSum (fun k : ℕ => (a : ℂ) ^ k • Sw hL hκ hr hs v n k) (Smat L κ r v n a) :=
    fun a ha => S_series hL hκ hr hs v n a (hball a ha).1
  have hK : ∀ a : ℝ, |a| < ρ0 →
      HasSum (fun k : ℕ => (a : ℂ) ^ k • Kw hL hκ hr hs v n k) (Kmat L κ r v n a) :=
    fun a ha => K_series hL hκ hr hs v n a (hball a ha).1
  have hW0 := Sw_zero hL hκ hr hs v n
  have hW1 := Sw_one hL hκ hr hs v n
  have hV0 := Kw_zero hL hκ hr hs v n
  have hS2 : (fun a : ℝ => Smat L κ r v n a - 1) =O[𝓝 0] fun a : ℝ => a ^ 2 := by
    refine (series_isBigO hρ0 hS 2).congr_left (fun a => ?_)
    simp [Finset.sum_range_succ, hW0, hW1]
  have hS3 : (fun a : ℝ => Smat L κ r v n a - 1 - (a : ℂ) ^ 2 • Sw hL hκ hr hs v n 2) =O[𝓝 0]
      fun a : ℝ => a ^ 3 := by
    refine (series_isBigO hρ0 hS 3).congr_left (fun a => ?_)
    simp [Finset.sum_range_succ, hW0, hW1, sub_sub]
  have hK4 : (fun a : ℝ => Kmat L κ r v n a - ((a : ℂ) • Kw hL hκ hr hs v n 1 +
      (a : ℂ) ^ 2 • Kw hL hκ hr hs v n 2 + (a : ℂ) ^ 3 • Kw hL hκ hr hs v n 3)) =O[𝓝 0]
      fun a : ℝ => a ^ 4 := by
    refine (series_isBigO hρ0 hK 4).congr_left (fun a => ?_)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hV0, pow_zero, pow_one,
      smul_zero, zero_add]
  have hXt : Tendsto (fun a : ℝ => Smat L κ r v n a - 1) (𝓝 0) (𝓝 0) := by
    refine hS2.trans_tendsto ?_
    have h0 : Tendsto (fun a : ℝ => a ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
      (continuous_pow 2).tendsto 0
    simpa using h0
  have hev : ∀ᶠ a in 𝓝 (0 : ℝ), ‖Smat L κ r v n a - 1‖ ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hXt (1 / 2) (by norm_num)] with a ha
    rw [dist_zero_right] at ha
    exact ha.le
  have hInv : (fun a : ℝ => invSqrtM (Smat L κ r v n a) -
      (1 - (1 / 2 : ℂ) • (Smat L κ r v n a - 1))) =O[𝓝 0] fun a : ℝ => a ^ 4 := by
    have h1 : (fun a : ℝ => invSqrtM (Smat L κ r v n a) -
        (1 - (1 / 2 : ℂ) • (Smat L κ r v n a - 1))) =O[𝓝 0]
        fun a : ℝ => ‖Smat L κ r v n a - 1‖ ^ 2 := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [hev] with a ha
      have hb := invSqrtM_sub_le (Smat L κ r v n a - 1) ha
      rw [add_sub_cancel] at hb
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hb
    have h2 : (fun a : ℝ => ‖Smat L κ r v n a - 1‖ ^ 2) =O[𝓝 0] fun a : ℝ => (a ^ 2) ^ 2 :=
      hS2.norm_left.pow 2
    exact (h1.trans h2).congr_right (fun a => by ring)
  have hA : (fun a : ℝ => invSqrtM (Smat L κ r v n a) -
      (1 - ((a : ℂ) ^ 2 / 2) • Sw hL hκ hr hs v n 2)) =O[𝓝 0] fun a : ℝ => a ^ 3 := by
    refine ((hInv.trans (pow_isBigO_pow (by norm_num : 3 ≤ 4))).add
      (hS3.const_smul_left (-(1 / 2 : ℂ)))).congr_left (fun a => ?_)
    simp only [Pi.smul_apply, smul_sub]
    module
  have hprod := normalized_product_cubic hA hK4
  have hmain := (ell.isBigO_comp _ _).trans hprod |>.const_mul_left (factor L κ)
  refine hmain.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ0] with a ha
  have ha' : |a| < ρ0 := by simpa [Real.dist_eq] using ha
  have hpc := profile_compression hL hr hr2 (a • v) (hball a ha').2 n
  have hsc : scalarG L κ r (a • v) n = factor L κ *
      ell (invSqrtM (Smat L κ r v n a) * Kmat L κ r v n a * invSqrtM (Smat L κ r v n a)) := by
    rw [scalarG, Smat, Kmat, ← hpc, ell_apply]
    simp [vec2]
  rw [hsc, cubicCoeff]
  simp only [map_sub, map_add, map_smul, smul_eq_mul]
  ring

/-- **Identification with the computed normalized source coefficient.**
For every analytic map `G` agreeing with the actual chart on a ball, and
every power series `p` of `G` at zero, the cubic Taylor coefficient in every
Fourier coordinate is the normalized source coefficient. -/
theorem p3_coord (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (hs : r < spacing L / 2) {ρ : ℝ} (hρ : 0 < ρ) {G : L2T L → Seq}
    {p : FormalMultilinearSeries ℝ (L2T L) Seq} (hp : HasFPowerSeriesAt G p 0)
    (hGe : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n)
    (v : L2T L) (n : ℤ) :
    p 3 (fun _ => v) n = cubicCoeff hL hκ hr hs v n := by
  apply third_coeff_of_expansion hp v n (factor L κ * ell (Kw hL hκ hr hs v n 1))
    (factor L κ * ell (Kw hL hκ hr hs v n 2))
  refine (line_expansion hL hκ hr hr2 hs v n).congr' ?_ (EventuallyEq.refl _ _)
  have hT : Tendsto (fun a : ℝ => a • v) (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun a : ℝ => a • v) (𝓝 0) (𝓝 ((0 : ℝ) • v)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rwa [zero_smul] at h0
  filter_upwards [hT (ball_mem_nhds (0 : L2T L) hρ)] with a ha
  rw [hGe _ ha n]

end QuantumNLS.Local006.G3Expansion

#print axioms QuantumNLS.Local006.G3Expansion.S_series
#print axioms QuantumNLS.Local006.G3Expansion.K_series
#print axioms QuantumNLS.Local006.G3Expansion.line_expansion
#print axioms QuantumNLS.Local006.G3Expansion.p3_coord

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.G3Expansion." ||
        n.toString.startsWith "_private.QuantumNLS.Local006G3Expansion" then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Local006G3Expansion audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
