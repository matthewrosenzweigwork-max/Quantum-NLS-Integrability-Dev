import NlsGge.Ramer.General.RamerApproximantG
import NlsGge.Ramer.General.TruncatedDerivConvergenceG
import NlsGge.Ramer.RamerApproximantLimit

/-!
# Convergence of Ramer's approximants `a_n(G) → η` in `L²(γ)`, general source law (GB5, part a)

Generalization of `NlsGge/Ramer/RamerApproximantLimit.lean` to a `RamerSetting S`.
Part a: basic facts, the difference field and its per-level `L²` estimate.
The anisotropy-sensitive change is `‖headToE v‖ ≤ √ratioSup ‖v‖` in place of `‖headToE v‖ ≤ ‖v‖`,
which enters the constants of `norm_fderiv_deltaF_le`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Basic facts about the truncation and the head inclusion -/

/-- `P_N b_p` is the basis vector argument of the `p`-th column. -/
def colArg  (N : ℕ)
    (p : ℤ × Fin 2) : S.E :=
  S.incl
    ((S.cmTrunc N (weightedRealHilbertBasis S.cmWeight p) : S.head N) :
      S.H)

theorem norm_colArg_le  (N : ℕ)
    (p : ℤ × Fin 2) :
    ‖S.colArg N p‖ ≤
      ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ :=
  S.norm_map_cmTrunc_basis_le N p (S.incl)

theorem colArg_eq_zero  (N : ℕ)
    (p : ℤ × Fin 2) (hp : p.1 ∉ symmetricModes N) : S.colArg N p = 0 := by
  unfold colArg
  rw [S.cmTrunc_basis_of_not_mem N p hp, map_zero]

theorem eventually_colArg_eq 
    (p : ℤ × Fin 2) :
    ∀ᶠ N : ℕ in atTop, S.colArg N p =
      S.incl (weightedRealHilbertBasis S.cmWeight p) := by
  filter_upwards [S.eventually_cmTrunc_basis_eq p] with N hN
  unfold colArg
  rw [hN]

theorem tendsto_cmTrunc_self  (a : S.H) :
    Tendsto (fun n : ℕ => ((S.cmTrunc n a : S.head n) : S.H)) atTop (𝓝 a) := by
  have h := S.tendsto_cmTrunc_comp (fun _ => a) continuous_const (fun _ => 0) 0
    tendsto_const_nhds
  exact h

/-! ### The difference field and its derivative -/

/-- v2's truncated field `G_N(x) = P_N G(P_N x)` on the finite head `V_N`. -/
def truncF 
    (G : S.E → S.H) (N : ℕ) :
    S.head N → S.head N :=
  fun v => S.cmTrunc N (G (S.headToE N v))

/-- The level-`N` difference `P_n G(P_N ·) - P_N G(P_N ·)` of the two cylindrical fields. -/
def deltaF  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) : S.head N → S.head N :=
  fun v => S.gRamer h G v - S.truncF G N v

/-- The field part `P_n G(P_N v) - P_N G(P_N v)` of the difference, in `H`. -/
def fieldD  (n N : ℕ)
    (G : S.E → S.H) (v : S.head N) : S.H :=
  ((S.cmTrunc n (G (S.headToE N v)) : S.head n) : S.H) -
    ((S.cmTrunc N (G (S.headToE N v)) : S.head N) : S.H)

/-- The `p`-th column of the derivative of the difference field. -/
def colD  (n N : ℕ)
    (G : S.E → S.H) (v : S.head N) (p : ℤ × Fin 2) :
    S.H :=
  ((S.cmTrunc n (fderiv ℝ G (S.headToE N v) (S.colArg N p)) : S.head n) :
      S.H) -
    ((S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.colArg N p)) : S.head N) :
      S.H)

theorem colD_eq_zero  (n N : ℕ)
    (G : S.E → S.H) (v : S.head N) (p : ℤ × Fin 2)
    (hp : p.1 ∉ symmetricModes N) : S.colD n N G v p = 0 := by
  unfold colD
  rw [S.colArg_eq_zero N p hp, (fderiv ℝ G (S.headToE N v)).map_zero,
    (S.cmTrunc n).map_zero, (S.cmTrunc N).map_zero]
  simp

theorem contDiff_deltaF  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (S.deltaF h G) := by
  have h1 : ContDiff ℝ 2 (S.gRamer h G) :=
    (S.levelIncl h).contDiff.comp ((S.cmTrunc n).contDiff.comp (hG.comp (S.headToE N).contDiff))
  have h2 : ContDiff ℝ 2 (S.truncF G N) :=
    (S.cmTrunc N).contDiff.comp (hG.comp (S.headToE N).contDiff)
  exact h1.sub h2

theorem contDiff_truncF  (N : ℕ)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (S.truncF G N) :=
  (S.cmTrunc N).contDiff.comp (hG.comp (S.headToE N).contDiff)

theorem contDiff_gRamer  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (S.gRamer h G) :=
  (S.levelIncl h).contDiff.comp ((S.cmTrunc n).contDiff.comp (hG.comp (S.headToE N).contDiff))

theorem fderiv_deltaF  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (v : S.head N) :
    fderiv ℝ (S.deltaF h G) v =
      (S.levelIncl h).comp ((S.cmTrunc n).comp
        ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) -
      (S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N)) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have h1 := (S.headToE N).hasFDerivAt (x := v)
  have h2 := (hGd (S.headToE N v)).hasFDerivAt.comp v h1
  have h3 := (S.cmTrunc n).hasFDerivAt.comp v h2
  have h4 := (S.levelIncl h).hasFDerivAt.comp v h3
  have h5 := (S.cmTrunc N).hasFDerivAt.comp v h2
  exact (h4.sub h5).fderiv

theorem norm_deltaF_le  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B)
    (v : S.head N) : ‖S.deltaF h G v‖ ≤ 2 * B := by
  unfold deltaF gRamer truncF
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖S.levelIncl h (S.cmTrunc n (G (S.headToE N v)))‖ ≤ B :=
    (S.norm_cmTrunc_le n _).trans (hB _)
  have h2 : ‖S.cmTrunc N (G (S.headToE N v))‖ ≤ B := (S.norm_cmTrunc_le N _).trans (hB _)
  linarith

theorem norm_fderiv_deltaF_le 
    {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (B : ℝ)
    (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (v : S.head N) :
    ‖fderiv ℝ (S.deltaF h G) v‖ ≤ 2 * B * Real.sqrt S.ratioSup := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
  have hκ0 : 0 ≤ Real.sqrt S.ratioSup := Real.sqrt_nonneg _
  rw [S.fderiv_deltaF h G hG]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
  have hw : ‖fderiv ℝ G (S.headToE N v) (S.headToE N w)‖ ≤ B * Real.sqrt S.ratioSup * ‖w‖ :=
    ((fderiv ℝ G _).le_opNorm _).trans
      (by
        calc ‖fderiv ℝ G (S.headToE N v)‖ * ‖S.headToE N w‖
            ≤ B * (Real.sqrt S.ratioSup * ‖w‖) :=
              mul_le_mul (hDB _) (S.norm_headToE_le N w) (norm_nonneg _) hB0
          _ = B * Real.sqrt S.ratioSup * ‖w‖ := by ring)
  have h1 : ‖(S.levelIncl h) (S.cmTrunc n (fderiv ℝ G (S.headToE N v) (S.headToE N w)))‖ ≤
      B * Real.sqrt S.ratioSup * ‖w‖ := (S.norm_cmTrunc_le n _).trans hw
  have h2 : ‖S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.headToE N w))‖ ≤
      B * Real.sqrt S.ratioSup * ‖w‖ :=
    (S.norm_cmTrunc_le N _).trans hw
  calc ‖((S.levelIncl h).comp ((S.cmTrunc n).comp
        ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) -
      (S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) w‖
      = ‖(S.levelIncl h) (S.cmTrunc n (fderiv ℝ G (S.headToE N v) (S.headToE N w))) -
        S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.headToE N w))‖ := rfl
    _ ≤ _ := (norm_sub_le _ _)
    _ ≤ 2 * B * Real.sqrt S.ratioSup * ‖w‖ := by linarith

theorem cylField_deltaF  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (z : ℤ → ℂ) :
    S.cylField N (S.deltaF h G) z = S.fieldD n N G (S.headPt N z) := rfl

theorem cylDiv_deltaF  {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (z : ℤ → ℂ) :
    S.cylDiv N (S.deltaF h G) z =
      S.cylDiv N (S.gRamer h G) z - S.cylDiv N (S.truncF G N) z := by
  unfold cylDiv deltaF
  exact finiteGaussianDivergence_sub _ _ _
    ((S.contDiff_gRamer h G hG).differentiable (by norm_num) _)
    ((S.contDiff_truncF N G hG).differentiable (by norm_num) _)

/-- **Hilbert-Schmidt norm of the derivative of the difference field.** -/
theorem hsNormSq_fderiv_deltaF 
    {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (v : S.head N) :
    hsNormSq (fderiv ℝ (S.deltaF h G) v) =
      ∑ p ∈ headIndex N, ‖S.colD n N G v p‖ ^ 2 := by
  rw [S.fderiv_deltaF h G hG, hsNormSq_eq_sum_norm_sq (S.headBasis N)]
  rw [← Finset.sum_coe_sort (headIndex N)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq := mem_headIndex.1 q.2
  have hb : (S.headBasis N q : S.head N) =
      ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head N q.1 hq⟩ :=
    congrFun (OrthonormalBasis.coe_mk _ _) q
  rw [hb]
  have e1 : S.headToE N ⟨weightedRealHilbertBasis S.cmWeight q.1,
      S.basis_mem_head N q.1 hq⟩ = S.colArg N q.1 := by
    rw [S.headToE_basis N q.1 hq]
    unfold colArg
    rw [S.cmTrunc_basis_of_mem N q.1 hq]
  have e2 : ‖(((S.levelIncl h).comp ((S.cmTrunc n).comp
        ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N))) -
      (S.cmTrunc N).comp ((fderiv ℝ G (S.headToE N v)).comp (S.headToE N)))
        ⟨weightedRealHilbertBasis S.cmWeight q.1,
      S.basis_mem_head N q.1 hq⟩)‖ =
      ‖S.colD n N G v q.1‖ := by
    change ‖(S.levelIncl h) (S.cmTrunc n (fderiv ℝ G (S.headToE N v) (S.headToE N
        ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head N q.1 hq⟩))) -
      S.cmTrunc N (fderiv ℝ G (S.headToE N v) (S.headToE N
        ⟨weightedRealHilbertBasis S.cmWeight q.1, S.basis_mem_head N q.1 hq⟩))‖ =
      _
    rw [e1]
    rfl
  rw [e2]

/-- The same in tsum form (finite support). -/
theorem ofReal_hsNormSq_fderiv_deltaF 
    {n N : ℕ} (h : n ≤ N)
    (G : S.E → S.H) (hG : ContDiff ℝ 2 G) (v : S.head N) :
    ENNReal.ofReal (hsNormSq (fderiv ℝ (S.deltaF h G) v)) =
      ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.colD n N G v p‖ ^ 2) := by
  rw [S.hsNormSq_fderiv_deltaF h G hG v,
    ENNReal.ofReal_sum_of_nonneg (fun p _ => sq_nonneg _)]
  rw [tsum_eq_sum (s := headIndex N)]
  intro p hp
  rw [S.colD_eq_zero n N G v p (fun h' => hp (mem_headIndex.2 h'))]
  simp


/-! ### The per-level `L²` estimate of the divergence of the difference field -/

theorem eLpNorm_cylDiv_deltaF_le 
    (n N : ℕ) (h : n ≤ N) (G : S.E → S.H) (hG : ContDiff ℝ 2 G)
    (B : ℝ) (hB : ∀ x, ‖G x‖ ≤ B) (hDB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    eLpNorm (fun z => S.cylDiv N (S.deltaF h G) z) 2
        (S.γ) ≤
      ((∫⁻ z, ENNReal.ofReal (‖S.fieldD n N G (S.headPt N z)‖ ^ 2)
          ∂(S.γ)) +
        ∫⁻ z, ∑' p : ℤ × Fin 2, ENNReal.ofReal (‖S.colD n N G (S.headPt N z) p‖ ^ 2)
          ∂(S.γ)) ^ (1 / (2 : ℝ)) := by
  set γ := S.γ with hγ
  have hΔ := S.contDiff_deltaF h G hG
  obtain ⟨i1, i2, i3, hle⟩ := S.integral_sq_cylDiv_le_of_growth N (S.deltaF h G) hΔ
    (2 * B * (1 + Real.sqrt S.ratioSup)) 0
    (fun v => by
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
      have := S.norm_deltaF_le h G B hB v
      rw [pow_zero, mul_one]
      nlinarith [mul_nonneg hB0 (Real.sqrt_nonneg S.ratioSup)])
    (fun v => by
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hDB 0)
      have := S.norm_fderiv_deltaF_le h G hG B hDB v
      rw [pow_zero, mul_one]
      nlinarith [mul_nonneg hB0 (Real.sqrt_nonneg S.ratioSup)])
  have hmeas : AEStronglyMeasurable (fun z => S.cylDiv N (S.deltaF h G) z) γ :=
    ((continuous_finiteGaussianDivergence (hΔ.of_le (by norm_num))).measurable.comp
      (S.measurable_headPt N)).aestronglyMeasurable
  rw [NlsGge.Ramer.ApproxLimit.eLpNorm_two_eq_lintegral _ hmeas]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have n1 : 0 ≤ᵐ[γ] fun z => (S.cylDiv N (S.deltaF h G) z) ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have n2 : 0 ≤ᵐ[γ] fun z => ‖S.cylField N (S.deltaF h G) z‖ ^ 2 :=
    Eventually.of_forall fun z => sq_nonneg _
  have n3 : 0 ≤ᵐ[γ] fun z => hsNormSq (fderiv ℝ (S.deltaF h G) (S.headPt N z)) :=
    Eventually.of_forall fun z => hsNormSq_nonneg _
  calc ∫⁻ z, ENNReal.ofReal (S.cylDiv N (S.deltaF h G) z ^ 2) ∂γ
      = ENNReal.ofReal (∫ z, (S.cylDiv N (S.deltaF h G) z) ^ 2 ∂γ) :=
        (ofReal_integral_eq_lintegral_ofReal i1 n1).symm
    _ ≤ ENNReal.ofReal (∫ z, ‖S.cylField N (S.deltaF h G) z‖ ^ 2 ∂γ +
          ∫ z, hsNormSq (fderiv ℝ (S.deltaF h G) (S.headPt N z)) ∂γ) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (∫ z, ‖S.cylField N (S.deltaF h G) z‖ ^ 2 ∂γ) +
          ENNReal.ofReal (∫ z, hsNormSq (fderiv ℝ (S.deltaF h G) (S.headPt N z)) ∂γ) :=
        ENNReal.ofReal_add (integral_nonneg_of_ae n2) (integral_nonneg_of_ae n3)
    _ = (∫⁻ z, ENNReal.ofReal (‖S.cylField N (S.deltaF h G) z‖ ^ 2) ∂γ) +
          ∫⁻ z, ENNReal.ofReal (hsNormSq (fderiv ℝ (S.deltaF h G) (S.headPt N z))) ∂γ := by
        rw [ofReal_integral_eq_lintegral_ofReal i2 n2, ofReal_integral_eq_lintegral_ofReal i3 n3]
    _ = _ := by
        congr 1
        refine lintegral_congr fun z => ?_
        exact S.ofReal_hsNormSq_fderiv_deltaF h G hG _



end NlsGge.Ramer.General.RamerSetting
