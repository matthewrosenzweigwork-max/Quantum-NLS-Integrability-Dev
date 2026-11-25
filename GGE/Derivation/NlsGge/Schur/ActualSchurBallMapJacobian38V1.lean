import NlsGge.Schur.ActualSchurBallMap38V1
import NlsGge.Schur.FiniteLogDetEstimate38V1

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace ENNReal
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

local notation "H1" => WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-!
# Injectivity and Jacobian bounds for `Ψ_{M,N}` (S-Ψ2, F05.05-.06)

For `R ≥ 1`, `A* R⁶ ≤ M` and `K (4R)³ ≤ M`, on the open H¹ ball `‖embed z‖ < R`:
the H¹-orthonormal matrix of `B = DΨ - I` has `‖·‖_{L2op} ≤ 1/4`, `|tr| ≤ 1/4`, `HS ≤ 1/16`;
hence `1/2 ≤ det DΨ ≤ 2`; `Ψ - id` is `1/4`-Lipschitz for the H¹ norm, so `Ψ` is injective.
-/

theorem mulVec_sq_le38 {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (x : ι → ℝ) :
    ∑ r, (∑ c, B r c * x c) ^ 2 ≤ (∑ r, ∑ c, B r c ^ 2) * ∑ c, x c ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

open scoped Matrix.Norms.L2Operator in
/-- L2 operator norm is bounded by the Frobenius norm. -/
theorem l2_le_hs38 {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∑ i, ∑ j, B i j ^ 2 ≤ c ^ 2) : ‖B‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  have key := mulVec_sq_le38 B x.ofLp
  have e1 : ‖Matrix.toEuclideanLin (𝕜 := ℝ) B x‖ ^ 2
      = ∑ r, (∑ c, B r c * x.ofLp c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
  have e2 : ‖x‖ ^ 2 = ∑ c, x.ofLp c ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp
  change ‖Matrix.toEuclideanLin (𝕜 := ℝ) B x‖ ≤ c * ‖x‖
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, e1, e2]
  exact key.trans (by gcongr)

/-- The threshold constant `A*`. -/
def actualSchurJacobianMConstant38 : ℝ :=
  1 + 16 * |actualSchurBallHSConstant38| + 4 * |actualSchurBallTraceConstant38|

theorem actualSchurJacobianMConstant38_ge_one : 1 ≤ actualSchurJacobianMConstant38 := by
  unfold actualSchurJacobianMConstant38
  have := abs_nonneg actualSchurBallHSConstant38
  have := abs_nonneg actualSchurBallTraceConstant38
  linarith

/-- Matrix-level smallness on the ball. -/
theorem actualSchurBallMap38_matrix_small (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    ∑ r, ∑ c, (actualSchurBallMapH1Matrix38 N M z r c) ^ 2 ≤ 1 / 16 ∧
    |Matrix.trace (actualSchurBallMapH1Matrix38 N M z)| ≤ 1 / 4 := by
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hA := actualSchurJacobianMConstant38_ge_one
  have hMge : (1 : ℝ) ≤ M := by nlinarith
  have hM1 : 1 ≤ M := by exact_mod_cast hMge
  have hMpos : (0 : ℝ) < M := by linarith
  have hz' : ‖planeH1Embedding38 N z‖ < R := hz
  have hHS := actualSchurBallMap38_hs_le N M hM1 R hR hK z hz'
  have hTr := actualSchurBallMap38_trace_le N M hM1 R hR hK z hz'
  have h1 := abs_nonneg actualSchurBallHSConstant38
  have h2 := abs_nonneg actualSchurBallTraceConstant38
  have hR4 : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  have hR4' : 0 ≤ R ^ 4 := by positivity
  have hAeq : actualSchurJacobianMConstant38 = 1 + 16 * |actualSchurBallHSConstant38| +
      4 * |actualSchurBallTraceConstant38| := rfl
  constructor
  · refine hHS.trans ?_
    rw [div_le_iff₀ hMpos]
    have : actualSchurBallHSConstant38 ≤ |actualSchurBallHSConstant38| := le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ R ^ 6)]
  · refine hTr.trans ?_
    rw [div_le_iff₀ hMpos]
    have : actualSchurBallTraceConstant38 ≤ |actualSchurBallTraceConstant38| := le_abs_self _
    have e1 := mul_le_mul_of_nonneg_right this hR4'
    have e2 := mul_le_mul_of_nonneg_left hR4 h2
    nlinarith [mul_nonneg h1 (by positivity : (0:ℝ) ≤ R ^ 6)]

open scoped Matrix.Norms.L2Operator in
/-- (1) Operator norm, trace and HS bounds. -/
theorem actualSchurBallMap38_matrix_norm_le (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    ‖actualSchurBallMapH1Matrix38 N M z‖ ≤ 1 / 4 := by
  have := (actualSchurBallMap38_matrix_small N M R hR hM hK z hz).1
  exact l2_le_hs38 _ _ (by norm_num) (by linarith)

open scoped Matrix.Norms.L2Operator in
/-- (1) `1/2 ≤ det DΨ ≤ 2`. -/
theorem actualSchurBallMap38_det_mem_Icc (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    1 / 2 ≤ LinearMap.det (fderiv ℝ (actualSchurBallMap38 N M) z :
        FourierPlane N →ₗ[ℝ] FourierPlane N) ∧
    LinearMap.det (fderiv ℝ (actualSchurBallMap38 N M) z :
        FourierPlane N →ₗ[ℝ] FourierPlane N) ≤ 2 := by
  have hs := actualSchurBallMap38_matrix_small N M R hR hM hK z hz
  have hn := actualSchurBallMap38_matrix_norm_le N M R hR hM hK z hz
  rw [actualSchurBallMap38_det_eq]
  exact det_one_add_mem_Icc _ (by linarith) (by linarith [hs.2]) (by linarith [hs.1])

/-- (1) in the form `ballChangeOfVariables38` needs. -/
theorem actualSchurBallMap38_abs_det_ge (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    (1 / 2 : ℝ) ≤ |(fderiv ℝ (actualSchurBallMap38 N M) z).det| := by
  have := (actualSchurBallMap38_det_mem_Icc N M R hR hM hK z hz).1
  exact this.trans (le_abs_self _)

/-- (3) `HasFDerivWithinAt` on the ball. -/
theorem actualSchurBallMap38_hasFDerivWithinAt (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    HasFDerivWithinAt (actualSchurBallMap38 N M) (fderiv ℝ (actualSchurBallMap38 N M) z)
      {z | planeH1Norm38 N z < R} z := by
  have := actualSchurBallMap38_hasFDerivAt N M R hR hK z hz
  rw [this.fderiv]
  exact this.hasFDerivWithinAt

/-! ### Injectivity -/

theorem planeH1Embedding38_norm_eq_zero (N : ℕ) (w : FourierPlane N)
    (h : ‖planeH1Embedding38 N w‖ = 0) : w = 0 := by
  have h2 := planeH1Embedding38_norm_sq N w
  rw [h] at h2
  funext i
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (1 + (modeIndex N j : ℝ) ^ 2) * ‖w j‖ ^ 2 :=
    fun j _ => by positivity
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by rw [← h2]; simp) i (Finset.mem_univ _)
  have hp : (0 : ℝ) < 1 + (modeIndex N i : ℝ) ^ 2 := by positivity
  have : ‖w i‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp.ne'
    · exact h
  simpa using this

theorem planeH1Embedding38_norm_sq_coords (N : ℕ) (w : FourierPlane N) :
    ‖planeH1Embedding38 N w‖ ^ 2 =
      ∑ c : PlaneRealIndex38 N, (planeH1Scale38 N c * (planeRealBasis38 N).repr w c) ^ 2 := by
  rw [planeH1Embedding38_norm_sq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply, planeRealBasis38_repr,
    planeRealBasis38_repr]
  have hd := planeH1Scale38_sq N (i, 0)
  have hd' : planeH1Scale38 N (i, 1) = planeH1Scale38 N (i, 0) := rfl
  rw [hd', mul_pow, mul_pow]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only at hd
  rw [hd]; ring

/-- The H¹ operator-norm bound on `B` from the Hilbert-Schmidt bound of its H¹ matrix. -/
theorem actualSchurBallMapB38_h1_le (N M : ℕ) (z : FourierPlane N)
    (hHS : ∑ r, ∑ c, (actualSchurBallMapH1Matrix38 N M z r c) ^ 2 ≤ 1 / 16)
    (w : FourierPlane N) :
    ‖planeH1Embedding38 N (actualSchurBallMapB38 N M z w)‖ ≤
      1 / 4 * ‖planeH1Embedding38 N w‖ := by
  have hcoord : ∀ r, planeH1Scale38 N r *
      (planeRealBasis38 N).repr (actualSchurBallMapB38 N M z w) r =
      ∑ c, actualSchurBallMapH1Matrix38 N M z r c *
        (planeH1Scale38 N c * (planeRealBasis38 N).repr w c) := by
    intro r
    have h := LinearMap.toMatrix_mulVec_repr (planeRealBasis38 N) (planeRealBasis38 N)
      (actualSchurBallMapB38 N M z : FourierPlane N →ₗ[ℝ] FourierPlane N) w
    have h' := congrFun h r
    simp only [ContinuousLinearMap.coe_coe] at h'
    rw [← h']
    change _ = ∑ c, _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have := (planeH1Scale38_pos N c).ne'
    simp only [actualSchurBallMapH1Matrix38, actualSchurBallMapPlainMatrix38]
    field_simp
  have key := mulVec_sq_le38 (actualSchurBallMapH1Matrix38 N M z)
    (fun c => planeH1Scale38 N c * (planeRealBasis38 N).repr w c)
  have hsq : ‖planeH1Embedding38 N (actualSchurBallMapB38 N M z w)‖ ^ 2 ≤
      (1 / 4 * ‖planeH1Embedding38 N w‖) ^ 2 := by
    rw [planeH1Embedding38_norm_sq_coords]
    simp_rw [hcoord]
    rw [mul_pow, planeH1Embedding38_norm_sq_coords]
    refine key.trans ?_
    have : 0 ≤ ∑ c : PlaneRealIndex38 N, (planeH1Scale38 N c * (planeRealBasis38 N).repr w c) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  exact le_of_sq_le_sq hsq (by positivity)

theorem ball_convex38 (N : ℕ) (R : ℝ) : Convex ℝ {z : FourierPlane N | planeH1Norm38 N z < R} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, planeH1Norm38] at *
  have : planeH1Embedding38 N (a • x + b • y) = a • planeH1Embedding38 N x + b • planeH1Embedding38 N y := by
    simp
  rw [this]
  calc ‖a • planeH1Embedding38 N x + b • planeH1Embedding38 N y‖
      ≤ ‖a • planeH1Embedding38 N x‖ + ‖b • planeH1Embedding38 N y‖ := norm_add_le _ _
    _ = a * ‖planeH1Embedding38 N x‖ + b * ‖planeH1Embedding38 N y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ < a * R + b * R := by
        rcases ha.eq_or_lt with h | h
        · subst h
          have : b = 1 := by linarith
          subst this
          nlinarith
        · nlinarith
    _ = R := by rw [← add_mul, hab, one_mul]

/-- (2) `Ψ - id` is `1/4`-Lipschitz in the H¹ norm on the open ball. -/
theorem actualSchurBallMap38_sub_id_lipschitz (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ))
    (x y : FourierPlane N) (hx : planeH1Norm38 N x < R) (hy : planeH1Norm38 N y < R) :
    ‖planeH1Embedding38 N ((actualSchurBallMap38 N M y - y) - (actualSchurBallMap38 N M x - x))‖ ≤
      1 / 4 * ‖planeH1Embedding38 N (y - x)‖ := by
  set d : FourierPlane N := y - x with hd
  set Ψ := actualSchurBallMap38 N M with hΨ
  let G : ℝ → H1 := fun t => planeH1EmbeddingR38 N (Ψ (x + t • d) - (x + t • d))
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, planeH1Norm38 N (x + t • d) < R := by
    intro t ht
    have hc := ball_convex38 N R hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
    have : (1 - t) • x + t • y = x + t • d := by
      rw [hd, smul_sub, sub_smul, one_smul]; abel
    rwa [this] at hc
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt G (planeH1EmbeddingR38 N (actualSchurBallMapB38 N M (x + t • d) d))
        (Set.Icc 0 1) t := by
    intro t ht
    have hline : HasDerivAt (fun s : ℝ => x + s • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hΨd := (actualSchurBallMap38_hasFDerivAt N M R hR hK (x + t • d) (hmem t ht)).comp_hasDerivAt
      t hline
    have h2 := (hΨd.sub hline)
    have h3 := (planeH1EmbeddingR38 N).hasFDerivAt.comp_hasDerivAt t h2
    refine h3.hasDerivWithinAt.congr_deriv ?_
    unfold actualSchurBallMapB38
    rw [(actualSchurBallMap38_hasFDerivAt N M R hR hK (x + t • d) (hmem t ht)).fderiv]
    simp
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖planeH1EmbeddingR38 N (actualSchurBallMapB38 N M (x + t • d) d)‖ ≤
        1 / 4 * ‖planeH1Embedding38 N d‖ := by
    intro t ht
    have hs := (actualSchurBallMap38_matrix_small N M R hR hM hK (x + t • d) (hmem t ht)).1
    exact actualSchurBallMapB38_h1_le N M _ hs d
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb (convex_Icc 0 1)
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  simp only [G, one_smul, zero_smul, add_zero, norm_one, sub_zero, mul_one,
    planeH1EmbeddingR38_apply] at this
  have e : x + d = y := by rw [hd]; abel
  rw [e] at this
  rw [← map_sub] at this
  exact this

/-- (2) Injectivity on the open H¹ ball. -/
theorem actualSchurBallMap38_injOn (N M : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (hM : actualSchurJacobianMConstant38 * R ^ 6 ≤ (M : ℝ))
    (hK : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ)) :
    Set.InjOn (actualSchurBallMap38 N M) {z : FourierPlane N | planeH1Norm38 N z < R} := by
  intro x hx y hy hxy
  have h := actualSchurBallMap38_sub_id_lipschitz N M R hR hM hK x y hx hy
  rw [hxy, sub_sub_sub_cancel_left] at h
  have e : x - y = -(y - x) := by abel
  rw [e, map_neg, norm_neg] at h
  have h0 : ‖planeH1Embedding38 N (y - x)‖ = 0 := by
    have := norm_nonneg (planeH1Embedding38 N (y - x))
    linarith
  have := planeH1Embedding38_norm_eq_zero N _ h0
  exact (sub_eq_zero.1 this).symm

end NlsGge.Schur
