import Mathlib
import QuantumNLS.RB01L2Factor

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-7: the `ℓ²` families of `2 × 2` matrices.

Source (collective_actions.tex:272-307): "Identify each free two-dimensional range with `ℂ²`, and set
`S_n = P_n⁰ P_n P_n⁰`, `K_n = P_n⁰ Q_n P_n⁰`. Then `S_n - 1` and `K_n` are holomorphic `ℓ²` families of matrices. ...
we may arrange `sup_{|n|>N} ‖S_n - 1‖ < 1/2`. Define the inverse square root by its power series at `1`, and put
`B_n = p_n 1 + S_n^{-1/2} K_n S_n^{-1/2}`. Thus `B_n - p_n 1` is a holomorphic `ℓ²` family."

Here, on the real slice (real analyticity on `L²(0,L;ℂ)`, as in stages RB01-3 and RB01-6), with `E = embed L n`
(the ordered free basis `(χ_{n,0}, χ_{n,1})`), `S_n = E^* P_n(u) E = compressionMatrix`, `Q_n = dressedIntegral`
(`(2πi)⁻¹ ∮ (z - p_n)(z - 𝓛_u)⁻¹ dz = (𝓛 - p_n) P_n`) and `K_n = E^* Q_n E`:
* `Phi j`: the bounded linear map `ℓ²(ℤ; H) → ℓ²(ℤ; Mat₂)`, `x ↦ (E_n^* (v ↦ v_j x_n))_n`; the matrix families are
  `Phi 0 (col₀) + Phi 1 (col₁)` with the analytic columns `FP, FD` of `RB01L2Factor.tail_columns_analytic`.
* `dressed_zero_chi`: `Q_n(0) χ_{n,j} = 0`, so `E^*(Q_n(u) - Q_n(0))E = K_n`.
* `isA`: the inverse square root power series `∑_k binom(-1/2,k) M^k` in the Banach algebra `ℓ∞(ℤ; Mat₂)` (fibre
  `MatW`, definitionally `B(ℂ²)`), analytic on the open unit ball (`isA_analyticAt`), acting componentwise as
  `invSqrtM (1 + M_n)` (`isA_apply`).
* `mulL`, `mulR`: the bounded bilinear products `ℓ∞ × ℓ² → ℓ²`, `ℓ² × ℓ∞ → ℓ²` (`incl : ℓ² ⊂ ℓ∞`).
* **`tail_matrix_analytic`**: for every `u₀` there are `N`, `ρ > 0` and maps `Sf, Kf, Bf : L² → ℓ²(ℤ; Mat₂)`, real
  analytic on `B(u₀, ρ)`, with, for `|n| > N`: `‖S_n - 1‖ ≤ 1/2`, `Sf(u)_n = S_n - 1`, `Kf(u)_n = K_n`,
  `Bf(u)_n = S_n^{-1/2} K_n S_n^{-1/2}` (`invSqrtM`, the power series at `1`), and all three `0` for `|n| ≤ N`.
* **`tail_entries_analytic`**: each matrix entry `n ↦ ⟨e_i, (B_n - p_n) e_j⟩` (in particular `a_n - p_n`, `b_n`,
  `b_n^♯`) is real analytic into `ℓ²(ℤ; ℂ)` on `B(u₀, ρ)`.

The identification of this `B_n` with `reducedMatrix2` (which uses `U_n^*`) and the doublet form are left to
RB01Spectral, as scheduled. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01Matrix
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Rank
  QuantumNLS.Local002SA QuantumNLS.Local002Basis QuantumNLS.RB01FourierAction QuantumNLS.RB01SquareSmall
  QuantumNLS.RB01Resolvent QuantumNLS.RB01Columns QuantumNLS.RB01L2Columns QuantumNLS.RB01L2Factor

variable {L κ : ℝ}

/-- `2 × 2` matrices, `B(ℂ²)`. -/
abbrev Mat := E2 →L[ℂ] E2
/-- `ℓ²(ℤ; Mat₂)`. -/
abbrev MS := lp (fun _ : ℤ => Mat) 2
/-! ### Fibrewise bounded maps on `ℓ²` -/

section Fiber

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem l2_norm_le {x : lp (fun _ : ℤ => F) 2} {y : lp (fun _ : ℤ => E) 2} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, ‖x n‖ ≤ c * ‖y n‖) : ‖x‖ ≤ c * ‖y‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (mul_nonneg hc (norm_nonneg _)) ?_
  have hy := lp.norm_rpow_eq_tsum hp y
  have hxs := (lp.memℓp x).summable hp
  have hys := (lp.memℓp y).summable hp
  rw [Real.mul_rpow hc (norm_nonneg _), hy, ← tsum_mul_left]
  refine hxs.tsum_le_tsum (fun n => ?_) (hys.mul_left _)
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h n) hp.le

theorem memℓp2_of_le' {f : ℤ → F} (y : lp (fun _ : ℤ => E) 2) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n, ‖f n‖ ≤ c * ‖y n‖) : Memℓp f 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _) (fun n => ?_)
    (((lp.memℓp y).summable hp).mul_left (c ^ (2 : ℝ≥0∞).toReal))
  rw [← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h n) hp.le

theorem fiber_le (T : ℤ → E →L[ℂ] F) {C : ℝ} (hT : ∀ n, ‖T n‖ ≤ C) (x : lp (fun _ : ℤ => E) 2) (n : ℤ) :
    ‖T n (x n)‖ ≤ C * ‖x n‖ :=
  ((T n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))

/-- The fibrewise map `x ↦ (T_n x_n)_n` on `ℓ²`, for a uniformly bounded family `T_n`. -/
def fiberMap (T : ℤ → E →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C) (hT : ∀ n, ‖T n‖ ≤ C) :
    lp (fun _ : ℤ => E) 2 →L[ℂ] lp (fun _ : ℤ => F) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => T n (x n), memℓp2_of_le' x hC (fiber_le T hT x)⟩
      map_add' := fun x y => lp.ext (funext fun n => by
        show T n ((x + y) n) = T n (x n) + T n (y n)
        rw [lp.coeFn_add, Pi.add_apply, map_add])
      map_smul' := fun c x => lp.ext (funext fun n => by
        show T n ((c • x) n) = c • T n (x n)
        rw [lp.coeFn_smul, Pi.smul_apply, map_smul]) }
    C (fun x => l2_norm_le hC (fiber_le T hT x))

theorem fiberMap_apply (T : ℤ → E →L[ℂ] F) {C : ℝ} (hC : 0 ≤ C) (hT : ∀ n, ‖T n‖ ≤ C)
    (x : lp (fun _ : ℤ => E) 2) (n : ℤ) : (fiberMap T hC hT x : ℤ → F) n = T n (x n) := rfl

end Fiber

/-! ### The column-to-matrix maps -/

/-- `v ↦ v_j a : ℂ² → H`. -/
def colj (j : Fin 2) (a : H2 L) : E2 →L[ℂ] H2 L :=
  LinearMap.mkContinuous
    { toFun := fun v => v j • a
      map_add' := fun v w => by
        show (v + w) j • a = v j • a + w j • a
        rw [PiLp.add_apply, add_smul]
      map_smul' := fun c v => by
        show (c • v) j • a = c • (v j • a)
        rw [PiLp.smul_apply, smul_eq_mul, mul_smul] }
    ‖a‖ (fun v => by
      show ‖v j • a‖ ≤ ‖a‖ * ‖v‖
      rw [norm_smul, mul_comm ‖a‖]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v j) (norm_nonneg a))

theorem colj_apply (j : Fin 2) (a : H2 L) (v : E2) : colj j a v = v j • a := rfl

/-- `a ↦ E_n^* (v ↦ v_j a) : H → Mat₂`. -/
def colOp (hL : 0 < L) (n : ℤ) (j : Fin 2) : H2 L →L[ℂ] Mat :=
  LinearMap.mkContinuous
    { toFun := fun a => ContinuousLinearMap.adjoint (embed L n) ∘L colj j a
      map_add' := fun a b => ContinuousLinearMap.ext fun v => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, colj_apply, smul_add, map_add]
      map_smul' := fun c a => ContinuousLinearMap.ext fun v => by
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, colj_apply, RingHom.id_apply]
        rw [smul_comm, map_smul] }
    1 (fun a => by
      have hE : ‖ContinuousLinearMap.adjoint (embed L n)‖ ≤ 1 := by
        rw [LinearIsometryEquiv.norm_map]; exact norm_embed_le hL n
      have hc : ‖colj j a‖ ≤ ‖a‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun v => by
        rw [colj_apply, norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v j) (norm_nonneg a)
      show ‖ContinuousLinearMap.adjoint (embed L n) ∘L colj j a‖ ≤ 1 * ‖a‖
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul hE hc (norm_nonneg _) zero_le_one))

theorem colOp_apply (hL : 0 < L) (n : ℤ) (j : Fin 2) (a : H2 L) (v : E2) :
    colOp hL n j a v = ContinuousLinearMap.adjoint (embed L n) (v j • a) := rfl

theorem colOp_le (hL : 0 < L) (n : ℤ) (j : Fin 2) : ‖colOp hL n j‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **`Phi j : ℓ²(ℤ; H) → ℓ²(ℤ; Mat₂)`**, `x ↦ (E_n^* (v ↦ v_j x_n))_n`. -/
def Phi (hL : 0 < L) (j : Fin 2) : lp (fun _ : ℤ => H2 L) 2 →L[ℂ] MS :=
  fiberMap (fun n => colOp hL n j) zero_le_one (fun n => colOp_le hL n j)

theorem Phi_apply (hL : 0 < L) (j : Fin 2) (x : lp (fun _ : ℤ => H2 L) 2) (n : ℤ) (v : E2) :
    (Phi hL j x : ℤ → Mat) n v = ContinuousLinearMap.adjoint (embed L n) (v j • x n) := rfl

/-- `(Phi 0 x + Phi 1 y)_n = E_n^* A E_n` whenever `x_n = A χ_{n,0}`, `y_n = A χ_{n,1}`. -/
theorem Phi_pair (hL : 0 < L) (x y : lp (fun _ : ℤ => H2 L) 2) (n : ℤ) (A : H2 L →L[ℂ] H2 L)
    (hx : x n = A (chi L n 0)) (hy : y n = A (chi L n 1)) :
    ((Phi hL 0 x + Phi hL 1 y : MS) : ℤ → Mat) n =
      ContinuousLinearMap.adjoint (embed L n) ∘L A ∘L embed L n := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [lp.coeFn_add, Pi.add_apply, ContinuousLinearMap.add_apply, Phi_apply, Phi_apply, hx, hy, ← map_add,
    ← map_smul, ← map_smul, ← map_add]
  rfl

theorem Phi_zero (hL : 0 < L) (x y : lp (fun _ : ℤ => H2 L) 2) (n : ℤ) (hx : x n = 0) (hy : y n = 0) :
    ((Phi hL 0 x + Phi hL 1 y : MS) : ℤ → Mat) n = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [lp.coeFn_add, Pi.add_apply, ContinuousLinearMap.add_apply, Phi_apply, Phi_apply, hx, hy, smul_zero,
    smul_zero, map_zero, add_zero]
  rfl

/-! ### `Q_n(0) χ_{n,j} = 0` -/

theorem dressed_zero_chi {r : ℝ} (S : Setup L r) (n : ℤ) (j : Fin 2) :
    dressedIntegral L κ (fun _ => 0) n r (chi L n j) = 0 := by
  have hsph : ∀ z ∈ sphere (pm L n : ℂ) r, ‖z - (pm L n : ℂ)‖ = r := fun z hz => by
    simpa [mem_sphere_iff_norm] using hz
  have hc0 : ContinuousOn (fun z => (z - (pm L n : ℂ)) • resolvent L κ (fun _ => 0) (parity n) z)
      (sphere (pm L n : ℂ) r) :=
    (continuous_id.sub continuous_const).continuousOn.smul (continuousOn_resolvent _ (M := 2 / r)
      (div_nonneg zero_le_two S.hr.le) (fun z hz => free_res_annulus (κ := κ) S.hL S.hr S.hr2
        (by rw [hsph z hz]; linarith [S.hr]) (hsph z hz).le))
  have e : (∮ z in C((pm L n : ℂ), r), ((z - (pm L n : ℂ)) • resolvent L κ (fun _ => 0) (parity n) z)
      (chi L n j)) = ∮ _z in C((pm L n : ℂ), r), chi L n j := by
    refine circleIntegral.integral_congr S.hr.le fun z hz => ?_
    have hz' := hsph z hz
    have hne : z ≠ (pm L n : ℂ) := by
      intro h; rw [h, sub_self, norm_zero] at hz'; exact S.hr.ne hz'
    have hR : resolvent L κ (fun _ => 0) (parity n) z (chi L n j) =
        ((z - (pm L n : ℂ))⁻¹ : ℂ) • chi L n j := res_chi S.hL j (free_at (κ := κ) S hz').1 rfl hne
    have hne' : z - (pm L n : ℂ) ≠ 0 := sub_ne_zero.2 hne
    show (z - (pm L n : ℂ)) • resolvent L κ (fun _ => 0) (parity n) z (chi L n j) = chi L n j
    rw [hR, smul_smul, mul_inv_cancel₀ hne', one_smul]
  show (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • circleIntegral (fun z => (z - (pm L n : ℂ)) •
    resolvent L κ (fun _ => 0) (parity n) z) (pm L n : ℂ) r) (chi L n j) = 0
  rw [ContinuousLinearMap.smul_apply, circleIntegral_apply _ (hc0.circleIntegrable S.hr.le), e,
    (diffContOnCl_const (c := chi L n j)).circleIntegral_eq_zero S.hr.le, smul_zero]

/-! ### The Banach algebra `ℓ∞(ℤ; Mat₂)` -/

/-- A copy of `Mat₂` (definitionally `E2 →L[ℂ] E2`) carrying only the bundled normed-algebra instances; it is the fibre
of the Banach algebra `ℓ∞(ℤ; Mat₂)` (this keeps instance unification on `lp` cheap). -/
def MatW : Type := E2 →L[ℂ] E2

instance : NormedRing MatW := ContinuousLinearMap.toNormedRing
instance : NormedAlgebra ℂ MatW := ContinuousLinearMap.toNormedAlgebra
instance : NormedSpace ℝ MatW := inferInstanceAs (NormedSpace ℝ (E2 →L[ℂ] E2))
instance : IsScalarTower ℝ ℂ MatW := inferInstanceAs (IsScalarTower ℝ ℂ (E2 →L[ℂ] E2))
instance : CompleteSpace MatW := inferInstanceAs (CompleteSpace (E2 →L[ℂ] E2))
instance : NormOneClass MatW := inferInstanceAs (NormOneClass (E2 →L[ℂ] E2))

/-- `ℓ∞(ℤ; Mat₂)` (a unital Banach algebra). -/
abbrev MI := lp (fun _ : ℤ => MatW) ∞

def toW (M : Mat) : MatW := M
def ofW (M : MatW) : Mat := M

theorem norm_toW (M : Mat) : ‖toW M‖ = ‖M‖ := rfl
theorem norm_ofW (M : MatW) : ‖ofW M‖ = ‖M‖ := rfl
theorem ofW_add (a b : MatW) : ofW (a + b) = ofW a + ofW b := rfl
theorem ofW_smul (c : ℂ) (a : MatW) : ofW (c • a) = c • ofW a := rfl
theorem ofW_pow (a : MatW) (k : ℕ) : ofW (a ^ k) = ofW a ^ k := rfl
theorem toW_add (a b : Mat) : toW (a + b) = toW a + toW b := rfl
theorem toW_smul (c : ℂ) (a : Mat) : toW (c • a) = c • toW a := rfl

/-- `ofW` as a continuous linear map. -/
def ofWL : MatW →L[ℂ] Mat :=
  LinearMap.mkContinuous
    { toFun := ofW
      map_add' := ofW_add
      map_smul' := ofW_smul }
    1 (fun M => by show ‖ofW M‖ ≤ 1 * ‖M‖; rw [one_mul, norm_ofW])

theorem ofWL_apply (M : MatW) : ofWL M = ofW M := rfl

/-! ### The inverse square root series in `ℓ∞(ℤ; Mat₂)` -/

/-- The inverse square root series `∑_k binom(-1/2,k) M^k` (of `1 + M`) in `ℓ∞(ℤ; Mat₂)`. -/
def isA (M : MI) : MI := ∑' k : ℕ, (invSqrtCoeff k : ℂ) • M ^ k

theorem isA_analyticAt {M0 : MI} (h : ‖M0‖ < 1) : AnalyticAt ℂ isA M0 := by
  let c : ℕ → ℂ := fun k => (invSqrtCoeff k : ℂ)
  let p : FormalMultilinearSeries ℂ MI MI := FormalMultilinearSeries.ofScalars MI c
  have hrad : (1 : ℝ≥0∞) ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun s hs => ?_
    have hs1 : (s : ℝ) < 1 := by exact_mod_cast hs
    refine p.le_radius_of_bound 1 (fun n => ?_)
    have h1 : ‖p n‖ ≤ 1 := by
      refine (FormalMultilinearSeries.ofScalars_norm MI c n).le.trans ?_
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_invSqrtCoeff_le n
    have h2 : (s : ℝ) ^ n ≤ 1 := pow_le_one₀ s.2 hs1.le
    calc ‖p n‖ * (s : ℝ) ^ n ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hball := p.hasFPowerSeriesOnBall (lt_of_lt_of_le one_pos hrad)
  have hmem : M0 ∈ Metric.eball (0 : MI) p.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    have h1 : ‖M0‖ₑ < 1 := by rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_lt_one.2 h
    exact lt_of_lt_of_le h1 hrad
  have han := hball.analyticAt_of_mem hmem
  have hfun : p.sum = isA := FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := MI) c
  rw [← hfun]; exact han

theorem summable_isA {M : MI} (h : ‖M‖ < 1) : Summable fun k : ℕ => (invSqrtCoeff k : ℂ) • M ^ k := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) h) fun k => ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc |invSqrtCoeff k| * ‖M ^ k‖ ≤ 1 * ‖M‖ ^ k :=
        mul_le_mul (abs_invSqrtCoeff_le k) (norm_pow_le _ _) (norm_nonneg _) zero_le_one
    _ = ‖M‖ ^ k := one_mul _

/-- Evaluation `ℓ∞(ℤ; Mat₂) → Mat₂` at `n`. -/
def evI (n : ℤ) : MI →L[ℂ] Mat :=
  LinearMap.mkContinuous
    { toFun := fun x => ofW (x n)
      map_add' := fun x y => by
        show ofW ((x + y) n) = ofW (x n) + ofW (y n)
        rw [lp.coeFn_add, Pi.add_apply, ofW_add]
      map_smul' := fun c x => by
        show ofW ((c • x) n) = c • ofW (x n)
        rw [lp.coeFn_smul, Pi.smul_apply, ofW_smul] }
    1 fun x => by
      show ‖ofW (x n)‖ ≤ 1 * ‖x‖
      rw [one_mul, norm_ofW]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero x n

theorem evI_apply (n : ℤ) (x : MI) : evI n x = ofW (x n) := rfl

/-- `(isA M)_n = (1 + M_n)^{-1/2}` (as the series `invSqrtM` at `C = 1 + M_n`). -/
theorem isA_apply {M : MI} (h : ‖M‖ < 1) (n : ℤ) {C : Mat} (hC : ofW (M n) = C - 1) :
    ofW ((isA M : ℤ → MatW) n) = invSqrtM C := by
  rw [← evI_apply, isA, (evI n).map_tsum (summable_isA h)]
  unfold invSqrtM
  refine tsum_congr fun k => ?_
  rw [← hC, evI_apply, lp.coeFn_smul, Pi.smul_apply, lp.infty_coeFn_pow, Pi.pow_apply, ofW_smul, ofW_pow]

/-! ### The inclusion `ℓ² ⊂ ℓ∞` and the products `ℓ∞ × ℓ² → ℓ²`, `ℓ² × ℓ∞ → ℓ²` -/

/-- The inclusion `ℓ² ⊂ ℓ∞`. -/
def incl : MS →L[ℂ] MI :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => toW (x n), memℓp_infty_iff.2 ⟨‖x‖, by
        rintro _ ⟨n, rfl⟩
        show ‖toW (x n)‖ ≤ ‖x‖
        rw [norm_toW]; exact lp.norm_apply_le_norm two_ne_zero x n⟩⟩
      map_add' := fun x y => lp.ext (funext fun n => by
        show toW ((x + y) n) = toW (x n) + toW (y n)
        rw [lp.coeFn_add, Pi.add_apply, toW_add])
      map_smul' := fun c x => lp.ext (funext fun n => by
        show toW ((c • x) n) = c • toW (x n)
        rw [lp.coeFn_smul, Pi.smul_apply, toW_smul]) }
    1 (fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x) fun n => by
        show ‖toW (x n)‖ ≤ ‖x‖
        rw [norm_toW]; exact lp.norm_apply_le_norm two_ne_zero x n)

theorem incl_apply (x : MS) (n : ℤ) : ofW ((incl x : ℤ → MatW) n) = x n := rfl

theorem ofW_le (a : MI) (n : ℤ) : ‖ofW (a n)‖ ≤ ‖a‖ := by
  rw [norm_ofW]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero a n

theorem mulL_le (a : MI) (x : MS) (n : ℤ) : ‖ofW (a n) * x n‖ ≤ ‖a‖ * ‖x n‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (ofW_le a n) (norm_nonneg _))

theorem mulR_le (x : MS) (a : MI) (n : ℤ) : ‖x n * ofW (a n)‖ ≤ ‖a‖ * ‖x n‖ := by
  rw [mul_comm ‖a‖]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ofW_le a n) (norm_nonneg _))

/-- `(a, x) ↦ (a_n x_n)_n`. -/
def mulL : MI →L[ℂ] MS →L[ℂ] MS :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun a x => (⟨fun n => ofW (a n) * x n,
        memℓp2_of_le' x (norm_nonneg a) (mulL_le a x)⟩ : MS))
      (fun a b x => lp.ext (funext fun n => by
        show ofW ((a + b) n) * x n = ofW (a n) * x n + ofW (b n) * x n
        rw [lp.coeFn_add, Pi.add_apply, ofW_add, add_mul]))
      (fun c a x => lp.ext (funext fun n => by
        show ofW ((c • a) n) * x n = c • (ofW (a n) * x n)
        rw [lp.coeFn_smul, Pi.smul_apply, ofW_smul, smul_mul_assoc]))
      (fun a x y => lp.ext (funext fun n => by
        show ofW (a n) * (x + y) n = ofW (a n) * x n + ofW (a n) * y n
        rw [lp.coeFn_add, Pi.add_apply, mul_add]))
      (fun c a x => lp.ext (funext fun n => by
        show ofW (a n) * (c • x) n = c • (ofW (a n) * x n)
        rw [lp.coeFn_smul, Pi.smul_apply, mul_smul_comm])))
    1 (fun a x => by rw [one_mul]; exact l2_norm_le (norm_nonneg a) (mulL_le a x))

theorem mulL_apply (a : MI) (x : MS) (n : ℤ) : (mulL a x : ℤ → Mat) n = ofW (a n) * x n := rfl

/-- `(x, a) ↦ (x_n a_n)_n`. -/
def mulR : MS →L[ℂ] MI →L[ℂ] MS :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun x a => (⟨fun n => x n * ofW (a n),
        memℓp2_of_le' x (norm_nonneg a) (mulR_le x a)⟩ : MS))
      (fun x y a => lp.ext (funext fun n => by
        show (x + y) n * ofW (a n) = x n * ofW (a n) + y n * ofW (a n)
        rw [lp.coeFn_add, Pi.add_apply, add_mul]))
      (fun c x a => lp.ext (funext fun n => by
        show (c • x) n * ofW (a n) = c • (x n * ofW (a n))
        rw [lp.coeFn_smul, Pi.smul_apply, smul_mul_assoc]))
      (fun x a b => lp.ext (funext fun n => by
        show x n * ofW ((a + b) n) = x n * ofW (a n) + x n * ofW (b n)
        rw [lp.coeFn_add, Pi.add_apply, ofW_add, mul_add]))
      (fun c x a => lp.ext (funext fun n => by
        show x n * ofW ((c • a) n) = c • (x n * ofW (a n))
        rw [lp.coeFn_smul, Pi.smul_apply, ofW_smul, mul_smul_comm])))
    1 (fun x a => by
      rw [one_mul, mul_comm]; exact l2_norm_le (norm_nonneg a) (mulR_le x a))

theorem mulR_apply (x : MS) (a : MI) (n : ℤ) : (mulR x a : ℤ → Mat) n = x n * ofW (a n) := rfl

/-! ### Matrix entries -/

/-- The entry `M ↦ (M v)_j`. -/
def entry (v : E2) (j : Fin 2) : Mat →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => (M v) j
      map_add' := fun M M' => by simp
      map_smul' := fun c M => by simp }
    ‖v‖ (fun M => by
      rw [mul_comm]
      exact (PiLp.norm_apply_le (M v) j).trans (M.le_opNorm v))

theorem entry_le (v : E2) (j : Fin 2) : ‖entry v j‖ ≤ ‖v‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg v) _

/-- The entry sequence `ℓ²(ℤ; Mat₂) → ℓ²(ℤ; ℂ)`, `x ↦ ((x_n v)_j)_n`. -/
def entS (v : E2) (j : Fin 2) : MS →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  fiberMap (fun _ => entry v j) (norm_nonneg v) (fun _ => entry_le v j)

theorem entS_apply (v : E2) (j : Fin 2) (x : MS) (n : ℤ) :
    (entS v j x : ℤ → ℂ) n = (x n v) j := rfl

/-! ### Analyticity helpers -/

theorem clm_comp_analytic {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (Λ : X →L[ℂ] Y) {f : E → X} {u : E}
    (hf : AnalyticAt ℝ f u) : AnalyticAt ℝ (fun v => Λ (f v)) u :=
  ((Λ.restrictScalars ℝ).analyticAt (f u)).comp hf

theorem bil_comp_analytic {E X Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (B : X →L[ℂ] Y →L[ℂ] Z) {f : E → X} {g : E → Y} {u : E} (hf : AnalyticAt ℝ f u)
    (hg : AnalyticAt ℝ g u) : AnalyticAt ℝ (fun v => B (f v) (g v)) u := by
  have h : AnalyticAt ℝ (fun p : X × Y => B p.1 p.2) (f u, g u) :=
    (B.analyticAt_bilinear (f u, g u)).restrictScalars
  exact AnalyticAt.comp (g := fun p : X × Y => B p.1 p.2) (f := fun v => (f v, g v)) h (hf.prod hg)

/-! ### The matrix families -/

/-- `(S_n - 1)` family. -/
def Sfam (hL : 0 < L) (N : ℕ) (FP0 FP1 : Lp ℂ 2 (μI L) → lp (fun _ : ℤ => H2 L) 2) (u : Lp ℂ 2 (μI L)) : MS :=
  Phi hL 0 (act (maskInf (L := L) N) (FP0 u)) + Phi hL 1 (act (maskInf (L := L) N) (FP1 u))

theorem Sfam_analyticAt (hL : 0 < L) (N : ℕ) {FP0 FP1 : Lp ℂ 2 (μI L) → lp (fun _ : ℤ => H2 L) 2}
    {u : Lp ℂ 2 (μI L)} (h0 : AnalyticAt ℝ FP0 u) (h1 : AnalyticAt ℝ FP1 u) :
    AnalyticAt ℝ (Sfam hL N FP0 FP1) u :=
  (clm_comp_analytic (Phi hL 0 ∘L act (maskInf (L := L) N)) h0).add
    (clm_comp_analytic (Phi hL 1 ∘L act (maskInf (L := L) N)) h1)

/-- `S_n^{-1/2}` family in `ℓ∞`. -/
def Ginv (M : MS) : MI := isA (incl M)

/-- `S_n^{-1/2} K_n S_n^{-1/2}` family in `ℓ²`. -/
def Bfam (Sm Km : MS) : MS := mulR (mulL (Ginv Sm) Km) (Ginv Sm)

/-- **The `ℓ²` matrix families**: for every interval field `u₀` there are `N`, `ρ > 0` and maps
`Sf, Kf, Bf : L²(0,L) → ℓ²(ℤ; B(ℂ²))`, real analytic on `B(u₀, ρ)`, such that for `‖u - u₀‖ < ρ` and `|n| > N`:
`‖S_n(u) - 1‖ ≤ 1/2` (`S_n = E^* P_n(u) E`), `Sf(u)_n = S_n - 1`, `Kf(u)_n = K_n = E^* Q_n(u) E`
(`Q_n = (2πi)⁻¹∮(z - p_n)(z - 𝓛_u)⁻¹ dz`), `Bf(u)_n = S_n^{-1/2} K_n S_n^{-1/2}` (inverse square root by its power
series at `1`), and `Sf(u)_n = Kf(u)_n = Bf(u)_n = 0` for `|n| ≤ N`. -/
theorem tail_matrix_analytic [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ Sf Kf Bf : Lp ℂ 2 (μI L) → MS,
      AnalyticOnNhd ℝ Sf (ball u₀ ρ) ∧ AnalyticOnNhd ℝ Kf (ball u₀ ρ) ∧ AnalyticOnNhd ℝ Bf (ball u₀ ρ) ∧
      ∀ u ∈ ball u₀ ρ, ∀ n : ℤ,
        ((N : ℝ) < |(n : ℝ)| →
          SqSmall L κ r n u ∧ ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ ≤ 1 / 2 ∧
          (Sf u : ℤ → Mat) n = compressionMatrix L κ (u : ℝ → ℂ) n r - 1 ∧
          (Kf u : ℤ → Mat) n =
            ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (u : ℝ → ℂ) n r ∘L embed L n ∧
          (Bf u : ℤ → Mat) n = invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) * (Kf u : ℤ → Mat) n *
            invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) ∧
        (|(n : ℝ)| ≤ N → (Sf u : ℤ → Mat) n = 0 ∧ (Kf u : ℤ → Mat) n = 0 ∧ (Bf u : ℤ → Mat) n = 0) := by
  have S : Setup L r := ⟨hL, hr, hr2⟩
  obtain ⟨N0, ρ0, hρ0, FP0, FD0, hP0, hD0, hc0⟩ := tail_columns_analytic (κ := κ) hL hr hr2 u₀ 0
  obtain ⟨N1, ρ1, hρ1, FP1, FD1, hP1, hD1, hc1⟩ := tail_columns_analytic (κ := κ) hL hr hr2 u₀ 1
  obtain ⟨Ns, ρs, hρs, hs⟩ := small_compression (κ := κ) hL hr hr2 u₀
  set N : ℕ := max (max N0 N1) Ns with hN
  set ρ : ℝ := min (min ρ0 ρ1) ρs with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hρ0 hρ1) hρs
  have hb0 : ball u₀ ρ ⊆ ball u₀ ρ0 := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hb1 : ball u₀ ρ ⊆ ball u₀ ρ1 := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hbs : ball u₀ ρ ⊆ ball u₀ ρs := ball_subset_ball (min_le_right _ _)
  have hN0 : (N0 : ℝ) ≤ N := by exact_mod_cast (le_max_left N0 N1).trans (le_max_left _ Ns)
  have hN1 : (N1 : ℝ) ≤ N := by exact_mod_cast (le_max_right N0 N1).trans (le_max_left _ Ns)
  have hNs : (Ns : ℝ) ≤ N := by exact_mod_cast le_max_right (max N0 N1) Ns
  set Sf := Sfam hL N FP0 FP1 with hSf
  set Kf := Sfam hL N FD0 FD1 with hKf
  -- componentwise description of `Sf`, `Kf`
  have hSc : ∀ u ∈ ball u₀ ρ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      (Sf u : ℤ → Mat) n = compressionMatrix L κ (u : ℝ → ℂ) n r - 1 := by
    intro u hu n hn
    have e0 := (hc0 u (hb0 hu) n).1
    have e1 := (hc1 u (hb1 hu) n).1
    rw [if_pos (lt_of_le_of_lt hN0 hn)] at e0
    rw [if_pos (lt_of_le_of_lt hN1 hn)] at e1
    rw [hSf, Sfam, Phi_pair hL _ _ n (perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r)
      (by rw [act_mask_apply, if_pos hn, e0]) (by rw [act_mask_apply, if_pos hn, e1])]
    refine ContinuousLinearMap.ext fun v => ?_
    rw [compression_sub_apply hL hr hr2 n]
    rfl
  have hKc : ∀ u ∈ ball u₀ ρ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      (Kf u : ℤ → Mat) n =
        ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (u : ℝ → ℂ) n r ∘L embed L n := by
    intro u hu n hn
    have e0 := (hc0 u (hb0 hu) n).2
    have e1 := (hc1 u (hb1 hu) n).2
    rw [if_pos (lt_of_le_of_lt hN0 hn)] at e0
    rw [if_pos (lt_of_le_of_lt hN1 hn)] at e1
    rw [hKf, Sfam, Phi_pair hL _ _ n
      (dressedIntegral L κ (u : ℝ → ℂ) n r - dressedIntegral L κ (fun _ => 0) n r)
      (by rw [act_mask_apply, if_pos hn, e0]) (by rw [act_mask_apply, if_pos hn, e1])]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, embed_apply, map_add, map_smul,
      dressed_zero_chi (κ := κ) S, smul_zero, add_zero, sub_zero]
  have hZ : ∀ u : Lp ℂ 2 (μI L), ∀ n : ℤ, |(n : ℝ)| ≤ N →
      (Sf u : ℤ → Mat) n = 0 ∧ (Kf u : ℤ → Mat) n = 0 := by
    intro u n hn
    have hn' : ¬ (N : ℝ) < |(n : ℝ)| := not_lt.2 hn
    exact ⟨Phi_zero hL _ _ n (by rw [act_mask_apply, if_neg hn']) (by rw [act_mask_apply, if_neg hn']),
      Phi_zero hL _ _ n (by rw [act_mask_apply, if_neg hn']) (by rw [act_mask_apply, if_neg hn'])⟩
  -- the `ℓ∞` bound `‖S - 1‖ ≤ 1/2`
  have hSI : ∀ u ∈ ball u₀ ρ, ‖incl (Sf u)‖ < 1 := by
    intro u hu
    refine lt_of_le_of_lt (lp.norm_le_of_forall_le (C := 1 / 2) (by norm_num) fun n => ?_) (by norm_num)
    rw [← norm_ofW, incl_apply]
    by_cases hn : (N : ℝ) < |(n : ℝ)|
    · rw [hSc u hu n hn]
      exact (hs n (lt_of_le_of_lt hNs hn) u (by simpa [dist_eq_norm] using hbs hu)).2.1
    · rw [(hZ u n (not_lt.1 hn)).1, norm_zero]; norm_num
  refine ⟨N, ρ, hρpos, Sf, Kf, fun u => Bfam (Sf u) (Kf u), fun u hu => ?_, fun u hu => ?_,
    fun u hu => ?_, fun u hu n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · exact Sfam_analyticAt hL N (hP0 u (hb0 hu)) (hP1 u (hb1 hu))
  · exact Sfam_analyticAt hL N (hD0 u (hb0 hu)) (hD1 u (hb1 hu))
  · have hS := Sfam_analyticAt hL N (hP0 u (hb0 hu)) (hP1 u (hb1 hu))
    have hK := Sfam_analyticAt hL N (hD0 u (hb0 hu)) (hD1 u (hb1 hu))
    have hI : AnalyticAt ℝ (fun v => incl (Sf v)) u := clm_comp_analytic incl hS
    have hG : AnalyticAt ℝ (fun v => Ginv (Sf v)) u :=
      AnalyticAt.comp (g := isA) (f := fun v => incl (Sf v))
        ((isA_analyticAt (hSI u hu)).restrictScalars (𝕜 := ℝ)) hI
    exact bil_comp_analytic mulR (bil_comp_analytic mulL hG hK) hG
  · obtain ⟨h1, h2, -⟩ := hs n (lt_of_le_of_lt hNs hn) u (by simpa [dist_eq_norm] using hbs hu)
    have hC : ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ < 1 := lt_of_le_of_lt h2 (by norm_num)
    have ha : ofW ((incl (Sf u) : ℤ → MatW) n) = compressionMatrix L κ (u : ℝ → ℂ) n r - 1 := by
      rw [incl_apply, hSc u hu n hn]
    refine ⟨h1, h2, hSc u hu n hn, hKc u hu n hn, ?_⟩
    show (mulR (mulL (Ginv (Sf u)) (Kf u)) (Ginv (Sf u)) : ℤ → Mat) n = _
    rw [mulR_apply, mulL_apply, Ginv, isA_apply (hSI u hu) n ha]
  · obtain ⟨h1, h2⟩ := hZ u n hn
    refine ⟨h1, h2, ?_⟩
    show (mulR (mulL (Ginv (Sf u)) (Kf u)) (Ginv (Sf u)) : ℤ → Mat) n = 0
    rw [mulR_apply, mulL_apply, h2, mul_zero, zero_mul]

/-- **Entries of `B_n - p_n` into `ℓ²(ℤ; ℂ)`**: in the setting of `tail_matrix_analytic`, for every `v ∈ ℂ²` and
`j`, `u ↦ ((S_n^{-1/2} K_n S_n^{-1/2} v)_j)_{|n|>N}` is real analytic into `ℓ²(ℤ; ℂ)`. With `v = (1,0)`, `j = 1` this
is `b_n`; with `j = 0` it is `a_n - p_n`; with `v = (0,1)`, `j = 0` it is `b_n^♯`. -/
theorem tail_entries_analytic [Fact (0 < L)] (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (u₀ : Lp ℂ 2 (μI L)) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ bf : E2 → Fin 2 → Lp ℂ 2 (μI L) → lp (fun _ : ℤ => ℂ) 2,
      (∀ v j, AnalyticOnNhd ℝ (bf v j) (ball u₀ ρ)) ∧
      ∀ u ∈ ball u₀ ρ, ∀ n : ℤ, ∀ v j,
        ((N : ℝ) < |(n : ℝ)| →
          SqSmall L κ r n u ∧ ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ ≤ 1 / 2 ∧
          (bf v j u : ℤ → ℂ) n = ((invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) *
            (ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (u : ℝ → ℂ) n r ∘L embed L n) *
            invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) v) j) ∧
        (|(n : ℝ)| ≤ N → (bf v j u : ℤ → ℂ) n = 0) := by
  obtain ⟨N, ρ, hρ, Sf, Kf, Bf, -, -, hB, h⟩ := tail_matrix_analytic (κ := κ) hL hr hr2 u₀
  refine ⟨N, ρ, hρ, fun v j u => entS v j (Bf u), fun v j u hu => clm_comp_analytic (entS v j) (hB u hu),
    fun u hu n v j => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · obtain ⟨h1, h2, -, hK, hBn⟩ := (h u hu n).1 hn
    refine ⟨h1, h2, ?_⟩
    rw [entS_apply, hBn, hK]
  · rw [entS_apply, ((h u hu n).2 hn).2.2]
    rfl

end QuantumNLS.RB01Matrix
#print axioms QuantumNLS.RB01Matrix.fiberMap
#print axioms QuantumNLS.RB01Matrix.Phi_pair
#print axioms QuantumNLS.RB01Matrix.dressed_zero_chi
#print axioms QuantumNLS.RB01Matrix.isA_analyticAt
#print axioms QuantumNLS.RB01Matrix.isA_apply
#print axioms QuantumNLS.RB01Matrix.mulL
#print axioms QuantumNLS.RB01Matrix.mulR
#print axioms QuantumNLS.RB01Matrix.tail_matrix_analytic
#print axioms QuantumNLS.RB01Matrix.tail_entries_analytic
