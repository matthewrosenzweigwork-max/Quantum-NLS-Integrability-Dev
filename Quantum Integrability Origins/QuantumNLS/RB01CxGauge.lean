import Mathlib
import QuantumNLS.RB01RootCount
import QuantumNLS.ComplexifiedDiscriminant
import QuantumNLS.RiccatiIndependentV

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-14: the interaction picture and the uniform trace estimates
for the complexified discriminant `ComplexifiedDiscriminant.cxDisc κ u v z` (independent `u`, `v ∈ L²(𝕋_L)`; the
real slice is `v = star u`, `cxDisc_star`).  Source `collective_actions.tex:318-362` ("All these facts hold on one
complex neighborhood and for all high labels"; "f_n ≠ 0 on |w| = 3d" is needed on the complexification for the
contour moments).

* `Bx κ u v z x = [[0, √κ v e^{izx}], [√κ u e^{-izx}, 0]]` (the gauge `E_z⁻¹(A_{u,v} − A_0)E_z`);
  `Nx_eq_transfer_cont` (continuous profiles: product rule + uniqueness of classical fundamental solutions,
  `RiccatiIndependentV.transfer_eq_of_fundamental`) and **`Nx_eq_transfer`** (all interval-integrable profiles,
  by `L¹` approximation of both `u` and `v`): `Dc z ℓ · transfer(cxCoef κ u v z) ℓ = transfer(Bx κ u v z) ℓ`;
* `trace_eq`: `tr transfer(cxCoef) ℓ = e^{-izℓ/2} W₀₀ + e^{izℓ/2} W₁₁`, `W = transfer(Bx) ℓ`;
* **`cxDisc_lipschitz`**: `|cxDisc κ u v z − cxDisc κ u' v' z| ≤ cxLip κ C₀ R L (‖u−u'‖ + ‖v−v'‖)` for
  `‖u‖,‖v‖,‖u'‖,‖v'‖ ≤ R`, every `Re z`, `|Im z| ≤ C₀` (uniform in `Re z`, hence in the label `n`);
* **`cx_prep`**: for every `u₀` there are `N` and `ρ > 0` such that for `|n| > N` and every `(u, v)` with
  `‖u − u₀‖ < ρ`, `‖v − star u₀‖ < ρ` (a complex neighborhood of the real point `(u₀, ū₀)`, containing all real
  points `(u, ū)` with `‖u − u₀‖ < ρ`): `|fx − freeF| ≤ 7ε₀` on `|w| ≤ 4d` and `|fx(w)| ≥ 9/65536` on
  `d/8 ≤ |w| ≤ 4d`, where `fx κ u v n w = cxDisc κ u v (p_n + w)² − 4`; in particular `fx ≠ 0` on `|w| = 3d`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
open QuantumNLS.RootDiscriminantBound (P1 P2 norm_le_of_row_sums)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

local instance instPMRB01Cx : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENRB01Cx : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RB01CxGauge

open QuantumNLS.RootInteractionL1 (Dc E1c E2c a1c E1c_mul_E2c hasDerivAt_Dc norm_E1c norm_E2c norm_E1c_sq_le
  norm_E2c_sq_le norm_offdiag_le exists_continuous_approx norm_transfer_sub_le_of norm_Dc_le)
open QuantumNLS.ComplexifiedDiscriminant (cxCoef cxDisc norm_cxCoef_le norm_entry_le intervalIntegrable_cxCoef
  cxDisc_star)
open QuantumNLS.RB01RootPrep (fn freeF dd ε₀ dd_pos root_prep freeF_lower small_arg cos_close)

/-- The complexified interaction coefficient. -/
def Bx (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) (x : ℝ) : Mat2 :=
  !![0, (Real.sqrt κ : ℂ) * v x * (E1c z x * E1c z x);
     (Real.sqrt κ : ℂ) * u x * (E2c z x * E2c z x), 0]

theorem hasDerivAt_Nx (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) {M : ℝ → Mat2}
    (hM : IsFundamental (cxCoef κ u v z) M) (x : ℝ) :
    HasDerivAt (fun y => Dc z y * M y) (Bx κ u v z x * (Dc z x * M x)) x := by
  have h := (hasDerivAt_Dc z x).mul (hM.2 x)
  refine h.congr_deriv ?_
  have hE : E1c z x * E2c z x = 1 := E1c_mul_E2c z x
  have hE2 : E2c z x = (E1c z x)⁻¹ := eq_inv_of_mul_eq_one_right hE
  have hne : E1c z x ≠ 0 := Complex.exp_ne_zero _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dc, P1, P2, Bx, cxCoef, a1c, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.vecMul, dotProduct] <;>
    (rw [hE2]; field_simp; try ring)

theorem continuous_Bx (κ : ℝ) {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v) (z : ℂ) :
    Continuous (Bx κ u v z) := by
  unfold Bx
  refine continuous_matrix fun i j => ?_
  have h1 : Continuous (E1c z) := by unfold E1c; fun_prop
  have h2 : Continuous (E2c z) := by unfold E2c; fun_prop
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_cxCoef (κ : ℝ) {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v) (z : ℂ) :
    Continuous (cxCoef κ u v z) := by
  unfold cxCoef
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem intervalIntegrable_Bx {ℓ : ℝ} {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 ℓ)
    (hv : IntervalIntegrable v volume 0 ℓ) (κ : ℝ) (z : ℂ) :
    IntervalIntegrable (Bx κ u v z) volume 0 ℓ := by
  have h1 : Continuous (E1c z) := by unfold E1c; fun_prop
  have h2 : Continuous (E2c z) := by unfold E2c; fun_prop
  let E : Mat2 := !![0, 1; 0, 0]
  let F : Mat2 := !![0, 0; 1, 0]
  have hh := (((hv.mul_continuousOn (g := fun x => E1c z x * E1c z x) (h1.mul h1).continuousOn).const_mul
      ((Real.sqrt κ : ℝ) : ℂ)).smul_continuousOn (g := fun _ => E) continuousOn_const).add
    (((hu.mul_continuousOn (g := fun x => E2c z x * E2c z x) (h2.mul h2).continuousOn).const_mul
      ((Real.sqrt κ : ℝ) : ℂ)).smul_continuousOn (g := fun _ => F) continuousOn_const)
  have he : Bx κ u v z = fun x =>
      (((Real.sqrt κ : ℝ) : ℂ) * (v x * (E1c z x * E1c z x))) • E +
        (((Real.sqrt κ : ℝ) : ℂ) * (u x * (E2c z x * E2c z x))) • F := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Bx, E, F] <;> ring
  rw [he]
  exact hh

/-! ## Pointwise and integral bounds -/

theorem Bx_sub (κ : ℝ) (u v u' v' : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    Bx κ u v z x - Bx κ u' v' z x = Bx κ (fun s => u s - u' s) (fun s => v s - v' s) z x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bx] <;> ring

theorem norm_Bx_le (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) {ℓ x : ℝ} (hx : x ∈ Icc (0 : ℝ) ℓ) :
    ‖Bx κ u v z x‖ ≤ 0 + Real.sqrt κ * Real.exp (|z.im| * ℓ) * (‖u x‖ + ‖v x‖) := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := norm_E1c_sq_le z hx
  have h2 := norm_E2c_sq_le z hx
  have hk := Real.sqrt_nonneg κ
  have he : 0 ≤ Real.exp (|z.im| * ℓ) := (Real.exp_pos _).le
  have hke := mul_nonneg hk he
  rw [zero_add]
  refine norm_offdiag_le _ _ ?_ ?_ (by positivity)
  · rw [norm_mul, norm_mul, hs]
    calc Real.sqrt κ * ‖v x‖ * ‖E1c z x * E1c z x‖ ≤ Real.sqrt κ * ‖v x‖ * Real.exp (|z.im| * ℓ) := by
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hke (norm_nonneg (u x))]
  · rw [norm_mul, norm_mul, hs]
    calc Real.sqrt κ * ‖u x‖ * ‖E2c z x * E2c z x‖ ≤ Real.sqrt κ * ‖u x‖ * Real.exp (|z.im| * ℓ) := by
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hke (norm_nonneg (v x))]

theorem norm_cxCoef_sub_le (κ : ℝ) (u v u' v' : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖cxCoef κ u v z x - cxCoef κ u' v' z x‖ ≤ 0 + Real.sqrt κ * (‖u x - u' x‖ + ‖v x - v' x‖) := by
  have hs : ‖((Real.sqrt κ : ℝ) : ℂ)‖ = Real.sqrt κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have he : cxCoef κ u v z x - cxCoef κ u' v' z x =
      !![0, (Real.sqrt κ : ℂ) * (v x - v' x); (Real.sqrt κ : ℂ) * (u x - u' x), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxCoef] <;> ring
  have hk := Real.sqrt_nonneg κ
  rw [he, zero_add]
  refine norm_offdiag_le _ _ ?_ ?_ (by positivity)
  · rw [norm_mul, hs]; nlinarith [mul_nonneg hk (norm_nonneg (u x - u' x))]
  · rw [norm_mul, hs]; nlinarith [mul_nonneg hk (norm_nonneg (v x - v' x))]

theorem integral_aff {ℓ : ℝ} {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 ℓ)
    (hv : IntervalIntegrable v volume 0 ℓ) (a b : ℝ) :
    ∫ s in (0 : ℝ)..ℓ, (a + b * (‖u s‖ + ‖v s‖)) =
      ℓ * a + b * ((∫ s in (0 : ℝ)..ℓ, ‖u s‖) + ∫ s in (0 : ℝ)..ℓ, ‖v s‖) := by
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hu.norm.add hv.norm).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_add hu.norm hv.norm,
    intervalIntegral.integral_const]
  simp

theorem integral_le_aff {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {A : ℝ → Mat2} (hA : IntervalIntegrable A volume 0 ℓ)
    {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 ℓ) (hv : IntervalIntegrable v volume 0 ℓ) {a b : ℝ}
    (h : ∀ x ∈ Icc (0 : ℝ) ℓ, ‖A x‖ ≤ a + b * (‖u x‖ + ‖v x‖)) :
    ∫ s in (0 : ℝ)..ℓ, ‖A s‖ ≤
      ℓ * a + b * ((∫ s in (0 : ℝ)..ℓ, ‖u s‖) + ∫ s in (0 : ℝ)..ℓ, ‖v s‖) := by
  rw [← integral_aff hu hv]
  exact intervalIntegral.integral_mono_on hℓ hA.norm
    (intervalIntegrable_const.add ((hu.norm.add hv.norm).const_mul b)) h

/-! ## The gauge identity -/

theorem Nx_eq_transfer_cont {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (κ : ℝ) (z : ℂ) : Dc z ℓ * transfer (cxCoef κ u v z) ℓ = transfer (Bx κ u v z) ℓ := by
  obtain ⟨M, hM⟩ := QuantumNLS.LinearFundamental.exists_isFundamental (continuous_cxCoef κ hu hv z)
  have h1 := QuantumNLS.RiccatiIndependentV.transfer_eq_of_fundamental hℓ (continuous_cxCoef κ hu hv z)
    hM.1 hM.2
  have hN0 : Dc z 0 * M 0 = 1 := by
    rw [hM.1, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dc, E1c, E2c, P1, P2]
  have h2 := QuantumNLS.RiccatiIndependentV.transfer_eq_of_fundamental (M := fun y => Dc z y * M y) hℓ
    (continuous_Bx κ hu hv z) hN0 (fun y => hasDerivAt_Nx κ u v z hM y)
  rw [h1, h2]

theorem Nx_eq_transfer {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 ℓ)
    (hv : IntervalIntegrable v volume 0 ℓ) (κ : ℝ) (z : ℂ) :
    Dc z ℓ * transfer (cxCoef κ u v z) ℓ = transfer (Bx κ u v z) ℓ := by
  have hℓm : ℓ ∈ Icc (0 : ℝ) ℓ := right_mem_Icc.2 hℓ
  set U : ℝ := ∫ s in (0 : ℝ)..ℓ, ‖u s‖ with hU
  set V : ℝ := ∫ s in (0 : ℝ)..ℓ, ‖v s‖ with hV
  have hU0 : 0 ≤ U := intervalIntegral.integral_nonneg hℓ (fun s _ => norm_nonneg _)
  have hV0 : 0 ≤ V := intervalIntegral.integral_nonneg hℓ (fun s _ => norm_nonneg _)
  have hk := Real.sqrt_nonneg κ
  set c : ℝ := Real.sqrt κ * Real.exp (|z.im| * ℓ) with hc
  have hc0 : 0 ≤ c := by positivity
  set P : ℝ := ℓ * (‖z‖ / 2) + Real.sqrt κ * (U + V) with hP
  set P' : ℝ := ℓ * (‖z‖ / 2) + Real.sqrt κ * (U + V + 2) with hP'
  set Q : ℝ := ℓ * 0 + c * (U + V) with hQ
  set Q' : ℝ := ℓ * 0 + c * (U + V + 2) with hQ'
  set D : ℝ := Real.exp (|z.im| * ℓ / 2) with hD
  set K : ℝ := D * (Real.sqrt κ * 2 * (Real.exp P * Real.exp P')) + c * 2 * (Real.exp Q * Real.exp Q')
    with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖Dc z ℓ * transfer (cxCoef κ u v z) ℓ - transfer (Bx κ u v z) ℓ‖ ≤ K * ε := by
    intro ε hε hε1
    obtain ⟨u', hu'c, hu'⟩ := exists_continuous_approx hℓ hu hε
    obtain ⟨v', hv'c, hv'⟩ := exists_continuous_approx hℓ hv hε
    have hu'I : IntervalIntegrable u' volume 0 ℓ := hu'c.intervalIntegrable 0 ℓ
    have hv'I : IntervalIntegrable v' volume 0 ℓ := hv'c.intervalIntegrable 0 ℓ
    have hdu : IntervalIntegrable (fun s => u s - u' s) volume 0 ℓ := hu.sub hu'I
    have hdv : IntervalIntegrable (fun s => v s - v' s) volume 0 ℓ := hv.sub hv'I
    have happ : ∀ {f g : ℝ → ℂ}, IntervalIntegrable f volume 0 ℓ → IntervalIntegrable g volume 0 ℓ →
        ∫ s in (0 : ℝ)..ℓ, ‖f s - g s‖ ≤ ε →
        ∫ s in (0 : ℝ)..ℓ, ‖g s‖ ≤ (∫ s in (0 : ℝ)..ℓ, ‖f s‖) + 1 := by
      intro f g hf hg hfg
      have hle : ∫ s in (0 : ℝ)..ℓ, ‖g s‖ ≤ ∫ s in (0 : ℝ)..ℓ, (‖f s‖ + ‖f s - g s‖) :=
        intervalIntegral.integral_mono_on hℓ hg.norm (hf.norm.add (hf.sub hg).norm) (fun s _ => by
          have := norm_sub_norm_le (g s) (f s)
          have h' : ‖g s - f s‖ = ‖f s - g s‖ := norm_sub_rev _ _
          linarith)
      rw [intervalIntegral.integral_add hf.norm (hf.sub hg).norm] at hle
      linarith
    have hU' := happ hu hu'I hu'
    have hV' := happ hv hv'I hv'
    have hA : ∫ s in (0 : ℝ)..ℓ, ‖cxCoef κ u v z s‖ ≤ P :=
      integral_le_aff hℓ (intervalIntegrable_cxCoef hu hv κ z) hu hv (fun x _ => norm_cxCoef_le κ u v z x)
    have hA' : ∫ s in (0 : ℝ)..ℓ, ‖cxCoef κ u' v' z s‖ ≤ P' := by
      refine (integral_le_aff hℓ (intervalIntegrable_cxCoef hu'I hv'I κ z) hu'I hv'I
        (fun x _ => norm_cxCoef_le κ u' v' z x)).trans ?_
      rw [hP']; nlinarith
    have hAd : ∫ s in (0 : ℝ)..ℓ, ‖cxCoef κ u v z s - cxCoef κ u' v' z s‖ ≤ Real.sqrt κ * (2 * ε) := by
      refine (integral_le_aff hℓ ((intervalIntegrable_cxCoef hu hv κ z).sub
        (intervalIntegrable_cxCoef hu'I hv'I κ z)) hdu hdv
        (fun x _ => norm_cxCoef_sub_le κ u v u' v' z x)).trans ?_
      nlinarith
    have hB : ∫ s in (0 : ℝ)..ℓ, ‖Bx κ u v z s‖ ≤ Q :=
      integral_le_aff hℓ (intervalIntegrable_Bx hu hv κ z) hu hv (fun x hx => norm_Bx_le κ u v z hx)
    have hB' : ∫ s in (0 : ℝ)..ℓ, ‖Bx κ u' v' z s‖ ≤ Q' := by
      refine (integral_le_aff hℓ (intervalIntegrable_Bx hu'I hv'I κ z) hu'I hv'I
        (fun x hx => norm_Bx_le κ u' v' z hx)).trans ?_
      rw [hQ']; nlinarith
    have hBd : ∫ s in (0 : ℝ)..ℓ, ‖Bx κ u v z s - Bx κ u' v' z s‖ ≤ c * (2 * ε) := by
      have hI := (intervalIntegrable_Bx hu hv κ z).sub (intervalIntegrable_Bx hu'I hv'I κ z)
      refine (integral_le_aff hℓ hI hdu hdv (fun x hx => by
        rw [Bx_sub]; exact norm_Bx_le κ _ _ z hx)).trans ?_
      nlinarith
    have e1 := norm_transfer_sub_le_of hℓ (intervalIntegrable_cxCoef hu hv κ z)
      (intervalIntegrable_cxCoef hu'I hv'I κ z) hA hA' hAd hℓm
    have e2 := norm_transfer_sub_le_of hℓ (intervalIntegrable_Bx hu hv κ z)
      (intervalIntegrable_Bx hu'I hv'I κ z) hB hB' hBd hℓm
    have hcont := Nx_eq_transfer_cont hℓ hu'c hv'c κ z
    have hDn := norm_Dc_le z hℓm
    have hdiff : Dc z ℓ * transfer (cxCoef κ u v z) ℓ - transfer (Bx κ u v z) ℓ =
        Dc z ℓ * (transfer (cxCoef κ u v z) ℓ - transfer (cxCoef κ u' v' z) ℓ) -
          (transfer (Bx κ u v z) ℓ - transfer (Bx κ u' v' z) ℓ) := by
      rw [mul_sub, hcont]; abel
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    have h3 : ‖Dc z ℓ * (transfer (cxCoef κ u v z) ℓ - transfer (cxCoef κ u' v' z) ℓ)‖ ≤
        D * (Real.sqrt κ * (2 * ε) * (Real.exp P * Real.exp P')) :=
      (norm_mul_le _ _).trans (mul_le_mul hDn e1 (norm_nonneg _) (Real.exp_pos _).le)
    have h4 : D * (Real.sqrt κ * (2 * ε) * (Real.exp P * Real.exp P')) +
        c * (2 * ε) * (Real.exp Q * Real.exp Q') = K * ε := by rw [hK]; ring
    linarith
  have hz : ‖Dc z ℓ * transfer (cxCoef κ u v z) ℓ - transfer (Bx κ u v z) ℓ‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    set e : ℝ := min 1 (ε / (K + 1)) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    have he1 : e ≤ 1 := min_le_left _ _
    have hb := hbound e he0 he1
    have hKe : K * e ≤ ε := by
      have : e ≤ ε / (K + 1) := min_le_right _ _
      calc K * e ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left this hK0
        _ ≤ ε := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

theorem trace_eq {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 ℓ)
    (hv : IntervalIntegrable v volume 0 ℓ) (κ : ℝ) (z : ℂ) :
    Matrix.trace (transfer (cxCoef κ u v z) ℓ) =
      E2c z ℓ * transfer (Bx κ u v z) ℓ 0 0 + E1c z ℓ * transfer (Bx κ u v z) ℓ 1 1 := by
  rw [← Nx_eq_transfer hℓ hu hv κ z]
  have hE := E1c_mul_E2c z ℓ
  set T := transfer (cxCoef κ u v z) ℓ
  rw [Matrix.trace_fin_two]
  simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(T 0 0 + T 1 1)) * hE

theorem norm_E_le (z : ℂ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {C₀ : ℝ} (hz : |z.im| ≤ C₀) :
    ‖E1c z ℓ‖ ≤ Real.exp (C₀ * ℓ / 2) ∧ ‖E2c z ℓ‖ ≤ Real.exp (C₀ * ℓ / 2) := by
  rw [norm_E1c, norm_E2c]
  constructor <;> apply Real.exp_le_exp.2
  · have : -(z.im * ℓ) ≤ C₀ * ℓ := by
      have := mul_le_mul_of_nonneg_right ((neg_le_abs z.im).trans hz) hℓ
      linarith
    linarith
  · have : z.im * ℓ ≤ C₀ * ℓ := mul_le_mul_of_nonneg_right ((le_abs_self z.im).trans hz) hℓ
    linarith

/-! ## Physical carrier: uniform Lipschitz bound on strips -/

variable {L : ℝ} [Fact (0 < L)]

/-- The `L¹` mass of the complexified interaction coefficient on the ball of radius `R`, strip `|Im z| ≤ C₀`. -/
def cxMass (κ C₀ R L : ℝ) : ℝ := Real.sqrt κ * Real.exp (C₀ * L) * (Real.sqrt L * (2 * R))

/-- The Lipschitz constant of `cxDisc` on the ball of radius `R`, strip `|Im z| ≤ C₀`. -/
def cxLip (κ C₀ R L : ℝ) : ℝ :=
  2 * Real.exp (C₀ * L / 2) * (Real.sqrt κ * Real.exp (C₀ * L) * Real.sqrt L) *
    (Real.exp (cxMass κ C₀ R L) * Real.exp (cxMass κ C₀ R L))

theorem cxLip_nonneg (κ C₀ R L : ℝ) : 0 ≤ cxLip κ C₀ R L := by unfold cxLip; positivity

theorem cxDisc_lipschitz (κ : ℝ) {C₀ R : ℝ} {u v u' v' : PhysicalTensor.L2T L} (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    (hu' : ‖u'‖ ≤ R) (hv' : ‖v'‖ ≤ R) {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖cxDisc κ u v z - cxDisc κ u' v' z‖ ≤ cxLip κ C₀ R L * (‖u - u'‖ + ‖v - v'‖) := by
  have hL : 0 < L := Fact.out
  have hLm : L ∈ Icc (0 : ℝ) L := right_mem_Icc.2 hL.le
  have hC₀ : 0 ≤ C₀ := (abs_nonneg _).trans hz
  set pu := L2SpatialTransfer.profile u
  set pv := L2SpatialTransfer.profile v
  set pu' := L2SpatialTransfer.profile u'
  set pv' := L2SpatialTransfer.profile v'
  have iu := L2SpatialTransfer.intervalIntegrable_profile u
  have iv := L2SpatialTransfer.intervalIntegrable_profile v
  have iu' := L2SpatialTransfer.intervalIntegrable_profile u'
  have iv' := L2SpatialTransfer.intervalIntegrable_profile v'
  have hk := Real.sqrt_nonneg κ
  have hsL := Real.sqrt_nonneg L
  set c : ℝ := Real.sqrt κ * Real.exp (|z.im| * L) with hc
  set c₀ : ℝ := Real.sqrt κ * Real.exp (C₀ * L) with hc₀
  have hcc : c ≤ c₀ := by
    rw [hc, hc₀]; gcongr
  have hc0 : 0 ≤ c := by positivity
  have hm : ∀ {a b : PhysicalTensor.L2T L}, ‖a‖ ≤ R → ‖b‖ ≤ R →
      ∫ s in (0 : ℝ)..L, ‖Bx κ (L2SpatialTransfer.profile a) (L2SpatialTransfer.profile b) z s‖ ≤
        cxMass κ C₀ R L := by
    intro a b ha hb
    have ia := L2SpatialTransfer.intervalIntegrable_profile a
    have ib := L2SpatialTransfer.intervalIntegrable_profile b
    refine (integral_le_aff hL.le (intervalIntegrable_Bx ia ib κ z) ia ib
      (fun x hx => norm_Bx_le κ _ _ z hx)).trans ?_
    have h1 := QuantumNLS.DiscParamContinuity.integral_profile_le a
    have h2 := QuantumNLS.DiscParamContinuity.integral_profile_le b
    have hsum : (∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile a s‖) +
        ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile b s‖ ≤ Real.sqrt L * (2 * R) := by nlinarith
    have hs0 : 0 ≤ (∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile a s‖) +
        ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile b s‖ :=
      add_nonneg (intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _))
        (intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _))
    unfold cxMass
    calc L * 0 + c * ((∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile a s‖) +
          ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile b s‖)
        ≤ c₀ * (Real.sqrt L * (2 * R)) := by
          rw [mul_zero, zero_add]
          exact mul_le_mul hcc hsum hs0 (by positivity)
      _ = _ := by rw [hc₀]
  have hd : ∫ s in (0 : ℝ)..L, ‖Bx κ pu pv z s - Bx κ pu' pv' z s‖ ≤
      c₀ * Real.sqrt L * (‖u - u'‖ + ‖v - v'‖) := by
    have hI := (intervalIntegrable_Bx iu iv κ z).sub (intervalIntegrable_Bx iu' iv' κ z)
    refine (integral_le_aff hL.le hI (iu.sub iu') (iv.sub iv') (fun x hx => by
      rw [Bx_sub]; exact norm_Bx_le κ _ _ z hx)).trans ?_
    have h1 := QuantumNLS.RB01TraceLip.integral_profile_sub_le u u'
    have h2 := QuantumNLS.RB01TraceLip.integral_profile_sub_le v v'
    have hs0 : 0 ≤ (∫ s in (0 : ℝ)..L, ‖pu s - pu' s‖) + ∫ s in (0 : ℝ)..L, ‖pv s - pv' s‖ :=
      add_nonneg (intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _))
        (intervalIntegral.integral_nonneg hL.le (fun s _ => norm_nonneg _))
    rw [mul_zero, zero_add]
    calc c * ((∫ s in (0 : ℝ)..L, ‖pu s - pu' s‖) + ∫ s in (0 : ℝ)..L, ‖pv s - pv' s‖)
        ≤ c₀ * (Real.sqrt L * ‖u - u'‖ + Real.sqrt L * ‖v - v'‖) :=
          mul_le_mul hcc (add_le_add h1 h2) hs0 (by positivity)
      _ = _ := by ring
  have e := norm_transfer_sub_le_of hL.le (intervalIntegrable_Bx iu iv κ z) (intervalIntegrable_Bx iu' iv' κ z)
    (hm hu hv) (hm hu' hv') hd hLm
  set W := transfer (Bx κ pu pv z) L
  set W' := transfer (Bx κ pu' pv' z) L
  have ht : cxDisc κ u v z - cxDisc κ u' v' z = E2c z L * (W - W') 0 0 + E1c z L * (W - W') 1 1 := by
    unfold cxDisc
    rw [trace_eq hL.le iu iv κ z, trace_eq hL.le iu' iv' κ z]
    simp only [Matrix.sub_apply]
    ring
  obtain ⟨hE1, hE2⟩ := norm_E_le z hL.le hz
  rw [ht]
  have h00 := norm_entry_le (W - W') 0 0
  have h11 := norm_entry_le (W - W') 1 1
  have hX : 0 ≤ Real.exp (C₀ * L / 2) := (Real.exp_pos _).le
  calc ‖E2c z L * (W - W') 0 0 + E1c z L * (W - W') 1 1‖
      ≤ ‖E2c z L‖ * ‖(W - W') 0 0‖ + ‖E1c z L‖ * ‖(W - W') 1 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ Real.exp (C₀ * L / 2) * ‖W - W'‖ + Real.exp (C₀ * L / 2) * ‖W - W'‖ := by
        gcongr
    _ = 2 * Real.exp (C₀ * L / 2) * ‖W - W'‖ := by ring
    _ ≤ 2 * Real.exp (C₀ * L / 2) * (c₀ * Real.sqrt L * (‖u - u'‖ + ‖v - v'‖) *
          (Real.exp (cxMass κ C₀ R L) * Real.exp (cxMass κ C₀ R L))) := by gcongr
    _ = cxLip κ C₀ R L * (‖u - u'‖ + ‖v - v'‖) := by unfold cxLip; rw [hc₀]; ring

/-! ## The complexified root-count preparation -/

/-- `‖star f‖ = ‖f‖` in `L²(𝕋_L)` (same proof as `ComplexifiedConjugation.norm_star'`, not imported). -/
theorem norm_star_L2 (f : PhysicalTensor.L2T L) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  have e : (fun x => ‖(star (⇑f)) x‖) = fun x => ‖f x‖ := funext fun x => norm_star (f x)
  rw [← eLpNorm_norm (star (⇑f)), e, eLpNorm_norm]
  all_goals first
    | exact Lp.aestronglyMeasurable f
    | exact continuous_star.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)

/-- `f_n(w; u, v) = cxDisc κ u v (p_n + w)² − 4`. -/
def fx (κ : ℝ) (u v : PhysicalTensor.L2T L) (n : ℤ) (w : ℂ) : ℂ :=
  cxDisc κ u v ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) ^ 2 - 4

theorem fx_star (κ : ℝ) (u : PhysicalTensor.L2T L) (n : ℤ) (w : ℂ) : fx κ u (star u) n w = fn κ u n w := by
  unfold fx fn; rw [cxDisc_star]

/-- **Complexified preparation**: one complex neighborhood of `(u₀, ū₀)`, all high labels. -/
theorem cx_prep (κ : ℝ) (u₀ : PhysicalTensor.L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
      ∀ u v : PhysicalTensor.L2T L, ‖u - u₀‖ < ρ → ‖v - star u₀‖ < ρ →
        (∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fx κ u v n w - freeF L w‖ ≤ 7 * ε₀) ∧
        (∀ w : ℂ, dd L / 8 ≤ ‖w‖ → ‖w‖ ≤ 4 * dd L → 9 / 65536 ≤ ‖fx κ u v n w‖) := by
  have hL : 0 < L := Fact.out
  have hd := dd_pos (L := L)
  obtain ⟨N, ρ₁, hρ₁, h⟩ := root_prep κ u₀
  set R : ℝ := ‖u₀‖ + 1 with hR
  set K : ℝ := cxLip κ (4 * dd L) R L with hK
  have hK0 : 0 ≤ K := cxLip_nonneg _ _ _ _
  have hε : (0 : ℝ) < ε₀ := by unfold ε₀; norm_num
  set ρ : ℝ := min 1 (ε₀ / (7 * (2 * K + 1))) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  refine ⟨N, ρ, hρ0, fun n hn u v hu hv => ?_⟩
  have hu1 : ‖u - u₀‖ < 1 := lt_of_lt_of_le hu (min_le_left _ _)
  have hv1 : ‖v - star u₀‖ < 1 := lt_of_lt_of_le hv (min_le_left _ _)
  have hnu : ‖u‖ ≤ R := by have := norm_le_insert' u u₀; linarith
  have hnv : ‖v‖ ≤ R := by
    have := norm_le_insert' v (star u₀); rw [norm_star_L2] at this; linarith
  have hnu0 : ‖u₀‖ ≤ R := by linarith
  have hnsu0 : ‖star u₀‖ ≤ R := by rw [norm_star_L2]; linarith
  obtain ⟨ha, -, -, -, -, -⟩ := h n hn u₀ (by simpa using hρ₁) 1 ⟨zero_le_one, le_rfl⟩
  rw [one_smul] at ha
  -- the perturbation of the trace
  have hδ : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L →
      ‖cxDisc κ u v ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
        L2SpatialTransfer.discriminant κ u₀ ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)‖ ≤ ε₀ / 7 := by
    intro w hw
    have hz : |((QuantumNLS.LocalSpectral.pm L n : ℂ) + w).im| ≤ 4 * dd L := by
      simp only [Complex.add_im, Complex.ofReal_im, zero_add]
      exact (Complex.abs_im_le_norm w).trans hw
    rw [← cxDisc_star κ u₀]
    refine (cxDisc_lipschitz κ hnu hnv hnu0 hnsu0 hz).trans ?_
    have hsum : ‖u - u₀‖ + ‖v - star u₀‖ ≤ 2 * ρ := by linarith
    have hρle : ρ ≤ ε₀ / (7 * (2 * K + 1)) := min_le_right _ _
    calc K * (‖u - u₀‖ + ‖v - star u₀‖) ≤ K * (2 * ρ) := mul_le_mul_of_nonneg_left hsum hK0
      _ ≤ (2 * K + 1) * ρ := by nlinarith
      _ ≤ (2 * K + 1) * (ε₀ / (7 * (2 * K + 1))) := mul_le_mul_of_nonneg_left hρle (by positivity)
      _ = ε₀ / 7 := by field_simp
  -- the real trace is bounded by 3 on the disk
  have hD3 : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L →
      ‖L2SpatialTransfer.discriminant κ u₀ ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)‖ ≤ 3 := by
    intro w hw
    set D := L2SpatialTransfer.discriminant κ u₀ ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)
    have h1 := ha w hw
    have hcos := cos_close (small_arg hw)
    have hc : ‖2 * Complex.cos (L * w / 2)‖ ≤ 5 / 2 := by
      rw [norm_mul]
      have : ‖Complex.cos (L * w / 2)‖ ≤ 5 / 4 := by
        have := norm_sub_norm_le (Complex.cos (L * w / 2)) 1
        rw [norm_one] at this; linarith
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2]; linarith
    have hDsq : D ^ 2 = (2 * Complex.cos (L * w / 2)) ^ 2 + (fn κ u₀ n w - freeF L w) := by
      unfold fn freeF; ring
    have hn2 : ‖D‖ ^ 2 ≤ (5 / 2) ^ 2 + 6 * ε₀ := by
      rw [← norm_pow, hDsq]
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow]
      have : ‖2 * Complex.cos (L * w / 2)‖ ^ 2 ≤ (5 / 2) ^ 2 := by
        gcongr
      linarith
    have : 6 * ε₀ ≤ 1 := by unfold ε₀; norm_num
    nlinarith [norm_nonneg D]
  have hclose : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fx κ u v n w - fn κ u₀ n w‖ ≤ ε₀ := by
    intro w hw
    set D := L2SpatialTransfer.discriminant κ u₀ ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)
    set D' := cxDisc κ u v ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w)
    have e : fx κ u v n w - fn κ u₀ n w = (D' - D) * (D' - D + 2 * D) := by unfold fx fn; ring
    rw [e, norm_mul]
    have h1 := hδ w hw
    have h2 := hD3 w hw
    have h3 : ‖D' - D + 2 * D‖ ≤ ε₀ / 7 + 6 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]; linarith
    have hε1 : ε₀ ≤ 1 := by unfold ε₀; norm_num
    calc ‖D' - D‖ * ‖D' - D + 2 * D‖ ≤ (ε₀ / 7) * (ε₀ / 7 + 6) :=
          mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      _ ≤ ε₀ := by nlinarith
  have hA : ∀ w : ℂ, ‖w‖ ≤ 4 * dd L → ‖fx κ u v n w - freeF L w‖ ≤ 7 * ε₀ := by
    intro w hw
    have e : fx κ u v n w - freeF L w = (fx κ u v n w - fn κ u₀ n w) + (fn κ u₀ n w - freeF L w) := by ring
    rw [e]
    have := norm_add_le (fx κ u v n w - fn κ u₀ n w) (fn κ u₀ n w - freeF L w)
    linarith [hclose w hw, ha w hw]
  refine ⟨hA, fun w hw1 hw2 => ?_⟩
  have hw' : ‖w‖ ≤ 1 / L := by
    have : 4 * dd L = 1 / L := by unfold dd; field_simp
    linarith
  have hlow := freeF_lower (L := L) hw'
  have hLw : 1 / 32 ≤ L * ‖w‖ := by
    have : dd L / 8 = 1 / (32 * L) := by unfold dd; field_simp; ring
    rw [this] at hw1
    rw [div_le_iff₀ (by positivity)] at hw1
    linarith
  have hfree : 16 / 65536 ≤ ‖freeF L w‖ := by nlinarith
  have := norm_sub_norm_le (freeF L w) (fx κ u v n w)
  have h7 := hA w hw2
  rw [norm_sub_rev] at h7
  unfold ε₀ at h7
  linarith

end QuantumNLS.RB01CxGauge

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01CxGauge.Nx_eq_transfer
#print axioms QuantumNLS.RB01CxGauge.trace_eq
#print axioms QuantumNLS.RB01CxGauge.cxDisc_lipschitz
#print axioms QuantumNLS.RB01CxGauge.fx_star
#print axioms QuantumNLS.RB01CxGauge.cx_prep
