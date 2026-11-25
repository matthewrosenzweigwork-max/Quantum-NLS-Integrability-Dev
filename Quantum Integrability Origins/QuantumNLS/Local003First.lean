import Mathlib
import QuantumNLS.Local003Inst

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage R2: the first-order coefficient.

Source (proof): "The linear part of `B_n - p_n 1` is `P V_u P`, whose `(2,1)` entry is `2i√(κ/L) u_n`."
For the Neumann package `(F0, G)` (`F0 = (z-𝓛_0)⁻¹` on `Γ_n`, `G u z = V_u R_0(z)`) we prove
`d/dζ bn(ζ G u)|₀ = ⟨χ_{n,2}, V_u χ_{n,1}⟩ = (2i√κ/L) ∫₀^L e^{-ip_n x} u(x) dx`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003First
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local003Neumann
  QuantumNLS.Local003Holo QuantumNLS.Local003Analytic

variable {L κ r : ℝ}

/-- `⟨χ_{n,j}, R_0(z) ψ⟩ = (z - p_n)⁻¹ ⟨χ_{n,j}, ψ⟩` on the contour. -/
lemma free_inner_res (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (j : Fin 2) {z : ℂ}
    (hz : z ∈ sphere (center L n) r) (ψ : H2 L) :
    ⟪chi L n j, resolvent L κ (fun _ => 0) (parity n) z ψ⟫_ℂ = (z - center L n)⁻¹ * ⟪chi L n j, ψ⟫_ℂ := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hz' : ‖z - (pm L n : ℂ)‖ = r := mem_sphere_iff_norm.mp hz
  have hzc : ‖conj z - (pm L n : ℂ)‖ = r := by
    have : conj z - (pm L n : ℂ) = conj (z - (pm L n : ℂ)) := by simp [Complex.conj_ofReal]
    rw [this, RCLike.norm_conj, hz']
  obtain ⟨Rz, hRz, -⟩ := hyp.res r n z hr hr2 hz'
  obtain ⟨Rc, hRc, -⟩ := hyp.res r n (conj z) hr hr2 hzc
  have hrel := QuantumNLS.Local003Hermitian.resolvent_adjoint_rel
    (fun p hp q hq => QuantumNLS.Local003Hermitian.graph_symm hL hr hr2 n (fun _ => 0) hp hq)
    hRc (by simpa using hRz) (chi L n j) ψ
  rw [resolvent_eq hRz, ← hrel]
  have h1 := QuantumNLS.LocalSpectral.resolvent_free_chi (κ := κ) hL n j (conj z) ⟨Rc, hRc⟩
  rw [resolvent_eq hRc] at h1
  have hne : conj z - center L n ≠ 0 := by
    intro h0
    have : ‖conj z - (pm L n : ℂ)‖ = 0 := by rw [show (pm L n : ℂ) = center L n from rfl, h0, norm_zero]
    rw [hzc] at this; linarith
  have h2 : Rc (chi L n j) = (conj z - center L n)⁻¹ • chi L n j := by
    calc Rc (chi L n j) = (conj z - center L n)⁻¹ • ((conj z - center L n) • Rc (chi L n j)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [h1]
  rw [h2, inner_smul_left]
  congr 1
  rw [map_inv₀, map_sub]
  congr 2
  · simp
  · simp [QuantumNLS.LocalSpectral.center, Complex.conj_ofReal]

/-- Inner-product form of the contour functional `Jclm`. -/
lemma Jinner (hr : 0 < r) {n : ℤ} (F : Alg L (center L n) r) (φ ψ : H2 L) :
    ⟪φ, Jclm L (center L n) hr F ψ⟫_ℂ =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * ∮ z in C(center L n, r), ⟪φ, extC F z ψ⟫_ℂ := by
  rw [Jclm_apply]
  unfold Jfun
  exact QuantumNLS.Local003Proj.inner_circle (extC F) hr.le (continuousOn_extC F) φ ψ

lemma extC_F0 {n : ℤ} (F0 : Alg L (center L n) r)
    (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz)
    {z : ℂ} (hz : z ∈ sphere (center L n) r) :
    extC F0 z = resolvent L κ (fun _ => 0) (parity n) z := by
  rw [extC_apply _ hz]; exact hF0e ⟨z, hz⟩

lemma ne_center (hr : 0 < r) {n : ℤ} {z : ℂ} (hz : z ∈ sphere (center L n) r) : z - center L n ≠ 0 := by
  intro h
  have := mem_sphere_iff_norm.mp hz
  rw [h, norm_zero] at this
  linarith

/-- `E* D_0 = 0` for the free dressed integral `D_0 = J (w · F_0)`. -/
lemma adj_D0 (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (F0 : Alg L (center L n) r)
    (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz)
    (j : Fin 2) (ψ : H2 L) : ⟪chi L n j, Jclm L (center L n) hr (wA L n r * F0) ψ⟫_ℂ = 0 := by
  rw [Jinner hr]
  have : ∮ z in C(center L n, r), ⟪chi L n j, extC (wA L n r * F0) z ψ⟫_ℂ =
      ∮ z in C(center L n, r), ⟪chi L n j, ψ⟫_ℂ := by
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [QuantumNLS.Local003Bridge.extC_wA_mul _ hz, extC_F0 F0 hF0e hz]
    show ⟪chi L n j, (((z - center L n) • resolvent L κ (fun _ => 0) (parity n) z) : H2 L →L[ℂ] H2 L) ψ⟫_ℂ = _
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, free_inner_res (κ := κ) hL hr hr2 n j hz,
      ← mul_assoc, mul_inv_cancel₀ (ne_center hr hz), one_mul]
  rw [this, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
    (f := fun _ => ⟪chi L n j, ψ⟫_ℂ) continuousOn_const (fun _ _ => differentiableAt_const _), mul_zero]

/-- `D_0 E = 0`. -/
lemma D0_embed (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (F0 : Alg L (center L n) r)
    (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz) (v : E2) :
    Jclm L (center L n) hr (wA L n r * F0) (embed L n v) = 0 := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hres : ∀ z : ℂ, ‖z - center L n‖ = r → ∃ R, IsResolvent L κ (fun _ => 0) (parity n) z R :=
    fun z hz => (hyp.res r n z hr hr2 hz).imp fun _ h => h.1
  have hD : Jclm L (center L n) hr (wA L n r * F0) = dressedIntegral L κ (fun _ => 0) n r := by
    rw [Jclm_apply]
    unfold dressedIntegral Jfun
    congr 1
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [QuantumNLS.Local003Bridge.extC_wA_mul _ hz, extC_F0 F0 hF0e hz]
  rw [hD]
  exact dressedIntegral_free_embed hL n hr hres v

/-- The pointwise matrix element `⟨χ_{n,2}(x), V_w χ_{n,1}(x)⟩ = (2i√κ/L) e^{-ip_n x} w`. -/
lemma inner_pt (hL : 0 < L) (κ : ℝ) (n : ℤ) (w : ℂ) (x : ℝ) :
    ⟪chiFun L n 1 x, Vpt κ w (chiFun L n 0 x)⟫_ℂ =
      2 * Complex.I * (Real.sqrt κ : ℂ) / (L : ℂ) * (Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ))) * w) := by
  have hs : ((Real.sqrt L)⁻¹ : ℝ) * (Real.sqrt L)⁻¹ = L⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hL.le]
  have hsc : ((Real.sqrt L : ℝ) : ℂ)⁻¹ * ((Real.sqrt L : ℝ) : ℂ)⁻¹ = (L : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hL.le]
  have e1 : conj (Complex.exp (rate L n 1 * (x : ℂ))) = Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ)) / 2) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [rate, sgn, Complex.conj_ofReal, map_ofNat]
    ring
  have e2 : Complex.exp (rate L n 0 * (x : ℂ)) = Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ)) / 2) := by
    congr 1
    simp [rate, sgn]
    ring
  have e3 : Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ)) / 2) * Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ)) / 2) =
      Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp [chiFun, Vpt, lopPt, Jm, vec2, PiLp.inner_apply, Fin.sum_univ_two, EuclideanSpace.single_apply, e1, e2]
  rw [← e3, show (2 * Complex.I * (Real.sqrt κ : ℂ) / (L : ℂ)) =
    2 * Complex.I * (Real.sqrt κ : ℂ) * (L : ℂ)⁻¹ from div_eq_mul_inv _ _, ← hsc]
  ring

/-- The scalar `I0 = (2i√κ/L) ∫ e^{-ip_n x} u(x) dx`. -/
def I0 (κ L : ℝ) (n : ℤ) (u : Lp ℂ 2 (μI L)) : ℂ :=
  2 * Complex.I * (Real.sqrt κ : ℂ) / (L : ℂ) *
    ∫ x, Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ))) * (u : ℝ → ℂ) x ∂(μI L)

/-- `⟨χ_{n,2}, T χ_{n,1}⟩ = (z - p_n)⁻¹ I0` for the multiplication operator `T = V_u R_0(z)`. -/
lemma Yinner (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L)) {z : ℂ}
    (hz : z ∈ sphere (center L n) r) {T : H2 L →L[ℂ] H2 L}
    (hT : IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) z) (u : ℝ → ℂ) T) :
    ⟪chi L n 1, T (chi L n 0)⟫_ℂ = (z - center L n)⁻¹ * I0 κ L n u := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hz' : ‖z - (pm L n : ℂ)‖ = r := mem_sphere_iff_norm.mp hz
  obtain ⟨Rz, hRz, -⟩ := hyp.res r n z hr hr2 hz'
  have h1 := QuantumNLS.LocalSpectral.resolvent_free_chi (κ := κ) hL n 0 z ⟨Rz, hRz⟩
  have hne := ne_center hr hz
  have h2 : resolvent L κ (fun _ => 0) (parity n) z (chi L n 0) = (z - center L n)⁻¹ • chi L n 0 := by
    calc _ = (z - center L n)⁻¹ • ((z - center L n) • resolvent L κ (fun _ => 0) (parity n) z (chi L n 0)) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by rw [h1]
  have hT0 := hT (chi L n 0)
  rw [h2] at hT0
  have hc0 : (chi L n 0 : ℝ → E2) =ᵐ[μI L] chiFun L n 0 := (memLp_chiFun L n 0).coeFn_toLp
  have hc1 : (chi L n 1 : ℝ → E2) =ᵐ[μI L] chiFun L n 1 := (memLp_chiFun L n 1).coeFn_toLp
  have hsm := Lp.coeFn_smul ((z - center L n)⁻¹) (chi L n 0)
  rw [MeasureTheory.L2.inner_def]
  have hae : ∀ᵐ x ∂(μI L), ⟪(chi L n 1 : ℝ → E2) x, (T (chi L n 0) : ℝ → E2) x⟫_ℂ =
      (z - center L n)⁻¹ * (2 * Complex.I * (Real.sqrt κ : ℂ) / (L : ℂ) *
        (Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ))) * (u : ℝ → ℂ) x)) := by
    filter_upwards [hc0, hc1, hT0, hsm] with x a0 a1 aT as
    rw [aT, as, Pi.smul_apply, a0, a1, Vpt_smul, inner_smul_right, inner_pt hL κ n ((u : ℝ → ℂ) x) x]
  rw [integral_congr_ae hae, integral_const_mul, integral_const_mul]
  unfold I0
  ring

/-- `⟨χ_{n,2}, D_1 χ_{n,1}⟩ = I0` for `D_1 = J(w · F_0 · G u)`. -/
lemma D1_entry (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (F0 : Alg L (center L n) r)
    (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz)
    (u : Lp ℂ 2 (μI L)) (Y : Alg L (center L n) r)
    (hY : ∀ zz : sphere (center L n) r,
      IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (Y zz)) :
    ⟪chi L n 1, Jclm L (center L n) hr (wA L n r * (F0 * Y)) (chi L n 0)⟫_ℂ = I0 κ L n u := by
  rw [Jinner hr]
  have : ∮ z in C(center L n, r), ⟪chi L n 1, extC (wA L n r * (F0 * Y)) z (chi L n 0)⟫_ℂ =
      ∮ z in C(center L n, r), (z - center L n)⁻¹ • I0 κ L n u := by
    refine circleIntegral.integral_congr hr.le (fun z hz => ?_)
    rw [QuantumNLS.Local003Bridge.extC_wA_mul _ hz, extC_apply _ hz, ContinuousLinearMap.smul_apply,
      ContinuousMap.mul_apply, ContinuousLinearMap.mul_apply, inner_smul_right, hF0e ⟨z, hz⟩]
    rw [free_inner_res (κ := κ) hL hr hr2 n 1 hz, Yinner hL hr hr2 n u hz (hY ⟨z, hz⟩), smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_center hr hz), one_mul]
  rw [this, circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr),
    smul_eq_mul, ← mul_assoc]
  have h2 : ((2 * Real.pi * Complex.I)⁻¹ : ℂ) * (2 * Real.pi * Complex.I) = 1 :=
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero])
  rw [h2, one_mul]

/-! ### The derivative along the complex line `ζ ↦ ζ • Y` -/

lemma invSqrtM_one : invSqrtM (1 : E2 →L[ℂ] E2) = 1 := by
  unfold invSqrtM
  rw [tsum_eq_single 0]
  · simp [invSqrtCoeff]
  · intro k hk
    have : ((1 : E2 →L[ℂ] E2) - 1) ^ k = 0 := by rw [sub_self]; exact zero_pow hk
    rw [this]; ext v; simp

lemma adjE_apply (n : ℤ) (ψ : H2 L) (j : Fin 2) :
    (ContinuousLinearMap.adjoint (embed L n) ψ) j = ⟪chi L n j, ψ⟫_ℂ := by
  have h1 : (ContinuousLinearMap.adjoint (embed L n) ψ) j =
      ⟪EuclideanSpace.single j (1 : ℂ), ContinuousLinearMap.adjoint (embed L n) ψ⟫_ℂ := by
    simp [EuclideanSpace.inner_single_left]
  rw [h1, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  rw [embed_apply]
  fin_cases j <;> simp

section Generic
variable {A B C : Type*} [NormedRing A] [NormedAlgebra ℂ A] [HasSummableGeomSeries A]
  [NormedRing B] [NormedAlgebra ℂ B] [NormedRing C] [NormedAlgebra ℂ C]

lemma hasDerivAt_inv_gen (Y : A) :
    HasDerivAt (fun ζ : ℂ => Ring.inverse ((1 : A) - ζ • Y)) Y 0 := by
  have hl : HasDerivAt (fun ζ : ℂ => (1 : A) - ζ • Y) (-Y) 0 := by
    have := (hasDerivAt_const (0 : ℂ) (1 : A)).sub ((hasDerivAt_id (0 : ℂ)).smul_const Y)
    exact this.congr_deriv (by simp)
  have hf := hasFDerivAt_ringInverse (𝕜 := ℂ) (R := A) (1 : Aˣ)
  have := hf.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
  exact this.congr_deriv (by simp)

/-- Derivative of `S · M · S` along the line, when `M(0) = 0`, `S(0) = 1`. -/
lemma hasDerivAt_B (Jc : A →L[ℂ] B) (Fm : B →L[ℂ] C) (S : C → C) (F0 Y W : A)
    (hS : DifferentiableAt ℂ (fun ζ : ℂ => S (Fm (Jc (F0 * Ring.inverse ((1 : A) - ζ • Y))))) 0)
    (hS0 : S (Fm (Jc F0)) = 1) (hM0 : Fm (Jc F0 * Jc (W * F0) * Jc F0) = 0) :
    HasDerivAt (fun ζ : ℂ =>
      S (Fm (Jc (F0 * Ring.inverse ((1 : A) - ζ • Y)))) *
        Fm (Jc (F0 * Ring.inverse ((1 : A) - ζ • Y)) * Jc (W * (F0 * Ring.inverse ((1 : A) - ζ • Y))) *
          Jc (F0 * Ring.inverse ((1 : A) - ζ • Y))) *
        S (Fm (Jc (F0 * Ring.inverse ((1 : A) - ζ • Y)))))
      (Fm (Jc (F0 * Y) * Jc (W * F0) * Jc F0 + Jc F0 * Jc (W * (F0 * Y)) * Jc F0 +
        Jc F0 * Jc (W * F0) * Jc (F0 * Y))) 0 := by
  have hI := hasDerivAt_inv_gen (A := A) Y
  have hR : HasDerivAt (fun ζ : ℂ => F0 * Ring.inverse ((1 : A) - ζ • Y)) (F0 * Y) 0 := hI.const_mul F0
  have hR0 : F0 * Ring.inverse ((1 : A) - (0 : ℂ) • Y) = F0 := by simp
  have hP : HasDerivAt (fun ζ : ℂ => Jc (F0 * Ring.inverse ((1 : A) - ζ • Y))) (Jc (F0 * Y)) 0 :=
    Jc.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hR
  have hRW : HasDerivAt (fun ζ : ℂ => W * (F0 * Ring.inverse ((1 : A) - ζ • Y))) (W * (F0 * Y)) 0 :=
    hR.const_mul W
  have hD : HasDerivAt (fun ζ : ℂ => Jc (W * (F0 * Ring.inverse ((1 : A) - ζ • Y)))) (Jc (W * (F0 * Y))) 0 :=
    Jc.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hRW
  have hPD := hP.fun_mul hD
  have hPDP := hPD.fun_mul hP
  have hM := Fm.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hPDP
  have hSd := hS.hasDerivAt
  have hfin := (hSd.fun_mul hM).fun_mul hSd
  convert hfin using 1
  · funext ζ; rfl
  simp only [Function.comp_apply, zero_smul, sub_zero, Ring.inverse_one, mul_one, hS0, hM0, add_mul, mul_zero,
    zero_add, one_mul, zero_mul, add_zero]

end Generic

/-! ### Concrete assembly -/

section Concrete
variable (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (F0 : Alg L (center L n) r)
  (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz)
  (hF0n : ‖F0‖ ≤ 1 / r)
  (hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n))

include hL in
lemma adjE_E (v : E2) : ContinuousLinearMap.adjoint (embed L n) (embed L n v) = v :=
  congrArg (fun T : E2 →L[ℂ] E2 => T v) (adjoint_embed_comp_embed hL n)

include hL hP0 in
lemma P0_embed (v : E2) : Jclm L (center L n) hr F0 (embed L n v) = embed L n v := by
  rw [hP0]; simp [adjE_E hL n v]

include hL hP0 in
lemma adjE_P0 (ψ : H2 L) :
    ContinuousLinearMap.adjoint (embed L n) (Jclm L (center L n) hr F0 ψ) =
      ContinuousLinearMap.adjoint (embed L n) ψ := by
  rw [hP0]; simp [adjE_E hL n]

include hL hP0 in
lemma Fm_P0 : Fm L n (Jclm L (center L n) hr F0) = 1 := by
  ext1 v
  simp only [Fm, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.one_apply]
  rw [P0_embed hL hr n F0 hP0, adjE_E hL n]

include hL hr hr2 hF0e in
lemma adjE_D0 (ψ : H2 L) :
    ContinuousLinearMap.adjoint (embed L n) (Jclm L (center L n) hr (wA L n r * F0) ψ) = 0 := by
  ext j
  rw [adjE_apply]
  simpa using adj_D0 (κ := κ) hL hr hr2 n F0 hF0e j ψ

include hL hr hr2 hF0e hP0 in
/-- **R2.** `d/dζ bn(ζ Y)|₀ = I0` for `Y = G u`. -/
theorem hasDerivAt_bn_line (u : Lp ℂ 2 (μI L)) (Y : Alg L (center L n) r)
    (hY : ∀ zz : sphere (center L n) r,
      IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (Y zz)) :
    HasDerivAt (fun ζ : ℂ => bn L n hr F0 (ζ • Y)) (I0 κ L n u) 0 := by
  -- differentiability of `S`
  have hS : DifferentiableAt ℂ (fun ζ : ℂ => invSqrtM (Fm L n (Jclm L (center L n) hr
      (F0 * Ring.inverse ((1 : Alg L (center L n) r) - ζ • Y))))) 0 := by
    have h1 : ‖(0 : Alg L (center L n) r)‖ < 1 := (norm_zero (E := Alg L (center L n) r)).trans_lt zero_lt_one
    have hR := analyticAt_Rn F0 h1
    have hJ : AnalyticAt ℂ (⇑(Jclm L (center L n) hr))
        ((fun Y : Alg L (center L n) r => F0 * Ring.inverse (1 - Y)) 0) :=
      by first
        | exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (Jclm L (center L n) hr) _
        | apply ContinuousLinearMap.analyticAt
        | exact ((Jclm L (center L n) hr).restrictScalars ℂ).analyticAt _
    have hP : AnalyticAt ℂ (Pn L n hr F0) 0 :=
      AnalyticAt.comp (f := fun Y : Alg L (center L n) r => F0 * Ring.inverse (1 - Y)) hJ hR
    have hC : AnalyticAt ℂ (fun Y => Fm L n (Pn L n hr F0 Y)) 0 :=
      ((Fm L n).analyticAt (Pn L n hr F0 0)).comp hP
    have hC0 : Fm L n (Pn L n hr F0 0) - 1 = 0 := by
      have : Pn L n hr F0 0 = Jclm L (center L n) hr F0 := by
        unfold Pn; simp
      rw [this, Fm_P0 hL hr n F0 hP0, sub_self]
    have hS' : AnalyticAt ℂ (Sn L n hr F0) 0 := by
      have h1' : AnalyticAt ℂ (fun Y => Fm L n (Pn L n hr F0 Y) - 1) 0 := hC.sub analyticAt_const
      have h2 := invSqrt_analyticAt (T0 := Fm L n (Pn L n hr F0 0) - 1) (by rw [hC0]; simp)
      exact AnalyticAt.comp (f := fun Y => Fm L n (Pn L n hr F0 Y) - 1) (x := 0) h2 h1'
    have hl0 : AnalyticAt ℂ (⇑(ContinuousLinearMap.toSpanSingleton ℂ Y)) (0 : ℂ) := by
      first
        | exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (ContinuousLinearMap.toSpanSingleton ℂ Y) _
        | apply ContinuousLinearMap.analyticAt
        | exact ((ContinuousLinearMap.toSpanSingleton ℂ Y).restrictScalars ℂ).analyticAt _
    have hline : AnalyticAt ℂ (fun ζ : ℂ => ζ • Y) 0 := hl0
    have hS'' : AnalyticAt ℂ (Sn L n hr F0) ((fun ζ : ℂ => ζ • Y) 0) := by
      convert hS' using 1
      exact zero_smul ℂ Y
    exact (AnalyticAt.comp (f := fun ζ : ℂ => ζ • Y) (x := 0) hS'' hline).differentiableAt
  have hS0 : invSqrtM (Fm L n (Jclm L (center L n) hr F0)) = 1 := by
    rw [Fm_P0 hL hr n F0 hP0]; exact invSqrtM_one
  have he0 : embed L n (vec2 1 0) = chi L n 0 := by simp [embed_apply, vec2]
  have hD0 : Jclm L (center L n) hr (wA L n r * F0) (chi L n 0) = 0 := by
    rw [← he0]; exact D0_embed (κ := κ) hL hr hr2 n F0 hF0e _
  have hP0c : Jclm L (center L n) hr F0 (chi L n 0) = chi L n 0 := by
    rw [← he0]; exact P0_embed hL hr n F0 hP0 _
  have hP0i : ∀ w : H2 L, ⟪chi L n 1, Jclm L (center L n) hr F0 w⟫_ℂ = ⟪chi L n 1, w⟫_ℂ := fun w => by
    have := congrArg (fun x : E2 => x 1) (adjE_P0 hL hr n F0 hP0 w)
    simpa [adjE_apply] using this
  have hM0 : Fm L n (Jclm L (center L n) hr F0 * Jclm L (center L n) hr (wA L n r * F0) *
      Jclm L (center L n) hr F0) = 0 := by
    ext1 v
    simp only [Fm, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply]
    rw [P0_embed hL hr n F0 hP0, D0_embed (κ := κ) hL hr hr2 n F0 hF0e, map_zero, map_zero]
  have hB := @hasDerivAt_B (Alg L (center L n) r) (H2 L →L[ℂ] H2 L) (E2 →L[ℂ] E2) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (Jclm L (center L n) hr) (Fm L n) invSqrtM F0 Y (wA L n r) hS hS0 hM0
  let Λ : (E2 →L[ℂ] E2) →L[ℂ] ℂ :=
    (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℂ] ℂ).comp (ContinuousLinearMap.apply ℂ E2 (vec2 1 0))
  have hΛ := Λ.hasFDerivAt.comp_hasDerivAt (0 : ℂ) hB
  convert hΛ using 1
  · funext ζ; rfl
  have hΛv : ∀ X : H2 L →L[ℂ] H2 L, Λ (Fm L n X) = ⟪chi L n 1, X (chi L n 0)⟫_ℂ := by
    intro X
    show (Fm L n X (vec2 1 0)) 1 = _
    simp only [Fm, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
    rw [adjE_apply, he0]
  rw [hΛv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, inner_add_right, hP0c, hD0, map_zero,
    inner_zero_right, hP0i]
  rw [D1_entry (κ := κ) hL hr hr2 n F0 hF0e u Y hY, adj_D0 (κ := κ) hL hr hr2 n F0 hF0e 1]
  ring

/-- The `n`-th Fourier coefficient of an interval profile: `u_n = L^{-1/2} ∫₀^L e^{-2πinx/L} u(x) dx`. -/
def uCoeff (L : ℝ) (n : ℤ) (u : Lp ℂ 2 (μI L)) : ℂ :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∫ x, Complex.exp (-(Complex.I * (pm L n : ℂ) * (x : ℂ))) * (u : ℝ → ℂ) x ∂(μI L)

lemma I0_eq (hL : 0 < L) (hκ : 0 ≤ κ) (n : ℤ) (u : Lp ℂ 2 (μI L)) :
    I0 κ L n u = 2 * Complex.I * ((Real.sqrt (κ / L) : ℝ) : ℂ) * uCoeff L n u := by
  unfold I0 uCoeff
  have hsq : Real.sqrt (κ / L) = Real.sqrt κ / Real.sqrt L := Real.sqrt_div hκ L
  have hLpos : (Real.sqrt L : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  have hLc : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLpos
  have hsc : ((Real.sqrt L : ℝ) : ℂ) * ((Real.sqrt L : ℝ) : ℂ) = (L : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hL.le]
  rw [hsq]
  push_cast
  rw [← hsc]
  field_simp

end Concrete

section Final
variable (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (F0 : Alg L (center L n) r)
  (hF0e : ∀ zz : sphere (center L n) r, F0 zz = resolvent L κ (fun _ => 0) (parity n) zz)
  (hP0 : Jclm L (center L n) hr F0 = embed L n ∘L ContinuousLinearMap.adjoint (embed L n))

include hL hr hr2 hF0e hP0 in
/-- **R2 (first-order identification).** `d/dζ bn(ζ G u)|₀ = ⟨χ_{n,2}, V_u χ_{n,1}⟩ = 2i√(κ/L) u_n`. -/
theorem first_order (hκ : 0 ≤ κ) (u : Lp ℂ 2 (μI L)) (Y : Alg L (center L n) r)
    (hY : ∀ zz : sphere (center L n) r,
      IsMulOp κ (resolvent L κ (fun _ => 0) (parity n) zz) (u : ℝ → ℂ) (Y zz)) :
    deriv (fun ζ : ℂ => bn L n hr F0 (ζ • Y)) 0 =
      2 * Complex.I * ((Real.sqrt (κ / L) : ℝ) : ℂ) * uCoeff L n u := by
  rw [(hasDerivAt_bn_line (κ := κ) hL hr hr2 n F0 hF0e hP0 u Y hY).deriv, I0_eq hL hκ]

end Final


end QuantumNLS.Local003First
#print axioms QuantumNLS.Local003First.free_inner_res
#print axioms QuantumNLS.Local003First.adj_D0
#print axioms QuantumNLS.Local003First.D0_embed
#print axioms QuantumNLS.Local003First.inner_pt
#print axioms QuantumNLS.Local003First.Yinner
#print axioms QuantumNLS.Local003First.D1_entry
#print axioms QuantumNLS.Local003First.hasDerivAt_B
#print axioms QuantumNLS.Local003First.hasDerivAt_bn_line
#print axioms QuantumNLS.Local003First.first_order

