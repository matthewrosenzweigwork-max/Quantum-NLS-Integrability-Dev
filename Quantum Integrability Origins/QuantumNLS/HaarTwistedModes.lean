import Mathlib
import QuantumNLS.HaarResolvent
import QuantumNLS.HaarKernelFactorizationSym

/-!
# R-F611926F (R3, one particle): twisted Fourier modes, their orthonormal basis, and `R_z^ρ` on them
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports HKF1 and the R1 modules read-only)

For `δ ∈ {0, 1/2}` (`δ_r`) and `ρ = e^{2πiδ} = ±1` (`ρ_r`), the twisted modes `e_k^δ(x) = L^{-1/2} e^{iω(k+δ)x}`,
`k ∈ ℤ`, `ω = 2π/L`, on `[0,L)` (representatives `rep₁`):
* `tbasis L δ : HilbertBasis ℤ ℂ (L²(𝕋_L))`: they form an orthonormal basis of `L²(0,L)` (`tbasis_apply`,
  `tmodeLp_ae`).  Construction: `e_k^δ = M_δ e_k` with `e_k` the untwisted Fourier basis (`fourierL2`) and
  `M_δ` multiplication by the unimodular phase `e^{iωδx}`, a unitary (`twistEquiv`).
* **`R1_tmode`**: for `q = ρ e^{izL} ≠ 1`, `R_z^ρ e_k^δ = i/(z − ω(k+δ)) e_k^δ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.HaarTwisted

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolventAnalysis QuantumNLS.HaarResolvent
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.Fourier

section Eigen

variable {L : ℝ} [Fact (0 < L)]

theorem Fpr_congr_ae {z : ℂ} {ψ ψ' : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ L)
    (h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L → ψ t = ψ' t) : Fpr z ψ a = Fpr z ψ' a := by
  unfold Fpr
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h] with t ht hmem
  rw [uIoc_of_le ha] at hmem
  beta_reduce
  rw [ht ⟨hmem.1, hmem.2.trans ha'⟩]

theorem gsol_congr_ae {q z : ℂ} {ψ ψ' : ℝ → ℂ} {a : ℝ} (ha : a ∈ Icc 0 L)
    (h : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L → ψ t = ψ' t) :
    gsol L q z ψ a = gsol L q z ψ' a := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  unfold gsol
  rw [Fpr_congr_ae ha.1 ha.2 h, Fpr_congr_ae hL le_rfl h]

/-- `∫₀ᵃ e^{-izt} (L^{-1/2} e^{iwt}) dt = L^{-1/2} (e^{c a} − 1)/c`, `c = i(w − z) ≠ 0`. -/
theorem Fpr_exp {z : ℂ} {w : ℝ} (hc : Complex.I * ((w : ℂ) - z) ≠ 0) (a : ℝ) :
    Fpr z (fun t : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * t)) a =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        ((Complex.exp (Complex.I * ((w : ℂ) - z) * a) - 1) / (Complex.I * ((w : ℂ) - z))) := by
  set c : ℂ := Complex.I * ((w : ℂ) - z) with hcdef
  have h1 : Fpr z (fun t : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * t)) a =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∫ t in (0 : ℝ)..a, Complex.exp (c * t) := by
    unfold Fpr
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    have : Complex.exp (-(Complex.I * z) * t) * Complex.exp (Complex.I * (w : ℂ) * t) =
        Complex.exp (c * t) := by
      rw [← Complex.exp_add, hcdef]; congr 1; ring
    rw [← this]; ring
  rw [h1]
  congr 1
  have h2 := integral_cexp_mul c (a := 0) (b := a)
  rw [intervalIntegral.integral_const_mul] at h2
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h2
  field_simp
  linear_combination h2

theorem gsol_alg (s c q Ea EL Ez Ew k : ℂ) (h1 : (1 - q) ≠ 0) (hc : c ≠ 0) (hqE : q * EL = 1)
    (hexp : Ez * Ea = Ew) (hk : k * c = 1) :
    Ez * (s * ((Ea - 1) / c) + q * (s * ((EL - 1) / c)) / (1 - q)) = k * (s * Ew) := by
  have hq' : q * (EL - 1) = 1 - q := by linear_combination hqE
  have e1 : q * (s * ((EL - 1) / c)) / (1 - q) = s / c := by
    rw [div_eq_iff h1]
    calc q * (s * ((EL - 1) / c)) = (s / c) * (q * (EL - 1)) := by ring
      _ = (s / c) * (1 - q) := by rw [hq']
  have hkc : k = c⁻¹ := eq_inv_of_mul_eq_one_left hk
  rw [e1, ← hexp, hkc]
  field_simp
  ring

/-- **The resolvent on an exponential**: for `e^{iwL} = ρ`, `ρ² = 1`, `q = ρ e^{izL} ≠ 1` and `a ∈ [0,L]`:
`gsol(L^{-1/2} e^{iwt})(a) = i/(z − w) L^{-1/2} e^{iwa}`. -/
theorem gsol_exp {ρ z : ℂ} {w : ℝ} (hρ : ρ * ρ = 1) (hw : Complex.exp (Complex.I * (w : ℂ) * L) = ρ)
    (hq : qOf L ρ z ≠ 1) {a : ℝ} (ha : a ∈ Icc 0 L) :
    gsol L (qOf L ρ z) z (fun t : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * t)) a =
      (Complex.I / (z - (w : ℂ))) *
        ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * (w : ℂ) * a)) := by
  have h1 : (1 - qOf L ρ z) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  have hzw : z ≠ (w : ℂ) := by
    intro h
    apply hq
    unfold qOf
    rw [h, hw, hρ]
  have hc : Complex.I * ((w : ℂ) - z) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (sub_ne_zero.2 (Ne.symm hzw))
  have hzw' : z - (w : ℂ) ≠ 0 := sub_ne_zero.2 hzw
  unfold gsol
  rw [Fpr_exp hc, Fpr_exp hc]
  have hEL : Complex.exp (Complex.I * ((w : ℂ) - z) * (L : ℂ)) =
      ρ * Complex.exp (-(Complex.I * z * L)) := by
    rw [show Complex.I * ((w : ℂ) - z) * (L : ℂ) =
      Complex.I * (w : ℂ) * L + -(Complex.I * z * L) by ring, Complex.exp_add, hw]
  have hqE : qOf L ρ z * Complex.exp (Complex.I * ((w : ℂ) - z) * (L : ℂ)) = 1 := by
    rw [hEL]; unfold qOf
    calc ρ * Complex.exp (Complex.I * z * L) * (ρ * Complex.exp (-(Complex.I * z * L)))
        = (ρ * ρ) * (Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * z * L))) := by ring
      _ = 1 := by rw [hρ, exp_mul_exp_neg, one_mul]
  have hexp : Complex.exp (Complex.I * z * (a : ℂ)) * Complex.exp (Complex.I * ((w : ℂ) - z) * (a : ℂ)) =
      Complex.exp (Complex.I * (w : ℂ) * a) := by
    rw [← Complex.exp_add]; congr 1; ring
  have hk : (Complex.I / (z - (w : ℂ))) * (Complex.I * ((w : ℂ) - z)) = 1 := by
    calc (Complex.I / (z - (w : ℂ))) * (Complex.I * ((w : ℂ) - z))
        = (Complex.I * Complex.I) * (((w : ℂ) - z) / (z - (w : ℂ))) := by ring
      _ = (-1) * (((w : ℂ) - z) / (z - (w : ℂ))) := by rw [Complex.I_mul_I]
      _ = 1 := by
        rw [show ((w : ℂ) - z) = -(z - (w : ℂ)) by ring, neg_div, div_self hzw']; ring
  exact gsol_alg _ _ _ _ _ _ _ _ h1 hc hqE hexp hk

end Eigen

/-! ### Twisted modes: the unitary twist and the Hilbert basis -/

section Basis

variable (L : ℝ) [Fact (0 < L)]

/-- The unimodular phase `e^{iωδx}` on the representatives `[0,L)`. -/
def phase (δ : ℝ) (x : AddCircle L) : ℂ :=
  Complex.exp (Complex.I * ((omegaL L * δ : ℝ) : ℂ) * (rep1 L x : ℂ))

theorem norm_phase (δ : ℝ) (x : AddCircle L) : ‖phase L δ x‖ = 1 := by
  unfold phase
  have : Complex.I * ((omegaL L * δ : ℝ) : ℂ) * (rep1 L x : ℂ) =
      ((omegaL L * δ * rep1 L x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

theorem measurable_phase (δ : ℝ) : Measurable (phase L δ) := by
  unfold phase
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_rep1 L)))

theorem conj_phase_mul (δ : ℝ) (x : AddCircle L) : conj (phase L δ x) * phase L δ x = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]; simp

/-- Multiplication by `e^{iωδx}`. -/
def twistOp (δ : ℝ) : L2T L →L[ℂ] L2T L :=
  mulOp (phase L δ) (measurable_phase L δ) 1 (fun x => (norm_phase L δ x).le)

/-- Multiplication by `e^{-iωδx}`. -/
def untwistOp (δ : ℝ) : L2T L →L[ℂ] L2T L :=
  mulOp (fun x => conj (phase L δ x))
    (Complex.continuous_conj.measurable.comp (measurable_phase L δ)) 1
    (fun x => by rw [Complex.norm_conj, norm_phase])

theorem untwist_twist (δ : ℝ) (f : L2T L) : untwistOp L δ (twistOp L δ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp (fun x => conj (phase L δ x))
      (Complex.continuous_conj.measurable.comp (measurable_phase L δ)) 1
      (fun x => by rw [Complex.norm_conj, norm_phase]) (twistOp L δ f),
    coeFn_mulOp (phase L δ) (measurable_phase L δ) 1 (fun x => (norm_phase L δ x).le) f] with x h1 h2
  show (untwistOp L δ (twistOp L δ f)) x = f x
  rw [show (untwistOp L δ (twistOp L δ f)) x = conj (phase L δ x) * (twistOp L δ f) x from h1,
    show (twistOp L δ f) x = phase L δ x * f x from h2, ← mul_assoc, conj_phase_mul, one_mul]

theorem twist_untwist (δ : ℝ) (f : L2T L) : twistOp L δ (untwistOp L δ f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp (phase L δ) (measurable_phase L δ) 1 (fun x => (norm_phase L δ x).le)
      (untwistOp L δ f),
    coeFn_mulOp (fun x => conj (phase L δ x))
      (Complex.continuous_conj.measurable.comp (measurable_phase L δ)) 1
      (fun x => by rw [Complex.norm_conj, norm_phase]) f] with x h1 h2
  show (twistOp L δ (untwistOp L δ f)) x = f x
  rw [show (twistOp L δ (untwistOp L δ f)) x = phase L δ x * (untwistOp L δ f) x from h1,
    show (untwistOp L δ f) x = conj (phase L δ x) * f x from h2, ← mul_assoc, mul_comm (phase L δ x),
    conj_phase_mul, one_mul]

theorem norm_twist_le (δ : ℝ) (f : L2T L) : ‖twistOp L δ f‖ ≤ ‖f‖ := by
  have := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (f := twistOp L δ f) (g := f) (by
    filter_upwards [coeFn_mulOp (phase L δ) (measurable_phase L δ) 1
      (fun x => (norm_phase L δ x).le) f] with x hx
    show ‖(twistOp L δ f) x‖ ≤ 1 * ‖f x‖
    rw [show (twistOp L δ f) x = phase L δ x * f x from hx, norm_mul, norm_phase, one_mul])
  simpa using this

theorem norm_untwist_le (δ : ℝ) (f : L2T L) : ‖untwistOp L δ f‖ ≤ ‖f‖ := by
  have := Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (f := untwistOp L δ f) (g := f) (by
    filter_upwards [coeFn_mulOp (fun x => conj (phase L δ x))
      (Complex.continuous_conj.measurable.comp (measurable_phase L δ)) 1
      (fun x => by rw [Complex.norm_conj, norm_phase]) f] with x hx
    show ‖(untwistOp L δ f) x‖ ≤ 1 * ‖f x‖
    rw [show (untwistOp L δ f) x = conj (phase L δ x) * f x from hx, norm_mul, Complex.norm_conj,
      norm_phase, one_mul])
  simpa using this

theorem norm_twist (δ : ℝ) (f : L2T L) : ‖twistOp L δ f‖ = ‖f‖ := by
  refine le_antisymm (norm_twist_le L δ f) ?_
  calc ‖f‖ = ‖untwistOp L δ (twistOp L δ f)‖ := by rw [untwist_twist]
    _ ≤ ‖twistOp L δ f‖ := norm_untwist_le L δ _

/-- Multiplication by `e^{iωδx}` as a unitary of `L²(𝕋_L)`. -/
def twistEquiv (δ : ℝ) : L2T L ≃ₗᵢ[ℂ] L2T L :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (twistOp L δ).toLinearMap, norm_map' := norm_twist L δ }
    (fun g => ⟨untwistOp L δ g, twist_untwist L δ g⟩)

/-- The twisted mode `e_k^δ = e^{iωδx} e_k` as an `L²` class. -/
def tmodeLp (δ : ℝ) (k : ℤ) : L2T L := twistEquiv L δ (modeLp L k)

/-- **The twisted modes form an orthonormal basis of `L²(0,L)`.** -/
def tbasis (δ : ℝ) : HilbertBasis ℤ ℂ (L2T L) :=
  HilbertBasis.ofRepr ((twistEquiv L δ).symm.trans (fourierL2 L))

theorem tbasis_apply (δ : ℝ) (k : ℤ) : tbasis L δ k = tmodeLp L δ k := by
  classical
  rw [← HilbertBasis.repr_symm_single]
  show ((twistEquiv L δ).symm.trans (fourierL2 L)).symm (lp.single 2 k (1 : ℂ)) = _
  rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply, ← fourierL2_modeLp L k,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem tmodeLp_ae (δ : ℝ) (k : ℤ) :
    ∀ᵐ x ∂(volume : Measure (AddCircle L)), tmodeLp L δ k x =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ) *
        (rep1 L x : ℂ)) := by
  filter_upwards [coeFn_mulOp (phase L δ) (measurable_phase L δ) 1 (fun x => (norm_phase L δ x).le)
    (modeLp L k), coeFn_modeLp L k] with x h1 h2
  show (twistOp L δ (modeLp L k)) x = _
  rw [show (twistOp L δ (modeLp L k)) x = phase L δ x * (modeLp L k) x from h1, h2]
  have hm := mode_coe L k (rep1 L x)
  rw [coe_rep1] at hm
  rw [hm, phase]
  have : Complex.exp (Complex.I * ((omegaL L * δ : ℝ) : ℂ) * (rep1 L x : ℂ)) *
      ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * k * (rep1 L x : ℂ) / L)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((omegaL L * δ : ℝ) : ℂ) * (rep1 L x : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * k * (rep1 L x : ℂ) / L)) := by ring
  rw [this, ← Complex.exp_add]
  congr 2
  unfold omegaL
  push_cast
  ring

end Basis

section Eigenvalue

variable (L : ℝ) [Fact (0 < L)]

theorem psi0_tmode_ae (δ : ℝ) (k : ℤ) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L → psi0 L (tmodeLp L δ k) t =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (Complex.I * ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ) * t) := by
  have h0 := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae (tmodeLp_ae L δ k)
  rw [zero_add, ae_restrict_iff' measurableSet_Ioc] at h0
  filter_upwards [h0, ae_ne_real L] with t ht ht' hmem
  have hr : rep1 L (t : AddCircle L) = t := rep1_coe L ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht'⟩
  have := ht hmem
  simp only [hr] at this
  simpa [psi0] using this

/-- **R3 (one particle): `R_z^ρ e_k^δ = i/(z − ω(k+δ)) e_k^δ`** for `ρ = e^{2πiδ}`, `ρ² = 1`, `q = ρ e^{izL} ≠ 1`. -/
theorem R1_tmode {ρ z : ℂ} {δ : ℝ} (hρ : ρ * ρ = 1)
    (hρδ : Complex.exp (2 * Real.pi * Complex.I * δ) = ρ) (hq : qOf L ρ z ≠ 1) (k : ℤ) :
    R1 L (qOf L ρ z) z (tmodeLp L δ k) =
      (Complex.I / (z - ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ))) • tmodeLp L δ k := by
  have hL : 0 < L := Fact.out
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hw : Complex.exp (Complex.I * ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ) * (L : ℂ)) = ρ := by
    rw [← hρδ]
    have : Complex.I * ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ) * (L : ℂ) =
        (k : ℂ) * (2 * Real.pi * Complex.I) + 2 * Real.pi * Complex.I * δ := by
      unfold omegaL
      push_cast
      field_simp
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  refine Lp.ext ?_
  filter_upwards [R1_apply_ae L (qOf L ρ z) z (tmodeLp L δ k), tmodeLp_ae L δ k,
    Lp.coeFn_smul (Complex.I / (z - ((omegaL L * ((k : ℝ) + δ) : ℝ) : ℂ))) (tmodeLp L δ k)]
    with x hx he hs
  have hxr : rep1 L x ∈ Icc 0 L := ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩
  rw [hx, kernel_integral L hq (intInt_psi0 L _) hxr,
    gsol_congr_ae hxr (psi0_tmode_ae L δ k), gsol_exp hρ hw hq hxr]
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [he]

end Eigenvalue

#print axioms tbasis_apply
#print axioms tmodeLp_ae
#print axioms R1_tmode

end QuantumNLS.HaarTwisted
