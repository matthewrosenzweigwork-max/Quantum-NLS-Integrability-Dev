import Mathlib
import QuantumNLS.HaarKernelFactorizationOp
import QuantumNLS.HaarResolventAnalysis

/-!
# R-F611926F (R1): `R_z^ρ = (D_ρ − iz)^{-1}`
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports HKF1 read-only)

`D_ρ = ∂_x` on `{f ∈ H¹(0,L) : f(L) = ρ f(0)}`, with `H¹` encoded exactly as `LocalSpectralOperator.IsH1Rep`
(absolutely continuous representative `g(x) = g(0) + ∫₀ˣ h`, `h ∈ L²`), here for scalar `L²(𝕋_L) ≅ L²(0,L)`
(`f = g ∘ rep₁` a.e.).  `graphD ρ z` is the graph of `D_ρ − iz`: `(f, ψ)` with `f ∈ dom D_ρ` and `ψ = h − iz g` a.e.

* `R1 q z`: the bounded integral operator with kernel `R_z^ρ(x,y) = e^{iz(x−y)}/(1−q)(1_{x>y} + q 1_{x<y})` (stage 1 `Rk`),
  `q = ρ e^{izL}`, `ρ² = 1`.
* **`resolvent_range`**: for `q ≠ 1`, every `R1 φ` lies in the domain and `(D_ρ − iz)(R1 φ) = φ`.
* **`resolvent_left_inverse`**: `R1 ψ = f` whenever `(f,ψ) ∈ graph(D_ρ − iz)`; hence `R1` is the (two-sided, unique)
  inverse of `D_ρ − iz` (`resolvent_unique`, `injective`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.HaarResolvent

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolventAnalysis

variable (L : ℝ) [Fact (0 < L)]

/-- The representative in `[0,L)` of a point of `𝕋_L`. -/
def rep1 (x : AddCircle L) : ℝ := (AddCircle.equivIco L 0 x : ℝ)

theorem measurable_rep1 : Measurable (rep1 L) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco L 0).measurable

theorem rep1_bounds (x : AddCircle L) : 0 ≤ rep1 L x ∧ rep1 L x < L := by
  have := (AddCircle.equivIco L 0 x).2
  simp only [Set.mem_Ico, zero_add] at this
  exact this

theorem rep1_coe {t : ℝ} (ht : t ∈ Ico 0 L) : rep1 L (t : AddCircle L) = t := by
  unfold rep1
  exact AddCircle.equivIco_coe_of_mem (by simpa using ht)

theorem coe_rep1 (x : AddCircle L) : ((rep1 L x : ℝ) : AddCircle L) = x := by
  unfold rep1
  exact AddCircle.coe_equivIco

/-- The kernel `R_z^ρ(x,y)` on `𝕋_L²` (representatives in `[0,L)`). -/
def R1ker (q z : ℂ) : Kernel (volume : Measure (AddCircle L)) where
  fn p := Rk q z (rep1 L p.1) (rep1 L p.2)
  measurable := by
    have h := (measurable_Rk q z).comp (((measurable_rep1 L).comp measurable_fst).prodMk
      ((measurable_rep1 L).comp measurable_snd))
    exact h
  bound := RB L q z
  bound_nonneg := RB_nonneg L q z
  norm_le p := norm_Rk_le L q z (rep1_bounds L p.1) (rep1_bounds L p.2)

/-- The resolvent operator `R_z^ρ` on `L²(𝕋_L) = L²(0,L)`. -/
def R1 (q z : ℂ) : L2T L →L[ℂ] L2T L := (R1ker L q z).operator

/-- Scalar `H¹` encoding (as in `LocalSpectralOperator.IsH1Rep`): `f = g ∘ rep₁` a.e. on the circle, `h ∈ L²(0,L)`,
`g(x) = g(0) + ∫₀ˣ h` on `[0,L]`. -/
def IsH1Rep (f : L2T L) (g h : ℝ → ℂ) : Prop :=
  (∀ᵐ x ∂(volume : Measure (AddCircle L)), f x = g (rep1 L x)) ∧
    MemLp h 2 (volume.restrict (Ioc 0 L)) ∧ ∀ x ∈ Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s

/-- The graph of `D_ρ − iz` on `D_ρ = {f ∈ H¹ : f(L) = ρ f(0)}`: `(f,ψ)` with `ψ = h − iz g` a.e. -/
def graphD (ρ z : ℂ) : Set (L2T L × L2T L) :=
  {p | ∃ g h, IsH1Rep L p.1 g h ∧ g L = ρ * g 0 ∧
    ∀ᵐ x ∂(volume : Measure (AddCircle L)), p.2 x = h (rep1 L x) - Complex.I * z * g (rep1 L x)}

/-- The domain `D_ρ`. -/
def domainD (ρ : ℂ) : Set (L2T L) := {f | ∃ g h, IsH1Rep L f g h ∧ g L = ρ * g 0}

/-! ### Analysis on `[0,L]` -/

section Analysis

variable {L}

/-- `F(x) = ∫₀ˣ e^{-izt} ψ(t) dt`. -/
def Fpr (z : ℂ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..x, Complex.exp (-(Complex.I * z) * t) * ψ t

/-- The solution `g(x) = e^{izx}(F(x) + qC/(1−q))`, `C = F(L)`. -/
def gsol (L : ℝ) (q z : ℂ) (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * x) * (Fpr z ψ x + q * Fpr z ψ L / (1 - q))

theorem intInt_exp_mul {z : ℂ} {ψ : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hL : a ≤ L)
    (hψ : IntervalIntegrable ψ volume 0 L) :
    IntervalIntegrable (fun t : ℝ => Complex.exp (-(Complex.I * z) * t) * ψ t) volume 0 a := by
  have hc : Continuous (fun t : ℝ => Complex.exp (-(Complex.I * z) * t)) := by fun_prop
  exact (hψ.mono_set (by rw [uIcc_of_le ha, uIcc_of_le (ha.trans hL)]; exact Icc_subset_Icc_right hL)).continuousOn_mul
    hc.continuousOn

theorem continuousOn_Fpr {z : ℂ} {ψ : ℝ → ℂ} (hL : 0 ≤ L) (hψ : IntervalIntegrable ψ volume 0 L) :
    ContinuousOn (Fpr z ψ) (Icc 0 L) := by
  have hint : IntervalIntegrable (fun t : ℝ => Complex.exp (-(Complex.I * z) * t) * ψ t) volume 0 L :=
    intInt_exp_mul hL le_rfl hψ
  have := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) (by simp [hL])
  rw [uIcc_of_le hL] at this
  exact this


theorem exp_mul_exp_neg (w : ℂ) : Complex.exp w * Complex.exp (-w) = 1 := by
  rw [← Complex.exp_add]; simp

theorem exp_cancel (z : ℂ) (t : ℝ) :
    Complex.exp (Complex.I * z * t) * Complex.exp (-(Complex.I * z) * t) = 1 := by
  have : -(Complex.I * z) * (t : ℂ) = -(Complex.I * z * t) := by ring
  rw [this]; exact exp_mul_exp_neg _

theorem Fpr_zero (z : ℂ) (ψ : ℝ → ℂ) : Fpr z ψ 0 = 0 := by simp [Fpr]

theorem gsol_zero (q z : ℂ) (ψ : ℝ → ℂ) : gsol L q z ψ 0 = q * Fpr z ψ L / (1 - q) := by
  simp [gsol, Fpr_zero]

theorem gsol_boundary {q ρ z : ℂ} (hq : q ≠ 1) (hρq : ρ * q = Complex.exp (Complex.I * z * L))
    (ψ : ℝ → ℂ) : gsol L q z ψ L = ρ * gsol L q z ψ 0 := by
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  rw [gsol_zero, gsol, ← hρq]
  field_simp
  ring

/-- **The ODE**: `g(x) = g(0) + ∫₀ˣ (iz g + ψ)` on `[0,L]`. -/
theorem gsol_ode (q z : ℂ) {ψ : ℝ → ℂ} (hL : 0 ≤ L) (hψ : IntervalIntegrable ψ volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    gsol L q z ψ x = gsol L q z ψ 0 + ∫ t in (0 : ℝ)..x, (Complex.I * z * gsol L q z ψ t + ψ t) := by
  have hx0 : 0 ≤ x := hx.1
  set κ : ℂ := q * Fpr z ψ L / (1 - q) with hκ
  have hu : IntervalIntegrable (fun t : ℝ => Complex.exp (-(Complex.I * z) * t) * ψ t) volume 0 x :=
    intInt_exp_mul hx0 hx.2 hψ
  have hψx : IntervalIntegrable ψ volume 0 x :=
    hψ.mono_set (by rw [uIcc_of_le hx0, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2)
  have hF : ContinuousOn (Fpr z ψ) (Icc 0 x) :=
    (continuousOn_Fpr hL hψ).mono (Icc_subset_Icc_right hx.2)
  have hA : IntervalIntegrable (fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * t) *
      Fpr z ψ t) volume 0 x := by
    have hc : Continuous (fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * t)) := by
      fun_prop
    have : ContinuousOn (fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * t) *
        Fpr z ψ t) (uIcc 0 x) := by
      rw [uIcc_of_le hx0]; exact hc.continuousOn.mul hF
    exact this.intervalIntegrable
  have h1 : Complex.exp (Complex.I * z * x) * Fpr z ψ x =
      ∫ t in (0 : ℝ)..x, (Complex.I * z * Complex.exp (Complex.I * z * t) * Fpr z ψ t + ψ t) := by
    have h := ibp (Complex.I * z) hx0 hu
    refine h.trans (intervalIntegral.integral_congr (fun t _ => ?_))
    beta_reduce
    have : Complex.exp (Complex.I * z * t) * (Complex.exp (-(Complex.I * z) * t) * ψ t) = ψ t := by
      rw [← mul_assoc, exp_cancel, one_mul]
    rw [this]; rfl
  have hint : ∫ t in (0 : ℝ)..x, (Complex.I * z * gsol L q z ψ t + ψ t) =
      ∫ t in (0 : ℝ)..x, ((Complex.I * z * Complex.exp (Complex.I * z * t) * Fpr z ψ t + ψ t) +
        κ * (Complex.I * z * Complex.exp (Complex.I * z * t))) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [gsol, hκ]
    ring
  have hB : IntervalIntegrable (fun t : ℝ => κ * (Complex.I * z * Complex.exp (Complex.I * z * t)))
      volume 0 x := (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hAB : IntervalIntegrable (fun t : ℝ => Complex.I * z * Complex.exp (Complex.I * z * t) *
      Fpr z ψ t + ψ t) volume 0 x := hA.add hψx
  rw [hint, intervalIntegral.integral_add hAB hB, ← h1, intervalIntegral.integral_const_mul,
    integral_cexp_mul, gsol_zero]
  simp only [gsol, hκ]
  simp [Fpr_zero]
  ring

/-- Left-inverse computation: if `g = g(0) + ∫ h` and `ψ = h − iz g` a.e., then `F_ψ(a) = e^{-iza} g(a) − g(0)`. -/
theorem Fpr_of_h1 (z : ℂ) {g h ψ : ℝ → ℂ} (hL : 0 ≤ L)
    (hh : IntervalIntegrable h volume 0 L)
    (hg : ∀ x ∈ Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s)
    (hψ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L → ψ t = h t - Complex.I * z * g t)
    {a : ℝ} (ha : a ∈ Icc 0 L) :
    Fpr z ψ a = Complex.exp (-(Complex.I * z) * a) * g a - g 0 := by
  have ha0 : 0 ≤ a := ha.1
  set c : ℂ := -(Complex.I * z) with hc
  have hsub : uIcc 0 a ⊆ uIcc 0 L := by
    rw [uIcc_of_le ha0, uIcc_of_le hL]; exact Icc_subset_Icc_right ha.2
  have hha : IntervalIntegrable h volume 0 a := hh.mono_set hsub
  have hG0 : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, h s) (uIcc 0 a) :=
    intervalIntegral.continuousOn_primitive_interval' hha (by simp [ha0])
  -- Step 1
  have h1 : Fpr z ψ a = ∫ t in (0 : ℝ)..a, Complex.exp (c * t) * (h t - Complex.I * z * g t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hψ] with t ht hmem
    rw [uIoc_of_le ha0] at hmem
    simp only [hc] at *
    rw [ht ⟨hmem.1, hmem.2.trans ha.2⟩]
  -- Step 2
  have h2 : ∫ t in (0 : ℝ)..a, Complex.exp (c * t) * (h t - Complex.I * z * g t) =
      ∫ t in (0 : ℝ)..a, ((c * Complex.exp (c * t) * (∫ s in (0 : ℝ)..t, h s) +
        Complex.exp (c * t) * h t) + g 0 * (c * Complex.exp (c * t))) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have htm : t ∈ Icc 0 L := by
      rw [uIcc_of_le ha0] at ht; exact ⟨ht.1, ht.2.trans ha.2⟩
    beta_reduce
    have hcz : Complex.I * z = -c := by rw [hc]; ring
    rw [hg t htm, hcz]
    ring
  have hA : IntervalIntegrable (fun t : ℝ => c * Complex.exp (c * t) * ∫ s in (0 : ℝ)..t, h s)
      volume 0 a := by
    have hcc : Continuous (fun t : ℝ => c * Complex.exp (c * t)) := by fun_prop
    exact (hcc.continuousOn.mul hG0).intervalIntegrable
  have hB : IntervalIntegrable (fun t : ℝ => Complex.exp (c * t) * h t) volume 0 a :=
    hha.continuousOn_mul (by fun_prop : Continuous (fun t : ℝ => Complex.exp (c * t))).continuousOn
  have hC : IntervalIntegrable (fun t : ℝ => g 0 * (c * Complex.exp (c * t))) volume 0 a :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hAB : IntervalIntegrable (fun t : ℝ => c * Complex.exp (c * t) * (∫ s in (0 : ℝ)..t, h s) +
      Complex.exp (c * t) * h t) volume 0 a := hA.add hB
  have h3 := ibp c ha0 hha
  rw [h1, h2, intervalIntegral.integral_add hAB hC, ← h3, intervalIntegral.integral_const_mul,
    integral_cexp_mul, hg a ha]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- **Left-inverse, analytic core**: `gsol` reproduces `g` when `ψ = h − iz g`, `g ∈ H¹`, `g(L) = ρ g(0)`. -/
theorem gsol_eq_of_h1 {q ρ z : ℂ} (hq : q ≠ 1) (hρq : ρ * q = Complex.exp (Complex.I * z * L))
    {g h ψ : ℝ → ℂ} (hL : 0 ≤ L) (hh : IntervalIntegrable h volume 0 L)
    (hg : ∀ x ∈ Icc 0 L, g x = g 0 + ∫ s in (0 : ℝ)..x, h s) (hgL : g L = ρ * g 0)
    (hψ : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L → ψ t = h t - Complex.I * z * g t)
    {a : ℝ} (ha : a ∈ Icc 0 L) : gsol L q z ψ a = g a := by
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  have hFa := Fpr_of_h1 z hL hh hg hψ ha
  have hFL := Fpr_of_h1 z hL hh hg hψ (a := L) ⟨hL, le_rfl⟩
  have hk : ρ * q * Complex.exp (-(Complex.I * z) * L) = 1 := by
    rw [hρq, exp_cancel]
  have hq' : q * (Complex.exp (-(Complex.I * z) * L) * (ρ * g 0) - g 0) / (1 - q) = g 0 := by
    generalize Complex.exp (-(Complex.I * z) * (L : ℂ)) = eL at hk ⊢
    field_simp
    linear_combination (g 0) * hk
  unfold gsol
  rw [hFa, hFL, hgL, hq']
  calc Complex.exp (Complex.I * z * a) * (Complex.exp (-(Complex.I * z) * a) * g a - g 0 + g 0)
      = (Complex.exp (Complex.I * z * a) * Complex.exp (-(Complex.I * z) * a)) * g a := by ring
    _ = g a := by rw [exp_cancel, one_mul]

end Analysis

/-! ### The operator `R1` and the identification with `(D_ρ − iz)^{-1}` -/

section Circle

variable (L : ℝ) [Fact (0 < L)]

/-- `q = ρ e^{izL}`. -/
def qOf (ρ z : ℂ) : ℂ := ρ * Complex.exp (Complex.I * z * L)

/-- The lift `ψ₀(t) = φ(t mod L)` of an `L²(𝕋_L)` class to `ℝ`. -/
def psi0 (φ : L2T L) : ℝ → ℂ := fun t => φ (t : AddCircle L)

theorem memLp_psi0 (φ : L2T L) : MemLp (psi0 L φ) 2 (volume.restrict (Ioc 0 L)) := by
  have h := (Lp.memLp φ).comp_measurePreserving (AddCircle.measurePreserving_mk L 0)
  rw [zero_add] at h
  exact h

theorem intInt_psi0 (φ : L2T L) : IntervalIntegrable (psi0 L φ) volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (Fact.out : 0 < L).le).2
    (MemLp.integrable (by norm_num) (memLp_psi0 L φ))

theorem ae_ne_real : ∀ᵐ t : ℝ, t ≠ L := by
  rw [ae_iff]; simp

theorem exp_split (z : ℂ) (a t : ℝ) :
    Complex.exp (Complex.I * z * ((a - t : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * a) * Complex.exp (-(Complex.I * z) * t) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `R1 φ (x) = ∫₀ᴸ R(x,t) φ(t) dt` almost everywhere. -/
theorem R1_apply_ae (q z : ℂ) (φ : L2T L) :
    ∀ᵐ x ∂(volume : Measure (AddCircle L)), R1 L q z φ x =
      ∫ t in (0 : ℝ)..L, Rk q z (rep1 L x) t * psi0 L φ t := by
  filter_upwards [(R1ker L q z).operator_apply_ae φ] with x hx
  refine hx.trans ?_
  show ∫ w, Rk q z (rep1 L x) (rep1 L w) * φ w ∂(volume : Measure (AddCircle L)) = _
  have h := AddCircle.intervalIntegral_preimage L 0
    (fun w : AddCircle L => Rk q z (rep1 L x) (rep1 L w) * φ w)
  rw [← h, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real L] with t ht hmem
  rw [uIoc_of_le (Fact.out : 0 < L).le] at hmem
  have : rep1 L (t : AddCircle L) = t := rep1_coe L ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩
  simp only [psi0, this]

theorem kernel_integral {q z : ℂ} (hq : q ≠ 1) {ψ : ℝ → ℂ} (hψ : IntervalIntegrable ψ volume 0 L)
    {a : ℝ} (ha : a ∈ Icc 0 L) :
    ∫ t in (0 : ℝ)..L, Rk q z a t * ψ t = gsol L q z ψ a := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have h1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  have hu0 := intInt_exp_mul (z := z) hL le_rfl hψ
  have hua := intInt_exp_mul (z := z) ha.1 ha.2 hψ
  have huaL : IntervalIntegrable (fun t : ℝ => Complex.exp (-(Complex.I * z) * t) * ψ t) volume a L :=
    hu0.mono_set (by rw [uIcc_of_le ha.2, uIcc_of_le hL]; exact Icc_subset_Icc_left ha.1)
  have hne : ∀ᵐ t : ℝ, t ≠ a := by rw [ae_iff]; simp
  -- left piece
  have hf1 : IntervalIntegrable (fun t : ℝ => Rk q z a t * ψ t) volume 0 a := by
    have hP1 : IntervalIntegrable (fun t : ℝ => Complex.exp (Complex.I * z * a) / (1 - q) *
        (Complex.exp (-(Complex.I * z) * t) * ψ t)) volume 0 a := hua.const_mul _
    refine hP1.congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le ha.1] at hmem
    have hlt : t < a := lt_of_le_of_ne hmem.2 ht
    simp only [Rk, if_pos hlt, exp_split]
    ring
  have hf2 : IntervalIntegrable (fun t : ℝ => Rk q z a t * ψ t) volume a L := by
    have hP2 : IntervalIntegrable (fun t : ℝ => q * Complex.exp (Complex.I * z * a) / (1 - q) *
        (Complex.exp (-(Complex.I * z) * t) * ψ t)) volume a L := huaL.const_mul _
    refine hP2.congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall (fun t hmem => ?_))
    rw [uIoc_of_le ha.2] at hmem
    have hlt : a < t := hmem.1
    simp only [Rk, if_neg (not_lt.2 hlt.le), if_pos hlt, exp_split]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hf1 hf2]
  have e1 : ∫ t in (0 : ℝ)..a, Rk q z a t * ψ t =
      Complex.exp (Complex.I * z * a) / (1 - q) * Fpr z ψ a := by
    rw [Fpr, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le ha.1] at hmem
    have hlt : t < a := lt_of_le_of_ne hmem.2 ht
    simp only [Rk, if_pos hlt, exp_split]
    ring
  have e2 : ∫ t in a..L, Rk q z a t * ψ t = q * Complex.exp (Complex.I * z * a) / (1 - q) *
      ∫ t in a..L, Complex.exp (-(Complex.I * z) * t) * ψ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    refine Eventually.of_forall (fun t hmem => ?_)
    rw [uIoc_of_le ha.2] at hmem
    have hlt : a < t := hmem.1
    simp only [Rk, if_neg (not_lt.2 hlt.le), if_pos hlt, exp_split]
    ring
  have e3 : ∫ t in a..L, Complex.exp (-(Complex.I * z) * t) * ψ t = Fpr z ψ L - Fpr z ψ a := by
    have := intervalIntegral.integral_add_adjacent_intervals hua huaL
    rw [Fpr, Fpr]
    rw [← this]; ring
  rw [e1, e2, e3, gsol]
  field_simp
  ring

theorem hgcont {q z : ℂ} {ψ : ℝ → ℂ} (hψ : IntervalIntegrable ψ volume 0 L) :
    ContinuousOn (gsol L q z ψ) (Icc 0 L) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hF := continuousOn_Fpr (z := z) hL hψ
  have hc : Continuous (fun t : ℝ => Complex.exp (Complex.I * z * t)) := by fun_prop
  exact hc.continuousOn.mul (hF.add continuousOn_const)

theorem memLp_gsol {q z : ℂ} {ψ : ℝ → ℂ} (hψ : IntervalIntegrable ψ volume 0 L) :
    MemLp (gsol L q z ψ) 2 (volume.restrict (Ioc 0 L)) := by
  have hc := hgcont (L := L) (q := q) (z := z) hψ
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine MemLp.of_bound ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2
    (Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx))

/-- **R1, range**: for `q = ρ e^{izL} ≠ 1` (`ρ² = 1`), `R_z^ρ φ ∈ dom D_ρ` and `(D_ρ − iz) R_z^ρ φ = φ`. -/
theorem resolvent_range {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) (φ : L2T L) :
    (R1 L (qOf L ρ z) z φ, φ) ∈ graphD L ρ z := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hρq : ρ * qOf L ρ z = Complex.exp (Complex.I * z * L) := by
    unfold qOf; rw [← mul_assoc, hρ, one_mul]
  have hψ := intInt_psi0 L φ
  refine ⟨gsol L (qOf L ρ z) z (psi0 L φ),
    fun t => Complex.I * z * gsol L (qOf L ρ z) z (psi0 L φ) t + psi0 L φ t,
    ⟨?_, ?_, fun x hx => gsol_ode (L := L) _ z hL hψ hx⟩, gsol_boundary hq hρq _, ?_⟩
  · filter_upwards [R1_apply_ae L (qOf L ρ z) z φ] with x hx
    rw [hx]
    exact kernel_integral L hq hψ ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩
  · exact ((memLp_gsol L (q := qOf L ρ z) (z := z) hψ).const_mul (Complex.I * z)).add
      (memLp_psi0 L φ)
  · refine Eventually.of_forall (fun x => ?_)
    have : psi0 L φ (rep1 L x) = φ x := by simp [psi0, coe_rep1]
    simp only [this]; ring

/-- **R1, left inverse**: `R_z^ρ ψ = f` whenever `f ∈ dom D_ρ` and `ψ = (D_ρ − iz) f`. -/
theorem resolvent_left_inverse {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) {f ψ : L2T L}
    (hfψ : (f, ψ) ∈ graphD L ρ z) : R1 L (qOf L ρ z) z ψ = f := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hρq : ρ * qOf L ρ z = Complex.exp (Complex.I * z * L) := by
    unfold qOf; rw [← mul_assoc, hρ, one_mul]
  obtain ⟨g, h, ⟨hf, hmem, hrep⟩, hgL, hψ'⟩ := hfψ
  have hhint : IntervalIntegrable h volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).2 (MemLp.integrable (by norm_num) hmem)
  have hψae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc 0 L →
      psi0 L ψ t = h t - Complex.I * z * g t := by
    have h0 := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae hψ'
    rw [zero_add, ae_restrict_iff' measurableSet_Ioc] at h0
    filter_upwards [h0, ae_ne_real L] with t ht ht' hmem
    have hr : rep1 L (t : AddCircle L) = t := rep1_coe L ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht'⟩
    have := ht hmem
    simp only [hr] at this
    simpa [psi0] using this
  refine Lp.ext ?_
  filter_upwards [R1_apply_ae L (qOf L ρ z) z ψ, hf] with x hx hfx
  rw [hx, hfx, kernel_integral L hq (intInt_psi0 L ψ)
    ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩]
  exact gsol_eq_of_h1 hq hρq hL hhint hrep hgL hψae
    ⟨(rep1_bounds L x).1, (rep1_bounds L x).2.le⟩

/-- `D_ρ − iz` has at most one preimage of each vector, and it is `R_z^ρ`. -/
theorem resolvent_unique {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) {f f' ψ : L2T L}
    (h1 : (f, ψ) ∈ graphD L ρ z) (h2 : (f', ψ) ∈ graphD L ρ z) : f = f' :=
  (resolvent_left_inverse L hρ hq h1).symm.trans (resolvent_left_inverse L hρ hq h2)

/-- `D_ρ − iz` is injective on its domain when `q ≠ 1`. -/
theorem resolvent_injective {ρ z : ℂ} (hρ : ρ * ρ = 1) (hq : qOf L ρ z ≠ 1) {f : L2T L}
    (h : (f, (0 : L2T L)) ∈ graphD L ρ z) : f = 0 := by
  have := resolvent_left_inverse L hρ hq h
  rw [map_zero] at this
  exact this.symm

end Circle

#print axioms resolvent_range
#print axioms resolvent_left_inverse
#print axioms resolvent_unique

end QuantumNLS.HaarResolvent
