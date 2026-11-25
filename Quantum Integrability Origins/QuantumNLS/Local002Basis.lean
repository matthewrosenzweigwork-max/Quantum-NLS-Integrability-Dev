import Mathlib
import QuantumNLS.LocalSpectralOperator

/-! LOCAL-002 prerequisite (spectral_reduction.tex:30-32): for each parity `σ`, the free eigenfunctions
`χ_{m,j}` (`m` of parity `σ`, `j ∈ {1,2}`) form an orthonormal basis of `H_σ = L²(0,L;ℂ²)`.

PROVED, not assumed: orthonormality by explicit exponential integrals (`inner_chi_general`) and
completeness by Mathlib's Parseval identity on an interval (`hasSum_sq_fourierCoeffOn`)
applied to `exp(∓ i π n₀ x/L) f_j`, whose Fourier coefficients are the pairings with `χ_{n₀+2k,j}`.
`chi_complete`: a vector orthogonal to every `χ_{m,j}` of the parity of `n₀` is zero. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Basis
open QuantumNLS.LocalSpectral

variable {L : ℝ}

lemma sgn_sq (j : Fin 2) : sgn j * sgn j = 1 := by
  unfold sgn; split_ifs <;> norm_num

lemma sgn_ne (j : Fin 2) : sgn j ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

lemma conj_exp_rate (m : ℤ) (j : Fin 2) (x : ℝ) :
    conj (Complex.exp (rate L m j * (x : ℂ))) = Complex.exp (-(rate L m j * (x : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [rate, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma inner_chiFun_same (hL : 0 < L) (a b : ℤ) (i : Fin 2) (x : ℝ) :
    ⟪chiFun L a i x, chiFun L b i x⟫_ℂ =
      ((L⁻¹ : ℝ) : ℂ) * Complex.exp ((rate L b i - rate L a i) * (x : ℂ)) := by
  unfold chiFun
  rw [inner_smul_left, inner_smul_right]
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, if_true, map_one,
    one_mul, mul_one]
  rw [map_mul, Complex.conj_ofReal, conj_exp_rate]
  have h1 : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) = ((L⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hL.le]
  have h2 : Complex.exp (-(rate L a i * (x : ℂ))) * Complex.exp (rate L b i * (x : ℂ)) =
      Complex.exp ((rate L b i - rate L a i) * (x : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (-(rate L a i * (x : ℂ))) *
        ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L b i * (x : ℂ)))
      = ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
        (Complex.exp (-(rate L a i * (x : ℂ))) * Complex.exp (rate L b i * (x : ℂ))) := by ring
    _ = _ := by rw [h1, h2]

lemma parity_eq_iff_even {a b : ℤ} (h : parity a = parity b) : ∃ k : ℤ, b - a = 2 * k := by
  have : Even a ↔ Even b := by
    unfold parity at h
    by_cases ha : Even a <;> by_cases hb : Even b <;> simp [ha, hb] at h ⊢
  have h2 : Even (b - a) := by
    rw [Int.even_sub]; exact this.symm
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by omega⟩

lemma parity_add_two_mul (n k : ℤ) : parity (n + 2 * k) = parity n := by
  unfold parity
  have : Even (n + 2 * k) ↔ Even n := by
    rw [Int.even_add]; simp
  simp [this]

lemma sgn_int (j : Fin 2) : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ sgn j = e := by
  unfold sgn
  split_ifs
  · exact ⟨-1, Or.inr rfl, by norm_num⟩
  · exact ⟨1, Or.inl rfl, by norm_num⟩

theorem inner_chi_general (hL : 0 < L) {a b : ℤ} (hab : parity a = parity b) (i j : Fin 2) :
    ⟪chi L a i, chi L b j⟫_ℂ = if a = b ∧ i = j then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  by_cases hij : i = j
  · subst hij
    have hpt : ∀ᵐ x ∂μI L, ⟪(chi L a i : ℝ → E2) x, (chi L b i : ℝ → E2) x⟫_ℂ =
        ((L⁻¹ : ℝ) : ℂ) * Complex.exp ((rate L b i - rate L a i) * (x : ℂ)) := by
      filter_upwards [(memLp_chiFun L a i).coeFn_toLp, (memLp_chiFun L b i).coeFn_toLp] with x h1 h2
      have e1 : (chi L a i : ℝ → E2) x = chiFun L a i x := h1
      have e2 : (chi L b i : ℝ → E2) x = chiFun L b i x := h2
      rw [e1, e2, inner_chiFun_same hL]
    rw [integral_congr_ae hpt]
    simp only [μI]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hL.le]
    by_cases hb : a = b
    · subst hb
      simp only [sub_self, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, sub_zero,
        and_self, if_true]
      rw [Complex.real_smul]
      push_cast
      have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      field_simp
    · rw [if_neg (by tauto)]
      obtain ⟨k, hk⟩ := parity_eq_iff_even hab
      have hk0 : k ≠ 0 := by
        rintro rfl
        apply hb; omega
      obtain ⟨e, he1, he⟩ := sgn_int i
      have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hc' : rate L b i - rate L a i = (e : ℂ) * Complex.I * (2 * Real.pi * k / L) := by
        unfold rate pm
        have hb' : (b : ℂ) = a + 2 * k := by
          have : (b : ℂ) - a = 2 * k := by exact_mod_cast hk
          linear_combination this
        push_cast
        rw [he]
        push_cast
        rw [hb']
        ring
      have he0 : (e : ℂ) ≠ 0 := by rcases he1 with rfl | rfl <;> simp
      have hcne : rate L b i - rate L a i ≠ 0 := by
        rw [hc']
        have h2 : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
        have h4 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
        simp [he0, h2, hLc, h4, Complex.I_ne_zero]
      have hexp : Complex.exp ((rate L b i - rate L a i) * (L : ℂ)) = 1 := by
        rw [Complex.exp_eq_one_iff]
        refine ⟨e * k, ?_⟩
        rw [hc']
        push_cast
        field_simp
      rw [integral_exp_mul_complex hcne, hexp]
      simp
  · have hpt : ∀ᵐ x ∂μI L, ⟪(chi L a i : ℝ → E2) x, (chi L b j : ℝ → E2) x⟫_ℂ = 0 := by
      filter_upwards [(memLp_chiFun L a i).coeFn_toLp, (memLp_chiFun L b j).coeFn_toLp] with x h1 h2
      have e1 : (chi L a i : ℝ → E2) x = chiFun L a i x := h1
      have e2 : (chi L b j : ℝ → E2) x = chiFun L b j x := h2
      rw [e1, e2]
      unfold chiFun
      simp [inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left, hij]
    rw [integral_congr_ae hpt]
    simp [hij]

theorem chi_orthonormal (hL : 0 < L) (σ : ℤˣ) :
    Orthonormal ℂ (fun p : {p : ℤ × Fin 2 // parity p.1 = σ} => chi L p.1.1 p.1.2) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨a, i⟩, ha⟩ ⟨⟨b, j⟩, hb⟩
  have := inner_chi_general hL (a := a) (b := b) (ha.trans hb.symm) i j
  rw [this]
  simp [Subtype.ext_iff, Prod.ext_iff]

lemma comp_memLp (f : H2 L) (j : Fin 2) : MemLp (fun x => (f : ℝ → E2) x j) 2 (μI L) := by
  have := (EuclideanSpace.proj j : E2 →L[ℂ] ℂ).comp_memLp' (Lp.memLp f)
  exact this

lemma inner_chi_eq (m : ℤ) (j : Fin 2) (f : H2 L) :
    ⟪chi L m j, f⟫_ℂ = ∫ x in Ioc 0 L, (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
      Complex.exp (-(rate L m j * (x : ℂ))) * (f : ℝ → E2) x j := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_chiFun L m j).coeFn_toLp] with x h1
  have e1 : (chi L m j : ℝ → E2) x = chiFun L m j x := h1
  rw [e1]
  unfold chiFun
  rw [inner_smul_left]
  simp [EuclideanSpace.inner_single_left, Complex.conj_ofReal, map_mul, conj_exp_rate]

lemma comp_ae_zero (hL : 0 < L) (n0 : ℤ) (f : H2 L)
    (h : ∀ m : ℤ, ∀ j : Fin 2, parity m = parity n0 → ⟪chi L m j, f⟫_ℂ = 0) (j : Fin 2) :
    (fun x => (f : ℝ → E2) x j) =ᵐ[μI L] 0 := by
  set g : ℝ → ℂ := fun x => (f : ℝ → E2) x j with hg
  have hgm : MemLp g 2 (μI L) := comp_memLp f j
  obtain ⟨e, he1, he⟩ := sgn_int j
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  set hh : ℝ → ℂ := fun x => Complex.exp (-(rate L n0 j * (x : ℂ))) * g x with hhdef
  have hhm : MemLp hh 2 (μI L) := by
    refine MemLp.mono' hgm.norm ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(rate L n0 j * (x : ℂ)))).aestronglyMeasurable.mul hgm.aestronglyMeasurable
    · simp only [hhdef, norm_mul]
      have : ‖Complex.exp (-(rate L n0 j * (x : ℂ)))‖ = 1 := by
        have h2 : -(rate L n0 j * (x : ℂ)) = (((-(sgn j * pm L n0 / 2 * x) : ℝ)) : ℂ) * Complex.I := by
          unfold rate; push_cast; ring
        rw [h2]; exact Complex.norm_exp_ofReal_mul_I _
      rw [this, one_mul]
  have hcoef : ∀ N : ℤ, ∫ x in (0 : ℝ)..L, fourier (-N) (x : AddCircle (L - 0)) • hh x = 0 := by
    intro N
    have hm : parity (n0 + 2 * (e * N)) = parity n0 := parity_add_two_mul _ _
    have h1 := h (n0 + 2 * (e * N)) j hm
    rw [inner_chi_eq] at h1
    simp only [mul_assoc] at h1
    rw [integral_const_mul] at h1
    have hne : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
      exact_mod_cast (inv_pos.2 this).ne'
    rw [mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hne
    · rw [intervalIntegral.integral_of_le hL.le, ← h1]
      refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      simp only [hhdef, fourier_coe_apply, smul_eq_mul, hg, sub_zero]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      unfold rate pm
      push_cast
      rw [he]
      rcases he1 with rfl | rfl <;> push_cast <;> field_simp <;> ring
  have hab : (0 : ℝ) < L := hL
  have hps := hasSum_sq_fourierCoeffOn hab (f := hh)
    (hhm : MemLp hh 2 (volume.restrict (Ioc 0 L)))
  have h0 : ∀ i : ℤ, fourierCoeffOn hab hh i = 0 := fun i => by
    rw [fourierCoeffOn_eq_integral, hcoef]; simp
  simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hps
  have hz := hps.unique hasSum_zero
  have hint : ∫ x in (0 : ℝ)..L, ‖hh x‖ ^ 2 = 0 := by
    rw [sub_zero] at hz
    have hz' := hz
    simp only [smul_eq_mul, mul_eq_zero, inv_eq_zero] at hz'
    rcases hz' with h | h
    · exact absurd h hL.ne'
    · exact h
  rw [intervalIntegral.integral_of_le hL.le] at hint
  have hae : (fun x => ‖hh x‖ ^ 2) =ᵐ[μI L] 0 :=
    (integral_eq_zero_iff_of_nonneg (μ := μI L) (fun x => by positivity)
      hhm.norm.integrable_sq).1 hint
  filter_upwards [hae] with x hx
  have hx' : hh x = 0 := by simpa using hx
  have : g x = Complex.exp (rate L n0 j * (x : ℂ)) * hh x := by
    simp only [hhdef]
    rw [← mul_assoc, ← Complex.exp_add]; simp
  rw [Pi.zero_apply, this, hx', mul_zero]

theorem chi_complete (hL : 0 < L) (n0 : ℤ) (f : H2 L)
    (h : ∀ m : ℤ, ∀ j : Fin 2, parity m = parity n0 → ⟪chi L m j, f⟫_ℂ = 0) : f = 0 := by
  apply Lp.ext
  have h0 := comp_ae_zero hL n0 f h 0
  have h1 := comp_ae_zero hL n0 f h 1
  filter_upwards [h0, h1, Lp.coeFn_zero E2 2 (μI L)] with x a b c
  rw [c]
  ext i
  fin_cases i
  · exact a
  · exact b

end QuantumNLS.Local002Basis
#print axioms QuantumNLS.Local002Basis.chi_orthonormal
#print axioms QuantumNLS.Local002Basis.chi_complete
#print axioms QuantumNLS.Local002Basis.inner_chi_general
