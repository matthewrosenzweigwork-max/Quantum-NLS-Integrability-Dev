import Mathlib
import QuantumNLS.Fourier
import QuantumNLS.Local002Bridge
import QuantumNLS.Local002Analytic
import QuantumNLS.Local002Basis
import QuantumNLS.Local002Rank

/-! R-EC25334D (`thm:global-B01-actions`, collective_actions.tex:49-66), stage RB01-1:
the Fourier action of the potential on the free basis.

Source (collective_actions.tex:117-125, 152-170): in the basis `χ_{m,1}, χ_{m,2}` of parity `(-1)^n`
the two nonzero matrix entries of `V` are `⟨χ_{m,2}, V χ_{l,1}⟩ = 2i√(κ/L) q_{(m+l)/2}` and
`⟨χ_{m,1}, V χ_{l,2}⟩ = -2i√(κ/L) q^♯_{(m+l)/2}`; "each monomial of `V_a` reflects a Fourier index `m`
to `2k - m` and changes its spin"; the free resolvent is diagonal, `R_0 χ_l = (z - p_l)⁻¹ χ_l`.

Proved here, for the actual objects of DEF-049 (`chi`, `Vpt`, `IsResolvent`, `IsMulOp` of LOCAL-002), on the
physical real slice `q^♯ = q̄`:
* `emode L k`: the scalar Fourier mode `e_k(x) = L^{-1/2} e^{i p_k x}` of `L²(0,L)`, equal to the DEF-001 mode
  transported by the accepted isometry `toInterval` (`toInterval_modeLp`); every interval field is approximated
  by finite Fourier sums (`exists_trig_approx`).
* `Vpt_mode_chi0/1`: the pointwise reflection identities (spin flip, `l ↦ 2k - l`, coefficients
  `2i√κ c L^{-1/2}` and `-2i√κ c̄ L^{-1/2}`).
* `mulOp_mode_chi0/1`: `T χ_{l,j}` for `T = V_{c e_k} R_{0,n}(z)` (the Local002 operator `T = V R_0`).
* `exists_mulOp`: `T = V_u R_{0,n}(z)` exists for every interval field with `‖T‖ ≤ 2√κ C_{L,s} ‖u‖`
  (`s = |z - p_n|`), from the proved LOCAL-001 (`free_resolvent_hyp`).
* `mulOp_trig_chi`, `norm_mulOp_trig_chi`, `norm_mulOp_trig_sq_chi`: for a finite Fourier sum `a`,
  `T_a χ_{l,j} = Σ_k (...) χ_{2k-l, 1-j}`, `‖T_a χ_{l,j}‖ ≤ 2√κ L^{-1/2} A/|z - p_l|` and
  `‖T_a² χ_{l,j}‖ ≤ Σ_k (2√κ L^{-1/2})² |c_k| A /(|z-p_l| |z-p_{2k-l}|)`, `A = Σ_k |c_k|`.
No smallness, high-frequency estimate or resolvent of the perturbed operator is asserted here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01FourierAction
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Basis QuantumNLS.Local002Free
  QuantumNLS.Local002Bridge

variable {L κ : ℝ}

/-! ### The scalar Fourier modes on `(0, L]` -/

/-- `e_k(x) = L^{-1/2} e^{2πikx/L}`. -/
def emodeFun (L : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * k * x / L)

theorem continuous_emodeFun (L : ℝ) (k : ℤ) : Continuous (emodeFun L k) := by
  unfold emodeFun; fun_prop

theorem norm_emodeFun (L : ℝ) (k : ℤ) (x : ℝ) : ‖emodeFun L k x‖ = (Real.sqrt L)⁻¹ := by
  unfold emodeFun
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h : 2 * Real.pi * Complex.I * k * x / L = (((2 * Real.pi * k * x / L : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem memLp_emodeFun (L : ℝ) (k : ℤ) : MemLp (emodeFun L k) 2 (μI L) :=
  MemLp.of_bound (continuous_emodeFun L k).aestronglyMeasurable _
    (Filter.Eventually.of_forall fun x => (norm_emodeFun L k x).le)

/-- The scalar mode `e_k ∈ L²(0,L)`. -/
def emode (L : ℝ) (k : ℤ) : Lp ℂ 2 (μI L) := (memLp_emodeFun L k).toLp (emodeFun L k)

theorem coeFn_emode (L : ℝ) (k : ℤ) : (emode L k : ℝ → ℂ) =ᵐ[μI L] emodeFun L k :=
  (memLp_emodeFun L k).coeFn_toLp

/-- The DEF-001 mode `e_k` of `L²(𝕋_L)` is carried by the accepted isometry to `emode L k`. -/
theorem toInterval_modeLp [Fact (0 < L)] (k : ℤ) :
    toInterval L (QuantumNLS.Fourier.modeLp L k) = emode L k := by
  apply Lp.ext
  have mp : MeasurePreserving (fun x : ℝ => (x : AddCircle L)) (μI L)
      (volume : Measure (AddCircle L)) := by
    simpa only [zero_add, μI] using (AddCircle.measurePreserving_mk L (0 : ℝ))
  have h2 := mp.quasiMeasurePreserving.ae_eq_comp (QuantumNLS.Fourier.coeFn_modeLp L k)
  filter_upwards [toInterval_coe L (QuantumNLS.Fourier.modeLp L k), h2, coeFn_emode L k]
    with x a b c
  rw [a, c]
  change (QuantumNLS.Fourier.modeLp L k : AddCircle L → ℂ) (x : AddCircle L) = _
  have b' : (QuantumNLS.Fourier.modeLp L k : AddCircle L → ℂ) (x : AddCircle L) =
      QuantumNLS.Fourier.mode L k (x : AddCircle L) := b
  rw [b', QuantumNLS.Fourier.mode_coe]
  rfl

/-- Finite Fourier sums are dense in `L²(0,L)` (via DEF-001 Fourier synthesis and `toInterval`). -/
theorem exists_trig_approx [Fact (0 < L)] (u₀ : Lp ℂ 2 (μI L)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset ℤ) (c : ℤ → ℂ), ‖(∑ k ∈ S, c k • emode L k) - u₀‖ < ε := by
  set v₀ := (toInterval L).symm u₀ with hv₀
  have hs := QuantumNLS.Fourier.hasSum_coeff_smul_modeLp L v₀
  obtain ⟨S, hS⟩ := (hs.eventually (Metric.ball_mem_nhds v₀ hε)).exists
  refine ⟨S, fun k => QuantumNLS.Fourier.coeff L (v₀ : AddCircle L → ℂ) k, ?_⟩
  have hmap : toInterval L (∑ k ∈ S, QuantumNLS.Fourier.coeff L (v₀ : AddCircle L → ℂ) k •
      QuantumNLS.Fourier.modeLp L k) =
      ∑ k ∈ S, QuantumNLS.Fourier.coeff L (v₀ : AddCircle L → ℂ) k • emode L k := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, toInterval_modeLp]
  rw [← hmap, show u₀ = toInterval L v₀ by simp [hv₀], ← map_sub, norm_toInterval]
  simpa [Metric.mem_ball, dist_eq_norm] using hS

/-! ### Pointwise reflection identities -/

/-- The spin-`0` component of the free basis function. -/
theorem chiFun_zero_apply (L : ℝ) (m : ℤ) (x : ℝ) :
    (chiFun L m 0 x) 0 = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L m 0 * (x : ℂ)) ∧
      (chiFun L m 0 x) 1 = 0 := by
  unfold chiFun
  simp

theorem chiFun_one_apply (L : ℝ) (m : ℤ) (x : ℝ) :
    (chiFun L m 1 x) 1 = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (rate L m 1 * (x : ℂ)) ∧
      (chiFun L m 1 x) 0 = 0 := by
  unfold chiFun
  simp

/-- The coefficient of the reflection `χ_{l,j} ↦ χ_{2k-l,1-j}` produced by `V_{c e_k}`. -/
def coef (κ L : ℝ) (c : ℂ) (j : Fin 2) : ℂ :=
  if j = 0 then (2 * Complex.I) * (Real.sqrt κ : ℂ) * c * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)
  else -(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj c * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)

/-- The spin flip `j ↦ 1 - j`. -/
def flip (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

theorem coef_zero (κ L : ℝ) (c : ℂ) :
    coef κ L c 0 = (2 * Complex.I) * (Real.sqrt κ : ℂ) * c * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) := by
  simp [coef]

theorem coef_one (κ L : ℝ) (c : ℂ) :
    coef κ L c 1 = -(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj c * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) := by
  simp [coef]

theorem norm_coef (κ L : ℝ) (c : ℂ) (j : Fin 2) :
    ‖coef κ L c j‖ = 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖c‖ := by
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  fin_cases j
  · rw [Fin.zero_eta, coef_zero]
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, h2,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg L))]
    ring
  · rw [Fin.mk_one, coef_one]
    simp only [norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, h2,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg L)),
      RCLike.norm_conj]
    ring

lemma exp_reflect0 (L : ℝ) (k l : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * k * x / L) * Complex.exp (rate L l 0 * (x : ℂ)) =
      Complex.exp (rate L (2 * k - l) 1 * (x : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [rate, sgn, pm]
  push_cast
  simp
  ring

lemma exp_reflect1 (L : ℝ) (k l : ℤ) (x : ℝ) :
    conj (Complex.exp (2 * Real.pi * Complex.I * k * x / L)) * Complex.exp (rate L l 1 * (x : ℂ)) =
      Complex.exp (rate L (2 * k - l) 0 * (x : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [rate, sgn, pm, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_intCast]
  push_cast
  simp
  ring

theorem Vpt_mode_chi0 (κ L : ℝ) (c : ℂ) (k l : ℤ) (x : ℝ) :
    Vpt κ (c * emodeFun L k x) (chiFun L l 0 x) = coef κ L c 0 • chiFun L (2 * k - l) 1 x := by
  obtain ⟨h0, h1⟩ := chiFun_zero_apply L l x
  obtain ⟨g1, g0⟩ := chiFun_one_apply L (2 * k - l) x
  rw [QuantumNLS.Local002SA.Vpt_explicit]
  ext i
  fin_cases i
  · simp [h1, g0]
  · simp only [Fin.mk_one, vec2_one, PiLp.smul_apply, smul_eq_mul, h0, g1, coef_zero,
      emodeFun]
    rw [← exp_reflect0 L k l x]
    ring

theorem Vpt_mode_chi1 (κ L : ℝ) (c : ℂ) (k l : ℤ) (x : ℝ) :
    Vpt κ (c * emodeFun L k x) (chiFun L l 1 x) = coef κ L c 1 • chiFun L (2 * k - l) 0 x := by
  obtain ⟨h1, h0⟩ := chiFun_one_apply L l x
  obtain ⟨g0, g1⟩ := chiFun_zero_apply L (2 * k - l) x
  rw [QuantumNLS.Local002SA.Vpt_explicit]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, vec2_zero, PiLp.smul_apply, smul_eq_mul, h1, g0, coef_one,
      emodeFun, map_mul, Complex.conj_ofReal]
    rw [← exp_reflect1 L k l x]
    ring
  · simp [h0, g1]

theorem Vpt_mode_chi (κ L : ℝ) (c : ℂ) (k l : ℤ) (j : Fin 2) (x : ℝ) :
    Vpt κ (c * emodeFun L k x) (chiFun L l j x) = coef κ L c j • chiFun L (2 * k - l) (flip j) x := by
  fin_cases j
  · exact Vpt_mode_chi0 κ L c k l x
  · exact Vpt_mode_chi1 κ L c k l x

/-! ### The operator `T = V_u R_{0,n}(z)` on the free basis -/

/-- `T = V_u R_{0,n}(z)` exists for every interval field, with the LOCAL-001 bound. -/
theorem exists_mulOp {n : ℤ} {z : ℂ} {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.pi / L)
    (hz : ‖z - (pm L n : ℂ)‖ = s) {R0 : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (u : Lp ℂ 2 (μI L)) :
    ∃ T : H2 L →L[ℂ] H2 L, QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T ∧
      ‖T‖ ≤ 2 * Real.sqrt κ * Cconst L s * ‖u‖ := by
  have hK : 0 ≤ 2 * Real.sqrt κ * Cconst L s * ‖u‖ := by
    have := Cconst_nonneg L s; positivity
  obtain ⟨T, hTn, hTa⟩ := exists_T (κ := κ) R0 (u : ℝ → ℂ) hK (fun φ =>
    (QuantumNLS.Local002Discharge.free_resolvent_hyp L κ).pot s n z R0 hs hs2 hz hR0 u φ)
  exact ⟨T, hTa, hTn⟩

theorem mulOp_mode_chi (hL : 0 < L) {n l : ℤ} (j : Fin 2) {z : ℂ} {R0 T : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (hl : parity l = parity n)
    (hz : z ≠ (pm L l : ℂ)) (c : ℂ) (k : ℤ)
    (hT : QuantumNLS.Local002.IsMulOp κ R0 ((c • emode L k : Lp ℂ 2 (μI L)) : ℝ → ℂ) T) :
    T (chi L l j) = ((z - (pm L l : ℂ))⁻¹ * coef κ L c j) • chi L (2 * k - l) (flip j) := by
  have hR := res_chi (κ := κ) hL j hR0 hl hz
  apply Lp.ext
  filter_upwards [hT (chi L l j), Lp.coeFn_smul c (emode L k), coeFn_emode L k,
    Lp.coeFn_smul ((z - (pm L l : ℂ))⁻¹) (chi L l j), (memLp_chiFun L l j).coeFn_toLp,
    Lp.coeFn_smul ((z - (pm L l : ℂ))⁻¹ * coef κ L c j) (chi L (2 * k - l) (flip j)),
    (memLp_chiFun L (2 * k - l) (flip j)).coeFn_toLp] with x a1 a2 a3 a4 a5 a6 a7
  rw [a1, a6, hR, a2, a4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [a3]
  have e5 : (chi L l j : ℝ → E2) x = chiFun L l j x := a5
  have e7 : (chi L (2 * k - l) (flip j) : ℝ → E2) x = chiFun L (2 * k - l) (flip j) x := a7
  rw [e5, e7, Vpt_smul, Vpt_mode_chi, smul_smul]

/-- The parity of the reflected index. -/
theorem parity_reflect (k l : ℤ) : parity (2 * k - l) = parity l := by
  have : 2 * k - l = l + 2 * (k - l) := by ring
  rw [this, parity_add_two_mul]

/-- Additivity of `T` over a finite Fourier sum. -/
theorem mulOp_finset {R0 : H2 L →L[ℂ] H2 L} {ι : Type*} (S : Finset ι) (f : ι → Lp ℂ 2 (μI L))
    (Tf : ι → H2 L →L[ℂ] H2 L) (hTf : ∀ i, QuantumNLS.Local002.IsMulOp κ R0 (f i : ℝ → ℂ) (Tf i)) :
    QuantumNLS.Local002.IsMulOp κ R0 ((∑ i ∈ S, f i : Lp ℂ 2 (μI L)) : ℝ → ℂ) (∑ i ∈ S, Tf i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro φ
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (μI L), Lp.coeFn_zero E2 2 (μI L)] with x h1 h2
    change (((0 : H2 L →L[ℂ] H2 L) φ : H2 L) : ℝ → E2) x = _
    rw [ContinuousLinearMap.zero_apply, h2, h1]
    simp [Vpt_zero_pot]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hTf a).add ih

/-- `T_a χ_{l,j}` for a finite Fourier sum `a = Σ_{k∈S} c_k e_k`. -/
theorem mulOp_trig_chi (hL : 0 < L) {n l : ℤ} (j : Fin 2) {z : ℂ} {R0 T : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (hl : parity l = parity n)
    (hz : z ≠ (pm L l : ℂ)) (S : Finset ℤ) (c : ℤ → ℂ)
    (hT : QuantumNLS.Local002.IsMulOp κ R0 ((∑ k ∈ S, c k • emode L k : Lp ℂ 2 (μI L)) : ℝ → ℂ) T)
    (hex : ∀ u : Lp ℂ 2 (μI L), ∃ T', QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T') :
    T (chi L l j) = ∑ k ∈ S, ((z - (pm L l : ℂ))⁻¹ * coef κ L (c k) j) • chi L (2 * k - l) (flip j) := by
  choose Tf hTf using fun k : ℤ => hex (c k • emode L k)
  have hsum := mulOp_finset (κ := κ) S (fun k => c k • emode L k) Tf hTf
  have heq : T = ∑ k ∈ S, Tf k := hT.unique hsum
  rw [heq, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun k _ => mulOp_mode_chi hL j hR0 hl hz (c k) k (hTf k)

theorem norm_chi (hL : 0 < L) (m : ℤ) (j : Fin 2) : ‖chi L m j‖ = 1 :=
  (chi_orthonormal hL (parity m)).1 ⟨(m, j), rfl⟩

theorem norm_mulOp_trig_chi (hL : 0 < L) {n l : ℤ} (j : Fin 2) {z : ℂ} {R0 T : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (hl : parity l = parity n)
    (hz : z ≠ (pm L l : ℂ)) (S : Finset ℤ) (c : ℤ → ℂ)
    (hT : QuantumNLS.Local002.IsMulOp κ R0 ((∑ k ∈ S, c k • emode L k : Lp ℂ 2 (μI L)) : ℝ → ℂ) T)
    (hex : ∀ u : Lp ℂ 2 (μI L), ∃ T', QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T') :
    ‖T (chi L l j)‖ ≤ ∑ k ∈ S, 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖c k‖ / ‖z - (pm L l : ℂ)‖ := by
  rw [mulOp_trig_chi hL j hR0 hl hz S c hT hex]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, norm_chi hL, mul_one, norm_mul, norm_inv, norm_coef]
  rw [div_eq_inv_mul]

/-- The square of `T_a` on a basis vector (the double reflection). -/
theorem norm_mulOp_trig_sq_chi (hL : 0 < L) {n l : ℤ} (j : Fin 2) {z : ℂ} {R0 T : H2 L →L[ℂ] H2 L}
    (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0) (hl : parity l = parity n)
    (hz : ∀ m : ℤ, parity m = parity n → z ≠ (pm L m : ℂ)) (S : Finset ℤ) (c : ℤ → ℂ)
    (hT : QuantumNLS.Local002.IsMulOp κ R0 ((∑ k ∈ S, c k • emode L k : Lp ℂ 2 (μI L)) : ℝ → ℂ) T)
    (hex : ∀ u : Lp ℂ 2 (μI L), ∃ T', QuantumNLS.Local002.IsMulOp κ R0 (u : ℝ → ℂ) T') :
    ‖T (T (chi L l j))‖ ≤ ∑ k ∈ S, (2 * Real.sqrt κ * (Real.sqrt L)⁻¹) ^ 2 * ‖c k‖ *
      (∑ k' ∈ S, ‖c k'‖) / (‖z - (pm L l : ℂ)‖ * ‖z - (pm L (2 * k - l) : ℂ)‖) := by
  rw [mulOp_trig_chi hL j hR0 hl (hz l hl) S c hT hex, map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hl' : parity (2 * k - l) = parity n := (parity_reflect k l).trans hl
  rw [map_smul, norm_smul]
  have h2 := norm_mulOp_trig_chi hL (flip j) hR0 hl' (hz _ hl') S c hT hex
  set a : ℝ := 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ with ha
  set A : ℝ := ∑ k' ∈ S, ‖c k'‖ with hAdef
  set B : ℝ := ‖z - (pm L (2 * k - l) : ℂ)‖ with hBdef
  set D : ℝ := ‖z - (pm L l : ℂ)‖ with hDdef
  have h2' : ‖T (chi L (2 * k - l) (flip j))‖ ≤ a * A / B := by
    refine h2.trans (le_of_eq ?_)
    rw [hAdef, Finset.mul_sum, Finset.sum_div]
  rw [norm_mul, norm_inv, norm_coef]
  have hB : 0 < B := norm_pos_iff.2 (sub_ne_zero.2 (hz _ hl'))
  have hD : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 (hz l hl))
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  calc D⁻¹ * (a * ‖c k‖) * ‖T (chi L (2 * k - l) (flip j))‖
      ≤ D⁻¹ * (a * ‖c k‖) * (a * A / B) := by
        apply mul_le_mul_of_nonneg_left h2'
        positivity
    _ = a ^ 2 * ‖c k‖ * A / (D * B) := by
        field_simp

end QuantumNLS.RB01FourierAction
#print axioms QuantumNLS.RB01FourierAction.toInterval_modeLp
#print axioms QuantumNLS.RB01FourierAction.exists_trig_approx
#print axioms QuantumNLS.RB01FourierAction.Vpt_mode_chi
#print axioms QuantumNLS.RB01FourierAction.exists_mulOp
#print axioms QuantumNLS.RB01FourierAction.mulOp_trig_chi
#print axioms QuantumNLS.RB01FourierAction.norm_mulOp_trig_chi
#print axioms QuantumNLS.RB01FourierAction.norm_mulOp_trig_sq_chi
