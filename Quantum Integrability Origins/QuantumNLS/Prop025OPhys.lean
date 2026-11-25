import QuantumNLS.Prop025OBirk
import QuantumNLS.Prop022PositiveDataR126
import QuantumNLS.R52CFHartree
import QuantumNLS.RF535Final

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O4d:
**eq:MP-physical-P** for factorial kernels whose coherent energy is invariant under the full product
torus (source lines 446-538).

"Let `𝒫` be the full coordinatewise phase torus through `Z(u)` ... The global analytic inverse quantum-derived
chart has bounded derivatives of each fixed order on `𝓔` ... By the explicit interface, every scalar transfer is
invariant under all coordinatewise phase rotations.  Thus `F∘Z^{-1}` has that invariance ... The frequencies are
constant on each full phase torus.  Its flow has coordinates `e^{-iτω_j(z)}z_j` ... Conjugating by the bounded
physical differentials of `Z` and `Z^{-1}` on that torus gives the required physical bound
`sup_{|σ|,|τ|≤1} ‖S(τ,σ)‖ ≤ CW_a` ... The frozen Hamiltonian itself has a global unit-sphere flow ... The
preceding phase formula identifies the same flow by uniqueness."

Data: the accepted global chart statement `GlobalStatement` (R-F5355ABD; `Φ`, `Ψ = Φ⁻¹` real-analytic, strong
symplectic, `Φ(T_ψ v) = rotate ψ⁻¹ (Φ v)`), a unit profile `u`, a factorial rate `A`.  For EVERY family of
self-adjoint kernels `K_n` with `‖K_n‖ ≤ M A^{n+1}/√((2(n+1))!)` whose coherent energy `E = coh K` is invariant
under the product-torus action `T_ψ` (`hinv`), with `S(τ,σ) = DΦ^E_τ(Φ^E_σ u)` the derivative of the ambient
classical flow (`Prop022ClassicalFlowR126.classicalFlow`, the flow consumed by PROP-021):
`‖S(τ,σ)‖ ≤ C (1 + |τ| M)` with ONE `C` depending only on `u`, the chart and `A`.  With `M ≤ CW_a`
(stage O4b) this is eq:MP-physical-P.

Route (recorded for review).  The chart vector field `Y = dΦ(Ψ·)[V(Ψ·)]` (`V` the Hartree field) is the
Hamiltonian field of `E∘Ψ` (strong symplecticity), equivariant under all rotations and infinitesimally
phase-invariant; stage O4c then gives `Y_n = -iΩ_n z_n`, `|Ω_n| ≤ Lip(Y)` and the torus flow.  The frequency bound
uses one derivative of the vector field (a small rotation inside a Lipschitz ball) instead of the
division-free formula eq:MP-frequency; the physical bound is obtained in Lipschitz form and converted by
`norm_fderiv_le_of_lip'`.  `Lip(Y) ≤ c·M` because `‖V‖, Lip(V) ≤ c·M` on the ball of radius 2 (explicit
factorial sums, `vel_bounds`) and `Φ, dΦ, Ψ` have ONE Lipschitz constant on balls of one radius around the
compact torus (`unif_lip`).  No hypothesis is added; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped ComplexConjugate Topology NNReal ENNReal InnerProductSpace
open Filter Set Metric

namespace QuantumNLS.Prop025OPhys
open QuantumNLS.ActionTorus QuantumNLS.ResetNormalizationUniqueness QuantumNLS.Prop025OBirk
open QuantumNLS.SymplecticBracket
open PhysicalTensor BetheCoefficientTransform TensorCarrier
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115 Prop022ActualProfileR117
open Prop022ClassicalFlowR126 Prop022PositiveDataR126

/-! ### DEF-015 identities (generic) -/

section Gen
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

/-- `Ω(X_F, h) = dF[h]`, with the literal factor two of DEF-015. -/
theorem omega_hamField' (F : H → ℝ) (u h : H) : omega (hamField F u) h = fderiv ℝ F u h := by
  rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner ℂ]
  unfold hamField omega
  rw [inner_smul_left]
  simp

theorem omega_ext' (a b : H) (h : ∀ k, omega a k = omega b k) : a = b := by
  let d := a - b
  have hz : ∀ k, omega d k = 0 := by
    intro k
    dsimp [d]
    unfold omega
    rw [inner_sub_left, Complex.sub_im]
    have hk := h k
    unfold omega at hk
    linarith
  have hd := omega_mul_I d
  rw [hz] at hd
  have hn : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end Gen

/-! ### Rotations as real-linear isometries of `ℓ²(ℤ)` -/

/-- `rotate ψ` as a continuous real-linear map. -/
def rotL (ψ : ℤ → Circle) : S2 ℤ →L[ℝ] S2 ℤ :=
  LinearMap.mkContinuous
    { toFun := fun z => rotate ψ z
      map_add' := fun z w => lp.ext (funext fun n => by
        simp only [rotate_apply, lp.coeFn_add, Pi.add_apply]; ring)
      map_smul' := fun c z => lp.ext (funext fun n => by
        simp only [rotate_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul, Complex.real_smul]; ring) }
    1 (fun z => by
      have h := norm_rotate_sub ψ z 0
      have h0 : rotate ψ (0 : S2 ℤ) = 0 := lp.ext (funext fun n => by simp)
      simp only [h0, sub_zero] at h
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact h.le)

theorem rotL_apply (ψ : ℤ → Circle) (z : S2 ℤ) : rotL ψ z = rotate ψ z := rfl

theorem inner_rotate (ψ : ℤ → Circle) (a b : S2 ℤ) :
    ⟪rotate ψ a, rotate ψ b⟫_ℂ = ⟪a, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  rw [rotate_apply, rotate_apply, ← smul_eq_mul, ← smul_eq_mul (a := (ψ n : ℂ)), inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_comm (conj (ψ n : ℂ)), Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Circle.norm_coe]
  simp

theorem norm_rotate (ψ : ℤ → Circle) (z : S2 ℤ) : ‖rotate ψ z‖ = ‖z‖ := by
  have h := norm_rotate_sub ψ z 0
  have h0 : rotate ψ (0 : S2 ℤ) = 0 := lp.ext (funext fun n => by simp)
  rwa [h0, sub_zero, sub_zero] at h

/-! ### Explicit velocity bounds, linear in the factorial constant `M` -/

/-- `Σ_n weight 1 (4A) (n+1)`. -/
def cv (A : ℝ) : ℝ := ∑' n : ℕ, weight 1 (4 * A) (n + 1)

/-- `2 Σ_n weight 2 (4A) (n+1)`. -/
def cl (A : ℝ) : ℝ := 2 * ∑' n : ℕ, weight 2 (4 * A) (n + 1)

variable {L : ℝ} [Fact (0 < L)]

theorem cv_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ cv A :=
  tsum_nonneg fun n => by unfold weight; positivity

theorem cl_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ cl A := by
  unfold cl; exact mul_nonneg (by norm_num) (tsum_nonneg fun n => by unfold weight; positivity)

theorem vel_bounds (K : ∀ n, HN L (n + 1) →L[ℂ] HN L (n + 1)) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ)) :
    (∀ u : L2T L, ‖u‖ ≤ 2 → ‖velocity (positiveExtension K) u‖ ≤ M * cv A) ∧
    (∀ u v : L2T L, ‖u‖ ≤ 2 → ‖v‖ ≤ 2 →
      ‖velocity (positiveExtension K) u - velocity (positiveExtension K) v‖ ≤ M * cl A * ‖u - v‖) := by
  set E : ∀ n : ℕ, HilbertTensorPower ℂ (L2T L) (n + 1) →L[ℂ] HilbertTensorPower ℂ (L2T L) (n + 1) :=
    fun n => TensorPlacements.extendSymKernel (K n) with hEdef
  have hV : ∀ u, velocity (positiveExtension K) u = Ext025A8.hartreeField E u := fun u => rfl
  have hEn : ∀ n, ‖E n‖ ≤ M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ) :=
    fun n => (TensorPlacements.norm_extendSymKernel_le _).trans (hK n)
  have hw1 : Summable (fun n : ℕ => weight 1 (4 * A) (n + 1)) :=
    (summable_nat_add_iff 1).mpr (weight_summable 1 (4 * A) (by positivity))
  have hw2 : Summable (fun n : ℕ => weight 2 (4 * A) (n + 1)) :=
    (summable_nat_add_iff 1).mpr (weight_summable 2 (4 * A) (by positivity))
  have h4 : ∀ n : ℕ, (2 : ℝ) ^ (2 * n + 1) ≤ 4 ^ (n + 1) := by
    intro n
    have e1 : (2 : ℝ) ^ (2 * n + 1) = 2 * 4 ^ n := by
      rw [pow_succ, pow_mul]; norm_num; ring
    have e2 : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by rw [pow_succ]; ring
    rw [e1, e2]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n]
  have h4' : ∀ n : ℕ, (2 : ℝ) ^ (2 * n) ≤ 4 ^ (n + 1) := by
    intro n
    have e1 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [e1, pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n]
  have hb1 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖E n‖ * (2 : ℝ) ^ (2 * n + 1) ≤ M * weight 1 (4 * A) (n + 1) := by
    intro n
    calc ((n + 1 : ℕ) : ℝ) * ‖E n‖ * (2 : ℝ) ^ (2 * n + 1)
        ≤ ((n + 1 : ℕ) : ℝ) * (M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ)) * 4 ^ (n + 1) := by
          gcongr
          · exact hEn n
          · exact h4 n
      _ = M * weight 1 (4 * A) (n + 1) := by unfold weight; rw [mul_pow]; push_cast; ring
  have hb2 : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * ‖E n‖ * (2 : ℝ) ^ (2 * n) ≤
      M * (2 * weight 2 (4 * A) (n + 1)) := by
    intro n
    have hc : ((n + 1 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast; nlinarith
    calc ((n + 1 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) * ‖E n‖ * (2 : ℝ) ^ (2 * n)
        ≤ (2 * ((n + 1 : ℕ) : ℝ) ^ 2) * (M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ)) *
            4 ^ (n + 1) := by
          gcongr
          · exact hEn n
          · exact h4' n
      _ = M * (2 * weight 2 (4 * A) (n + 1)) := by unfold weight; rw [mul_pow]; push_cast; ring
  have hsum1 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖E n‖ * (2 : ℝ) ^ (2 * n + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hb1 (hw1.mul_left M)
  refine ⟨fun u hu => ?_, fun u v hu hv => ?_⟩
  · rw [hV]
    have hb : ∀ n, ‖Ext025A8.hartreeTerm E n u‖ ≤ M * weight 1 (4 * A) (n + 1) := by
      intro n
      refine (Ext025A8.hartreeTerm_norm E n u).trans (le_trans ?_ (hb1 n))
      gcongr
    have h := tsum_of_norm_bounded ((hw1.mul_left M).hasSum) hb
    simpa only [Ext025A8.hartreeField, norm_smul, norm_neg, Complex.norm_I, one_mul, tsum_mul_left, cv]
      using h
  · rw [hV, hV]
    have hsu := Ext025A8.hartree_series_summable E (by norm_num : (0 : ℝ) ≤ 2) hsum1 hu
    have hsv := Ext025A8.hartree_series_summable E (by norm_num : (0 : ℝ) ≤ 2) hsum1 hv
    have hb : ∀ n, ‖Ext025A8.hartreeTerm E n u - Ext025A8.hartreeTerm E n v‖ ≤
        M * (2 * weight 2 (4 * A) (n + 1)) * ‖u - v‖ := by
      intro n
      refine (Ext025A8.hartreeTerm_lipschitz E n (by norm_num) hu hv).trans ?_
      exact mul_le_mul_of_nonneg_right (hb2 n) (norm_nonneg _)
    have h := tsum_of_norm_bounded (((hw2.mul_left 2).mul_left M).mul_right ‖u - v‖).hasSum hb
    rw [tsum_mul_right, tsum_mul_left, tsum_mul_left] at h
    have he : Ext025A8.hartreeField E u - Ext025A8.hartreeField E v =
        (-Complex.I) • ∑' n, (Ext025A8.hartreeTerm E n u - Ext025A8.hartreeTerm E n v) := by
      rw [hsu.tsum_sub hsv]; simp only [Ext025A8.hartreeField, smul_sub]
    rw [he, norm_smul, norm_neg, Complex.norm_I, one_mul]
    calc _ ≤ M * (2 * ∑' n, weight 2 (4 * A) (n + 1)) * ‖u - v‖ := h
      _ = M * cl A * ‖u - v‖ := by unfold cl; ring

/-! ### The coherent energy has the Hartree field as its Hamiltonian field, everywhere -/

theorem coh_field (K : ∀ n, HN L (n + 1) →L[ℂ] HN L (n + 1)) {M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u : L2T L) :
    DifferentiableAt ℝ (R52CFHartree.coh K) u ∧
      hamField (R52CFHartree.coh K) u = velocity (positiveExtension K) u := by
  set S : ℝ := ‖u‖ + 1 with hSdef
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith [norm_nonneg u]
  have hw : Summable (fun n : ℕ => weight 1 (A * S ^ 2) (n + 1)) :=
    (summable_nat_add_iff 1).mpr (weight_summable 1 (A * S ^ 2) (by positivity))
  have hb : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) * ‖K n‖ * S ^ (2 * n + 1) ≤ M * weight 1 (A * S ^ 2) (n + 1) := by
    intro n
    have hp : S ^ (2 * n + 1) ≤ S ^ (2 * (n + 1)) := pow_le_pow_right₀ hS1 (by omega)
    calc ((n + 1 : ℕ) : ℝ) * ‖K n‖ * S ^ (2 * n + 1)
        ≤ ((n + 1 : ℕ) : ℝ) * (M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ)) *
            S ^ (2 * (n + 1)) := by
          gcongr
          exact hK n
      _ = M * weight 1 (A * S ^ 2) (n + 1) := by
          unfold weight; rw [mul_pow, ← pow_mul, mul_comm 2 (n + 1)]; push_cast; ring
  have hsum : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖K n‖ * S ^ (2 * n + 1)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hb (hw.mul_left M)
  have hsa : ∀ n, IsSelfAdjoint (K n) := fun n => by
    show star (K n) = K n
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hsK n
  have h := R52CFHartree.hamField_coh_eq K hsa (by linarith) hsum u (by rw [hSdef]; linarith)
  exact ⟨h.1.differentiableAt, h.2⟩

/-! ### eq:MP-physical-P -/

variable {κ : ℝ}

set_option maxHeartbeats 16000000 in
/-- **eq:MP-physical-P** (Lipschitz/torus form).  ONE constant `C` (depending only on the chart, the unit
profile `u` and the factorial rate `A`) bounds `‖DΦ^E_τ(Φ^E_σ u)‖ ≤ C(1 + |τ|M)` for EVERY factorial family
whose coherent energy is product-torus invariant. -/
theorem phys_P (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → S2 ℤ} {Ψl : S2 ℤ → L2T L}
    (hG : RF535Final.GlobalStatement L κ hκ d Φl Ψl) (u : L2T L) (hu : ‖u‖ = 1) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ∀ n, HN L (n + 1) →L[ℂ] HN L (n + 1)) (M : ℝ) (hM : 0 ≤ M)
      (hK : ∀ n, ‖K n‖ ≤ M * A ^ (n + 1) / Real.sqrt ((2 * (n + 1)).factorial : ℝ))
      (hsK : ∀ n, (K n).adjoint = K n),
      (∀ (ψ : ℤ → Circle) (v : L2T L),
        R52CFHartree.coh K (RF535Final.Tact (L := L) hκ ψ v) = R52CFHartree.coh K v) →
      ∀ τ σ : ℝ,
        ‖fderiv ℝ (classicalFlow (positiveExtension K) M A hA (positiveExtension_bound K M A hK)
            (positiveExtension_selfAdjoint K hsK) τ)
          (classicalFlow (positiveExtension K) M A hA (positiveExtension_bound K M A hK)
            (positiveExtension_selfAdjoint K hsK) σ u)‖ ≤ C * (1 + |τ| * M) := by
  obtain ⟨-, -, Φ, Ψ, -, -, -, -, -, -, -, hΦa, hΨa, hΨΦ, hΦΨ, -, hnorm, hsymp, hdiff, -, -, -, -, hrotψ,
    -, -, -⟩ := hG.2
  -- regularity of the chart
  have hΦc : ContDiff ℝ 2 Φ := contDiff_iff_contDiffAt.mpr fun x => (hΦa x).contDiffAt
  have hΦc1 : ContDiff ℝ 1 Φ := contDiff_iff_contDiffAt.mpr fun x => (hΦa x).contDiffAt
  have hΨc : ContDiff ℝ 1 Ψ := contDiff_iff_contDiffAt.mpr fun x => (hΨa x).contDiffAt
  have hdΦc : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦc.fderiv_right (le_of_eq one_add_one_eq_two)
  have hΨn : ∀ z, ‖Ψ z‖ = ‖z‖ := by
    intro z
    have h := hnorm (Ψ z)
    rw [hΦΨ] at h
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h).symm
  have hΦn : ∀ x, ‖Φ x‖ = ‖x‖ := fun x =>
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (hnorm x)
  -- the phase torus through `Φ u`
  set z0 := Φ u with hz0
  set P : Set (S2 ℤ) := range (fun ψ : ℤ → Circle => rotate ψ z0) with hPdef
  have hPc : IsCompact P := isCompact_range (continuous_rotate_left z0)
  have hProt : ∀ p ∈ P, ∀ ψ : ℤ → Circle, rotate ψ p ∈ P := by
    rintro p ⟨ψ', rfl⟩ ψ
    exact ⟨ψ * ψ', (rotate_mul ψ ψ' z0)⟩
  have hPn : ∀ p ∈ P, ‖p‖ = 1 := by
    rintro p ⟨ψ', rfl⟩
    rw [norm_rotate, hz0, hΦn, hu]
  have hz0P : z0 ∈ P := ⟨1, rotate_one z0⟩
  set Q : Set (L2T L) := Ψ '' P with hQdef
  have hQc : IsCompact Q := hPc.image hΨc.continuous
  -- one radius and one constant for `Ψ`, `Φ`, `dΦ`
  obtain ⟨CΨ, δΨ, hδΨ, hΨL⟩ := unif_lip hΨc hPc
  obtain ⟨CΦ, δΦ, hδΦ, hΦL⟩ := unif_lip hΦc1 hQc
  obtain ⟨CdΦ, δdΦ, hδdΦ, hdΦL⟩ := unif_lip hdΦc hQc
  set c1 : ℝ := (CdΦ : ℝ) * CΨ * cv A + CΦ * cl A * CΨ with hc1
  have hc10 : 0 ≤ c1 := by
    have := cv_nonneg A hA; have := cl_nonneg A hA; positivity
  refine ⟨CΨ * CΦ * (1 + 2 * c1), by positivity, ?_⟩
  intro K M hM hK hsK hinv τ σ
  set V := velocity (positiveExtension K) with hVdef
  obtain ⟨hVb, hVl⟩ := vel_bounds K hM hA hK
  have hcohf := coh_field K hM hA hK hsK
  -- the chart vector field
  set Y : S2 ℤ → S2 ℤ := fun z => fderiv ℝ Φ (Ψ z) (V (Ψ z)) with hYdef
  set G : S2 ℤ → ℝ := fun z => R52CFHartree.coh K (Ψ z) with hGdef
  have hGrot : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), G (rotate ψ z) = G z := by
    intro ψ z
    have hΨrot : Ψ (rotate ψ z) = RF535Final.Tact (L := L) hκ ψ⁻¹ (Ψ z) := by
      have h := hrotψ ψ⁻¹ (Ψ z)
      rw [inv_inv, hΦΨ] at h
      rw [← h, hΨΦ]
    simp only [hGdef]
    rw [hΨrot]
    exact hinv ψ⁻¹ (Ψ z)
  have hGd : ∀ z, HasFDerivAt G ((fderiv ℝ (R52CFHartree.coh K) (Ψ z)).comp (fderiv ℝ Ψ z)) z :=
    fun z => ((hcohf (Ψ z)).1.hasFDerivAt).comp z (hΨa z).differentiableAt.hasFDerivAt
  have hGk : ∀ z k, fderiv ℝ G z k = omega (Y z) k := by
    intro z k
    obtain ⟨e, he, hie⟩ := hdiff (Ψ z)
    rw [hΦΨ] at hie
    have h1 : omega (hamField (R52CFHartree.coh K) (Ψ z)) ((e.symm : S2 ℤ →L[ℝ] L2T L) k) =
        fderiv ℝ (R52CFHartree.coh K) (Ψ z) ((e.symm : S2 ℤ →L[ℝ] L2T L) k) := omega_hamField' _ _ _
    rw [(hGd z).fderiv, ContinuousLinearMap.comp_apply, hie.fderiv, ← h1, (hcohf (Ψ z)).2]
    have hp := hsymp (Ψ z) (V (Ψ z)) (e.symm k)
    rw [he.fderiv] at hp
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hp
    simp only [hYdef, he.fderiv, ContinuousLinearEquiv.coe_coe]
    unfold omega
    linarith
  -- equivariance of `Y`
  have hY : ∀ (ψ : ℤ → Circle) (z : S2 ℤ), Y (rotate ψ z) = rotate ψ (Y z) := by
    intro ψ z
    apply omega_ext'
    intro k
    have hcomp : HasFDerivAt (G ∘ rotL ψ) ((fderiv ℝ G (rotate ψ z)).comp (rotL ψ)) z :=
      (hGd (rotate ψ z)).differentiableAt.hasFDerivAt.comp z (rotL ψ).hasFDerivAt
    have hGG : G ∘ rotL ψ = G := funext fun w => hGrot ψ w
    rw [hGG] at hcomp
    have hk' : rotate ψ (rotate ψ⁻¹ k) = k := by rw [← rotate_mul, mul_inv_cancel, rotate_one]
    have h1 := congrArg (fun T : S2 ℤ →L[ℝ] ℝ => T (rotate ψ⁻¹ k)) hcomp.fderiv
    simp only [ContinuousLinearMap.comp_apply, rotL_apply, hk'] at h1
    rw [← hGk, ← h1, hGk]
    unfold omega
    conv_rhs => rw [← hk', inner_rotate]
  -- infinitesimal phase invariance
  have hre : ∀ (z : S2 ℤ) (n : ℤ), (conj (z n) * Y z n).re = 0 := by
    intro z n
    set s : S2 ℤ := lp.single 2 n (z n) with hsdef
    have hcurve : ∀ φ : ℝ, rotate (rotj n (Circle.exp φ)) z = z + (Complex.exp ((φ : ℂ) * Complex.I) - 1) • s := by
      intro φ
      refine lp.ext (funext fun m => ?_)
      rw [rotate_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, hsdef, lp.single_apply]
      unfold rotj
      rw [Pi.mulSingle_apply]
      by_cases hm : m = n
      · subst hm
        rw [if_pos rfl, Pi.single_eq_same, Circle.coe_exp, smul_eq_mul]; ring
      · rw [if_neg hm, Pi.single_eq_of_ne hm]; simp
    have hd1 : HasDerivAt (fun φ : ℝ => Complex.exp ((φ : ℂ) * Complex.I) - 1) Complex.I 0 := by
      have h1 : HasDerivAt (fun φ : ℝ => (φ : ℂ) * Complex.I) Complex.I 0 := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
      have h2 := (Complex.hasDerivAt_exp (((0 : ℝ) : ℂ) * Complex.I)).comp (0 : ℝ) h1
      simpa using h2.sub_const 1
    have hc : HasDerivAt (fun φ : ℝ => z + (Complex.exp ((φ : ℂ) * Complex.I) - 1) • s) (Complex.I • s) 0 :=
      (hd1.smul_const s).const_add z
    have hc0 : z + (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) - 1) • s = z := by simp
    have hGc : HasDerivAt (fun φ : ℝ => G (z + (Complex.exp ((φ : ℂ) * Complex.I) - 1) • s))
        (fderiv ℝ G z (Complex.I • s)) 0 := by
      have hG0 : HasFDerivAt G (fderiv ℝ G z) (z + (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) - 1) • s) := by
        rw [hc0]; exact (hGd z).differentiableAt.hasFDerivAt
      exact hG0.comp_hasDerivAt (0 : ℝ) hc
    have hconst : (fun φ : ℝ => G (z + (Complex.exp ((φ : ℂ) * Complex.I) - 1) • s)) = fun _ => G z := by
      funext φ; rw [← hcurve φ, hGrot]
    rw [hconst] at hGc
    have h0 := hGc.unique (hasDerivAt_const (0 : ℝ) (G z))
    rw [hGk] at h0
    unfold omega at h0
    rw [inner_smul_right, hsdef, lp.inner_single_right] at h0
    have h3 : (Complex.I * ⟪Y z n, z n⟫_ℂ).im = (conj (Y z n) * z n).re := by
      simp [Complex.mul_im, Complex.mul_re, inner]
      ring
    have h4 : (conj (z n) * Y z n).re = (conj (Y z n) * z n).re := by
      simp [Complex.mul_re]; ring
    rw [h4, ← h3]
    linarith
  -- the Lipschitz radius and constant of `Y`
  set δY : ℝ := min (min δΨ 1) (min δΦ δdΦ / ((CΨ : ℝ) + 1)) with hδYdef
  have hδY : 0 < δY := lt_min (lt_min hδΨ one_pos) (div_pos (lt_min hδΦ hδdΦ) (by positivity))
  have hδYΨ : δY ≤ δΨ := (min_le_left _ _).trans (min_le_left _ _)
  have hδY1 : δY ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδYm : δY ≤ min δΦ δdΦ / ((CΨ : ℝ) + 1) := min_le_right _ _
  set CY : ℝ≥0 := Real.toNNReal (M * c1) with hCYdef
  have hCY : (CY : ℝ) = M * c1 := by rw [hCYdef, Real.coe_toNNReal _ (by positivity)]
  -- points near the torus
  have hnear : ∀ p ∈ P, ∀ z ∈ ball p δY, ‖Ψ z‖ ≤ 2 ∧ Ψ z ∈ ball (Ψ p) δΦ ∧ Ψ z ∈ ball (Ψ p) δdΦ ∧
      ‖Ψ z - Ψ p‖ ≤ CΨ * ‖z - p‖ := by
    intro p hp z hz
    have hzΨ : z ∈ ball p δΨ := ball_subset_ball hδYΨ hz
    have hpΨ : p ∈ ball p δΨ := mem_ball_self hδΨ
    have hl := (hΨL p hp).1.dist_le_mul z hzΨ p hpΨ
    rw [dist_eq_norm, dist_eq_norm] at hl
    have hzp : ‖z - p‖ < δY := by rw [← dist_eq_norm]; exact hz
    have hlt : (CΨ : ℝ) * ‖z - p‖ < min δΦ δdΦ := by
      have h1 : (CΨ : ℝ) * ‖z - p‖ ≤ CΨ * δY := mul_le_mul_of_nonneg_left hzp.le CΨ.2
      have h2 : (CΨ : ℝ) * δY ≤ CΨ * (min δΦ δdΦ / ((CΨ : ℝ) + 1)) := mul_le_mul_of_nonneg_left hδYm CΨ.2
      have h3 : (CΨ : ℝ) * (min δΦ δdΦ / ((CΨ : ℝ) + 1)) < min δΦ δdΦ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [lt_min hδΦ hδdΦ]
      linarith
    refine ⟨?_, ?_, ?_, hl⟩
    · rw [hΨn]
      have := norm_sub_norm_le z p
      rw [hPn p hp] at this
      linarith
    · rw [mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hl (lt_of_lt_of_le hlt (min_le_left _ _))
    · rw [mem_ball, dist_eq_norm]; exact lt_of_le_of_lt hl (lt_of_lt_of_le hlt (min_le_right _ _))
  have hYL : ∀ p ∈ P, LipschitzOnWith CY Y (ball p δY) := by
    intro p hp
    apply LipschitzOnWith.of_dist_le_mul
    intro z1 hz1 z2 hz2
    obtain ⟨hn1, hΦ1, hd1, -⟩ := hnear p hp z1 hz1
    obtain ⟨hn2, hΦ2, hd2, -⟩ := hnear p hp z2 hz2
    have hΨp : Ψ p ∈ Q := ⟨p, hp, rfl⟩
    have hz1Ψ : z1 ∈ ball p δΨ := ball_subset_ball hδYΨ hz1
    have hz2Ψ : z2 ∈ ball p δΨ := ball_subset_ball hδYΨ hz2
    have hΨ12 := (hΨL p hp).1.dist_le_mul z1 hz1Ψ z2 hz2Ψ
    have hdΦ12 := (hdΦL (Ψ p) hΨp).1.dist_le_mul (Ψ z1) hd1 (Ψ z2) hd2
    have hΦb := (hΦL (Ψ p) hΨp).2 (Ψ z2) hΦ2
    rw [dist_eq_norm, dist_eq_norm] at hΨ12 hdΦ12 ⊢
    have hV1 := hVb (Ψ z1) hn1
    have hV12 := hVl (Ψ z1) (Ψ z2) hn1 hn2
    have he : Y z1 - Y z2 = (fderiv ℝ Φ (Ψ z1) - fderiv ℝ Φ (Ψ z2)) (V (Ψ z1)) +
        fderiv ℝ Φ (Ψ z2) (V (Ψ z1) - V (Ψ z2)) := by
      simp only [hYdef, sub_apply, map_sub]; abel
    rw [he]
    calc ‖(fderiv ℝ Φ (Ψ z1) - fderiv ℝ Φ (Ψ z2)) (V (Ψ z1)) + fderiv ℝ Φ (Ψ z2) (V (Ψ z1) - V (Ψ z2))‖
        ≤ ‖fderiv ℝ Φ (Ψ z1) - fderiv ℝ Φ (Ψ z2)‖ * ‖V (Ψ z1)‖ +
            ‖fderiv ℝ Φ (Ψ z2)‖ * ‖V (Ψ z1) - V (Ψ z2)‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
            (ContinuousLinearMap.le_opNorm _ _))
      _ ≤ ((CdΦ : ℝ) * (CΨ * ‖z1 - z2‖)) * (M * cv A) + (CΦ : ℝ) * (M * cl A * (CΨ * ‖z1 - z2‖)) := by
          gcongr
          · exact hdΦ12.trans (mul_le_mul_of_nonneg_left hΨ12 CdΦ.2)
          · exact hV12.trans (mul_le_mul_of_nonneg_left hΨ12 (by have := cl_nonneg A hA; positivity))
      _ = (CY : ℝ) * ‖z1 - z2‖ := by rw [hCY, hc1]; ring
  -- ODE uniqueness: the classical flow is the torus flow, near the torus
  set flow := classicalFlow (positiveExtension K) M A hA (positiveExtension_bound K M A hK)
    (positiveExtension_selfAdjoint K hsK) with hflowdef
  have hVlip : LipschitzOnWith (Real.toNNReal (M * cl A)) V (closedBall (0 : L2T L) 2) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx hy
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := cl_nonneg A hA; positivity)]
    exact hVl x y hx hy
  have hflow : ∀ p ∈ P, ∀ x : L2T L, Φ x ∈ ball p δY → ∀ τ' : ℝ,
      flow τ' x = Ψ (flowR (freq Y (Φ x)) τ' (Φ x)) := by
    intro p hp x hx τ'
    have hC : ∀ n, |freq Y (Φ x) n| ≤ (CY : ℝ) := fun n => freq_le hY hre (hYL p hp) hx n
    have hx2 : ‖x‖ ≤ 2 := by
      rw [← hΦn]
      have h1 := norm_sub_norm_le (Φ x) p
      rw [hPn p hp] at h1
      have h2 : ‖Φ x - p‖ < δY := by rw [← dist_eq_norm]; exact hx
      linarith
    have hγ : ∀ t, HasDerivAt (fun s => Ψ (flowR (freq Y (Φ x)) s (Φ x)))
        (V (Ψ (flowR (freq Y (Φ x)) t (Φ x)))) t ∧ Ψ (flowR (freq Y (Φ x)) t (Φ x)) ∈ closedBall (0 : L2T L) 2 := by
      intro t
      set w := flowR (freq Y (Φ x)) t (Φ x)
      obtain ⟨e, he, hie⟩ := hdiff (Ψ w)
      rw [hΦΨ] at hie
      have hd := hie.comp_hasDerivAt t (flowR_hasDerivAt hY hre hC t)
      refine ⟨?_, ?_⟩
      · have hv : (e.symm : S2 ℤ →L[ℝ] L2T L) (Y w) = V (Ψ w) := by
          simp only [hYdef, he.fderiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
        rw [hv] at hd
        exact hd
      · rw [mem_closedBall_zero_iff, hΨn, norm_flowR, hΦn]; exact hx2
    have hspec := classicalFlow_spec (positiveExtension K) M A hA (positiveExtension_bound K M A hK)
      (positiveExtension_selfAdjoint K hsK) x
    have hf : ∀ t, HasDerivAt (fun s => flow s x) (V (flow t x)) t ∧ flow t x ∈ closedBall (0 : L2T L) 2 := by
      intro t
      refine ⟨(hspec.2 t).1, ?_⟩
      rw [mem_closedBall_zero_iff, (hspec.2 t).2]; exact hx2
    have heq := ODE_solution_unique_univ (v := fun _ => V) (s := fun _ => closedBall (0 : L2T L) 2)
      (t₀ := 0) (fun _ => hVlip) hf hγ (by rw [hflowdef, hspec.1, flowR_zero, hΨΦ])
    exact congrFun heq τ'
  -- the base point stays on the torus
  have hu0 : Φ u ∈ ball z0 δY := by rw [← hz0]; exact mem_ball_self hδY
  set x0 := flow σ u with hx0def
  have hx0 : x0 = Ψ (flowR (freq Y z0) σ z0) := hflow z0 hz0P u hu0 σ
  set p0 := flowR (freq Y z0) σ z0 with hp0def
  have hp0P : p0 ∈ P := hProt z0 hz0P _
  have hΦx0 : Φ x0 = p0 := by rw [hx0, hΦΨ]
  have hx0Q : x0 ∈ Q := ⟨p0, hp0P, hx0.symm⟩
  -- the final Lipschitz estimate at `x0`
  set Lt : ℝ := 1 + 2 * |τ| * CY with hLt
  have hLt1 : 1 ≤ Lt := by
    rw [hLt]; have h0 : 0 ≤ 2 * |τ| * (CY : ℝ) := by have := CY.2; positivity
    linarith
  set ρ : ℝ := min δΦ (min (δY / ((CΦ : ℝ) + 1)) (δΨ / (Lt * ((CΦ : ℝ) + 1)))) with hρdef
  have hρ : 0 < ρ := lt_min hδΦ (lt_min (by positivity) (by positivity))
  have hlip : ∀ x ∈ ball x0 ρ, ‖flow τ x - flow τ x0‖ ≤ (CΨ * (Lt * CΦ)) * ‖x - x0‖ := by
    intro x hx
    have hxΦ : x ∈ ball x0 δΦ := ball_subset_ball (min_le_left _ _) hx
    have hxx0 : ‖x - x0‖ < ρ := by rw [← dist_eq_norm]; exact hx
    have hΦlip := (hΦL x0 hx0Q).1.dist_le_mul x hxΦ x0 (mem_ball_self hδΦ)
    rw [dist_eq_norm, dist_eq_norm, hΦx0] at hΦlip
    have hρ1 : ρ ≤ δY / ((CΦ : ℝ) + 1) := (min_le_right _ _).trans (min_le_left _ _)
    have hρ2 : ρ ≤ δΨ / (Lt * ((CΦ : ℝ) + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hCΦx : (CΦ : ℝ) * ‖x - x0‖ ≤ ((CΦ : ℝ) + 1) * ρ := by
      have : (CΦ : ℝ) * ‖x - x0‖ ≤ ((CΦ : ℝ) + 1) * ‖x - x0‖ := by nlinarith [norm_nonneg (x - x0)]
      nlinarith [norm_nonneg (x - x0)]
    have hΦxb : Φ x ∈ ball p0 δY := by
      rw [mem_ball, dist_eq_norm]
      have h1 : ((CΦ : ℝ) + 1) * ρ ≤ δY := by
        have := mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ (CΦ : ℝ) + 1)
        rwa [mul_div_cancel₀ _ (by positivity)] at this
      have h2 : (CΦ : ℝ) * ‖x - x0‖ < ((CΦ : ℝ) + 1) * ρ := by
        nlinarith [norm_nonneg (x - x0)]
      linarith
    have hfx := hflow p0 hp0P x hΦxb τ
    have hfx0 := hflow p0 hp0P x0 (by rw [hΦx0]; exact mem_ball_self hδY) τ
    rw [hfx, hfx0, hΦx0]
    have hR := flowR_lip hY hre (hYL p0 hp0P) (mem_ball_self hδY) hΦxb τ
    set R0 := flowR (freq Y p0) τ p0
    have hR0P : R0 ∈ P := hProt p0 hp0P _
    have hRx : ‖flowR (freq Y (Φ x)) τ (Φ x) - R0‖ ≤ Lt * (CΦ * ‖x - x0‖) := by
      rw [hLt]; exact hR.trans (mul_le_mul_of_nonneg_left hΦlip (by have := CY.2; positivity))
    have hRb : flowR (freq Y (Φ x)) τ (Φ x) ∈ ball R0 δΨ := by
      rw [mem_ball, dist_eq_norm]
      have h1 : Lt * ((CΦ : ℝ) * ‖x - x0‖) < δΨ := by
        have h2 : (CΦ : ℝ) * ‖x - x0‖ < ((CΦ : ℝ) + 1) * ρ := by nlinarith [norm_nonneg (x - x0)]
        have h3 : Lt * (((CΦ : ℝ) + 1) * ρ) ≤ δΨ := by
          have := mul_le_mul_of_nonneg_left hρ2 (by positivity : (0 : ℝ) ≤ Lt * ((CΦ : ℝ) + 1))
          rw [mul_div_cancel₀ _ (by positivity)] at this
          linarith [this]
        calc Lt * ((CΦ : ℝ) * ‖x - x0‖) < Lt * (((CΦ : ℝ) + 1) * ρ) :=
              mul_lt_mul_of_pos_left h2 (by linarith)
          _ ≤ δΨ := h3
      linarith
    have hΨl := (hΨL R0 hR0P).1.dist_le_mul _ hRb R0 (mem_ball_self hδΨ)
    rw [dist_eq_norm, dist_eq_norm] at hΨl
    calc ‖Ψ (flowR (freq Y (Φ x)) τ (Φ x)) - Ψ R0‖ ≤ CΨ * ‖flowR (freq Y (Φ x)) τ (Φ x) - R0‖ := hΨl
      _ ≤ CΨ * (Lt * (CΦ * ‖x - x0‖)) := mul_le_mul_of_nonneg_left hRx CΨ.2
      _ = (CΨ * (Lt * CΦ)) * ‖x - x0‖ := by ring
  have hfd := norm_fderiv_le_of_lip' (𝕜 := ℝ) (f := flow τ) (x₀ := x0)
    (by have := CY.2; positivity) (Filter.mem_of_superset (ball_mem_nhds x0 hρ) hlip)
  refine hfd.trans ?_
  rw [hLt, hCY]
  have hCΨ := CΨ.2
  have hCΦ := CΦ.2
  have hτ := abs_nonneg τ
  have : (CΨ : ℝ) * ((1 + 2 * |τ| * (M * c1)) * CΦ) = CΨ * CΦ * (1 + 2 * c1 * (|τ| * M)) := by ring
  rw [this]
  have hx : 1 + 2 * c1 * (|τ| * M) ≤ (1 + 2 * c1) * (1 + |τ| * M) := by
    nlinarith [mul_nonneg hτ hM, mul_nonneg hc10 (mul_nonneg hτ hM)]
  calc (CΨ : ℝ) * CΦ * (1 + 2 * c1 * (|τ| * M)) ≤ CΨ * CΦ * ((1 + 2 * c1) * (1 + |τ| * M)) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = CΨ * CΦ * (1 + 2 * c1) * (1 + |τ| * M) := by ring

end QuantumNLS.Prop025OPhys

#print axioms QuantumNLS.Prop025OPhys.vel_bounds
#print axioms QuantumNLS.Prop025OPhys.coh_field
#print axioms QuantumNLS.Prop025OPhys.phys_P

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OPhys." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OPhys aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
