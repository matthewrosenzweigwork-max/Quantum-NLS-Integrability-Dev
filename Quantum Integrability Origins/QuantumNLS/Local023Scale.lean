import Mathlib
import QuantumNLS.Local023Phi

/-!
# LOCAL-023, stage S: transport to coupling `κ` by the printed scaling `u ↦ √κ u`

Source: `local_transform.tex:60-63` ("At coupling `κ` use the same construction after the scaling `u ↦ √κ u`, and hence the radius `d_L/√κ`") and
`local_transform.tex:9-14`.  With `s = √κ`, `Φ̂_κ(u) = s⁻¹ Φ_1(s u)` (`Local021R.PhiHat`) and `Ψ̂_κ(y) = s⁻¹ Ψ_1(s y)`; this module proves for a unit-coupling `Setting S`
(with `hc : Corr S`) and `√κ‖u‖ < r_M`:
`Φ̂_κ`, `Ψ̂_κ` analytic, mutually inverse, norm preserving; `|Φ̂_κ(u)_n|² = I_n^{(κ)}(u)` (exact mass scaling `RootMassScaling.masses_smul`);
`DΦ̂_κ(u) = DΦ_1(√κ u)` invertible with inverse differential `D(Ψ̂_κ)(Φ̂_κ u)`; the six covariances (index forms), `Φ̂_κ(c e_k) = 𝓕(c e_k)`, and `Φ̂_κ(C R u) = conj Φ̂_κ(u)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction

namespace QuantumNLS.Local023

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 modeLp)
open QuantumNLS.Local021 QuantumNLS.Local021R
open QuantumNLS.LocalSpectral (pm)
open QuantumNLS.RootIndexedMasses (masses)

variable {L : ℝ} [Fact (0 < L)] {r : ℝ}

theorem analyticAt_smul_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℝ) (x : E) :
    AnalyticAt ℝ (fun x : E => s • x) x := by
  have e : (fun x : E => s • x) = ⇑(s • ContinuousLinearMap.id ℝ E) := by ext x; simp
  rw [e]; exact ContinuousLinearMap.analyticAt _ x

theorem hasFDerivAt_sc {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : X → Y} {f' : X →L[ℝ] Y} {s : ℝ} (hs : 0 < s) {x : X}
    (h : HasFDerivAt f f' (s • x)) : HasFDerivAt (fun w : X => s⁻¹ • f (s • w)) f' x := by
  have hl : HasFDerivAt (fun w : X => s • w) (s • ContinuousLinearMap.id ℝ X) x :=
    (hasFDerivAt_id x).const_smul s
  have h' := (h.comp x hl).const_smul s⁻¹
  have e : s⁻¹ • (f'.comp (s • ContinuousLinearMap.id ℝ X)) = f' := by
    ext w
    simp [smul_smul, inv_mul_cancel₀ hs.ne']
  exact h'.congr_fderiv e

/-- `Ψ̂_κ(y) = κ^{-1/2} Ψ_1(√κ y)`: the genuine inverse of `Φ̂_κ`. -/
def PsiHat (S : Setting L 1 r one_pos) (κ : ℝ) (y : K) : L2T L :=
  (Real.sqrt κ)⁻¹ • Psi S (Real.sqrt κ • y)

section Hat

variable (S : Setting L 1 r one_pos)

theorem smul_norm_lt {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) : ‖Real.sqrt κ • u‖ < S.rM := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs]

theorem smul_norm_lt' {κ : ℝ} (hκ : 0 < κ) {y : K} (hy : Real.sqrt κ * ‖y‖ < S.rM) : ‖Real.sqrt κ • y‖ < S.rM := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hs]

theorem analyticAt_PhiHat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) : AnalyticAt ℝ (PhiHat S κ) u := by
  have hv := smul_norm_lt S hκ hu
  have h1 : AnalyticAt ℝ S.Phi (Real.sqrt κ • u) := analyticAt_Phi S hc hv
  have h2 : AnalyticAt ℝ (fun w : L2T L => Real.sqrt κ • w) u := analyticAt_smul_gen _ _
  exact AnalyticAt.const_smul (c := (Real.sqrt κ)⁻¹) (f := fun w : L2T L => S.Phi (Real.sqrt κ • w)) (h1.comp h2)

theorem analyticAt_PsiHat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {y : K} (hy : Real.sqrt κ * ‖y‖ < S.rM) : AnalyticAt ℝ (PsiHat S κ) y := by
  have hv := smul_norm_lt' S hκ hy
  have h1 : AnalyticAt ℝ (Psi S) (Real.sqrt κ • y) := analyticAt_Psi S hc hv
  have h2 : AnalyticAt ℝ (fun w : K => Real.sqrt κ • w) y := analyticAt_smul_gen _ _
  exact AnalyticAt.const_smul (c := (Real.sqrt κ)⁻¹) (f := fun w : K => Psi S (Real.sqrt κ • w)) (h1.comp h2)

theorem norm_PhiHat {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) : ‖PhiHat S κ u‖ = ‖u‖ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt S hκ hu
  have h1 : ‖(Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u)‖ = (Real.sqrt κ)⁻¹ * ‖S.Phi (Real.sqrt κ • u)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  show ‖(Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u)‖ = ‖u‖
  rw [h1, norm_Phi S hv, norm_smul, Real.norm_eq_abs, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem norm_PsiHat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {y : K} (hy : Real.sqrt κ * ‖y‖ < S.rM) : ‖PsiHat S κ y‖ = ‖y‖ := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt' S hκ hy
  have h1 : ‖(Real.sqrt κ)⁻¹ • Psi S (Real.sqrt κ • y)‖ = (Real.sqrt κ)⁻¹ * ‖Psi S (Real.sqrt κ • y)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  show ‖(Real.sqrt κ)⁻¹ • Psi S (Real.sqrt κ • y)‖ = ‖y‖
  rw [h1, norm_Psi S hc hv, norm_smul, Real.norm_eq_abs, abs_of_pos hs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

theorem PsiHat_PhiHat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) : PsiHat S κ (PhiHat S κ u) = u := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt S hκ hu
  show (Real.sqrt κ)⁻¹ • Psi S (Real.sqrt κ • ((Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u))) = u
  rw [smul_inv_smul₀ hs.ne', Psi_Phi S hc hv, inv_smul_smul₀ hs.ne']

theorem PhiHat_PsiHat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {y : K} (hy : Real.sqrt κ * ‖y‖ < S.rM) : PhiHat S κ (PsiHat S κ y) = y := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt' S hκ hy
  show (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • ((Real.sqrt κ)⁻¹ • Psi S (Real.sqrt κ • y))) = y
  rw [smul_inv_smul₀ hs.ne', Phi_Psi S hc hv, inv_smul_smul₀ hs.ne']

/-- `|Φ̂_κ(u)_n|² = I_n^{(κ)}(u)`. -/
theorem norm_PhiHat_apply (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) (n : ℤ) :
    ‖PhiHat S κ u n‖ ^ 2 = (masses hκ u).1 n := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt S hκ hu
  have hκ₂ : 0 < (1 : ℝ) * Real.sqrt κ ^ 2 := by positivity
  have hmass : (masses (one_pos : (0 : ℝ) < 1) (Real.sqrt κ • u)).1 n = Real.sqrt κ ^ 2 * (masses hκ u).1 n := by
    have h := QuantumNLS.Local020Fin2.masses_scale (L := L) (one_pos : (0 : ℝ) < 1) hs hκ₂ u n
    have key : ∀ κ₂ : ℝ, ∀ (hh : κ₂ = κ) (h0 : 0 < κ₂), (masses h0 u).1 n = (masses hκ u).1 n := by
      intro κ₂ hh h0
      subst hh
      rfl
    rw [show Real.sqrt κ • u = ((Real.sqrt κ : ℝ) : ℂ) • u from (Complex.coe_smul _ _).symm]
    rw [h, key (1 * Real.sqrt κ ^ 2) (by rw [one_mul, Real.sq_sqrt hκ.le]) hκ₂]
  rw [show PhiHat S κ u n = (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u) n from rfl, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hs), mul_pow, norm_Phi_apply S hc hv n, hmass, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hs.ne', one_pow, one_mul]

/-- the differential of `Φ̂_κ` is the unit-coupling differential at `√κ u`; it is a bounded invertible real-linear map whose inverse is the differential of `Ψ̂_κ` at `Φ̂_κ(u)`. -/
theorem exists_equiv_hat (hc : Corr S) {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : Real.sqrt κ * ‖u‖ < S.rM) :
    ∃ e : L2T L ≃L[ℝ] K, (e : L2T L →L[ℝ] K) = fderiv ℝ S.Phi (Real.sqrt κ • u) ∧
      HasFDerivAt (PhiHat S κ) (e : L2T L →L[ℝ] K) u ∧
      HasFDerivAt (PsiHat S κ) (e.symm : K →L[ℝ] L2T L) (PhiHat S κ u) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hv := smul_norm_lt S hκ hu
  obtain ⟨e, he1, he2⟩ := exists_equiv S hc hv
  refine ⟨e, he1, ?_, ?_⟩
  · rw [he1]; exact hasFDerivAt_PhiHat S hs hu
  · have hPv : ‖S.Phi (Real.sqrt κ • u)‖ < S.rM := by rw [norm_Phi S hv]; exact hv
    have hd : HasFDerivAt (Psi S) (fderiv ℝ (Psi S) (S.Phi (Real.sqrt κ • u))) (S.Phi (Real.sqrt κ • u)) :=
      ((analyticAt_Psi S hc hPv).differentiableAt).hasFDerivAt
    have hsm : Real.sqrt κ • PhiHat S κ u = S.Phi (Real.sqrt κ • u) := by
      show Real.sqrt κ • ((Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u)) = _
      exact smul_inv_smul₀ hs.ne' _
    have hd' : HasFDerivAt (Psi S) (fderiv ℝ (Psi S) (S.Phi (Real.sqrt κ • u))) (Real.sqrt κ • PhiHat S κ u) := by
      rw [hsm]; exact hd
    rw [he2]
    exact hasFDerivAt_sc hs hd'

end Hat

/-! ### Covariances of `Φ̂_κ` -/

theorem phys_smul_real (sk : SymKind) (a : ℝ) (u : L2T L) : sk.phys L (a • u) = a • sk.phys L u := by
  have e1 : ∀ w : L2T L, fourierL2 L (a • w) = a • fourierL2 L w := fun w => by
    have h1 : (a • w) = (a : ℂ) • w := (Complex.coe_smul a w).symm
    have h2 : a • fourierL2 L w = (a : ℂ) • fourierL2 L w := (Complex.coe_smul a _).symm
    rw [h1, h2, map_smul]
  apply (fourierL2 L).injective
  rw [SymKind.fourier_phys, e1, (sk.mono L).act_smul_real, e1, SymKind.fourier_phys]

theorem PhiHat_cov (S : Setting L 1 r one_pos) (sk : SymKind) {κ : ℝ} (hκ : 0 < κ) {u : L2T L}
    (hu : Real.sqrt κ * ‖u‖ < S.rM) :
    PhiHat S κ (sk.phys L u) = (sk.mono L).act (PhiHat S κ u) := by
  have hv : ‖Real.sqrt κ • u‖ < S.rM := smul_norm_lt S hκ hu
  show (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • sk.phys L u) = (sk.mono L).act ((Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • u))
  rw [← phys_smul_real, S.Phi_cov sk hv, ← (sk.mono L).act_smul_real]

theorem PhiHat_cov_index (S : Setting L 1 r one_pos) {κ : ℝ} (hκ : 0 < κ) {u : L2T L}
    (hu : Real.sqrt κ * ‖u‖ < S.rM) (n : ℤ) :
    (∀ y : ℝ, PhiHat S κ (QuantumNLS.BornTranslation.trans y u) n =
        Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * PhiHat S κ u n) ∧
    (∀ k : ℤ, PhiHat S κ (QuantumNLS.RootMassBoostSymbol.boost k u) n = PhiHat S κ u (n - k)) ∧
    PhiHat S κ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = PhiHat S κ u (-n) ∧
    PhiHat S κ (star u) n = conj (PhiHat S κ u (-n)) ∧
    (∀ φ : ℝ, PhiHat S κ (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
      Complex.exp ((φ : ℂ) * Complex.I) * PhiHat S κ u n) ∧
    PhiHat S κ (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = conj (PhiHat S κ u n) := by
  refine ⟨fun y => ?_, fun k => ?_, ?_, ?_, fun φ => ?_, ?_⟩
  · have := congrArg (fun w : K => w n) (PhiHat_cov S (SymKind.trans y) hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (PhiHat_cov S (SymKind.boost k) hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj, sub_eq_add_neg] using this
  · have := congrArg (fun w : K => w n) (PhiHat_cov S SymKind.refl hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (PhiHat_cov S SymKind.cj hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (PhiHat_cov S (SymKind.phase φ) hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this
  · have := congrArg (fun w : K => w n) (PhiHat_cov S SymKind.cjr hκ hu)
    simpa [SymKind.mono, SymKind.phys, Mono.cj] using this

theorem PhiHat_Cphys (S : Setting L 1 r one_pos) {κ : ℝ} (hκ : 0 < κ) {u : L2T L}
    (hu : Real.sqrt κ * ‖u‖ < S.rM) :
    PhiHat S κ (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) = star (PhiHat S κ u) := by
  refine lp.ext (funext fun n => ?_)
  have h := (PhiHat_cov_index S hκ hu n).2.2.2.2.2
  rw [lp.star_apply]
  exact h

theorem PhiHat_plane (S : Setting L 1 r one_pos) {κ : ℝ} (hκ : 0 < κ) (k : ℤ) (c : ℂ)
    (hc : Real.sqrt κ * ‖c‖ < S.rM) :
    PhiHat S κ (c • modeLp L k) = fourierL2 L (c • modeLp L k) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have e1 : Real.sqrt κ • (c • modeLp L k) = ((Real.sqrt κ : ℂ) * c) • modeLp L k := by
    rw [show Real.sqrt κ • (c • modeLp L k) = (Real.sqrt κ : ℂ) • (c • modeLp L k) from (Complex.coe_smul _ _).symm,
      smul_smul]
  have h2 := S.Phi_plane k ((Real.sqrt κ : ℂ) * c)
    (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hc)
  have h3 : ∀ X : K, (Real.sqrt κ)⁻¹ • ((Real.sqrt κ : ℝ) : ℂ) • X = X := by
    intro X
    refine lp.ext (funext fun n => ?_)
    simp only [lp.coeFn_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    have hne : (Real.sqrt κ : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast
    field_simp
  show (Real.sqrt κ)⁻¹ • S.Phi (Real.sqrt κ • (c • modeLp L k)) = _
  rw [e1, h2, mul_smul, map_smul]
  exact h3 _

end QuantumNLS.Local023

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local023.PsiHat_PhiHat
#print axioms QuantumNLS.Local023.PhiHat_PsiHat
#print axioms QuantumNLS.Local023.norm_PhiHat_apply
#print axioms QuantumNLS.Local023.exists_equiv_hat
#print axioms QuantumNLS.Local023.PhiHat_cov_index
#print axioms QuantumNLS.Local023.PhiHat_Cphys
#print axioms QuantumNLS.Local023.PhiHat_plane
