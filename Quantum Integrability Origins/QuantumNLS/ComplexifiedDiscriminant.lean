import QuantumNLS.ComplexifiedVolterra
import QuantumNLS.DEF014DiscriminantAnalytic

/-!
# Complexified analytic infrastructure, stage X3: the discriminant, holomorphic in `(u, v, z)`

For R-3FEAD88B (`values:prop:riccati`, E5 gap (a)/(iii)). The physical DEF-013/DEF-014 discriminant
`L2SpatialTransfer.discriminant κ u z = tr M_L` is built from the balanced coefficient
`[[−iz/2, √κ ū], [√κ u, iz/2]]`. Its complexification replaces `ū` by an independent `v`:
`cxCoef κ u v z = [[−iz/2, √κ v], [√κ u, iz/2]]` (`balCoef_eq_cxCoef`: the physical coefficient is the case
`v = ū`), and `cxDisc κ u v z = tr` of the actual Volterra transfer of `cxCoef` over one period, for `u v : L²(𝕋_L)`,
`z : ℂ`.

Proved (unconditional; no GP contract, no owner-held contract):
* `cxFamily κ`: a DEF-014 coefficient family on `L²(𝕋_L) × L²(𝕋_L) × ℂ`, complex-homogeneous a.e.
  (`cxFamily_chom`);
* **`analyticOnNhd_cxDisc`**: `(u, v, z) ↦ cxDisc κ u v z` is complex analytic on all of
  `L²(𝕋_L) × L²(𝕋_L) × ℂ` (an entire function, jointly in the field, the independent "conjugate" field and the
  spectral parameter), via stage X2;
* `cxDisc_bound`: `|cxDisc κ u v z| ≤ C exp(B ‖(u,v,z)‖)` with `C, B ≥ 0` (uniform on bounded sets);
* **`cxDisc_star`**: on the real slice `v = ū` (`star u`, pointwise conjugation in `L²`),
  `cxDisc κ u (star u) z = L2SpatialTransfer.discriminant κ u z` for all `u`, `z`;
* **`cxDisc_local`** (the importable packaging): near any point `p₀` (in particular `(φ₀, φ̄₀, z₀)`) and for any
  radius `r > 0`, the extension is complex differentiable and complex analytic on `B(p₀, r)`, bounded there by one
  constant, and agrees with the real-slice discriminant.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology MeasureTheory ComplexConjugate Metric
open scoped Matrix Interval

namespace QuantumNLS.ComplexifiedDiscriminant

open SpatialTransfer L2SpatialTransfer DEF014VolterraOperator DEF014VolterraAnalytic ComplexifiedVolterra
open PhysicalTensor (L2T)
open RootDiscriminantBound (row_sum_le_norm norm_le_of_row_sums)

attribute [-instance] NormedSpace.complexToReal NormedAlgebra.complexToReal Module.complexToReal
  Algebra.complexToReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

/-- Complexified balanced coefficient: the conjugate entry `√κ ū` is replaced by an independent `√κ v`. -/
def cxCoef (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) (x : ℝ) : Mat2 :=
  !![-(Complex.I * z) / 2, (Real.sqrt κ : ℂ) * v x; (Real.sqrt κ : ℂ) * u x, Complex.I * z / 2]

/-- The physical balanced coefficient is the real slice `v = ū`. -/
theorem balCoef_eq_cxCoef (κ : ℝ) (u : ℝ → ℂ) (z : ℂ) :
    balCoef κ u z = cxCoef κ u (fun x => conj (u x)) z := rfl

theorem intervalIntegrable_cxCoef {L : ℝ} {u v : ℝ → ℂ} (hu : IntervalIntegrable u volume 0 L)
    (hv : IntervalIntegrable v volume 0 L) (κ : ℝ) (z : ℂ) :
    IntervalIntegrable (cxCoef κ u v z) volume 0 L := by
  let C : Mat2 := !![-(Complex.I * z) / 2, 0; 0, Complex.I * z / 2]
  let E : Mat2 := !![0, 1; 0, 0]
  let F : Mat2 := !![0, 0; 1, 0]
  have hh := ((intervalIntegrable_const (c := C)).add
    ((hv.const_mul (Real.sqrt κ : ℂ)).smul_continuousOn (g := fun _ => E) continuousOn_const)).add
      ((hu.const_mul (Real.sqrt κ : ℂ)).smul_continuousOn (g := fun _ => F) continuousOn_const)
  have he : cxCoef κ u v z = fun x =>
      C + ((Real.sqrt κ : ℂ) * v x) • E + ((Real.sqrt κ : ℂ) * u x) • F := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxCoef, C, E, F]
  rw [he]
  exact hh

theorem norm_cxCoef_le (κ : ℝ) (u v : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖cxCoef κ u v z x‖ ≤ ‖z‖ / 2 + Real.sqrt κ * (‖u x‖ + ‖v x‖) := by
  refine norm_le_of_row_sums _ (by positivity) fun i => ?_
  have h1 := mul_nonneg (Real.sqrt_nonneg κ) (norm_nonneg (u x))
  have h2 := mul_nonneg (Real.sqrt_nonneg κ) (norm_nonneg (v x))
  fin_cases i <;> simp [cxCoef, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg κ)] <;> nlinarith

theorem norm_entry_le (m : Mat2) (i j : Fin 2) : ‖m i j‖ ≤ ‖m‖ := by
  have hi := row_sum_le_norm m i
  have he : ‖m i j‖ ≤ ∑ k : Fin 2, ‖m i k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)
  exact he.trans (by simpa only [Fin.sum_univ_two] using hi)

variable {L : ℝ} [Fact (0 < L)]

theorem profile_smulC (c : ℂ) (u : L2T L) :
    (fun x : ℝ => profile (c • u) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => c * profile u x := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c u)
  simpa [L2SpatialTransfer.profile, Function.comp_def, zero_add] using h

theorem profile_star (u : L2T L) :
    (fun x : ℝ => profile (star u) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => conj (profile u x) := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star u)
  simpa [L2SpatialTransfer.profile, Function.comp_def, zero_add] using h

/-- The complexified coefficient family on `L²(𝕋_L) × L²(𝕋_L) × ℂ` (field, independent conjugate field, spectral
parameter). -/
def cxFamily (κ : ℝ) : Family (L2T L × L2T L × ℂ) Mat2 L where
  coef p := cxCoef κ (profile p.1) (profile p.2.1) p.2.2
  integrable p := intervalIntegrable_cxCoef (intervalIntegrable_profile p.1) (intervalIntegrable_profile p.2.1) κ p.2.2
  add_ae p q := by
    filter_upwards [DEF014DiscriminantAnalytic.profile_add p.1 q.1,
      DEF014DiscriminantAnalytic.profile_add p.2.1 q.2.1] with t h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxCoef, h1, h2] <;> ring
  smul_ae c p := by
    filter_upwards [DEF014DiscriminantAnalytic.profile_smul c p.1,
      DEF014DiscriminantAnalytic.profile_smul c p.2.1] with t h1 h2
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cxCoef, h1, h2, Complex.real_smul] <;> ring
  bound := L / 2 + 2 * (Real.sqrt κ * Real.sqrt L)
  bound_nonneg := by have hL : 0 < L := Fact.out; positivity
  norm_integral_le p := by
    have hL : 0 < L := Fact.out
    have hu := intervalIntegrable_profile p.1
    have hv := intervalIntegrable_profile p.2.1
    have hcoef := intervalIntegrable_cxCoef hu hv κ p.2.2
    calc
      _ ≤ ∫ t in (0 : ℝ)..L, ‖p.2.2‖ / 2 + Real.sqrt κ * (‖profile p.1 t‖ + ‖profile p.2.1 t‖) :=
        intervalIntegral.integral_mono_on hL.le hcoef.norm
          (intervalIntegrable_const.add ((hu.norm.add hv.norm).const_mul _))
          (fun t _ => norm_cxCoef_le κ _ _ _ t)
      _ = L * (‖p.2.2‖ / 2) + Real.sqrt κ * ((∫ t in (0 : ℝ)..L, ‖profile p.1 t‖) +
          ∫ t in (0 : ℝ)..L, ‖profile p.2.1 t‖) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const ((hu.norm.add hv.norm).const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add hu.norm hv.norm]
        simp [smul_eq_mul]
      _ ≤ L * (‖p.2.2‖ / 2) + Real.sqrt κ * (Real.sqrt L * ‖p.1‖ + Real.sqrt L * ‖p.2.1‖) := by
        gcongr
        · exact DiscParamContinuity.integral_profile_le p.1
        · exact DiscParamContinuity.integral_profile_le p.2.1
      _ ≤ (L / 2 + 2 * (Real.sqrt κ * Real.sqrt L)) * ‖p‖ := by
        have h1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
        have h2 : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
        have h3 : ‖p.2.2‖ ≤ ‖p‖ := (norm_snd_le p.2).trans (norm_snd_le p)
        have hk : 0 ≤ Real.sqrt κ * Real.sqrt L := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 hk, mul_le_mul_of_nonneg_left h2 hk,
          mul_le_mul_of_nonneg_left h3 hL.le]

/-- The complexified coefficient is complex-linear in `(u, v, z)` almost everywhere. -/
theorem cxFamily_chom (κ : ℝ) : CHomFamily (cxFamily (L := L) κ) := by
  intro c p
  filter_upwards [profile_smulC c p.1, profile_smulC c p.2.1] with t h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cxFamily, cxCoef, h1, h2] <;> ring

/-- **The complexified discriminant** `tr M_L(u, v, z)` with independent `u`, `v`. -/
def cxDisc (κ : ℝ) (u v : L2T L) (z : ℂ) : ℂ :=
  Matrix.trace (L1SpatialTransfer.transfer (cxCoef κ (profile u) (profile v) z) L)

/-- **Agreement on the real slice** `v = ū`: the complexified discriminant is the physical discriminant. -/
theorem cxDisc_star (κ : ℝ) (u : L2T L) (z : ℂ) : cxDisc κ u (star u) z = L2SpatialTransfer.discriminant κ u z := by
  have hL : 0 < L := Fact.out
  unfold cxDisc L2SpatialTransfer.discriminant L2SpatialTransfer.spatialTransfer
  congr 1
  apply L1SpatialTransfer.transfer_eq_of_ae hL.le _ ⟨hL.le, le_rfl⟩
  have he : volume.restrict (Icc (0 : ℝ) L) = volume.restrict (Ioc 0 L) := restrict_Ioc_eq_restrict_Icc.symm
  rw [he]
  filter_upwards [profile_star u] with t ht
  simp only [balCoef, coef, cxCoef, ht]

/-- Matrix entries as bounded complex-linear functionals. -/
def entryCLMc (i j : Fin 2) : Mat2 →L[ℂ] ℂ :=
  ({ toFun := fun m => m i j
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : Mat2 →ₗ[ℂ] ℂ).mkContinuous 1 (by
    intro m
    change ‖m i j‖ ≤ 1 * ‖m‖
    rw [one_mul]
    exact norm_entry_le m i j)

/-- **Complex analyticity of the complexified discriminant** jointly in `(u, v, z)`, everywhere. -/
theorem analyticOnNhd_cxDisc (κ : ℝ) :
    AnalyticOnNhd ℂ (fun p : L2T L × L2T L × ℂ => cxDisc κ p.1 p.2.1 p.2.2) univ := by
  intro p _
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hp := analyticAt_transferPathC hL (cxFamily κ) (cxFamily_chom κ) p
  have hm := ((ContinuousMap.evalCLM ℂ (⟨L, hL, le_rfl⟩ : Icc (0 : ℝ) L)).analyticAt _).comp hp
  have ht := (((entryCLMc 0 0).analyticAt _).comp hm).add (((entryCLMc 1 1).analyticAt _).comp hm)
  change AnalyticAt ℂ (fun q : L2T L × L2T L × ℂ =>
    L1SpatialTransfer.transfer (cxCoef κ (profile q.1) (profile q.2.1) q.2.2) L 0 0 +
    L1SpatialTransfer.transfer (cxCoef κ (profile q.1) (profile q.2.1) q.2.2) L 1 1) p at ht
  simpa only [cxDisc, Matrix.trace_fin_two] using ht

/-- Exponential bound, uniform on bounded sets. -/
theorem cxDisc_bound (κ : ℝ) : ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧
    ∀ p : L2T L × L2T L × ℂ, ‖cxDisc κ p.1 p.2.1 p.2.2‖ ≤ C * Real.exp (B * ‖p‖) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  refine ⟨2 * ‖(1 : Mat2)‖, (cxFamily (L := L) κ).bound, by positivity, (cxFamily (L := L) κ).bound_nonneg,
    fun p => ?_⟩
  have hMn : ‖transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩‖ ≤
      ‖(1 : Mat2)‖ * Real.exp ((cxFamily (L := L) κ).bound * ‖p‖) :=
    (ContinuousMap.norm_coe_le_norm _ _).trans (norm_transferPath_le hL (cxFamily κ) p)
  have hd : cxDisc κ p.1 p.2.1 p.2.2 = transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩ 0 0 +
      transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩ 1 1 :=
    Matrix.trace_fin_two _
  rw [hd]
  have e0 := norm_entry_le (transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩) 0 0
  have e1 := norm_entry_le (transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩) 1 1
  have := norm_add_le (transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩ 0 0)
    (transferPath hL (cxFamily κ) p ⟨L, hL, le_rfl⟩ 1 1)
  linarith

/-- **Importable packaging for R-3FEAD88B E5.** Near any point `p₀ = (u₀, v₀, z₀)` (in particular the real point
`(φ₀, φ̄₀, z₀) = (φ₀, star φ₀, z₀)`) and for any radius `r > 0`, the discriminant has the holomorphic extension
`cxDisc κ` in the complexified variables `(u, v, z)`: complex differentiable and complex analytic on `B(p₀, r)`,
bounded there by one constant, and equal to the physical discriminant on the real slice `v = ū`. -/
theorem cxDisc_local (κ : ℝ) (p₀ : L2T L × L2T L × ℂ) (r : ℝ) :
    ∃ M : ℝ,
      DifferentiableOn ℂ (fun p : L2T L × L2T L × ℂ => cxDisc κ p.1 p.2.1 p.2.2) (ball p₀ r) ∧
      AnalyticOnNhd ℂ (fun p : L2T L × L2T L × ℂ => cxDisc κ p.1 p.2.1 p.2.2) (ball p₀ r) ∧
      (∀ p ∈ ball p₀ r, ‖cxDisc κ p.1 p.2.1 p.2.2‖ ≤ M) ∧
      ∀ (u : L2T L) (z : ℂ), cxDisc κ u (star u) z = L2SpatialTransfer.discriminant κ u z := by
  obtain ⟨C, B, hC, hB, hbd⟩ := cxDisc_bound (L := L) κ
  refine ⟨C * Real.exp (B * (‖p₀‖ + r)), (analyticOnNhd_cxDisc κ).differentiableOn.mono (subset_univ _),
    (analyticOnNhd_cxDisc κ).mono (subset_univ _), fun p hp => ?_, cxDisc_star κ⟩
  have h1 : ‖p‖ ≤ ‖p₀‖ + r := by
    have := norm_sub_norm_le p p₀
    linarith [mem_ball_iff_norm.1 hp]
  exact (hbd p).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hB)) hC)

end QuantumNLS.ComplexifiedDiscriminant

#print axioms QuantumNLS.ComplexifiedDiscriminant.cxFamily_chom
#print axioms QuantumNLS.ComplexifiedDiscriminant.cxDisc_star
#print axioms QuantumNLS.ComplexifiedDiscriminant.analyticOnNhd_cxDisc
#print axioms QuantumNLS.ComplexifiedDiscriminant.cxDisc_bound
#print axioms QuantumNLS.ComplexifiedDiscriminant.cxDisc_local
