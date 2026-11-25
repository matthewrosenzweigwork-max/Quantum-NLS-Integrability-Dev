import NlsGge.Ramer.General.HeadLawG
import NlsGge.Ramer.CylindricalDivergence

/-!
# Cylindrical Gaussian divergence on the general source law (GA2)

Generalization of `NlsGge/Ramer/CylindricalDivergence.lean` to a `RamerSetting S`:
`γ = S.γ` on `ℤ → ℂ`, `H = S.H`, level-`N` head `V_N = S.head N`.

The `S`-independent lemmas `finiteGaussianDivergence_conj`, `exists_growth_of_hasCompactSupport`
and `symmetricModes_mono` are reused from the old file (they live in `NlsGge.Ramer`).

Namespace: every declaration lives in `NlsGge.Ramer.General.RamerSetting` (like GA1), and is used
with dot notation `S.headPt`, `S.cylDiv`, ... .
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Head points and their law -/

/-- The head point `x_N(z) ∈ V_N` of a sample `z : ℤ → ℂ`. -/
def headPt (N : ℕ) (z : ℤ → ℂ) : S.head N :=
  (S.headCoord N).symm (fun i => z (modeIndex N i))

theorem hcoord_headPt (N : ℕ) (z : ℤ → ℂ) (n : ℤ) :
    S.hcoord ((S.headPt N z : S.head N) : S.H) n =
      if n ∈ symmetricModes N then z n else 0 := by
  change headSeq N (fun i => z (modeIndex N i)) n = _
  split_ifs with hn
  · rw [symmetricModes_eq_image] at hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    rw [headSeq_modeIndex]
  · exact headSeq_eq_zero N _ hn

theorem measurable_headPt (N : ℕ) : Measurable (S.headPt N) := by
  have hL : Continuous ((S.headCoord N).symm.toContinuousLinearEquiv :
      FourierPlane N → S.head N) :=
    (S.headCoord N).symm.toContinuousLinearEquiv.continuous
  have hπ : Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  exact hL.measurable.comp hπ

/-- **Head-law bridge on samples.** Under `S.γ`, the head point `x_N` is standard Gaussian on
`(V_N, ⟨,⟩_H)`. -/
theorem headPt_map (N : ℕ) :
    S.γ.map (S.headPt N) = finiteStdGaussian (S.head N) := by
  set L := S.headCoord N
  have hπ : Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  have hLs : Measurable (L.symm : FourierPlane N → S.head N) :=
    L.symm.toContinuousLinearEquiv.continuous.measurable
  have hL : Measurable (L : S.head N → FourierPlane N) :=
    L.toContinuousLinearEquiv.continuous.measurable
  have h1 : S.headPt N = (L.symm : FourierPlane N → S.head N) ∘
      (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) := rfl
  rw [h1, ← Measure.map_map hLs hπ, ← S.head_finiteStdGaussian_map_eq_cylinder N,
    Measure.map_map hLs hL]
  have : (L.symm : FourierPlane N → S.head N) ∘ L = id := by
    funext v; simp
  rw [this, Measure.map_id]

theorem integral_comp_headPt (N : ℕ) (f : S.head N → ℝ) (hf : Continuous f) :
    ∫ z, f (S.headPt N z) ∂S.γ = ∫ v, f v ∂(finiteStdGaussian (S.head N)) := by
  rw [← S.headPt_map, integral_map (S.measurable_headPt N).aemeasurable
    hf.aestronglyMeasurable]

/-! ### Cylindrical fields and their divergence -/

/-- The `H`-valued field of a level-`N` cylindrical field `g`. -/
def cylField (N : ℕ) (g : S.head N → S.head N) (z : ℤ → ℂ) : S.H :=
  (g (S.headPt N z) : S.H)

/-- Divergence of a level-`N` cylindrical field: `δ_cyl g (z) = δ_{V_N} g (x_N z)`. -/
def cylDiv (N : ℕ) (g : S.head N → S.head N) (z : ℤ → ℂ) : ℝ :=
  finiteGaussianDivergence g (S.headPt N z)

/-- Gaussian integration by parts on `S.γ`. -/
theorem integral_mul_cylDiv (N : ℕ)
    (ψ : S.head N → ℝ) (g : S.head N → S.head N)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) :
    ∫ z, ψ (S.headPt N z) * S.cylDiv N g z ∂S.γ =
      ∫ z, fderiv ℝ ψ (S.headPt N z) (g (S.headPt N z)) ∂S.γ := by
  have hc1 : Continuous (fun v => ψ v * finiteGaussianDivergence g v) :=
    hψ.continuous.mul (continuous_finiteGaussianDivergence hg)
  have hc2 : Continuous (fun v => fderiv ℝ ψ v (g v)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply hg.continuous
  rw [show (fun z => ψ (S.headPt N z) * S.cylDiv N g z) =
      fun z => (fun v => ψ v * finiteGaussianDivergence g v) (S.headPt N z) from rfl,
    S.integral_comp_headPt N _ hc1,
    S.integral_comp_headPt N (fun v => fderiv ℝ ψ v (g v)) hc2]
  exact integral_mul_finiteGaussianDivergence ψ g hψ hψc hg

/-- Integrability transfers along the head point. -/
theorem integrable_comp_headPt_iff (N : ℕ) (f : S.head N → ℝ) (hf : Continuous f) :
    Integrable (fun z => f (S.headPt N z)) S.γ ↔
      Integrable f (finiteStdGaussian (S.head N)) := by
  rw [← S.headPt_map]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (S.measurable_headPt N).aemeasurable).symm

/-- **Cylindrical `L²` divergence estimate on `S.γ`** (Ramer, Lemma 4.1). -/
theorem integral_sq_cylDiv_le_of_growth (N : ℕ)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) (C : ℝ) (k : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ k) (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ k) :
    Integrable (fun z => (S.cylDiv N g z) ^ 2) S.γ ∧
    Integrable (fun z => ‖S.cylField N g z‖ ^ 2) S.γ ∧
    Integrable (fun z => hsNormSq (fderiv ℝ g (S.headPt N z))) S.γ ∧
    ∫ z, (S.cylDiv N g z) ^ 2 ∂S.γ ≤
      ∫ z, ‖S.cylField N g z‖ ^ 2 ∂S.γ +
        ∫ z, hsNormSq (fderiv ℝ g (S.headPt N z)) ∂S.γ := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have c1 : Continuous (fun v => (finiteGaussianDivergence g v) ^ 2) :=
    (continuous_finiteGaussianDivergence hg1).pow 2
  have c2 : Continuous (fun v => ‖g v‖ ^ 2) := hg1.continuous.norm.pow 2
  have c3 : Continuous (fun v => hsNormSq (fderiv ℝ g v)) := continuous_hsNormSq_fderiv hg
  obtain ⟨i1, i2, i3, hle⟩ := integral_sq_finiteGaussianDivergence_le_of_growth hg C k hgg hDg
  have hnorm : (fun z => ‖S.cylField N g z‖ ^ 2) =
      fun z => (fun v => ‖g v‖ ^ 2) (S.headPt N z) := rfl
  refine ⟨(S.integrable_comp_headPt_iff N _ c1).2 i1, ?_,
    (S.integrable_comp_headPt_iff N _ c3).2 i3, ?_⟩
  · rw [hnorm]; exact (S.integrable_comp_headPt_iff N _ c2).2 i2
  · have e1 := S.integral_comp_headPt N _ c1
    have e2 := S.integral_comp_headPt N _ c2
    have e3 := S.integral_comp_headPt N _ c3
    simp only [cylDiv] at e1 ⊢
    rw [hnorm, e1, e2, e3]
    exact hle

/-- Compactly supported `C²` level-`N` fields: integrability and the `L²` estimate on `S.γ`. -/
theorem integral_sq_cylDiv_le (N : ℕ)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable (fun z => (S.cylDiv N g z) ^ 2) S.γ ∧
    Integrable (fun z => ‖S.cylField N g z‖ ^ 2) S.γ ∧
    Integrable (fun z => hsNormSq (fderiv ℝ g (S.headPt N z))) S.γ ∧
    ∫ z, (S.cylDiv N g z) ^ 2 ∂S.γ ≤
      ∫ z, ‖S.cylField N g z‖ ^ 2 ∂S.γ +
        ∫ z, hsNormSq (fderiv ℝ g (S.headPt N z)) ∂S.γ := by
  obtain ⟨C, h1, h2⟩ := exists_growth_of_hasCompactSupport (hg.of_le (by norm_num)) hgc
  exact S.integral_sq_cylDiv_le_of_growth N g hg C 0 h1 h2

/-! ### Level consistency -/

/-- Inclusion `V_N ↪ V_M` for `N ≤ M`. -/
def levelInclLin {N M : ℕ} (h : N ≤ M) : S.head N →ₗ[ℝ] S.head M where
  toFun v := ⟨(v : S.H), fun n hn => v.2 n (fun hN => hn (symmetricModes_mono h hN))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelIncl {N M : ℕ} (h : N ≤ M) : S.head N →L[ℝ] S.head M :=
  LinearMap.toContinuousLinearMap (S.levelInclLin h)

theorem coe_levelIncl {N M : ℕ} (h : N ≤ M) (v : S.head N) :
    ((S.levelIncl h v : S.head M) : S.H) = v := rfl

/-- Coordinate truncation `V_M → V_N`. -/
def levelProjLin (N M : ℕ) : S.head M →ₗ[ℝ] S.head N where
  toFun u := (S.headCoord N).symm (fun i => S.hcoord (u : S.H) (modeIndex N i))
  map_add' u v := by
    rw [← map_add]; rfl
  map_smul' r u := by
    rw [RingHom.id_apply, ← map_smul]; congr 1

def levelProj (N M : ℕ) : S.head M →L[ℝ] S.head N :=
  LinearMap.toContinuousLinearMap (S.levelProjLin N M)

theorem hcoord_levelProj (N M : ℕ) (u : S.head M) (n : ℤ) :
    S.hcoord ((S.levelProj N M u : S.head N) : S.H) n =
      if n ∈ symmetricModes N then S.hcoord (u : S.H) n else 0 := by
  change headSeq N (fun i => S.hcoord (u : S.H) (modeIndex N i)) n = _
  split_ifs with hn
  · rw [symmetricModes_eq_image] at hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    rw [headSeq_modeIndex]
  · exact headSeq_eq_zero N _ hn

theorem levelProj_levelIncl {N M : ℕ} (h : N ≤ M) (v : S.head N) :
    S.levelProj N M (S.levelIncl h v) = v := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro n
  rw [hcoord_levelProj, coe_levelIncl]
  split_ifs with hn
  · rfl
  · exact (v.2 n hn).symm

/-- The truncation is the coordinate projection `P_N`. -/
theorem coe_levelProj_eq_headProj (N M : ℕ) (u : S.head M) :
    ((S.levelProj N M u : S.head N) : S.H) = S.headProj N (u : S.H) := by
  apply S.hcoord_ext
  intro n
  rw [hcoord_levelProj, S.hcoord_headProj]

/-- `levelProj` is the adjoint of `levelIncl`. -/
theorem inner_levelIncl {N M : ℕ} (h : N ≤ M) (u : S.head M) (v : S.head N) :
    ⟪u, S.levelIncl h v⟫ = ⟪S.levelProj N M u, v⟫ := by
  set P := weightedProjection S.cmWeight (symmetricModes N)
  set x : WeightedHilbert S.cmWeight := (u : S.H)
  set y : WeightedHilbert S.cmWeight := (v : S.H)
  have hPx : ∀ n, (P x) n = if n ∈ symmetricModes N then x n else 0 :=
    weightedProjection_apply _ _ _
  have hy : P y = y := S.headProj_eq_self_of_mem_head N v
  have hres := weightedProjection_range_residual S.cmWeight (symmetricModes N) x y
  have hpx : ((S.levelProj N M u : S.head N) : S.H) = (show S.H from P x) := by
    apply S.hcoord_ext
    intro n
    rw [hcoord_levelProj]
    exact (hPx n).symm
  change ⟪(u : S.H), (v : S.H)⟫ = ⟪((S.levelProj N M u : S.head N) : S.H), (v : S.H)⟫
  rw [hpx]
  change Complex.re (inner ℂ x y) = Complex.re (inner ℂ (P x) y)
  have hsplit : inner ℂ x y = inner ℂ (P x) y + inner ℂ (x - P x) y := by
    rw [← inner_add_left]; congr 1; abel
  have hzero : inner ℂ (x - P x) y = 0 := by
    rw [← hy, ← inner_conj_symm, hres, map_zero]
  rw [hsplit, hzero, add_zero]

theorem levelProj_headPt {N M : ℕ} (h : N ≤ M) (z : ℤ → ℂ) :
    S.levelProj N M (S.headPt M z) = S.headPt N z := by
  apply Subtype.ext
  apply S.hcoord_ext
  intro n
  rw [hcoord_levelProj, hcoord_headPt, hcoord_headPt]
  split_ifs with h1 h2 <;> first | rfl | exact absurd (symmetricModes_mono h h1) h2

/-- The lift of a level-`N` field to level `M ≥ N`. -/
def liftField {N M : ℕ} (h : N ≤ M) (g : S.head N → S.head N) : S.head M → S.head M :=
  fun u => S.levelIncl h (g (S.levelProj N M u))

/-- **Level consistency of fields.** The lift is the same `H`-valued field. -/
theorem cylField_lift {N M : ℕ} (h : N ≤ M) (g : S.head N → S.head N) (z : ℤ → ℂ) :
    S.cylField M (S.liftField h g) z = S.cylField N g z := by
  simp only [cylField, liftField, coe_levelIncl, S.levelProj_headPt h]

/-- **Level consistency of the divergence.** -/
theorem cylDiv_lift {N M : ℕ} (h : N ≤ M) (g : S.head N → S.head N)
    (hg : Differentiable ℝ g) (z : ℤ → ℂ) :
    S.cylDiv M (S.liftField h g) z = S.cylDiv N g z := by
  unfold cylDiv liftField
  rw [finiteGaussianDivergence_conj (S.levelIncl h) (S.levelProj N M)
      (S.levelProj_levelIncl h) (S.inner_levelIncl h) g _ (hg _),
    S.levelProj_headPt h]

end NlsGge.Ramer.General.RamerSetting
