import NlsGge.Ramer.ActualHeadLawBridge
import NlsGge.Ramer.DivergenceProductRule
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.Sobolev.WeightedProjection

/-!
# Cylindrical Gaussian divergence on the actual source law

`γ = fullWeightSequenceGaussian c` is the actual countable product law on `ℤ → ℂ`, and
`H = ActualCM c` is its real Cameron–Martin space, with `‖h‖²_H = 2 Σ q_n |h_n|²`. For each
level `N`, `V_N = actualCMHead c N` is the finite head `P_N H` with the `H` inner product.

A *cylindrical field of level `N`* is given by `g : V_N → V_N`. It is the `H`-valued field
`z ↦ g(x_N(z))`, where `x_N(z) = L_N⁻¹((z_{modeIndex N i})_i)` is the head point of the
sample `z` (`headPt`). Its divergence is the finite Gaussian divergence on `V_N`,
`δ_cyl g (z) = δ_{V_N} g (x_N z)` (`cylDiv`).

Main results:
* `headPt_map`: the law of `x_N` under `γ` is the standard Gaussian of `(V_N, ⟨,⟩_H)`;
  this is the head-law bridge.
* `finiteGaussianDivergence_conj`: the divergence is invariant under isometric lifting.
* `cylDiv_lift`, `cylField_lift`: **level consistency.** A level-`N` field lifted to level
  `M ≥ N` (`u ↦ j(g(p u))`) is the same `H`-valued field and has the same divergence, so
  `δ_cyl` is well defined on cylindrical fields.
* `integral_mul_cylDiv`: Gaussian integration by parts on `γ`.
* `integral_sq_cylDiv_le`: the `L²` estimate on `γ` (Ramer, Lemma 4.1; v2
  `eq:divergenceestimate`) for compactly supported `C²` level-`N` fields. Here `hsNormSq` is the
  squared Hilbert–Schmidt norm of `Dg` on `V_N`, equivalently of `D_H` of the field on `H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace NlsGge.Ramer

/-! ### Divergence under isometric lifting -/

section Conj

variable {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- If `j : W → V` and `p : V → W` satisfy `p ∘ j = id` and `⟪v, j w⟫ = ⟪p v, w⟫`, so that
`j` is an isometric embedding with adjoint `p`, then
`δ_V(j ∘ G ∘ p)(v) = δ_W G (p v)`. -/
theorem finiteGaussianDivergence_conj (j : W →L[ℝ] V) (p : V →L[ℝ] W)
    (hpj : ∀ w, p (j w) = w) (hadj : ∀ v w, ⟪v, j w⟫ = ⟪p v, w⟫) (G : W → W) (v : V)
    (hG : DifferentiableAt ℝ G (p v)) :
    finiteGaussianDivergence (fun y => j (G (p y))) v = finiteGaussianDivergence G (p v) := by
  set D := fderiv ℝ G (p v)
  have hd : fderiv ℝ (fun y => j (G (p y))) v = j.comp (D.comp p) := by
    have h1 := hG.hasFDerivAt.comp v p.hasFDerivAt
    exact (j.hasFDerivAt.comp v h1).fderiv
  unfold finiteGaussianDivergence
  rw [hd, hadj]
  congr 1
  have := LinearMap.trace_comp_comm' (R := ℝ) (p : V →ₗ[ℝ] W) ((j.comp D : W →L[ℝ] V) : W →ₗ[ℝ] V)
  have e1 : ((j.comp (D.comp p) : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      ((j.comp D : W →L[ℝ] V) : W →ₗ[ℝ] V) ∘ₗ (p : V →ₗ[ℝ] W) := rfl
  have e2 : (p : V →ₗ[ℝ] W) ∘ₗ ((j.comp D : W →L[ℝ] V) : W →ₗ[ℝ] V) = (D : W →ₗ[ℝ] W) := by
    refine LinearMap.ext fun w => ?_
    exact hpj (D w)
  rw [e1, this, e2]

/-- A compactly supported `C¹` field has bounded value and derivative (growth exponent `0`). -/
theorem exists_growth_of_hasCompactSupport {g : W → W} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∃ C : ℝ, (∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) ∧
      (∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ (0 : ℕ)) := by
  obtain ⟨B0, hB0⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨B1, hB1⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hgc.fderiv (𝕜 := ℝ))
  refine ⟨max B0 B1, fun v => ?_, fun v => ?_⟩
  · rw [pow_zero, mul_one]; exact (hB0 v).trans (le_max_left _ _)
  · rw [pow_zero, mul_one]; exact (hB1 v).trans (le_max_right _ _)

end Conj

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### Head points and their law -/

/-- The head point `x_N(z) ∈ V_N` of a sample `z : ℤ → ℂ`. -/
def headPt (c : BoundedCoefficients lower upper) (N : ℕ) (z : ℤ → ℂ) : actualCMHead c N :=
  (actualCMHeadCoord c N).symm (fun i => z (modeIndex N i))

theorem cmCoord_headPt (c : BoundedCoefficients lower upper) (N : ℕ) (z : ℤ → ℂ) (n : ℤ) :
    cmCoord ((headPt c N z : actualCMHead c N) : ActualCM c) n =
      if n ∈ symmetricModes N then z n else 0 := by
  change headSeq N (fun i => z (modeIndex N i)) n = _
  split_ifs with hn
  · rw [symmetricModes_eq_image] at hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    rw [headSeq_modeIndex]
  · exact headSeq_eq_zero N _ hn

theorem measurable_headPt (c : BoundedCoefficients lower upper) (N : ℕ) :
    Measurable (headPt c N) := by
  have hL : Continuous ((actualCMHeadCoord c N).symm.toContinuousLinearEquiv :
      FourierPlane N → actualCMHead c N) :=
    (actualCMHeadCoord c N).symm.toContinuousLinearEquiv.continuous
  have hπ : Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  exact hL.measurable.comp hπ

/-- **Head-law bridge on samples.** Under the actual source law, the head point `x_N` is
standard Gaussian on `(V_N, ⟨,⟩_H)`. -/
theorem headPt_map (c : BoundedCoefficients lower upper) (N : ℕ) :
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map (headPt c N) =
      finiteStdGaussian (actualCMHead c N) := by
  set L := actualCMHeadCoord c N
  have hπ : Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    measurable_pi_iff.2 (fun i => measurable_pi_apply _)
  have hLs : Measurable (L.symm : FourierPlane N → actualCMHead c N) :=
    L.symm.toContinuousLinearEquiv.continuous.measurable
  have hL : Measurable (L : actualCMHead c N → FourierPlane N) :=
    L.toContinuousLinearEquiv.continuous.measurable
  have h1 : headPt c N = (L.symm : FourierPlane N → actualCMHead c N) ∘
      (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) := rfl
  rw [h1, ← Measure.map_map hLs hπ, NlsGge.Measure.fullWeightSequenceGaussian_map_modes,
    ← actualCMHead_finiteStdGaussian_map, Measure.map_map hLs hL]
  have : (L.symm : FourierPlane N → actualCMHead c N) ∘ L = id := by
    funext v; simp
  rw [this, Measure.map_id]

theorem integral_comp_headPt (c : BoundedCoefficients lower upper) (N : ℕ)
    (f : actualCMHead c N → ℝ) (hf : Continuous f) :
    ∫ z, f (headPt c N z) ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∫ v, f v ∂(finiteStdGaussian (actualCMHead c N)) := by
  rw [← headPt_map, integral_map (measurable_headPt c N).aemeasurable
    hf.aestronglyMeasurable]

/-! ### Cylindrical fields and their divergence -/

/-- The `H`-valued field of a level-`N` cylindrical field `g`. -/
def cylField (c : BoundedCoefficients lower upper) (N : ℕ)
    (g : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) : ActualCM c :=
  (g (headPt c N z) : ActualCM c)

/-- Divergence of a level-`N` cylindrical field: `δ_cyl g (z) = δ_{V_N} g (x_N z)`. -/
def cylDiv (c : BoundedCoefficients lower upper) (N : ℕ)
    (g : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) : ℝ :=
  finiteGaussianDivergence g (headPt c N z)

/-- Gaussian integration by parts on the actual law, for a level-`N` cylindrical test
function `ψ(x_N)` (`C¹`, compactly supported on `V_N`) and a `C¹` level-`N` field `g`:
`∫ ψ(x_N) δ_cyl g dγ = ∫ ⟨∇ψ(x_N), g(x_N)⟩_H dγ`. -/
theorem integral_mul_cylDiv (c : BoundedCoefficients lower upper) (N : ℕ)
    (ψ : actualCMHead c N → ℝ) (g : actualCMHead c N → actualCMHead c N)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) :
    ∫ z, ψ (headPt c N z) * cylDiv c N g z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      ∫ z, fderiv ℝ ψ (headPt c N z) (g (headPt c N z))
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hc1 : Continuous (fun v => ψ v * finiteGaussianDivergence g v) :=
    hψ.continuous.mul (continuous_finiteGaussianDivergence hg)
  have hc2 : Continuous (fun v => fderiv ℝ ψ v (g v)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply hg.continuous
  rw [show (fun z => ψ (headPt c N z) * cylDiv c N g z) =
      fun z => (fun v => ψ v * finiteGaussianDivergence g v) (headPt c N z) from rfl,
    integral_comp_headPt c N _ hc1,
    integral_comp_headPt c N (fun v => fderiv ℝ ψ v (g v)) hc2]
  exact integral_mul_finiteGaussianDivergence ψ g hψ hψc hg

/-- Integrability transfers along the head point. -/
theorem integrable_comp_headPt_iff (c : BoundedCoefficients lower upper) (N : ℕ)
    (f : actualCMHead c N → ℝ) (hf : Continuous f) :
    Integrable (fun z => f (headPt c N z)) (NlsGge.Measure.fullWeightSequenceGaussian c.val) ↔
      Integrable f (finiteStdGaussian (actualCMHead c N)) := by
  rw [← headPt_map]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_headPt c N).aemeasurable).symm

/-- **Cylindrical `L²` divergence estimate on the actual law** (Ramer, Lemma 4.1; v2
`eq:divergenceestimate`) for level-`N` fields that are `C²` with `g`, `Dg` of polynomial
growth: all three integrands are integrable and
`E_γ (δ_cyl g)² ≤ E_γ ‖g(x_N)‖²_H + E_γ ‖Dg(x_N)‖²_HS`. -/
theorem integral_sq_cylDiv_le_of_growth (c : BoundedCoefficients lower upper) (N : ℕ)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) (C : ℝ) (k : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ k) (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ k) :
    Integrable (fun z => (cylDiv c N g z) ^ 2) (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => ‖cylField c N g z‖ ^ 2)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => hsNormSq (fderiv ℝ g (headPt c N z)))
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    ∫ z, (cylDiv c N g z) ^ 2 ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      ∫ z, ‖cylField c N g z‖ ^ 2 ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫ z, hsNormSq (fderiv ℝ g (headPt c N z))
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have c1 : Continuous (fun v => (finiteGaussianDivergence g v) ^ 2) :=
    (continuous_finiteGaussianDivergence hg1).pow 2
  have c2 : Continuous (fun v => ‖g v‖ ^ 2) := hg1.continuous.norm.pow 2
  have c3 : Continuous (fun v => hsNormSq (fderiv ℝ g v)) := continuous_hsNormSq_fderiv hg
  obtain ⟨i1, i2, i3, hle⟩ := integral_sq_finiteGaussianDivergence_le_of_growth hg C k hgg hDg
  have hnorm : (fun z => ‖cylField c N g z‖ ^ 2) = fun z => (fun v => ‖g v‖ ^ 2) (headPt c N z) :=
    rfl
  refine ⟨(integrable_comp_headPt_iff c N _ c1).2 i1, ?_,
    (integrable_comp_headPt_iff c N _ c3).2 i3, ?_⟩
  · rw [hnorm]; exact (integrable_comp_headPt_iff c N _ c2).2 i2
  · have e1 := integral_comp_headPt c N _ c1
    have e2 := integral_comp_headPt c N _ c2
    have e3 := integral_comp_headPt c N _ c3
    simp only [cylDiv] at e1 ⊢
    rw [hnorm, e1, e2, e3]
    exact hle

/-- Compactly supported `C²` level-`N` fields: integrability and the `L²` estimate on `γ`. -/
theorem integral_sq_cylDiv_le (c : BoundedCoefficients lower upper) (N : ℕ)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Integrable (fun z => (cylDiv c N g z) ^ 2) (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => ‖cylField c N g z‖ ^ 2)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    Integrable (fun z => hsNormSq (fderiv ℝ g (headPt c N z)))
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    ∫ z, (cylDiv c N g z) ^ 2 ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) ≤
      ∫ z, ‖cylField c N g z‖ ^ 2 ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) +
        ∫ z, hsNormSq (fderiv ℝ g (headPt c N z))
          ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  obtain ⟨C, h1, h2⟩ := exists_growth_of_hasCompactSupport (hg.of_le (by norm_num)) hgc
  exact integral_sq_cylDiv_le_of_growth c N g hg C 0 h1 h2

/-! ### Level consistency -/

theorem symmetricModes_mono {N M : ℕ} (h : N ≤ M) : symmetricModes N ⊆ symmetricModes M := by
  intro n hn
  simp only [symmetricModes, Finset.mem_Icc] at hn ⊢
  omega

/-- Inclusion `V_N ↪ V_M` for `N ≤ M`. -/
def levelInclLin (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M) :
    actualCMHead c N →ₗ[ℝ] actualCMHead c M where
  toFun v := ⟨(v : ActualCM c), fun n hn => v.2 n (fun hN => hn (symmetricModes_mono h hN))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelIncl (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M) :
    actualCMHead c N →L[ℝ] actualCMHead c M :=
  LinearMap.toContinuousLinearMap (levelInclLin c h)

theorem coe_levelIncl (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (v : actualCMHead c N) : ((levelIncl c h v : actualCMHead c M) : ActualCM c) = v := rfl

/-- Coordinate truncation `V_M → V_N`. -/
def levelProjLin (c : BoundedCoefficients lower upper) (N M : ℕ) :
    actualCMHead c M →ₗ[ℝ] actualCMHead c N where
  toFun u := (actualCMHeadCoord c N).symm (fun i => cmCoord (u : ActualCM c) (modeIndex N i))
  map_add' u v := by
    rw [← map_add]; rfl
  map_smul' r u := by
    rw [RingHom.id_apply, ← map_smul]; congr 1

def levelProj (c : BoundedCoefficients lower upper) (N M : ℕ) :
    actualCMHead c M →L[ℝ] actualCMHead c N :=
  LinearMap.toContinuousLinearMap (levelProjLin c N M)

theorem cmCoord_levelProj (c : BoundedCoefficients lower upper) (N M : ℕ)
    (u : actualCMHead c M) (n : ℤ) :
    cmCoord ((levelProj c N M u : actualCMHead c N) : ActualCM c) n =
      if n ∈ symmetricModes N then cmCoord (u : ActualCM c) n else 0 := by
  change headSeq N (fun i => cmCoord (u : ActualCM c) (modeIndex N i)) n = _
  split_ifs with hn
  · rw [symmetricModes_eq_image] at hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
    rw [headSeq_modeIndex]
  · exact headSeq_eq_zero N _ hn

theorem levelProj_levelIncl (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (v : actualCMHead c N) : levelProj c N M (levelIncl c h v) = v := by
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  rw [cmCoord_levelProj, coe_levelIncl]
  split_ifs with hn
  · rfl
  · exact (v.2 n hn).symm

/-- The truncation is the actual coordinate projection `P_N`. -/
theorem coe_levelProj_eq_weightedProjection (c : BoundedCoefficients lower upper) (N M : ℕ)
    (u : actualCMHead c M) :
    ((levelProj c N M u : actualCMHead c N) : ActualCM c) =
      (show ActualCM c from
        weightedProjection (cmModeWeight c) (symmetricModes N) (u : ActualCM c)) := by
  apply cmCoord_ext
  intro n
  rw [cmCoord_levelProj]
  exact (weightedProjection_apply (cmModeWeight c) (symmetricModes N)
    (show WeightedHilbert (cmModeWeight c) from (u : ActualCM c)) n).symm

/-- `levelProj` is the adjoint of `levelIncl`. -/
theorem inner_levelIncl (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (u : actualCMHead c M) (v : actualCMHead c N) :
    ⟪u, levelIncl c h v⟫ = ⟪levelProj c N M u, v⟫ := by
  set P := weightedProjection (cmModeWeight c) (symmetricModes N)
  set x : WeightedHilbert (cmModeWeight c) := (u : ActualCM c)
  set y : WeightedHilbert (cmModeWeight c) := (v : ActualCM c)
  have hy : P y = y := weightedProjection_eq_self_of_mem_actualCMHead c N v
  have hres := weightedProjection_range_residual (cmModeWeight c) (symmetricModes N) x y
  have hpx : ((levelProj c N M u : actualCMHead c N) : ActualCM c) = (show ActualCM c from P x) :=
    coe_levelProj_eq_weightedProjection c N M u
  change ⟪(u : ActualCM c), (v : ActualCM c)⟫ =
    ⟪((levelProj c N M u : actualCMHead c N) : ActualCM c), (v : ActualCM c)⟫
  rw [hpx]
  change Complex.re (inner ℂ x y) = Complex.re (inner ℂ (P x) y)
  have hsplit : inner ℂ x y = inner ℂ (P x) y + inner ℂ (x - P x) y := by
    rw [← inner_add_left]; congr 1; abel
  have hzero : inner ℂ (x - P x) y = 0 := by
    rw [← hy, ← inner_conj_symm, hres, map_zero]
  rw [hsplit, hzero, add_zero]

theorem levelProj_headPt (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (z : ℤ → ℂ) : levelProj c N M (headPt c M z) = headPt c N z := by
  apply Subtype.ext
  apply cmCoord_ext
  intro n
  rw [cmCoord_levelProj, cmCoord_headPt, cmCoord_headPt]
  split_ifs with h1 h2 <;> first | rfl | exact absurd (symmetricModes_mono h h1) h2

/-- The lift of a level-`N` field to level `M ≥ N`. -/
def liftField (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) : actualCMHead c M → actualCMHead c M :=
  fun u => levelIncl c h (g (levelProj c N M u))

/-- **Level consistency of fields.** The lift is the same `H`-valued field. -/
theorem cylField_lift (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) (z : ℤ → ℂ) :
    cylField c M (liftField c h g) z = cylField c N g z := by
  simp only [cylField, liftField, coe_levelIncl, levelProj_headPt c h]

/-- **Level consistency of the divergence.** The lift has the same cylindrical divergence;
hence `δ_cyl` is well defined on cylindrical fields. -/
theorem cylDiv_lift (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) (hg : Differentiable ℝ g) (z : ℤ → ℂ) :
    cylDiv c M (liftField c h g) z = cylDiv c N g z := by
  unfold cylDiv liftField
  rw [finiteGaussianDivergence_conj (levelIncl c h) (levelProj c N M)
      (levelProj_levelIncl c h) (inner_levelIncl c h) g _ (hg _),
    levelProj_headPt c h]

end NlsGge.Ramer
