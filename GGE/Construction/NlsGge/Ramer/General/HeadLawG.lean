import NlsGge.Ramer.General.RamerSettingMeasure
import NlsGge.Ramer.FiniteHeadLawBridge
import NlsGge.Ramer.ActualHeadLawBridge

/-!
# The finite head of the general Cameron–Martin space and its law (GA1)

Generalization of `NlsGge/Ramer/ActualHeadLawBridge.lean` to a `RamerSetting`
(`S.H = WeightedRealHilbert (2 S.q)`).  The mode-index helper lemmas `headSeq`,
`headSeq_modeIndex`, `headSeq_eq_zero`, `symmetricModes_eq_image`,
`modeIndex_mem_symmetricModes` are generic and are reused from the old file.

Namespace note: every declaration here is used with dot notation (`S.head`,
`S.headCoord`, ...), so it must live in `NlsGge.Ramer.General.RamerSetting`
(the namespace of the structure), not in `NlsGge.Ramer.Gen`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

theorem hnorm_sq (x : S.H) :
    ‖x‖ ^ 2 = ∑' n : ℤ, S.cmWeight n * ‖S.hcoord x n‖ ^ 2 :=
  weightedHilbert_norm_sq S.cmWeight x

/-- The finite head `P_N H`: vectors of `S.H` supported in the modes `-N..N`. -/
def head (N : ℕ) :
    @Submodule ℝ S.H _ _ (InnerProductSpace.toNormedSpace (𝕜 := ℝ)).toModule where
  carrier := {x | ∀ n ∉ symmetricModes N, S.hcoord x n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by
    intro x y hx hy n hn
    change S.hcoord (x + y) n = 0
    rw [S.hcoord_add, hx n hn, hy n hn, add_zero]
  smul_mem' := by
    intro r x hx n hn
    change S.hcoord (r • x) n = 0
    rw [S.hcoord_smul, hx n hn, mul_zero]

/-- The head embedding `FourierPlane N → H`. -/
def headVec (N : ℕ) (z : FourierPlane N) : S.H :=
  (⟨headSeq N z, by
    classical
    change Memℓp (weightedCoordinates S.cmWeight (headSeq N z)) 2
    refine memℓp_gen (summable_of_ne_finset_zero (s := symmetricModes N) ?_)
    intro n hn
    simp [weightedCoordinates, headSeq_eq_zero N z hn]⟩ : WeightedHilbert S.cmWeight)

theorem hcoord_headVec (N : ℕ) (z : FourierPlane N) (n : ℤ) :
    S.hcoord (S.headVec N z) n = headSeq N z n := rfl

/-- Head coordinates `P_N H ≃ FourierPlane N`, `v ↦ (v_{modeIndex i})_i`. -/
def headCoord (N : ℕ) : S.head N ≃ₗ[ℝ] FourierPlane N where
  toFun v := fun i => S.hcoord (v : S.H) (modeIndex N i)
  invFun z := ⟨S.headVec N z, fun n hn => headSeq_eq_zero N z hn⟩
  map_add' v w := by
    funext i
    exact S.hcoord_add (v : S.H) (w : S.H) _
  map_smul' r v := by
    funext i
    change S.hcoord (r • (v : S.H)) _ = _
    rw [S.hcoord_smul]
    simp [Complex.real_smul]
  left_inv v := by
    apply Subtype.ext
    apply S.hcoord_ext
    intro n
    change headSeq N (fun i => S.hcoord (v : S.H) (modeIndex N i)) n = _
    by_cases hn : n ∈ symmetricModes N
    · rw [symmetricModes_eq_image] at hn
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
      rw [headSeq_modeIndex]
    · rw [headSeq_eq_zero N _ hn, v.2 n hn]
  right_inv z := by
    funext i
    exact headSeq_modeIndex N z i

theorem headCoord_apply (N : ℕ) (v : S.head N) (i : Fin (2 * N + 1)) :
    S.headCoord N v i = S.hcoord (v : S.H) (modeIndex N i) := rfl

/-- The CM norm on the head: `‖v‖² = Σ_i 2 q_{modeIndex i} |v_{modeIndex i}|²`. -/
theorem head_norm_sq (N : ℕ) (v : S.head N) :
    ‖v‖ ^ 2 = ∑ i, 2 * S.q (modeIndex N i) * ‖S.headCoord N v i‖ ^ 2 := by
  change ‖(v : S.H)‖ ^ 2 = _
  rw [S.hnorm_sq, tsum_eq_sum (s := symmetricModes N)]
  · rw [symmetricModes_eq_image, Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
    rfl
  · intro n hn
    rw [v.2 n hn]; simp

instance head_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (S.head N) :=
  LinearEquiv.finiteDimensional (S.headCoord N).symm

/-- Borel σ-algebra on the finite head (same justification as in the old file: no diamond,
the ambient `S.H` has no `MeasurableSpace` instance). -/
instance head_measurableSpace (N : ℕ) : MeasurableSpace (S.head N) := borel _

instance head_borelSpace (N : ℕ) : BorelSpace (S.head N) := ⟨rfl⟩

/-- **Finite head-law bridge.** The standard Gaussian of `(P_N H, ⟨,⟩_H)` is carried by the
head coordinates onto the product of complex Gaussians of rates `S.q (modeIndex i)`. -/
theorem head_finiteStdGaussian_map (N : ℕ) :
    (finiteStdGaussian (S.head N)).map (S.headCoord N) =
      NlsGge.Measure.finiteComplexGaussian (fun i => S.q (modeIndex N i)) :=
  finiteStdGaussian_map_eq_finiteComplexGaussian
    (fun i => S.q (modeIndex N i)) (fun i => S.q_pos _)
    (S.headCoord N) (S.head_norm_sq N)

/-- The same law is the cylinder marginal of `S.γ`. -/
theorem head_finiteStdGaussian_map_eq_cylinder (N : ℕ) :
    (finiteStdGaussian (S.head N)).map (S.headCoord N) =
      S.γ.map (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) := by
  rw [S.head_finiteStdGaussian_map]
  exact (NlsGge.Measure.countableComplexGaussian_map_modes N S.q).symm

/-- **Finite Ramer formula for the cylinder marginal.** -/
theorem head_map_symm_eq_withDensity_ramer (N : ℕ)
    (T : FourierPlane N ≃ₜ FourierPlane N) (hT : Differentiable ℝ T) :
    (NlsGge.Measure.finiteComplexGaussian (fun i => S.q (modeIndex N i))).map T.symm =
      (NlsGge.Measure.finiteComplexGaussian (fun i => S.q (modeIndex N i))).withDensity
        (fun z =>
          ENNReal.ofReal (finiteRamerDensity
            (fun v => (S.headCoord N).symm (T (S.headCoord N v)))
            ((S.headCoord N).symm z))) :=
  finiteComplexGaussian_map_symm_eq_withDensity_ramer
    (fun i => S.q (modeIndex N i)) (fun i => S.q_pos _)
    (S.headCoord N) (S.head_norm_sq N) T hT

/-- The head is the range of the coordinate projection `P_N`. -/
theorem headProj_mem_head (N : ℕ) (x : S.H) : S.headProj N x ∈ S.head N := by
  intro n hn
  rw [S.hcoord_headProj, if_neg hn]

theorem headProj_eq_self_of_mem_head (N : ℕ) (v : S.head N) :
    S.headProj N (v : S.H) = (v : S.H) := by
  apply S.hcoord_ext
  intro n
  rw [S.hcoord_headProj]
  split_ifs with hn
  · rfl
  · exact (v.2 n hn).symm

end NlsGge.Ramer.General.RamerSetting
