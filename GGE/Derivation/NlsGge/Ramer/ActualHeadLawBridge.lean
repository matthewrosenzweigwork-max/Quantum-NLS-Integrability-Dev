import NlsGge.Ramer.FiniteHeadLawBridge
import NlsGge.Sobolev.CMWeightComparison
import NlsGge.Measure.CountableGaussian

/-!
# The finite head of the actual Cameron–Martin space and its law

`H = WeightedRealHilbert (cmModeWeight c)` is the actual real Cameron–Martin space,
`‖h‖²_H = Σ_n 2 q_n |h_n|²` with `q_n = sourceRate c n` (`weightedHilbert_norm_sq`,
`cmModeWeight = 2 · sourceRate`). Its finite head `P_N H` is realized as the real
subspace `actualCMHead c N` of vectors supported in the symmetric modes `-N..N`, with
the inner product inherited from `H`. It is exactly the range of the actual coordinate
projection `weightedProjection (cmModeWeight c) (symmetricModes N)`.

Main results:
* `actualCMHeadCoord c N : actualCMHead c N ≃ₗ[ℝ] FourierPlane N`, `v ↦ (v_{modeIndex i})_i`;
* `actualCMHead_norm_sq`: `‖v‖² = Σ_i 2 q_{modeIndex i} |v_{modeIndex i}|²`;
* `actualCMHead_finiteStdGaussian_map`: the standard Gaussian of `(P_N H, ⟨,⟩_H)` is carried
  onto the project's head law `fullWeightFourierGaussian N c` (real-component variance
  `1/(2 q_n)`), which is the actual cylinder marginal of `fullWeightSequenceGaussian c`;
* `actualHead_map_symm_eq_withDensity_ramer`: the finite Ramer formula for the actual
  cylinder marginal.

The `ℝ`-module structure on `H` is fixed explicitly to the one underlying the inner
product (`InnerProductSpace.toNormedSpace`), because the `RestrictScalars` module instance
coincides with it only up to default-transparency unfolding.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- The actual real Cameron–Martin space. -/
abbrev ActualCM (c : BoundedCoefficients lower upper) : Type :=
  WeightedRealHilbert (cmModeWeight c)

/-- Fourier coordinates of a vector of the actual CM space. -/
def cmCoord {c : BoundedCoefficients lower upper} (x : ActualCM c) (n : ℤ) : ℂ :=
  (show WeightedHilbert (cmModeWeight c) from x) n

theorem cmCoord_add {c : BoundedCoefficients lower upper} (x y : ActualCM c) (n : ℤ) :
    cmCoord (x + y) n = cmCoord x n + cmCoord y n := rfl

theorem cmCoord_smul {c : BoundedCoefficients lower upper} (r : ℝ) (x : ActualCM c)
    (n : ℤ) : cmCoord (r • x) n = (r : ℂ) * cmCoord x n := rfl

theorem cmCoord_ext {c : BoundedCoefficients lower upper} {x y : ActualCM c}
    (h : ∀ n, cmCoord x n = cmCoord y n) : x = y := by
  change (show WeightedHilbert (cmModeWeight c) from x) =
    (show WeightedHilbert (cmModeWeight c) from y)
  exact Subtype.ext (funext h)

theorem actualCM_norm_sq {c : BoundedCoefficients lower upper} (x : ActualCM c) :
    ‖x‖ ^ 2 = ∑' n : ℤ, cmModeWeight c n * ‖cmCoord x n‖ ^ 2 :=
  weightedHilbert_norm_sq (cmModeWeight c) x

/-- The finite head `P_N H`: actual CM vectors supported in the modes `-N..N`. -/
def actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ) :
    @Submodule ℝ (ActualCM c) _ _ (InnerProductSpace.toNormedSpace (𝕜 := ℝ)).toModule where
  carrier := {x | ∀ n ∉ symmetricModes N, cmCoord x n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by
    intro x y hx hy n hn
    change cmCoord (x + y) n = 0
    rw [cmCoord_add, hx n hn, hy n hn, add_zero]
  smul_mem' := by
    intro r x hx n hn
    change cmCoord (r • x) n = 0
    rw [cmCoord_smul, hx n hn, mul_zero]

theorem symmetricModes_eq_image (N : ℕ) :
    symmetricModes N = Finset.univ.image (modeIndex N) := by
  ext n
  simp only [symmetricModes, Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact modeIndex_covers N n h1 h2
  · rintro ⟨i, rfl⟩; exact modeIndex_bounds N i

theorem modeIndex_mem_symmetricModes (N : ℕ) (i : Fin (2 * N + 1)) :
    modeIndex N i ∈ symmetricModes N := by
  rw [symmetricModes_eq_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-- The sequence with prescribed head coordinates and zero tail. -/
def headSeq (N : ℕ) (z : FourierPlane N) (n : ℤ) : ℂ :=
  ∑ i, if modeIndex N i = n then z i else 0

theorem headSeq_modeIndex (N : ℕ) (z : FourierPlane N) (j : Fin (2 * N + 1)) :
    headSeq N z (modeIndex N j) = z j := by
  unfold headSeq
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h; exact hij (modeIndex_injective N h)
  · intro h; exact absurd (Finset.mem_univ j) h

theorem headSeq_eq_zero (N : ℕ) (z : FourierPlane N) {n : ℤ}
    (hn : n ∉ symmetricModes N) : headSeq N z n = 0 := by
  unfold headSeq
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  rintro rfl; exact hn (modeIndex_mem_symmetricModes N i)

/-- The head embedding `FourierPlane N → H`. -/
def headVec (c : BoundedCoefficients lower upper) (N : ℕ) (z : FourierPlane N) :
    ActualCM c :=
  (⟨headSeq N z, by
    classical
    change Memℓp (weightedCoordinates (cmModeWeight c) (headSeq N z)) 2
    refine memℓp_gen (summable_of_ne_finset_zero (s := symmetricModes N) ?_)
    intro n hn
    simp [weightedCoordinates, headSeq_eq_zero N z hn]⟩ : WeightedHilbert (cmModeWeight c))

theorem cmCoord_headVec (c : BoundedCoefficients lower upper) (N : ℕ) (z : FourierPlane N)
    (n : ℤ) : cmCoord (headVec c N z) n = headSeq N z n := rfl

/-- Head coordinates `P_N H ≃ FourierPlane N`, `v ↦ (v_{modeIndex i})_i`. -/
def actualCMHeadCoord (c : BoundedCoefficients lower upper) (N : ℕ) :
    actualCMHead c N ≃ₗ[ℝ] FourierPlane N where
  toFun v := fun i => cmCoord (v : ActualCM c) (modeIndex N i)
  invFun z := ⟨headVec c N z, fun n hn => headSeq_eq_zero N z hn⟩
  map_add' v w := by
    funext i
    exact cmCoord_add (v : ActualCM c) (w : ActualCM c) _
  map_smul' r v := by
    funext i
    change cmCoord (r • (v : ActualCM c)) _ = _
    rw [cmCoord_smul]
    simp [Complex.real_smul]
  left_inv v := by
    apply Subtype.ext
    apply cmCoord_ext
    intro n
    change headSeq N (fun i => cmCoord (v : ActualCM c) (modeIndex N i)) n = _
    by_cases hn : n ∈ symmetricModes N
    · rw [symmetricModes_eq_image] at hn
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hn
      rw [headSeq_modeIndex]
    · rw [headSeq_eq_zero N _ hn, v.2 n hn]
  right_inv z := by
    funext i
    exact headSeq_modeIndex N z i

theorem actualCMHeadCoord_apply (c : BoundedCoefficients lower upper) (N : ℕ)
    (v : actualCMHead c N) (i : Fin (2 * N + 1)) :
    actualCMHeadCoord c N v i = cmCoord (v : ActualCM c) (modeIndex N i) := rfl

/-- The CM norm on the head: `‖v‖² = Σ_i 2 q_{modeIndex i} |v_{modeIndex i}|²`. -/
theorem actualCMHead_norm_sq (c : BoundedCoefficients lower upper) (N : ℕ)
    (v : actualCMHead c N) :
    ‖v‖ ^ 2 = ∑ i, 2 * sourceRate c (modeIndex N i) * ‖actualCMHeadCoord c N v i‖ ^ 2 := by
  change ‖(v : ActualCM c)‖ ^ 2 = _
  rw [actualCM_norm_sq, tsum_eq_sum (s := symmetricModes N)]
  · rw [symmetricModes_eq_image, Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
    rfl
  · intro n hn
    rw [v.2 n hn]; simp

instance actualCMHead_finiteDimensional (c : BoundedCoefficients lower upper) (N : ℕ) :
    FiniteDimensional ℝ (actualCMHead c N) :=
  LinearEquiv.finiteDimensional (actualCMHeadCoord c N).symm

/-- Borel σ-algebra on the finite head. Kept as a global instance because the main statements
(`finiteStdGaussian (actualCMHead c N)`) need it at every use site. It cannot create a diamond:
`actualCMHead c N` is a definition owned by this file, and the ambient `ActualCM c` carries no
`MeasurableSpace` instance (`#synth` fails), so no subtype σ-algebra competes with it. It is the
Borel σ-algebra of the subspace topology, i.e. the one used by `finiteStdGaussian`. -/
instance actualCMHead_measurableSpace (c : BoundedCoefficients lower upper) (N : ℕ) :
    MeasurableSpace (actualCMHead c N) := borel _

instance actualCMHead_borelSpace (c : BoundedCoefficients lower upper) (N : ℕ) :
    BorelSpace (actualCMHead c N) := ⟨rfl⟩

/-- **Finite head-law bridge on the actual spaces.** The standard Gaussian of the actual
finite head `(P_N H, ⟨,⟩_H)` is carried by the head coordinates onto the project's
finite Fourier head law `fullWeightFourierGaussian N c` (product of complex Gaussians
with real-component variance `1/(2 q_n)`). -/
theorem actualCMHead_finiteStdGaussian_map (c : BoundedCoefficients lower upper) (N : ℕ) :
    (finiteStdGaussian (actualCMHead c N)).map (actualCMHeadCoord c N) =
      NlsGge.Measure.fullWeightFourierGaussian N c.val :=
  finiteStdGaussian_map_eq_finiteComplexGaussian
    (fun i => sourceRate c (modeIndex N i)) (fun i => sourceRate_pos c _)
    (actualCMHeadCoord c N) (actualCMHead_norm_sq c N)

/-- The same law is the actual cylinder marginal of the countable source law. -/
theorem actualCMHead_finiteStdGaussian_map_eq_cylinder
    (c : BoundedCoefficients lower upper) (N : ℕ) :
    (finiteStdGaussian (actualCMHead c N)).map (actualCMHeadCoord c N) =
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
        (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) := by
  rw [actualCMHead_finiteStdGaussian_map, NlsGge.Measure.fullWeightSequenceGaussian_map_modes]

/-- **Finite Ramer formula for the actual cylinder marginal.** For a real-differentiable
homeomorphism `S` of the head plane, with `T = L⁻¹ ∘ S ∘ L` on `(P_N H, ⟨,⟩_H)`,
`(S⁻¹)_# μ_N = J_T(L⁻¹ ·) μ_N` for the actual head law `μ_N`. -/
theorem actualHead_map_symm_eq_withDensity_ramer (c : BoundedCoefficients lower upper)
    (N : ℕ) (S : FourierPlane N ≃ₜ FourierPlane N) (hS : Differentiable ℝ S) :
    (NlsGge.Measure.fullWeightFourierGaussian N c.val).map S.symm =
      (NlsGge.Measure.fullWeightFourierGaussian N c.val).withDensity (fun z =>
        ENNReal.ofReal (finiteRamerDensity
          (fun v => (actualCMHeadCoord c N).symm (S (actualCMHeadCoord c N v)))
          ((actualCMHeadCoord c N).symm z))) :=
  finiteComplexGaussian_map_symm_eq_withDensity_ramer
    (fun i => sourceRate c (modeIndex N i)) (fun i => sourceRate_pos c _)
    (actualCMHeadCoord c N) (actualCMHead_norm_sq c N) S hS

/-- The head is the range of the actual coordinate projection `P_N`. -/
theorem weightedProjection_mem_actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ)
    (x : ActualCM c) :
    (show ActualCM c from weightedProjection (cmModeWeight c) (symmetricModes N) x) ∈
      actualCMHead c N := by
  intro n hn
  exact (weightedProjection_apply (cmModeWeight c) (symmetricModes N)
    (show WeightedHilbert (cmModeWeight c) from x) n).trans (if_neg hn)

theorem weightedProjection_eq_self_of_mem_actualCMHead (c : BoundedCoefficients lower upper)
    (N : ℕ) (v : actualCMHead c N) :
    (show ActualCM c from
      weightedProjection (cmModeWeight c) (symmetricModes N) (v : ActualCM c)) =
      (v : ActualCM c) := by
  apply cmCoord_ext
  intro n
  refine (weightedProjection_apply (cmModeWeight c) (symmetricModes N)
    (show WeightedHilbert (cmModeWeight c) from (v : ActualCM c)) n).trans ?_
  split_ifs with hn
  · rfl
  · exact (v.2 n hn).symm

end NlsGge.Ramer
