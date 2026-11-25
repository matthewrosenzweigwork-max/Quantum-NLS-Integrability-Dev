import Mathlib
import QuantumNLS.Local003InvSqrt
import QuantumNLS.Local003Range
import QuantumNLS.Local003Analytic

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage M4: the normalized isometry.

Source (before the theorem): "`U_n = P_n(u) P [P P_n(u) P]^{-1/2}` ... Thus `U_n^* U_n = 1` and `U_n U_n^* = P_n(u)`."
Here `U = Uf = P_n(u) ∘ embed ∘ invSqrtM (compressionMatrix)` (the repaired definition `normalizedIsometry2`, see
`Local003Analytic.Uf`).

* `goodRadius`: one ball `‖u‖ < goodRadius κ L r` (independent of `n`) on which `Ctx` holds: graph self-adjointness,
  `P² = P`, `rank P = 2`, `P` self-adjoint, `‖C - 1‖ < 1`, `D` Hermitian.
* `UU_one : U^* U = 1` (uses `C^{-1/2} C C^{-1/2} = 1`, `Local003InvSqrt.invSqrtM_mul_mul`).
* `UUstar : U U^* = P_n(u)` (`U` is an isometry with range inside `ran P`, which has rank 2). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Isometry
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local002Rank
  QuantumNLS.Local002Free QuantumNLS.Local003Hermitian QuantumNLS.Local003Proj QuantumNLS.Local003Range
  QuantumNLS.Local003Analytic QuantumNLS.Local003InvSqrt QuantumNLS.LocalSpectral.Round27

variable {L κ r : ℝ}

/-- One ball, independent of `n`. -/
def goodRadius (κ L r : ℝ) : ℝ :=
  min (compressionRadius κ L r) (1 / (4 * (Real.sqrt κ * Cmax L (r / 2) + 1)))

lemma goodRadius_pos (κ L r : ℝ) : 0 < goodRadius κ L r := by
  unfold goodRadius
  refine lt_min (compressionRadius_pos κ L r) ?_
  have h1 : 0 ≤ Real.sqrt κ * Cmax L (r / 2) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  positivity

/-- The standing facts on the ball. -/
structure Ctx (L κ r : ℝ) (n : ℤ) (u : Lp ℂ 2 (μI L)) : Prop where
  hq : qpar κ L r u < 1
  hidem : perturbedProj L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
    perturbedProj L κ (u : ℝ → ℂ) n r
  hrank : Module.finrank ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) = 2
  hSA : IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n))
  hsmall : SmallCompression L κ (u : ℝ → ℂ) n r
  hP : ContinuousLinearMap.adjoint (perturbedProj L κ (u : ℝ → ℂ) n r) = perturbedProj L κ (u : ℝ → ℂ) n r
  hD : ContinuousLinearMap.adjoint (dressedIntegral L κ (u : ℝ → ℂ) n r) = dressedIntegral L κ (u : ℝ → ℂ) n r

theorem ctx_of_ball (hL : 0 < L) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hu : ‖u‖ < goodRadius κ L r) : Ctx L κ r n u := by
  have hyp := QuantumNLS.Local002Discharge.free_resolvent_hyp L κ
  have hu1 : ‖u‖ < compressionRadius κ L r := lt_of_lt_of_le hu (min_le_left _ _)
  have hu2 : ‖u‖ < 1 / (4 * (Real.sqrt κ * Cmax L (r / 2) + 1)) := lt_of_lt_of_le hu (min_le_right _ _)
  set a : ℝ := Real.sqrt κ * Cmax L (r / 2) with ha
  have ha0 : 0 ≤ a := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hK : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ < 1 / 2 := by
    have h1 : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ = 2 * a * ‖u‖ := by rw [ha]; ring
    rw [h1]
    calc 2 * a * ‖u‖ ≤ 2 * a * (1 / (4 * (a + 1))) :=
          mul_le_mul_of_nonneg_left hu2.le (by positivity)
      _ < 1 / 2 := by
          rw [div_eq_mul_inv]
          have : (0 : ℝ) < a + 1 := by linarith
          field_simp
          linarith
  have hqle : qpar κ L r u ≤ 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ := by
    have hC : Cconst L r ≤ Cmax L (r / 2) := Cconst_le hL (by positivity) (by linarith) hr2
    unfold qpar
    have : 0 ≤ 2 * Real.sqrt κ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC this) (norm_nonneg _)
  have hq1 : qpar κ L r u < 1 := by linarith
  have hPs : ContinuousLinearMap.adjoint (perturbedProj L κ (u : ℝ → ℂ) n r) =
      perturbedProj L κ (u : ℝ → ℂ) n r :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).2 (fun x y => proj_symm hL hr hr2 n u hq1 x y)).symm
  have hDs : ContinuousLinearMap.adjoint (dressedIntegral L κ (u : ℝ → ℂ) n r) =
      dressedIntegral L κ (u : ℝ → ℂ) n r :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).2 (fun x y => dressedIntegral_symm hL hr hr2 n u hq1 x y)).symm
  exact ⟨hq1, proj_idem hyp hL hr hr2 n u (by linarith), proj_rank hyp hL hr hr2 n u hK,
    local_selfadjoint hyp hL hr hr2 n u hq1, (smallCompression_on_ball hL hyp hr hr2 u hu1 n).1, hPs, hDs⟩

/-! ### The matrices `C`, `S = C^{-1/2}` and the isometry `U` -/

lemma star_invSqrtM {T : E2 →L[ℂ] E2} (h : ‖T - 1‖ < 1) : star (invSqrtM T) = invSqrtM (star T) := by
  have h1 := (hasSum_invSqrtM h).star
  have e : (fun k : ℕ => star ((invSqrtCoeff k : ℂ) • (T - 1) ^ k)) =
      fun k : ℕ => (invSqrtCoeff k : ℂ) • (star T - 1) ^ k := by
    ext1 k
    have hs : star (T - 1) = star T - 1 := by
      rw [ContinuousLinearMap.star_eq_adjoint, map_sub, ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint]
      simp
    rw [star_smul, star_pow, hs]
    simp
  rw [e] at h1
  rw [← h1.tsum_eq]
  rfl

variable {n : ℤ} {u : Lp ℂ 2 (μI L)}

lemma C_herm (c : Ctx L κ r n u) :
    star (compressionMatrix L κ (u : ℝ → ℂ) n r) = compressionMatrix L κ (u : ℝ → ℂ) n r := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  unfold compressionMatrix
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    c.hP]
  rfl

lemma S_herm (c : Ctx L κ r n u) :
    ContinuousLinearMap.adjoint (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) =
      invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_invSqrtM c.hsmall, C_herm c]

lemma adjU (c : Ctx L κ r n u) :
    ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) =
      (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)) ∘L (ContinuousLinearMap.adjoint (embed L n)) ∘L
        (perturbedProj L κ (u : ℝ → ℂ) n r) := by
  unfold Uf
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, c.hP, S_herm c]
  rfl

lemma PP_apply (c : Ctx L κ r n u) (x : H2 L) :
    perturbedProj L κ (u : ℝ → ℂ) n r (perturbedProj L κ (u : ℝ → ℂ) n r x) =
      perturbedProj L κ (u : ℝ → ℂ) n r x :=
  congrArg (fun T : H2 L →L[ℂ] H2 L => T x) c.hidem

/-- **`U^* U = 1`.** -/
theorem UU_one (c : Ctx L κ r n u) :
    ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) ∘L Uf L κ (u : ℝ → ℂ) n r =
      ContinuousLinearMap.id ℂ E2 := by
  have hS := invSqrtM_mul_mul c.hsmall
  refine ContinuousLinearMap.ext fun v => ?_
  rw [adjU c]
  show invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r)
      (ContinuousLinearMap.adjoint (embed L n) (perturbedProj L κ (u : ℝ → ℂ) n r
        (perturbedProj L κ (u : ℝ → ℂ) n r (embed L n
          (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) v))))) = v
  rw [PP_apply c]
  have := congrArg (fun T : E2 →L[ℂ] E2 => T v) hS
  simpa [ContinuousLinearMap.mul_apply, compressionMatrix] using this

lemma U_inj (c : Ctx L κ r n u) : Function.Injective (Uf L κ (u : ℝ → ℂ) n r) := by
  intro v w h
  have h1 := UU_one c
  have e := fun x : E2 => congrArg (fun T : E2 →L[ℂ] E2 => T x) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e
  rw [← e v, ← e w, h]

lemma range_U_eq (c : Ctx L κ r n u) :
    LinearMap.range (Uf L κ (u : ℝ → ℂ) n r : E2 →ₗ[ℂ] H2 L) = rng (perturbedProj L κ (u : ℝ → ℂ) n r) := by
  have hle : LinearMap.range (Uf L κ (u : ℝ → ℂ) n r : E2 →ₗ[ℂ] H2 L) ≤
      rng (perturbedProj L κ (u : ℝ → ℂ) n r) := by
    rintro _ ⟨w, rfl⟩
    exact ⟨embed L n (invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) w), rfl⟩
  have hfin : Module.Finite ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) :=
    Module.finite_of_finrank_pos (by rw [c.hrank]; norm_num)
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [c.hrank, LinearMap.finrank_range_of_inj (U_inj c)]
  simp

/-- **`U U^* = P_n(u)`.** -/
theorem UUstar (c : Ctx L κ r n u) :
    Uf L κ (u : ℝ → ℂ) n r ∘L ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) =
      perturbedProj L κ (u : ℝ → ℂ) n r := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hPx : perturbedProj L κ (u : ℝ → ℂ) n r x ∈ LinearMap.range (Uf L κ (u : ℝ → ℂ) n r : E2 →ₗ[ℂ] H2 L) := by
    rw [range_U_eq c]; exact ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := hPx
  have hx : ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) x =
      ContinuousLinearMap.adjoint (Uf L κ (u : ℝ → ℂ) n r) (perturbedProj L κ (u : ℝ → ℂ) n r x) := by
    rw [adjU c]
    simp only [ContinuousLinearMap.comp_apply, PP_apply c]
  have h1 := UU_one c
  have e := congrArg (fun T : E2 →L[ℂ] E2 => T w) h1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at e
  simp only [ContinuousLinearMap.comp_apply]
  rw [hx]
  have hw' : Uf L κ (u : ℝ → ℂ) n r w = perturbedProj L κ (u : ℝ → ℂ) n r x := hw
  rw [← hw', e]

end QuantumNLS.Local003Isometry
#print axioms QuantumNLS.Local003Isometry.ctx_of_ball
#print axioms QuantumNLS.Local003Isometry.UU_one
#print axioms QuantumNLS.Local003Isometry.UUstar
