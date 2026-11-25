import QuantumNLS.Local003Final
import QuantumNLS.Local005SourceResetD

/-! LOCAL-006, construction identity. All operators below are the actual frozen
DEF-049 objects. No spectral or summability conclusion is supplied as a premise
of the ball theorem. This module alone does not prove the collective chart. -/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace QuantumNLS.Local006.CompressionE
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA
  QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry QuantumNLS.Local003Range

variable {L κ r : ℝ}

/-- The actual free compression of the shifted spectral moment, in the ordered
two-dimensional free basis. -/
def momentMatrix (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ) : E2 →L[ℂ] E2 :=
  ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ u n r ∘L embed L n

lemma graph_output_unique {G : Set (H2 L × H2 L)} (hG : IsSelfAdjointGraph G)
    {x v w : H2 L} (hv : (x, v) ∈ G) (hw : (x, w) ∈ G) : v = w := by
  have hzero : ∀ y ∈ domOf G, ⟪v - w, y⟫_ℂ = 0 := by
    rintro y ⟨z, hz⟩
    have hv' := hG.eq ▸ hv
    have hw' := hG.eq ▸ hw
    have a : ⟪x, z⟫_ℂ = ⟪v, y⟫_ℂ := hv' (y, z) hz
    have b : ⟪x, z⟫_ℂ = ⟪w, y⟫_ℂ := hw' (y, z) hz
    rw [inner_sub_left, ← a, ← b, sub_self]
  have hclosed : IsClosed {y : H2 L | ⟪v - w, y⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : closure (domOf G) ⊆ {y : H2 L | ⟪v - w, y⟫_ℂ = 0} :=
    hclosed.closure_subset_iff.mpr hzero
  have h := hsub (hG.dense (v - w))
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h)

/-- The shifted moment vanishes on the complementary spectral subspace. -/
theorem moment_mul_projection (hL : 0 < L) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (c : Ctx L κ r n u) :
    dressedIntegral L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
      dressedIntegral L κ (u : ℝ → ℂ) n r := by
  ext f : 1
  have a := pair_mem hL hr hr2 n u c.hq c.hSA f
  have b := pair_mem hL hr hr2 n u c.hq c.hSA
    (perturbedProj L κ (u : ℝ → ℂ) n r f)
  rw [PP_apply c] at b
  exact add_right_cancel (graph_output_unique c.hSA b a)

/-- The moment also has range in the spectral subspace. -/
theorem projection_mul_moment (hL : 0 < L) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (c : Ctx L κ r n u) :
    perturbedProj L κ (u : ℝ → ℂ) n r * dressedIntegral L κ (u : ℝ → ℂ) n r =
      dressedIntegral L κ (u : ℝ → ℂ) n r := by
  have h := congrArg (fun T : H2 L →L[ℂ] H2 L => ContinuousLinearMap.adjoint T)
    (moment_mul_projection hL hr hr2 n u c)
  change ContinuousLinearMap.adjoint
    (dressedIntegral L κ (u : ℝ → ℂ) n r ∘L perturbedProj L κ (u : ℝ → ℂ) n r) = _ at h
  rw [ContinuousLinearMap.adjoint_comp, c.hP, c.hD] at h
  exact h

/-- The exact normalization identity printed in the LOCAL-006 proof. -/
theorem reduced_matrix_compression (hL : 0 < L) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (c : Ctx L κ r n u) :
    Bf L κ (u : ℝ → ℂ) n r - (pm L n : ℂ) • (1 : E2 →L[ℂ] E2) =
      invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) *
        momentMatrix L κ (u : ℝ → ℂ) n r *
        invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
  have hPD := projection_mul_moment hL hr hr2 n u c
  have hDP := moment_mul_projection hL hr hr2 n u c
  rw [Bf_eq, S_herm c, c.hP, hPD, hDP, add_sub_cancel_left]
  rfl

/-- The normalization identity holds on one full ball with a proved positive
radius, independent of the frequency and of Fourier support. -/
theorem reduced_matrix_compression_on_ball (hL : 0 < L) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (u : Lp ℂ 2 (μI L)), ‖u‖ < ρ → ∀ n : ℤ,
      SmallCompression L κ (u : ℝ → ℂ) n r ∧
      Bf L κ (u : ℝ → ℂ) n r - (pm L n : ℂ) • (1 : E2 →L[ℂ] E2) =
        invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) *
          momentMatrix L κ (u : ℝ → ℂ) n r *
          invSqrtM (compressionMatrix L κ (u : ℝ → ℂ) n r) := by
  refine ⟨goodRadius κ L r, goodRadius_pos κ L r, ?_⟩
  intro u hu n
  have c := ctx_of_ball hL hr hr2 n u hu
  exact ⟨c.hsmall, reduced_matrix_compression hL hr hr2 n u c⟩

end QuantumNLS.Local006.CompressionE

#print axioms QuantumNLS.Local006.CompressionE.graph_output_unique
#print axioms QuantumNLS.Local006.CompressionE.moment_mul_projection
#print axioms QuantumNLS.Local006.CompressionE.projection_mul_moment
#print axioms QuantumNLS.Local006.CompressionE.reduced_matrix_compression_on_ball

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.CompressionE." ||
        n.toString.startsWith "_private.QuantumNLS.Local006CompressionE" then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Local006CompressionE audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
