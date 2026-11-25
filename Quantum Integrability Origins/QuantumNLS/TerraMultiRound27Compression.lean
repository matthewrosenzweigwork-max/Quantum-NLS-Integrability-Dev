import QuantumNLS.Local002Free
import QuantumNLS.TerraMultiRound26ReducedParity

/-! Smallness of the actual two-dimensional compression on a common Neumann ball. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 QuantumNLS.Local002Free Round25 Round26

variable {L κ r : ℝ}

theorem embed_norm_le_one (hL : 0 < L) (n : ℤ) : ‖embed L n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (embed L n)).2
    (adjoint_embed_comp_embed hL n)
  simpa using (h v).le

theorem compression_diff_bound (hL : 0 < L) (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1) :
    ‖compressionMatrix L κ (u : ℝ → ℂ) n r - 1‖ ≤
      qpar κ L r u / (1 - qpar κ L r u) := by
  have hP := freeProj_eq hL hr hr2 n (fun z hz => hyp.res r n z hr hr2 hz)
  have hzero := compressionMatrix_zero (κ := κ) hL n r hP
  have heq : compressionMatrix L κ (u : ℝ → ℂ) n r - 1 =
      (ContinuousLinearMap.adjoint (embed L n)) ∘L
        (perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r) ∘L embed L n := by
    rw [← hzero]
    ext v
    simp [compressionMatrix, perturbedProj_zero]
  rw [heq]
  have hE := embed_norm_le_one hL n
  have hEa : ‖ContinuousLinearMap.adjoint (embed L n)‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hE
  calc
    ‖(ContinuousLinearMap.adjoint (embed L n)) ∘L
        (perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r) ∘L embed L n‖
        ≤ ‖ContinuousLinearMap.adjoint (embed L n)‖ *
            (‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ * ‖embed L n‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ 1 * (‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ * 1) := by
      gcongr
    _ = ‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ := by ring
    _ ≤ qpar κ L r u / (1 - qpar κ L r u) := proj_diff_bound hyp hr hr2 n u hq

theorem smallCompression_of_q (hL : 0 < L) (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1 / 2) :
    SmallCompression L κ (u : ℝ → ℂ) n r := by
  have hq1 : qpar κ L r u < 1 := by linarith
  apply lt_of_le_of_lt (compression_diff_bound hL hyp hr hr2 n u hq1)
  rw [div_lt_one (by linarith : 0 < 1 - qpar κ L r u)]
  linarith

theorem smallCompression_both (hL : 0 < L) (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (u : Lp ℂ 2 (μI L)) (hq : qpar κ L r u < 1 / 2) :
    SmallCompression L κ (u : ℝ → ℂ) n r ∧
      SmallCompression L κ (fun t => -(u : ℝ → ℂ) t) n r := by
  refine ⟨smallCompression_of_q hL hyp hr hr2 n u hq, ?_⟩
  have hn : qpar κ L r (-u) < 1 / 2 := by simpa [qpar] using hq
  have hs := smallCompression_of_q hL hyp hr hr2 n (-u) hn
  have hp : perturbedProj L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) n r =
      perturbedProj L κ (fun t => -(u : ℝ → ℂ) t) n r := by
    have hf : (fun z => resolvent L κ ((-u : Lp ℂ 2 (μI L)) : ℝ → ℂ) (parity n) z) =
        (fun z => resolvent L κ (fun t => -(u : ℝ → ℂ) t) (parity n) z) := by
      funext z
      exact resolvent_congr_ae (Lp.coeFn_neg u) _ _
    unfold perturbedProj rieszProj
    rw [hf]
  simpa only [SmallCompression, compressionMatrix, hp] using hs

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.embed_norm_le_one
#print axioms QuantumNLS.LocalSpectral.Round27.compression_diff_bound
#print axioms QuantumNLS.LocalSpectral.Round27.smallCompression_of_q
#print axioms QuantumNLS.LocalSpectral.Round27.smallCompression_both
