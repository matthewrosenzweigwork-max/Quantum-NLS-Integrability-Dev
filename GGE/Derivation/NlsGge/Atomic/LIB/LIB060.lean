import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory

namespace NlsGge.Atomic.LIB060

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {f : ℕ → α → E} {G : α → ℝ}

/-- A family dominated almost everywhere by one integrable real envelope is
uniformly integrable in `L¹`. The result holds for arbitrary measures and
Banach-valued (indeed normed additive group-valued) functions. -/
theorem uniformIntegrable_of_common_domination
    (hG : Integrable G μ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ G x) :
    UniformIntegrable f 1 μ := by
  have hGmem : MemLp G 1 μ := memLp_one_iff_integrable.mpr hG
  have hconstant : UnifIntegrable (fun _ : ℕ => G) 1 μ :=
    unifIntegrable_const (by norm_num) (by norm_num) hGmem
  have hunif : UnifIntegrable f 1 μ := by
    rw [unifIntegrable_iff] at hconstant ⊢
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hconstant ε hε
    refine ⟨δ, hδ, fun n s hs => ?_⟩
    exact (eLpNorm_mono_ae_real (hf n).restrict
      ((hb n).filter_mono ae_restrict_le)).trans (hbound 0 s hs)
  refine ⟨hunif, ⟨(eLpNorm G 1 μ).toNNReal, ?_⟩⟩
  intro n
  calc
    eLpNorm (f n) 1 μ ≤ eLpNorm G 1 μ := eLpNorm_mono_ae_real (hf n) (hb n)
    _ = (eLpNorm G 1 μ).toNNReal := (ENNReal.coe_toNNReal hGmem.eLpNorm_lt_top.ne).symm

end NlsGge.Atomic.LIB060
