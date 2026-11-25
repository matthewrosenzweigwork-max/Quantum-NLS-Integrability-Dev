import Mathlib

/- LP1SEPARABLE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/ThirdConsultation/PDE/LP1Separable.lean, namespace NlsGge.ThirdConsultation.PDE.  SUPPORT (no packet increment)
   for proof development's PDE-060 conjunct (ii).  Mathlib-only.
   grep (repo .lake Mathlib d13f23b7): Mathlib has no SeparableSpace/SecondCountableTopology instance for `lp`;
   NlsGge G6SupSeparable covers PhysicalL2 (an `Lp` space) only.
   Route: the countable family lp.single 1 i 1 (i : ℤ) is separable, hence so is its real span
   (Mathlib TopologicalSpace.IsSeparable.span); by Mathlib lp.hasSum_single every element is a limit of finite sums
   Σ_{i∈s} lp.single 1 i (f i) = Σ (f i) • lp.single 1 i 1 in that span, so the span is dense; closure of a separable set
   is separable (isSeparable_closure).  Second countability then follows from Mathlib's uniform-space instance
   secondCountable_of_separable.  Stated as theorems, NOT global instances (as G6SupSeparable); consumers use
   `haveI := NlsGge.ThirdConsultation.PDE.lp_one_int_real_secondCountable`. -/
set_option autoImplicit false
open TopologicalSpace

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

theorem lp_one_int_real_separableSpace : SeparableSpace (lp (fun _ : ℤ => ℝ) 1) := by
  set S : Set (lp (fun _ : ℤ => ℝ) 1) := Set.range (fun i : ℤ => lp.single (E := fun _ : ℤ => ℝ) 1 i (1 : ℝ)) with hSdef
  have hS : IsSeparable S := (Set.countable_range _).isSeparable
  have hspan : IsSeparable (Submodule.span ℝ S : Set (lp (fun _ : ℤ => ℝ) 1)) := hS.span
  have hcl : closure (Submodule.span ℝ S : Set (lp (fun _ : ℤ => ℝ) 1)) = Set.univ := by
    refine Set.eq_univ_of_forall (fun f => ?_)
    have hf := lp.hasSum_single (E := fun _ : ℤ => ℝ) (p := 1) ENNReal.one_ne_top f
    refine mem_closure_of_tendsto hf (Filter.Eventually.of_forall (fun s => ?_))
    refine Submodule.sum_mem _ (fun i _ => ?_)
    have e : lp.single (E := fun _ : ℤ => ℝ) 1 i (f i) = (f i) • lp.single (E := fun _ : ℤ => ℝ) 1 i (1 : ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← isSeparable_univ_iff, ← hcl]
  exact isSeparable_closure.2 hspan

theorem lp_one_int_real_secondCountable : SecondCountableTopology (lp (fun _ : ℤ => ℝ) 1) := by
  haveI := lp_one_int_real_separableSpace
  infer_instance

end
end NlsGge.ThirdConsultation.PDE
