import QuantumNLS.Ext025GP04LocalR30m
import QuantumNLS.Ext025GP04AnalyticR30m
import QuantumNLS.Ext025A3Gronwall
import QuantumNLS.Ext025A6CompactFlow

/-!
FIN-EXT025-GP-04, historical manifest SHA-256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782.
Owner decision 2026-11-17 item 2 applies continuity of the state derivative
to the C¹ clause. The other real clauses use the original Picard hypotheses.
-/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
open Set Metric Topology Filter Function ODE
open scoped NNReal
namespace QuantumNLS.Ext025GP04ContractR30m

open Ext025GP04LocalR30m Ext025GP04FlowR30m Ext025GP04AnalyticR30m
open Ext025A2 Ext025A3 Ext025GP04RealAnalyticR30m

/-- The operator-norm estimate for the actual variational equation. -/
theorem variational_operator_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b C : ℝ} {A J : ℝ → V →L[ℝ] V}
    (hJ : ContinuousOn J (Icc a b))
    (h0 : J a = ContinuousLinearMap.id ℝ V)
    (hvar : ∀ t ∈ Icc a b, HasDerivWithinAt J ((A t).comp (J t)) (Icc a b) t)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ C) :
    ∀ t ∈ Icc a b, ‖J t‖ ≤ Real.exp (C * (t-a)) := by
  have hright (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt J ((A t).comp (J t)) (Ici t) t := by
    have h := (hvar t (Ico_subset_Icc_self ht)).mono
      (show Ici t ∩ Iio b ⊆ Icc a b from fun _ hz => ⟨ht.1.trans hz.1,hz.2.le⟩)
    exact (hasDerivWithinAt_inter (Iio_mem_nhds ht.2)).mp h
  have h := gp04_exponential_norm hJ hright
    (show ‖J a‖ ≤ 1 by rw [h0]; exact ContinuousLinearMap.norm_id_le)
    (fun t ht => (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hA t (Ico_subset_Icc_self ht)) (norm_nonneg _)))
  simpa only [one_mul] using h

/-- The GP-04 clauses in their local Banach-space formulations. Each field
is the complete statement of its named theorem, before any arguments. -/
structure Contract.{u,v} : Prop where
  commonPicardTime : type_of% (@common_time.{u})
  integralExistence : type_of% (@gp04_differential_existence.{u})
  integralUniqueness : type_of% (@unique_integral.{u})
  differentialUniqueness : type_of% (@gp04_uniqueness.{u})
  integralGronwall : type_of% (@gp04_integral_gronwall)
  trajectoryGronwall : type_of% (@gp04_exponential_dependence.{u})
  variationalGronwall : type_of% (@gp04_exponential_norm.{u})
  variationalOperatorBound : type_of% (@variational_operator_bound.{u})
  variationalPicard : type_of% (@gp04_variational_existence.{u})
  continuouslyDifferentiableFlow : type_of% (@local_c1.{u})
  reverseDifferential : type_of% (@inverse_differential.{u})
  complexInitialDependence : type_of% (@complex_initial.{u})
  realInitialDependence : type_of% (@real_analytic_flow.{u})
  localAutonomousTime : type_of% (@autonomous_time_analytic.{u})
  localAnalyticTimeField : type_of% (@nonautonomous_time_analytic.{u})
  finiteTrajectoryCover : type_of% (@finite_trajectory_cover.{u,v})
  compactCommonAutonomousTime : type_of% (@Ext025A6.compact_common_local_solutions.{u})
  compactEndpoint : type_of% (@compact_endpoint.{u})
  compactRestart : type_of% (@compact_restart.{u})
  boundedAngleUniformity : type_of% (@Ext025A4HeldDependence.held.{u,v})

/-- The GP-04 clauses with the owner-corrected state regularity condition. -/
theorem contract_GP04.{u,v} : Contract.{u,v} :=
  ⟨@common_time.{u}, @gp04_differential_existence.{u}, @unique_integral.{u}, @gp04_uniqueness.{u},
    @gp04_integral_gronwall, @gp04_exponential_dependence.{u}, @gp04_exponential_norm.{u}, @variational_operator_bound.{u},
    @gp04_variational_existence.{u},
    @local_c1.{u}, @inverse_differential.{u}, @complex_initial.{u}, @real_analytic_flow.{u},
    @autonomous_time_analytic.{u}, @nonautonomous_time_analytic.{u},
    @finite_trajectory_cover.{u,v}, @Ext025A6.compact_common_local_solutions.{u},
    @compact_endpoint.{u}, @compact_restart.{u},
    @Ext025A4HeldDependence.held.{u,v}⟩

end QuantumNLS.Ext025GP04ContractR30m

#print axioms QuantumNLS.Ext025GP04ContractR30m.variational_operator_bound
#print axioms QuantumNLS.Ext025GP04ContractR30m.contract_GP04
