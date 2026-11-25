import QuantumNLS.TerraMultiRound18AnalyticFlow
import QuantumNLS.ProductTorusLocalDiff

/-! Variational equation for the D01 flow, conditional only on the named
short-time GP-04 analytic initial-dependence remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Filter Topology Set Metric
open QuantumNLS.D01LocalPrimitive QuantumNLS.TerraMultiRound18Flow
open QuantumNLS.TerraMultiRound18AnalyticFlow QuantumNLS.ProductTorusLocalDiff
namespace QuantumNLS.TerraMultiRound18Variational

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem right_deriv_zero {f : H → H} {φ : ℝ → H → H}
    (hf : ContDiff ℝ 1 f)
    (hφ : ∀ v t, HasDerivAt (fun t => φ t v) (f (φ t v)) t)
    (hφ0 : ∀ v, φ 0 v = v) (p : H) :
    HasDerivWithinAt (fun r => fderiv ℝ (φ r) p) (fderiv ℝ f p) (Ici 0) 0 := by
  obtain ⟨ρ, hρ, τ, hτ, Hloc⟩ := local_diff hf hφ hφ0 p
  obtain ⟨J, -, hJ0, hJd, hJt⟩ := Hloc p (mem_ball_self hρ)
  have h1 : HasDerivWithinAt J ((fderiv ℝ f (φ 0 p)).comp (J 0)) (Icc 0 τ) 0 :=
    hJd 0 ⟨le_rfl, hτ.le⟩
  rw [hφ0, hJ0, ContinuousLinearMap.comp_id] at h1
  have h2 : HasDerivWithinAt J (fderiv ℝ f p) (Ici 0) 0 :=
    (hasDerivWithinAt_inter (Iio_mem_nhds hτ)).1
      (h1.mono fun x hx => ⟨(mem_Ici.1 hx.1), (mem_Iio.1 hx.2).le⟩)
  refine h2.congr_of_eventuallyEq ?_ (hJt 0 ⟨le_rfl, hτ.le⟩).fderiv
  filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ)) (Iio_mem_nhds hτ)] with r hr
  exact (hJt r ⟨mem_Ici.1 hr.1, (mem_Iio.1 hr.2).le⟩).fderiv

private theorem field_contDiff (S : Hyp H) : ContDiff ℝ 1 S.Y :=
  contDiff_iff_contDiffAt.mpr (fun x =>
    ((QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 x).contDiffAt)

private theorem deriv_zero (S : Hyp H) (p : H) :
    HasDerivAt (fun r => fderiv ℝ (flow S r) p) (fderiv ℝ S.Y p) 0 := by
  have hR := right_deriv_zero (field_contDiff S) (fun v t => (flow_spec S v).2 t)
    (fun v => (flow_spec S v).1) p
  have hφneg : ∀ v t, HasDerivAt (fun t => flow S (-t) v) (-S.Y (flow S (-t) v)) t := by
    intro v t
    simpa [Function.comp_def] using ((flow_spec S v).2 (-t)).scomp t (hasDerivAt_neg t)
  have hL0 := right_deriv_zero (field_contDiff S).neg hφneg
    (fun v => by simpa using (flow_spec S v).1) p
  have hneg : HasDerivWithinAt (fun r : ℝ => -r) (-1) (Iic 0) 0 :=
    (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
  have hmaps : MapsTo (fun r : ℝ => -r) (Iic 0) (Ici 0) := fun r hr => by
    simp only [mem_Iic, mem_Ici] at hr ⊢
    linarith
  have hL0' : HasDerivWithinAt (fun r => fderiv ℝ (fun x => flow S (-r) x) p)
      (fderiv ℝ (fun x => -S.Y x) p) (Ici 0) ((fun r : ℝ => -r) 0) := by
    simp only [neg_zero]
    exact hL0
  have hL1 := hL0'.scomp 0 hneg hmaps
  have hL : HasDerivWithinAt (fun r => fderiv ℝ (flow S r) p) (fderiv ℝ S.Y p) (Iic 0) 0 := by
    have he : (fun r => fderiv ℝ (flow S r) p) =
        (fun r => fderiv ℝ (fun x => flow S (-r) x) p) ∘ (fun r : ℝ => -r) := by
      funext r
      simp
    rw [he]
    convert hL1 using 1
    rw [fderiv_fun_neg, smul_neg, neg_one_smul, neg_neg]
  have hU := hL.union hR
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hU
  exact hU

theorem fderiv_flow_add (S : Hyp H) (ha : GP04CompactLocalAnalyticity S) (r t : ℝ) (u : H) :
    fderiv ℝ (flow S (r + t)) u =
      (fderiv ℝ (flow S r) (flow S t u)).comp (fderiv ℝ (flow S t) u) := by
  have hcomp : flow S (r + t) = flow S r ∘ flow S t := funext fun x => flow_add S r t x
  rw [hcomp]
  exact fderiv_comp (hg := (analytic_initial_dependence S ha r _).differentiableAt)
    (hf := (analytic_initial_dependence S ha t u).differentiableAt)

theorem variational (S : Hyp H) (ha : GP04CompactLocalAnalyticity S) (u : H) (t : ℝ) :
    HasDerivAt (fun t => fderiv ℝ (flow S t) u)
      ((fderiv ℝ S.Y (flow S t u)).comp (fderiv ℝ (flow S t) u)) t := by
  set p := flow S t u
  set D0 := fderiv ℝ (flow S t) u
  have he : (fun s => fderiv ℝ (flow S s) u) = fun s => (fderiv ℝ (flow S (s - t)) p).comp D0 := by
    funext s
    rw [← fderiv_flow_add S ha, sub_add_cancel]
  rw [he]
  have hG : HasDerivAt (fun s => fderiv ℝ (flow S (s - t)) p) (fderiv ℝ S.Y p) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact deriv_zero S p)
  have hc := hG.clm_comp (hasDerivAt_const t D0)
  convert hc using 1
  simp

theorem variational_apply (S : Hyp H) (ha : GP04CompactLocalAnalyticity S) (u k : H) (t : ℝ) :
    HasDerivAt (fun t => fderiv ℝ (flow S t) u k)
      (fderiv ℝ S.Y (flow S t u) (fderiv ℝ (flow S t) u k)) t := by
  have hc := (variational S ha u t).clm_apply (hasDerivAt_const t k)
  convert hc using 1
  simp

#print axioms fderiv_flow_add
#print axioms variational
#print axioms variational_apply
end QuantumNLS.TerraMultiRound18Variational
