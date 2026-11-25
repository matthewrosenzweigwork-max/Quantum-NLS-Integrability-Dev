import NlsGge.GK38.GradFundamentalLittleO

/-! # K1: exact potential remainder of the independently defined resolvent.
GK Chapter I, Proposition3.1. The direct Volterra difference proof identifies
this derivative before subsequent variation-of-constants integral identities.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Asymptotics
namespace NlsGge.GK38
noncomputable section

/-- Multiplication by `1−Vφ` recovers an independent inhomogeneous source. -/
theorem resolvent_source38 (φ : PotPair) (z : ℂ) (F : PairCont38) :
    Ring.inverse (1 - volterraP φ z) F -
      volterraP φ z (Ring.inverse (1 - volterraP φ z) F) = F := by
  have h := congrArg (fun T : PairCont38 →L[ℂ] PairCont38 => T F)
    (Ring.mul_inverse_cancel (1 - volterraP φ z) (isUnit_one_sub_volterraP φ z))
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using h

/-- Actual injectivity of `1−Vφ`, from the previously proved invertibility. -/
theorem volterra_inhomogeneous_unique38 (φ : PotPair) (z : ℂ) {X Y F : PairCont38}
    (hX : X - volterraP φ z X = F) (hY : Y - volterraP φ z Y = F) : X = Y := by
  have hx : (1 - volterraP φ z) X = F := by simpa only [sub_apply, one_apply_eq_self] using hX
  have hy : (1 - volterraP φ z) Y = F := by simpa only [sub_apply, one_apply_eq_self] using hY
  have h := congrArg (fun Q : PairCont38 →L[ℂ] PairCont38 => Q X)
    (Ring.inverse_mul_cancel (1 - volterraP φ z) (isUnit_one_sub_volterraP φ z))
  have h' := congrArg (fun Q : PairCont38 →L[ℂ] PairCont38 => Q Y)
    (Ring.inverse_mul_cancel (1 - volterraP φ z) (isUnit_one_sub_volterraP φ z))
  simp only [mul_apply_eq_comp, one_apply_eq_self, hx, hy] at h h'
  exact h.symm.trans h'

/-- Exact second-order remainder, without differentiating nested operator CLMs. -/
theorem fundPotential_remainder_eq38 (φ h : PotPair) (z : ℂ) :
    fundContP (φ + h) z - fundContP φ z - fundPotentialResolventCLM38 φ z h =
      Ring.inverse (1 - volterraP φ z)
        (volterraP h z (fundContP (φ + h) z - fundContP φ z)) := by
  apply volterra_inhomogeneous_unique38 φ z
    (F := volterraP h z (fundContP (φ + h) z - fundContP φ z))
  · have hm := fundCont_eq_add (φ + h) z
    have hm0 := fundCont_eq_add φ z
    have hw := fundPotentialResolventCLM38_volterra φ z h
    rw [volterraP_add, add_apply] at hm
    rw [map_sub, map_sub, map_sub]
    linear_combination hm - hm0 - hw
  · exact resolvent_source38 φ z _

/-- The explicit remainder bound is a product with a factor tending to zero. -/
theorem norm_fundPotential_remainder_le38 (φ h : PotPair) (z : ℂ) :
    ‖fundContP (φ + h) z - fundContP φ z - fundPotentialResolventCLM38 φ z h‖ ≤
      (2 * Real.exp |z.im| * ‖Ring.inverse (1 - volterraP φ z)‖) * ‖h‖ *
        ‖fundContP (φ + h) z - fundContP φ z‖ := by
  rw [fundPotential_remainder_eq38]
  refine ((Ring.inverse (1 - volterraP φ z)).le_opNorm _).trans ?_
  have hv := (volterraP h z).le_opNorm (fundContP (φ + h) z - fundContP φ z)
  have hvnorm : ‖volterraP h z‖ ≤ 2 * Real.exp |z.im| * ‖h‖ := by
    refine (norm_volterraP_le h z).trans ?_
    have hp := mul_le_mul_of_nonneg_left (potL1Norm38_le_two_mul h) (Real.exp_nonneg |z.im|)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hp
  calc
    _ ≤ ‖Ring.inverse (1 - volterraP φ z)‖ *
        ((2 * Real.exp |z.im| * ‖h‖) * ‖fundContP (φ + h) z - fundContP φ z‖) := by
      exact mul_le_mul_of_nonneg_left
        (hv.trans (mul_le_mul_of_nonneg_right hvnorm (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring



/-- The last factor in the exact remainder bound tends to zero. -/
theorem fundPotential_difference_tendsto_zero38 (φ : PotPair) (z : ℂ) :
    Tendsto (fun h : PotPair => ‖fundContP (φ + h) z - fundContP φ z‖) (𝓝 0) (𝓝 0) := by
  have hJ : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hA : Continuous (fun h : PotPair => (φ + h, z)) :=
    ((continuous_const : Continuous (fun _ : PotPair => φ)).add continuous_id).prodMk
      (continuous_const : Continuous (fun _ : PotPair => z))
  have hcomp := hJ.comp hA
  have hc : Continuous (fun h : PotPair => fundContP (φ + h) z) := by
    simpa only [Function.comp_def] using hcomp
  have ht : Tendsto (fun h : PotPair => fundContP (φ + h) z) (𝓝 0) (𝓝 (fundContP φ z)) := by
    simpa only [add_zero] using hc.tendsto 0
  have hs : Tendsto (fun h : PotPair => fundContP (φ + h) z - fundContP φ z) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using ht.sub (show Tendsto (fun _ : PotPair => fundContP φ z) (𝓝 0)
      (𝓝 (fundContP φ z)) from tendsto_const_nhds)
  simpa only [norm_zero] using hs.norm

/-- F3 continuity makes the independently defined exact remainder little-o. -/
theorem isLittleO_fundPotential_remainder38 (φ : PotPair) (z : ℂ) :
    (fun h : PotPair => fundContP (φ + h) z - fundContP φ z -
      fundPotentialResolventCLM38 φ z h) =o[𝓝 0] (fun h : PotPair => h) := by
  apply k1LittleO_norm_factor38
    (q := fun h : PotPair => ‖fundContP (φ + h) z - fundContP φ z‖)
    (K := 2 * Real.exp |z.im| * ‖Ring.inverse (1 - volterraP φ z)‖)
  · positivity
  · intro h; exact norm_nonneg _
  · exact fundPotential_difference_tendsto_zero38 φ z
  · intro h; exact norm_fundPotential_remainder_le38 φ h z


/-- The actual potential derivative is the independently defined Volterra resolvent. -/
theorem hasFDerivAt_fundPotentialResolvent38 (φ : PotPair) (z : ℂ) :
    HasFDerivAt (𝕜 := ℂ) (E := PotPair) (F := PairCont38)
      (fun ψ : PotPair => fundContP ψ z) (fundPotentialResolventCLM38 φ z) φ :=
  k1HasFDerivAt_of_remainder38 (𝕜 := ℂ) (E := PotPair) (F := PairCont38)
    (fun ψ : PotPair => fundContP ψ z) (fundPotentialResolventCLM38 φ z) φ
    (isLittleO_fundPotential_remainder38 φ z)

end
end NlsGge.GK38
