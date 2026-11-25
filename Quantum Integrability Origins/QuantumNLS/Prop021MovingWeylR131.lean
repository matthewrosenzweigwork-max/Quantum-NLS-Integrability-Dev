import QuantumNLS.Prop021WeylLawR131
import QuantumNLS.Prop022OFormIdentity

/-! Strong differentiation of the physical displacement along a moving
center. The linear approximation is compared using the first-moment
field bound, then the strong product rule transports a moving vector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology
open Filter Asymptotics Set
namespace QuantumNLS.Prop021MovingWeylR131

open PhysicalTensor Ext025B3PhysicalSectors Prop022OVacuum Prop024WWeylPhysical
open Prop021WeylLawR131 Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Prop021DisplacementR129
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal
local instance : NormedSpace ℝ (L2T L) := NormedSpace.restrictScalars ℝ ℂ (L2T L)

private lemma norm_G (v : L2T L) (x : physSmooth L) :
    ‖(G v x).val‖ ≤ 2 * ‖v‖ *
      Real.sqrt (Prop022OFormIdentity.T (Phi x.val) + ‖Phi x.val‖^2) := by
  have hg := (G_eq v x).trans (generator_rotation v x.val x.property)
  rw [hg, LinearIsometryEquiv.norm_map, norm_smul, Complex.norm_I, one_mul]
  have h := Prop022OFormIdentity.field_bound (weylVec v) (smoothLift x.val x.property)
  rw [norm_weylVec] at h
  exact h

private lemma ray_sub_self (v : L2T L) (x : physSmooth L) :
    ‖printedWeyl v x.val - x.val‖ ≤ ‖(G v x).val‖ := by
  have hn (r : ℝ) (_hr : r ∈ Icc (0 : ℝ) 1) : ‖(G v (rayD v r x)).val‖ ≤ ‖(G v x).val‖ := by
    rw [G_rayD, LinearIsometryEquiv.norm_map]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (ray_hasDerivAt v r x).hasDerivWithinAt) hn
    (convex_Icc (0 : ℝ) 1) (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  rw [ray_zero] at h
  simpa only [ray, Complex.ofReal_one, one_smul, sub_zero, norm_one, mul_one] using h

private lemma phase_linear_hasDerivAt {f : ℝ → ℂ} {df : ℂ} {t : ℝ} (h : HasDerivAt f df t) :
    HasDerivAt (fun s => Complex.exp (Complex.I * f s))
      ((Complex.I * df) * Complex.exp (Complex.I * f t)) t := by
  have h' := (h.const_mul Complex.I).cexp
  change HasDerivAt (fun s => Complex.exp (Complex.I * f s))
    (Complex.exp (Complex.I * f t) * (Complex.I * df)) t at h'
  rwa [mul_comm] at h'

private lemma phase_sub_one (d : ℝ) : ‖Complex.exp (Complex.I * (d : ℂ)) - 1‖ ≤ |d| := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((t : ℂ) * (d : ℂ)))
  have hd (t : ℝ) : HasDerivAt f ((Complex.I * (d : ℂ)) * f t) t := by
    have ht := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)
    change HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t at ht
    simpa only [f, one_mul] using phase_linear_hasDerivAt (ht.mul_const (d : ℂ))
  have hb (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) : ‖(Complex.I * (d : ℂ)) * f t‖ ≤ |d| := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
    have he : ‖f t‖ = 1 := by
      simp [f, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    rw [he, mul_one]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  simpa [f] using h

/-- Pointwise Lipschitz bound for a fixed smooth vector with a bounded base center. -/
theorem displacement_sub_bound (v w : L2T L) (x : physSmooth L) :
    ‖printedWeyl v x.val - printedWeyl w x.val‖ ≤
      (2 * Real.sqrt (Prop022OFormIdentity.T (Phi x.val)+‖Phi x.val‖^2) + ‖w‖ * ‖x.val‖) * ‖v-w‖ := by
  let d := v-w
  let c := Complex.exp (Complex.I * (⟪w,d⟫_ℂ).im)
  let U := printedWeyl w
  have hv : printedWeyl v x.val = c • U (printedWeyl d x.val) := by
    have he : w+d = v := by dsimp [d]; abel
    rw [← he]
    exact printedWeyl_add w d x.val
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp, Complex.mul_re]
  have ha : ‖c-1‖ ≤ ‖w‖*‖d‖ :=
    (phase_sub_one _).trans ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _))
  rw [hv]
  change ‖c • U (printedWeyl d x.val) - U x.val‖ ≤ _
  have he : c • U (printedWeyl d x.val) - U x.val =
      c • U (printedWeyl d x.val-x.val) + (c-1) • U x.val := by
    rw [map_sub, smul_sub, sub_smul, one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖c • U (printedWeyl d x.val-x.val)‖ + ‖(c-1) • U x.val‖ := norm_add_le _ _
    _ = ‖printedWeyl d x.val-x.val‖ + ‖c-1‖ * ‖x.val‖ := by
      rw [norm_smul, norm_smul, hc, U.norm_map, U.norm_map, one_mul]
    _ ≤ (2 * Real.sqrt (Prop022OFormIdentity.T (Phi x.val)+‖Phi x.val‖^2) + ‖w‖ * ‖x.val‖) * ‖v-w‖ := by
      have h1 := (ray_sub_self d x).trans (norm_G d x)
      have h2 := mul_le_mul_of_nonneg_right ha (norm_nonneg x.val)
      simpa only [d, add_mul, mul_right_comm, mul_assoc, mul_left_comm] using add_le_add h1 h2

/-- Strong Weyl derivative at a fixed smooth vector and arbitrary differentiable center. -/
theorem displacement_hasDerivAt (v : ℝ → L2T L) (t : ℝ) (dv : L2T L) (x : physSmooth L)
    (hv : HasDerivAt v dv t) :
    HasDerivAt (fun r => printedWeyl (v r) x.val)
      (printedWeyl (v t) ((G dv x).val + (Complex.I * (⟪v t,dv⟫_ℂ).im) • x.val)) t := by
  let a := v t
  let z : ℝ → L2T L := fun r => v r - a
  let w : ℝ → L2T L := fun r => (r-t) • dv
  have hw (r : ℝ) : w r = ((r-t : ℝ) : ℂ) • dv :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  have hdiff : (fun r => z r-w r) =o[𝓝 t] fun r => r-t := hv.isLittleO
  have hbase : ∀ᶠ r in 𝓝 t, ‖w r‖ ≤ ‖dv‖ := by
    have hball : ∀ᶠ r in 𝓝 t, r ∈ Metric.ball t (1 : ℝ) := Metric.ball_mem_nhds t (by norm_num)
    filter_upwards [hball] with r hr
    have hb : |r-t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    rw [hw, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hb.le (norm_nonneg dv)).trans_eq (one_mul _)
  have herror : (fun r => printedWeyl (z r) x.val-printedWeyl (w r) x.val) =o[𝓝 t]
      fun r => r-t := by
    have hb : (fun r => printedWeyl (z r) x.val-printedWeyl (w r) x.val) =O[𝓝 t]
        (fun r => z r-w r) := by
      apply IsBigOWith.isBigO (c := 2 * Real.sqrt (Prop022OFormIdentity.T (Phi x.val)+‖Phi x.val‖^2) +
        ‖dv‖ * ‖x.val‖)
      apply IsBigOWith.of_bound
      filter_upwards [hbase] with r hr
      exact (displacement_sub_bound (z r) (w r) x).trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr (norm_nonneg _)))
          (norm_nonneg _))
    exact hb.trans_isLittleO hdiff
  have hlinear : HasDerivAt (fun r => printedWeyl (w r) x.val) (G dv x).val t := by
    let shift : ℝ → ℝ := fun r => r-t
    have harg : HasDerivAt shift 1 t := (hasDerivAt_id t).sub_const t
    have hd := ray_hasDerivAt dv (shift t) x
    have h := hd.hasFDerivAt.comp_hasDerivAt t harg
    have hzero : shift t = 0 := sub_self _
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul, G_rayD, hzero, ray_zero] at h
    have hf : (fun r => printedWeyl (w r) x.val) = (fun r => ray dv (shift r) x.val) := by
      funext r
      rw [hw]
      rfl
    rw [hf]
    exact h
  have hz : HasDerivAt (fun r => printedWeyl (z r) x.val) (G dv x).val t := by
    apply HasDerivAt.of_isLittleO
    convert herror.add hlinear.isLittleO using 1
    funext r
    have hzt : z t = 0 := sub_self _
    have hwt : w t = 0 := by simp [w]
    rw [hzt, hwt]
    abel
  let U := printedWeyl a
  have hlin : HasDerivAt (fun r => U (printedWeyl (z r) x.val)) (U (G dv x).val) t :=
    (U.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hz
  let innerIm := Complex.imCLM.comp ((innerSL ℂ a).restrictScalars ℝ)
  have hi : HasDerivAt (fun r => ((⟪a,z r⟫_ℂ).im : ℂ)) ((⟪a,dv⟫_ℂ).im : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (innerIm.hasFDerivAt.comp_hasDerivAt t (hv.sub_const a))
  have hf := (phase_linear_hasDerivAt hi).smul hlin
  have hzt : z t = 0 := sub_self _
  have hzero : printedWeyl (0 : L2T L) x.val = x.val := by simpa [ray] using ray_zero a x.val
  have hwadd (r : ℝ) : printedWeyl (v r) x.val =
      Complex.exp (Complex.I * (⟪a,z r⟫_ℂ).im) • U (printedWeyl (z r) x.val) := by
    have he : a+z r = v r := by dsimp [z]; abel
    rw [← he]
    exact printedWeyl_add a (z r) x.val
  change HasDerivAt (fun r => Complex.exp (Complex.I * (⟪a,z r⟫_ℂ).im) • U (printedWeyl (z r) x.val))
    (Complex.exp (Complex.I * (⟪a,z t⟫_ℂ).im) • U (G dv x).val +
      (Complex.I * (⟪a,dv⟫_ℂ).im * Complex.exp (Complex.I * (⟪a,z t⟫_ℂ).im)) •
        U (printedWeyl (z t) x.val)) t at hf
  rw [hzt, hzero, inner_zero_right, Complex.zero_im, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, one_smul] at hf
  rw [map_add, map_smul]
  exact hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hwadd r)

/-- Strong continuity extends from the smooth domain to the whole Fock space
by isometry and density. -/
theorem displacement_continuousAt (v : ℝ → L2T L) (t : ℝ) (hv : ContinuousAt v t) (x : Fock L) :
    ContinuousAt (fun r => printedWeyl (v r) x) t := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := smooth_dense.exists_dist_lt x (by linarith : 0 < ε/4)
  let C := 2 * Real.sqrt (Prop022OFormIdentity.T (Phi y)+‖Phi y‖^2) + ‖v t‖ * ‖y‖
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hv' := Metric.tendsto_nhds.mp hv.tendsto (ε/(2*(C+1))) (by positivity)
  filter_upwards [hv'] with r hr
  have hd : dist (printedWeyl (v r) y) (printedWeyl (v t) y) ≤ C * dist (v r) (v t) := by
    simpa only [dist_eq_norm, C] using displacement_sub_bound (v r) (v t) ⟨y,hy⟩
  have hn : dist (printedWeyl (v r) y) (printedWeyl (v t) y) < ε/2 := by
    have h₁ : C * dist (v r) (v t) ≤ (C+1)*dist (v r) (v t) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) dist_nonneg
    apply (hd.trans h₁).trans_lt
    have h₂ := (lt_div_iff₀ (by positivity : 0 < 2*(C+1))).mp hr
    nlinarith
  have he := dist_triangle4 (printedWeyl (v r) x) (printedWeyl (v r) y)
    (printedWeyl (v t) y) (printedWeyl (v t) x)
  rw [LinearIsometryEquiv.dist_map, LinearIsometryEquiv.dist_map] at he
  have hyx : dist y x < ε/4 := by simpa only [dist_comm] using hxy
  linarith

private def asReal (U : Fock L ≃ₗᵢ[ℂ] Fock L) : Fock L →ₗᵢ[ℝ] Fock L where
  toLinearMap := U.toLinearEquiv.toLinearMap.restrictScalars ℝ
  norm_map' := U.norm_map

/-- Strong product rule on the actual moving input, with its physical
Weyl generator and exact central scalar. -/
theorem moving_displacement_hasDerivAt (v : ℝ → L2T L) (x : ℝ → Fock L) (t : ℝ)
    (dv : L2T L) (dx : Fock L) (hv : HasDerivAt v dv t) (hx : HasDerivAt x dx t)
    (hs : x t ∈ physSmooth L) :
    HasDerivAt (fun r => printedWeyl (v r) (x r))
      (printedWeyl (v t)
        (dx + (G dv ⟨x t,hs⟩).val + (Complex.I * (⟪v t,dv⟫_ℂ).im) • x t)) t := by
  have hd := displacement_hasDerivAt v t dv ⟨x t,hs⟩ hv
  let force := (G dv ⟨x t,hs⟩).val + (Complex.I * (⟪v t,dv⟫_ℂ).im) • x t
  have h := Prop021StrongProductR131.hasDerivAt_apply (E := Fock L)
    (U := fun r => asReal (printedWeyl (v r))) (v := x) (t := t) (dv := dx)
    (dU := printedWeyl (v t) force) (displacement_continuousAt v t hv.continuousAt) hd hx
  change HasDerivAt (fun r => printedWeyl (v r) (x r))
    (printedWeyl (v t) dx + printedWeyl (v t) force) t at h
  rw [add_assoc]
  change HasDerivAt (fun r => printedWeyl (v r) (x r))
    (printedWeyl (v t) (dx + force)) t
  rw [map_add]
  exact h

end QuantumNLS.Prop021MovingWeylR131

#print axioms QuantumNLS.Prop021MovingWeylR131.moving_displacement_hasDerivAt

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021MovingWeylR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
