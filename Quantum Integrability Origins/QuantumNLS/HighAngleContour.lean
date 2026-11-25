import QuantumNLS.HaarNonlinearTail
import QuantumNLS.Prop018Period

/-! Exact free-background algebra and the contour residue needed to identify
NC0 - NL with the accepted nonlinear remainder in R-F1423202. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Set Filter Topology
open scoped BigOperators
namespace QuantumNLS.HighAngleContour
open HaarFreeTaylor HaarSummableReconstruction PeriodReconstructionCore
open LabelExactPeriod PeriodReconstruction PeriodTwoTerm HaarNonlinearAbstract Prop018Period

/-- Both accepted modules use exactly the same quadratic root, including
the branch. This is an algebraic identity of their literal definitions. -/
lemma free_root_identity (L κ c : ℝ) {N : ℕ} (q : Fin N → ℝ) (z w : ℂ)
    (hew : ef L z = ew L w) :
    aNf L κ c G0 q z = aF L w (sNf L c q z - (1 + ew L w)) := by
  have ha : Af κ G0 z = 1 := Af_G0 κ z
  have hd : Df L κ G0 z = 1 - ew L w := by simp only [Df, ha, hew, div_one]
  have hs : sf L κ G0 z = 1 + ew L w := by simp only [sf, ha, hew, div_one]
  have hu : Wf L κ c G0 q z = uF L w (sNf L c q z - (1 + ew L w)) := by
    simp only [Wf, hs, hd, uF]
    congr 1
    ring
  simp only [aNf, DNf, hd, hu, aF]
  congr 1
  ring

/-- Closed square used for the translated high-angle contour. -/
def box (a : ℝ) : Set ℂ := Icc (-a) a ×ℂ Icc (-a) a

lemma box_mem_nhds {a : ℝ} (ha : 0 < a) : box a ∈ 𝓝 (0 : ℂ) := by
  have hr : Icc (-a) a ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) ha
  exact inter_mem (continuous_re.continuousAt.preimage_mem_nhds hr)
    (continuous_im.continuousAt.preimage_mem_nhds hr)

lemma rect_zero {a : ℝ} (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (box a)) : rectIntegral f (-a) a a = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((-a : ℂ) - a * I) ((a : ℂ) + a * I)
  have hs : (Set.uIcc (((-a : ℂ) - a * I).re) (((a : ℂ) + a * I).re) ×ℂ
      Set.uIcc (((-a : ℂ) - a * I).im) (((a : ℂ) + a * I).im)) = box a := by
    simp [box, uIcc_of_le (show -a ≤ a by linarith)]
  rw [hs] at h
  simpa [rectIntegral] using h hf

/-- A simple pole on the square, proved by removing it with two divided
slopes and applying Cauchy-Goursat to the regular part. -/
theorem rect_simple_pole {a : ℝ} (ha : 0 < a) (f d : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hd : Differentiable ℂ d)
    (hd0 : d 0 = 0) (hd' : deriv d 0 ≠ 0)
    (hdne : ∀ z ∈ box a, z ≠ 0 → d z ≠ 0) :
    rectIntegral (fun z => f z / d z) (-a) a a =
      2 * Real.pi * I * (f 0 / deriv d 0) := by
  let D := dslope d 0
  have hDall : Differentiable ℂ D := differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (show Set.univ ∈ 𝓝 (0 : ℂ) from univ_mem)).mpr hd.differentiableOn)
  have hD : DifferentiableOn ℂ D (box a) := hDall.differentiableOn
  have hDn : ∀ z ∈ box a, D z ≠ 0 := by
    intro z hz
    by_cases h0 : z = 0
    · subst z
      simpa only [D, dslope_same] using hd'
    · simpa only [D, dslope_of_ne _ h0, slope, vsub_eq_sub, hd0, sub_zero, smul_eq_mul,
        mul_ne_zero_iff] using mul_ne_zero (inv_ne_zero h0) (hdne z hz h0)
  let F := fun z => f z / D z
  have hF : DifferentiableOn ℂ F (box a) := hf.differentiableOn.div hD hDn
  have hG : DifferentiableOn ℂ (dslope F 0) (box a) :=
    (Complex.differentiableOn_dslope (box_mem_nhds ha)).mpr hF
  have hsplit : rectIntegral (fun z => f z / d z) (-a) a a =
      rectIntegral (fun z => dslope F 0 z + (f 0 / deriv d 0) * z⁻¹) (-a) a a := by
    apply rect_congr_Gam (by linarith) ha.le
    intro z hz
    have hz0 : z ≠ 0 := Gam_ne (by simpa using ha) (by simpa using ha) (by simpa using ha) hz
    have hzb : z ∈ box a := by
      rcases hz with ⟨⟨h1,h2⟩, h3|h3⟩ | ⟨⟨h1,h2⟩, h3|h3⟩ <;>
        exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩
    have hdzn := hdne z hzb hz0
    simp only [dslope_of_ne _ hz0, slope, sub_zero, smul_eq_mul]
    change f z / d z = z⁻¹ * (f z / D z - f 0 / D 0) + (f 0 / deriv d 0) * z⁻¹
    have he : D z = z⁻¹ * d z := by simp only [D, dslope_of_ne _ hz0, slope, vsub_eq_sub, smul_eq_mul, hd0, sub_zero]
    have he0 : D 0 = deriv d 0 := dslope_same _ _
    rw [he, he0]
    field_simp
    ring
  have hcont : ∀ z ∈ Gam (-a) a a, ContinuousAt (dslope F 0) z := by
    intro z hz
    have hzb : z ∈ box a := by
      rcases hz with ⟨⟨h1,h2⟩, h3|h3⟩ | ⟨⟨h1,h2⟩, h3|h3⟩ <;>
        exact ⟨by constructor <;> linarith, by constructor <;> linarith⟩
    have hz0 : z ≠ 0 := Gam_ne (by simpa using ha) (by simpa using ha) (by simpa using ha) hz
    apply (continuousAt_dslope_of_ne hz0).mpr
    exact (hf z).continuousAt.div (hDall z).continuousAt (hDn z hzb)
  rw [hsplit]
  rw [rectIntegral_add (f := dslope F 0) (g := fun z => (f 0 / deriv d 0) * z⁻¹) (by linarith) ha.le hcont
    (fun z hz => continuousAt_const.mul (continuousAt_inv₀
      (Gam_ne (by simpa using ha) (by simpa using ha) (by simpa using ha) hz))),
    rect_zero ha.le _ hG, zero_add, rectIntegral_const_mul]
  have hi : rectIntegral (fun z : ℂ => z⁻¹) (-a) a a = 2 * Real.pi * I := by
    simpa only [sub_zero] using (rect_inv (w := 0) (by simpa using ha)
      (by simpa using ha) (by simpa using ha))
  rw [hi]
  ring

/-- The exponential denominator has only its simple zero at the origin
in the fixed free-background contour square. -/
lemma free_denominator_nonzero (L : ℝ) (hL : 0 < L) (z : ℂ)
    (hz : z ∈ box (HaarKernelFactorizationSym.omegaL L / 4)) (hz0 : z ≠ 0) :
    1 - ew L z ≠ 0 := by
  intro he
  have hex : exp (I * L * z) = 1 := (sub_eq_zero.mp he).symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hex
  have hω : 0 < HaarKernelFactorizationSym.omegaL L := by
    unfold HaarKernelFactorizationSym.omegaL
    positivity
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have heq : z = ((HaarKernelFactorizationSym.omegaL L * n : ℝ) : ℂ) := by
    apply mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hLc)
    calc
      (I * L) * z = (n : ℂ) * (2 * Real.pi * I) := hn
      _ = (I * L) * ((HaarKernelFactorizationSym.omegaL L * n : ℝ) : ℂ) := by
        unfold HaarKernelFactorizationSym.omegaL
        push_cast
        field_simp
  have hnr : |(n : ℝ)| ≤ 1 / 4 := by
    have hab : |z.re| ≤ HaarKernelFactorizationSym.omegaL L / 4 := abs_le.mpr hz.1
    rw [heq, ofReal_re, abs_mul, abs_of_pos hω] at hab
    nlinarith
  have hn0 : n = 0 := by
    have hnlt : |n| < (1 : ℤ) := by exact_mod_cast (lt_of_le_of_lt hnr (by norm_num : (1 : ℝ) / 4 < 1))
    rw [abs_lt] at hnlt
    omega
  apply hz0
  simp only [hn0, Int.cast_zero, mul_zero, ofReal_zero] at heq
  exact heq

/-- Residue of the free-background linear term, with its exact sign and
normalization. The numerator can be any entire scalar transfer function. -/
theorem free_linear_residue (L : ℝ) (hL : 0 < L) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    rectIntegral (fun z => f z / (1 - ew L z))
      (-(HaarKernelFactorizationSym.omegaL L / 4))
      (HaarKernelFactorizationSym.omegaL L / 4) (HaarKernelFactorizationSym.omegaL L / 4) =
        -(2 * Real.pi / L : ℂ) * f 0 := by
  have hω : 0 < HaarKernelFactorizationSym.omegaL L := by
    unfold HaarKernelFactorizationSym.omegaL
    positivity
  let d : ℂ → ℂ := fun z => 1 - ew L z
  have hd : Differentiable ℂ d := by unfold d ew; fun_prop
  have hd0 : d 0 = 0 := by simp [d, ew]
  have hder : deriv d 0 = -(I * L) := by
    have hh := ((((hasDerivAt_id (0 : ℂ)).const_mul (I * L)).cexp).const_sub 1).deriv
    simpa only [d, ew, id_eq, mul_zero, exp_zero, one_mul, mul_one] using hh
  have hdne : deriv d 0 ≠ 0 := by
    rw [hder]
    exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hL.ne'))
  rw [rect_simple_pole (by linarith : 0 < HaarKernelFactorizationSym.omegaL L / 4)
    f d hf hd hd0 hdne (fun z hz hz0 => free_denominator_nonzero L hL z hz hz0), hder]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp

/-- The residue formula for the actual transfer eigenvalue, at every grid
point (including removable root values). -/
theorem actual_linear_period (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    {N : ℕ} (hN : 0 < N) (m : BetheLabels.MArr N) (n : ℤ) :
    rectIntegral (fun w => HaarNonlinearTail.xEig L hκ hN n w m / (1 - ew L w))
      (-(HaarKernelFactorizationSym.omegaL L / 4))
      (HaarKernelFactorizationSym.omegaL L / 4) (HaarKernelFactorizationSym.omegaL L / 4) =
        -(2 * Real.pi / L : ℂ) *
          (NormalityBridge.eigen (L := L) κ hκ hN m (GridEigen.gridPt L n) - 2) := by
  have hf : Differentiable ℂ (fun w => HaarNonlinearTail.xEig L hκ hN n w m) := by
    unfold HaarNonlinearTail.xEig OffgridCommutator.zpt ew
    exact ((NormalityBridge.eigen_differentiable κ hκ hN m).comp (by fun_prop)).sub (by fun_prop)
  have h := free_linear_residue L (Fact.out : 0 < L)
    (fun w => HaarNonlinearTail.xEig L hκ hN n w m) hf
  simpa only [HaarNonlinearTail.xEig, OffgridCommutator.zpt_eq, add_zero, ew,
    mul_zero, exp_zero, GridEigen.gridPt, one_add_one_eq_two] using h

end QuantumNLS.HighAngleContour

-- Author audits: every own declaration and its generated/transitive constants.
#print axioms QuantumNLS.HighAngleContour.free_root_identity
#print axioms QuantumNLS.HighAngleContour.box
#print axioms QuantumNLS.HighAngleContour.box_mem_nhds
#print axioms QuantumNLS.HighAngleContour.rect_zero
#print axioms QuantumNLS.HighAngleContour.rect_simple_pole
#print axioms QuantumNLS.HighAngleContour.free_denominator_nonzero
#print axioms QuantumNLS.HighAngleContour.free_linear_residue
#print axioms QuantumNLS.HighAngleContour.actual_linear_period

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleContour." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
