import QuantumNLS.HighAngleContour
import QuantumNLS.HighAngleReconstruction
import QuantumNLS.LinearTailFinal

/-! Scalar binding of the reconstructed leading multiplier to the actual
linear generator and the accepted nonlinear remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Complex Set Filter Topology
open scoped BigOperators
namespace QuantumNLS.HighAngleSpectralBridge
open HighAngleContour HighAngleReconstruction HaarSummableReconstruction
open PeriodReconstructionCore LabelExactPeriod HaarFreeTaylor HaarNonlinearTail
open HaarNonlinearAbstract PeriodReconstruction PeriodTwoTerm

lemma rect_translate (c a h : ℝ) (f : ℂ → ℂ) :
    rectIntegral (fun z => f ((c : ℂ) + z)) (-a) a h = rectIntegral f (c - a) (c + a) h := by
  have hh (y : ℝ) :
      (∫ x in (-a)..a, f ((c : ℂ) + ((x : ℂ) + y * I))) =
        ∫ x in (c - a)..(c + a), f ((x : ℂ) + y * I) := by
    convert intervalIntegral.integral_comp_add_left (fun x : ℝ => f ((x : ℂ) + y * I)) c
      (a := -a) (b := a) using 1
    · congr 1
      funext x
      congr 1
      push_cast
      ring
  have hvp : (fun y : ℝ => f ((c : ℂ) + ((a : ℂ) + y * I))) =
      (fun y : ℝ => f (((c + a : ℝ) : ℂ) + y * I)) := by
    funext y
    congr 1
    push_cast
    ring
  have hvm : (fun y : ℝ => f ((c : ℂ) + (((-a : ℝ) : ℂ) + y * I))) =
      (fun y : ℝ => f (((c - a : ℝ) : ℂ) + y * I)) := by
    funext y
    congr 1
    push_cast
    ring
  unfold rectIntegral
  rw [hh (-h), hh h, hvp, hvm]

lemma eigen_eq_sNf_rev (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    {N : ℕ} (hN : 0 < N) (m : BetheLabels.MArr N) (z : ℂ)
    (hz : ∀ j, z ≠ (roots L κ m j : ℂ)) :
    NormalityBridge.eigen (L := L) κ hκ hN m z = sNf L (κ / N) (roots L κ m) z := by
  have hz' : ∀ j, z ≠ (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j : ℂ) := by
    intro j
    simpa only [roots, Function.comp_apply, Fin.rev_rev] using hz (Fin.rev j)
  unfold NormalityBridge.eigen
  rw [(BetheSpectralContinuity.basis_eigenvalue L (NormalityBridge.cpos hκ hN)
    (NormalityBridge.label m).property).2.1 z hz']
  unfold TransferSeparation.sFun sNf ANf roots
  have he (c : ℂ) :
      (∏ j, (1 + I * c / (z - (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j : ℂ)))) =
        ∏ j, (1 + I * c / (z - (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) (Fin.rev j) : ℂ))) :=
    (Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)).symm
  simp only [Function.comp_apply, ef, ofReal_neg, mul_neg, neg_div]
  rw [he ((κ / N : ℝ) : ℂ), show (∏ j, (1 - I * ((κ / N : ℝ) : ℂ) /
      (z - (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j : ℂ)))) =
    ∏ j, (1 - I * ((κ / N : ℝ) : ℂ) /
      (z - (BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) (Fin.rev j) : ℂ))) by
        exact (Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)).symm]
  simp only [sub_eq_add_neg]

lemma FW_actual (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    {N : ℕ} (hN : 0 < N) (m : BetheLabels.MArr N) (n : ℤ) (w : ℂ)
    (hz : ∀ j, OffgridCommutator.zpt L w n ≠ (roots L κ m j : ℂ)) :
    FW L w (xEig L hκ hN n w m) =
      log (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n)) := by
  unfold FW xEig
  rw [eigen_eq_sNf_rev L hκ hN m _ hz]
  rw [← free_root_identity L κ (κ / N) (roots L κ m) _ w (HaarSpectralTail.ew_zpt w n)]

lemma rect_sum {ι : Type*} (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (s : Finset ι) (f : ι → ℂ → ℂ)
    (hc : ∀ n ∈ s, ∀ z ∈ Gam (-a) a h, ContinuousAt (f n) z) :
    rectIntegral (fun z => ∑ n ∈ s, f n z) (-a) a h =
      ∑ n ∈ s, rectIntegral (f n) (-a) a h :=
  rectIntegral_sum s (fun n hn x hx => hc n hn _ (bot_mem (by linarith) hx))
    (fun n hn x hx => hc n hn _ (top_mem (by linarith) hx))
    (fun n hn y hy => hc n hn _ (right_mem hh hy))
    (fun n hn y hy => hc n hn _ (left_mem hh hy))

lemma rect_sub (a : ℝ) (ha : 0 ≤ a) (f g : ℂ → ℂ)
    (hf : ∀ z ∈ Gam (-a) a a, ContinuousAt f z)
    (hg : ∀ z ∈ Gam (-a) a a, ContinuousAt g z) :
    rectIntegral (fun z => f z - g z) (-a) a a =
      rectIntegral f (-a) a a - rectIntegral g (-a) a a := by
  have he : (fun z => f z - g z) = (fun z => f z + (-1 : ℂ) * g z) := by
    funext z; ring
  rw [he, rectIntegral_add (f := f) (g := fun z => (-1 : ℂ) * g z) (by linarith) ha hf
    (fun z hz => continuousAt_const.mul (hg z hz)), rectIntegral_const_mul]
  ring

lemma centered_boundary (L : ℝ) [Fact (0 < L)] (n : ℤ) (f : ℂ → ℂ) :
    rectIntegral (fun w => f (OffgridCommutator.zpt L w n))
      (-(HaarKernelFactorizationSym.omegaL L / 4)) (HaarKernelFactorizationSym.omegaL L / 4)
      (HaarKernelFactorizationSym.omegaL L / 4) = HighContours.boundaryIntegral L n f := by
  simp_rw [OffgridCommutator.zpt_eq]
  rw [rect_translate]
  simpa only [HaarSpectralTail.omegaL_eq_om, lo, hi, ht] using (rect_eq_boundary L n f)

/-- The exact scalar cutoff identity, before the final operator assembly.
The only analytic hypotheses concern the contour's avoiding roots and
continuity of the literal logarithm; no operator identity is assumed. -/
theorem remainder_identity (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)
    {N : ℕ} (hN : 0 < N) (E : ℝ) (m : BetheLabels.MArr N)
    (hm : m ∈ HaarSpectralTail.adm L κ N E) (a : Finset ℤ) (t : ℤ → ℝ)
    (hne : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ∀ j, OffgridCommutator.zpt L w n ≠ (roots L κ m j : ℂ))
    (hc : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ContinuousAt (fun w => log (aNf L κ (κ / N) G0 (roots L κ m)
        (OffgridCommutator.zpt L w n))) w) :
    (rEig L hκ hN E a t m).re = leadingEigen L κ a t m -
      (N : ℝ) * (LinearTailCommute.genEigen L κ hκ N hN a t m).re := by
  let ω := HaarKernelFactorizationSym.omegaL L
  have hω : 0 < ω := HaarSpectralTail.omegaL_pos
  let f := fun n w => log (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n))
  let g := fun n w => xEig L hκ hN n w m / (1 - ew L w)
  have hfc : ∀ n ∈ a, ∀ w ∈ Gam (- (ω / 4)) (ω / 4) (ω / 4), ContinuousAt (f n) w := by
    intro n hn w hw
    exact hc n hn w (by rwa [HaarSpectralTail.Gam0_eq] at hw)
  have hgc : ∀ n ∈ a, ∀ w ∈ Gam (- (ω / 4)) (ω / 4) (ω / 4), ContinuousAt (g n) w := by
    intro n _ w hw
    have hw' : w ∈ OffgridBessel.Gamma0 L := by rwa [HaarSpectralTail.Gam0_eq] at hw
    have hx : Differentiable ℂ (fun w => xEig L hκ hN n w m) := by
      unfold xEig OffgridCommutator.zpt ew
      exact ((NormalityBridge.eigen_differentiable κ hκ hN m).comp (by fun_prop)).sub (by fun_prop)
    exact (hx w).continuousAt.div (by unfold ew; fun_prop) (norm_pos_iff.mp
      (lt_of_lt_of_le etaL_pos (one_sub_ew_lower hw')))
  have hG : ∀ n ∈ a, ∀ w ∈ Gam (- (ω / 4)) (ω / 4) (ω / 4),
      Gfun L w (xEig L hκ hN n w m) = f n w - g n w := by
    intro n hn w hw
    have hw' : w ∈ OffgridBessel.Gamma0 L := by rwa [HaarSpectralTail.Gam0_eq] at hw
    unfold Gfun f g
    rw [FW_actual L hκ hN m n w (hne n hn w hw')]
  have hperiod (n : ℤ) (hn : n ∈ a) :
      rectIntegral (fun w => Gfun L w (xEig L hκ hN n w m))
        (- (ω / 4)) (ω / 4) (ω / 4) =
      HighContours.boundaryIntegral L n (fun z => log (aNf L κ (κ / N) G0 (roots L κ m) z)) -
        (-(2 * Real.pi / L : ℂ) * (NormalityBridge.eigen (L := L) κ hκ hN m (GridEigen.gridPt L n) - 2)) := by
    rw [rect_congr_Gam (by linarith) (by linarith) (hG n hn),
      rect_sub (ω / 4) (by linarith) (f n) (g n) (hfc n hn) (hgc n hn)]
    rw [show rectIntegral (f n) (- (ω / 4)) (ω / 4) (ω / 4) =
      HighContours.boundaryIntegral L n (fun z => log (aNf L κ (κ / N) G0 (roots L κ m) z)) from
        (by simpa only [f, ω] using (centered_boundary L n
          (fun z => log (aNf L κ (κ / N) G0 (roots L κ m) z)))), show rectIntegral (g n) (- (ω / 4)) (ω / 4) (ω / 4) = _ from
          actual_linear_period L hκ hN m n]
  have hcontG : ∀ n ∈ a, ∀ w ∈ Gam (- (ω / 4)) (ω / 4) (ω / 4),
      ContinuousAt (fun w => Gfun L w (xEig L hκ hN n w m)) w := by
    intro n hn w hw
    have hw' : w ∈ OffgridBessel.Gamma0 L := by rwa [HaarSpectralTail.Gam0_eq] at hw
    have hlocal : (fun v => FW L v (xEig L hκ hN n v m)) =ᶠ[𝓝 w] f n := by
      have hh : ∀ᶠ v in 𝓝 w, ∀ j : Fin N,
          OffgridCommutator.zpt L v n ≠ (roots L κ m j : ℂ) := by
        apply Filter.eventually_all.mpr
        intro j
        have hzcont : ContinuousAt (fun v => OffgridCommutator.zpt L v n) w := by
          unfold OffgridCommutator.zpt
          fun_prop
        exact hzcont.eventually_ne (hne n hn w hw' j)
      filter_upwards [hh] with v hv
      exact FW_actual L hκ hN m n v hv
    unfold Gfun
    exact ((hfc n hn w hw).congr_of_eventuallyEq hlocal).sub (hgc n hn w hw)
  unfold rEig
  rw [ite_eq_left hm]
  simp only [ofReal_re]
  rw [rect_sum (ω / 4) (ω / 4) (by linarith) (by linarith) a
    (fun n w => (t n : ℂ) * Gfun L w (xEig L hκ hN n w m))
    (fun n hn w hw => continuousAt_const.mul (hcontG n hn w hw))]
  simp_rw [rectIntegral_const_mul]
  have hsum : (∑ n ∈ a, (t n : ℂ) * rectIntegral
      (fun w => Gfun L w (xEig L hκ hN n w m)) (-(ω / 4)) (ω / 4) (ω / 4)) =
      ∑ n ∈ a, (t n : ℂ) *
        (HighContours.boundaryIntegral L n (fun z => log (aNf L κ (κ / N) G0 (roots L κ m) z)) -
          (-(2 * Real.pi / L : ℂ) * (NormalityBridge.eigen (L := L) κ hκ hN m (GridEigen.gridPt L n) - 2))) := by
    exact Finset.sum_congr rfl fun n hn => congrArg (fun z => (t n : ℂ) * z) (hperiod n hn)
  rw [hsum]
  have hconst : -(2 * Real.pi / L : ℂ) = (((-(2 * Real.pi / L) : ℝ)) : ℂ) := by push_cast; rfl
  rw [hconst]
  unfold leadingEigen LinearTailCommute.genEigen C0
  simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.sub_re, Complex.re_ofNat]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  field_simp
  ring

/-- The actual uniform scalar error after combining the accepted summed
reconstruction with the exact linear/nonlinear contour decomposition.
All contour hypotheses of remainder_identity are discharged here. -/
theorem actual_combined_error (L : ℝ) [Fact (0 < L)] {κ E : ℝ}
    (hκ : 0 < κ) (hE : 0 < E) :
    ∃ NE : ℕ, ∃ RE C : ℝ, 0 < NE ∧ 2 ≤ RE ∧ 0 ≤ C ∧
      ∀ (N : ℕ) (hN : 0 < N), NE ≤ N →
        ∀ m : BetheLabels.MArr N, m ∈ HaarSpectralTail.adm L κ N E →
          ∀ R : ℝ, RE ≤ R → ∀ a : Finset ℤ, (∀ n ∈ a, R < |(n : ℝ)|) →
            ∀ t : ℤ → ℝ, (∀ n, |t n| ≤ 1) →
              |countEigen a t m - (N : ℝ) * (LinearTailCommute.genEigen L κ hκ N hN a t m).re -
                (rEig L hκ hN E a t m).re| ≤ C / R := by
  have hL : 0 < L := Fact.out
  obtain ⟨N1, R1, C1, hN1, hR1, _, hmain⟩ := haar_summable_reconstruction hL hκ hE
  obtain ⟨N2, R2, C2, hN2, hR2, hC2, hfinite⟩ := finite_reconstruction L hκ hE
  refine ⟨max N1 N2, max R1 R2, C2, lt_of_lt_of_le hN1 (le_max_left _ _),
    hR1.trans (le_max_left _ _), hC2, ?_⟩
  intro N hN hNN m hm R hR a ha t ht
  have hNR1 : N1 ≤ N := (le_max_left _ _).trans hNN
  have hNR2 : N2 ≤ N := (le_max_right _ _).trans hNN
  have hRR1 : R1 ≤ R := (le_max_left _ _).trans hR
  have hRR2 : R2 ≤ R := (le_max_right _ _).trans hR
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hact := HaarSpectralTail.sourceRoots_actual hL (div_pos hκ hNr)
    (NormalityBridge.label m).property
  have hen : (N : ℝ)⁻¹ * ∑ j, roots L κ m j ^ 2 ≤ E := by
    have he : ∑ j, roots L κ m j ^ 2 = EnergyProjection.energyEig L κ N (NormalityBridge.label m) := by
      unfold roots EnergyProjection.energyEig
      exact HaarSpectralTail.sum_rev
        (fun j => BetheSmooth.sourceRoots L (NormalityBridge.label m).val (κ / N) j ^ 2)
    rw [he, inv_mul_le_iff₀ hNr]
    exact hm
  obtain ⟨hpt, -, -, -⟩ := hmain N ((NormalityBridge.label m).val ∘ Fin.rev)
    (roots L κ m) hNR1 hact hen
  have hpoint (n : ℤ) (hn : n ∈ a) (w : ℂ) (hw : w ∈ OffgridBessel.Gamma0 L) :=
    hpt n (hRR1.trans_lt (ha n hn)) (OffgridCommutator.zpt L w n)
      (Gam_subset_Γ hL n (HaarSpectralTail.zpt_mem hw n))
  have hne : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ∀ j, OffgridCommutator.zpt L w n ≠ (roots L κ m j : ℂ) := by
    intro n hn w hw j
    apply sub_ne_zero.mp
    apply norm_pos_iff.mp
    exact lt_trans (by positivity : (0 : ℝ) < 2 * |κ / (N : ℝ)|) ((hpoint n hn w hw).1 j)
  have hc : ∀ n ∈ a, ∀ w ∈ OffgridBessel.Gamma0 L,
      ContinuousAt (fun w => log (aNf L κ (κ / N) G0 (roots L κ m)
        (OffgridCommutator.zpt L w n))) w := by
    intro n hn w hw
    obtain ⟨-, -, hnorm, hdiff, -, -, -⟩ := hpoint n hn w hw
    have hre := Complex.abs_re_le_norm
      (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n) - 1)
    simp only [sub_re, one_re] at hre
    have hp : 0 < (aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n)).re := by
      have hneg := neg_abs_le
        ((aNf L κ (κ / N) G0 (roots L κ m) (OffgridCommutator.zpt L w n)).re - 1)
      linarith
    have hzcont : ContinuousAt (fun v => OffgridCommutator.zpt L v n) w := by
      unfold OffgridCommutator.zpt
      fun_prop
    have hinner : ContinuousAt (fun v : ℂ => aNf L κ (κ / N) G0 (roots L κ m)
        (OffgridCommutator.zpt L v n)) w :=
      ContinuousAt.comp (f := fun v : ℂ => OffgridCommutator.zpt L v n)
        (g := aNf L κ (κ / N) G0 (roots L κ m)) (x := w) hdiff.continuousAt hzcont
    exact ContinuousAt.comp (f := fun v : ℂ => aNf L κ (κ / N) G0 (roots L κ m)
      (OffgridCommutator.zpt L v n)) (g := log) (x := w) (continuousAt_clog (Or.inl hp)) hinner
  have heq := remainder_identity L hκ hN E m hm a t hne hc
  have hb := hfinite N hNR2 m hm R hRR2 a ha t ht
  convert hb using 1
  congr 1
  rw [heq]
  ring

end QuantumNLS.HighAngleSpectralBridge

-- Author audits: every own declaration and its generated/transitive constants.
#print axioms QuantumNLS.HighAngleSpectralBridge.rect_translate
#print axioms QuantumNLS.HighAngleSpectralBridge.eigen_eq_sNf_rev
#print axioms QuantumNLS.HighAngleSpectralBridge.FW_actual
#print axioms QuantumNLS.HighAngleSpectralBridge.rect_sum
#print axioms QuantumNLS.HighAngleSpectralBridge.rect_sub
#print axioms QuantumNLS.HighAngleSpectralBridge.centered_boundary
#print axioms QuantumNLS.HighAngleSpectralBridge.remainder_identity
#print axioms QuantumNLS.HighAngleSpectralBridge.actual_combined_error

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.HighAngleSpectralBridge." then
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
