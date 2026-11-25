import QuantumNLS.Prop018Operators
import QuantumNLS.Prop018SequenceScalar

/-! Window-contour eigenvalue identification and the actual event-projected
operator inequalities of PROP-018. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop018SequenceWindowOperators
open TensorCarrier PhysicalTensor KernelDefinition BetheLabels BetheCoefficientTransform
open HaarSpectralTail HaarNonlinearAbstract Prop018Operators Prop018ChargeCutoff
open Prop018SequencePhase Prop018Period PeriodReconstructionCore LabelExactPeriod
open PeriodReconstruction MPContour Prop020Contour

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

lemma root_avoid {a h R : ℝ} (ha : R < a) (hh : 0 < h)
    (m : MArr N) (hm : ∀ j, |Prop017Quantum.qAct L κ N m j| ≤ R)
    {z : ℂ} (hz : z ∈ Gam (-a) a h) (j : Fin N) : z ≠ (Prop017Quantum.qAct L κ N m j : ℂ) := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [ofReal_re, ofReal_im] at hre him
  have hj := abs_le.mp (hm j)
  rcases hz with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> linarith

lemma eigen_deriv_eq (m : MArr N) (z : ℂ)
    (hne : ∀ j, z ≠ (Prop017Quantum.qAct L κ N m j : ℂ)) :
    Prop018Operators.lam (L := L) hκ hN m z = sNf L (κ / N) (Prop017Quantum.qAct L κ N m) z ∧
    Prop018Operators.dlam (L := L) hκ hN m z = deriv (sNf L (κ / N) (Prop017Quantum.qAct L κ N m)) z := by
  have hh : ∀ᶠ w in 𝓝 z, ∀ j, w ≠ (Prop017Quantum.qAct L κ N m j : ℂ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact continuous_id.continuousAt.eventually_ne (hne j)
  have he : (Prop018Operators.lam (L := L) hκ hN m) =ᶠ[𝓝 z] sNf L (κ / N) (Prop017Quantum.qAct L κ N m) := by
    filter_upwards [hh] with w hw
    exact Prop019Deviation.eigen_eq_sNf hκ hN m w hw
  exact ⟨he.self_of_nhds, he.deriv_eq⟩

def WindowConclusion (a : ℕ → ℝ) (h : ℝ) (E : Set (MArr N))
    (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ) (p : ℕ → ℝ) (d : ℕ) (δ0 δ1 c : ℝ) : Prop :=
    ∃ P C0 C1 Q : HN L N →L[ℂ] HN L N,
      (∀ m, P (bas L hκ hN m) = eventMask E m • bas L hκ hN m) ∧
      P * P = P ∧ ContinuousLinearMap.adjoint P = P ∧
      C0 = MPOps.C0op (nu 6)
        (fun τ => S (L := L) (κ := κ) (N := N) (zθ (rectPieces (a N) h (poly p d) (continuous_poly p d)) τ))
        (uθ κ (rectPieces (a N) h (poly p d) (continuous_poly p d)))
        (fun τ => f (zθ (rectPieces (a N) h (poly p d) (continuous_poly p d)) τ)) ∧
      C1Realization (L := L) hκ hN (nu 6)
        (zθ (rectPieces (a N) h (poly p d) (continuous_poly p d)))
        (uθ κ (rectPieces (a N) h (poly p d) (continuous_poly p d))) qt C1 ∧
      IsSelfAdjoint C0 ∧ IsSelfAdjoint C1 ∧ Commute C0 C1 ∧ Commute P C0 ∧ Commute P C1 ∧
      CommutesAllCharges (bas L hκ hN) (κ / N) C0 ∧ CommutesAllCharges (bas L hκ hN) (κ / N) C1 ∧
      (∀ m ∈ E, C0 (bas L hκ hN m) = (C0ev L κ f a h p d N m : ℂ) • bas L hκ hN m ∧
        C1 (bas L hκ hN m) = (C1ev L κ qt a h p d N m : ℂ) • bas L hκ hN m) ∧
      (∀ ψ : HN L N, ∃ hq : P ψ ∈ (BetheSpectralCharges.multiplier (bas L hκ hN)
        (fun m => ∑ r ∈ Finset.range (d + 1), p r * BetheSpectralCharges.eigenvalue L N (κ / N) r m)).domain,
          BetheSpectralCharges.multiplier (bas L hκ hN) _ ⟨P ψ, hq⟩ = Q ψ) ∧
      ‖Q - (((N : ℂ) • C0 + C1) * P)‖ ≤ δ0 ∧
      ‖(C1 - (c : ℂ) • (1 : HN L N →L[ℂ] HN L N)) * P‖ ≤ δ1 ∧
      ∃ hd : ∀ r (ψ : HN L N), P ψ ∈ (BetheSpectralCharges.charge (bas L hκ hN) (κ / N) r).domain,
        ∀ ψ : HN L N, Q ψ = ∑ r ∈ Finset.range (d + 1), (p r : ℂ) •
          BetheSpectralCharges.charge (bas L hκ hN) (κ / N) r ⟨P ψ, hd r ψ⟩

/-- On any event contained in a root window strictly inside the vertical
cuts, construct the actual C0,C1, identify both eigenvalues, and lift both
uniform scalar inequalities to bounded operator norms with charge domains. -/
theorem event_operators (a : ℕ → ℝ) (h R : ℝ) (hh : 0 < h) (hR : 0 ≤ R)
    (ha : R < a N) (E : Set (MArr N))
    (hroot : ∀ m ∈ E, ∀ j, |Prop017Quantum.qAct L κ N m j| ≤ R)
    (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ)
    (hf : ∀ z ∈ Gam (-(a N)) (a N) h,
      ∀ w, ContinuousAt (fun p : ℂ × ℂ => f p.1 p.2) (z, w))
    (hqt : ∀ z ∈ Gam (-(a N)) (a N) h,
      ∀ w v, ContinuousAt (fun p : ℂ × (ℂ × ℂ) => qt p.1 p.2.1 p.2.2) (z, (w, v)))
    (p : ℕ → ℝ) (d : ℕ) {δ0 δ1 c : ℝ} (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (he0 : ∀ m ∈ E, |(∑ r ∈ Finset.range (d + 1), p r * BetheSpectralCharges.eigenvalue L N (κ / N) r m)
      - N * C0ev L κ f a h p d N m - C1ev L κ qt a h p d N m| ≤ δ0)
    (he1 : ∀ m ∈ E, |C1ev L κ qt a h p d N m - c| ≤ δ1) :
    WindowConclusion (L := L) hκ hN a h E f qt p d δ0 δ1 c := by
  classical
  unfold WindowConclusion
  let A := a N
  have ha0 : 0 < A := lt_of_le_of_lt hR ha
  let Pcs := rectPieces A h (poly p d) (continuous_poly p d)
  let z := zθ Pcs
  let u := uθ κ Pcs
  have hZ : Continuous z := continuous_zθ Pcs
  have hU : Continuous u := continuous_uθ κ Pcs
  have hmem (τ : ThetaSpace 6) : z τ ∈ Gam (-A) A h :=
    rect_mem_Gam ha0.le hh.le (poly p d) (continuous_poly p d) τ.1 τ.2.2
  have hfp : Continuous (fun q : ThetaSpace 6 × ℂ => f (z q.1) q.2) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ContinuousAt.comp (f := fun q : ThetaSpace 6 × ℂ => (z q.1, q.2))
      (g := fun p : ℂ × ℂ => f p.1 p.2) (x := q) (hf _ (hmem q.1) q.2)
      ((hZ.continuousAt.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
  have hqp : Continuous (fun q : ThetaSpace 6 × (ℂ × ℂ) => qt (z q.1) q.2.1 q.2.2) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact ContinuousAt.comp (f := fun q : ThetaSpace 6 × (ℂ × ℂ) => (z q.1, q.2))
      (g := fun p : ℂ × (ℂ × ℂ) => qt p.1 p.2.1 p.2.2) (x := q) (hqt _ (hmem q.1) q.2.1 q.2.2)
      ((hZ.continuousAt.comp continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
  obtain ⟨K, hK, x, Φ, C1, hx, hΦ, hcoords, hC1def, hC0sa, hC1sa, hcomm, hC0eig, hC1eig⟩ :=
    construct (L := L) hκ hN (nu 6) z hZ u hU f qt hfp hqp
  let C0 := MPOps.C0op (nu 6) (fun τ => S (L := L) (κ := κ) (N := N) (z τ)) u (fun τ => f (z τ))
  let c0 := fun m => ∫ τ, (u τ * f (z τ) (Prop018Operators.lam (L := L) hκ hN m (z τ))).re ∂(nu 6)
  let c1 := fun m => (∫ τ, ((-I * κ) * u τ) * qt (z τ) (Prop018Operators.lam (L := L) hκ hN m (z τ))
    (Prop018Operators.dlam (L := L) hκ hN m (z τ)) ∂(nu 6)).re
  have hne (m : MArr N) (hm : m ∈ E) (w : ℂ) (hw : w ∈ Gam (-A) A h) :=
    root_avoid (L := L) (κ := κ) ha hh m (hroot m hm) hw
  have h0 (m : MArr N) (hm : m ∈ E) : c0 m = C0ev L κ f a h p d N m := by
    let F : ℂ → ℂ := fun w => f w (Prop018Operators.lam (L := L) hκ hN m w)
    have hF : ∀ w ∈ Gam (-A) A h, ContinuousAt F w := fun w hw =>
      ContinuousAt.comp (f := fun w : ℂ => (w, Prop018Operators.lam (L := L) hκ hN m w))
        (g := fun p : ℂ × ℂ => f p.1 p.2) (x := w) (hf w hw _)
        (continuousAt_id.prodMk (NormalityBridge.eigen_differentiable (L := L) κ hκ hN m w).continuousAt)
    have hFc : Continuous (fun τ => F (z τ)) := continuous_iff_continuousAt.mpr
      (fun τ => (hF _ (hmem τ)).comp hZ.continuousAt)
    have hi : Integrable (fun τ => u τ * F (z τ)) (nu 6) :=
      (hU.mul hFc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have he := theta_integral_rect ha0 hh κ (poly p d) (continuous_poly p d) F hF
    have heq : rectIntegral (fun w => poly p d w * F w) (-A) A h =
        rectIntegral (fun w => poly p d w * f w (sNf L (κ / N) (Prop017Quantum.qAct L κ N m) w)) (-A) A h :=
      rect_congr_Gam (by linarith) hh.le (fun w hw => by dsimp only [F]; rw [(eigen_deriv_eq (L := L) hκ hN m w (hne m hm w hw)).1])
    have hre : (∫ τ, (u τ * F (z τ)).re ∂(nu 6)) = (∫ τ, u τ * F (z τ) ∂(nu 6)).re :=
      Complex.reCLM.integral_comp_comm hi
    change (∫ τ, (u τ * F (z τ)).re ∂(nu 6)) = _
    rw [hre, he, heq]
    simp only [C0ev, A, neg_mul, Complex.mul_re, ofReal_re, ofReal_im, neg_re, zero_mul, sub_zero, one_div]
  have h1 (m : MArr N) (hm : m ∈ E) : c1 m = C1ev L κ qt a h p d N m := by
    let F : ℂ → ℂ := fun w => qt w (Prop018Operators.lam (L := L) hκ hN m w) (Prop018Operators.dlam (L := L) hκ hN m w)
    have hF : ∀ w ∈ Gam (-A) A h, ContinuousAt F w := fun w hw =>
      ContinuousAt.comp (f := fun w : ℂ => (w, (Prop018Operators.lam (L := L) hκ hN m w,
          Prop018Operators.dlam (L := L) hκ hN m w)))
        (g := fun p : ℂ × (ℂ × ℂ) => qt p.1 p.2.1 p.2.2) (x := w) (hqt w hw _ _)
        (continuousAt_id.prodMk
        ((NormalityBridge.eigen_differentiable (L := L) κ hκ hN m w).continuousAt.prodMk
          (((NormalityBridge.eigen_differentiable (L := L) κ hκ hN m).contDiff (n := 1)).continuous_deriv_one.continuousAt)))
    have he := theta_integral_rect ha0 hh κ (poly p d) (continuous_poly p d) F hF
    have heq : rectIntegral (fun w => poly p d w * F w) (-A) A h =
        rectIntegral (fun w => poly p d w * qt w (sNf L (κ / N) (Prop017Quantum.qAct L κ N m) w)
          (deriv (sNf L (κ / N) (Prop017Quantum.qAct L κ N m)) w)) (-A) A h :=
      rect_congr_Gam (by linarith) hh.le (fun w hw => by
        dsimp only [F]
        rw [(eigen_deriv_eq (L := L) hκ hN m w (hne m hm w hw)).1,
          (eigen_deriv_eq (L := L) hκ hN m w (hne m hm w hw)).2])
    dsimp only [c1]
    simp_rw [show ∀ τ, ((-I * κ) * u τ) * qt (z τ) (Prop018Operators.lam (L := L) hκ hN m (z τ)) (Prop018Operators.dlam (L := L) hκ hN m (z τ)) =
      (-I * κ) * (u τ * F (z τ)) from fun _ => by dsimp [F]; ring]
    rw [integral_const_mul, he, heq]
    have hc : (-I * (κ : ℂ)) * -(((2 * Real.pi * κ)⁻¹ : ℝ) : ℂ) = I / (2 * Real.pi) := by
      have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    rw [← mul_assoc, hc]
    rfl
  obtain ⟨P, hP, -⟩ := HilbertDiagOp.diag_exists (bas L hκ hN) (eventMask E) 1
    (fun m => by unfold eventMask; split_ifs <;> norm_num) zero_le_one
  have hPb := (show IsDiagC (bas L hκ hN) P _ from hP).apply_basis
  have hPP : P * P = P := by
    apply TransferNormality.ext_of_hilbertBasis (bas L hκ hN)
    intro m
    simp only [mul_ap, hPb, map_smul, smul_smul]
    by_cases hm : m ∈ E <;> simp [eventMask, hm]
  have hPsa : ContinuousLinearMap.adjoint P = P := by
    apply TransferNormality.ext_of_hilbertBasis (bas L hκ hN)
    intro m
    rw [TransferNormality.adjoint_diag _ _ _ hPb m, hPb]
    congr 1
    by_cases hm : m ∈ E <;> simp [eventMask, hm]
  obtain ⟨Q, hdom, hphase, hscalar⟩ := operator_bounds (bas L hκ hN) E P C0 C1 hPb
    (fun m => ∑ r ∈ Finset.range (d + 1), p r * BetheSpectralCharges.eigenvalue L N (κ / N) r m)
    c0 c1 hC0eig hC1eig hδ0 hδ1
    (fun m hm => by rw [h0 m hm, h1 m hm]; exact he0 m hm)
    (fun m hm => by rw [h1 m hm]; exact he1 m hm)
  refine ⟨P, C0, C1, Q, hPb, hPP, hPsa, rfl, ?_, hC0sa, hC1sa, hcomm,
    HaarNonlinearTail.IsDiagC.commute (diagC_of_apply hPb) (diagC_of_apply hC0eig),
    HaarNonlinearTail.IsDiagC.commute (diagC_of_apply hPb) (diagC_of_apply hC1eig),
    commutes_all_charges (bas L hκ hN) (κ / N) C0 _ hC0eig,
    commutes_all_charges (bas L hκ hN) (κ / N) C1 _ hC1eig,
    ?_, hdom, hphase, hscalar, ?_⟩
  · have : CompactSpace K := hK
    let g : ThetaSpace 6 → C(K, ℂ) := fun τ =>
      ⟨fun y => ((-I * κ) * u τ) * qt (z τ) y.val.1 y.val.2,
        continuous_const.mul ((hqp.comp (continuous_const.prodMk continuous_id)).comp continuous_subtype_val)⟩
    exact ⟨K, hK, x, Φ, g, hx, hΦ, hcoords, fun _ _ => rfl, hC1def⟩
  · intro m hm
    constructor
    · rw [hC0eig]
      change (c0 m : ℂ) • bas L hκ hN m = _
      rw [h0 m hm]
    · rw [hC1eig]
      change (c1 m : ℂ) • bas L hκ hN m = _
      rw [h1 m hm]
  · let hd := all_charge_domains hκ hN E P hPb hR hroot
    refine ⟨hd, fun ψ => ?_⟩
    obtain ⟨hq, heq⟩ := hdom ψ
    rw [← heq]
    exact sum_charge_actions (bas L hκ hN) (κ / N) p d (P ψ) (fun r => hd r ψ) hq

end QuantumNLS.Prop018SequenceWindowOperators

#print axioms QuantumNLS.Prop018SequenceWindowOperators.root_avoid
#print axioms QuantumNLS.Prop018SequenceWindowOperators.eigen_deriv_eq
#print axioms QuantumNLS.Prop018SequenceWindowOperators.WindowConclusion
#print axioms QuantumNLS.Prop018SequenceWindowOperators.event_operators

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018SequenceWindowOperators." then
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
