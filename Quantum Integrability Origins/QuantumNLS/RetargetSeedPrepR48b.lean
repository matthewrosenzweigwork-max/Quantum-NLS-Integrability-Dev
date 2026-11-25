import QuantumNLS.RetargetCompactR48b
import QuantumNLS.R52CFMain
import QuantumNLS.HighAngleEvolutionBridge

/-! Finite-angle cutoffs for the actual chart and the actual Bethe count dynamics. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology UniformSpace Complex
open scoped BigOperators ENNReal Uniformity

namespace QuantumNLS.RetargetAnglesR48b
open PhysicalTensor CountRotations DynSeedInputR47b HighAngleRotations
open BetheCoefficientTransform BetheLabels ProductTorusGenerator
open scoped Pointwise
attribute [local instance] InnerProductSpace.complexToReal

variable {L κ : ℝ} [Fact (0 < L)]

/-- Symmetric label head ([-J,J]). -/
def labels (J : ℕ) : Finset ℤ := Finset.Icc (-(J : ℤ)) J

theorem mem_labels (J : ℕ) (a : ℤ) : a ∈ labels J ↔ |a| ≤ (J : ℤ) := by
  rw [labels, Finset.mem_Icc, abs_le]

theorem eventually_mem_labels (a : ℤ) : ∀ᶠ J in atTop, a ∈ labels J := by
  filter_upwards [eventually_ge_atTop a.natAbs] with J hJ
  apply (mem_labels J a).2
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hJ

/-- The action used by the accepted finite propagation statement, expressed
using the same chosen chart as the frozen seed symbols. -/
theorem classical_time (hκ : 0 < κ) (t : Linf) (u : L2T L) :
    RF535Final.Tθ (L := L) hκ t u = physicalAngle hκ (fun a => Circle.exp (t a)) u := by
  let C := Def021ChartR41b.chart L κ hκ
  let loc := Def021ChartR41b.localChart L
  have hg := (RF535Final.global_actual_chart L).2 loc.d loc.CL loc.Φ loc.Ψ
    loc.positive loc.nonnegative loc.spec κ hκ
  obtain ⟨Y, Fl, Φ, Ψ, -, -, -, -, -, -, -, hΦ, -, -, -, -, -, -, -, hloc, -, -, -, -, hrot, -, -⟩ := hg.2
  have hnear : Φ =ᶠ[𝓝 (0 : L2T L)] C.Φ := by
    filter_upwards [Metric.ball_mem_nhds (0 : L2T L)
      (div_pos loc.positive (Real.sqrt_pos.2 hκ))] with v hv
    exact (hloc v hv).trans (C.local_agreement v hv).symm
  have he : Φ = C.Φ :=
    (show AnalyticOnNhd ℝ Φ univ from fun v _ => hΦ v).eq_of_eventuallyEq
      (fun v _ => C.analytic v) hnear
  have ho : Φ (RF535Final.Tθ (L := L) hκ t u) =
      coordinateRotation (fun a => Circle.exp (t a)) (Φ u) := by
    apply lp.ext
    funext a
    rw [hrot, coordinateRotation, ActionTorus.rotate_apply]
    change _ = (((Circle.exp (t a))⁻¹ : Circle) : ℂ) * Φ u a
    rw [← Circle.exp_neg, Circle.coe_exp]
    push_cast
    rfl
  rw [he] at ho
  change RF535Final.Tθ (L := L) hκ t u = C.Ψ (coordinateRotation _ (C.Φ u))
  rw [← ho, C.left_inverse]

/-- A principal argument on the finite head and zero outside it. -/
def shortTime (F : Finset ℤ) (θ : AngleTorus) : Linf :=
  ⟨fun a => (truncate F θ a : ℂ).arg, memℓp_infty ⟨Real.pi, by
    rintro _ ⟨a, rfl⟩
    simpa only [Real.norm_eq_abs] using Complex.abs_arg_le_pi (truncate F θ a : ℂ)⟩⟩

theorem shortTime_zero (F : Finset ℤ) (θ : AngleTorus) {a : ℤ} (ha : a ∉ F) :
    shortTime F θ a = 0 := by
  change (truncate F θ a : ℂ).arg = 0
  simp [truncate, ha]

theorem shortTime_exp (F : Finset ℤ) (θ : AngleTorus) :
    (fun a => Circle.exp (shortTime F θ a)) = truncate F θ := by
  funext a
  exact Circle.exp_arg _

theorem shortTime_bound (F : Finset ℤ) (θ : AngleTorus) (a : ℤ) :
    -Real.pi ≤ shortTime F θ a ∧ shortTime F θ a ≤ Real.pi :=
  abs_le.mp (Complex.abs_arg_le_pi (truncate F θ a : ℂ))

theorem finite_classical (hκ : 0 < κ) (F : Finset ℤ) (θ : AngleTorus) (u : L2T L) :
    RF535Final.Tθ (L := L) hκ (shortTime F θ) u = physicalAngle hκ (truncate F θ) u := by
  rw [classical_time, shortTime_exp]

/-- The exponent of the accepted finite-count propagator has precisely the
inverse-circle character on every complete Bethe array. -/
theorem finite_quantum (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (F : Finset ℤ) (θ : AngleTorus) (ψ : HN L N) :
    R52CFEvol.countEvol L hκ hN F (shortTime F θ) ψ =
      quantumRotation (HaarSpectralTail.bas L hκ hN) (truncate F θ) ψ := by
  let b := HaarSpectralTail.bas L hκ hN
  let t := shortTime F θ
  let X := ∑ a ∈ F, (t a : ℂ) • R52CFEvol.countOp L hκ hN a
  let μ (m : MArr N) := HighAngleReconstruction.countEigen F t m
  have hX (m : MArr N) : X (b m) = (μ m : ℂ) • b m := by
    rw [R52CFEvol.diag_sum b F _ _ _
      (fun a i => R52CFEvol.B_eigen L hκ hN a i)]
    congr 1
    unfold μ HighAngleReconstruction.countEigen
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
  have he (m : MArr N) : μ m = Real.pi * HighAngleReconstruction.countEigen F
      (HighAngleEvolutionBridge.unitAngle θ) m := by
    unfold μ HighAngleReconstruction.countEigen HighAngleEvolutionBridge.unitAngle
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    change (truncate F θ a : ℂ).arg * (m.val a : ℝ) = _
    rw [truncate, ite_eq_left ha]
    field_simp
  have hop : R52CFEvol.countEvol L hκ hN F t =
      (quantumRotation b (truncate F θ)).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply NormalityBridge.clm_ext_basis b
    intro m
    change R52CFEvol.expG X (b m) = quantumRotation b (truncate F θ) (b m)
    rw [R52CFEvol.exp_diag b X μ hX, quantumRotation_basis,
      HighAngleEvolutionBridge.countPhase_exp, he]
    congr 2
    ring
  exact congrArg (fun A : HN L N →L[ℂ] HN L N => A ψ) hop

end QuantumNLS.RetargetAnglesR48b

#print axioms QuantumNLS.RetargetAnglesR48b.finite_classical
#print axioms QuantumNLS.RetargetAnglesR48b.finite_quantum
end


/-! The compact-profile version of the graded seed step. Placement moments,
character projection and orthogonality are the frozen R-300B8640 machinery. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate ENNReal

namespace QuantumNLS.RetargetUniformSeedR48b
open PhysicalTensor TensorCarrier BetheCoefficientTransform CountRotations FullCharacterProjection
open DynSeedInputR47b DynSeedClassicalR47b DynSeedPolynomialR47b
open DynSeedGradingR47b DynSeedMomentsR47b DynSeedHaarR47b
open Def044D1SpectralR51a (basis)
variable {L κ : ℝ} [Fact (0 < L)]

/-- Uniform physical marginals for the zero hierarchy-time slice, over the
actual smooth unit profile class and every full angle sequence. -/
def UniformAngles (hκ : 0 < κ) (R : ℝ) : Prop :=
  ∀ k ε, 0 < ε → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1,
    ∀ u ∈ R52CFCompact.profileClass L R, ∀ θ : AngleTorus,
      stateError k hk (quantumRotation (basis hκ n) θ (HighMomentsOps.wvec (n+1) u))
        (physicalAngle hκ θ u) ≤ ENNReal.ofReal ε

theorem symbol_residual_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x y : E) (z w : ℂ) (hx : ‖x‖ = 1) :
    ‖y - z • x‖ ≤ ‖y - w • x‖ + ‖w - z‖ := by
  have he : y - z • x = (y - w • x) + (w - z) • x := by
    rw [sub_smul]
    abel
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, hx, mul_one])

theorem eventual_seed (hκ : 0 < κ) (R : ℝ) (a b : ℤ) (hab : a ≠ b)
    (hmarginal : UniformAngles (L := L) hκ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ A : HN L (n+1) →L[ℂ] HN L (n+1),
      Graded (basis hκ n) a b A ∧ ∀ u ∈ R52CFCompact.profileClass L R,
        residual A (symbol hκ a b u) (HighMomentsOps.wvec (n+1) u) ≤ ε := by
  let U := R52CFCompact.profileClass L R
  let X := U × AngleTorus
  let v (p : X) := physicalAngle hκ p.2 p.1.1
  let x (n : ℕ) (p : X) : HN L (n+1) :=
    quantumRotation (basis hκ n) p.2 (HighMomentsOps.wvec (n+1) p.1.1)
  have hvO (p : X) : v p ∈ RetargetCompactR48b.orbit hκ R :=
    ⟨p.1.1, subset_closure p.1.2, angle_mem_torus hκ _ _ (fun _ => rfl) p.2⟩
  have hv (p : X) : ‖v p‖ = 1 := RetargetCompactR48b.orbit_unit hκ R (hvO p)
  have hx (n : ℕ) (p : X) : ‖x n p‖ = 1 := by
    rw [show x n p = quantumRotation (basis hκ n) p.2 (HighMomentsOps.wvec (n+1) p.1.1) from rfl,
      LinearIsometryEquiv.norm_map]
    change ‖(htpow (n+1) p.1.1 : HilbertTensorPower ℂ (L2T L) (n+1))‖ = 1
    simp only [norm_htpow, p.1.2.2.1, one_pow]
  have harg : ∀ k δ, 0 < δ → ∀ᶠ n in atTop, ∀ hk : k ≤ n+1, ∀ p,
      stateError k hk (x n p) (v p) ≤ ENNReal.ofReal δ := by
    intro k δ hδ
    filter_upwards [hmarginal k δ hδ] with n hn
    exact fun hk p => hn hk p.1.1 p.1.2 p.2
  have hquarter : 0 < ε / 4 := by positivity
  obtain ⟨f, hf, hclose⟩ := RetargetCompactR48b.orbit_approximants (L := L) hκ R a b hquarter
  obtain ⟨T, _, _, _, _, hstrong⟩ := coherent_residual hf (DynSeedR47b.quadratic v x hv hx harg)
  filter_upwards [hstrong (ε / 4) hquarter] with n hn
  refine ⟨component (basis hκ n) (T n) a b, component_graded (basis hκ n) (T n) a b hab, ?_⟩
  intro u hu
  let ψ := HighMomentsOps.wvec (n+1) u
  let z := symbol hκ a b u
  have hphase (θ : AngleTorus) : symbol hκ a b (v (⟨u, hu⟩, θ)) = character b a θ * z :=
    symbol_angle hκ a b θ _
  have hfwd (θ : AngleTorus) :
      ‖T n (x n (⟨u, hu⟩, θ)) - (character b a θ * z) • x n (⟨u, hu⟩, θ)‖ ≤ ε / 2 := by
    rw [← hphase θ]
    have hh := hn ((⟨u, hu⟩ : U), θ)
    have h1 : ‖T n (x n (⟨u, hu⟩, θ)) - f (v (⟨u, hu⟩, θ)) • x n (⟨u, hu⟩, θ)‖ ≤ ε / 4 :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans hh
    have h2 := hclose _ (hvO (⟨u, hu⟩, θ))
    refine (symbol_residual_le _ _ _ (f (v (⟨u, hu⟩, θ))) (hx n _)).trans ?_
    exact (add_le_add h1 h2.le).trans_eq (by ring)
  have hadj (θ : AngleTorus) :
      ‖(T n).adjoint (x n (⟨u, hu⟩, θ)) -
        conj (character b a θ * z) • x n (⟨u, hu⟩, θ)‖ ≤ ε / 2 := by
    rw [← hphase θ]
    have hh := hn ((⟨u, hu⟩ : U), θ)
    have h1 : ‖(T n).adjoint (x n (⟨u, hu⟩, θ)) -
        conj (f (v (⟨u, hu⟩, θ))) • x n (⟨u, hu⟩, θ)‖ ≤ ε / 4 :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans hh
    have h2 : ‖conj (f (v (⟨u, hu⟩, θ))) - conj (symbol hκ a b (v (⟨u, hu⟩, θ)))‖ < ε / 4 := by
      rw [← map_sub, Complex.norm_conj]
      exact hclose _ (hvO (⟨u, hu⟩, θ))
    refine (symbol_residual_le _ _ _ (conj (f (v (⟨u, hu⟩, θ)))) (hx n _)).trans ?_
    exact (add_le_add h1 h2.le).trans_eq (by ring)
  have h1 := residual_le (basis hκ n) (T n) a b ψ z (ε/2) hfwd
  have h2 := adjoint_residual_le (basis hκ n) (T n) a b ψ z (ε/2) hadj
  exact (add_le_add h1 h2).trans_eq (by ring)

end QuantumNLS.RetargetUniformSeedR48b

#print axioms QuantumNLS.RetargetUniformSeedR48b.eventual_seed
end

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.RetargetAnglesR48b." ||
        name.toString.startsWith "QuantumNLS.RetargetUniformSeedR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetSeedPrepR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
