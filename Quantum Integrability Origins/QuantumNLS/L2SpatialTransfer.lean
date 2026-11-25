import QuantumNLS.L1SpatialTransfer

/-!
DEF-013: transfer for every physical L² equivalence class.
The coefficient, balanced/unbalanced conventions and diagonal gauge come from
frozen SpatialTransfer. The finite-period L¹ construction is L1SpatialTransfer.
No continuous representative is required.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval
namespace QuantumNLS.L2SpatialTransfer
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat2 :=
  NormedAddGroup.toENormedAddMonoid

/-- Every L¹ profile has the source's integrable matrix coefficient. -/
theorem intervalIntegrable_coef {L : ℝ} {u : ℝ → ℂ}
    (hu : IntervalIntegrable u volume 0 L) (p q : ℝ) (z : ℂ) :
    IntervalIntegrable (coef p q u z) volume 0 L := by
  have hconj : IntervalIntegrable (fun x => conj (u x)) volume 0 L :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp hu.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hu.2⟩
  let C : Mat2 := !![-(Complex.I * z) / 2, 0; 0, Complex.I * z / 2]
  let E : Mat2 := !![0, 1; 0, 0]
  let F : Mat2 := !![0, 0; 1, 0]
  have hh := ((intervalIntegrable_const (c := C)).add
    ((hconj.const_mul (p : ℂ)).smul_continuousOn (g := fun _ => E) continuousOn_const)).add
      ((hu.const_mul (q : ℂ)).smul_continuousOn (g := fun _ => F) continuousOn_const)
  have he : coef p q u z = fun x =>
      C + ((p : ℂ) * conj (u x)) • E + ((q : ℂ) * u x) • F := by
    funext x
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coef, C, E, F]
  rw [he]
  exact hh

variable {L : ℝ} [Fact (0 < L)]

/-- Pullback of the canonical representative to the physical period. -/
def profile (u : PhysicalTensor.L2T L) (x : ℝ) : ℂ := u (x : AddCircle L)

/-- L² on the mass-L torus implies L¹ on the physical interval. -/
theorem intervalIntegrable_profile (u : PhysicalTensor.L2T L) :
    IntervalIntegrable (profile u) volume 0 L := by
  have hm := (Lp.memLp u).comp_measurePreserving (AddCircle.measurePreserving_mk L 0)
  have hi := hm.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (Fact.out : 0 < L).le).mpr
  change Integrable (fun x : ℝ => u (x : AddCircle L)) (volume.restrict (Ioc 0 L))
  simpa only [Function.comp_def, zero_add] using hi

/-- Actual balanced fundamental matrix for any L² input, defined by the convergent Volterra series. -/
def spatialTransfer (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) : ℝ → Mat2 :=
  transfer (balCoef κ (profile u) z)

/-- Actual finite-period discriminant on the physical L² carrier. -/
def discriminant (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) : ℂ :=
  Matrix.trace (spatialTransfer κ u z L)

/-- Initial condition, absolute continuity and a.e. differential equation for arbitrary L² data. -/
theorem spatialTransfer_spec (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    spatialTransfer κ u z 0 = 1 ∧
      AbsolutelyContinuousOnInterval (spatialTransfer κ u z) 0 L ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 L),
        HasDerivAt (spatialTransfer κ u z)
          (balCoef κ (profile u) z x * spatialTransfer κ u z x) x) ∧
      ∀ M : ℝ → Mat2, ContinuousOn M (Icc 0 L) →
        (∀ x ∈ Icc 0 L, M x = 1 + ∫ s in (0 : ℝ)..x, balCoef κ (profile u) z s * M s) →
        EqOn M (spatialTransfer κ u z) (Icc 0 L) :=
  fundamental_spec (Fact.out : 0 < L).le
    (intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z)

/-- The constructed matrix satisfies the integral equation at every point, including endpoints. -/
theorem spatialTransfer_integral_eq (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    spatialTransfer κ u z x = 1 + ∫ s in (0 : ℝ)..x,
      balCoef κ (profile u) z s * spatialTransfer κ u z s :=
  transfer_integral_eq (Fact.out : 0 < L).le
    (intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z) hx

/-- An arbitrary torus representative agrees a.e. after pullback to one period. -/
theorem profile_ae_of_representative (u : PhysicalTensor.L2T L) {v : AddCircle L → ℂ}
    (hv : v =ᵐ[volume] u) :
    (fun x : ℝ => v (x : AddCircle L)) =ᵐ[volume.restrict (Icc 0 L)] profile u := by
  have hm := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp hv
  have he : volume.restrict (Icc (0 : ℝ) L) = volume.restrict (Ioc (0 : ℝ) L) :=
    restrict_Ioc_eq_restrict_Icc.symm
  rw [he]
  change (fun x : ℝ => v (x : AddCircle L)) =ᵐ[volume.restrict (Ioc 0 L)]
    (fun x : ℝ => u (x : AddCircle L))
  simpa only [Function.comp_def, zero_add] using hm

/-- Every representative yields exactly the same matrix at every x in the period. -/
theorem spatialTransfer_eq_of_representative (κ : ℝ) (u : PhysicalTensor.L2T L)
    {v : AddCircle L → ℂ} (hv : v =ᵐ[volume] u) (z : ℂ)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    transfer (balCoef κ (fun s => v (s : AddCircle L)) z) x = spatialTransfer κ u z x := by
  apply transfer_eq_of_ae (Fact.out : 0 < L).le _ hx
  filter_upwards [profile_ae_of_representative u hv] with s hs
  simp only [balCoef, coef, hs]

/-- The monodromy trace is independent of the torus representative. -/
theorem discriminant_eq_of_representative (κ : ℝ) (u : PhysicalTensor.L2T L)
    {v : AddCircle L → ℂ} (hv : v =ᵐ[volume] u) (z : ℂ) :
    Matrix.trace (transfer (balCoef κ (fun s => v (s : AddCircle L)) z) L) = discriminant κ u z := by
  rw [spatialTransfer_eq_of_representative κ u hv z ⟨(Fact.out : 0 < L).le, le_rfl⟩]
  rfl

/-- Agreement with the frozen classical transfer wherever a continuous representative exists. -/
theorem transfer_eq_classical {A : ℝ → Mat2} (hA : Continuous A)
    {M : ℝ → Mat2} (hM : IsFundamental A M) :
    EqOn (transfer A) M (Icc 0 L) := by
  have hc : Continuous M := continuous_iff_continuousAt.mpr (fun x => (hM.2 x).continuousAt)
  apply integral_solution_unique (Fact.out : 0 < L).le (hA.intervalIntegrable 0 L)
    (continuousOn_transfer (Fact.out : 0 < L).le (hA.intervalIntegrable 0 L)) hc.continuousOn
    (fun _ hx => transfer_integral_eq (Fact.out : 0 < L).le (hA.intervalIntegrable 0 L) hx)
  intro x _
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hM.2 t)
    ((hA.mul hc).intervalIntegrable 0 x)
  rw [hi, hM.1]; abel


/-- Direct agreement with the frozen selected classical transfer on its continuous-profile class. -/
theorem transfer_eq_frozen (κ : ℝ) {f : ℝ → ℂ} (hf : Continuous f) (z : ℂ) :
    EqOn (transfer (balCoef κ f z)) (SpatialTransfer.spatialTransfer κ f z) (Icc 0 L) :=
  transfer_eq_classical (continuous_coef _ _ hf z)
    (LinearFundamental.spatialTransfer_spec' κ hf z)

/-- Positive-coupling diagonal gauge for every L² profile, including discontinuous profiles. -/
theorem bal_eq_gauge {κ : ℝ} (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    EqOn (spatialTransfer κ u z)
      (fun x => Dinv κ * transfer (unbalCoef κ (profile u) z) x * Dm κ) (Icc 0 L) := by
  let A := unbalCoef κ (profile u) z
  let U := transfer A
  let G : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 (Dinv κ) (Dm κ)
  have hi : IntervalIntegrable A volume 0 L := intervalIntegrable_coef (intervalIntegrable_profile u) κ 1 z
  have hc : ContinuousOn U (Icc 0 L) := continuousOn_transfer (Fact.out : 0 < L).le hi
  have hGc : ContinuousOn (fun x => G (U x)) (Icc 0 L) := G.continuous.comp_continuousOn hc
  have hp : IntervalIntegrable (fun s => A s * U s) volume 0 L :=
    hi.mul_continuousOn (by rw [uIcc_of_le (Fact.out : 0 < L).le]; exact hc)
  have hGe : ∀ x ∈ Icc 0 L, G (U x) = 1 + ∫ s in (0 : ℝ)..x,
      balCoef κ (profile u) z s * G (U s) := by
    intro x hx
    have hs : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le (Fact.out : 0 < L).le]
      exact Icc_subset_Icc_right hx.2
    have hpx : IntervalIntegrable (fun s => A s * U s) volume 0 x := hp.mono_set hs
    calc
      G (U x) = G (1 + ∫ s in (0 : ℝ)..x, A s * U s) :=
        congrArg G (transfer_integral_eq (Fact.out : 0 < L).le hi hx)
      _ = 1 + ∫ s in (0 : ℝ)..x, G (A s * U s) := by
        rw [map_add]
        have hG1 : G 1 = 1 := by
          change Dinv κ * (1 : Mat2) * Dm κ = 1
          simpa only [mul_one] using Dinv_mul_Dm hκ
        rw [hG1]
        exact congrArg (fun y : Mat2 => 1 + y) (G.intervalIntegral_comp_comm hpx).symm
      _ = 1 + ∫ s in (0 : ℝ)..x, balCoef κ (profile u) z s * G (U s) := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s _
        change Dinv κ * (unbalCoef κ (profile u) z s * U s) * Dm κ =
          balCoef κ (profile u) z s * (Dinv κ * U s * Dm κ)
        rw [← Dinv_unbalCoef_Dm hκ (profile u) z s]
        calc
          Dinv κ * (unbalCoef κ (profile u) z s * U s) * Dm κ =
              Dinv κ * unbalCoef κ (profile u) z s * (Dm κ * Dinv κ) * U s * Dm κ := by
            rw [Dm_mul_Dinv hκ]
            simp [mul_assoc]
          _ = (Dinv κ * unbalCoef κ (profile u) z s * Dm κ) * (Dinv κ * U s * Dm κ) := by
            simp only [mul_assoc]
  exact integral_solution_unique (Fact.out : 0 < L).le
    (intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z)
    (continuousOn_transfer (Fact.out : 0 < L).le
      (intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z)) hGc
    (fun _ hx => spatialTransfer_integral_eq κ u z hx) hGe

/-- The discriminant is also the actual unbalanced monodromy trace for arbitrary L² input. -/
theorem discriminant_eq_unbalanced {κ : ℝ} (hκ : 0 < κ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    discriminant κ u z = Matrix.trace (transfer (unbalCoef κ (profile u) z) L) := by
  unfold discriminant
  rw [bal_eq_gauge hκ u z ⟨(Fact.out : 0 < L).le, le_rfl⟩,
    Matrix.trace_mul_comm, ← mul_assoc, Dm_mul_Dinv hκ, one_mul]

end QuantumNLS.L2SpatialTransfer

#print axioms QuantumNLS.L2SpatialTransfer.intervalIntegrable_coef
#print axioms QuantumNLS.L2SpatialTransfer.profile
#print axioms QuantumNLS.L2SpatialTransfer.intervalIntegrable_profile
#print axioms QuantumNLS.L2SpatialTransfer.spatialTransfer
#print axioms QuantumNLS.L2SpatialTransfer.discriminant
#print axioms QuantumNLS.L2SpatialTransfer.spatialTransfer_spec
#print axioms QuantumNLS.L2SpatialTransfer.spatialTransfer_integral_eq
#print axioms QuantumNLS.L2SpatialTransfer.profile_ae_of_representative
#print axioms QuantumNLS.L2SpatialTransfer.spatialTransfer_eq_of_representative
#print axioms QuantumNLS.L2SpatialTransfer.discriminant_eq_of_representative
#print axioms QuantumNLS.L2SpatialTransfer.transfer_eq_classical
#print axioms QuantumNLS.L2SpatialTransfer.transfer_eq_frozen
#print axioms QuantumNLS.L2SpatialTransfer.bal_eq_gauge
#print axioms QuantumNLS.L2SpatialTransfer.discriminant_eq_unbalanced

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L2SpatialTransfer." then
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
