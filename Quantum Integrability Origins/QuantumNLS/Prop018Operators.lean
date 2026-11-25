import QuantumNLS.Prop018ChargeCutoff
import QuantumNLS.MPLinearization

/-! The printed C0 and C1, through one common functional calculus of the
actual transfer and its derivative. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop018Operators
open TensorCarrier PhysicalTensor KernelDefinition NormalizedTransfer UnconditionalBetheBasis
open HaarSpectralTail HaarNonlinearAbstract HaarNonlinearTail MixedQuadratures MPOps
open Prop018JointCalculus Prop018ChargeCutoff

section Generic
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma real_integral_selfadjoint (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (a : ι → ℝ)
    (ha : ∀ i, A (b i) = (a i : ℂ) • b i) : IsSelfAdjoint A :=
  HighAngleNonlinearEvolution.real_diagonal_selfadjoint b A a (diagC_of_apply ha)
/-- Keep the standard CFC instance at an abstract Hilbert space, then
specialize it to the physical carrier. -/
def normalCfc (f : ℂ → ℂ) (A : H →L[ℂ] H) : H →L[ℂ] H := cfc (p := IsStarNormal) f A

lemma weighted_fst_calculus {K : Set (ℂ × ℂ)} [CompactSpace K]
    (b : HilbertBasis ι ℂ H) (x : ι → K) (A : H →L[ℂ] H) (hA : IsStarNormal A)
    (hd : ∀ i, A (b i) = (x i).val.1 • b i) (f : ℂ → ℂ) (hf : Continuous f) (u : ℂ) :
    spectralHom b x (u • (⟨fun y : K => f y.val.1, hf.comp fstC.continuous⟩ : C(K, ℂ))) =
      u • normalCfc f A := by
  rw [map_smul, spectralHom_fst_cfc b x A hA hd f hf]
  rfl

lemma continuous_ops_aesm {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] (ν : Measure Θ)
    (A : Θ → H →L[ℂ] H) (hc : Continuous A) : AEStronglyMeasurable A ν :=
  hc.aestronglyMeasurable_of_compactSpace

end Generic

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

abbrev S (z : ℂ) := normalizedTransfer L κ N z
abbrev T (z : ℂ) := deriv (fun w => normalizedTransfer L κ N w) z
abbrev lam (m : BetheLabels.MArr N) (z : ℂ) := NormalityBridge.eigen (L := L) κ hκ hN m z
abbrev dlam (m : BetheLabels.MArr N) (z : ℂ) := deriv (NormalityBridge.eigen (L := L) κ hκ hN m) z

include hκ hN

lemma T_eigen (z : ℂ) (m : BetheLabels.MArr N) :
    T (L := L) (κ := κ) (N := N) z (bas L hκ hN m) = dlam (L := L) hκ hN m z • bas L hκ hN m := by
  simpa only [iteratedDeriv_one] using NormalityBridge.deriv_basis (L := L) hκ hN
    (meanField_isBetheBasis (L := L) hκ hN) 1 z m

/-- Normality and all cross commutations, including adjoints, on the actual
physical Hilbert space. -/
lemma joint_normal (z w : ℂ) :
    IsStarNormal (S (L := L) (κ := κ) (N := N) z) ∧
    IsStarNormal (T (L := L) (κ := κ) (N := N) w) ∧
    Commute (S (L := L) (κ := κ) (N := N) z) (T (L := L) (κ := κ) (N := N) w) ∧
    Commute (S (L := L) (κ := κ) (N := N) z) (ContinuousLinearMap.adjoint (T (L := L) (κ := κ) (N := N) w)) := by
  have hs := normal_deriv_physical (L := L) hκ hN 0 z
  have ht := normal_deriv_physical (L := L) hκ hN 1 w
  have hdS := diagC_of_apply (transfer_physicalBasis (L := L) hκ hN z)
  have hdT := diagC_of_apply (T_eigen (L := L) hκ hN w)
  refine ⟨⟨by simpa only [S, iteratedDeriv_zero, ContinuousLinearMap.star_eq_adjoint] using hs⟩,
    ⟨by simpa only [T, iteratedDeriv_one, ContinuousLinearMap.star_eq_adjoint] using ht⟩, IsDiagC.commute hdS hdT, IsDiagC.commute hdS hdT.adjoint⟩

section Family
variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (ν : Measure Θ) [IsFiniteMeasure ν]

/-- The printed correction operator, explicitly tied to the common
transfer/derivative calculus and its operator-valued contour integral. -/
def C1Realization (z : Θ → ℂ) (u : Θ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ)
    (C1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) : Prop :=
  ∃ (K : Set (ℂ × ℂ)) (_ : CompactSpace K)
    (x : Θ → BetheLabels.MArr N → K)
    (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N))
    (g : Θ → C(K, ℂ)),
    (∀ τ m, (x τ m).val = (lam (L := L) hκ hN m (z τ), dlam (L := L) hκ hN m (z τ))) ∧
    (∀ τ v m, Φ τ v (bas L hκ hN m) = v (x τ m) • bas L hκ hN m) ∧
    (∀ τ, Φ τ fstC = S (L := L) (κ := κ) (N := N) (z τ) ∧
      Φ τ sndC = T (L := L) (κ := κ) (N := N) (z τ)) ∧
    (∀ τ y, g τ y = ((-I * κ) * u τ) * qt (z τ) y.val.1 y.val.2) ∧
    C1 = reOp (∫ τ, Φ τ (g τ) ∂ν)

/-- The two bounded source operators and their exact eigenvalues. The
common compact calculus and C1's literal Bochner formula are retained. -/
theorem construct (z : Θ → ℂ) (hz : Continuous z) (u : Θ → ℂ) (hu : Continuous u)
    (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ)
    (hf : Continuous fun p : Θ × ℂ => f (z p.1) p.2)
    (hqt : Continuous fun p : Θ × (ℂ × ℂ) => qt (z p.1) p.2.1 p.2.2) :
    ∃ (K : Set (ℂ × ℂ)) (_ : CompactSpace K)
      (x : Θ → BetheLabels.MArr N → K)
      (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N))
      (C1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N),
      (∀ θ m, (x θ m).val = (lam (L := L) hκ hN m (z θ), dlam (L := L) hκ hN m (z θ))) ∧
      (∀ θ g m, Φ θ g (bas L hκ hN m) = g (x θ m) • bas L hκ hN m) ∧
      (∀ θ, Φ θ fstC = S (L := L) (κ := κ) (N := N) (z θ) ∧
        Φ θ sndC = T (L := L) (κ := κ) (N := N) (z θ)) ∧
      C1 = reOp (∫ θ, Φ θ ⟨fun y => ((-I * κ) * u θ) * qt (z θ) y.val.1 y.val.2,
        (continuous_const.mul ((hqt.comp (continuous_const.prodMk continuous_id)).comp continuous_subtype_val))⟩ ∂ν) ∧
      IsSelfAdjoint (C0op ν (fun θ => S (L := L) (κ := κ) (N := N) (z θ)) u (fun θ => f (z θ))) ∧
      IsSelfAdjoint C1 ∧
      Commute (C0op ν (fun θ => S (L := L) (κ := κ) (N := N) (z θ)) u (fun θ => f (z θ))) C1 ∧
      (∀ m, C0op ν (fun θ => S (L := L) (κ := κ) (N := N) (z θ)) u (fun θ => f (z θ)) (bas L hκ hN m) =
        (((∫ θ, (u θ * f (z θ) (lam (L := L) hκ hN m (z θ))).re ∂ν : ℝ)) : ℂ) • bas L hκ hN m) ∧
      (∀ m, C1 (bas L hκ hN m) =
        (((∫ θ, ((-I * κ) * u θ) * qt (z θ) (lam (L := L) hκ hN m (z θ)) (dlam (L := L) hκ hN m (z θ)) ∂ν).re : ℝ) : ℂ) •
          bas L hκ hN m) := by
  let b := bas L hκ hN
  have hScont : Continuous (fun θ => S (L := L) (κ := κ) (N := N) (z θ)) :=
    (NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)).continuous.comp hz
  have hTcont : Continuous (fun θ => T (L := L) (κ := κ) (N := N) (z θ)) := by
    have hd := NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)
    exact (Differentiable.deriv (E := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) hd).continuous.comp hz
  have hcS : IsCompact (Set.range (fun θ => S (L := L) (κ := κ) (N := N) (z θ))) := isCompact_range hScont
  have hcT : IsCompact (Set.range (fun θ => T (L := L) (κ := κ) (N := N) (z θ))) := isCompact_range hTcont
  obtain ⟨M0, hM0⟩ := (IsCompact.isBounded (α := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) hcS).exists_norm_le
  obtain ⟨M1, hM1⟩ := (IsCompact.isBounded (α := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) hcT).exists_norm_le
  let K : Set (ℂ × ℂ) := Metric.closedBall 0 (max M0 0) ×ˢ Metric.closedBall 0 (max M1 0)
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : ℂ) (max M0 0)).prod (isCompact_closedBall (0 : ℂ) (max M1 0)))
  let x : Θ → BetheLabels.MArr N → K := fun θ m =>
    ⟨(lam (L := L) hκ hN m (z θ), dlam (L := L) hκ hN m (z θ)), by
      constructor
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (eigen_norm_le b _ _ (transfer_physicalBasis (L := L) hκ hN (z θ)) m).trans
          ((hM0 _ ⟨θ, rfl⟩).trans (le_max_left _ _))
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact (eigen_norm_le b _ _ (T_eigen (L := L) hκ hN (z θ)) m).trans
          ((hM1 _ ⟨θ, rfl⟩).trans (le_max_left _ _))⟩
  let Φ := fun θ => spectralHom b (x θ)
  have hcoords (θ : Θ) : Φ θ fstC = S (L := L) (κ := κ) (N := N) (z θ) ∧
      Φ θ sndC = T (L := L) (κ := κ) (N := N) (z θ) := by
    constructor <;> apply TransferNormality.ext_of_hilbertBasis b
    · intro m
      rw [spectralHom_eigen, transfer_physicalBasis]
      rfl
    · intro m
      rw [spectralHom_eigen, T_eigen (L := L) hκ hN]
      rfl
  have hm0 : AEStronglyMeasurable (fun θ => Φ θ fstC) ν := by
    have he : (fun θ => Φ θ fstC) = (fun θ => S (L := L) (κ := κ) (N := N) (z θ)) :=
      funext fun θ => (hcoords θ).1
    rw [he]
    exact continuous_ops_aesm (H := SymSector ℂ (L2T L) N) ν _ hScont
  have hm1 : AEStronglyMeasurable (fun θ => Φ θ sndC) ν := by
    have he : (fun θ => Φ θ sndC) = (fun θ => T (L := L) (κ := κ) (N := N) (z θ)) :=
      funext fun θ => (hcoords θ).2
    rw [he]
    exact continuous_ops_aesm (H := SymSector ℂ (L2T L) N) ν _ hTcont
  let F0 : C(Θ × K, ℂ) := ⟨fun p => u p.1 * f (z p.1) p.2.val.1,
    (hu.comp continuous_fst).mul (hf.comp
      (continuous_fst.prodMk (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))))⟩
  let F1 : C(Θ × K, ℂ) := ⟨fun p => ((-I * κ) * u p.1) * qt (z p.1) p.2.val.1 p.2.val.2,
    (continuous_const.mul (hu.comp continuous_fst)).mul
      (hqt.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have hi0 := pair_integrable ν b x hm0 hm1 F0
  have hi1 := pair_integrable ν b x hm0 hm1 F1
  have he0 (θ : Θ) : Φ θ (F0.curry θ) =
      u θ • normalCfc (f (z θ)) (S (L := L) (κ := κ) (N := N) (z θ)) := by
    have hfθ : Continuous (f (z θ)) := hf.comp (continuous_const.prodMk continuous_id)
    change spectralHom b (x θ) (F0.curry θ) = _
    rw [show F0.curry θ = u θ • (⟨fun y : K => f (z θ) y.val.1,
      hfθ.comp fstC.continuous⟩ : C(K, ℂ)) by ext y; rfl]
    exact weighted_fst_calculus (H := SymSector ℂ (L2T L) N) b (x θ) _
      (joint_normal (L := L) hκ hN (z θ) (z θ)).1
      (transfer_physicalBasis (L := L) hκ hN (z θ)) _ hfθ (u θ)
  have hint : Integrable (fun θ => u θ • normalCfc (f (z θ)) (S (L := L) (κ := κ) (N := N) (z θ))) ν :=
    hi0.congr (ae_of_all _ he0)
  let C1 := reOp (∫ θ, Φ θ (F1.curry θ) ∂ν)
  have hC0 (m : BetheLabels.MArr N) := Prop020Diag.C0op_eigen (H := SymSector ℂ (L2T L) N) ν
    (fun θ => S (L := L) (κ := κ) (N := N) (z θ))
    (fun θ => (joint_normal (L := L) hκ hN (z θ) (z θ)).1) u (fun θ => f (z θ))
    (fun θ => hf.comp (continuous_const.prodMk continuous_id)) hint
    (b.orthonormal.ne_zero m) (fun θ => lam (L := L) hκ hN m (z θ))
    (fun θ => transfer_physicalBasis (L := L) hκ hN (z θ) m)
  have hC1 (m : BetheLabels.MArr N) := integrated_eigen ν b x (fun θ => F1.curry θ) hi1 m
  refine ⟨K, inferInstance, x, Φ, C1, fun _ _ => rfl, fun θ g m => spectralHom_eigen b (x θ) g m,
    hcoords, rfl, real_integral_selfadjoint b _ _ hC0,
    real_integral_selfadjoint b _ _ hC1, IsDiagC.commute (diagC_of_apply hC0) (diagC_of_apply hC1),
    hC0, hC1⟩
end Family
end QuantumNLS.Prop018Operators

#print axioms QuantumNLS.Prop018Operators.real_integral_selfadjoint
#print axioms QuantumNLS.Prop018Operators.normalCfc
#print axioms QuantumNLS.Prop018Operators.weighted_fst_calculus
#print axioms QuantumNLS.Prop018Operators.continuous_ops_aesm
#print axioms QuantumNLS.Prop018Operators.S
#print axioms QuantumNLS.Prop018Operators.T
#print axioms QuantumNLS.Prop018Operators.lam
#print axioms QuantumNLS.Prop018Operators.dlam
#print axioms QuantumNLS.Prop018Operators.T_eigen
#print axioms QuantumNLS.Prop018Operators.joint_normal
#print axioms QuantumNLS.Prop018Operators.C1Realization
#print axioms QuantumNLS.Prop018Operators.construct

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018Operators." then
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
