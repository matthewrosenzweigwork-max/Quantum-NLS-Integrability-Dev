import QuantumNLS.Ext006PhysicalContinuityR38a

/-! Finite matrix-pair approximations of the actual completed HS tensor.
The physical operator exponential is continuous along these approximations
in every degree. Identification with occupation-core coefficients is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped InnerProductSpace
open Filter Topology
namespace QuantumNLS.Ext006PhysicalApproximationR38a
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors TraceClass
open Ext006PhysicalNormBridge.PairTensor Ext006PhysicalExponentialTerms
variable {L : ℝ} [Fact (0 < L)] {ι : Type*}

/-- Projection of an ordered completed tensor into the physical pair sector. -/
def pairProjection : HilbertTensor ℂ (L2T L) (L2T L) →L[ℂ] HN L 2 :=
  (physSector L 2).orthogonalProjectionOnto ∘L
    (twoIso (E := L2T L)).symm.toContinuousLinearEquiv.toContinuousLinearMap

def basisPair (b : HilbertBasis ι ℂ (L2T L)) (i j : ι) : HN L 2 :=
  pairProjection (htmul (b i) (b j))

/-- The literal finite matrix in the fixed physical basis, symmetrized in HN 2. -/
def finitePair (b : HilbertBasis ι ℂ (L2T L)) (K : L2T L →L[ℂ] L2T L)
    (S : Finset ι) : HN L 2 :=
  ∑ i ∈ S, ∑ j ∈ S, inner ℂ (b i) (K (b j)) • basisPair b i j

lemma pairProjection_pairTensor (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    pairProjection (Ext006PairTensor.pairTensor b K hHS) = physicalPair b K hHS hSym := by
  change (physSector L 2).orthogonalProjectionOnto
    (physicalPair b K hHS hSym : HilbertTensorPower ℂ (L2T L) 2) = _
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

/-- Norm convergence of the completed tensor's matrix expansion. -/
theorem hasSum_pair (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    HasSum (fun p : ι × ι => inner ℂ (b p.1) (K (b p.2)) • basisPair b p.1 p.2)
      (physicalPair b K hHS hSym) := by
  have h := (pairProjection (L := L)).hasSum
    ((htmulBasis b b).hasSum_repr (Ext006PairTensor.pairTensor b K hHS))
  simpa only [HilbertBasis.repr_apply_apply, htmulBasis_apply,
    Ext006PairTensor.pairTensor_coefficient, map_smul,
    pairProjection_pairTensor b K hHS hSym, basisPair] using h

/-- Finite square mode sets are cofinal among all finite sets of matrix entries. -/
lemma square_tendsto_atTop :
    Tendsto (fun S : Finset ι => S.product S) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro T
  refine eventually_atTop.2 ⟨T.image Prod.fst ∪ T.image Prod.snd, ?_⟩
  intro S hS p hp
  exact Finset.mem_product.mpr
    ⟨hS (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)),
      hS (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp))⟩

/-- The finite-mode physical pairs converge in physical Hilbert norm. -/
theorem finitePair_tendsto (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    Tendsto (finitePair b K) atTop (𝓝 (physicalPair b K hHS hSym)) := by
  have h := (hasSum_pair b K hHS hSym).comp (square_tendsto_atTop (ι := ι))
  apply h.congr'
  filter_upwards [] with S
  change (∑ p ∈ S.product S, inner ℂ (b p.1) (K (b p.2)) • basisPair b p.1 p.2) =
    ∑ i ∈ S, ∑ j ∈ S, inner ℂ (b i) (K (b j)) • basisPair b i j
  exact Finset.sum_product S S (fun p => inner ℂ (b p.1) (K (b p.2)) • basisPair b p.1 p.2)

/-- Every exact physical exponential degree is obtained by a norm limit of
finite-mode pair-creation degrees. No norm/trace identity is an input. -/
theorem finitePair_term_tendsto (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) (n : ℕ) :
    Tendsto (fun S : Finset ι => term (finitePair b K S) n) atTop
      (𝓝 (term (physicalPair b K hHS hSym) n)) :=
  Ext006PhysicalContinuityR38a.term_tendsto (finitePair_tendsto b K hHS hSym) n

theorem finitePair_truncation_tendsto (b : HilbertBasis ι ℂ (L2T L))
    (K : L2T L →L[ℂ] L2T L) (hHS : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) (M : ℕ) :
    Tendsto (fun S : Finset ι => truncation (finitePair b K S) M) atTop
      (𝓝 (truncation (physicalPair b K hHS hSym) M)) :=
  Ext006PhysicalContinuityR38a.truncation_tendsto (finitePair_tendsto b K hHS hSym) M

end QuantumNLS.Ext006PhysicalApproximationR38a

#print axioms QuantumNLS.Ext006PhysicalApproximationR38a.hasSum_pair

#print axioms QuantumNLS.Ext006PhysicalApproximationR38a.square_tendsto_atTop

#print axioms QuantumNLS.Ext006PhysicalApproximationR38a.finitePair_tendsto

#print axioms QuantumNLS.Ext006PhysicalApproximationR38a.finitePair_term_tendsto

#print axioms QuantumNLS.Ext006PhysicalApproximationR38a.finitePair_truncation_tendsto

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalApproximationR38a." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round38a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
