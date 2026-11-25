import QuantumNLS.BetheBasisOneParticle
import QuantumNLS.BetheCoefficientTransform

/-!
Conditional assembly of R-8E4D05E7, periodic_basis.tex:54–61,70–85,301–310.
The held R-9BF8373D is a Prop-valued argument, never a proved import.
`AbstractContinuity` states its strict-positive shifted-operator version:
A = H+1 >= 1, R = A⁻¹. For such operators increasing closed-form order
is equivalently decreasing inverse order; strong right continuity of R is
strong resolvent right continuity. Compact R(0) is compact free resolvent.
The only conclusion supplied by this premise is propagation of dense span.
Neither orthogonality, nonvanishing, normalization nor either eigenrelation
uses it. The N=1 density branch is the frozen ordinary Fourier proof.
-/
noncomputable section
open Set Filter
open scoped BigOperators Topology InnerProductSpace NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheConditionalBasis
open PhysicalTensor BethePhysicalTransfer ContactOperator BetheFreeFamily BetheContinuityInputs
open BetheBasisOrthogonality

/-- Exact abstract continuity principle used, R-9BF8373D / basis:prop:continuity,
in the H+1 convention explicitly permitted after the printed proposition.
For arbitrary fixed complex Hilbert space and fixed discrete label set:
self-adjoint A >= 1, actual inverse R, increasing form order (inverse-order
encoding), strong right resolvent continuity, compact initial resolvent,
continuous nonzero pointwise independent eigenvectors and initial density
imply density at every parameter. No orthogonality or energy simplicity
hypothesis occurs. This definition asserts no proof of the principle. -/
def AbstractContinuity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ι : Type) (A : ℝ≥0 → E →ₗ.[ℂ] E) (R : ℝ≥0 → E →L[ℂ] E),
    (∀ t, IsSelfAdjoint (A t)) →
    (∀ t, ∀ x : (A t).domain, ‖(x : E)‖ ^ 2 ≤ (⟪(x : E), A t x⟫_ℂ).re) →
    (∀ t f, ∃ h : R t f ∈ (A t).domain, A t ⟨R t f, h⟩ = f) →
    (∀ t (x : (A t).domain), R t (A t x) = (x : E)) →
    (∀ s t, s ≤ t → ∀ f, (⟪R t f, f⟫_ℂ).re ≤ (⟪R s f, f⟫_ℂ).re) →
    (∀ t f, Tendsto (fun s => R s f) (𝓝[≥] t) (𝓝 (R t f))) →
    IsCompactOperator (R 0) →
    ∀ (v : ℝ≥0 → ι → E) (ev : ℝ≥0 → ι → ℝ),
      (∀ i, Continuous (fun t => v t i)) →
      (∀ t i, v t i ≠ 0) →
      (∀ t, LinearIndependent ℂ (v t)) →
      (∀ t i, ∃ h : v t i ∈ (A t).domain, A t ⟨v t i, h⟩ = (ev t i : ℂ) • v t i) →
      (Submodule.span ℂ (range (v 0))).topologicalClosure = ⊤ →
      ∀ t, (Submodule.span ℂ (range (v t))).topologicalClosure = ⊤

/-- Concrete instantiation with exactly the proved BetheContinuityInputs,
including all inverse identities; in particular valid for N+1 >= 2. -/
theorem density_from_continuity (hcont : AbstractContinuity) (L : ℝ)
    [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  obtain ⟨hsa, hpos, _hform, _hnorm, hcompact, hv, hnz, hli, heig, hzero⟩ :=
    continuity_inputs (L := L) (N := N)
  exact hcont (SymL2 L (N+1)) (Label (N+1))
    (fun t => Tinv t t.property) (resolvent (L := L)) hsa hpos
    (fun t f => ⟨mem_Tinv_domain t.property f, Tinv_Rop t.property f⟩)
    (fun t x => by
      obtain ⟨f, hf⟩ := exists_of_mem_Tinv_domain t.property x
      have hTf : Tinv (L := L) (N := N+1) (t : ℝ) t.property x = f :=
        Tinv_apply_of_eq t.property x f hf
      exact (congrArg (Rop (t : ℝ) t.property) hTf).trans hf)
    (fun s t h f => ContactFormFamily.Rop_antitone s.property t.property h f)
    resolvent_right_strong hcompact wave (fun t n => parameterEnergy t n + 1)
    hv hnz hli (fun t n => by simpa only [Complex.ofReal_add, Complex.ofReal_one] using heig t n)
    hzero c

/-- The one-particle branch has no continuity-principle dependency. -/
theorem dense (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (c : ℝ≥0) :
    (Submodule.span ℂ (range (wave (L := L) c : Label (N+1) → SymL2 L (N+1)))).topologicalClosure = ⊤ := by
  cases N with
  | zero => exact BetheBasisOneParticle.one_dense L c
  | succ n => exact density_from_continuity hcont L (n+1) c

/-- Original coordinate vector, with a harmless free definition at N=0;
all basis conclusions below require N >= 1. -/
def sourceWave (L : ℝ) [Fact (0 < L)] : (N : ℕ) → ℝ≥0 → Label N → SymL2 L N
  | 0, _, n => freeSym n
  | _+1, c, n => wave c n

/-- Literal normalization of the original vector, with positive real norm. -/
def normalizedWave (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) (n : Label N) : SymL2 L N :=
  (‖sourceWave L N c n‖⁻¹ : ℂ) • sourceWave L N c n

/-- Normalization preserves the actual unbounded Hamiltonian eigenrelation;
this proof has no abstract-continuity premise. -/
theorem unitWave_Hop_eigen (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ≥0} (hc : 0 < (c : ℝ)) (n : Label (N+1)) :
    ∃ h : unitWave (L := L) c n ∈ (Hop (L := L) c c.property).domain,
      Hop c c.property ⟨unitWave (L := L) c n, h⟩ =
        (BetheEigen.energy L c n.val : ℂ) • unitWave (L := L) c n := by
  obtain ⟨h, he⟩ := wave_Hop_eigen (L := L) c n
  simp only [parameterEnergy, ite_eq_left hc] at he
  let a : ℂ := (‖wave (L := L) c n‖⁻¹ : ℂ)
  have hm : a • wave (L := L) c n ∈ (Hop (L := L) c c.property).domain :=
    Submodule.smul_mem _ a h
  refine ⟨hm, ?_⟩
  change (Hop c c.property).toFun (a • (⟨wave (L := L) c n, h⟩ : (Hop c c.property).domain)) = _
  exact ((Hop (L := L) (c : ℝ) c.property).toFun.map_smul a _).trans
    ((congrArg (fun v : SymL2 L (N+1) => a • v) he).trans (smul_comm _ _ _))

/-- Full printed basis:thm:basis conclusion, separated from its one premise. -/
def BasisConclusion (L : ℝ) [Fact (0 < L)] (N : ℕ) (c : ℝ≥0) : Prop :=
  (∀ n, sourceWave L N c n ≠ 0) ∧
  (Submodule.span ℂ (range (sourceWave L N c))).topologicalClosure = ⊤ ∧
  (∀ n m, n ≠ m → ⟪sourceWave L N c n, sourceWave L N c m⟫_ℂ = 0) ∧
  (∀ n, ∃ h : sourceWave L N c n ∈ (Hop (L := L) c c.property).domain,
    Hop c c.property ⟨sourceWave L N c n, h⟩ =
      ((∑ j, (BetheSmooth.sourceRoots L n.val c j)^2 : ℝ) : ℂ) • sourceWave L N c n) ∧
  (∀ n, ‖normalizedWave L N c n‖ = 1) ∧
  Orthonormal ℂ (normalizedWave L N c) ∧
  (Submodule.span ℂ (range (normalizedWave L N c))).topologicalClosure = ⊤ ∧
  (∀ n, ∃ h : normalizedWave L N c n ∈ (Hop (L := L) c c.property).domain,
    Hop c c.property ⟨normalizedWave L N c n, h⟩ =
      ((∑ j, (BetheSmooth.sourceRoots L n.val c j)^2 : ℝ) : ℂ) • normalizedWave L N c n)

/-- R-8E4D05E7 conditionally, for every N >= 1, L > 0 and c > 0.
The ONLY scientific premise is the fully stated abstract principle above. -/
theorem basis (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    BasisConclusion L N ⟨c, hc.le⟩ := by
  cases N with
  | zero => omega
  | succ n =>
    change (∀ m, wave (L := L) ⟨c, hc.le⟩ m ≠ 0) ∧ _
    refine ⟨wave_ne_zero _, dense hcont L n _, fun m k h => wave_orthogonal L (c := ⟨c, hc.le⟩) hc h,
      ?_, norm_unitWave _, unitWave_orthonormal L (c := ⟨c, hc.le⟩) hc, ?_, unitWave_Hop_eigen L (c := ⟨c, hc.le⟩) hc⟩
    · intro m
      obtain ⟨hm, he⟩ := wave_Hop_eigen (L := L) (⟨c, hc.le⟩ : ℝ≥0) m
      have hp : parameterEnergy (L := L) (⟨c, hc.le⟩ : ℝ≥0) m =
          BetheEigen.energy L c m.val := ite_eq_left hc
      exact ⟨hm, he.trans (congrArg (fun r : ℝ =>
        (r : ℂ) • wave (L := L) (⟨c, hc.le⟩ : ℝ≥0) m) hp)⟩
    · change (Submodule.span ℂ (range (unitWave (L := L) ⟨c, hc.le⟩ : Label (n+1) → _))).topologicalClosure = ⊤
      exact (congrArg Submodule.topologicalClosure
        (span_unitWave L (N := n) (⟨c, hc.le⟩ : ℝ≥0))).trans (dense hcont L n _)

/-- Exact mean-field specialization c = κ/N, with no uniform-in-N estimate. -/
theorem meanField_basis (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    BasisConclusion L N ⟨κ / N, (div_pos hκ (by exact_mod_cast hN)).le⟩ :=
  basis hcont L N hN (κ / N) (div_pos hκ (by exact_mod_cast hN))

/-- Hilbert basis of the original periodic coordinate Hilbert space. -/
def coordinateBasis (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) : HilbertBasis (Label N) ℂ (SymL2 L N) :=
  HilbertBasis.mk (basis hcont L N hN c hc).2.2.2.2.2.1
    (by rw [(basis hcont L N hN c hc).2.2.2.2.2.2.1])

theorem coordinateBasis_apply (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (n : Label N) :
    coordinateBasis hcont L N hN c hc n = normalizedWave L N ⟨c, hc.le⟩ n := by
  simp only [coordinateBasis, HilbertBasis.coe_mk]

/-- Reversing enumeration, never signs, identifies the source's decreasing
integer labels with DEF-006's increasing corrected integers. -/
def reverseLabel (N : ℕ) : Label N ≃ BetheLabels.Corrected N where
  toFun n := ⟨BetheLabels.srcOf n.val, fun _i _j h => n.property (Fin.rev_le_rev.mpr h)⟩
  invFun n := ⟨BetheLabels.srcOf n.val, BetheLabels.srcOf_antitone n.property⟩
  left_inv n := Subtype.ext (BetheLabels.srcOf_srcOf n.val)
  right_inv n := Subtype.ext (BetheLabels.srcOf_srcOf n.val)

/-- Exact DEF-006 occupation-array index, including repeated momenta. -/
def labelArr (N : ℕ) : Label N ≃ BetheLabels.MArr N :=
  (reverseLabel N).trans BetheLabels.correctedEquivArr

/-- The physical Bethe Hilbert basis of Sym^N L²(T_L), indexed by MArr N.
It has precisely the type required by frozen DEF-007 (0702484d). -/
def physicalBasis (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    HilbertBasis (BetheLabels.MArr N) ℂ (physSector L N) :=
  BetheCoefficientTransform.reindexBasis (labelArr N)
    (HilbertBasis.ofRepr ((symmetricPosition L N).trans (coordinateBasis hcont L N hN c hc).repr))

/-- Each physical vector is exactly the normalized original coordinate
Bethe wave, transported by the frozen symmetric-position unitary. -/
theorem physicalBasis_position (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (m : BetheLabels.MArr N) :
    symmetricPosition L N (physicalBasis hcont L N hN c hc m) =
      normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m) := by
  classical
  rw [physicalBasis, BetheCoefficientTransform.reindexBasis_apply]
  let b := coordinateBasis hcont L N hN c hc
  let bp : HilbertBasis (Label N) ℂ (physSector L N) :=
    HilbertBasis.ofRepr ((symmetricPosition L N).trans b.repr)
  exact (b.repr.injective ((bp.repr_self ((labelArr N).symm m)).trans
    (b.repr_self ((labelArr N).symm m)).symm)).trans
      (coordinateBasis_apply hcont L N hN c hc _)

/-- Concrete instantiation of DEF-007, conditional on the same single Prop. -/
def coefficientTransform (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) :
    (physSector L N) ≃ₗᵢ[ℂ] lp (fun _ : BetheLabels.MArr N => ℂ) 2 :=
  BetheCoefficientTransform.coefficientTransform (physicalBasis hcont L N hN c hc)

theorem coefficientTransform_apply (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (ψ : physSector L N) (m : BetheLabels.MArr N) :
    coefficientTransform hcont L N hN c hc ψ m =
      ⟪normalizedWave L N ⟨c, hc.le⟩ ((labelArr N).symm m), symmetricPosition L N ψ⟫_ℂ := by
  rw [coefficientTransform, BetheCoefficientTransform.coefficientTransform_apply,
    ← (symmetricPosition L N).inner_map_map, physicalBasis_position]

/-- The physical basis object at exactly kappa/N. -/
def meanField_physicalBasis (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) {κ : ℝ} (hκ : 0 < κ) :
    HilbertBasis (BetheLabels.MArr N) ℂ (physSector L N) :=
  physicalBasis hcont L N hN (κ / N) (div_pos hκ (by exact_mod_cast hN))

/-- DEF-007's full product-state law now has the actual Bethe basis as
its argument; its mass-one conclusion uses the same single premise. -/
theorem bornLaw_hasSum_one (hcont : AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (u : L2T L) (hu : ‖u‖ = 1) :
    HasSum (BetheCoefficientTransform.bornLaw (physicalBasis hcont L N hN c hc) u) 1 :=
  BetheCoefficientTransform.hasSum_bornLaw_unit _ u hu

end QuantumNLS.BetheConditionalBasis

#print axioms QuantumNLS.BetheConditionalBasis.AbstractContinuity
#print axioms QuantumNLS.BetheConditionalBasis.density_from_continuity
#print axioms QuantumNLS.BetheConditionalBasis.dense
#print axioms QuantumNLS.BetheConditionalBasis.sourceWave
#print axioms QuantumNLS.BetheConditionalBasis.normalizedWave
#print axioms QuantumNLS.BetheConditionalBasis.unitWave_Hop_eigen
#print axioms QuantumNLS.BetheConditionalBasis.BasisConclusion
#print axioms QuantumNLS.BetheConditionalBasis.basis
#print axioms QuantumNLS.BetheConditionalBasis.meanField_basis
#print axioms QuantumNLS.BetheConditionalBasis.coordinateBasis
#print axioms QuantumNLS.BetheConditionalBasis.coordinateBasis_apply
#print axioms QuantumNLS.BetheConditionalBasis.reverseLabel
#print axioms QuantumNLS.BetheConditionalBasis.labelArr
#print axioms QuantumNLS.BetheConditionalBasis.physicalBasis
#print axioms QuantumNLS.BetheConditionalBasis.physicalBasis_position
#print axioms QuantumNLS.BetheConditionalBasis.coefficientTransform
#print axioms QuantumNLS.BetheConditionalBasis.coefficientTransform_apply

#print axioms QuantumNLS.BetheConditionalBasis.meanField_physicalBasis
#print axioms QuantumNLS.BetheConditionalBasis.bornLaw_hasSum_one

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheConditionalBasis.AbstractContinuity,
    ``QuantumNLS.BetheConditionalBasis.density_from_continuity,
    ``QuantumNLS.BetheConditionalBasis.dense,
    ``QuantumNLS.BetheConditionalBasis.sourceWave,
    ``QuantumNLS.BetheConditionalBasis.normalizedWave,
    ``QuantumNLS.BetheConditionalBasis.unitWave_Hop_eigen,
    ``QuantumNLS.BetheConditionalBasis.BasisConclusion,
    ``QuantumNLS.BetheConditionalBasis.basis,
    ``QuantumNLS.BetheConditionalBasis.meanField_basis,
    ``QuantumNLS.BetheConditionalBasis.coordinateBasis,
    ``QuantumNLS.BetheConditionalBasis.coordinateBasis_apply,
    ``QuantumNLS.BetheConditionalBasis.reverseLabel,
    ``QuantumNLS.BetheConditionalBasis.labelArr,
    ``QuantumNLS.BetheConditionalBasis.physicalBasis,
    ``QuantumNLS.BetheConditionalBasis.physicalBasis_position,
    ``QuantumNLS.BetheConditionalBasis.coefficientTransform,
    ``QuantumNLS.BetheConditionalBasis.coefficientTransform_apply,
    ``QuantumNLS.BetheConditionalBasis.meanField_physicalBasis,
    ``QuantumNLS.BetheConditionalBasis.bornLaw_hasSum_one]
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
            throwError "Conditional basis nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheContinuityInputs.continuity_inputs,
    ``QuantumNLS.BetheBasisOneParticle.one_dense,
    ``QuantumNLS.ContactFormFamily.Rop_antitone,
    ``QuantumNLS.ContactOperator.Tinv_Rop,
    ``QuantumNLS.BetheBasisOrthogonality.unitWave_orthonormal,
    ``QuantumNLS.BetheBasisOrthogonality.span_unitWave,
    ``QuantumNLS.BetheCoefficientTransform.coefficientTransform,
    ``QuantumNLS.BetheCoefficientTransform.hasSum_bornLaw_unit,
    ``QuantumNLS.BetheEigenGlobal.Hop_eigen] do
    unless seen.contains n do
      throwError "Conditional basis missing proved ingredient: {n}"
  for n in seen do
    if n == ``sorryAx || n.toString.startsWith "QuantumNLS.AbstractContinuity." then
      throwError "Conditional basis forbidden dependency: {n}"
  for root in #[``QuantumNLS.BetheConditionalBasis.unitWave_Hop_eigen,
    ``QuantumNLS.BetheBasisOneParticle.one_dense,
    ``QuantumNLS.BetheBasisOrthogonality.unitWave_orthonormal] do
    let mut check := #[root]
    let mut visited : Std.HashSet Lean.Name := {}
    while !check.isEmpty do
      let n := check.back!
      check := check.pop
      unless visited.contains n do
        visited := visited.insert n
        if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
          throwError "Unconditional clause reached abstract premise: {root}"
        if let some ci := env.find? n then
          check := check ++ ci.type.getUsedConstants
          if let some v := ci.value? (allowOpaque := true) then
            check := check ++ v.getUsedConstants
  Lean.logInfo m!"Conditional basis aggregate audit PASS: {seen.size} transitive constants. Explicit Prop premise only; actual inverse identities and all concrete inputs; independent one-particle density, orthogonality, normalization and Hamiltonian eigenrelations; physical MArr HilbertBasis and frozen DEF-007 instantiated."
