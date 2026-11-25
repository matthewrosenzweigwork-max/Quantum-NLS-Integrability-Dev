import QuantumNLS.BoundedBetheTransfer
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! R-892D1666: resolution of the BCH1 maximal charge. BBT1 is read-only.
The adjoint below is mathlib's unbounded LinearPMap adjoint. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate LinearPMap
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace QuantumNLS.BetheChargeResolution
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels
open BoundedBetheTransfer Function
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Real maximal multipliers are symmetric on their full domains. -/
theorem multiplier_formalAdjoint (b : BetheBasis L N) (ev : MArr N → ℝ) :
    (multiplier b ev).IsFormalAdjoint (multiplier b ev) := by
  intro x y
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro m
  have hx := multiplier_coord b ev x m
  have hy := multiplier_coord b ev y m
  simp only [← HilbertBasis.repr_apply_apply] at hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Self-adjointness, including equality of the maximal adjoint domain.
Testing the adjoint on each basis vector forces the entire multiplied
coordinate array to lie in l2; no lower bound on the real symbol is used. -/
theorem multiplier_selfAdjoint (b : BetheBasis L N) (ev : MArr N → ℝ) :
    IsSelfAdjoint (multiplier b ev) := by
  have hd : Dense ((multiplier b ev).domain : Set (HN L N)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact domain_dense b ev
  have hle : multiplier b ev ≤ (multiplier b ev)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd (multiplier_formalAdjoint b ev)
  have hdom : (multiplier b ev)†.domain ≤ (multiplier b ev).domain := by
    intro y hy
    let z := (multiplier b ev)† ⟨y, hy⟩
    have he (m : MArr N) : b.repr z m = (ev m : ℂ) * b.repr y m := by
      have h := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩
        ⟨b m, basis_mem_domain b ev m⟩
      rw [multiplier_basis, inner_smul_right] at h
      have hh := congrArg (starRingEnd ℂ) h
      simpa only [map_mul, inner_conj_symm, Complex.conj_ofReal,
        HilbertBasis.repr_apply_apply] using hh
    change Memℓp (fun m => (ev m : ℂ) * b.repr y m) 2
    simpa only [← he] using lp.memℓp (b.repr z)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

theorem charge_selfAdjoint (b : BetheBasis L N) (c : ℝ) (r : ℕ) :
    IsSelfAdjoint (charge b c r) := multiplier_selfAdjoint b _

/-- Projection on a label subset is exactly the corresponding basis subseries. -/
theorem projection_hasSum (b : BetheBasis L N) (s : Set (MArr N)) (x : HN L N) :
    HasSum (fun m : s => b.repr x m • b m) (projection b s x) := by
  have hi : HasSum (s.indicator (fun m => b.repr x m • b m)) (projection b s x) := by
    convert (b.hasSum_repr x).mapL (projection b s) using 1
    funext m
    simp only [map_smul, projection_basis, Set.indicator_apply]
    split_ifs <;> simp
  exact hasSum_subtype_iff_indicator.mpr hi

/-- Strong countable additivity, even for arbitrary indexed disjoint families.
The proof groups an unconditionally convergent Hilbert basis subseries. -/
theorem projection_iUnion_hasSum {J : Type*} (b : BetheBasis L N)
    (s : J → Set (MArr N)) (hs : Pairwise (Disjoint on s)) (x : HN L N) :
    HasSum (fun j => projection b (s j) x) (projection b (⋃ j, s j) x) := by
  have hu := projection_hasSum b (⋃ j, s j) x
  have he := (Set.unionEqSigmaOfDisjoint hs).symm.hasSum_iff.mpr hu
  exact he.sigma (fun j => projection_hasSum b (s j) x)

/-- Label projection intersection law. -/
theorem projection_inter (b : BetheBasis L N) (s t : Set (MArr N)) :
    projection b s * projection b t = projection b (s ∩ t) := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  change b.repr (projection b s (projection b t x)) m = _
  simp only [projection_coord, Set.mem_inter_iff]
  split_ifs <;> simp_all

theorem projection_empty (b : BetheBasis L N) : projection b ∅ = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  simp [projection_coord]

theorem projection_univ (b : BetheBasis L N) : projection b Set.univ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply b.repr.injective
  ext m
  simp [projection_coord]

/-- An actual projection-valued measure: normalized, orthogonal, multiplicative,
and countably additive in the strong Hilbert topology on Borel sets. -/
structure ProjectionMeasure (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  toFun : Set ℝ → E →L[ℂ] E
  empty : toFun ∅ = 0
  univ : toFun Set.univ = 1
  selfAdjoint : ∀ s, MeasurableSet s → (toFun s).adjoint = toFun s
  inter : ∀ s t, MeasurableSet s → MeasurableSet t → toFun s * toFun t = toFun (s ∩ t)
  additive : ∀ (s : ℕ → Set ℝ), (∀ n, MeasurableSet (s n)) →
    Pairwise (Disjoint on s) → ∀ x, HasSum (fun n => toFun (s n) x) (toFun (⋃ n, s n) x)

/-- The atomic resolution on the real symbol, including repeated eigenvalues. -/
def resolution (b : BetheBasis L N) (ev : MArr N → ℝ) : ProjectionMeasure (HN L N) where
  toFun s := projection b (ev ⁻¹' s)
  empty := by simpa using projection_empty b
  univ := by simpa using projection_univ b
  selfAdjoint s _ := projection_selfAdjoint b _
  inter s t _ _ := by simpa using projection_inter b (ev ⁻¹' s) (ev ⁻¹' t)
  additive s _ hs x := by
    have hd : Pairwise (Disjoint on fun n => ev ⁻¹' s n) := fun i j hij => (hs hij).preimage ev
    simpa only [Set.preimage_iUnion] using projection_iUnion_hasSum b (fun n => ev ⁻¹' s n) hd x

/-- The atomic spectral integral of a real function, defined through the PVM's
singleton projections. The maximal domain is convergence of this vector series;
its equivalence to the weighted l2 domain is proved below. -/
def AtomicIntegralGraph (P : ProjectionMeasure (HN L N)) (f : ℝ → ℝ)
    (x y : HN L N) : Prop := HasSum (fun a : ℝ => (f a : ℂ) • P.toFun {a} x) y

/-- Each singleton projection is the full eigenspace subseries, with degeneracy. -/
theorem resolution_singleton_hasSum (b : BetheBasis L N) (ev : MArr N → ℝ)
    (x : HN L N) (a : ℝ) :
    HasSum (fun m : ev ⁻¹' {a} => b.repr x m • b m)
      ((resolution b ev).toFun {a} x) := projection_hasSum b _ x

/-- Reconstruction of the unbounded operator from its PVM's atoms. -/
theorem multiplier_atomicIntegral (b : BetheBasis L N) (ev : MArr N → ℝ)
    (x : (multiplier b ev).domain) :
    AtomicIntegralGraph (resolution b ev) id x (multiplier b ev x) := by
  unfold AtomicIntegralGraph
  have hh := (multiplier_expansion b ev x).tsum_fiberwise ev
  convert hh using 1
  funext a
  have h := HasSum.const_smul (a : ℂ) (resolution_singleton_hasSum b ev x a)
  apply h.tsum_eq.symm.trans
  congr 1
  funext m
  have hm : ev m = a := m.property
  simp only [smul_smul, hm, HilbertBasis.repr_apply_apply]


/-- Full real Borel calculus: integrate the function of the symbol on the
maximal product domain. No boundedness or finite-support hypothesis. -/
theorem calculus_atomicIntegral (b : BetheBasis L N) (ev : MArr N → ℝ)
    (f : ℝ → ℝ) (x : (multiplier b (f ∘ ev)).domain) :
    AtomicIntegralGraph (resolution b ev) f x (multiplier b (f ∘ ev) x) := by
  unfold AtomicIntegralGraph
  have hh := (multiplier_expansion b (f ∘ ev) x).tsum_fiberwise ev
  convert hh using 1
  funext a
  have h := HasSum.const_smul (f a : ℂ) (resolution_singleton_hasSum b ev x a)
  apply h.tsum_eq.symm.trans
  congr 1
  funext m
  have hm : ev m = a := m.property
  simp only [Function.comp_apply, smul_smul, hm, HilbertBasis.repr_apply_apply]

/-- Conversely, existence of the atomic spectral integral forces exactly the
BCH1 maximal domain. This rules out merely finite-core reconstruction. -/
theorem atomicIntegral_iff (b : BetheBasis L N) (ev : MArr N → ℝ)
    (f : ℝ → ℝ) (x y : HN L N) :
    AtomicIntegralGraph (resolution b ev) f x y ↔
      ∃ hx : x ∈ (multiplier b (f ∘ ev)).domain,
        multiplier b (f ∘ ev) ⟨x, hx⟩ = y := by
  constructor
  · intro h
    have he (m : MArr N) : ⟪b m, y⟫_ℂ = (f (ev m) : ℂ) * ⟪b m, x⟫_ℂ := by
      have hh : HasSum (fun a : ℝ => ⟪b m, (f a : ℂ) • (resolution b ev).toFun {a} x⟫_ℂ)
          ⟪b m, y⟫_ℂ := by
        simpa only [innerSL_apply_apply] using h.mapL (innerSL ℂ (b m))
      have hh' : HasSum (fun a : ℝ => if a = ev m then
          (f (ev m) : ℂ) * ⟪b m, x⟫_ℂ else 0) ⟪b m, y⟫_ℂ := by
        convert hh using 1
        funext a
        simp only [inner_smul_right, ← HilbertBasis.repr_apply_apply]
        change (if a = ev m then _ else 0) =
          (f a : ℂ) * b.repr (projection b (ev ⁻¹' {a}) x) m
        rw [projection_coord]
        by_cases ha : a = ev m
        · subst a; simp [HilbertBasis.repr_apply_apply]
        · simp [ha, Ne.symm ha]
      exact hh'.unique (hasSum_ite_eq (ev m) _)
    have hx : x ∈ (multiplier b (f ∘ ev)).domain :=
      (maximal b (f ∘ ev) x).mpr ⟨y, he, fun z hz => by
        apply b.repr.injective
        ext m
        simp only [HilbertBasis.repr_apply_apply]
        exact (hz m).trans (he m).symm⟩
    refine ⟨hx, ?_⟩
    exact ((calculus_atomicIntegral b ev f ⟨x, hx⟩).unique h)
  · rintro ⟨hx, rfl⟩
    exact calculus_atomicIntegral b ev f ⟨x, hx⟩

/-- A spectral resolution here is an actual normalized strongly countably
additive PVM, purely atomic, with the identity integral equal to the given
partial operator on its entire domain. -/
structure AtomicSpectralResolution (A : HN L N →ₗ.[ℂ] HN L N) where
  measure : ProjectionMeasure (HN L N)
  selfAdjoint : IsSelfAdjoint A
  completeAtoms : ∀ x, HasSum (fun a : ℝ => measure.toFun {a} x) x
  generator : ∀ x y, AtomicIntegralGraph measure id x y ↔
    ∃ hx : x ∈ A.domain, A ⟨x, hx⟩ = y

/-- The PVM really resolves the actual BCH1 maximal multiplier. -/
def spectralResolution (b : BetheBasis L N) (ev : MArr N → ℝ) :
    AtomicSpectralResolution (multiplier b ev) where
  measure := resolution b ev
  selfAdjoint := multiplier_selfAdjoint b ev
  completeAtoms x := by
    have hh := (b.hasSum_repr x).tsum_fiberwise ev
    convert hh using 1
    funext a
    exact (resolution_singleton_hasSum b ev x a).tsum_eq.symm
  generator x y := by simpa only [Function.id_comp] using atomicIntegral_iff b ev id x y

/-- Indicator functional calculus is the PVM's projection, with full domain. -/
theorem indicator_atomicIntegral (b : BetheBasis L N) (ev : MArr N → ℝ)
    (s : Set ℝ) (x : HN L N) :
    AtomicIntegralGraph (resolution b ev) (s.indicator (fun _ => (1 : ℝ))) x
      ((resolution b ev).toFun s x) := by
  apply (atomicIntegral_iff b ev _ _ _).mpr
  have hx : x ∈ (multiplier b ((s.indicator (fun _ => (1 : ℝ))) ∘ ev)).domain := by
    change Memℓp _ 2
    convert lp.memℓp (b.repr ((resolution b ev).toFun s x)) using 1
    funext m
    by_cases hm : ev m ∈ s <;> simp [resolution, projection_coord, hm]
  refine ⟨hx, ?_⟩
  apply b.repr.injective
  ext m
  rw [HilbertBasis.repr_apply_apply, multiplier_coord]
  by_cases hm : ev m ∈ s <;> simp [resolution, ← HilbertBasis.repr_apply_apply, projection_coord, hm]

/-- Distinct atoms of a PVM multiply to zero. -/
theorem atom_mul (P : ProjectionMeasure (HN L N)) (a t : ℝ) :
    P.toFun {t} * P.toFun {a} = if t = a then P.toFun {a} else 0 := by
  rw [P.inter {t} {a} (MeasurableSet.singleton _) (MeasurableSet.singleton _)]
  by_cases h : t = a
  · subst t; simp
  · have he : ({t} ∩ {a} : Set ℝ) = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨rfl, rfl⟩
      exact h rfl
    rw [he, P.empty, ite_eq_right h]

/-- The atom range lies in the corresponding eigenspace of its integral. -/
theorem atom_integral (P : ProjectionMeasure (HN L N)) (a : ℝ) (x : HN L N) :
    AtomicIntegralGraph P id (P.toFun {a} x) ((a : ℂ) • P.toFun {a} x) := by
  unfold AtomicIntegralGraph
  convert hasSum_ite_eq a ((a : ℂ) • P.toFun {a} x) using 1
  funext t
  have hm := congrArg (fun T : HN L N →L[ℂ] HN L N => T x) (atom_mul P a t)
  change (t : ℂ) • (P.toFun {t} (P.toFun {a} x)) = _
  change P.toFun {t} (P.toFun {a} x) = _ at hm
  rw [hm]
  split_ifs with ht <;> simp_all

/-- An atom away from a basis eigenvalue annihilates that basis vector.
This is derived from the actual generator, not assumed as a diagonal premise. -/
theorem resolution_atom_basis_zero (b : BetheBasis L N) (ev : MArr N → ℝ)
    (R : AtomicSpectralResolution (multiplier b ev)) (a : ℝ) (m : MArr N)
    (ha : a ≠ ev m) : R.measure.toFun {a} (b m) = 0 := by
  let P := R.measure
  let y := P.toFun {a} (b m)
  obtain ⟨hy, hAy⟩ := (R.generator y ((a : ℂ) • y)).mp (atom_integral P a (b m))
  have hc := multiplier_coord b ev ⟨y, hy⟩ m
  rw [hAy, inner_smul_right] at hc
  have hz : ⟪b m, y⟫_ℂ = 0 := by
    have hn : (a : ℂ) - (ev m : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ha)
    apply (mul_eq_zero.mp (show ((a : ℂ) - (ev m : ℂ)) * ⟪b m, y⟫_ℂ = 0 by
      linear_combination hc)).resolve_left hn
  have hp : P.toFun {a} y = y := by
    have h := congrArg (fun T : HN L N →L[ℂ] HN L N => T (b m)) (atom_mul P a a)
    change P.toFun {a} (P.toFun {a} (b m)) = (if a = a then P.toFun {a} else 0) (b m) at h
    simpa only [ite_true] using h
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪P.toFun {a} (b m), y⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, P.selfAdjoint {a} (MeasurableSet.singleton _), hp]
  exact hz

/-- Atomic completeness forces the remaining atom to fix its eigenvectors. -/
theorem resolution_atom_basis (b : BetheBasis L N) (ev : MArr N → ℝ)
    (R : AtomicSpectralResolution (multiplier b ev)) (m : MArr N) :
    R.measure.toFun {ev m} (b m) = b m := by
  have h := R.completeAtoms (b m)
  have he : (fun a : ℝ => R.measure.toFun {a} (b m)) =
      (fun a : ℝ => if a = ev m then R.measure.toFun {ev m} (b m) else 0) := by
    funext a
    split_ifs with ha
    · subst a; rfl
    · exact resolution_atom_basis_zero b ev R a m ha
  rw [he] at h
  exact (h.unique (hasSum_ite_eq (ev m) _)).symm

/-- Uniqueness of the resolution for this diagonal self-adjoint operator.
Only PVM axioms, atomic completeness and generator equality are premises;
no basis-diagonal or symbol-preimage conclusion is supplied. -/
theorem spectralResolution_unique (b : BetheBasis L N) (ev : MArr N → ℝ)
    (R : AtomicSpectralResolution (multiplier b ev)) (s : Set ℝ) (hs : MeasurableSet s) :
    R.measure.toFun s = (spectralResolution b ev).measure.toFun s := by
  apply NormalityBridge.clm_ext_basis b
  intro m
  rw [show (spectralResolution b ev).measure.toFun s = projection b (ev ⁻¹' s) from rfl,
    projection_basis]
  rw [← resolution_atom_basis b ev R m]
  have hm := congrArg (fun T : HN L N →L[ℂ] HN L N => T (b m))
    (R.measure.inter s {ev m} hs (MeasurableSet.singleton _))
  change R.measure.toFun s (R.measure.toFun {ev m} (b m)) = _ at hm
  rw [hm]
  by_cases h : ev m ∈ s
  · have he : s ∩ {ev m} = {ev m} := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr h)
    rw [he]
    simp [h]
  · have he : s ∩ {ev m} = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hz, rfl⟩
      exact h hz
    rw [he, R.measure.empty]
    simp [h]

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (hN : 0 < N)

/-- Unconditional physical spectral resolution of the actual unbounded charge. -/
def physicalChargeResolution (r : ℕ) :
    AtomicSpectralResolution (charge (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
      (κ / N) r) :=
  spectralResolution _ (eigenvalue L N (κ / N) r)

/-- The requested BBT1 bridge. The left side is a projection of a PVM whose
identity integral is the actual BCH1 charge on its maximal domain. -/
theorem physical_spectralProjection_eq_chargeProjection (r : ℕ) (s : Set ℝ)
    (_hs : MeasurableSet s) :
    (physicalChargeResolution L hκ hN r).measure.toFun s =
      chargeProjection L hκ hN r s := rfl

/-- Explicit physical generator/domain identification, without an hcont premise. -/
theorem physical_charge_integral_iff (r : ℕ) (x y : physSector L N) :
    AtomicIntegralGraph (physicalChargeResolution L hκ hN r).measure id x y ↔
      ∃ hx : x ∈ (charge (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
        (κ / N) r).domain,
        charge (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
          (κ / N) r ⟨x, hx⟩ = y :=
  (physicalChargeResolution L hκ hN r).generator x y

/-- Uniqueness form of the physical bridge: every normalized atomic PVM
with this actual maximal charge as generator gives the frozen BBT1 mask. -/
theorem physical_spectralProjection_unique (r : ℕ)
    (R : AtomicSpectralResolution (charge
      (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) (κ / N) r))
    (s : Set ℝ) (hs : MeasurableSet s) :
    R.measure.toFun s = chargeProjection L hκ hN r s :=
  spectralResolution_unique _ _ R s hs

/-- The transfer commutes with every Borel projection of every realized real
maximal diagonal charge, including the rapidity-polynomial combinations. -/
theorem transfer_commutes_spectralResolution (ev : MArr N → ℝ) (z : ℂ) (s : Set ℝ)
    (_hs : MeasurableSet s) :
    Commute (NormalizedTransfer.normalizedTransfer L κ N z)
      ((spectralResolution (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) ev).measure.toFun s) :=
  BoundedBetheTransfer.commute_projection L hκ hN z (ev ⁻¹' s)

end QuantumNLS.BetheChargeResolution

#print axioms QuantumNLS.BetheChargeResolution.multiplier_formalAdjoint
#print axioms QuantumNLS.BetheChargeResolution.multiplier_selfAdjoint
#print axioms QuantumNLS.BetheChargeResolution.charge_selfAdjoint
#print axioms QuantumNLS.BetheChargeResolution.projection_hasSum
#print axioms QuantumNLS.BetheChargeResolution.projection_iUnion_hasSum
#print axioms QuantumNLS.BetheChargeResolution.projection_inter
#print axioms QuantumNLS.BetheChargeResolution.projection_empty
#print axioms QuantumNLS.BetheChargeResolution.projection_univ
#print axioms QuantumNLS.BetheChargeResolution.ProjectionMeasure
#print axioms QuantumNLS.BetheChargeResolution.resolution
#print axioms QuantumNLS.BetheChargeResolution.AtomicIntegralGraph
#print axioms QuantumNLS.BetheChargeResolution.resolution_singleton_hasSum
#print axioms QuantumNLS.BetheChargeResolution.multiplier_atomicIntegral
#print axioms QuantumNLS.BetheChargeResolution.calculus_atomicIntegral
#print axioms QuantumNLS.BetheChargeResolution.atomicIntegral_iff
#print axioms QuantumNLS.BetheChargeResolution.AtomicSpectralResolution
#print axioms QuantumNLS.BetheChargeResolution.spectralResolution
#print axioms QuantumNLS.BetheChargeResolution.indicator_atomicIntegral
#print axioms QuantumNLS.BetheChargeResolution.atom_mul
#print axioms QuantumNLS.BetheChargeResolution.atom_integral
#print axioms QuantumNLS.BetheChargeResolution.resolution_atom_basis_zero
#print axioms QuantumNLS.BetheChargeResolution.resolution_atom_basis
#print axioms QuantumNLS.BetheChargeResolution.spectralResolution_unique
#print axioms QuantumNLS.BetheChargeResolution.physicalChargeResolution
#print axioms QuantumNLS.BetheChargeResolution.physical_spectralProjection_eq_chargeProjection
#print axioms QuantumNLS.BetheChargeResolution.physical_charge_integral_iff
#print axioms QuantumNLS.BetheChargeResolution.physical_spectralProjection_unique
#print axioms QuantumNLS.BetheChargeResolution.transfer_commutes_spectralResolution

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BetheChargeResolution." then
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
