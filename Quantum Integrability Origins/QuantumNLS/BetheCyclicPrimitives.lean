import QuantumNLS.BethePrimitiveTransport

/-! Cyclic transport of every denominator in a partially integrated source
wave. These equalities follow from the on-shell term identity, rather than
assuming periodicity of primitives. They do not enumerate all physical
iterated faces or prove cancellation of the full transfer sum. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheCyclicPrimitives
open BetheWavefunctions BetheInternalFaces BethePeriodic BetheSmooth

/-- Pull original coordinate labels back through the cyclic relocation. -/
def rotateActive {N : ℕ} (A : Finset (Fin (N+1))) : Finset (Fin (N+1)) :=
  A.image (finRotate (N+1)).symm

/-- Covariant denominator transport for an arbitrary coordinate permutation.
The rapidities themselves are never negated or rescaled. -/
theorem denominator_relabel {N : ℕ} (z : ℂ) (q : Fin N → ℝ)
    (e : Equiv.Perm (Fin N)) (A : Finset (Fin N)) :
    denominator z (q ∘ e) (A.image e.symm) = denominator z q A := by
  classical
  unfold denominator
  rw [Finset.prod_image (fun _ _ _ _ h => e.symm.injective h)]
  simp

theorem rotateActive_insert {N : ℕ} (A : Finset (Fin (N+1))) (a : Fin (N+1)) :
    rotateActive (insert a A) = insert ((finRotate (N+1)).symm a) (rotateActive A) := by
  classical
  exact Finset.image_insert _ _ _

theorem card_rotateActive {N : ℕ} (A : Finset (Fin (N+1))) :
    (rotateActive A).card = A.card := by
  classical
  exact Finset.card_image_of_injective _ (finRotate (N+1)).symm.injective

theorem mem_rotateActive {N : ℕ} (A : Finset (Fin (N+1))) (a : Fin (N+1)) :
    a ∈ rotateActive A ↔ finRotate (N+1) a ∈ A := by
  classical
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    rw [← he]
    simpa only [Equiv.apply_symm_apply] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨finRotate (N+1) a,h,(finRotate (N+1)).symm_apply_apply a⟩

/-- Every finite primitive denominator, including a denominator for the
crossing coordinate, follows the same cyclic assignment bijection. Root
avoidance is unnecessary for this algebraic equality of totalized products. -/
theorem source_primitive_periodic {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x : Fin N → ℝ) (t : ℝ)
    (z : ℂ) (A : Finset (Fin (N+1))) :
    primitive c (sourceRoots L n c) (Fin.cons (L+t) x) z A =
      primitive c (sourceRoots L n c) (Fin.snoc x t) z (rotateActive A) := by
  classical
  unfold primitive
  rw [← (rotatePermutation_bijective N).sum_comp
    (fun σ : Equiv.Perm (Fin (N+1)) =>
      coefficient c (sourceRoots L n c ∘ σ) *
        planeWave (sourceRoots L n c ∘ σ) (Fin.snoc x t) *
        denominator z (sourceRoots L n c ∘ σ) (rotateActive A))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [sourceRoots_term_periodic hL hc hn]
  have hd := denominator_relabel z (sourceRoots L n c ∘ σ) (finRotate (N+1)) A
  change denominator z (sourceRoots L n c ∘ rotatePermutation σ) (rotateActive A) =
    denominator z (sourceRoots L n c ∘ σ) A at hd
  rw [hd]

/-- Actual exterior 0/L traces with the transported pending set. -/
theorem source_primitive_outer_faces {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    (z : ℂ) (A : Finset (Fin (N+1))) :
    primitive c (sourceRoots L n c) (Fin.cons L x) z A =
      primitive c (sourceRoots L n c) (Fin.snoc x 0) z (rotateActive A) := by
  simpa using source_primitive_periodic hL hc hn x 0 z A

/-- The original full lower-branch phase cancels against the displacement
change. Every primitive denominator is retained in the paired outer term. -/
theorem source_primitive_outer_cancel {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin (N+1) → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    (z : ℂ) (A : Finset (Fin (N+1))) (d : ℝ) :
    Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*(d-L)) *
        primitive c (sourceRoots L n c) (Fin.cons L x) z A -
      Complex.exp (Complex.I*z*d) *
        primitive c (sourceRoots L n c) (Fin.snoc x 0) z (rotateActive A) = 0 := by
  rw [source_primitive_outer_faces hL hc hn, ← Complex.exp_add]
  have he : Complex.I*z*(L : ℂ) + Complex.I*z*((d : ℂ)-(L : ℂ)) = Complex.I*z*d := by
    ring
  rw [he,sub_self]

/-- Integration of the literal paired residual on any common parameter
measure needs no unsupported ambient-a.e. boundary inference. -/
theorem integral_source_primitive_outer_cancel {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (x : α → Fin N → ℝ)
    (d : α → ℝ) (z : ℂ) (A : Finset (Fin (N+1))) :
    (∫ u, Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*(d u-L)) *
        primitive c (sourceRoots L n c) (Fin.cons L (x u)) z A -
      Complex.exp (Complex.I*z*d u) *
        primitive c (sourceRoots L n c) (Fin.snoc (x u) 0) z (rotateActive A) ∂μ) = 0 := by
  simp_rw [source_primitive_outer_cancel hL hc hn]
  exact integral_zero _ _

/-- The crossing input 0 becomes the last input; all other pending labels
are transported by the same inverse rotation. -/
theorem rotateActive_insert_zero {N : ℕ} (A : Finset (Fin (N+1))) :
    rotateActive (insert 0 A) = insert (Fin.last N) (rotateActive A) := by
  rw [rotateActive_insert]
  congr 1


/-- Exterior endpoint terms produced by two ordinary primitive integrations
cancel between the original lower and upper branches. The two remaining
interior endpoints are displayed, and are not assumed to vanish. -/
theorem integral_source_primitive_outer_pair {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (z : ℂ) (hz : ∀ k, z ≠ (sourceRoots L n c k : ℂ))
    (A : Finset (Fin (N+1))) (ha : 0 ∉ A) (u lo hi : ℝ) :
    Complex.exp (Complex.I*z*L) *
      (∫ t in lo..L, Complex.exp (Complex.I*z*(u-t)) *
        primitive c (sourceRoots L n c) (Fin.cons t x) z A) +
      (∫ t in 0..hi, Complex.exp (Complex.I*z*(u-t)) *
        primitive c (sourceRoots L n c) (Fin.snoc x t) z (rotateActive A)) =
      Complex.exp (Complex.I*z*(u-hi)) *
        primitive c (sourceRoots L n c) (Fin.snoc x hi) z (insert (Fin.last N) (rotateActive A)) -
      Complex.exp (Complex.I*z*L) * Complex.exp (Complex.I*z*(u-lo)) *
        primitive c (sourceRoots L n c) (Fin.cons lo x) z (insert 0 A) := by
  have hb : Fin.last N ∉ rotateActive A := by
    rw [mem_rotateActive, finRotate_last]
    exact ha
  have ht (t : ℝ) : Function.update (Fin.cons (α := fun _ => ℝ) (0 : ℝ) x) 0 t = Fin.cons (α := fun _ => ℝ) t x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hb' (t : ℝ) : Function.update (Fin.snoc (α := fun _ => ℝ) x (0 : ℝ)) (Fin.last N) t = Fin.snoc (α := fun _ => ℝ) x t := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have h1 := BetheCrossDegreeFaces.integral_primitive_update c (sourceRoots L n c)
    (Fin.cons (α := fun _ => ℝ) 0 x) (0 : Fin (N+1)) z hz A ha u lo L
  have h2 := BetheCrossDegreeFaces.integral_primitive_update c (sourceRoots L n c)
    (Fin.snoc x 0) (Fin.last N) z hz (rotateActive A) hb u 0 hi
  simp_rw [ht] at h1
  simp_rw [hb'] at h2
  rw [h1,h2]
  have hf := source_primitive_outer_cancel hL hc hn x z (insert 0 A) u
  rw [rotateActive_insert_zero] at hf
  simp only [Complex.ofReal_zero, sub_zero]
  linear_combination hf

end QuantumNLS.BetheCyclicPrimitives

#print axioms QuantumNLS.BetheCyclicPrimitives.rotateActive
#print axioms QuantumNLS.BetheCyclicPrimitives.denominator_relabel
#print axioms QuantumNLS.BetheCyclicPrimitives.rotateActive_insert
#print axioms QuantumNLS.BetheCyclicPrimitives.card_rotateActive
#print axioms QuantumNLS.BetheCyclicPrimitives.mem_rotateActive
#print axioms QuantumNLS.BetheCyclicPrimitives.source_primitive_periodic
#print axioms QuantumNLS.BetheCyclicPrimitives.source_primitive_outer_faces
#print axioms QuantumNLS.BetheCyclicPrimitives.source_primitive_outer_cancel
#print axioms QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_cancel

#print axioms QuantumNLS.BetheCyclicPrimitives.rotateActive_insert_zero
#print axioms QuantumNLS.BetheCyclicPrimitives.integral_source_primitive_outer_pair
