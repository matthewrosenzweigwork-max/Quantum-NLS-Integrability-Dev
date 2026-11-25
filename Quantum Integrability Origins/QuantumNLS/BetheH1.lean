import QuantumNLS.BetheWeakGradient
import QuantumNLS.ProductWeakDerivatives
import QuantumNLS.ContactForm

/-!
Actual H¹ membership of the unnormalized coordinate Bethe function.
Source: foundations/periodic_basis.tex:24–41,245–259; DEF-005.
Frozen inputs: BetheWeakGradient 237c4704, ProductWeakDerivatives 91ec7338.
The cube and product torus carry ordinary Lebesgue measure, of mass L^N.
No gluing, normalization, nonvanishing, completeness or U5 premise is used.
-/

noncomputable section
open scoped BigOperators ContDiff InnerProductSpace ComplexConjugate
open MeasureTheory QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.ProductWeakDerivatives QuantumNLS.BetheExtension QuantumNLS.BetheWeakGradient
  QuantumNLS.Energy

namespace QuantumNLS.BetheH1

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The two partial-derivative conventions agree for every C¹ test. -/
theorem testPartial_eq_pderiv {φ : (Fin N → ℝ) → ℂ} (hφ : ContDiff ℝ 1 φ)
    (i : Fin N) : testPartial φ i = pderiv i φ := by
  funext x
  exact (pderiv_eq_fderiv (hφ.differentiable one_ne_zero) i x).symm

omit [Fact (0 < L)] in
/-- A lattice-periodic smooth test matches opposite coordinate faces exactly. -/
theorem test_faces {φ : (Fin N → ℝ) → ℂ} (hφ : LatticePeriodic L φ) (i : Fin N)
    (x : Fin N → ℝ) : φ (Function.update x i L) = φ (Function.update x i 0) := by
  have h := (latticePeriodic_iff.mp hφ) i (Function.update x i 0)
  simpa only [Function.update_self, zero_add, Function.update_idem] using h

/-- Every continuous lattice-periodic real test descends continuously to the
product torus. The compact closed cube is a quotient map, including its seams. -/
theorem continuous_liftK {φ : (Fin N → ℝ) → ℂ} (hφ : Continuous φ)
    (hp : LatticePeriodic L φ) : Continuous (liftK (L := L) φ) := by
  let P := fun x : Fin N → Set.Icc (0 : ℝ) L => fun i => ((x i : ℝ) : AddCircle L)
  have hP : Continuous P := by fun_prop
  have hs : Function.Surjective P := by
    intro y
    refine ⟨fun i => ⟨rep (y i), rep_mem (y i)⟩, ?_⟩
    funext i
    exact coe_rep (y i)
  apply (Topology.IsQuotientMap.of_surjective_continuous hs hP).continuous_iff.mpr
  have he : liftK (L := L) φ ∘ P = fun x : Fin N → Set.Icc (0 : ℝ) L =>
      φ (fun i => (x i : ℝ)) := by
    funext x
    exact liftK_coe hp _
  rw [he]
  exact hφ.comp (by fun_prop)

omit [Fact (0 < L)] in
/-- The real pullback of any torus function is lattice-periodic. -/
theorem pullback_periodic (ψ : (Fin N → AddCircle L) → ℂ) :
    LatticePeriodic L (fun x : Fin N → ℝ => ψ (fun i => (x i : AddCircle L))) := by
  intro x m
  apply congrArg ψ
  funext i
  simp [← zsmul_eq_mul]

omit [Fact (0 < L)] in
/-- Conversely a smooth real pullback is an admissible product-torus test. -/
theorem pullback_isTest (ψ : (Fin N → AddCircle L) → ℂ)
    (hs : ContDiff ℝ ∞ (fun x : Fin N → ℝ => ψ (fun i => (x i : AddCircle L)))) :
    IsTorusTest L (fun x : Fin N → ℝ => ψ (fun i => (x i : AddCircle L))) :=
  ⟨hs, pullback_periodic ψ⟩

/-- Descent followed by pullback recovers the literal smooth test everywhere. -/
theorem test_pullback {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (fun x : Fin N → ℝ => liftK (L := L) φ (fun i => (x i : AddCircle L))) = φ :=
  funext (liftK_coe hφ.periodic)

/-- The real periodic-test and continuous-torus-test presentations are
equivalent, with exactly the same smoothness of the real pullback. -/
theorem isTorusTest_iff_descent (φ : (Fin N → ℝ) → ℂ) :
    IsTorusTest L φ ↔ ∃ ψ : (Fin N → AddCircle L) → ℂ,
      Continuous ψ ∧ ContDiff ℝ ∞ (fun x : Fin N → ℝ => ψ (fun i => (x i : AddCircle L))) ∧
        (fun x : Fin N → ℝ => ψ (fun i => (x i : AddCircle L))) = φ := by
  constructor
  · intro hφ
    refine ⟨liftK (L := L) φ, continuous_liftK hφ.smooth.continuous hφ.periodic, ?_,
      test_pullback hφ⟩
    rw [test_pullback hφ]
    exact hφ.smooth
  · rintro ⟨ψ, _, hs, he⟩
    rw [← he]
    exact pullback_isTest ψ hs

/-- The frozen torus partial is precisely the lift of the classical partial. -/
theorem torusTestPartial_liftK {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ)
    (i : Fin N) : torusTestPartial L (liftK (L := L) φ) i = liftK (L := L) (pderiv i φ) := by
  unfold torusTestPartial
  rw [test_pullback hφ, testPartial_eq_pderiv
    (hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))]
  rfl

/-- Exact ordinary-measure conversion for both terms of a weak test identity.
No periodicity of the derivative is needed: the removed upper faces are null. -/
theorem integral_liftK_mul {φ : (Fin N → ℝ) → ℂ} (hφ : Continuous φ)
    (f : (Fin N → AddCircle L) → ℂ) (hf : Measurable f) :
    (∫ y, f y * liftK (L := L) φ y ∂torusPiMeasure L N) =
      ∫ x, f (fun i => (x i : AddCircle L)) * φ x ∂cubeMeasure N L := by
  have hm : Measurable (fun y => f y * φ (representatives L y)) :=
    hf.mul (hφ.measurable.comp (measurable_representatives N L))
  rw [show torusPiMeasure L N = volume from volume_pi.symm]
  change (∫ y, f y * φ (representatives L y)) = _
  rw [torus_integral_cube L _ hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [representatives_coe_ae N L] with x hx
  change f _ * φ (representatives L (fun i => (x i : AddCircle L))) = _
  rw [hx]

/-- The actual unnormalized Bethe vector, in the product-measure L² carrier. -/
def wave {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) : L2TN L (N+1) :=
  (show MemLp (torusExtension L c n) 2 (torusPiMeasure L (N+1)) by
    simpa only [volume_pi] using torusExtension_memLp (L := L) hc hn).toLp _

/-- The actual weak partial, in the same product-measure L² carrier. -/
def weakGradient (c : ℝ) (n : Fin N → ℤ) (i : Fin N) : L2TN L N :=
  (show MemLp (torusGradient L c n i) 2 (torusPiMeasure L N) by
    simpa only [volume_pi] using torusGradient_memLp L c n i).toLp _

theorem coe_wave {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (wave (L := L) hc hn : (Fin (N+1) → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L (N+1)]
      torusExtension L c n := MemLp.coeFn_toLp _

theorem coe_weakGradient (c : ℝ) (n : Fin N → ℤ) (i : Fin N) :
    (weakGradient (L := L) c n i : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      torusGradient L c n i := MemLp.coeFn_toLp _

/-- The constructed Bethe partial satisfies the exact generic smooth-test
definition; its gluing and periodic matching have already been proved. -/
theorem wave_hasWeakPartial {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i : Fin (N+1)) :
    HasWeakPartial i (wave (L := L) hc hn) (weakGradient c n i) := by
  intro φ hφ
  have hs : ContDiff ℝ 1 φ :=
    hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have he := torusExtension_weak hc hn i (liftK (L := L) φ)
    (continuous_liftK hφ.smooth.continuous hφ.periodic) (by rwa [test_pullback hφ])
  rw [torusTestPartial_liftK hφ i, volume_pi] at he
  calc
    _ = ∫ y, torusExtension L c n y * liftK (L := L) (pderiv i φ) y
        ∂torusPiMeasure L (N+1) := by
      apply integral_congr_ae
      filter_upwards [coe_wave (L := L) hc hn] with y hy
      rw [hy]
    _ = -(∫ y, torusGradient L c n i y * liftK (L := L) φ y
        ∂torusPiMeasure L (N+1)) := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [coe_weakGradient (L := L) c n i] with y hy
      rw [hy]

/-- Membership in the existing Fourier-defined physical H¹ space. -/
theorem wave_mem_range_physH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) :
    wave (L := L) hc hn ∈ Set.range (PhysH1.val : PhysH1 L (N+1) → L2TN L (N+1)) :=
  (mem_range_physH1_iff _).2 fun i => ⟨weakGradient c n i, wave_hasWeakPartial hc hn i⟩

/-- A physical H¹ element whose L² value is the literal Bethe extension. -/
def waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) : PhysH1 L (N+1) :=
  Classical.choose (wave_mem_range_physH1 (L := L) hc hn)

theorem waveH1_val {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (waveH1 (L := L) hc hn).val = wave hc hn :=
  Classical.choose_spec (wave_mem_range_physH1 (L := L) hc hn)

/-- The constructed H¹ element represents exactly the unnormalized periodic
Bethe extension, not an abstract vector with a supplied weak certificate. -/
theorem coe_waveH1_val {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ((waveH1 (L := L) hc hn).val : (Fin (N+1) → AddCircle L) → ℂ)
      =ᵐ[torusPiMeasure L (N+1)] torusExtension L c n := by
  rw [waveH1_val]
  exact coe_wave hc hn

/-- Permutation invariance of the actual L² class, including null-set transport. -/
theorem wave_perm {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (σ : Equiv.Perm (Fin (N+1))) : physPerm σ (wave (L := L) hc hn) = wave hc hn := by
  apply Lp.ext
  have hp := (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae
    (coe_wave (L := L) hc hn)
  filter_upwards [coeFn_physPerm σ (wave (L := L) hc hn), hp, coe_wave (L := L) hc hn]
    with y h1 h2 h3
  rw [h1, h2, h3]
  exact torusExtension_permute L c n y σ

/-- Actual membership in H¹_sym, rather than a conditional symmetry certificate. -/
theorem waveH1_mem_sym {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    waveH1 (L := L) hc hn ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L (N+1))) := by
  rw [PhysH1.mem_sym_iff, waveH1_val]
  exact wave_perm hc hn

/-- The resulting symmetric physical H¹ vector, with its existing carrier. -/
def waveH1Sym {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (PhysH1.sym : Submodule ℂ (PhysH1 L (N+1))) :=
  ⟨waveH1 hc hn, waveH1_mem_sym hc hn⟩

/-- The norm uses the source's ordinary measure and the constructed weak partials. -/
theorem waveH1_norm_sq {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ‖waveH1 (L := L) hc hn‖ ^ 2 = ‖wave (L := L) hc hn‖ ^ 2 +
      ∑ i, ‖weakGradient (L := L) c n i‖ ^ 2 := by
  have h := ProductWeakDerivatives.PhysH1.norm_sq_eq_weak (waveH1 (L := L) hc hn)
    (weakGradient c n) (by simpa only [waveH1_val] using wave_hasWeakPartial (L := L) hc hn)
  simpa only [waveH1_val] using h

/-- The constructed weak partial has the exact physical Fourier multiplier. -/
theorem momUnitary_weakGradient {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i : Fin (N+1)) (w : Mom (N+1)) :
    (momUnitary L (N+1) (weakGradient c n i) : Mom (N+1) → ℂ) w =
      WeakDerivatives.ikn L (w i) * (momUnitary L (N+1) (wave hc hn) : Mom (N+1) → ℂ) w :=
  momUnitary_of_hasWeakPartial (wave_hasWeakPartial hc hn i) w

/-- Identification with the existing contact form's kinetic derivative map. -/
theorem gradient_eq_I_Dj {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ}
    (hn : Antitone n) (i : Fin (N+1)) :
    momUnitary L (N+1) (weakGradient c n i) =
      Complex.I • ContactForm.Dj i (waveH1 (L := L) hc hn) := by
  apply Subtype.ext
  funext w
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [momUnitary_weakGradient hc hn, ContactForm.Dj_apply]
  unfold WeakDerivatives.ikn CollisionTrace.coeffFun
  rw [waveH1_val]
  ring

/-- The kinetic contact form paired with the Bethe vector is the actual
L² weak-gradient pairing, for every H¹ test and its weak partials. -/
theorem kinSum_waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (v : PhysH1 L (N+1)) (g : Fin (N+1) → L2TN L (N+1))
    (hg : ∀ i, HasWeakPartial i v.val (g i)) :
    ContactForm.kinSum (waveH1 (L := L) hc hn) v =
      ∑ i, ⟪weakGradient (L := L) c n i, g i⟫_ℂ := by
  unfold ContactForm.kinSum
  apply Finset.sum_congr rfl
  intro i _
  have hv : momUnitary L (N+1) (g i) = Complex.I • ContactForm.Dj i v := by
    apply Subtype.ext
    funext w
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [momUnitary_of_hasWeakPartial (hg i), ContactForm.Dj_apply]
    unfold WeakDerivatives.ikn CollisionTrace.coeffFun
    ring
  rw [← (momUnitary L (N+1)).inner_map_map, gradient_eq_I_Dj hc hn, hv]
  simp [inner_smul_left, inner_smul_right, ← mul_assoc]

/-- The full existing contact form evaluated on the actual H¹ Bethe vector.
The collision term remains the constructed trace operator; no identification
with a literal wall value or eigenvalue identity is assumed here. -/
theorem q_waveH1 {c : ℝ} (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (v : PhysH1 L (N+1)) (g : Fin (N+1) → L2TN L (N+1))
    (hg : ∀ i, HasWeakPartial i v.val (g i)) :
    ContactForm.q c (waveH1 (L := L) hc hn) v =
      (∑ i, ⟪weakGradient (L := L) c n i, g i⟫_ℂ) +
        ((2 * c : ℝ) : ℂ) * ContactForm.contactSum (waveH1 hc hn) v := by
  rw [ContactForm.q, kinSum_waveH1 hc hn v g hg]

/-- The literal second chamber partial; no boundary distribution is included. -/
def ansatzSecondPartial (c : ℝ) (q : Fin N → ℝ) (i : Fin N) (x : Fin N → ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin N), BetheWavefunctions.coefficient c (q ∘ σ) *
    (-(q (σ i) : ℂ) ^ 2 * BetheWavefunctions.planeWave (q ∘ σ) x)

/-- Each constructed chamber gradient differentiates to the literal second
partial. This is only a classical assertion within one chamber chart. -/
theorem ansatzPartial_update_hasDerivAt (c : ℝ) (q x : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    HasDerivAt (fun s => ansatzPartial c q i (Function.update x i s))
      (ansatzSecondPartial c q i (Function.update x i t)) t := by
  classical
  have h := HasDerivAt.sum (u := Finset.univ) (fun (σ : Equiv.Perm (Fin N)) _ =>
    ((planeWave_update_hasDerivAt (q ∘ σ) x i t).const_mul
      (Complex.I * (q (σ i) : ℂ))).const_mul (BetheWavefunctions.coefficient c (q ∘ σ)))
  convert h using 1
  · simp only [ansatzPartial, Finset.sum_fn]
  · unfold ansatzSecondPartial
    apply Finset.sum_congr rfl
    intro σ _
    dsimp only [Function.comp_apply]
    ring_nf
    simp [Complex.I_sq]

/-- Every term has the same free energy Σ q_j², since permutation leaves
that sum unchanged. This is the source's classical free eigenvalue equation. -/
theorem coordinateAnsatz_laplacian (c : ℝ) (q x : Fin N → ℝ) :
    (∑ i, ansatzSecondPartial c q i x) =
      -(∑ i, (q i : ℂ) ^ 2) * BetheWavefunctions.coordinateAnsatz c q x := by
  classical
  unfold ansatzSecondPartial BetheWavefunctions.coordinateAnsatz
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = ∑ i, (-(q (σ i) : ℂ) ^ 2) *
        (BetheWavefunctions.coefficient c (q ∘ σ) * BetheWavefunctions.planeWave (q ∘ σ) x) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, -(q (σ i) : ℂ) ^ 2) *
        (BetheWavefunctions.coefficient c (q ∘ σ) * BetheWavefunctions.planeWave (q ∘ σ) x) :=
      (Finset.sum_mul ..).symm
    _ = _ := by
      have hsum : (∑ i, (q (σ i) : ℂ) ^ 2) = ∑ i, (q i : ℂ) ^ 2 :=
        Equiv.sum_comp σ (fun i => (q i : ℂ) ^ 2)
      rw [Finset.sum_neg_distrib, hsum]

/-- Classical free eigenvalue equation with the printed real energy. This
does not discard the boundary terms in the global second integration by parts. -/
theorem coordinateAnsatz_free_eigen (c : ℝ) (q x : Fin N → ℝ) :
    -(∑ i, deriv (fun t => ansatzPartial c q i (Function.update x i t)) (x i)) =
      ((∑ i, q i ^ 2 : ℝ) : ℂ) * BetheWavefunctions.coordinateAnsatz c q x := by
  have hd (i : Fin N) :
      deriv (fun t => ansatzPartial c q i (Function.update x i t)) (x i) =
        ansatzSecondPartial c q i x := by
    simpa only [Function.update_eq_self] using (ansatzPartial_update_hasDerivAt c q x i (x i)).deriv
  simp_rw [hd]
  rw [coordinateAnsatz_laplacian, neg_mul, neg_neg]
  push_cast
  rfl

omit [Fact (0 < L)] in
/-- In particular the actual source rapidities and unnormalized coefficients
satisfy the free equation in their chamber chart. -/
theorem wavefunction_free_eigen (c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ) :
    -(∑ i, deriv (fun t => ansatzPartial c (BetheSmooth.sourceRoots L n c) i
      (Function.update x i t)) (x i)) =
      ((∑ i, BetheSmooth.sourceRoots L n c i ^ 2 : ℝ) : ℂ) *
        BetheWavefunctions.wavefunction L c n x :=
  coordinateAnsatz_free_eigen c (BetheSmooth.sourceRoots L n c) x

end QuantumNLS.BetheH1

#print axioms QuantumNLS.BetheH1.testPartial_eq_pderiv
#print axioms QuantumNLS.BetheH1.test_faces
#print axioms QuantumNLS.BetheH1.continuous_liftK
#print axioms QuantumNLS.BetheH1.pullback_periodic
#print axioms QuantumNLS.BetheH1.pullback_isTest
#print axioms QuantumNLS.BetheH1.test_pullback
#print axioms QuantumNLS.BetheH1.torusTestPartial_liftK
#print axioms QuantumNLS.BetheH1.integral_liftK_mul
#print axioms QuantumNLS.BetheH1.wave
#print axioms QuantumNLS.BetheH1.weakGradient
#print axioms QuantumNLS.BetheH1.coe_wave
#print axioms QuantumNLS.BetheH1.coe_weakGradient
#print axioms QuantumNLS.BetheH1.wave_hasWeakPartial
#print axioms QuantumNLS.BetheH1.wave_mem_range_physH1
#print axioms QuantumNLS.BetheH1.waveH1
#print axioms QuantumNLS.BetheH1.waveH1_val
#print axioms QuantumNLS.BetheH1.wave_perm
#print axioms QuantumNLS.BetheH1.waveH1_mem_sym
#print axioms QuantumNLS.BetheH1.waveH1Sym
#print axioms QuantumNLS.BetheH1.waveH1_norm_sq
#print axioms QuantumNLS.BetheH1.momUnitary_weakGradient
#print axioms QuantumNLS.BetheH1.gradient_eq_I_Dj
#print axioms QuantumNLS.BetheH1.kinSum_waveH1
#print axioms QuantumNLS.BetheH1.q_waveH1
#print axioms QuantumNLS.BetheH1.isTorusTest_iff_descent
#print axioms QuantumNLS.BetheH1.coe_waveH1_val
#print axioms QuantumNLS.BetheH1.ansatzSecondPartial
#print axioms QuantumNLS.BetheH1.ansatzPartial_update_hasDerivAt
#print axioms QuantumNLS.BetheH1.coordinateAnsatz_laplacian
#print axioms QuantumNLS.BetheH1.coordinateAnsatz_free_eigen
#print axioms QuantumNLS.BetheH1.wavefunction_free_eigen
