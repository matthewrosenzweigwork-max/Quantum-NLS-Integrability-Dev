import QuantumNLS.BetheEigenGlobal
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Roots

/-!
Printed separating-line Vandermonde argument, periodic_basis.tex:277–286.
The imported global identity is frozen at 6a958295 and is never changed.
Only the elementary chamber and root-separation results from that module
are used in the independence proof. No continuation or character theorem
is used. The coefficients and physical vectors retain their literal values.
-/
noncomputable section
open scoped BigOperators Topology InnerProductSpace
open Filter MeasureTheory Set
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheExtension
  QuantumNLS.BetheWeakGradient QuantumNLS.BetheH1 QuantumNLS.BetheEigen

namespace QuantumNLS.BetheVandermonde

/-- A moment-curve direction separates any finite set of real vectors:
the exceptional parameters are roots of finitely many nonzero polynomials. -/
theorem separating_direction {I : Type*} [Fintype I] {N : ℕ}
    (q : I → Fin N → ℝ) (hq : Function.Injective q) :
    ∃ v : Fin N → ℝ, Function.Injective (fun a => ∑ j, q a j * v j) := by
  classical
  let P (a : I) : Polynomial ℝ := ∑ j : Fin N, Polynomial.monomial j.val (q a j)
  have hcoeff (a : I) (j : Fin N) : (P a).coeff j.val = q a j := by
    simp [P, Polynomial.coeff_monomial, Fin.val_inj]
  have hp : Function.Injective P := by
    intro a b h
    apply hq
    funext j
    have := congrArg (fun p : Polynomial ℝ => p.coeff j.val) h
    simpa only [hcoeff] using this
  have hav (a b : I) : ∀ᶠ t : ℝ in Filter.cofinite,
      a ≠ b → (P a).eval t ≠ (P b).eval t := by
    by_cases hab : a = b
    · simp [hab]
    · filter_upwards [Polynomial.eventually_eval_ne_zero_cofinite
        (sub_ne_zero.mpr (fun h => hab (hp h)))] with t ht _
      simpa only [Polynomial.eval_sub, sub_ne_zero] using ht
  have hall : ∀ᶠ t : ℝ in Filter.cofinite, ∀ a b : I,
      a ≠ b → (P a).eval t ≠ (P b).eval t :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 (hav a)
  obtain ⟨t, ht⟩ := hall.exists
  refine ⟨fun j => t ^ j.val, ?_⟩
  intro a b hab
  by_contra hne
  apply ht a b hne
  simpa [P, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using hab

/-- Differentiating a finite exponential relation on a real neighbourhood
produces every row of the one-dimensional Vandermonde system. -/
theorem exponential_moments {I : Type*} [Fintype I] (z a : I → ℂ)
    (hz : (fun t : ℝ => ∑ i, a i * Complex.exp (z i * (t : ℂ))) =ᶠ[𝓝 0] 0) :
    ∀ k : ℕ, ∑ i, a i * z i ^ k = 0 := by
  classical
  let F (k : ℕ) (t : ℝ) := ∑ i, (a i * z i ^ k) * Complex.exp (z i * (t : ℂ))
  have hd (k : ℕ) : deriv (F k) = F (k+1) := by
    funext t
    have he (i : I) : HasDerivAt (fun t : ℝ => Complex.exp (z i * (t : ℂ)))
        (Complex.exp (z i * (t : ℂ)) * z i) t := by
      convert ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_id t)).const_mul (z i)).cexp using 1 <;> simp
    have hh := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (he i).const_mul (a i * z i ^ k))
    convert hh.deriv using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [pow_succ]
    ring
  have hF (k : ℕ) : F k =ᶠ[𝓝 0] 0 := by
    induction k with
    | zero => simpa [F] using hz
    | succ k ih =>
      have h := ih.deriv
      simpa only [hd, deriv_zero] using h
  intro k
  have h := (hF k).eq_of_nhds
  simpa [F] using h

/-- The square Vandermonde determinant forces every coefficient to vanish.
Only a local relation on the real line is required. -/
theorem exponential_relation {I : Type*} [Fintype I] (z a : I → ℂ)
    (hz : Function.Injective z)
    (hzero : (fun t : ℝ => ∑ i, a i * Complex.exp (z i * (t : ℂ))) =ᶠ[𝓝 0] 0) :
    ∀ i, a i = 0 := by
  classical
  let e := Fintype.equivFin I
  have hm := exponential_moments z a hzero
  have hv : (fun j : Fin (Fintype.card I) => a (e.symm j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (hz.comp e.symm.injective)
    intro k
    simpa only [← Equiv.sum_comp e.symm, Function.comp_apply] using hm k.val
  intro i
  have := congrFun hv (e i)
  simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using this

/-- Restrict to a segment through an interior point, separate the real
frequencies, differentiate at its centre, and solve the Vandermonde system. -/
theorem planeWaves_chamber_relation {I : Type*} [Fintype I] {N : ℕ} {L : ℝ}
    (hL : 0 < L) (q : I → Fin N → ℝ) (hq : Function.Injective q) (a : I → ℂ)
    (hzero : ∀ x ∈ chamber N L, ∑ i, a i * planeWave (q i) x = 0) :
    ∀ i, a i = 0 := by
  classical
  obtain ⟨v, hv⟩ := separating_direction q hq
  obtain ⟨x, hx⟩ := BetheEigenGlobal.chamber_nonempty hL N
  let line (t : ℝ) : Fin N → ℝ := fun j => x j + t * v j
  have hline : Continuous line := by unfold line; fun_prop
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), line t ∈ chamber N L := by
    have hx0 : line 0 ∈ chamber N L := by simpa [line] using hx
    exact hline.continuousAt.preimage_mem_nhds
      ((BetheEigenGlobal.isOpen_chamber N L).mem_nhds hx0)
  let z (i : I) : ℂ := Complex.I * ((∑ j, q i j * v j : ℝ) : ℂ)
  let b (i : I) : ℂ := a i * planeWave (q i) x
  have hz : Function.Injective z := by
    intro i j h
    exact hv (Complex.ofReal_injective (mul_left_cancel₀ Complex.I_ne_zero h))
  have hf (i : I) (t : ℝ) : planeWave (q i) (line t) =
      planeWave (q i) x * Complex.exp (z i * (t : ℂ)) := by
    have hs : (∑ j, q i j * (x j + t * v j)) =
        (∑ j, q i j * x j) + t * (∑ j, q i j * v j) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    change Complex.exp (Complex.I * ((∑ j, q i j * (x j + t * v j) : ℝ) : ℂ)) = _
    rw [hs, Complex.ofReal_add, Complex.ofReal_mul, mul_add, Complex.exp_add]
    congr 2
    dsimp [z]
    ring
  have hb : (fun t : ℝ => ∑ i, b i * Complex.exp (z i * (t : ℂ))) =ᶠ[𝓝 0] 0 := by
    filter_upwards [hmem] with t ht
    simpa only [hf, mul_assoc, b, Pi.zero_apply] using hzero (line t) ht
  have he := exponential_relation z b hz hb
  intro i
  exact (mul_eq_zero.1 (he i)).resolve_right (Complex.exp_ne_zero _)

/-- The literal scattering coefficients and distinct permutation frequencies
force a nonzero value somewhere in the source chamber. -/
theorem coordinateAnsatz_chamber_nonzero {N : ℕ} {L : ℝ} (hL : 0 < L)
    (c : ℝ) (q : Fin N → ℝ) (hq : Function.Injective q) :
    ∃ x ∈ chamber N L, coordinateAnsatz c q x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hi : Function.Injective (fun σ : Equiv.Perm (Fin N) => q ∘ σ) := by
    intro σ τ he
    apply Equiv.ext
    intro j
    exact hq (congrFun he j)
  have he := planeWaves_chamber_relation hL (fun σ : Equiv.Perm (Fin N) => q ∘ σ)
    hi (fun σ => coefficient c (q ∘ σ)) h
  exact coefficient_ne_zero c _ (he (Equiv.refl _))

/-- A finite relation of source Bethe sums unfolds into one finite relation
with pairwise distinct real frequencies and nonzero scattering factors. -/
theorem chamber_ansatz_independent {I : Type*} [Fintype I] {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) (n : I → Fin N → ℤ)
    (hn : ∀ a, Antitone (n a)) (hinj : Function.Injective n) (g : I → ℂ)
    (hzero : ∀ x ∈ chamber N L, ∑ a, g a * wavefunction L c (n a) x = 0) :
    ∀ a, g a = 0 := by
  classical
  let Q : I × Equiv.Perm (Fin N) → Fin N → ℝ :=
    fun p => BetheSmooth.sourceRoots L (n p.1) c ∘ p.2
  have hq : Function.Injective Q :=
    BetheEigenGlobal.joint_frequencies_injective hL hc n hn hinj
  have hp (x : Fin N → ℝ) (hx : x ∈ chamber N L) :
      (∑ p : I × Equiv.Perm (Fin N), (g p.1 * coefficient c (Q p)) * planeWave (Q p) x) = 0 := by
    rw [Fintype.sum_prod_type]
    simpa only [wavefunction, coordinateAnsatz, Finset.mul_sum, mul_assoc, Q] using hzero x hx
  have he := planeWaves_chamber_relation hL Q hq (fun p => g p.1 * coefficient c (Q p)) hp
  intro a
  exact (mul_eq_zero.1 (he (a, Equiv.refl _))).resolve_right (coefficient_ne_zero c _)

/-- Literal nonvanishing of the actual, unnormalized Bethe L² vector. -/
theorem wave_ne_zero {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (waveH1 (L := L) hc hn).val ≠ 0 := by
  intro hz
  have hae : torusExtension L c n =ᵐ[torusPiMeasure L (N+1)] 0 := by
    have he := coe_waveH1_val (L := L) hc hn
    rw [hz] at he
    exact he.symm.trans (Lp.coeFn_zero ℂ 2 _)
  have heq : torusExtension L c n = 0 :=
    Measure.eq_of_ae_eq hae (continuous_torusExtension hc hn) continuous_const
  obtain ⟨x, hx, hne⟩ := coordinateAnsatz_chamber_nonzero (Fact.out : 0 < L) c
    (BetheSmooth.sourceRoots L n c) (BetheSmooth.sourceRoots_strictAnti (Fact.out : 0 < L) hc hn).injective
  apply hne
  change wavefunction L c n x = 0
  rw [← periodicExtension_chamber L c n hx]
  exact congrFun heq (fun i => (x i : AddCircle L))

/-- The same literal nonvanishing on the source's symmetric Hilbert space. -/
theorem valSym_ne_zero {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    ContactOperator.valSym (waveH1Sym (L := L) hc hn) ≠ 0 := by
  intro h
  exact wave_ne_zero hc hn (congrArg (fun x : ContactOperator.SymL2 L (N+1) => (x : L2TN L (N+1))) h)


/-- A finite L² linear relation gives a literal zero relation on the chamber.
The passage from classes to functions uses continuity and positive measure
of nonempty open subsets of the ordinary product torus. -/
theorem finite_waves_independent {I : Type*} [Fintype I] {N : ℕ}
    {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    (n : I → Fin (N+1) → ℤ) (hn : ∀ a, Antitone (n a)) (hinj : Function.Injective n) :
    LinearIndependent ℂ (fun a => (waveH1 (L := L) hc (hn a)).val) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro g hg
  let F : (Fin (N+1) → AddCircle L) → ℂ := fun x =>
    ∑ a, g a * torusExtension L c (n a) x
  have hF : Continuous F := continuous_finsetSum _ fun a _ =>
    continuous_const.mul (continuous_torusExtension hc (hn a))
  have hvals (a : I) :
      ((g a • (waveH1 (L := L) hc (hn a)).val : L2TN L (N+1)) : (Fin (N+1) → AddCircle L) → ℂ)
        =ᵐ[torusPiMeasure L (N+1)] (fun x => g a * torusExtension L c (n a) x) := by
    filter_upwards [Lp.coeFn_smul (g a) (waveH1 (L := L) hc (hn a)).val,
      coe_waveH1_val (L := L) hc (hn a)] with x hx hv
    rw [hx, Pi.smul_apply, smul_eq_mul, hv]
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun a => g a • (waveH1 (L := L) hc (hn a)).val)
  rw [hg] at hsum
  have hae : F =ᵐ[torusPiMeasure L (N+1)] 0 := by
    filter_upwards [hsum, Filter.eventually_all.2 hvals, Lp.coeFn_zero ℂ 2 (torusPiMeasure L (N+1))]
      with x hx hv hz
    change (∑ a, g a * torusExtension L c (n a) x) = 0
    calc
      _ = ∑ a, ((g a • (waveH1 (L := L) hc (hn a)).val : L2TN L (N+1)) :
          (Fin (N+1) → AddCircle L) → ℂ) x := Finset.sum_congr rfl fun a _ => (hv a).symm
      _ = (0 : L2TN L (N+1)) x := by
        simpa only [Finset.sum_apply] using hx.symm
      _ = 0 := hz
  have heq : F = 0 := Measure.eq_of_ae_eq hae hF continuous_const
  apply chamber_ansatz_independent (Fact.out : 0 < L) hc n hn hinj g
  intro x hx
  have he := congrFun heq (fun i => (x i : AddCircle L))
  dsimp only [F] at he
  have hp (a : I) : torusExtension L c (n a) (fun i => (x i : AddCircle L)) =
      wavefunction L c (n a) x := periodicExtension_chamber L c (n a) hx
  simpa only [hp, Pi.zero_apply] using he

/-- Literal linear independence of the unnormalized Bethe vectors for c>0,
indexed by all antitone integer labels. No normalization, orthogonality,
energy separation, or completeness premise is used. -/
theorem waves_independent {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c) :
    LinearIndependent ℂ (fun n : {n : Fin (N+1) → ℤ // Antitone n} =>
      (waveH1 (L := L) hc n.property).val) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact finite_waves_independent hc (fun a : s => a.val.val) (fun a => a.val.property)
    (Subtype.val_injective.comp Subtype.val_injective)



/-- The BE1 remainder, for every positive particle number: the global H¹
weak identity, actual operator-domain/eigenvalue equation, and literal
nonvanishing of the same unnormalized symmetric Bethe vector. -/
theorem bethe_eigenvector {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    (∀ φ : ContactOperator.VSym L (N+1),
      ContactForm.q c φ.1 (waveH1 (L := L) hc hn) =
        (energy L c n : ℂ) * ⟪φ.1.val, (waveH1 (L := L) hc hn).val⟫_ℂ) ∧
    (∃ h : (ContactOperator.valSym (waveH1Sym (L := L) hc hn) : ContactOperator.SymL2 L (N+1)) ∈
        (ContactOperator.Hop c hc.le).domain,
      ContactOperator.Hop c hc.le ⟨ContactOperator.valSym (waveH1Sym hc hn), h⟩ =
        (energy L c n : ℂ) • ContactOperator.valSym (waveH1Sym hc hn)) ∧
    ContactOperator.valSym (waveH1Sym (L := L) hc hn) ≠ 0 :=
  ⟨BetheEigenGlobal.weak_eigen hc hn, BetheEigenGlobal.Hop_eigen hc hn, valSym_ne_zero hc hn⟩

end QuantumNLS.BetheVandermonde

#print axioms QuantumNLS.BetheVandermonde.separating_direction
#print axioms QuantumNLS.BetheVandermonde.exponential_moments
#print axioms QuantumNLS.BetheVandermonde.exponential_relation
#print axioms QuantumNLS.BetheVandermonde.planeWaves_chamber_relation
#print axioms QuantumNLS.BetheVandermonde.coordinateAnsatz_chamber_nonzero
#print axioms QuantumNLS.BetheVandermonde.chamber_ansatz_independent
#print axioms QuantumNLS.BetheVandermonde.wave_ne_zero
#print axioms QuantumNLS.BetheVandermonde.valSym_ne_zero
#print axioms QuantumNLS.BetheVandermonde.finite_waves_independent
#print axioms QuantumNLS.BetheVandermonde.waves_independent
#print axioms QuantumNLS.BetheVandermonde.bethe_eigenvector

/- Executable dependency inspection; adds no mathematical premise. -/
set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let forbidden : Array Lean.Name := #[
    ``QuantumNLS.BetheEigenGlobal.planeCharacter,
    ``QuantumNLS.BetheEigenGlobal.planeCharacter_injective,
    ``QuantumNLS.BetheEigenGlobal.planeCharacters_independent,
    ``QuantumNLS.BetheEigenGlobal.coordinateAnsatz_not_zero,
    ``QuantumNLS.BetheEigenGlobal.analyticAt_coordinateAnsatz,
    ``QuantumNLS.BetheEigenGlobal.coordinateAnsatz_chamber_nonzero,
    ``QuantumNLS.BetheEigenGlobal.wave_ne_zero,
    ``QuantumNLS.BetheEigenGlobal.valSym_ne_zero,
    ``QuantumNLS.BetheEigenGlobal.chamber_ansatz_independent,
    ``QuantumNLS.BetheEigenGlobal.finite_waves_independent,
    ``QuantumNLS.BetheEigenGlobal.waves_independent,
    ``QuantumNLS.BetheEigenGlobal.bethe_eigenvector,
    ``linearIndependent_monoidHom]
  let mut pending := #[``QuantumNLS.BetheVandermonde.bethe_eigenvector,
    ``QuantumNLS.BetheVandermonde.waves_independent]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if forbidden.contains n then
        throwError "Vandermonde route reached forbidden alternate proof: {n}"
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheVandermonde.separating_direction,
      ``QuantumNLS.BetheVandermonde.exponential_moments,
      ``Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero,
      ``Matrix.det_vandermonde,
      ``QuantumNLS.BetheEigenGlobal.joint_frequencies_injective,
      ``QuantumNLS.BetheEigenGlobal.weak_eigen,
      ``QuantumNLS.BetheEigenGlobal.Hop_eigen] do
    unless seen.contains n do
      throwError "Vandermonde route missed required step: {n}"
  Lean.logInfo m!"Vandermonde route PASS: {seen.size} transitive constants; separating line, differentiated moments, Vandermonde determinant, label disjointness, frozen weak/operator identity reached; 13 alternate proof declarations excluded."
