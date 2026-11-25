import QuantumNLS.RootEnergyMomentLaws
import QuantumNLS.ContactFormTheorem

/-! Closed coercive form Parseval, proved from the actual form topology.
This generic support lemma assumes eigenvector identities, not a moment
conclusion. Its physical application must supply all of those identities. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.RootEnergyMomentForm
variable {V E J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (F : V →L⋆[ℂ] V →L[ℂ] ℂ) (iota : V →L[ℂ] E)
  (b : HilbertBasis J ℂ E) (v : J → V) (w : J → ℝ)
  (hv : ∀ j, iota (v j) = b j)
  (hp : ∀ x j, F x (v j) = (w j : ℂ) * ⟪iota x, b j⟫_ℂ)

include hv hp

omit [CompleteSpace V] [CompleteSpace E] in
lemma finite_pair (a : J → ℂ) (s : Finset J) (j : J) (hj : j ∈ s) :
    F (∑ k ∈ s, a k • v k) (v j) = (w j : ℂ) * conj (a j) := by
  classical
  rw [hp]
  simp only [map_sum, map_smul, hv, sum_inner, inner_smul_left]
  have hb : ∀ k, ⟪b k, b j⟫_ℂ = if k = j then 1 else 0 :=
    fun k => (orthonormal_iff_ite.mp b.orthonormal) k j
  simp [hb, hj]

omit [CompleteSpace V] [CompleteSpace E] in
lemma finite_energy (a : J → ℂ) (s : Finset J) :
    F (∑ k ∈ s, a k • v k) (∑ k ∈ s, a k • v k) =
      ((∑ k ∈ s, w k * ‖a k‖^2 : ℝ) : ℂ) := by
  classical
  rw [map_sum (F (∑ k ∈ s, a k • v k))]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, smul_eq_mul, finite_pair F iota b v w hv hp a s j hj]
  rw [← mul_assoc, mul_comm (a j) (w j : ℂ), mul_assoc,
    Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]

omit [CompleteSpace E] in
/-- Parseval for a coercive continuous form with a complete eigenbasis.
Both summability and the exact form value are conclusions. -/
theorem form_parseval
    (hinj : Function.Injective iota)
    (hs : ∀ x y, conj (F x y) = F y x)
    (hco : ∀ x, ‖x‖^2 ≤ (F x x).re)
    (hw : ∀ j, 0 ≤ w j) (x : V) :
    HasSum (fun j => w j * ‖b.repr (iota x) j‖^2) (F x x).re := by
  classical
  let a := fun j => b.repr (iota x) j
  let e := fun j => w j * ‖a j‖^2
  let S := fun s : Finset J => ∑ j ∈ s, a j • v j
  have he : ∀ j, 0 ≤ e j := fun j => mul_nonneg (hw j) (sq_nonneg _)
  have hxs (s : Finset J) : F x (S s) = ((∑ j ∈ s, e j : ℝ) : ℂ) := by
    rw [show S s = ∑ j ∈ s, a j • v j from rfl, map_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul, hp]
    have hc : ⟪iota x, b j⟫_ℂ = conj (a j) := by
      dsimp only [a]
      rw [HilbertBasis.repr_apply_apply]
      exact (inner_conj_symm _ _).symm
    rw [hc]
    change a j * ((w j : ℂ) * conj (a j)) = ((w j * ‖a j‖^2 : ℝ) : ℂ)
    rw [← mul_assoc, mul_comm (a j) (w j : ℂ), mul_assoc,
      Complex.mul_conj, ← Complex.sq_norm, Complex.ofReal_pow]
    push_cast
    rfl
  have hss (s : Finset J) : F (S s) (S s) = ((∑ j ∈ s, e j : ℝ) : ℂ) :=
    finite_energy F iota b v w hv hp a s
  have hbound (s : Finset J) : ∑ j ∈ s, e j ≤ (F x x).re := by
    have hn : 0 ≤ (F (x-S s) (x-S s)).re := (sq_nonneg _).trans (hco _)
    have hsub : F (x-S s) (x-S s) = F x x - F x (S s) - F (S s) x + F (S s) (S s) := by
      simp only [map_sub, sub_apply]
      abel
    rw [hsub, ← hs x (S s), hxs, hss] at hn
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.ofReal_re] at hn
    linarith
  have hsum : Summable e := summable_of_sum_le he hbound
  have hvec : Summable (fun j => a j • v j) := by
    apply summable_iff_vanishing_norm.mpr
    intro ε hε
    obtain ⟨s, hsε⟩ := summable_iff_vanishing_norm.mp hsum (ε^2) (sq_pos_of_pos hε)
    refine ⟨s, fun t ht => ?_⟩
    have hsmall := hsε t ht
    have hnon : 0 ≤ ∑ j ∈ t, e j := Finset.sum_nonneg (fun j _ => he j)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon] at hsmall
    have hlow := hco (S t)
    rw [hss, Complex.ofReal_re] at hlow
    dsimp only [S] at hlow
    nlinarith [norm_nonneg (∑ j ∈ t, a j • v j)]
  have hval : iota (∑' j, a j • v j) = iota x := by
    have h := iota.hasSum hvec.hasSum
    simp only [map_smul, hv] at h
    exact h.unique (b.hasSum_repr (iota x))
  have hvsum : HasSum (fun j => a j • v j) x := by
    convert hvec.hasSum using 1
    exact (hinj hval).symm
  have hlim := (F x).continuous.continuousAt.tendsto.comp hvsum
  have hlimre := Complex.continuous_re.continuousAt.tendsto.comp hlim
  change Tendsto (fun s : Finset J => (F x (S s)).re) atTop (nhds (F x x).re) at hlimre
  simp_rw [hxs, Complex.ofReal_re] at hlimre
  exact hlimre

#print axioms form_parseval
end QuantumNLS.RootEnergyMomentForm

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentForm." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentForm." then
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
