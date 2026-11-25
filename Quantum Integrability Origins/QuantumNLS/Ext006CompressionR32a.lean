import QuantumNLS.Ext006CoreMajorantR31a
import QuantumNLS.Ext006KernelHilbertSchmidt

/-! Uniform physical finite-compression estimates. The matrix is formed from
an actual continuous operator and a fixed Hilbert basis. No matrix norm is
substituted for the physical operator norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ENNReal ComplexOrder
open Matrix
namespace QuantumNLS.Ext006CompressionR32a
open Ext006CoreNorm Ext006CoreLimit TraceClass
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coordinates (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H) : ℤ → ℤ → ℂ :=
  fun i j => inner ℂ (b i) (K (b j))

def lift (b : HilbertBasis ℤ ℂ H) (S : Finset ℤ) (z : S → ℂ) : H :=
  ∑ i : S, z i • b i

omit [CompleteSpace H] in
lemma lift_norm_sq (b : HilbertBasis ℤ ℂ H) (S : Finset ℤ) (z : S → ℂ) :
    ‖lift b S z‖^2 = ∑ i : S, ‖z i‖^2 := by
  classical
  have hv : Orthonormal ℂ (fun i : S => b i) := b.orthonormal.comp _ Subtype.val_injective
  rw [@norm_sq_eq_re_inner ℂ]
  simp only [lift, sum_inner, inner_smul_left, hv.inner_right_fintype z,
    Complex.conj_mul', map_sum]
  norm_cast

omit [CompleteSpace H] in
lemma compression_apply (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (S : Finset ℤ) (z : S → ℂ) (i : S) :
    (Km S (coordinates b K) *ᵥ z) i = inner ℂ (b i) (K (lift b S z)) := by
  classical
  simp [Km, coordinates, lift, Matrix.mulVec, dotProduct, map_sum, mul_comm]

omit [CompleteSpace H] in
/-- Bessel and the physical operator bound, for every finite mode set. -/
lemma compression_norm_sq_le (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (S : Finset ℤ) (z : S → ℂ) :
    (∑ i : S, ‖(Km S (coordinates b K) *ᵥ z) i‖^2) ≤
      ‖K‖^2 * ∑ i : S, ‖z i‖^2 := by
  classical
  simp_rw [compression_apply]
  have hv : Orthonormal ℂ (fun i : S => b i) := b.orthonormal.comp _ Subtype.val_injective
  calc
    _ ≤ ‖K (lift b S z)‖^2 := hv.sum_inner_products_le _
    _ ≤ (‖K‖ * ‖lift b S z‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (K.le_opNorm _) 2
    _ = _ := by rw [mul_pow, lift_norm_sq]

lemma gram_form {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : n → ℂ) :
    (star z ⬝ᵥ ((Aᴴ * A) *ᵥ z)).re = ∑ i, ‖(A *ᵥ z) i‖^2 := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have he : star z ᵥ* Aᴴ = star (A *ᵥ z) := by
    rw [Matrix.star_mulVec]
  rw [he]
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

omit [CompleteSpace H] in
/-- Every eigenvalue of the compression square is bounded by the physical
operator norm squared, including compressions of arbitrarily large rank. -/
lemma eigenvalue_le (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (S : Finset ℤ) (i : S) :
    (Tm_posSemidef S (coordinates b K)).isHermitian.eigenvalues i ≤ ‖K‖^2 := by
  classical
  let hT := (Tm_posSemidef S (coordinates b K)).isHermitian
  let z : EuclideanSpace ℂ S := hT.eigenvectorBasis i
  have hn : ∑ j : S, ‖z j‖^2 = 1 := by
    have h := hT.eigenvectorBasis.orthonormal.1 i
    rw [← PiLp.norm_sq_eq_of_L2]
    change ‖hT.eigenvectorBasis i‖^2 = 1
    rw [h]; norm_num
  have he : hT.eigenvalues i = ∑ j : S, ‖(Km S (coordinates b K) *ᵥ (⇑z)) j‖^2 := by
    rw [hT.eigenvalues_eq]
    exact gram_form _ _
  rw [he]
  exact (compression_norm_sq_le b K S (⇑z)).trans_eq (by rw [hn, mul_one])

/-- The trace of the first compression square is bounded by the original HS
sum. The estimate uses Bessel before summing over the input basis. -/
lemma compression_trace_le (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hK : hsSq b K ≠ ⊤) (S : Finset ℤ) :
    ((Tm S (coordinates b K)).trace).re ≤ (hsSq b K).toReal := by
  classical
  have he : ((Tm S (coordinates b K)).trace).re =
      ∑ j : S, ∑ i : S, ‖coordinates b K i j‖^2 := by
    simp [Tm, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Km, Complex.conj_mul']
    norm_cast
  rw [he]
  calc
    _ ≤ ∑ j : S, ‖K (b j)‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (b.orthonormal.comp (fun i : S => (i : ℤ)) Subtype.val_injective).sum_inner_products_le _
    _ = ∑ j ∈ S, ‖K (b j)‖^2 := Finset.sum_coe_sort S (fun j => ‖K (b j)‖^2)
    _ ≤ (hsSq b K).toReal := sum_norm_sq_le b K hK S

/-- The missing r31 geometric compression-trace estimate, with no restriction
on the size of the HS sum. -/
theorem compression_trace_power_le (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hK : hsSq b K ≠ ⊤) (S : Finset ℤ) (j : ℕ) :
    (((Tm S (coordinates b K))^(j+1)).trace).re ≤ (hsSq b K).toReal * (‖K‖^2)^j := by
  classical
  let hT := (Tm_posSemidef S (coordinates b K)).isHermitian
  have hre : ∀ m : ℕ, (((Tm S (coordinates b K))^m).trace).re =
      ∑ i : S, (hT.eigenvalues i)^m := by
    intro m
    rw [trace_pow_eq_sum hT m]
    simp [← Complex.ofReal_pow]
  rw [hre]
  calc
    _ ≤ ∑ i : S, hT.eigenvalues i * (‖K‖^2)^j := by
      apply Finset.sum_le_sum
      intro i _
      have hi := (Tm_posSemidef S (coordinates b K)).eigenvalues_nonneg i
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hi (eigenvalue_le b K S i) j) hi
    _ = (∑ i : S, hT.eigenvalues i) * (‖K‖^2)^j := (Finset.sum_mul ..).symm
    _ ≤ (hsSq b K).toReal * (‖K‖^2)^j := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have ht := compression_trace_le b K hK S
      have he1 := hre 1
      simp only [pow_one] at he1
      rwa [he1] at ht

end QuantumNLS.Ext006CompressionR32a

#print axioms QuantumNLS.Ext006CompressionR32a.lift_norm_sq
#print axioms QuantumNLS.Ext006CompressionR32a.compression_norm_sq_le
#print axioms QuantumNLS.Ext006CompressionR32a.gram_form
#print axioms QuantumNLS.Ext006CompressionR32a.eigenvalue_le
#print axioms QuantumNLS.Ext006CompressionR32a.compression_trace_le
#print axioms QuantumNLS.Ext006CompressionR32a.compression_trace_power_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006CompressionR32a." then
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
  Lean.logInfo m!"Round32a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
