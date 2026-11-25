import QuantumNLS.CountFunctionsS01Calc
import QuantumNLS.FullWickH4

/-!
# CountFunctionsS01Sym: strong symbols of `f(B_{N,J})` and the scaled finite difference

PRINTED SOURCES
* `source-text/chapters/principal_correspondence.tex:42` : "Every fixed ordered word in these bounded observables,
  their adjoints, and continuous functions of finitely many intensive counts has the product of the corresponding
  scalar symbols, in the same strong and compact-time-uniform sense."
* `source-text/chapters/core/canonical_algebra.tex:54` : "Count functions follow by bounded convergence under the
  invariant occupation law."

`count_strong` / `count_pair` (generic in the sector index `Nn`, Bethe basis family `b`, gauge `g`, preparation
family `ψ`, and classical point `a ∈ cube J`): if the diagonal transfers `E^q_{N,jj} = B_{N,j}`, `j ∈ J`, have the
uniform strong symbols `a_j`, then `f(B_{N,J})` has the uniform strong symbol `f(a_J)` for every `f` continuous on
the cube (and its adjoint `conj f(B)` the conjugate symbol).  The proof is the spectral Chebyshev estimate
`CountFunctionsS01Ops.countOp_sub_le` (the functional calculus is diagonal in the Bethe basis); no property of the
preparation is used except `‖ψ‖ ≤ 1`, and the symbol points are only required to lie in `[0,1]^J`.

No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open QuantumNLS Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge
open QuantumNLS.CountFunctionsS01Ops QuantumNLS.CountFunctionsS01Calc
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)

namespace QuantumNLS.CountFunctionsS01Sym

variable {L : ℝ} [Fact (0 < L)] {X Θ : Type*}

/-- **Strong symbol of `f(B_{N,J})`.** -/
theorem count_strong (Nn : ℕ → ℕ) (b : ∀ n, BetheBasis L (Nn n)) (g : Gauge) (J : Finset ℤ)
    {f : (↥J → ℝ) → ℂ} (hf : ContinuousOn f (cube J)) (S : Set X) (Tb : Set Θ)
    (ψ : X → Θ → ∀ n, HN L (Nn n)) (a : X → Θ → (↥J → ℝ))
    (ha : ∀ u ∈ S, ∀ t ∈ Tb, a u t ∈ cube J)
    (hψ : ∀ᶠ n in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t n‖ ≤ 1)
    (hB : ∀ j : ↥J, HasUniformStrongT (H := fun n => HN L (Nn n))
      (fun n => CartesianOccupationTransfer.physical (b n) g (j : ℤ) (j : ℤ)) S Tb ψ
      (fun u t => ((a u t j : ℝ) : ℂ))) :
    HasUniformStrongT (H := fun n => HN L (Nn n)) (fun n => countOp (b n) g J f) S Tb ψ
      (fun u t => f (a u t)) := by
  intro ε hε
  obtain ⟨M, hM, hbd⟩ := BddOn.of_continuousOn hf
  obtain ⟨δ, hδ, hmod⟩ := modulus_cube hf (half_pos hε)
  set K : ℝ := 2 * M / δ with hK
  have hK0 : 0 ≤ K := by positivity
  set c₀ : ℝ := (Fintype.card ↥J : ℝ) with hc₀
  have hc0 : 0 ≤ c₀ := by positivity
  set η : ℝ := ε / (2 * (K + 1) * (c₀ + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hall : ∀ᶠ n in atTop, ∀ j : ↥J, ∀ u ∈ S, ∀ t ∈ Tb,
      ‖(CartesianOccupationTransfer.physical (b n) g (j : ℤ) (j : ℤ) -
        ((a u t j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L (Nn n))) (ψ u t n)‖ ≤ η := by
    rw [Filter.eventually_all]
    intro j
    exact hB j η hηpos
  filter_upwards [hall, hψ] with n hn hn'
  intro u hu t ht
  have h1 := countOp_sub_le (b n) g hM (half_pos hε).le hδ hbd hmod (ha u hu t ht) (ψ u t n)
  refine h1.trans ?_
  have h2 : ∑ j : ↥J, ‖(CartesianOccupationTransfer.physical (b n) g (j : ℤ) (j : ℤ) -
      ((a u t j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L (Nn n))) (ψ u t n)‖ ≤ c₀ * η := by
    calc _ ≤ ∑ _j : ↥J, η := Finset.sum_le_sum fun j _ => hn j u hu t ht
      _ = c₀ * η := by simp [hc₀]
  have h3 : ‖ψ u t n‖ ≤ 1 := hn' u hu t ht
  have h4 : K * (c₀ * η) ≤ ε / 2 := by
    have : K * (c₀ * η) ≤ (K + 1) * (c₀ + 1) * η := by
      have : 0 ≤ η := hηpos.le
      nlinarith [mul_nonneg hK0 hc0, mul_nonneg hK0 this, mul_nonneg hc0 this, mul_nonneg (mul_nonneg hK0 hc0) this]
    refine this.trans (le_of_eq ?_)
    rw [hη]
    field_simp
  calc ε / 2 * ‖ψ u t n‖ + K * ∑ j : ↥J, ‖(CartesianOccupationTransfer.physical (b n) g (j : ℤ) (j : ℤ) -
        ((a u t j : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (HN L (Nn n))) (ψ u t n)‖
      ≤ ε / 2 * 1 + K * (c₀ * η) := by
        gcongr
    _ ≤ ε := by linarith

/-- **Pair clause for `f(B_{N,J})`**: the operator and its adjoint `conj f (B_{N,J})`. -/
theorem count_pair (Nn : ℕ → ℕ) (b : ∀ n, BetheBasis L (Nn n)) (g : Gauge) (J : Finset ℤ)
    {f : (↥J → ℝ) → ℂ} (hf : ContinuousOn f (cube J)) (S : Set X) (Tb : Set Θ)
    (ψ : X → Θ → ∀ n, HN L (Nn n)) (a : X → Θ → (↥J → ℝ))
    (ha : ∀ u ∈ S, ∀ t ∈ Tb, a u t ∈ cube J)
    (hψ : ∀ᶠ n in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t n‖ ≤ 1)
    (hB : ∀ j : ↥J, HasUniformStrongT (H := fun n => HN L (Nn n))
      (fun n => CartesianOccupationTransfer.physical (b n) g (j : ℤ) (j : ℤ)) S Tb ψ
      (fun u t => ((a u t j : ℝ) : ℂ))) :
    HasUniformPairT (H := fun n => HN L (Nn n)) (fun n => countOp (b n) g J f)
      (fun n => (countOp (b n) g J f).adjoint) S Tb ψ (fun u t => f (a u t)) := by
  have hbd := BddOn.of_continuousOn hf
  refine ⟨count_strong Nn b g J hf S Tb ψ a ha hψ hB, ?_⟩
  have h2 := count_strong Nn b g J (f := fun x => conj (f x))
    (Complex.continuous_conj.comp_continuousOn hf) S Tb ψ a ha hψ hB
  have e : (fun n => (countOp (b n) g J f).adjoint) = fun n => countOp (b n) g J (fun x => conj (f x)) := by
    funext n
    exact countOp_adjoint (b n) g J hbd
  rw [e]
  exact h2

end QuantumNLS.CountFunctionsS01Sym
