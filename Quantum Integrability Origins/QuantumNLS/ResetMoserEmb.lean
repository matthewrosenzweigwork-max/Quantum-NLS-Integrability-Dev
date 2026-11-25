import QuantumNLS.ResetMoserBounds

/-!
# `thm:reset-moser` (LOCAL-017), stage 3d-2 (item 2(c), finite coordinate vectors)

Source: `symplectic_correction.tex`, "The periods of a radial primitive": "Lifting again to `ℝ^{|F|}`"; the coordinate torus of a finitely supported point.
For a finite index set `T`, `Emb T c = Σ_{k∈T} c_k e_k ∈ ℓ²(ℤ;ℂ)` embeds coordinate vectors; derivatives of curves of such vectors are computed
coordinatewise (finite sum), and tangent vectors `i a_k z_k` of the torus through `Emb T z` are exactly the `Emb` of such coordinates.

* `Emb_apply`, `Emb_self` (`Emb T z = z` when `T` contains the support), `Emb_continuous`, `Emb_hasDerivAt`;
* `norm_Emb_eq`: `‖Emb T c‖ = ‖Emb T d‖` when the coordinate moduli agree on `T`;
* `Emb_mem_Tz`: `Emb T c ∈ 𝒯_{Emb T s}` when `c_k = i s_k a_k` with real `a_k` (`k ∈ T`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef

/-- The `k`th unit vector. -/
def ek (k : ℤ) : K := lp.single (E := fun _ : ℤ => ℂ) 2 k (1 : ℂ)

/-- `Σ_{k∈T} c_k e_k`. -/
def Emb (T : Finset ℤ) (c : ℤ → ℂ) : K := ∑ k ∈ T, c k • ek k

theorem Emb_apply (T : Finset ℤ) (c : ℤ → ℂ) (n : ℤ) : Emb T c n = if n ∈ T then c n else 0 := by
  unfold Emb ek
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]

theorem Emb_self {T : Finset ℤ} {z : K} (hT : ∀ n, z n ≠ 0 → n ∈ T) : Emb T (fun k => z k) = z := by
  ext n
  rw [Emb_apply]
  by_cases h : n ∈ T
  · simp [h]
  · simp only [h, if_false]
    by_contra hne
    exact h (hT n (Ne.symm hne))

theorem Emb_continuous {α : Type*} [TopologicalSpace α] (T : Finset ℤ) {f : α → ℤ → ℂ}
    (hf : ∀ k ∈ T, Continuous fun a => f a k) : Continuous fun a => Emb T (f a) := by
  unfold Emb
  exact continuous_finset_sum _ fun k hk => (hf k hk).smul continuous_const

theorem Emb_hasDerivAt (T : Finset ℤ) {f f' : ℝ → ℤ → ℂ} {s : ℝ}
    (h : ∀ k ∈ T, HasDerivAt (fun s => f s k) (f' s k) s) :
    HasDerivAt (fun s => Emb T (f s)) (Emb T (f' s)) s := by
  have h2 := HasDerivAt.sum (u := T) (A := fun k y => f y k • ek k) (A' := fun k => f' s k • ek k) (x := s)
    fun k hk => (h k hk).smul_const (ek k)
  have e : (fun s => Emb T (f s)) = ∑ k ∈ T, fun y => f y k • ek k := by
    funext y; simp [Emb, Finset.sum_apply]
  rw [e]
  exact h2

theorem norm_Emb_eq (T : Finset ℤ) (c d : ℤ → ℂ) (h : ∀ k ∈ T, ‖c k‖ = ‖d k‖) :
    ‖Emb T c‖ = ‖Emb T d‖ := by
  have h1 : ∀ n, ‖Emb T c n‖ = ‖Emb T d n‖ := by
    intro n
    rw [Emb_apply, Emb_apply]
    by_cases hn : n ∈ T
    · simp [hn, h n hn]
    · simp [hn]
  have h2 : ‖Emb T c‖ ^ 2 = ‖Emb T d‖ ^ 2 := by
    rw [tsum_norm_sq, tsum_norm_sq]
    exact tsum_congr fun n => by rw [h1 n]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0)).1 h2

theorem Emb_mem_Tz (T : Finset ℤ) (s c : ℤ → ℂ) (h : ∀ k ∈ T, ∃ a : ℝ, c k = Complex.I * s k * a) :
    Emb T c ∈ Tz (Emb T s) := by
  intro n
  rw [Emb_apply, Emb_apply]
  by_cases hn : n ∈ T
  · obtain ⟨a, ha⟩ := h n hn
    exact ⟨a, by simp [hn, ha]⟩
  · exact ⟨0, by simp [hn]⟩

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Emb_apply
#print axioms QuantumNLS.ResetMoser.Emb_self
#print axioms QuantumNLS.ResetMoser.Emb_continuous
#print axioms QuantumNLS.ResetMoser.Emb_hasDerivAt
#print axioms QuantumNLS.ResetMoser.norm_Emb_eq
#print axioms QuantumNLS.ResetMoser.Emb_mem_Tz
