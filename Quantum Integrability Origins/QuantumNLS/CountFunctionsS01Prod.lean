import QuantumNLS.FullWickH6

/-!
# CountFunctionsS01Prod: ordered products of strong-symbol pairs with letter-dependent bounds

PRINTED SOURCE `source-text/chapters/core/canonical_algebra.tex:48-54` (eq:words and the sentence after it):
  "For completeness, strong convergence for a fixed ordered word follows from the exact telescoping identity
   `∏A_{N,j} - ∏s_j = Σ_j A_{N,1}⋯A_{N,j-1}(A_{N,j}-s_j)∏_{h>j}s_h`. The prefixes have uniformly bounded norm."

This module restates the frozen `FullWickH6.pair_list_prod` (which carries the telescoping, adjoint pairing and the
bounds `C^len`, `K^len` for letters with ONE common operator bound) in the form needed for words mixing letters with
DIFFERENT operator bounds (`1` for Cartesian and phase transfers, `sup|f|` for count functions, `coeffNorm f` for Wick
quantizations): the common bound is the finite sum of the letter bounds; the symbol bounds are DERIVED from the strong
symbols (`symbol_le_of_strong`), as in `FullWickH8.symbol_le_one_of_strong`.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH6 (GoodFactor pair_list_prod)

namespace QuantumNLS.CountFunctionsS01Prod

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
variable {X Θ : Type*}

/-- The symbol of an operator family with eventual norm bound `C` on a unit preparation is bounded by `C`. -/
theorem symbol_le_of_strong {A : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}
    {a : X → Θ → ℂ} {C : ℝ} (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ = 1)
    (hs : HasUniformStrongT A S Tb ψ a) : ∀ u ∈ S, ∀ t ∈ Tb, ‖a u t‖ ≤ C := by
  intro u hu t ht
  by_contra hcon
  push_neg at hcon
  have hε : 0 < (‖a u t‖ - C) / 2 := by linarith
  obtain ⟨N, h1, h2, h3⟩ := ((hs _ hε).and (hA.and hψ)).exists
  have h4 := h1 u hu t ht
  have h5 := h3 u hu t ht
  have e : a u t • ψ u t N = A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp
  have h6 : ‖a u t‖ = ‖A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ := by
    rw [← e, norm_smul, h5, mul_one]
  have h7 : ‖A N (ψ u t N)‖ ≤ C := by
    have := (A N).le_opNorm (ψ u t N)
    rw [h5, mul_one] at this
    exact this.trans h2
  have h8 := norm_sub_le (A N (ψ u t N)) ((A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N))
  linarith

/-- **Ordered words of strong-symbol pairs with letter-dependent bounds.** For a list `l` of letters, each with an
operator `f i`, a companion `f' i`, a symbol `s i`, a nonnegative bound `bnd i` (for `f i`, `f' i` eventually) and a
uniform strong-symbol pair on a unit preparation, the ordered product is a uniform strong-symbol pair with the
product symbol, and the companion is the reversed product of the companions. -/
theorem prod_of_pairs {ι : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N) (s : ι → X → Θ → ℂ) (S : Set X)
    (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N) (bnd : ι → ℝ) (l : List ι)
    (hb : ∀ i ∈ l, 0 ≤ bnd i)
    (hf : ∀ i ∈ l, ∀ᶠ N in atTop, ‖f i N‖ ≤ bnd i)
    (hf' : ∀ i ∈ l, ∀ᶠ N in atTop, ‖f' i N‖ ≤ bnd i)
    (hpair : ∀ i ∈ l, HasUniformPairT (f i) (f' i) S Tb ψ (s i))
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ = 1) :
    HasUniformPairT (fun N => (l.map (fun i => f i N)).prod)
      (fun N => ((l.map (fun i => f' i N)).reverse).prod) S Tb ψ
      (fun u t => (l.map (fun i => s i u t)).prod) := by
  set C : ℝ := (l.map bnd).sum with hC
  have hC0 : 0 ≤ C := List.sum_nonneg (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hb i hi)
  have hle : ∀ i ∈ l, bnd i ≤ C := fun i hi =>
    List.single_le_sum (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact hb j hj) _ (List.mem_map_of_mem hi)
  have hgood : ∀ i ∈ l, GoodFactor f f' s S Tb ψ C C i := by
    intro i hi
    refine ⟨(hf i hi).mono fun N h => h.trans (hle i hi), (hf' i hi).mono fun N h => h.trans (hle i hi),
      ?_, hpair i hi⟩
    exact symbol_le_of_strong ((hf i hi).mono fun N h => h.trans (hle i hi)) hψ (hpair i hi).1
  exact (pair_list_prod f f' s S Tb ψ C C hC0 hC0 l hgood).1

end QuantumNLS.CountFunctionsS01Prod
