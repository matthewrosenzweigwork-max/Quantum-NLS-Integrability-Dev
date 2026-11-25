import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall

/-!
# `thm:reset-moser` (LOCAL-017), stage 5b: complete flow of a bounded Lipschitz autonomous field (Picard-Lindelof)

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The nonautonomous integral equation for `Y_t` has a unique
local solution by the uniform derivative bound ... the solution extends through `0 ≤ t ≤ 1`".  Existence by Mathlib's Picard-Lindelof
theorem on `[-n-1, n+1]`, glued over `n` by Mathlib's uniqueness theorem.  `exists_flow`: for a bounded, globally Lipschitz field `F` on a
real Banach space there is `Φ : ℝ → E → E` with `Φ 0 = id` and `∂ₜ Φ t v = F (Φ t v)` for all `t`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

open Set Metric Filter Topology
open scoped NNReal

namespace QuantumNLS.ResetMoserExist

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_flow {F : E → E} {Kc : ℝ≥0} {Bd : ℝ} (hF : LipschitzWith Kc F) (hB : ∀ x, ‖F x‖ ≤ Bd) :
    ∃ Φ : ℝ → E → E, (∀ v, Φ 0 v = v) ∧ ∀ v t, HasDerivAt (fun s => Φ s v) (F (Φ t v)) t := by
  classical
  let L : ℝ≥0 := ⟨max Bd 0, le_max_right _ _⟩
  have hex : ∀ (v : E) (n : ℕ), ∃ α : ℝ → E, α 0 = v ∧ ∀ t ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivWithinAt α (F (α t)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) t := by
    intro v n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    let T : ℝ≥0 := ⟨(n : ℝ) + 1, hn.le⟩
    have h0 : (0 : ℝ) ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := ⟨by linarith, hn.le⟩
    have hPL : IsPicardLindelof (fun (_ : ℝ) (x : E) => F x) (tmin := -((n : ℝ) + 1))
        (tmax := (n : ℝ) + 1) ⟨0, h0⟩ v (L * T) 0 L Kc :=
      { lipschitzOnWith := fun t _ => hF.lipschitzOnWith
        continuousOn := fun x _ => continuousOn_const
        norm_le := fun t _ x _ => (hB x).trans (le_max_left _ _)
        mul_max_le := by
          show (L : ℝ) * max ((n : ℝ) + 1 - 0) (0 - (-((n : ℝ) + 1))) ≤ ((L * T : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
          have : max ((n : ℝ) + 1 - 0) (0 - (-((n : ℝ) + 1))) = (n : ℝ) + 1 := by simp
          rw [this, NNReal.coe_mul, NNReal.coe_zero, sub_zero]
          exact le_rfl }
    exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose α h0 hd using hex
  have hint : ∀ (v : E) (n : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 → HasDerivAt (α v n) (F (α v n t)) t := by
    intro v n t ht
    have h1 := abs_lt.mp ht
    exact (hd v n t ⟨by linarith [h1.1], by linarith [h1.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [h1.1]) (by linarith [h1.2]))
  have huniq : ∀ (v : E) (n m : ℕ) (t : ℝ), |t| < (n : ℝ) + 1 → |t| < (m : ℝ) + 1 →
      α v n t = α v m t := by
    intro v n m t htn htm
    have hk : (0 : ℝ) < (min n m : ℕ) + 1 := by positivity
    have hkn : (min n m : ℕ) ≤ n := min_le_left _ _
    have hkm : (min n m : ℕ) ≤ m := min_le_right _ _
    have hkn' : ((min n m : ℕ) : ℝ) ≤ n := by exact_mod_cast hkn
    have hkm' : ((min n m : ℕ) : ℝ) ≤ m := by exact_mod_cast hkm
    have htk : |t| < ((min n m : ℕ) : ℝ) + 1 := by
      rcases le_total n m with h | h
      · rw [min_eq_left h]; exact htn
      · rw [min_eq_right h]; exact htm
    have := ODE_solution_unique_of_mem_Ioo (v := fun _ x => F x) (s := fun _ => (Set.univ : Set E))
      (K := Kc) (f := α v n) (g := α v m) (t₀ := 0) (a := -(((min n m : ℕ) : ℝ) + 1))
      (b := ((min n m : ℕ) : ℝ) + 1) (fun _ _ => hF.lipschitzOnWith)
      ⟨by linarith, hk⟩
      (fun s hs => ⟨hint v n s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]), trivial⟩)
      (fun s hs => ⟨hint v m s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2]), trivial⟩)
      (by rw [h0, h0])
    have h1 := abs_lt.mp htk
    exact this ⟨by linarith [h1.1], by linarith [h1.2]⟩
  refine ⟨fun t v => α v ⌈|t|⌉₊ t, fun v => ?_, fun v t => ?_⟩
  · simp [h0]
  · have hN : |t| < (⌈|t|⌉₊ : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
    have hev : (fun s => α v ⌈|s|⌉₊ s) =ᶠ[𝓝 t] α v ⌈|t|⌉₊ := by
      have hopen : ∀ᶠ s in 𝓝 t, |s| < (⌈|t|⌉₊ : ℝ) + 1 :=
        (continuous_abs.continuousAt (x := t)).eventually (Iio_mem_nhds hN)
      filter_upwards [hopen] with s hs
      exact huniq v _ _ s (lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)) hs
    have := (hint v ⌈|t|⌉₊ t hN).congr_of_eventuallyEq hev
    exact this

end QuantumNLS.ResetMoserExist

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserExist.exists_flow
