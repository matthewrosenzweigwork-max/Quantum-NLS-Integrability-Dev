import QuantumNLS.Local001FinalB
import QuantumNLS.ResolventWordLabelInjectiveLOCAL005
import QuantumNLS.ResolventWordEstimateStage2LOCAL005
import QuantumNLS.ResolventWordGP11LOCAL005
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
namespace QuantumNLS.Local005

/-- Product counting sums factor over all independent integer labels. -/
theorem pi_tsum {k : ℕ} (f : Fin k → ℤ → ℝ)
    (hf0 : ∀ j m, 0 ≤ f j m) (hf : ∀ j, Summable (f j)) :
    Summable (fun q : Fin k → ℤ => ∏ j, f j (q j)) ∧
      ∑' q : Fin k → ℤ, ∏ j, f j (q j) = ∏ j, ∑' m, f j m := by
  classical
  induction k with
  | zero =>
    let : Unique (Fin 0 → ℤ) :=
      ⟨⟨fun i => Fin.elim0 i⟩, fun q => by funext i; exact Fin.elim0 i⟩
    exact ⟨(hasSum_fintype _).summable, by simp⟩
  | succ k ih =>
    obtain ⟨hs, he⟩ := ih (fun j => f j.succ) (fun j => hf0 j.succ)
      (fun j => hf j.succ)
    let e : (Fin (k + 1) → ℤ) ≃ ℤ × (Fin k → ℤ) := (Fin.consEquiv (fun _ => ℤ)).symm
    have hm := (hf 0).mul_of_nonneg hs (hf0 0)
      (fun q => Finset.prod_nonneg fun j _ => hf0 j.succ (q j))
    have hc : Summable (fun q : Fin (k + 1) → ℤ => ∏ j, f j (q j)) := by
      simpa [e, Function.comp_def, Fin.prod_univ_succ, Fin.tail] using hm.comp_injective e.injective
    refine ⟨hc, ?_⟩
    calc
      ∑' q : Fin (k + 1) → ℤ, ∏ j, f j (q j) =
          ∑' p : ℤ × (Fin k → ℤ), f 0 p.1 * ∏ j, f j.succ (p.2 j) := by
        simpa [e, Fin.prod_univ_succ, Fin.tail] using
          (e.tsum_eq (fun p => f 0 p.1 * ∏ j, f j.succ (p.2 j)))
      _ = (∑' m, f 0 m) * ∑' q : Fin k → ℤ, ∏ j, f j.succ (q j) :=
        ((hf 0).tsum_mul_tsum hs hm).symm
      _ = ∏ j, ∑' m, f j m := by rw [he, Fin.prod_univ_succ]

/-- Cauchy--Schwarz for nonnegative scalar series, with its summability conclusion. -/
theorem cauchy {ι : Type*} (f g : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i)
    (hf : Summable fun i => f i ^ 2) (hg : Summable fun i => g i ^ 2) :
    Summable (fun i => f i * g i) ∧
      (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  have hf' : Summable fun i => f i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hf
  have hg' : Summable fun i => g i ^ (2 : ℝ) := by simpa [Real.rpow_two] using hg
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 hf' hg'
  have hle' : ∑' i, f i * g i ≤
      Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2) := by
    simpa [Real.sqrt_eq_rpow, Real.rpow_two] using hle
  refine ⟨hs, ?_⟩
  calc
    (∑' i, f i * g i) ^ 2 ≤
        (Real.sqrt (∑' i, f i ^ 2) * Real.sqrt (∑' i, g i ^ 2)) ^ 2 :=
      (sq_le_sq₀ (tsum_nonneg fun i => mul_nonneg (hf0 i) (hg0 i)) (by positivity)).2 hle'
    _ = _ := by rw [mul_pow, Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _),
      Real.sq_sqrt (tsum_nonneg fun i => sq_nonneg _)]

#print axioms pi_tsum
#print axioms cauchy
end QuantumNLS.Local005
