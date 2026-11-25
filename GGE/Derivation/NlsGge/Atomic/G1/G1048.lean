import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe
import NlsGge.Atomic.G1.G1047
import NlsGge.GK38.PeriodicLabellingCounting
import NlsGge.GK38.CountingLemma

/- G1-048 production: the G1-047 private copy (G1047S2 namespace tree, verbatim) of the reviewed candidate is replaced by `import NlsGge.Atomic.G1.G1047`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator
-- file-level opens that sat between the removed G1047S2 blocks in the reviewed candidate (kept: the remaining code was compiled with them active)
open NlsGge.Atomic.G1047S2.K17.K16
open NlsGge.Pilot


/-! ============================================================================
G1-048 COMMAND02 pre-approval proof (proof development, AUTHOR; not self-reviewed).
In the reviewed candidate G1048_PROOF03 the G1-047 proof (proof development/G1047_PROOF02, with its G1-017/G1-016 copies, namespace G1047S2) was inlined verbatim; in this
production file it is imported (`NlsGge.Atomic.G1.G1047`) and the namespace tree G1047S2 is not repeated.
Route (GK Lemma 6.3): G1-047 with ε = 1/4 gives |(Δ²-4)/(-4 sin²) - 1| ≤ 1/4 for ψ in a G1-047 neighbourhood, ‖z‖ > Λ, z off
the discs; hence ‖perChar ψ z - (-4 sin² z)‖ ≤ ‖sin z‖² (sin z ≠ 0 off the discs, production), the strict Rouché comparison
(`counting_strict_comparison38`); production `periodic_counting_at38` (Rouché `Lib.rouche_circle` on ∂D_n and ∂B_N against
-4 sin², exclusion off the discs) gives the three clauses with the same N.
============================================================================ -/

namespace NlsGge.Atomic.G1048S3

open Filter Topology Set Metric NlsGge.GK38

noncomputable section

theorem perChar_cmp_s3 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ n : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 n‖) →
      ‖perChar φ z - perChar 0 z‖ < ‖perChar 0 z‖ := by
  obtain ⟨U, hU, Λ, h⟩ := NlsGge.Atomic.G1047S2.G1047_whole φ₀ (1 / 4) (by norm_num)
  refine ⟨U, hU, Λ + 1, fun φ hφ z hz hsep => ?_⟩
  have hsep' : ∀ n : ℤ, Real.pi / 4 ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := hsep
  obtain ⟨-, h2, -⟩ := h φ hφ z (by linarith) hsep'
  have hsin : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
  have hpos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr hsin
  have hd : (-4 * Complex.sin z ^ 2 : ℂ) ≠ 0 := by
    have : (-4 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero this (pow_ne_zero 2 hsin)
  have hpc : perChar φ z = (monodromyPair φ z).trace ^ 2 - 4 := rfl
  set q : ℂ := ((monodromyPair φ z).trace ^ 2 - 4) / (-4 * Complex.sin z ^ 2) with hq
  have e : perChar φ z - (-4 * Complex.sin z ^ 2) = (q - 1) * (-4 * Complex.sin z ^ 2) := by
    rw [hpc, sub_mul, one_mul, hq, div_mul_cancel₀ _ hd]
  have herr : ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ‖Complex.sin z‖ ^ 2 := by
    rw [e, norm_mul]
    have h4 : ‖(-4 * Complex.sin z ^ 2 : ℂ)‖ = 4 * ‖Complex.sin z‖ ^ 2 := by
      rw [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
    rw [h4]
    nlinarith [sq_nonneg ‖Complex.sin z‖]
  exact counting_strict_comparison38 herr hsep

theorem periodic_counting_s3 (φ₀ : PotPair) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ N : ℕ, 0 < N ∧ ∀ φ ∈ U,
      (∀ n : ℤ, (N : ℤ) < |n| →
        Multiset.card (Lib.zeroMultiset (perChar φ)
          (ball (countingCenter38 n) (Real.pi / 4))) = 2) ∧
      Multiset.card (Lib.zeroMultiset (perChar φ)
        (ball (0 : ℂ) (countingRadius38 N))) = 4 * N + 2 ∧
      ∀ z : ℂ, perChar φ z = 0 →
        z ∈ ball (0 : ℂ) (countingRadius38 N) ∨
          ∃ n : ℤ, (N : ℤ) < |n| ∧ z ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  obtain ⟨U, hU, R, hcmp⟩ := perChar_cmp_s3 φ₀
  obtain ⟨K, hK⟩ := exists_nat_gt (R / Real.pi)
  let N : ℕ := K + 1
  have hNpos : 0 < N := Nat.succ_pos K
  have hRN : R ≤ countingRadius38 N := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hK
    unfold countingRadius38 N
    push_cast
    linarith [Real.pi_pos]
  exact ⟨U, hU, N, hNpos, fun φ hφ => periodic_counting_at38 φ N
    (fun z hz hsep => hcmp φ hφ z (hRN.trans hz) hsep)⟩

theorem natAbs_iff {N : ℕ} {n : ℤ} : N < n.natAbs ↔ (N : ℤ) < |n| := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl

theorem G1048_main :
    ((
  ∀ φ : PotPair,
  ∃ V : Set PotPair, IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ, 0 < N ∧ ∀ ψ ∈ V,
    (∀ n : ℤ, N < n.natAbs →
      Multiset.card (Lib.zeroMultiset (fun w : ℂ => perChar ψ w)
        (Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))) = 2) ∧
    Multiset.card (Lib.zeroMultiset (fun w : ℂ => perChar ψ w)
      (Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4))) = 4 * N + 2 ∧
    (∀ w : ℂ, perChar ψ w = 0 →
      w ∈ Metric.ball (0 : ℂ) ((N : ℝ) * Real.pi + Real.pi / 4) ∨
      ∃ n : ℤ, N < n.natAbs ∧ w ∈ Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4))
  : Prop)) := by
  intro φ
  obtain ⟨U, hU, N, hN, h⟩ := periodic_counting_s3 φ
  refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, N, hN, fun ψ hψ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h ψ (interior_subset hψ)
  refine ⟨fun n hn => h1 n (natAbs_iff.1 hn), h2, fun w hw => ?_⟩
  rcases h3 w hw with h4 | ⟨n, hn, h5⟩
  · exact Or.inl h4
  · exact Or.inr ⟨n, natAbs_iff.2 hn, h5⟩

end

end NlsGge.Atomic.G1048S3
