import Mathlib
import QuantumNLS.BetheExtension

/-!
# Translation covariance of the actual Bethe waves (periodic extension)

Source use: `ROOT_spectral_measure.tex` (`prop:root-free` discussion) and `ROOT_measure_extensions.tex`, `prop:root-full-mass`: "Common phase and translation leave every
finite-particle probability unchanged".  This module proves, for the actual constructed Bethe wave (`BetheExtension.torusExtension`), the covariance
`ψ(x_1+a, …, x_N+a) = e^{i a Σ_j q_j} ψ(x)` on the torus, `a ∈ ℝ`, with `q = sourceRoots L n c`.

Proof (no new analytic input): (1) the analytic ansatz `wavefunction` is trivially covariant under a real shift of all coordinates (`wavefunction_add_const`) and
sorting commutes with shifts (`decreasing_add_const`); (2) hence `periodicExtension` is covariant for all small non-negative shifts that do not move any
coordinate across the seam (`periodicExtension_local`); (3) the accepted continuity of `periodicExtension` across the seam
(`BetheExtension.continuous_periodicExtension`, which encodes the on-shell Bethe periodicity) and real induction (`IsClosed.Icc_subset_of_forall_exists_gt`) extend
this to every shift.  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

noncomputable section

namespace QuantumNLS.WaveTranslation

open QuantumNLS.BetheWavefunctions (planeWave coordinateAnsatz wavefunction)
open QuantumNLS.BetheExtension (decreasing decreasing_antitone decreasing_eq_permute symmetricExtension torusExtension
  periodicExtension continuous_periodicExtension)

/-- The total rapidity `Σ_i q_i` of the label `n`. -/
def totalRoot (L c : ℝ) {N : ℕ} (n : Fin N → ℤ) : ℝ := ∑ i, QuantumNLS.BetheSmooth.sourceRoots L n c i

theorem planeWave_add_const {N : ℕ} (q x : Fin N → ℝ) (s : ℝ) :
    planeWave q (fun i => x i + s) =
      planeWave q x * Complex.exp (Complex.I * ((s * ∑ i, q i : ℝ) : ℂ)) := by
  unfold planeWave
  rw [← Complex.exp_add]
  congr 1
  have e : ∑ i, q i * (x i + s) = ∑ i, q i * x i + s * ∑ i, q i := by
    simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm]
  rw [e]
  push_cast
  ring

theorem wavefunction_add_const {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ) (s : ℝ) :
    wavefunction L c n (fun i => x i + s) =
      Complex.exp (Complex.I * ((s * totalRoot L c n : ℝ) : ℂ)) * wavefunction L c n x := by
  unfold wavefunction coordinateAnsatz
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [planeWave_add_const]
  have : ∑ i, ((QuantumNLS.BetheSmooth.sourceRoots L n c) ∘ σ) i = totalRoot L c n :=
    Equiv.sum_comp σ (QuantumNLS.BetheSmooth.sourceRoots L n c)
  rw [this]
  ring

theorem decreasing_add_const {N : ℕ} (x : Fin N → ℝ) (s : ℝ) :
    decreasing (fun i => x i + s) = fun i => decreasing x i + s := by
  have hanti : Antitone ((fun i => x i + s) ∘ Tuple.sort (α := ℝᵒᵈ) x) := by
    intro a b hab
    exact add_le_add_left (decreasing_antitone x hab) s
  rw [decreasing_eq_permute _ _ hanti]
  rfl

theorem symmetricExtension_add_const {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ) (s : ℝ) :
    symmetricExtension L c n (fun i => x i + s) =
      Complex.exp (Complex.I * ((s * totalRoot L c n : ℝ) : ℂ)) * symmetricExtension L c n x := by
  unfold symmetricExtension
  rw [decreasing_add_const]
  exact wavefunction_add_const L c n _ s

/-! ### Local covariance away from the seam -/

theorem periodicExtension_local {N : ℕ} {L : ℝ} [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ) (y : Fin N → ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), periodicExtension L c n (fun i => y i + δ) =
      Complex.exp (Complex.I * ((δ * totalRoot L c n : ℝ) : ℂ)) * periodicExtension L c n y := by
  have hL : 0 < L := Fact.out
  set r : Fin N → ℝ := fun i => (AddCircle.equivIco L 0 (y i : AddCircle L) : ℝ) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => (AddCircle.equivIco L 0 (y i : AddCircle L)).2.1
  have hrL : ∀ i, r i < L := fun i =>
    lt_of_lt_of_eq (AddCircle.equivIco L 0 (y i : AddCircle L)).2.2 (zero_add L)
  have hcoe : ∀ i, ((y i : ℝ) : AddCircle L) = ((r i : ℝ) : AddCircle L) := fun i => by
    simp only [hr]
    exact (AddCircle.coe_equivIco).symm
  have hfin : ∀ i, ∀ᶠ δ in 𝓝 (0 : ℝ), δ < L - r i := fun i =>
    gt_mem_nhds (by linarith [hrL i])
  have hall : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ i, δ < L - r i := Filter.eventually_all.2 hfin
  filter_upwards [nhdsWithin_le_nhds hall, self_mem_nhdsWithin] with δ hδ hδpos
  have hδ0 : 0 < δ := hδpos
  have hbase : periodicExtension L c n y = symmetricExtension L c n r := by
    unfold periodicExtension torusExtension
    congr 1
  have hshift : periodicExtension L c n (fun i => y i + δ) = symmetricExtension L c n (fun i => r i + δ) := by
    unfold periodicExtension torusExtension
    congr 1
    funext i
    have h1 : (((y i + δ : ℝ)) : AddCircle L) = (((r i + δ : ℝ)) : AddCircle L) := by
      rw [AddCircle.coe_add, AddCircle.coe_add, hcoe i]
    show ((AddCircle.equivIco L 0 (((y i + δ : ℝ)) : AddCircle L) : ℝ)) = r i + δ
    rw [h1]
    exact AddCircle.equivIco_coe_of_mem (by
      simp only [zero_add]
      exact ⟨by linarith [hr0 i], by linarith [hδ i]⟩)
  rw [hshift, hbase]
  exact symmetricExtension_add_const L c n r δ

/-! ### Global covariance by real induction -/

theorem periodicExtension_shift_nonneg {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin (N + 1) → ℤ} (hn : Antitone n) (y : Fin (N + 1) → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    periodicExtension L c n (fun i => y i + a) =
      Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ)) * periodicExtension L c n y := by
  set P := totalRoot L c n with hP
  let g : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * ((t * P : ℝ) : ℂ))) *
    periodicExtension L c n (fun i => y i + t)
  have hgc : Continuous g := by
    refine Continuous.mul (by fun_prop) ?_
    exact (continuous_periodicExtension hc hn).comp (by fun_prop)
  have hS : IsClosed ({t : ℝ | g t = g 0} ∩ Set.Icc 0 a) :=
    (isClosed_eq hgc continuous_const).inter isClosed_Icc
  have hsub : Set.Icc 0 a ⊆ {t : ℝ | g t = g 0} := by
    refine hS.Icc_subset_of_forall_exists_gt (by simp) ?_
    intro t ht b hb
    have hloc := periodicExtension_local (L := L) c n (fun i => y i + t)
    have hmem : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Set.Ioc (0 : ℝ) (b - t) :=
      Ioc_mem_nhdsGT (sub_pos.2 hb)
    obtain ⟨δ, hδ1, hδ2⟩ := (hloc.and hmem).exists
    refine ⟨t + δ, ?_, ⟨by linarith [hδ2.1], by linarith [hδ2.2]⟩⟩
    show g (t + δ) = g 0
    have e : (fun i => y i + (t + δ)) = fun i => (y i + t) + δ := by funext i; ring
    have hg : g (t + δ) = g t := by
      simp only [g]
      rw [e]
      try beta_reduce at hδ1
      rw [hδ1, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [hg]; exact ht.1
  have h1 := hsub ⟨ha, le_rfl⟩
  simp only [Set.mem_setOf_eq] at h1
  have h0 : g 0 = periodicExtension L c n y := by simp [g]
  rw [h0] at h1
  simp only [g] at h1
  calc periodicExtension L c n (fun i => y i + a)
      = Complex.exp (Complex.I * ((a * P : ℝ) : ℂ)) *
          (Complex.exp (-(Complex.I * ((a * P : ℝ) : ℂ))) * periodicExtension L c n (fun i => y i + a)) := by
        rw [← mul_assoc, ← Complex.exp_add]; simp
    _ = _ := by rw [h1]

theorem periodicExtension_shift {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin (N + 1) → ℤ} (hn : Antitone n) (y : Fin (N + 1) → ℝ) (a : ℝ) :
    periodicExtension L c n (fun i => y i + a) =
      Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ)) * periodicExtension L c n y := by
  rcases le_total 0 a with ha | ha
  · exact periodicExtension_shift_nonneg hc hn y a ha
  · have h := periodicExtension_shift_nonneg (L := L) hc hn (fun i => y i + a) (-a) (by linarith)
    have e : (fun i => (y i + a) + -a) = y := by funext i; ring
    rw [e] at h
    calc periodicExtension L c n (fun i => y i + a)
        = Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * ((-a * totalRoot L c n : ℝ) : ℂ)) *
              periodicExtension L c n (fun i => y i + a)) := by
          rw [← mul_assoc, ← Complex.exp_add]
          have : Complex.I * ((a * totalRoot L c n : ℝ) : ℂ) + Complex.I * ((-a * totalRoot L c n : ℝ) : ℂ) = 0 := by
            push_cast; ring
          rw [this]; simp
      _ = _ := by rw [← h]

/-- **Translation covariance of the actual Bethe wave on the torus**: `ψ(x + a·1) = e^{i a Σ q_j} ψ(x)`. -/
theorem torusExtension_translate {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin (N + 1) → ℤ} (hn : Antitone n) (x : Fin (N + 1) → AddCircle L) (a : ℝ) :
    torusExtension L c n (fun i => x i + (a : AddCircle L)) =
      Complex.exp (Complex.I * ((a * totalRoot L c n : ℝ) : ℂ)) * torusExtension L c n x := by
  set y : Fin (N + 1) → ℝ := fun i => (AddCircle.equivIco L 0 (x i) : ℝ) with hy
  have hx : x = fun i => ((y i : ℝ) : AddCircle L) := funext fun i => (AddCircle.coe_equivIco).symm
  have h := periodicExtension_shift (L := L) hc hn y a
  unfold periodicExtension at h
  rw [hx]
  simpa [AddCircle.coe_add] using h

end QuantumNLS.WaveTranslation

#print axioms QuantumNLS.WaveTranslation.periodicExtension_local
#print axioms QuantumNLS.WaveTranslation.periodicExtension_shift
#print axioms QuantumNLS.WaveTranslation.torusExtension_translate
