import QuantumNLS.Local001ComponentsB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

theorem contour_ne_free_mode {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {n m : ℤ} {z : ℂ}
    (hz : OnGamma L r n z) (hpar : LocalSpectral.parity m = LocalSpectral.parity n) :
    z ≠ (pm L m : ℂ) := by
  intro heq
  obtain ⟨k, hk⟩ := (even_iff_two_dvd.mp (parity_eq_even_sub hpar))
  have hindex : m = n + 2 * k := by omega
  by_cases hk0 : k = 0
  · have hmn : m = n := by rw [hindex, hk0]; ring
    rw [hmn] at heq
    change ‖z - (pm L n : ℂ)‖ = r at hz
    rw [heq] at hz
    have hz0 : (0 : ℝ) = r := by simpa using hz
    linarith
  · have hdist := contour_distance_lower hL (n := n) (k := k) (z := z) hz
    rw [heq, hindex, pm_even_shift, sub_self, norm_zero] at hdist
    have hkabs : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    have hd : 0 < spacing L := spacing_pos hL
    have hmul : spacing L ≤ spacing L * |(k : ℝ)| := by
      calc
        spacing L = spacing L * 1 := by ring
        _ ≤ spacing L * |(k : ℝ)| := mul_le_mul_of_nonneg_left hkabs hd.le
    have hgap : r < spacing L * |(k : ℝ)| - r := by linarith
    linarith


#print axioms contour_ne_free_mode

theorem scalarContour_q_ne {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {n : ℤ} {z ζ : ℂ}
    (hz : OnGamma L r n z) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hζ : ζ = (s : ℂ) * z / 2) :
    QuantumNLS.HaarResolvent.qOf L (parityComplex n) ζ ≠ 1 := by
  intro hq
  have hq' : (-1 : ℂ) ^ parityTag n * Complex.exp (Complex.I * ζ * L) = 1 := by
    rw [QuantumNLS.HaarResolvent.qOf, parityComplex_eq_pow n] at hq
    exact hq
  obtain ⟨k, hk⟩ :=
    (QuantumNLS.HaarKernelFactorizationSym.q_eq_one_iff hL (parityTag n) ζ).1 hq'
  let M : ℤ := 2 * k + parityTag n
  have hδ : QuantumNLS.HaarKernelFactorizationSym.deltaR (parityTag n + 1) =
      (parityTag n : ℝ) / 2 := deltaR_parityTag n
  have hfreq : QuantumNLS.HaarKernelFactorizationSym.omegaL L *
        ((k : ℝ) + QuantumNLS.HaarKernelFactorizationSym.deltaR (parityTag n + 1)) =
      QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) / 2 := by
    rw [hδ]
    dsimp [M]
    push_cast
    ring
  have hζeq : ζ = (((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hk, hfreq]
  have hsz : (s : ℂ) * z =
      ((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) : ℝ) : ℂ) := by
    have ht := congrArg (fun w : ℂ => (2 : ℂ) * w) hζeq
    rw [hζ] at ht
    have hcalc : (2 : ℂ) * ((s : ℂ) * z / 2) = (s : ℂ) * z := by ring
    rw [hcalc] at ht
    have hcast : (2 : ℂ) *
        (((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) / 2) : ℝ) : ℂ) =
        ((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast] at ht
    exact ht
  let m : ℤ := s * M
  have hmode : z = (LocalSpectral.pm L m : ℂ) := by
    rcases hs with hs | hs
    · subst s
      have h := hsz
      dsimp [m] at h ⊢
      have homega :
          ((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) : ℝ) : ℂ) =
            (LocalSpectral.pm L M : ℂ) := by
        unfold QuantumNLS.HaarKernelFactorizationSym.omegaL LocalSpectral.pm
        push_cast
        field_simp [ne_of_gt hL]
      simpa [m, homega] using h
    · subst s
      have h := hsz
      dsimp [m] at h ⊢
      have homega :
          ((QuantumNLS.HaarKernelFactorizationSym.omegaL L * (M : ℝ) : ℝ) : ℂ) =
            (LocalSpectral.pm L M : ℂ) := by
        unfold QuantumNLS.HaarKernelFactorizationSym.omegaL LocalSpectral.pm
        push_cast
        field_simp [ne_of_gt hL]
      rw [homega] at h
      have hneg : -z = (LocalSpectral.pm L M : ℂ) := by simpa using h
      have hpmneg : (LocalSpectral.pm L (-M) : ℂ) = -(LocalSpectral.pm L M : ℂ) := by
        unfold LocalSpectral.pm
        push_cast
        ring
      have hmul : (-1 : ℤ) * M = -M := by ring
      rw [hmul]
      calc
        z = -(-z) := by ring
        _ = -(LocalSpectral.pm L M : ℂ) := congrArg Neg.neg hneg
        _ = (LocalSpectral.pm L (-M) : ℂ) := hpmneg.symm
  have hparity : LocalSpectral.parity m = LocalSpectral.parity n := by
    rcases Int.even_or_odd' n with ⟨a, ha | ha⟩
    · subst n
      have hn : Even (2 * a : ℤ) := even_two_mul a
      have htag : parityTag (2 * a) = 0 := by simp [parityTag, hn]
      have hM : M = 2 * k := by simp [M, htag]
      rcases hs with hs | hs
      · subst s
        simp only [m]
        rw [hM]
        simp [LocalSpectral.parity, hn, even_two_mul]
      · subst s
        simp only [m]
        rw [hM]
        have hm : Even ((-1 : ℤ) * (2 * k)) := by
          refine ⟨-k, ?_⟩
          ring
        simp [LocalSpectral.parity, hn, hm]
    · subst n
      have hn : ¬ Even (2 * a + 1 : ℤ) := Int.not_even_two_mul_add_one a
      have htag : parityTag (2 * a + 1) = 1 := by simp [parityTag, hn]
      have hM : M = 2 * k + 1 := by simp [M, htag]
      rcases hs with hs | hs <;> subst s
      · simp only [m]
        rw [hM]
        simp [LocalSpectral.parity, hn, Int.not_even_two_mul_add_one]
      · have hneg : (-1 : ℤ) * (2 * k + 1) = 2 * (-k - 1) + 1 := by ring
        simp only [m]
        rw [hM, hneg]
        simp [LocalSpectral.parity, hn, Int.not_even_two_mul_add_one]
  exact (contour_ne_free_mode hL hr hsmall hz hparity) hmode



#print axioms scalarContour_q_ne

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
