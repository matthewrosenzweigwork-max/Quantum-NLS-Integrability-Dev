import NlsGge.GK38.PairAsymptoticsForce
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.PairPotentialProbe

/-!
# F5: independent triangular complex-pair probes

For the genuinely complex pair `(u,0)`, the first Volterra forcing has zero
second row, so its next Volterra iterate vanishes. Thus `E+V E` solves the
book integral equation exactly, and F2 uniqueness identifies the fundamental
matrix. Its trace and periodic characteristic function are free, although
for `(constL2 a,0)` the upper-right entry at `z=0,t=1` is `i a`.
No general F5 asymptotic conclusion is used. All representative identities
inside integrals are almost-everywhere identities with respect to real volume.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

open NlsGge.Pilot NlsGge.SpectralFoundations

noncomputable section

/-- The lower-left first forcing vanishes when the second potential is the zero L² class. -/
theorem triangularForce_lower_left38 (u : PhysicalL2) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    pairForce38 (u, 0) z t 1 0 = 0 := by
  have hi := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one (0 : PhysicalL2)) z t.2
  rw [pairForce38_one_zero]
  have he : (fun s : ℝ => Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) *
      potRepSnd38 (u, 0) s) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [coverRep38_zero_ae] with s hs
    simp [potRepSnd38, hs]
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [he] with s hs _ using hs)]
  simp

/-- The second Volterra iterate of the free matrix is exactly zero for triangular pairs. -/
theorem triangularForce_volterra_zero38 (u : PhysicalL2) (z : ℂ) :
    volterraP (u, 0) z (pairForce38 (u, 0) z) = 0 := by
  ext t i j
  have hK : Continuous (fun s : ℝ => freeE z ((t : ℝ) - s)) :=
    (continuous_freeE z).comp (continuous_const.sub continuous_id)
  have hi := intervalIntegrable_triple_entry_of_mem (u, 0) hK
    (continuous_ext38 (pairForce38 (u, 0) z)) t.2 i j
  rw [volterraP_apply, volterraFun_apply]
  change (∫ s in (0 : ℝ)..(t : ℝ),
    (freeE z ((t : ℝ) - s) * potCoeff38 (u, 0) s * ext38 (pairForce38 (u, 0) z) s) i j) = 0
  have he : ∀ᵐ s : ℝ, s ∈ Set.uIcc (0 : ℝ) t →
      (freeE z ((t : ℝ) - s) * potCoeff38 (u, 0) s *
        ext38 (pairForce38 (u, 0) z) s) i j = 0 := by
    filter_upwards [coverRep38_zero_ae] with s hs hst
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using uIcc_zero_subset t.2 hst
    rw [mul3_apply]
    rw [ext38_of_mem _ hs01]
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two, freeE, potCoeff38, potRepSnd38, hs,
        triangularForce_lower_left38, pairForce38_diagonal]
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [he] with s hs hst using hs (Set.uIoc_subset_uIcc hst))]
  simp

/-- Independent exact fundamental matrix: triangular potentials stop after the first correction. -/
theorem triangularFund_eq38 (u : PhysicalL2) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair (u, 0) z t = freeE z t + Matrix.of (pairForce38 (u, 0) z t) := by
  let G : PairCont38 := freeFundP z + pairForce38 (u, 0) z
  have hV : volterraP (u, 0) z G = pairForce38 (u, 0) z := by
    rw [show G = freeFundP z + pairForce38 (u, 0) z from rfl, map_add,
      triangularForce_volterra_zero38, add_zero]
    rfl
  have hbook : ∀ (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2), G t i j = freeE z t i j +
      ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 (u, 0) s *
        (Set.IccExtend zero_le_one G s : PairMat38)) i j := by
    intro t i j
    change G t i j = freeE z t i j + (volterraP (u, 0) z G) t i j
    rw [hV]
    rfl
  have hG := fundCont_unique (u, 0) z G hbook
  rw [fundPair_eq, ← hG]
  rfl

/-- Exact triangular monodromy, independent of spectral asymptotic statements. -/
theorem triangularMonodromy_eq38 (u : PhysicalL2) (z : ℂ) :
    monodromyPair (u, 0) z = freeE z 1 +
      Matrix.of (pairForce38 (u, 0) z ⟨1, by norm_num, le_rfl⟩) := by
  rw [monodromyPair_eq_fundPair, triangularFund_eq38]

/-- The full trace is free for every triangular complex pair, including nonzero potentials. -/
theorem triangularDiscrim_eq38 (u : PhysicalL2) (z : ℂ) :
    discrim (u, 0) z = 2 * Complex.cos z := by
  unfold discrim
  rw [triangularMonodromy_eq38]
  have he : Matrix.trace (freeE z 1 +
      Matrix.of (pairForce38 (u, 0) z ⟨1, by norm_num, le_rfl⟩)) =
      Matrix.trace (freeE z 1) := by
    simp [Matrix.trace, Matrix.of_apply, Fin.sum_univ_two, pairForce38_diagonal]
  rw [he, freeE_eq]
  exact zsFullTrace_zeroPotential z

/-- The periodic characteristic function is free for every triangular complex pair. -/
theorem triangularPerChar_eq38 (u : PhysicalL2) (z : ℂ) :
    perChar (u, 0) z = -4 * Complex.sin z ^ 2 := by
  unfold perChar
  have he : discrim (u, 0) = fun w => 2 * Complex.cos w := funext (triangularDiscrim_eq38 u)
  rw [he]
  exact perCharOf_free z

/-- A constant triangular pair has a visibly nontrivial upper-right entry at spectral parameter zero. -/
theorem triangularConst_upper_right_zero38 (a : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair (constL2 a, 0) 0 t 0 1 = Complex.I * a * (t : ℂ) := by
  have hi := intervalIntegrable_coverRep38_one (constL2 a)
  rw [triangularFund_eq38]
  change freeE 0 t 0 1 + pairForce38 (constL2 a, 0) 0 t 0 1 = _
  rw [pairForce38_zero_one]
  simp only [freeE, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add, neg_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
  have he : (fun s : ℝ => potRepFst38 (constL2 a, 0) s) =ᵐ[volume] fun _ => a := by
    exact coverRep38_const_ae a
  rw [intervalIntegral.integral_congr_ae (by
    filter_upwards [he] with s hs _ using hs)]
  simp [intervalIntegral.integral_const, Complex.real_smul]
  ring

/-- Unit-period monodromy at zero: a nonzero potential produces a nonzero off-diagonal entry. -/
theorem triangularConst_monodromy_nonzero38 (a : ℂ) (ha : a ≠ 0) :
    monodromyPair (constL2 a, 0) 0 0 1 = Complex.I * a ∧
      monodromyPair (constL2 a, 0) 0 0 1 ≠ 0 := by
  have he : monodromyPair (constL2 a, 0) 0 0 1 = Complex.I * a := by
    rw [monodromyPair_eq_fundPair, triangularConst_upper_right_zero38]
    simp
  exact ⟨he, by rw [he]; exact mul_ne_zero Complex.I_ne_zero ha⟩

/-- A fixed nonzero complex potential gives a nontrivial matrix while both scalar functions are free. -/
theorem triangular_probe_complex38 :
    monodromyPair (constL2 Complex.I, 0) 0 0 1 = -1 ∧
      (∀ z : ℂ, discrim (constL2 Complex.I, 0) z = 2 * Complex.cos z) ∧
      (∀ z : ℂ, perChar (constL2 Complex.I, 0) z = -4 * Complex.sin z ^ 2) := by
  refine ⟨?_, triangularDiscrim_eq38 _, triangularPerChar_eq38 _⟩
  rw [(triangularConst_monodromy_nonzero38 Complex.I Complex.I_ne_zero).1]
  exact Complex.I_mul_I

end
end NlsGge.GK38
