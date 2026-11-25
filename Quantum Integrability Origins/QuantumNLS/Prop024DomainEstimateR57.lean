import QuantumNLS.Prop024PairMomentsR55
import QuantumNLS.Prop023SpectralMoments
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Round 57 domain estimate for the factorial interaction.

The sector estimate below turns an exponential number moment into membership
in the exact maximal direct-sum domain.  Its source-state instance uses the
already-proved R55 moment bridge.  It deliberately makes no claim yet about
the exponential moment of a Weyl-translated vector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024DomainEstimateR57

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Prop022FactorialCoefficientsR115 Prop024PhysicalHamiltonianR54
open Prop024WeylConventionR55 Prop024PairMomentsR55
open Ext006NumberPhase Ext006PhysFockCoord Prop023SpectralMoments

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The factorial in an even factorial controls the ordinary factorial. -/
lemma factorial_le_sqrt_two_mul (m : ℕ) :
    (m.factorial : ℝ) ≤ Real.sqrt ((2*m).factorial : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hd : m.factorial * m.factorial ∣ (m+m).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add m m
  have hle : m.factorial * m.factorial ≤ (2*m).factorial := by
    rw [two_mul]
    exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  have hleR : ((m.factorial * m.factorial : ℕ) : ℝ) ≤
      (((2*m).factorial : ℕ) : ℝ) := by exact_mod_cast hle
  rw [sq]
  exact_mod_cast hleR

/-- One factorial-series coefficient is bounded by the full exponential. -/
lemma factorial_exp_term_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    x^m / (m.factorial : ℝ) ≤ Real.exp x := by
  have hs := Real.summable_pow_div_factorial x
  have hsum := hs.sum_le_tsum ({m} : Finset ℕ)
    (fun k hk => div_nonneg (pow_nonneg hx _) (by positivity))
  have hexp : (∑' k : ℕ, x^k / (k.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simpa [hexp] using hsum

/-- A factorial kernel gives at most linear times exponential growth of the
physical interaction restriction on the `n`-particle sector. -/
theorem interactionSector_norm_le_exp
    (N n : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hN : 0 < N) (hM : 0 ≤ M) (hA : 0 < A)
    (hB : FactorialBound B M A) :
    ‖interactionSector N n B‖ ≤
      (N : ℝ) * M * (n : ℝ) * Real.exp (A * (n : ℝ) / N) := by
  have hbase := interactionSector_norm_le N n B
  have hterm (k : Fin n) :
      fallingScale N n (k.val+1) * ‖B (k.val+1)‖ ≤
        M * Real.exp (A * (n : ℝ) / N) := by
    let m := k.val + 1
    have hm1 : 1 ≤ m := by dsimp [m]; omega
    have hmn : m ≤ n := by dsimp [m]; exact Nat.succ_le_iff.mpr k.isLt
    have hdf : (n.descFactorial m : ℝ) ≤ (n : ℝ)^m := by
      exact_mod_cast Nat.descFactorial_le_pow n m
    have hscale : fallingScale N n m ≤ ((n : ℝ) / N)^m := by
      unfold fallingScale
      rw [div_pow]
      exact div_le_div_of_nonneg_right hdf (by positivity)
    have hfac := factorial_le_sqrt_two_mul m
    have hfacPos : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hinv : (Real.sqrt ((2*m).factorial : ℝ))⁻¹ ≤
        (m.factorial : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hfacPos hfac
    have hx : 0 ≤ A * (n : ℝ) / N := by positivity
    have hseries := factorial_exp_term_le (A * (n : ℝ) / N) hx m
    have hkernel := hB m hm1
    have hBnorm : 0 ≤ ‖B m‖ := norm_nonneg (B m)
    have hscaleNonneg : 0 ≤ ((n : ℝ) / N)^m := by positivity
    calc
      fallingScale N n m * ‖B m‖ ≤
          ((n : ℝ) / N)^m * (M * A^m / Real.sqrt ((2*m).factorial : ℝ)) :=
        mul_le_mul hscale hkernel hBnorm hscaleNonneg
      _ = M * ((A * (n : ℝ) / N)^m /
          Real.sqrt ((2*m).factorial : ℝ)) := by
        rw [div_pow, div_pow]
        ring
      _ ≤ M * ((A * (n : ℝ) / N)^m / (m.factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hM
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hx _)
      _ ≤ M * Real.exp (A * (n : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hseries hM
  calc
    ‖interactionSector N n B‖ ≤
        (N : ℝ) * ∑ k : Fin n,
          fallingScale N n (k.val+1) * ‖B (k.val+1)‖ := hbase
    _ ≤ (N : ℝ) * ∑ k : Fin n, M * Real.exp (A * (n : ℝ) / N) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k
    _ = (N : ℝ) * M * (n : ℝ) * Real.exp (A * (n : ℝ) / N) := by
      simp [Finset.sum_const]
      ring

/-- A finite exponential number moment controls the physical factorial
interaction's actual maximal direct-sum domain. -/
theorem interaction_mem_domain_of_exponentialMoment
    (N : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A Q : ℝ) (hM : 0 ≤ M) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N)
    (hB : FactorialBound B M A) (x : Fock L)
    (hExp : exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ))) :
    x ∈ (interaction N B).domain := by
  have hQ0 : 0 < Q := by linarith
  have hNposR : (0 : ℝ) < (N : ℝ) := by
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  have hNposNat : 0 < N := by exact_mod_cast hNposR
  have hExpSeries :
      (∑' n : ℕ, ENNReal.ofReal
        (Real.exp ((n : ℝ) / (16*Q)) * ‖x n‖^2)) ≠ ⊤ := by
    have heq : exponentialMoment Q x =
        ∑' n : ℕ, ENNReal.ofReal
          (Real.exp ((n : ℝ) / (16*Q)) * ‖x n‖^2) := by
      unfold exponentialMoment numberExpectation
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [← heq]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hExp
  have hsumExpENN := ENNReal.summable_toReal hExpSeries
  have hsumExp : Summable (fun n : ℕ =>
      Real.exp ((n : ℝ) / (16*Q)) * ‖x n‖^2) := by
    exact hsumExpENN.congr (by
      intro n
      rw [ENNReal.toReal_ofReal]
      positivity)
  have hrate : 2*A/N ≤ 1/(32*Q) := by
    have he : 1 ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (0 : ℝ)
      norm_num at h ⊢
    have hcoef : 32 ≤ 256 * Real.exp 1 := by nlinarith [he]
    have hAQ : 0 ≤ A*Q := mul_nonneg hA.le (by linarith)
    have h32 : 32*A*Q ≤ N := by
      calc
        32*A*Q = 32*(A*Q) := by ring
        _ ≤ (256*Real.exp 1)*(A*Q) := mul_le_mul_of_nonneg_right hcoef hAQ
        _ = 256*Real.exp 1*A*Q := by ring
        _ ≤ N := hN
    rw [div_le_div_iff₀ hNposR (by positivity)]
    nlinarith [h32]
  have hpoint (n : ℕ) :
      (n : ℝ)^2 * Real.exp (2*A*(n : ℝ)/N) ≤
        (64*Q)^2 * Real.exp ((n : ℝ)/(16*Q)) := by
    have hpoly := pointwise_polynomial_bound (2*Q) (by nlinarith [hQ])
      2 (by norm_num) (n : ℝ) (by positivity)
    have hpoly' : (n : ℝ)^2 ≤ (64*Q)^2 * Real.exp ((n : ℝ)/(32*Q)) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc
        (n : ℝ)^2 ≤ ((n : ℝ)+2)^2 := by nlinarith [hn0]
        _ ≤ (16*(2*Q)*2)^2 * Real.exp ((n : ℝ)/(16*(2*Q))) := hpoly
        _ = (64*Q)^2 * Real.exp ((n : ℝ)/(32*Q)) := by congr 1 <;> ring
    have hrate' : 2*A*(n : ℝ)/N ≤ (n : ℝ)/(32*Q) := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hh := mul_le_mul_of_nonneg_right hrate hn0
      calc
        2*A*(n : ℝ)/N = (2*A/N)*(n : ℝ) := by ring
        _ ≤ (1/(32*Q))*(n : ℝ) := hh
        _ = (n : ℝ)/(32*Q) := by ring
    calc
      (n : ℝ)^2 * Real.exp (2*A*(n : ℝ)/N) ≤
          (64*Q)^2 * Real.exp ((n : ℝ)/(32*Q)) *
            Real.exp (2*A*(n : ℝ)/N) :=
        mul_le_mul_of_nonneg_right hpoly' (Real.exp_nonneg _)
      _ = (64*Q)^2 * Real.exp
          ((n : ℝ)/(32*Q) + 2*A*(n : ℝ)/N) := by
        rw [mul_assoc, ← Real.exp_add]
      _ ≤ (64*Q)^2 * Real.exp ((n : ℝ)/(16*Q)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply Real.exp_le_exp.mpr
        calc
          (n : ℝ)/(32*Q) + 2*A*(n : ℝ)/N ≤
              (n : ℝ)/(32*Q) + (n : ℝ)/(32*Q) := by linarith [hrate']
          _ = (n : ℝ)/(16*Q) := by ring
  have hsector (n : ℕ) :
      ‖interactionSector N n B (x n)‖^2 ≤
        ((N : ℝ)*M)^2 * (64*Q)^2 *
          (Real.exp ((n : ℝ)/(16*Q)) * ‖x n‖^2) := by
    have hnorm := interactionSector_norm_le_exp N n B M A hNposNat hM hA hB
    have hnorm' : ‖interactionSector N n B (x n)‖ ≤
        ((N : ℝ)*M*(n : ℝ)*Real.exp (A*(n : ℝ)/N))*‖x n‖ := by
      calc
        ‖interactionSector N n B (x n)‖ ≤
            ‖interactionSector N n B‖ * ‖x n‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ ((N : ℝ)*M*(n : ℝ)*Real.exp (A*(n : ℝ)/N))*‖x n‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    have hsq : ‖interactionSector N n B (x n)‖^2 ≤
        ((N : ℝ)*M*(n : ℝ)*Real.exp (A*(n : ℝ)/N)*‖x n‖)^2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
    calc
      ‖interactionSector N n B (x n)‖^2 ≤
          ((N : ℝ)*M)^2 * (n : ℝ)^2 *
            Real.exp (2*A*(n : ℝ)/N) * ‖x n‖^2 := by
        have hexp2 : (Real.exp (A*(n : ℝ)/N))^2 =
            Real.exp (2*A*(n : ℝ)/N) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        calc
          ‖interactionSector N n B (x n)‖^2 ≤
              ((N : ℝ)*M*(n : ℝ)*Real.exp (A*(n : ℝ)/N)*‖x n‖)^2 := hsq
          _ = ((N : ℝ)*M)^2 * (n : ℝ)^2 *
              Real.exp (2*A*(n : ℝ)/N) * ‖x n‖^2 := by
            simp only [mul_pow, hexp2]
      _ ≤ ((N : ℝ)*M)^2 * (64*Q)^2 *
          (Real.exp ((n : ℝ)/(16*Q)) * ‖x n‖^2) := by
        have hconst : 0 ≤ ((N : ℝ)*M)^2 := sq_nonneg _
        have hcoeff : 0 ≤ ((N : ℝ)*M)^2 * ‖x n‖^2 := by positivity
        calc
          ((N : ℝ)*M)^2 * (n : ℝ)^2 *
              Real.exp (2*A*(n : ℝ)/N) * ‖x n‖^2 =
            ((N : ℝ)*M)^2 *
              ((n : ℝ)^2 * Real.exp (2*A*(n : ℝ)/N)) * ‖x n‖^2 := by ring
          _ ≤ ((N : ℝ)*M)^2 *
              ((64*Q)^2 * Real.exp ((n : ℝ)/(16*Q))) * ‖x n‖^2 := by
            have hh := mul_le_mul_of_nonneg_left (hpoint n) hconst
            exact (mul_le_mul_of_nonneg_right hh (sq_nonneg (‖x n‖))).trans_eq (by ring)
          _ = _ := by ring
  have hsumOutput : Summable (fun n : ℕ =>
      ‖interactionSector N n B (x n)‖^2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hsector
      (hsumExp.mul_left (((N : ℝ)*M)^2 * (64*Q)^2))
  have hmem : Memℓp (fun n => interactionSector N n B (x n)) 2 := by
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsumOutput
  exact (interaction_mem_domain_iff N B x).2 hmem

/-- The source quasifree vector itself lies in the physical interaction
domain.  This is the undisplaced input to the translated-vector domain step. -/
theorem pairInput_untranslated_interaction_domain
    (N : ℕ) (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1))
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) /
      Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n)
    (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hSBound :
      let B := Prop022PositiveDataR126.positiveExtension K
      let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
      let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
      let Phi := Prop022ClassicalFlowR126.classicalFlow B M A hA.le hB hsa
      let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
      let S := fun t s : ℝ => fderiv ℝ (Phi (t-s)) (u s)
      ∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P)
    (hN : ∀ t : ℝ,
      |t| ≤ T → 256*Real.exp 1*A*
        (1+(Prop022FactorialMajorantR115.pairMajorant A*T*M*P)^2) ≤ N) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
      (by linarith) hA.le
      (Prop022PositiveDataR126.positiveExtension_bound K M A hK)
      (Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK) u₀ s t
    ∀ t : ℝ, |t| ≤ T → V t 0 vac ∈ (interaction N B).domain := by
  let B := Prop022PositiveDataR126.positiveExtension K
  let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
  let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
  let V := fun t s : ℝ => Prop022FockPropagatorR122.propagator B M A
    (by linarith) hA.le hB hsa u₀ s t
  let Q : ℝ := 1 +
    (Prop022FactorialMajorantR115.pairMajorant A*T*M*P)^2
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact le_add_of_nonneg_right (sq_nonneg _)
  change ∀ t : ℝ, |t| ≤ T → V t 0 vac ∈ (interaction N B).domain
  have hMom := pairInput_moments K M A hM hA hK hsK u₀ T P hP hPair hSBound
  intro t ht
  have hExp := (hMom t ht).1
  have hNt := hN t ht
  exact interaction_mem_domain_of_exponentialMoment N B M A Q
    (by linarith) hA hQ hNt hB (V t 0 vac) hExp

end QuantumNLS.Prop024DomainEstimateR57

#print axioms QuantumNLS.Prop024DomainEstimateR57.factorial_le_sqrt_two_mul
#print axioms QuantumNLS.Prop024DomainEstimateR57.factorial_exp_term_le
#print axioms QuantumNLS.Prop024DomainEstimateR57.interactionSector_norm_le_exp
#print axioms QuantumNLS.Prop024DomainEstimateR57.interaction_mem_domain_of_exponentialMoment
#print axioms QuantumNLS.Prop024DomainEstimateR57.pairInput_untranslated_interaction_domain

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024DomainEstimateR57." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024DomainEstimateR57." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any
          (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"R57 domain estimate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
