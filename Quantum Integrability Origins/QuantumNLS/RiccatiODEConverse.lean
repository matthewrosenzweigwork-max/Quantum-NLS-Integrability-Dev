import QuantumNLS.RiccatiClassical
import QuantumNLS.RiccatiMainFull

/-! The periodic physical Riccati ODE implies the resolvent fixed point.
The homogeneous difference from the resolvent solution vanishes by an
integrating factor and periodicity. No derivative-domain assumption is
imposed on a competing solution. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.RiccatiODEConverse
open Set
open QuantumNLS.RiccatiPointwiseCoef
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.RiccatiClassical QuantumNLS.RiccatiChargeIdent
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiDerivative
open QuantumNLS.SmoothScalarMomentsPrerequisite

/-- The continuous physical representative determines its Ell2 element. -/
theorem physRep_injective {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a) :
    Function.Injective (physRep L a) := by
  intro x y h
  have hs : Fourier.seriesRep (L := L) (toField L a x) =
      Fourier.seriesRep (L := L) (toField L a y) := by
    funext t
    induction t using QuotientAddGroup.induction_on with
    | H t =>
      simpa only [seriesRep_coe, physRep] using congrFun h t
  apply lp.ext
  funext k
  have hc := congrArg (fun f : AddCircle L → ℂ => Fourier.coeff L f k) hs
  rw [Fourier.coeff_seriesRep (summable_norm_toField hL ha x),
    Fourier.coeff_seriesRep (summable_norm_toField hL ha y)] at hc
  exact (div_left_inj' (pw_ne_zero L a k)).mp hc

/-- An upper-half-plane homogeneous solution with matching endpoints is zero.
This is the scalar variation-of-constants uniqueness step. -/
theorem periodic_homogeneous_eq_zero {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : 0 < z.im)
    {w : ℝ → ℂ} (hw : ∀ t, HasDerivAt w (Complex.I * z * w t) t)
    (hp : w L = w 0) : w = 0 := by
  let g : ℝ → ℂ := fun t => Complex.exp (-Complex.I * z * (t : ℂ)) * w t
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * z * (s : ℂ)))
        (Complex.exp (-Complex.I * z * (t : ℂ)) * (-Complex.I * z)) t := by
      simpa only [id_eq, Complex.ofReal_one, mul_one] using
        (((hasDerivAt_id t).ofReal_comp).const_mul (-Complex.I * z)).cexp
    have hd := he.mul (hw t)
    have hd0 : Complex.exp (-Complex.I * z * (t : ℂ)) * (-Complex.I * z) * w t +
        Complex.exp (-Complex.I * z * (t : ℂ)) * (Complex.I * z * w t) = 0 := by ring
    rw [hd0] at hd
    exact hd
  have hc : ∀ t, g t = w 0 := by
    intro t
    have hh := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) t 0
    simpa [g] using hh
  have hn : Complex.exp (-Complex.I * z * (L : ℂ)) ≠ 1 := by
    intro he
    have hn := congrArg norm he
    rw [Complex.norm_exp, norm_one] at hn
    have hre : (-Complex.I * z * (L : ℂ)).re = z.im * L := by simp
    rw [hre] at hn
    have : 1 < Real.exp (z.im * L) := Real.one_lt_exp_iff.mpr (mul_pos hz hL)
    linarith
  have h0 : w 0 = 0 := by
    have hh := hc L
    dsimp [g] at hh
    rw [hp] at hh
    have : (Complex.exp (-Complex.I * z * (L : ℂ)) - 1) * w 0 = 0 := by
      linear_combination hh
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hn)
  funext t
  have hh := hc t
  rw [h0] at hh
  exact (mul_eq_zero.mp hh).resolve_left (Complex.exp_ne_zero _)

/-- The resolvent solves the inhomogeneous physical linear equation. -/
theorem ropCLM_physical_ode {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    {z : ℂ} (hz : 0 < z.im) (F : Ell2) (t : ℝ) :
    HasDerivAt (physRep L a (ropCLM L z hz F))
      (Complex.I * z * physRep L a (ropCLM L z hz F) t + physRep L a F t) t := by
  let y := ropCLM L z hz F
  have hy : y ∈ dDom L := ropCLM_mem_dDom L z hz F
  have hid : dmulEll L ⟨y, hy⟩ - (Complex.I * z) • y = F := by
    apply ropCLM_injective L z hz
    exact ropCLM_dmul_sub L z hz ⟨y, hy⟩
  have hd := physRep_hasDerivAt hL ha hy t
  rw [eq_add_of_sub_eq hid, physRep_add hL ha, Pi.add_apply, physRep_smul_apply] at hd
  convert hd using 1; ring

/-- Variation of constants on the periodic physical representatives. -/
theorem periodic_linear_eq_resolvent {L a : ℝ} [Fact (0 < L)]
    (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (q F : Ell2)
    (hq : ∀ t, HasDerivAt (physRep L a q)
      (Complex.I * z * physRep L a q t + physRep L a F t) t) :
    q = ropCLM L z hz F := by
  apply physRep_injective hL ha
  have hw : (fun t => physRep L a q t - physRep L a (ropCLM L z hz F) t) = 0 := by
    apply periodic_homogeneous_eq_zero hL hz
    · intro t
      convert (hq t).sub (ropCLM_physical_ode hL ha hz F t) using 1; ring
    · rw [physRep_periodic hL q, physRep_periodic hL (ropCLM L z hz F)]
  funext t
  exact sub_eq_zero.mp (congrFun hw t)

/-- Every represented periodic classical solution of the physical Riccati ODE
is a fixed point at model coupling κ/L. Smallness is unnecessary here. -/
theorem riccati_ode_fixed {L a : ℝ} [Fact (0 < L)] (hL : 0 < L) (ha : 1 / 2 < a)
    {z : ℂ} (hz : 0 < z.im) (κ : ℝ) (u v q : Ell2)
    (hq : ∀ t, HasDerivAt (physRep L a q)
      (Complex.I * z * physRep L a q t + physRep L a u t
        - (κ : ℂ) * physRep L a v t * physRep L a q t ^ 2) t) :
    riccatiT hL ha hz (κ / L) u v q = q := by
  let F := u - ((κ / L : ℝ) : ℂ) • mulBil hL ha v (mulBil hL ha q q)
  have hF : ∀ t, physRep L a F t = physRep L a u t -
      (κ : ℂ) * physRep L a v t * physRep L a q t ^ 2 := by
    intro t
    have hkL : ((κ / L : ℝ) : ℂ) * (L : ℂ) = (κ : ℂ) := by
      have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    change physRep L a (u - ((κ / L : ℝ) : ℂ) •
      mulBil hL ha v (mulBil hL ha q q)) t = _
    rw [physRep_sub_apply hL ha, physRep_smul_apply]
    simp only [mulBil_apply, physRep_mulEll]
    linear_combination (-(((κ / L : ℝ) : ℂ) * physRep L a v t * physRep L a q t ^ 2)) *
      (sqrt_sq_cast hL) + (-(physRep L a v t * physRep L a q t ^ 2)) * hkL
  have heq : q = ropCLM L z hz F := periodic_linear_eq_resolvent hL ha hz q F (by
    intro t
    rw [hF]
    convert hq t using 1; ring)
  change ropCLM L z hz u - ((κ / L : ℝ) : ℂ) •
    ropCLM L z hz (mulBil hL ha v (mulBil hL ha q q)) = q
  rw [← map_smul, ← map_sub]
  exact heq.symm

/-- The frozen local output has uniqueness among all small periodic ODE
solutions represented at level a, with the same radius C/Im z. -/
theorem unique_small_periodic_ode {L a S δ : ℝ} [Fact (0 < L)] {M : ℕ}
    {K : Set ℝ} {f : ℝ → ℂ} {hL : 0 < L} {ha : 1 / 2 < a}
    (out : LocalOutput L f M a S δ K hL ha)
    {κ : ℝ} (hκ : κ ∈ K) {z : ℂ} (hR : out.R ≤ ‖z‖)
    (hsec : δ * ‖z‖ ≤ z.im) (hz : 0 < z.im) {p : Ell2 × Ell2} (hp : p ∈ out.V)
    (q : Ell2) (hsmall : ‖q‖ ≤ out.C / z.im)
    (hq : ∀ t, HasDerivAt (physRep L a q)
      (Complex.I * z * physRep L a q t + physRep L a (lowT L a S p.1) t
        - (κ : ℂ) * physRep L a (lowT L a S p.2) t * physRep L a q t ^ 2) t) :
    q = out.rf κ z p := by
  exact out.unique_small κ hκ z hR hsec hz p hp q hsmall
    (riccati_ode_fixed hL ha hz κ _ _ q hq)

/-- Arbitrary periodic C¹ profiles are covered whenever they have the stated
Ell2 representation; the conclusion identifies both coordinates and profile. -/
theorem represented_periodic_ode_unique {L a S δ : ℝ} [Fact (0 < L)] {M : ℕ}
    {K : Set ℝ} {f : ℝ → ℂ} {hL : 0 < L} {ha : 1 / 2 < a}
    (out : LocalOutput L f M a S δ K hL ha)
    {κ : ℝ} (hκ : κ ∈ K) {z : ℂ} (hR : out.R ≤ ‖z‖)
    (hsec : δ * ‖z‖ ≤ z.im) (hz : 0 < z.im) {p : Ell2 × Ell2} (hp : p ∈ out.V)
    (r : ℝ → ℂ) (q : Ell2) (hrep : physRep L a q = r)
    (hsmall : ‖q‖ ≤ out.C / z.im)
    (hr : ∀ t, HasDerivAt r
      (Complex.I * z * r t + physRep L a (lowT L a S p.1) t
        - (κ : ℂ) * physRep L a (lowT L a S p.2) t * r t ^ 2) t) :
    riccatiT hL ha hz (κ / L) (lowT L a S p.1) (lowT L a S p.2) q = q ∧
    q = out.rf κ z p ∧ r = physRep L a (out.rf κ z p) := by
  rw [← hrep] at hr
  have hq := unique_small_periodic_ode out hκ hR hsec hz hp q hsmall hr
  exact ⟨riccati_ode_fixed hL ha hz κ _ _ q hr, hq, hrep.symm.trans (congrArg _ hq)⟩


/-- Strengthening of the frozen local output: uniqueness is quantified over
arbitrary represented physical ODE profiles at the existing smallness radius. -/
def PeriodicODEUnique {L a S δ : ℝ} [Fact (0 < L)] {M : ℕ}
    {K : Set ℝ} {f : ℝ → ℂ} {hL : 0 < L} {ha : 1 / 2 < a}
    (out : LocalOutput L f M a S δ K hL ha) : Prop :=
  ∀ κ ∈ K, ∀ z : ℂ, out.R ≤ ‖z‖ → δ * ‖z‖ ≤ z.im →
    (hz : 0 < z.im) → ∀ p ∈ out.V, ∀ (r : ℝ → ℂ) (q : Ell2),
    physRep L a q = r → ‖q‖ ≤ out.C / z.im →
    (∀ t, HasDerivAt r
      (Complex.I * z * r t + physRep L a (lowT L a S p.1) t
        - (κ : ℂ) * physRep L a (lowT L a S p.2) t * r t ^ 2) t) →
    riccatiT hL ha hz (κ / L) (lowT L a S p.1) (lowT L a S p.2) q = q ∧
    q = out.rf κ z p ∧ r = physRep L a (out.rf κ z p)

/-- The complete frozen local output, with its all-small-periodic-ODE
uniqueness clause proved from the same printed hypotheses. -/
theorem riccati_main_full_periodic_ode (L : ℝ) [Fact (0 < L)]
    {M : ℕ} {a S δ : ℝ} {K : Set ℝ} {f : ℝ → ℂ}
    (hL : 0 < L) (ha : 1 / 2 < a) (hM : 1 ≤ M) (haS : a + (M : ℝ) + 1 ≤ S)
    (hδ : 0 < δ) (hK : IsCompact K) (hKpos : K ⊆ Ioi 0) (base : Ell2)
    (hbase : physRep L a (lowT L a S base) = f) :
    ∃ out : LocalOutput L f M a S δ K hL ha, PeriodicODEUnique out := by
  obtain ⟨out⟩ := QuantumNLS.RiccatiMainFull.riccati_main_full L hL ha hM haS hδ hK hKpos base hbase
  refine ⟨out, ?_⟩
  intro κ hκ z hR hsec hz p hp r q hrep hsmall hr
  exact represented_periodic_ode_unique out hκ hR hsec hz hp r q hrep hsmall hr

#print axioms riccati_ode_fixed
#print axioms unique_small_periodic_ode
#print axioms represented_periodic_ode_unique
#print axioms riccati_main_full_periodic_ode
end QuantumNLS.RiccatiODEConverse

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut ownCount : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RiccatiODEConverse." ||
        n.toString.startsWith "_private.QuantumNLS.RiccatiODEConverse." then
      pending := pending.push n
      ownCount := ownCount + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Riccati ODE converse audit PASS: {ownCount} own/generated constants; {seen.size} transitive constants; standard only."
