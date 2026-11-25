import QuantumNLS.Prop021RemainderInputR131
import QuantumNLS.Prop021MovingWeylR131
import QuantumNLS.Prop021ManyBodyGroupR129

/-! Signed-time coherent comparison on physical Fock, with the exact
named predecessor inputs and the actual common-domain Weyl derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology
open Set
namespace QuantumNLS.Prop021CoherentComparisonR131

open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Prop022OVacuum
open Prop021RemainderInputR131 Prop021PhaseR130 Prop021ManyBodyR129
open Prop021ManyBodyGroupR129 Prop021ManyBodyDomainR129 Prop021QuadraticBindingR129
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Ext006PhysFockCoord
open Prop024WWeylPhysical Ext006ModeDomainR33a Ext005Moments
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

section Curve

local instance : NormedSpace ℝ (L2T L) := NormedSpace.restrictScalars ℝ ℂ (L2T L)

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (hs : ∀ m, (B m).adjoint = B m) (u₀ : Prop001.Sphere (L2T L)) (N : ℕ)
local notation "u" => profile B M A hA hB hs u₀
local notation "ξ" => fluctuation B M A hM hA hB hs u₀
local notation "v" => center B M A hA hB hs u₀ N
local notation "p" => phase B M A hA hB hs u₀ N
local notation "H" => hamiltonian B N

/-- The literal approximate curve of the printed proof. -/
def approximate (t : ℝ) : Fock L := p t • printedWeyl (v t) (ξ t)

theorem approximate_initial :
    approximate B M A hM hA hB hs u₀ N 0 =
      printedWeyl ((Real.sqrt N : ℂ) • (u₀ : L2T L)) vac := by
  unfold approximate
  rw [phase_zero, one_smul, (fluctuation_initial_norm_smooth B M A hM hA hB hs u₀).1]
  simp only [Prop021PhaseR130.center, (profile_spec B M A hA hB hs u₀).1]

/-- Differentiation of the actual curve leaves precisely the low-order
velocity. The domain hypotheses follow from the actual quadratic vacuum. -/
theorem approximate_hasDerivAt (t : ℝ)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient (ξ t))) (h₂ : ξ t ∈ momentDomain 2) :
    HasDerivAt (approximate B M A hM hA hB hs u₀ N)
      ((-Complex.I) • (p t • printedWeyl (v t) (lowOrders B N (u t) (ξ t) hx h₂))) t := by
  have hc := (center_hasDerivAt B M A hA hB hs u₀ N t)
  have hξ := (fluctuation_initial_norm_smooth B M A hM hA hB hs u₀).2.2.2
  have hdξ : HasDerivAt ξ (deriv ξ t) t :=
    (hξ.differentiable (by norm_num) t).hasDerivAt
  have hdv : HasDerivAt v (deriv v t) t := by
    have he : deriv v t = _ := hc.deriv
    rw [he]
    exact hc
  have hm := Prop021MovingWeylR131.moving_displacement_hasDerivAt
    v ξ t (deriv v t) (deriv ξ t) hdv hdξ hx
  have hp := phase_hasDerivAt B M A hM hA hB hs u₀ N t
  have h := hp.smul hm
  simp only [Prop021WeylLawR131.G_eq] at h
  let a : ℂ := (-Complex.I) * ((N : ℝ) * density B M A hA hB hs u₀ t : ℂ)
  let b : ℂ := Complex.I * (⟪v t,deriv v t⟫_ℂ).im
  let g := Prop021DisplacementR129.generator (deriv v t) (ξ t) hx
  let U := printedWeyl (v t)
  change HasDerivAt (approximate B M A hM hA hB hs u₀ N)
    (p t • U (deriv ξ t + g + b • ξ t) + (a*p t) • U (ξ t)) t at h
  have hsum : p t • U (deriv ξ t + g + b • ξ t) + (a*p t) • U (ξ t) =
      p t • U (a • ξ t + g + b • ξ t + deriv ξ t) := by
    simp only [map_add, map_smul, smul_add, smul_smul]
    rw [mul_comm a (p t)]
    abel
  have hcancel : a • ξ t + g + b • ξ t + deriv ξ t =
      (-Complex.I) • lowOrders B N (u t) (ξ t) hx h₂ :=
    vacuum_cancellation B M A hM hA hB hs u₀ N t hx h₂
  rw [hsum, hcancel, map_smul, smul_comm (p t) (-Complex.I)] at h
  exact h

/-- The exact shifted identity turns the differentiated curve into
the strong residual, with its sign and maximal-domain witness. -/
theorem approximate_residual (t : ℝ)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient (ξ t))) (h₂ : ξ t ∈ momentDomain 2)
    (hd : printedWeyl (v t) (ξ t) ∈ (H).domain) (R : Fock L)
    (he : H ⟨printedWeyl (v t) (ξ t),hd⟩ =
      printedWeyl (v t) (lowOrders B N (u t) (ξ t) hx h₂ + R)) :
    ∃ h : approximate B M A hM hA hB hs u₀ N t ∈ (H).domain,
      HasDerivAt (approximate B M A hM hA hB hs u₀ N)
        ((-Complex.I) • H ⟨approximate B M A hM hA hB hs u₀ N t,h⟩ +
          Complex.I • (p t • printedWeyl (v t) R)) t := by
  have h := (H).domain.smul_mem (p t) hd
  refine ⟨h, ?_⟩
  have eq : H ⟨approximate B M A hM hA hB hs u₀ N t,h⟩ =
      p t • printedWeyl (v t) (lowOrders B N (u t) (ξ t) hx h₂ + R) := by
    change H ((p t) • (⟨printedWeyl (v t) (ξ t),hd⟩ : (H).domain)) = _
    rw [LinearPMap.map_smul, he]
  rw [eq, map_add, smul_add, smul_add]
  have hz : (-Complex.I) • (p t • printedWeyl (v t) R) +
      Complex.I • (p t • printedWeyl (v t) R) = 0 := by
    simp only [neg_smul, neg_add_cancel]
  rw [add_assoc, hz, add_zero]
  exact approximate_hasDerivAt B M A hM hA hB hs u₀ N t hx h₂

end Curve

section PositiveRanks

open Prop024WeylConventionR55 Prop022PositiveDataR126 Prop022ClassicalFlowR126
open Prop021RatesR128 Prop022FactorialMajorantR115 Prop021DuhamelR128

variable (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L))
    (T P : ℝ) (hP : 1 ≤ P) (N : ℕ)
local notation "B" => positiveExtension K
local notation "hB" => positiveExtension_bound K M A hK
local notation "hs" => positiveExtension_selfAdjoint K hsK
local notation "hM₀" => (zero_le_one.trans hM)
local notation "Q" => numberParameter (pairMajorant A) T M P
local notation "H" => hamiltonian B N
local notation "E" => manyBodyEvolution B hs N
local notation "u" => profile B M A hA.le hB hs u₀
local notation "ξ" => fluctuation B M A hM₀ hA.le hB hs u₀
local notation "v" => center B M A hA.le hB hs u₀ N
local notation "p" => phase B M A hA.le hB hs u₀ N
local notation "app" => approximate B M A hM₀ hA.le hB hs u₀ N

private lemma abs_le_of_between_zero {t r : ℝ} (hr : r ∈ uIcc 0 t) :
    |r| ≤ |t| := by
  rcases le_total 0 t with ht | ht
  · rw [uIcc_of_le ht, mem_Icc] at hr
    rw [abs_of_nonneg hr.1, abs_of_nonneg ht]
    exact hr.2
  · rw [uIcc_comm, uIcc_of_le ht, mem_Icc] at hr
    rw [abs_of_nonpos hr.2, abs_of_nonpos ht]
    linarith [hr.1]

/-- The source coherent comparison, for every signed endpoint in the
time interval. The only predecessor premises are the exact named inputs
specialized at the indicated parameters. -/
theorem coherent_bound (hT : 0 ≤ T)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hs (r - q)) (u q)‖ ≤ P)
    (CA' : ℝ) (hCA' : 0 ≤ CA') (hRem : RemainderEstimate (L := L) A CA')
    (hN : 256 * Real.exp 1 * A * Q ≤ N) (t : ℝ) (ht : |t| ≤ T) :
    ‖E t (printedWeyl ((Real.sqrt N : ℂ) • (u₀ : L2T L)) vac) - app t‖ ≤
      (T * CA') * M * (N : ℝ)^(-(1/2 : ℝ)) * Q^(3/2 : ℝ) := by
  let x₀ := printedWeyl ((Real.sqrt N : ℂ) • (u₀ : L2T L)) (vac : Fock L)
  let w := fun r => E r x₀ - app r
  let C := CA' * M * (N : ℝ)^(-(1/2 : ℝ)) * Q^(3/2 : ℝ)
  have hQ : 1 ≤ Q := one_le_numberParameter _ _ _ _
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hinit : app 0 = x₀ := approximate_initial B M A hM₀ hA.le hB hs u₀ N
  have hzero : w 0 = 0 := by simp only [w, manyBody_zero, hinit, sub_self]
  have hrs (r : ℝ) (hr : |r| ≤ T) :
      ∃ R : Fock L, ‖R‖ ≤ C ∧ ∃ hdom : app r ∈ (H).domain,
        HasDerivAt app ((-Complex.I) • H ⟨app r,hdom⟩ +
          Complex.I • (p r • printedWeyl (v r) R)) r := by
    obtain ⟨hx,h₂,hd,R,he,hn⟩ := shifted_vacuum K M A hM hA hK hsK u₀ T P hP
      hPair hS CA' hRem N hN r hr
    exact ⟨R, hn, approximate_residual B M A hM₀ hA.le hB hs u₀ N r hx h₂ hd R he⟩
  obtain ⟨_,_,hdom₀,_⟩ := hrs 0 (by simpa using hT)
  have hx₀ : x₀ ∈ (H).domain := hinit ▸ hdom₀
  have hw (r : ℝ) (hr : r ∈ uIcc 0 t) :
      ∃ z : (H).domain, z.val = w r ∧
      ∃ e : Fock L, ‖e‖ ≤ C ∧ HasDerivAt w ((-Complex.I) • H z + e) r := by
    obtain ⟨R,hR,hdom,hD⟩ := hrs r ((abs_le_of_between_zero hr).trans ht)
    let y : (H).domain := ⟨E r x₀, evolution_mem_domain B hs N ⟨x₀,hx₀⟩ r⟩
    let x : (H).domain := ⟨app r,hdom⟩
    let e := (-Complex.I) • (p r • printedWeyl (v r) R)
    refine ⟨y-x,rfl,e,?_,?_⟩
    · simpa only [e, norm_smul, norm_neg, Complex.norm_I, phase_norm, one_mul,
        LinearIsometryEquiv.norm_map] using hR
    · have he := manyBody_schrodinger B hs N ⟨x₀,hx₀⟩ r
      have hh := he.sub hD
      change HasDerivAt w ((-Complex.I) • H y -
        ((-Complex.I) • H x + Complex.I • (p r • printedWeyl (v r) R))) r at hh
      have heq : (-Complex.I) • H (y-x) + e = (-Complex.I) • H y -
          ((-Complex.I) • H x + Complex.I • (p r • printedWeyl (v r) R)) := by
        rw [LinearPMap.map_sub, smul_sub]
        simp only [e, neg_smul]
        abel
      rw [heq]
      exact hh
  have hnorm : ‖w t‖ ≤ C * |t-0| := by
    refine @norm_bound_of_energy (Fock L) _ _ w (fun r => deriv w r) 0 t C hC hzero ?_ ?_
    · intro r hr
      obtain ⟨z,_,e,_,he⟩ := hw r hr
      exact he.differentiableAt.hasDerivAt
    · intro r hr
      obtain ⟨z,hz,e,hne,he⟩ := hw r hr
      rw [he.deriv, inner_add_right]
      have hsk : ⟪w r,(-Complex.I) • H z⟫_ℝ = 0 := by
        rw [← hz]
        exact block_skew (sector B N) (sector_adjoint B hs N) z
      rw [hsk, zero_add]
      exact (abs_real_inner_le_norm _ _).trans (by
        rw [mul_comm C]
        exact mul_le_mul_of_nonneg_left hne (norm_nonneg _))
  have ht' : ‖w t‖ ≤ C*T :=
    (by simpa only [sub_zero] using hnorm : ‖w t‖ ≤ C*|t|).trans
      (mul_le_mul_of_nonneg_left ht hC)
  change ‖w t‖ ≤ _
  calc
    _ ≤ C*T := ht'
    _ = _ := by unfold C; ring

end PositiveRanks

end QuantumNLS.Prop021CoherentComparisonR131

#print axioms QuantumNLS.Prop021CoherentComparisonR131.coherent_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021CoherentComparisonR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
