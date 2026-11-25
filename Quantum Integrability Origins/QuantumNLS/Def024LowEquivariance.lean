import QuantumNLS.Def024LowFlows

/-!
# DEF-024, stage D3: the order-0/1 flows against every charge and every higher Hamiltonian flow

Source: DEF-024 (`chapters/definitions.tex:145-149`), DEF-022 recursion `v_1 = u`,
`v_{j+1} = −i ∂ₓ v_j + κ ū ∑_{a=1}^{j−1} v_a v_{j−a}`, `I_j = ∫ ū v_j`; `thm:hierarchy`
(R-7B122087, DYNAMICS_LEMMAS.tex:115-197: "All local charges [...] are conserved", "Every finite
family of these flows commutes").

What is proved (no assumption on the higher flows beyond the frozen `IsHamFlow`):
* `vseq_mul_unit`, `charge_mul_unit`: for a unit phase `c` (`c̄ c = 1`), `v_j(cu) = c v_j(u)` and
  `I_j(cu) = I_j(u)` for every `j` (every profile);
* `vseq_trans`, `charge_trans`: `v_j(u(·−s)) = v_j(u)(·−s)` and `I_j(u(·−s)) = I_j(u)` (smooth
  periodic `u`);
  hence **every charge `I_j` is conserved by the order-0 and order-1 flows** (`charge_conserved_low`);
* `grad_phase`, `grad_trans`: the DEF-015 gradient of a phase- (resp. translation-) invariant
  functional is equivariant;
* `phase_conj_isHamFlow`, `trans_conj_isHamFlow`: for every order `r` and every Hamiltonian flow
  `Φ` of `Re I_{r+1}` (frozen `IsHamFlow`), the conjugated maps `e^{−ia} Φ_s(e^{ia} ·)` and
  `Φ_s(· + a)(· − a)` are again Hamiltonian flows of `Re I_{r+1}`;
* `comm_low_of_unique`: consequently, **if** the flow of `Re I_{r+1}` is unique on the smooth
  periodic class (the predicate `UniqueHamFlow`, which is the still-open uniqueness clause of
  R-7B122087 for `r ≥ 2`, proved here for `r = 0, 1`: `unique_low`), it commutes with the order-0
  and order-1 flows.  `UniqueHamFlow` is a named hypothesis of that implication only; it is not
  assumed anywhere else and is not claimed for `r ≥ 2`.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.Def024LowEquivariance

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024Gradient
  QuantumNLS.Def024LowFlows

variable {L : ℝ}

/-! ## Charges under a unit phase -/

theorem vseq_mul_unit (κ : ℝ) {c : ℂ} (hc : conj c * c = 1) (u : ℝ → ℂ) (j : ℕ) :
    vseq κ (fun x => c * u x) j = fun x => c * vseq κ u j x := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => funext x; simp only [vseq, mul_zero]
    | 1, _ => rw [vseq_one, vseq_one]
    | k + 2, ih =>
      rw [vseq_succ, vseq_succ]
      funext x
      beta_reduce
      have hs : ∑ a ∈ Finset.Icc 1 k,
          vseq κ (fun x => c * u x) a x * vseq κ (fun x => c * u x) (k + 1 - a) x
          = c ^ 2 * ∑ a ∈ Finset.Icc 1 k, vseq κ u a x * vseq κ u (k + 1 - a) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have ha' := Finset.mem_Icc.mp ha
        rw [ih a (by omega), ih (k + 1 - a) (by omega)]
        ring
      rw [hs, ih (k + 1) (by omega), deriv_const_mul_field, map_mul]
      linear_combination ((κ : ℂ) * conj (u x) * c *
        ∑ a ∈ Finset.Icc 1 k, vseq κ u a x * vseq κ u (k + 1 - a) x) * hc

theorem charge_mul_unit (L κ : ℝ) {c : ℂ} (hc : conj c * c = 1) (u : ℝ → ℂ) (j : ℕ) :
    charge L κ (fun x => c * u x) j = charge L κ u j := by
  unfold charge
  rw [vseq_mul_unit κ hc]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  beta_reduce
  rw [map_mul]
  linear_combination (conj (u x) * vseq κ u j x) * hc

theorem conj_exp_negI_mul (a : ℝ) :
    conj (Complex.exp (-Complex.I * a)) * Complex.exp (-Complex.I * a) = 1 := by
  rw [Complex.conj_mul', norm_exp_negI]
  simp

theorem conj_exp_negI (a : ℝ) :
    conj (Complex.exp (-Complex.I * a)) = Complex.exp (-Complex.I * ((-a : ℝ) : ℂ)) := by
  rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- Every charge is invariant under the order-0 flow (every profile). -/
theorem charge_phase (L κ : ℝ) (a : ℝ) (u : ℝ → ℂ) (j : ℕ) :
    charge L κ (phaseFlow a u) j = charge L κ u j :=
  charge_mul_unit L κ (conj_exp_negI_mul a) u j

/-! ## Charges under translation -/

theorem vseq_trans (κ : ℝ) (u : ℝ → ℂ) (s : ℝ) (j : ℕ) :
    vseq κ (fun x => u (x - s)) j = fun x => vseq κ u j (x - s) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => funext x; simp only [vseq]
    | 1, _ => rw [vseq_one, vseq_one]
    | k + 2, ih =>
      rw [vseq_succ, vseq_succ]
      funext x
      beta_reduce
      have hs : ∑ a ∈ Finset.Icc 1 k,
          vseq κ (fun x => u (x - s)) a x * vseq κ (fun x => u (x - s)) (k + 1 - a) x
          = ∑ a ∈ Finset.Icc 1 k, vseq κ u a (x - s) * vseq κ u (k + 1 - a) (x - s) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have ha' := Finset.mem_Icc.mp ha
        rw [ih a (by omega), ih (k + 1 - a) (by omega)]
      rw [hs, ih (k + 1) (by omega), deriv_comp_sub_const]

/-- `∫₀^L f(x − s) dx = ∫₀^L f` for `L`-periodic `f`. -/
theorem integral_shift {f : ℝ → ℂ} (hp : Function.Periodic f L) (s : ℝ) :
    ∫ x in (0 : ℝ)..L, f (x - s) = ∫ x in (0 : ℝ)..L, f x := by
  rw [intervalIntegral.integral_comp_sub_right f s]
  have := hp.intervalIntegral_add_eq (0 - s) 0
  rw [show (0 : ℝ) - s + L = L - s by ring, zero_add] at this
  exact this

/-- Every charge is invariant under the order-1 flow (smooth periodic profiles). -/
theorem charge_trans (L κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) (j : ℕ) :
    charge L κ (transFlow s u) j = charge L κ u j := by
  unfold charge
  have e : (fun x => conj (transFlow s u x) * vseq κ (transFlow s u) j x) =
      fun x => (fun y => conj (u y) * vseq κ u j y) (x - s) := by
    funext x
    rw [show transFlow s u = fun x => u (x - s) from rfl, vseq_trans]
  rw [e]
  refine integral_shift (f := fun y => conj (u y) * vseq κ u j y) (fun y => ?_) s
  show conj (u (y + L)) * vseq κ u j (y + L) = conj (u y) * vseq κ u j y
  rw [hu.periodic y, (vseq_regular κ hu j).2 y]

/-- **Every charge `I_j` is conserved by the order-0 and order-1 flows.** -/
theorem charge_conserved_low (L κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (a : ℝ) (j : ℕ) :
    charge L κ (phaseFlow a u) j = charge L κ u j ∧ charge L κ (transFlow a u) j = charge L κ u j :=
  ⟨charge_phase L κ a u j, charge_trans L κ hu a j⟩

/-! ## Gradient equivariance -/

theorem phase_neg_cancel (a : ℝ) (w : ℝ → ℂ) : phaseFlow a (phaseFlow (-a) w) = w := by
  rw [phase_add, add_neg_cancel]
  funext x
  simp [phaseFlow]

theorem trans_neg_cancel (a : ℝ) (w : ℝ → ℂ) : transFlow a (transFlow (-a) w) = w := by
  rw [trans_add, add_neg_cancel]
  funext x
  simp [transFlow]

/-- The DEF-015 gradient of a phase-invariant functional is phase-equivariant. -/
theorem grad_phase {F : (ℝ → ℂ) → ℝ}
    (hF : ∀ v : ℝ → ℂ, SmoothPeriodic L v → ∀ a : ℝ, F (phaseFlow a v) = F v)
    {w g : ℝ → ℂ} (hw : SmoothPeriodic L w) (hg : IsSmoothGradient L F w g) (a : ℝ) :
    IsSmoothGradient L F (phaseFlow a w) (phaseFlow a g) := by
  refine ⟨phase_smooth hg.1 a, fun h hh => ?_⟩
  set h' := phaseFlow (-a) h with hh'
  have hh'S : SmoothPeriodic L h' := phase_smooth hh (-a)
  have hfun : (fun ε : ℝ => F (fun x => phaseFlow a w x + (ε : ℂ) * h x)) =
      fun ε : ℝ => F (fun x => w x + (ε : ℂ) * h' x) := by
    funext ε
    have hS : SmoothPeriodic L (fun x => w x + (ε : ℂ) * h' x) :=
      ⟨hw.smooth.add (contDiff_const.mul hh'S.smooth), fun x => by
        simp only [hw.periodic x, hh'S.periodic x]⟩
    rw [← hF _ hS a]
    congr 1
    funext x
    have e := congrFun (phase_neg_cancel a h) x
    simp only [phaseFlow] at e ⊢
    rw [hh', ← e]
    simp only [phaseFlow]
    ring
  rw [hfun]
  refine (hg.2 h' hh'S).congr_deriv ?_
  congr 2
  unfold pair
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hh', phaseFlow]
  rw [map_mul, conj_exp_negI]
  ring

/-- The DEF-015 gradient of a translation-invariant functional is translation-equivariant. -/
theorem grad_trans {F : (ℝ → ℂ) → ℝ}
    (hF : ∀ v : ℝ → ℂ, SmoothPeriodic L v → ∀ a : ℝ, F (transFlow a v) = F v)
    {w g : ℝ → ℂ} (hw : SmoothPeriodic L w) (hg : IsSmoothGradient L F w g) (a : ℝ) :
    IsSmoothGradient L F (transFlow a w) (transFlow a g) := by
  refine ⟨trans_smooth hg.1 a, fun h hh => ?_⟩
  set h' := transFlow (-a) h with hh'
  have hh'S : SmoothPeriodic L h' := trans_smooth hh (-a)
  have hfun : (fun ε : ℝ => F (fun x => transFlow a w x + (ε : ℂ) * h x)) =
      fun ε : ℝ => F (fun x => w x + (ε : ℂ) * h' x) := by
    funext ε
    have hS : SmoothPeriodic L (fun x => w x + (ε : ℂ) * h' x) :=
      ⟨hw.smooth.add (contDiff_const.mul hh'S.smooth), fun x => by
        simp only [hw.periodic x, hh'S.periodic x]⟩
    rw [← hF _ hS a]
    congr 1
    funext x
    simp only [hh', transFlow]
    rw [show x - a - -a = x by ring]
  rw [hfun]
  refine (hg.2 h' hh'S).congr_deriv ?_
  congr 2
  unfold pair
  have hp : Function.Periodic (fun y => conj (g y) * h' y) L := fun y => by
    simp only [hg.1.periodic y, hh'S.periodic y]
  rw [← integral_shift hp a]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [hh', transFlow]
  rw [show x - a - -a = x by ring]

/-! ## Conjugated higher flows -/

/-- For a phase-invariant `F`, `e^{−ia} Φ_s(e^{ia} ·)` is again a Hamiltonian flow of `F`. -/
theorem phase_conj_isHamFlow {F : (ℝ → ℂ) → ℝ}
    (hF : ∀ v : ℝ → ℂ, SmoothPeriodic L v → ∀ a : ℝ, F (phaseFlow a v) = F v)
    {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΦ : IsHamFlow L F Φ) (a : ℝ) :
    IsHamFlow L F (fun s w => phaseFlow a (Φ s (phaseFlow (-a) w))) := by
  intro w hw
  have hu : SmoothPeriodic L (phaseFlow (-a) w) := phase_smooth hw (-a)
  obtain ⟨h0, hsm, hs⟩ := hΦ _ hu
  refine ⟨?_, ?_, fun s => ?_⟩
  · simp only [h0]; exact phase_neg_cancel a w
  · exact contDiff_const.mul hsm
  · obtain ⟨hS, g, hg, hd⟩ := hs s
    refine ⟨phase_smooth hS a, phaseFlow a g, grad_phase hF hS hg a, fun x => ?_⟩
    refine ((hd x).const_mul (Complex.exp (-Complex.I * a))).congr_deriv ?_
    rw [show phaseFlow a g x = Complex.exp (-Complex.I * a) * g x from rfl]
    ring

/-- For a translation-invariant `F`, `Φ_s(· (+a))(· − a)` is again a Hamiltonian flow of `F`. -/
theorem trans_conj_isHamFlow {F : (ℝ → ℂ) → ℝ}
    (hF : ∀ v : ℝ → ℂ, SmoothPeriodic L v → ∀ a : ℝ, F (transFlow a v) = F v)
    {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)} (hΦ : IsHamFlow L F Φ) (a : ℝ) :
    IsHamFlow L F (fun s w => transFlow a (Φ s (transFlow (-a) w))) := by
  intro w hw
  have hu : SmoothPeriodic L (transFlow (-a) w) := trans_smooth hw (-a)
  obtain ⟨h0, hsm, hs⟩ := hΦ _ hu
  refine ⟨?_, ?_, fun s => ?_⟩
  · simp only [h0]; exact trans_neg_cancel a w
  · exact hsm.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))
  · obtain ⟨hS, g, hg, hd⟩ := hs s
    exact ⟨trans_smooth hS a, transFlow a g, grad_trans hF hS hg a, fun x => hd (x - a)⟩

/-! ## Specialization to the DEF-022 Hamiltonians -/

theorem hamiltonian_phase (L κ : ℝ) (r : ℕ) (v : ℝ → ℂ) (a : ℝ) :
    hamiltonian L κ r (phaseFlow a v) = hamiltonian L κ r v := by
  simp only [hamiltonian, charge_phase]

theorem hamiltonian_trans (L κ : ℝ) (r : ℕ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (a : ℝ) :
    hamiltonian L κ r (transFlow a v) = hamiltonian L κ r v := by
  simp only [hamiltonian, charge_trans L κ hv]

/-- Uniqueness of the Hamiltonian flow `Φ` of `F` on the smooth periodic class. -/
def UniqueHamFlow (L : ℝ) (F : (ℝ → ℂ) → ℝ) (Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)) : Prop :=
  ∀ Ψ : ℝ → (ℝ → ℂ) → (ℝ → ℂ), IsHamFlow L F Ψ →
    ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s : ℝ, Ψ s u = Φ s u

/-- The uniqueness predicate holds for the orders `0` and `1` (proved in D2). -/
theorem unique_low (hL : 0 < L) (κ : ℝ) :
    UniqueHamFlow L (hamiltonian L κ 0) phaseFlow ∧ UniqueHamFlow L (hamiltonian L κ 1) transFlow :=
  ⟨fun _ hΨ _ hu s => isHamFlow_zero_eq hL κ hΨ hu s,
    fun _ hΨ _ hu s => isHamFlow_one_eq hL κ hΨ hu s⟩

/-- **Commutation with the order-0 and order-1 flows**: for every order `r`, a Hamiltonian flow
`Φ` of `Re I_{r+1}` which is unique on the smooth periodic class commutes, on smooth periodic data,
with `e^{−ia}` and with translation by `a`, for all real `s, a`. -/
theorem comm_low_of_unique (κ : ℝ) (r : ℕ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ r) Φ) (huniq : UniqueHamFlow L (hamiltonian L κ r) Φ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s a : ℝ) :
    Φ s (phaseFlow a u) = phaseFlow a (Φ s u) ∧ Φ s (transFlow a u) = transFlow a (Φ s u) := by
  constructor
  · have hΨ := phase_conj_isHamFlow (fun v _ a => hamiltonian_phase L κ r v a) hΦ a
    have := huniq _ hΨ (phaseFlow a u) (phase_smooth hu a) s
    have e : phaseFlow (-a) (phaseFlow a u) = u := by
      rw [phase_add, neg_add_cancel]; funext x; simp [phaseFlow]
    calc Φ s (phaseFlow a u) = phaseFlow a (Φ s (phaseFlow (-a) (phaseFlow a u))) := this.symm
      _ = phaseFlow a (Φ s u) := by rw [e]
  · have hΨ := trans_conj_isHamFlow (fun v hv a => hamiltonian_trans L κ r hv a) hΦ a
    have := huniq _ hΨ (transFlow a u) (trans_smooth hu a) s
    have e : transFlow (-a) (transFlow a u) = u := by
      rw [trans_add, neg_add_cancel]; funext x; simp [transFlow]
    calc Φ s (transFlow a u) = transFlow a (Φ s (transFlow (-a) (transFlow a u))) := this.symm
      _ = transFlow a (Φ s u) := by rw [e]

/-! Kernel axiom audit. -/
#print axioms vseq_mul_unit
#print axioms charge_mul_unit
#print axioms conj_exp_negI
#print axioms charge_phase
#print axioms vseq_trans
#print axioms integral_shift
#print axioms charge_trans
#print axioms charge_conserved_low
#print axioms grad_phase
#print axioms grad_trans
#print axioms phase_conj_isHamFlow
#print axioms trans_conj_isHamFlow
#print axioms hamiltonian_phase
#print axioms hamiltonian_trans
#print axioms unique_low
#print axioms comm_low_of_unique

end QuantumNLS.Def024LowEquivariance
