import QuantumNLS.Def024Gradient

/-!
# DEF-024, stage D2: the order-0 and order-1 Hamiltonian flows

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:145-149`): "For a fixed finite set
of nonnegative orders `𝓡`, the joint classical flow is the composition of the Hamiltonian flows of
`I_{r+1}^{(κ)}` [...] Existence and commutation of the higher classical flows are proved with finite
loss."  The source theorem `thm:hierarchy` (R-7B122087) treats the orders `r ≥ 2` (through the global
chart); the orders `r = 0` (`I_1`, mass) and `r = 1` (`I_2`, momentum) of DEF-024's nonnegative-order
convention are constructed here explicitly, against the frozen `HierarchyFlow.IsHamFlow`.

* `phaseFlow s u = e^{−is} u` is the Hamiltonian flow of `Re I_1` (`phase_isHamFlow`);
* `transFlow s u = u(· − s)` is the Hamiltonian flow of `Re I_2` (`trans_isHamFlow`);
* uniqueness (`phase_unique`, `trans_unique`) on every open preconnected time set containing `0`,
  for smooth periodic solutions (order 1: jointly differentiable, weaker than the `C^∞` of
  `IsHamFlow`); consequently every `IsHamFlow` of these Hamiltonians equals the explicit one on the
  smooth periodic class (`isHamFlow_zero_eq`, `isHamFlow_one_eq`);
* commutation and group laws, the `HamFlows` family `lowHamFlows` for every `𝓡 ⊆ {0,1}`, the
  explicit joint flow `e^{−it_0} u(x − t_1)` and its uniqueness among all `HamFlows` families;
* conservation of the mass and of every `L²` norm of a spatial derivative;
* exact finite-loss identities: `∂_s^k ∂_x^m Φ_s u = (−i)^k e^{−is} ∂_x^m u` (order 0, no loss) and
  `∂_s^k ∂_x^m Φ_s u (x) = (−1)^k u^{(k+m)}(x − s)` (order 1, loss `k`), and the corresponding
  joint continuity estimates in every `C^m` seminorm (smooth topology).
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.Def024LowFlows

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024Gradient

variable {L : ℝ}

/-- The order-0 flow: `Φ_s u = e^{−is} u`. -/
def phaseFlow (s : ℝ) (u : ℝ → ℂ) : ℝ → ℂ := fun x => Complex.exp (-Complex.I * s) * u x

/-- The order-1 flow: `Φ_s u = u(· − s)`. -/
def transFlow (s : ℝ) (u : ℝ → ℂ) : ℝ → ℂ := fun x => u (x - s)

/-! ## Elementary calculus -/

theorem hasDerivAt_cexp_mul (c : ℂ) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => Complex.exp (c * s')) (c * Complex.exp (c * s)) s := by
  have h1 : HasDerivAt (fun s' : ℝ => ((s' : ℝ) : ℂ)) ((1 : ℝ) : ℂ) s :=
    (hasDerivAt_id' s).ofReal_comp
  have h2 := (h1.const_mul c).cexp
  convert h2 using 1
  push_cast
  ring

theorem exp_neg_mul_exp (s : ℝ) :
    Complex.exp (-Complex.I * s) * Complex.exp (Complex.I * s) = 1 := by
  rw [← Complex.exp_add]
  ring_nf
  exact Complex.exp_zero

theorem norm_exp_negI (s : ℝ) : ‖Complex.exp (-Complex.I * s)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem iteratedDeriv_periodic {u : ℝ → ℂ} (hp : Function.Periodic u L) (m : ℕ) :
    Function.Periodic (iteratedDeriv m u) L := by
  induction m with
  | zero => simpa using hp
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact WeakDerivatives.periodic_deriv ih

theorem contDiff_iteratedDeriv {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m u) := by
  rw [iteratedDeriv_eq_iterate]
  exact hu.iterate_deriv m

/-! ## Smoothness and the Hamiltonian equations -/

theorem phase_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    SmoothPeriodic L (phaseFlow s u) :=
  ⟨contDiff_const.mul hu.smooth, fun x => by simp only [phaseFlow, hu.periodic x]⟩

theorem trans_smooth {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    SmoothPeriodic L (transFlow s u) :=
  ⟨hu.smooth.comp (contDiff_id.sub contDiff_const), fun x => by
    simp only [transFlow]
    rw [show x + L - s = x - s + L by ring]
    exact hu.periodic (x - s)⟩

/-- **Existence, order 0**: `e^{−is}u` is a Hamiltonian flow of `Re I_1` on smooth periodic fields,
for all real times, jointly `C^∞` in `(s, x)`. -/
theorem phase_isHamFlow (κ : ℝ) : IsHamFlow L (hamiltonian L κ 0) phaseFlow := by
  intro u hu
  refine ⟨?_, ?_, fun s => ⟨phase_smooth hu s, phaseFlow s u,
    gradient_zero κ (phase_smooth hu s), fun x => ?_⟩⟩
  · funext x; simp [phaseFlow]
  · have h1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    exact (contDiff_const.mul h1).cexp.mul (hu.smooth.comp contDiff_snd)
  · have := (hasDerivAt_cexp_mul (-Complex.I) s).mul_const (u x)
    refine this.congr_deriv ?_
    rw [show phaseFlow s u x = Complex.exp (-Complex.I * s) * u x from rfl]
    ring

/-- **Existence, order 1**: `u(· − s)` is a Hamiltonian flow of `Re I_2` on smooth periodic fields,
for all real times, jointly `C^∞` in `(s, x)`. -/
theorem trans_isHamFlow (κ : ℝ) : IsHamFlow L (hamiltonian L κ 1) transFlow := by
  intro u hu
  have hdu := (contDiff_infty_iff_deriv.mp hu.smooth).1
  refine ⟨?_, ?_, fun s => ⟨trans_smooth hu s, _,
    gradient_one κ (trans_smooth hu s), fun x => ?_⟩⟩
  · funext x; simp [transFlow]
  · exact hu.smooth.comp (contDiff_snd.sub contDiff_fst)
  · have hd : deriv (transFlow s u) x = deriv u (x - s) := by
      show deriv (fun y => u (y - s)) x = deriv u (x - s)
      exact deriv_comp_sub_const u s x
    have := HasDerivAt.comp_const_sub x s ((hdu (x - s)).hasDerivAt)
    refine this.congr_deriv ?_
    show -deriv u (x - s) = -Complex.I * (-Complex.I * deriv (transFlow s u) x)
    rw [hd, ← mul_assoc, neg_mul_neg, Complex.I_mul_I]
    ring

/-! ## Uniqueness -/

/-- **Uniqueness, order 0**: on an open preconnected time set `J ∋ 0`, a family of smooth periodic
profiles solving `∂_s v = −i∇(Re I_1)(v)` (DEF-015 gradient) with `v 0 = u` is `e^{−is}u`. -/
theorem phase_unique (hL : 0 < L) (κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (h0 : (0 : ℝ) ∈ J) {v : ℝ → ℝ → ℂ} {u : ℝ → ℂ} (hv0 : v 0 = u)
    (hv : ∀ s ∈ J, SmoothPeriodic L (v s) ∧ ∃ g : ℝ → ℂ,
      IsSmoothGradient L (hamiltonian L κ 0) (v s) g ∧
        ∀ x, HasDerivAt (fun s' => v s' x) (-Complex.I * g x) s) :
    ∀ s ∈ J, v s = phaseFlow s u := by
  have hder : ∀ s ∈ J, ∀ x, HasDerivAt (fun s' => v s' x) (-Complex.I * v s x) s := by
    intro s hs x
    obtain ⟨hvs, g, hg, hd⟩ := hv s hs
    have hgs : g = v s := gradient_unique hL hg (gradient_zero κ hvs)
    simpa [hgs] using hd x
  intro s hs
  funext x
  set w : ℝ → ℂ := fun s' => Complex.exp (Complex.I * s') * v s' x with hw
  have hwd : ∀ t ∈ J, HasDerivAt w 0 t := by
    intro t ht
    have := (hasDerivAt_cexp_mul Complex.I t).mul (hder t ht x)
    convert this using 1
    ring
  have hconst : w s = w 0 :=
    hJ.is_const_of_deriv_eq_zero hJc (fun t ht => (hwd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hwd t ht).deriv) hs h0
  have hw0 : w 0 = u x := by simp [hw, hv0]
  have key : Complex.exp (Complex.I * s) * v s x = u x := by rw [← hw0, ← hconst]
  calc v s x = Complex.exp (-Complex.I * s) * (Complex.exp (Complex.I * s) * v s x) := by
        rw [← mul_assoc, exp_neg_mul_exp, one_mul]
    _ = phaseFlow s u x := by rw [key]; rfl

/-- **Uniqueness, order 1**: on an open preconnected time set `J ∋ 0`, a jointly differentiable
family of smooth periodic profiles solving `∂_s v = −i∇(Re I_2)(v)` (DEF-015 gradient) with
`v 0 = u` is `u(· − s)`. -/
theorem trans_unique (hL : 0 < L) (κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) (hJc : IsPreconnected J)
    (h0 : (0 : ℝ) ∈ J) {v : ℝ → ℝ → ℂ} {u : ℝ → ℂ} (hv0 : v 0 = u)
    (hdiff : ∀ s ∈ J, ∀ y : ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => v p.1 p.2) (s, y))
    (hv : ∀ s ∈ J, SmoothPeriodic L (v s) ∧ ∃ g : ℝ → ℂ,
      IsSmoothGradient L (hamiltonian L κ 1) (v s) g ∧
        ∀ x, HasDerivAt (fun s' => v s' x) (-Complex.I * g x) s) :
    ∀ s ∈ J, v s = transFlow s u := by
  have hder : ∀ s ∈ J, ∀ y, HasDerivAt (fun s' => v s' y) (-deriv (v s) y) s := by
    intro s hs y
    obtain ⟨hvs, g, hg, hd⟩ := hv s hs
    have hgs : g = fun x => -Complex.I * deriv (v s) x := gradient_unique hL hg (gradient_one κ hvs)
    have h := hd y
    rw [hgs] at h
    convert h using 1
    rw [← mul_assoc, neg_mul_neg, Complex.I_mul_I]
    ring
  intro s hs
  funext y
  -- characteristic: `w(t) = v t (x + t)` is constant
  set x : ℝ := y - s with hx
  have hwd : ∀ t ∈ J, HasDerivAt (fun t' => v t' (x + t')) 0 t := by
    intro t ht
    have hFd := (hdiff t ht (x + t)).hasFDerivAt
    set D := fderiv ℝ (fun p : ℝ × ℝ => v p.1 p.2) (t, x + t) with hD
    have hγ : HasDerivAt (fun t' : ℝ => (t', x + t')) ((1 : ℝ), (1 : ℝ)) t :=
      (hasDerivAt_id' t).prodMk ((hasDerivAt_id' t).const_add x)
    have hw := hFd.comp_hasDerivAt t hγ
    have h10 := hFd.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (x + t)))
    have h01 := hFd.comp_hasDerivAt (x + t)
      ((hasDerivAt_const (x + t) t).prodMk (hasDerivAt_id' (x + t)))
    have e10 : D ((1 : ℝ), (0 : ℝ)) = -deriv (v t) (x + t) := h10.unique (hder t ht (x + t))
    have e01 : D ((0 : ℝ), (1 : ℝ)) = deriv (v t) (x + t) := by
      have h01' : HasDerivAt (v t) (D ((0 : ℝ), (1 : ℝ))) (x + t) := h01
      exact h01'.deriv.symm
    have e11 : D ((1 : ℝ), (1 : ℝ)) = 0 := by
      have hsplit : ((1 : ℝ), (1 : ℝ)) = ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by simp
      rw [hsplit, map_add, e10, e01]
      ring
    rw [← e11]
    exact hw
  have hconst : (fun t' => v t' (x + t')) s = (fun t' => v t' (x + t')) 0 :=
    hJ.is_const_of_deriv_eq_zero hJc
      (fun t ht => (hwd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hwd t ht).deriv) hs h0
  simp only [add_zero, hv0] at hconst
  rw [show x + s = y by rw [hx]; ring] at hconst
  rw [hconst]
  rfl

/-- Every Hamiltonian flow of `Re I_1` (frozen `IsHamFlow`) is `e^{−is}u` on smooth periodic data. -/
theorem isHamFlow_zero_eq (hL : 0 < L) (κ : ℝ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 0) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    Φ s u = phaseFlow s u :=
  phase_unique hL κ isOpen_univ isPreconnected_univ (Set.mem_univ 0) (v := fun s => Φ s u)
    (hΦ u hu).1 (fun s _ => (hΦ u hu).2.2 s) s (Set.mem_univ s)

/-- Every Hamiltonian flow of `Re I_2` (frozen `IsHamFlow`) is `u(· − s)` on smooth periodic data. -/
theorem isHamFlow_one_eq (hL : 0 < L) (κ : ℝ) {Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)}
    (hΦ : IsHamFlow L (hamiltonian L κ 1) Φ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    Φ s u = transFlow s u :=
  trans_unique hL κ isOpen_univ isPreconnected_univ (Set.mem_univ 0) (v := fun s => Φ s u)
    (hΦ u hu).1
    (fun _ _ y => ((hΦ u hu).2.1.differentiable (by simp)).differentiableAt (x := (_, y)))
    (fun s _ => (hΦ u hu).2.2 s) s (Set.mem_univ s)

/-! ## Commutation, group laws and the joint flow -/

theorem phase_trans_comm (t a : ℝ) (u : ℝ → ℂ) :
    phaseFlow t (transFlow a u) = transFlow a (phaseFlow t u) := rfl

theorem phase_add (s t : ℝ) (u : ℝ → ℂ) :
    phaseFlow s (phaseFlow t u) = phaseFlow (s + t) u := by
  funext x
  simp only [phaseFlow]
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem trans_add (s t : ℝ) (u : ℝ → ℂ) :
    transFlow s (transFlow t u) = transFlow (s + t) u := by
  funext x
  simp only [transFlow]
  ring_nf

/-- The flow map attached to each order: `0 ↦ e^{−is}`, `1 ↦` translation (other orders unused). -/
def lowFlowMap : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0 => phaseFlow
  | 1 => transFlow
  | _ + 2 => fun _ u => u

/-- All the low-order flow maps commute (on every profile, for all times). -/
theorem lowFlowMap_comm (r r' : ℕ) (t a : ℝ) (u : ℝ → ℂ) :
    lowFlowMap r t (lowFlowMap r' a u) = lowFlowMap r' a (lowFlowMap r t u) := by
  match r, r' with
  | 0, 0 => simp only [lowFlowMap, phase_add, add_comm]
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => simp only [lowFlowMap, trans_add, add_comm]
  | 0, _ + 2 => rfl
  | 1, _ + 2 => rfl
  | _ + 2, _ => rfl

/-- **The DEF-024 family for `𝓡 ⊆ {0,1}`**: an inhabitant of the frozen `HamFlows`. -/
def lowHamFlows (L κ : ℝ) (𝓡 : Finset ℕ) (h𝓡 : 𝓡 ⊆ {0, 1}) : HamFlows L κ 𝓡 where
  Φ := lowFlowMap
  ham := fun r hr => by
    have := h𝓡 hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with rfl | rfl
    · exact phase_isHamFlow κ
    · exact trans_isHamFlow κ

/-- Any `HamFlows` family for `𝓡 ⊆ {0,1}` agrees with the explicit flows on smooth periodic data. -/
theorem hamFlows_eq (hL : 0 < L) {κ : ℝ} {𝓡 : Finset ℕ} (h𝓡 : 𝓡 ⊆ {0, 1})
    (F : HamFlows L κ 𝓡) {r : ℕ} (hr : r ∈ 𝓡) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    F.Φ r s u = lowFlowMap r s u := by
  have := h𝓡 hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl
  · exact isHamFlow_zero_eq hL κ (F.ham 0 hr) hu s
  · exact isHamFlow_one_eq hL κ (F.ham 1 hr) hu s

theorem sort_zero_one : (({0, 1} : Finset ℕ).sort (· ≤ ·)) = [0, 1] := by
  rw [Finset.sort_insert (· ≤ ·) (by simp) (by simp), Finset.sort_singleton]

/-- **The joint classical flow for `𝓡 = {0,1}`** is `e^{−i t_0} u(x − t_1)`. -/
theorem jointClassicalFlow_low (L κ : ℝ) (t : ℕ → ℝ) (u : ℝ → ℂ) :
    jointClassicalFlow (lowHamFlows L κ {0, 1} subset_rfl) t u =
      fun x => Complex.exp (-Complex.I * t 0) * u (x - t 1) := by
  simp only [jointClassicalFlow, sort_zero_one, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, Function.comp_id]
  rfl

/-- **Uniqueness of the joint flow**: for every `HamFlows` family with `𝓡 = {0,1}` and every
smooth periodic `u`, the joint flow is `e^{−i t_0} u(x − t_1)`. -/
theorem jointClassicalFlow_unique (hL : 0 < L) {κ : ℝ} (F : HamFlows L κ {0, 1}) (t : ℕ → ℝ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    jointClassicalFlow F t u = fun x => Complex.exp (-Complex.I * t 0) * u (x - t 1) := by
  simp only [jointClassicalFlow, sort_zero_one, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, Function.comp_id, Function.comp_apply]
  have h1 : F.Φ 1 (t 1) u = transFlow (t 1) u :=
    hamFlows_eq hL subset_rfl F (by simp) hu (t 1)
  rw [h1, hamFlows_eq hL subset_rfl F (by simp) (trans_smooth hu (t 1)) (t 0)]
  rfl

/-! ## Conservation laws -/

theorem phase_iteratedDeriv (s : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    iteratedDeriv m (phaseFlow s u) = fun x => Complex.exp (-Complex.I * s) * iteratedDeriv m u x := by
  induction m with
  | zero => rw [iteratedDeriv_zero, iteratedDeriv_zero]; rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, ih]
    funext x
    have hd := (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv hu m)).1 x
    exact (hd.hasDerivAt.const_mul _).deriv

theorem trans_iteratedDeriv (s : ℝ) (u : ℝ → ℂ) (m : ℕ) :
    iteratedDeriv m (transFlow s u) = fun x => iteratedDeriv m u (x - s) :=
  iteratedDeriv_comp_sub_const m u s

/-- **Order 0 conserves every `L²` norm of a spatial derivative** (in particular the mass, `m = 0`). -/
theorem phase_conserves (s : ℝ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    ∫ x in (0 : ℝ)..L, ‖iteratedDeriv m (phaseFlow s u) x‖ ^ 2 =
      ∫ x in (0 : ℝ)..L, ‖iteratedDeriv m u x‖ ^ 2 := by
  rw [phase_iteratedDeriv s hu m]
  simp only [norm_mul, norm_exp_negI, one_mul]

/-- **Order 1 conserves every `L²` norm of a spatial derivative** (in particular the mass, `m = 0`). -/
theorem trans_conserves (s : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (m : ℕ) :
    ∫ x in (0 : ℝ)..L, ‖iteratedDeriv m (transFlow s u) x‖ ^ 2 =
      ∫ x in (0 : ℝ)..L, ‖iteratedDeriv m u x‖ ^ 2 := by
  rw [trans_iteratedDeriv]
  have hp : Function.Periodic (fun x => ‖iteratedDeriv m u x‖ ^ 2) L := fun x => by
    simp only [iteratedDeriv_periodic hu.periodic m x]
  rw [intervalIntegral.integral_comp_sub_right (fun x => ‖iteratedDeriv m u x‖ ^ 2) s]
  have := hp.intervalIntegral_add_eq (0 - s) 0
  rw [show (0 : ℝ) - s + L = L - s by ring, zero_add] at this
  exact this

/-- Mass conservation for both flows (`I_1 = ∫ |u|²`). -/
theorem mass_conserved (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    hamiltonian L κ 0 (phaseFlow s u) = hamiltonian L κ 0 u ∧
      hamiltonian L κ 0 (transFlow s u) = hamiltonian L κ 0 u := by
  simp only [hamiltonian_zero]
  have h0 := phase_conserves (L := L) s hu.smooth 0
  have h1 := trans_conserves s hu 0
  simp only [iteratedDeriv_zero] at h0 h1
  exact ⟨h0, h1⟩

/-! ## Finite loss -/

theorem iteratedDeriv_phase_time (c : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => Complex.exp (-Complex.I * s) * c) =
      fun s : ℝ => (-Complex.I) ^ k * (Complex.exp (-Complex.I * s) * c) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have := (((hasDerivAt_cexp_mul (-Complex.I) s).mul_const c).const_mul ((-Complex.I) ^ k)).deriv
    rw [this, pow_succ]
    ring

/-- **Order 0, no loss**: `∂_s^k ∂_x^m (e^{−is}u) = (−i)^k e^{−is} ∂_x^m u`. -/
theorem phase_time_space (k m : ℕ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (x s : ℝ) :
    iteratedDeriv k (fun s' => iteratedDeriv m (phaseFlow s' u) x) s =
      (-Complex.I) ^ k * phaseFlow s (iteratedDeriv m u) x := by
  have : (fun s' => iteratedDeriv m (phaseFlow s' u) x) =
      fun s' : ℝ => Complex.exp (-Complex.I * s') * iteratedDeriv m u x := by
    funext s'; rw [phase_iteratedDeriv s' hu m]
  rw [this, iteratedDeriv_phase_time]
  rfl

/-- **Order 1, loss exactly `k`**: `∂_s^k ∂_x^m (u(x − s)) = (−1)^k u^{(k+m)}(x − s)`. -/
theorem trans_time_space (k m : ℕ) (u : ℝ → ℂ) (x s : ℝ) :
    iteratedDeriv k (fun s' => iteratedDeriv m (transFlow s' u) x) s =
      ((-1 : ℝ) ^ k : ℝ) • iteratedDeriv (k + m) u (x - s) := by
  have : (fun s' => iteratedDeriv m (transFlow s' u) x) = fun s' => iteratedDeriv m u (x - s') := by
    funext s'; rw [trans_iteratedDeriv]
  have e : iteratedDeriv k (iteratedDeriv m u) = iteratedDeriv (k + m) u := by
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
      Function.iterate_add_apply]
  rw [this, iteratedDeriv_comp_const_sub]
  simp only
  rw [e]

/-- **Order 1, `L²` finite-loss identity**: `‖∂_s^k ∂_x^m Φ_s u‖_{L²} = ‖∂_x^{k+m} u‖_{L²}`. -/
theorem trans_time_space_L2 (k m : ℕ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    ∫ x in (0 : ℝ)..L, ‖iteratedDeriv k (fun s' => iteratedDeriv m (transFlow s' u) x) s‖ ^ 2 =
      ∫ x in (0 : ℝ)..L, ‖iteratedDeriv (k + m) u x‖ ^ 2 := by
  simp only [trans_time_space, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := trans_conserves s hu (k + m)
  rw [trans_iteratedDeriv] at this
  exact this

/-- **Order 0, `L²` identity**: `‖∂_s^k ∂_x^m Φ_s u‖_{L²} = ‖∂_x^m u‖_{L²}`. -/
theorem phase_time_space_L2 (k m : ℕ) {u : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (s : ℝ) :
    ∫ x in (0 : ℝ)..L, ‖iteratedDeriv k (fun s' => iteratedDeriv m (phaseFlow s' u) x) s‖ ^ 2 =
      ∫ x in (0 : ℝ)..L, ‖iteratedDeriv m u x‖ ^ 2 := by
  simp only [phase_time_space k m hu, phaseFlow, norm_mul, norm_pow, norm_neg, Complex.norm_I,
    one_pow, one_mul, norm_exp_negI]

/-- **Joint continuity in every `C^m` seminorm, order 1**: if `|u^{(m+1)}| ≤ C` and
`|u^{(m)} − v^{(m)}| ≤ δ` pointwise, then `|∂_x^m Φ_s u − ∂_x^m Φ_{s'} v| ≤ C|s − s'| + δ`. -/
theorem trans_continuity (m : ℕ) {u v : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) {C δ : ℝ}
    (hC : ∀ y, ‖iteratedDeriv (m + 1) u y‖ ≤ C)
    (hδ : ∀ y, ‖iteratedDeriv m u y - iteratedDeriv m v y‖ ≤ δ) (s s' x : ℝ) :
    ‖iteratedDeriv m (transFlow s u) x - iteratedDeriv m (transFlow s' v) x‖ ≤ C * |s - s'| + δ := by
  rw [trans_iteratedDeriv, trans_iteratedDeriv]
  have hdiff : ∀ y ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (iteratedDeriv m u) y :=
    fun y _ => (contDiff_infty_iff_deriv.mp (contDiff_iteratedDeriv hu m)).1 y
  have hbound : ∀ y ∈ (Set.univ : Set ℝ), ‖deriv (iteratedDeriv m u) y‖ ≤ C := fun y _ => by
    rw [← iteratedDeriv_succ]; exact hC y
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound convex_univ
    (Set.mem_univ (x - s')) (Set.mem_univ (x - s))
  have e : ‖(x - s) - (x - s')‖ = |s - s'| := by
    rw [Real.norm_eq_abs, show (x - s) - (x - s') = s' - s by ring, abs_sub_comm]
  rw [e] at hmvt
  calc ‖iteratedDeriv m u (x - s) - iteratedDeriv m v (x - s')‖
      ≤ ‖iteratedDeriv m u (x - s) - iteratedDeriv m u (x - s')‖ +
          ‖iteratedDeriv m u (x - s') - iteratedDeriv m v (x - s')‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C * |s - s'| + δ := add_le_add hmvt (hδ _)

/-- **Joint continuity in every `C^m` seminorm, order 0**: if `|u^{(m)}| ≤ A` and
`|u^{(m)} − v^{(m)}| ≤ δ` pointwise, then `|∂_x^m Φ_s u − ∂_x^m Φ_{s'} v| ≤ A|s − s'| + δ`. -/
theorem phase_continuity (m : ℕ) {u v : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) {A δ : ℝ}
    (hA : ∀ y, ‖iteratedDeriv m u y‖ ≤ A)
    (hδ : ∀ y, ‖iteratedDeriv m u y - iteratedDeriv m v y‖ ≤ δ) (s s' x : ℝ) :
    ‖iteratedDeriv m (phaseFlow s u) x - iteratedDeriv m (phaseFlow s' v) x‖ ≤ A * |s - s'| + δ := by
  rw [phase_iteratedDeriv s hu, phase_iteratedDeriv s' hv]
  set c := iteratedDeriv m u x
  have hd : ∀ y ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * t) * c)
        (-Complex.I * Complex.exp (-Complex.I * y) * c) y :=
    fun y _ => (hasDerivAt_cexp_mul (-Complex.I) y).mul_const c
  have hbound : ∀ y ∈ (Set.univ : Set ℝ),
      ‖deriv (fun t : ℝ => Complex.exp (-Complex.I * t) * c) y‖ ≤ A := fun y hy => by
    rw [(hd y hy).deriv, norm_mul, norm_mul, norm_neg, Complex.norm_I, norm_exp_negI, one_mul,
      one_mul]
    exact hA x
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (fun y hy => (hd y hy).differentiableAt)
    hbound convex_univ (Set.mem_univ s') (Set.mem_univ s)
  rw [Real.norm_eq_abs] at hmvt
  have h2 : ‖Complex.exp (-Complex.I * s') * c - Complex.exp (-Complex.I * s') * iteratedDeriv m v x‖
      ≤ δ := by
    rw [← mul_sub, norm_mul, norm_exp_negI, one_mul]; exact hδ x
  calc ‖Complex.exp (-Complex.I * s) * c - Complex.exp (-Complex.I * s') * iteratedDeriv m v x‖
      ≤ ‖Complex.exp (-Complex.I * s) * c - Complex.exp (-Complex.I * s') * c‖ +
          ‖Complex.exp (-Complex.I * s') * c - Complex.exp (-Complex.I * s') * iteratedDeriv m v x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ A * |s - s'| + δ := by
        exact add_le_add hmvt h2

/-! Kernel axiom audit. -/
#print axioms hasDerivAt_cexp_mul
#print axioms phase_isHamFlow
#print axioms trans_isHamFlow
#print axioms phase_unique
#print axioms trans_unique
#print axioms isHamFlow_zero_eq
#print axioms isHamFlow_one_eq
#print axioms phase_trans_comm
#print axioms phase_add
#print axioms trans_add
#print axioms lowFlowMap_comm
#print axioms lowHamFlows
#print axioms hamFlows_eq
#print axioms jointClassicalFlow_low
#print axioms jointClassicalFlow_unique
#print axioms phase_conserves
#print axioms trans_conserves
#print axioms mass_conserved
#print axioms phase_time_space
#print axioms trans_time_space
#print axioms trans_time_space_L2
#print axioms phase_time_space_L2
#print axioms trans_continuity
#print axioms phase_continuity

end QuantumNLS.Def024LowFlows
