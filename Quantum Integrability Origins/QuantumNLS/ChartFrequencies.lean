import Mathlib
import QuantumNLS.SymplecticBracket
import QuantumNLS.RephasingFlow

/-!
# R-E28AD0D3 `lem:frequency`: exact-action canonical charts have the same flow frequencies

Source: `source-text/chapters/core/DYNAMICS_LEMMAS.tex` (Lemma `lem:frequency`, ~line 329, with proof).
Owner: sonnet_fourier.  Frozen read-only imports: `SymplecticBracket` (DEF-015 `omega = 2 Im⟨·,·⟩`) and
`RephasingFlow` (`E = ℓ²(ℤ)`, `rotE`, `pr`, `IsStrongSymplecticDiffeo`, the flow `U` used for a
non-vacuity instance).

Printed proof followed step by step:
* the transition `S = Φ₂ Φ₁⁻¹` is canonical (`transition_canonical`) and preserves each action;
* it intertwines the Hamiltonian vector field `X_n = -i z_n e_n` of each action (`Xn_intertwine`:
  `Ω(X_n(Sw) - DS X_n(w), DS h) = 0`, nondegeneracy, `DS` onto), hence the complete flow, which is the
  rotation of coordinate `n` (`equivariant_single`: the curve `S(ρ_t z)` solves `c' = X_n(c)`, solved
  coordinatewise);
* finite compositions (`equivariant_finite`); arbitrary angle arrays by truncation and continuity of `S`
  (`tendsto_rotE_trunc`, `equivariant`);
* the ratio `S(z)_n / z_n` depends only on the actions (`transition_ratio`, cross-multiplied);
* along the physical rotation `S` acquires the same factor (`frequency_strong`), and equality of the
  characters `exp(-i t a)` for all real `t` fixes the active frequency (`freq_eq_of_char_eq`).

No Fourier normalization or real identity is used.  `H` is any complex inner product space (the
physical space `L²(𝕋_L)` is an instance); the real structure on `H` is `NormedSpace.complexToReal`.
-/

open scoped ComplexConjugate ENNReal
open InnerProductSpace

namespace QuantumNLS.ChartFrequencies

open QuantumNLS.RephasingFlow

noncomputable section

/-- the Hamiltonian vector field `-i ∇ |z_n|² = -i z_n e_n` of the action `|z_n|²` -/
def Xn (n : ℤ) (w : E) : E := lp.single (E := fun _ : ℤ => ℂ) 2 n (-Complex.I * w n)

lemma Xn_apply_self (n : ℤ) (w : E) : Xn n w n = -Complex.I * w n := by
  simp [Xn, lp.single_apply]

lemma Xn_apply_ne (n m : ℤ) (w : E) (h : m ≠ n) : Xn n w m = 0 := by
  simp [Xn, lp.single_apply, h]

lemma inner_single_left (n : ℤ) (a : ℂ) (h : E) :
    inner ℂ (lp.single (E := fun _ : ℤ => ℂ) 2 n a) h = conj a * h n := by
  rw [lp.inner_eq_tsum, tsum_eq_single n]
  · simp [lp.single_apply, mul_comm]
  · intro m hm
    simp [lp.single_apply, hm]

lemma omega_Xn (n : ℤ) (v h : E) :
    SymplecticBracket.omega (Xn n v) h = 2 * (conj (v n) * h n).re := by
  unfold SymplecticBracket.omega Xn
  rw [inner_single_left]
  have : conj (-Complex.I * v n) * h n = Complex.I * (conj (v n) * h n) := by
    simp [map_mul]; ring
  rw [this]
  simp

lemma omega_sub_left (a b h : E) :
    SymplecticBracket.omega (a - b) h = SymplecticBracket.omega a h - SymplecticBracket.omega b h := by
  unfold SymplecticBracket.omega
  rw [inner_sub_left]; simp; ring

lemma omega_zero_of_forall {d : E}
    (hd : ∀ k : E, SymplecticBracket.omega d k = 0) : d = 0 := by
  have := SymplecticBracket.omega_mul_I d
  rw [hd] at this
  have h2 : ‖d‖ ^ 2 = 0 := by linarith
  have : ‖d‖ = 0 := by simpa using h2
  exact norm_eq_zero.mp this

/-- coordinate action derivative -/
lemma hasFDerivAt_action (n : ℤ) (v : E) :
    HasFDerivAt (fun z : E => ‖z n‖ ^ 2) ((2 : ℕ) • (innerSL ℝ (v n)).comp (pr n)) v := by
  have := ((hasStrictFDerivAt_norm_sq (v n)).hasFDerivAt).comp v (pr n).hasFDerivAt
  exact this

/-- the transition map of two charts: a differentiable map with surjective, `Ω`-preserving derivative -/
structure CanonicalMap (S : E → E) : Prop where
  differentiable : ∀ w, DifferentiableAt ℝ S w
  surj : ∀ w k, ∃ h, fderiv ℝ S w h = k
  symplectic : ∀ w h k, SymplecticBracket.omega (fderiv ℝ S w h) (fderiv ℝ S w k) =
    SymplecticBracket.omega h k

lemma action_deriv {S : E → E} {w : E} (hS : DifferentiableAt ℝ S w)
    (hact : ∀ z n, ‖S z n‖ = ‖z n‖) (n : ℤ) (h : E) :
    (conj (S w n) * (fderiv ℝ S w h) n).re = (conj (w n) * h n).re := by
  have h1 := (hasFDerivAt_action n (S w)).comp w hS.hasFDerivAt
  have h3 : (fun z => ‖S z n‖ ^ 2) = fun z => ‖z n‖ ^ 2 := by
    funext z; rw [hact]
  have h1' : HasFDerivAt (fun z : E => ‖z n‖ ^ 2)
      (((2 : ℕ) • (innerSL ℝ (S w n)).comp (pr n)).comp (fderiv ℝ S w)) w := by
    rw [← h3]; exact h1
  have h4 := h1'.unique (hasFDerivAt_action n w)
  have h5 := congrArg (fun L => L h) h4
  simp only [ContinuousLinearMap.comp_apply, smul_apply, pr_apply, innerSL_apply_apply] at h5
  simp only [Complex.inner] at h5
  simp [Complex.mul_re] at h5 ⊢
  linarith

/-- canonical maps intertwine the Hamiltonian vector field of each coordinate action -/
lemma Xn_intertwine {S : E → E} (hS : CanonicalMap S) (hact : ∀ z n, ‖S z n‖ = ‖z n‖)
    (n : ℤ) (w : E) : fderiv ℝ S w (Xn n w) = Xn n (S w) := by
  have hd : ∀ k : E, SymplecticBracket.omega (fderiv ℝ S w (Xn n w) - Xn n (S w)) k = 0 := by
    intro k
    obtain ⟨h, rfl⟩ := hS.surj w k
    rw [omega_sub_left, hS.symplectic, omega_Xn, omega_Xn, action_deriv (hS.differentiable w) hact]
    ring
  exact sub_eq_zero.mp (omega_zero_of_forall hd)

/-! ### Rotation of one coordinate is the Hamiltonian flow of its action -/

lemma rotE_single_self (n : ℤ) (θ : ℝ) (z : E) :
    rotE (Pi.single n θ) z n = Complex.exp ((θ : ℂ) * Complex.I) * z n := by
  rw [rotE_apply]; simp

lemma rotE_single_ne (n m : ℤ) (θ : ℝ) (z : E) (h : m ≠ n) :
    rotE (Pi.single n θ) z m = z m := by
  rw [rotE_apply]; simp [h]

/-- `a ↦ a e_n` as a continuous real-linear map -/
def ι (n : ℤ) : ℂ →L[ℝ] E :=
  LinearMap.mkContinuous (lp.lsingle (E := fun _ : ℤ => ℂ) (𝕜 := ℝ) 2 n) 1 (by
    intro a
    show ‖lp.single (E := fun _ : ℤ => ℂ) 2 n a‖ ≤ 1 * ‖a‖
    rw [lp.norm_single (by norm_num), one_mul])

lemma ι_apply (n : ℤ) (a : ℂ) : ι n a = lp.single (E := fun _ : ℤ => ℂ) 2 n a := rfl

/-- the rotation curve of the coordinate `n` (the flow of `X_n`: `z_n ↦ e^{-it} z_n`) -/
def rho (n : ℤ) (z : E) (t : ℝ) : E := rotE (Pi.single n (-t)) z

lemma rho_eq (n : ℤ) (z : E) (t : ℝ) :
    rho n z t = z + ι n ((Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1) * z n) := by
  apply lp.ext; funext m
  by_cases h : m = n
  · subst h
    simp only [rho, rotE_single_self, ι_apply]
    simp [lp.single_apply]; ring
  · simp only [rho, rotE_single_ne _ _ _ _ h, ι_apply]
    simp [lp.single_apply, h]

lemma rho_zero (n : ℤ) (z : E) : rho n z 0 = z := by
  rw [rho_eq]; simp

lemma rho_hasDerivAt (n : ℤ) (z : E) (t : ℝ) :
    HasDerivAt (rho n z) (Xn n (rho n z t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1) * z n)
      ((-Complex.I * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) * z n) t := by
    have h0 : HasDerivAt (fun t : ℝ => ((-t : ℝ) : ℂ) * Complex.I) (-Complex.I) t := by
      have := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_neg t)).mul_const Complex.I
      simpa using this
    have h2 := ((h0.cexp).sub_const 1).mul_const (z n)
    simpa [mul_comm] using h2
  have h3 := (ι n).hasFDerivAt.comp_hasDerivAt t h1
  have h4 := h3.const_add z
  have h5 : HasDerivAt (rho n z) ((ι n) (-Complex.I * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) * z n)) t := by
    have heq : rho n z = fun t => z + ι n ((Complex.exp (((-t : ℝ) : ℂ) * Complex.I) - 1) * z n) := by
      funext t; exact rho_eq n z t
    rw [heq]; exact h4
  convert h5 using 1
  rw [ι_apply, Xn]
  have : rho n z t n = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) * z n := rotE_single_self _ _ _
  rw [this]
  congr 1; ring

/-- a canonical action-preserving map intertwines the rotation of one coordinate -/
theorem equivariant_single {S : E → E} (hS : CanonicalMap S) (hact : ∀ z n, ‖S z n‖ = ‖z n‖)
    (n : ℤ) (θ : ℝ) (z : E) :
    S (rotE (Pi.single n θ) z) = rotE (Pi.single n θ) (S z) := by
  -- the curve `c(t) = S(ρ_t z)` solves `c' = X_n(c)`
  set c : ℝ → E := fun t => S (rho n z t) with hc
  have hcd : ∀ t, HasDerivAt c (Xn n (c t)) t := by
    intro t
    have h1 := (hS.differentiable (rho n z t)).hasFDerivAt.comp_hasDerivAt t (rho_hasDerivAt n z t)
    rw [Xn_intertwine hS hact] at h1
    exact h1
  have hcoord : ∀ m, ∀ t, HasDerivAt (fun t => c t m) (Xn n (c t) m) t := fun m t =>
    (pr m).hasFDerivAt.comp_hasDerivAt t (hcd t)
  have hc0 : c 0 = S z := by simp [hc, rho_zero]
  -- coordinates `m ≠ n` are constant
  have hne : ∀ m, m ≠ n → ∀ t, c t m = S z m := by
    intro m hm t
    have hder : ∀ x, deriv (fun t => c t m) x = 0 := fun x => by
      rw [(hcoord m x).deriv, Xn_apply_ne _ _ _ hm]
    have := is_const_of_deriv_eq_zero (fun x => (hcoord m x).differentiableAt) hder t 0
    rw [this, hc0]
  -- coordinate `n` rotates
  have hn : ∀ t, c t n = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) * S z n := by
    intro t
    have hg : ∀ x, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * c t n) 0 x := by
      intro x
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I x := by
        have := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)).mul_const Complex.I
        simpa using this
      have h1 := h0.cexp.mul (hcoord n x)
      rw [Xn_apply_self] at h1
      convert h1 using 1
      ring
    have hder : ∀ x, deriv (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) * c t n) x = 0 :=
      fun x => (hg x).deriv
    have := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt) hder t 0
    rw [hc0] at this
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at this
    have h2 : c t n = Complex.exp (-((t : ℂ) * Complex.I)) * (Complex.exp ((t : ℂ) * Complex.I) * c t n) := by
      rw [← mul_assoc, ← Complex.exp_add]; simp
    rw [h2, this]; simp
  have key : S (rho n z (-θ)) = rotE (Pi.single n θ) (S z) := by
    apply lp.ext; funext m
    by_cases h : m = n
    · subst h
      have := hn (-θ)
      simp only [hc] at this
      rw [this, rotE_single_self]; simp
    · have := hne m h (-θ)
      simp only [hc] at this
      rw [this, rotE_single_ne _ _ _ _ h]
  simpa [rho] using key

/-! ### Finite and infinite angle arrays -/

lemma rotE_add (θ θ' : ℤ → ℝ) (z : E) : rotE (θ + θ') z = rotE θ (rotE θ' z) := by
  apply lp.ext; funext m
  simp only [rotE_apply, Pi.add_apply, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

lemma rotE_zero (z : E) : rotE 0 z = z := by
  apply lp.ext; funext m
  simp [rotE_apply]

theorem equivariant_finite {S : E → E} (hS : CanonicalMap S) (hact : ∀ z n, ‖S z n‖ = ‖z n‖)
    (s : Finset ℤ) : ∀ θ : ℤ → ℝ, (∀ m, m ∉ s → θ m = 0) → ∀ z : E,
      S (rotE θ z) = rotE θ (S z) := by
  induction s using Finset.induction_on with
  | empty =>
    intro θ hθ z
    have : θ = 0 := funext fun m => hθ m (by simp)
    subst this
    simp [rotE_zero]
  | insert a s ha ih =>
    intro θ hθ z
    have hdec : θ = Pi.single a (θ a) + Function.update θ a 0 := by
      funext m
      by_cases h : m = a
      · subst h; simp
      · simp [h]
    have hsupp : ∀ m, m ∉ s → Function.update θ a 0 m = 0 := by
      intro m hm
      by_cases h : m = a
      · subst h; simp
      · simp only [Function.update_of_ne h]
        exact hθ m (by simp [h, hm])
    rw [hdec, rotE_add, rotE_add, equivariant_single hS hact, ih _ hsupp]

/-- the truncation of an angle array to `[-K, K]` -/
def trunc (θ : ℤ → ℝ) (K : ℕ) : ℤ → ℝ := fun m => if m ∈ Finset.Icc (-(K : ℤ)) K then θ m else 0

lemma trunc_zero_outside (θ : ℤ → ℝ) (K : ℕ) (m : ℤ) (h : m ∉ Finset.Icc (-(K : ℤ)) K) :
    trunc θ K m = 0 := by simp [trunc, h]

lemma rotE_trunc_sub (θ : ℤ → ℝ) (z : E) (K : ℕ) :
    rotE (trunc θ K) z - z = ∑ m ∈ Finset.Icc (-(K : ℤ)) K,
      lp.single (E := fun _ : ℤ => ℂ) 2 m ((rotE θ z - z) m) := by
  apply lp.ext; funext m
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.coeFn_single, lp.coeFn_sub, Pi.sub_apply,
    rotE_apply, trunc]
  by_cases h : m ∈ Finset.Icc (-(K : ℤ)) K <;> simp [h]

theorem tendsto_rotE_trunc (θ : ℤ → ℝ) (z : E) :
    Filter.Tendsto (fun K : ℕ => rotE (trunc θ K) z) Filter.atTop (nhds (rotE θ z)) := by
  have hs := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) (rotE θ z - z)
  have hmono : Monotone (fun K : ℕ => Finset.Icc (-(K : ℤ)) (K : ℤ)) := by
    intro a b hab m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  have hcof : Filter.Tendsto (fun K : ℕ => Finset.Icc (-(K : ℤ)) (K : ℤ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_finset_of_monotone hmono (fun x => ⟨x.natAbs, by
      simp only [Finset.mem_Icc]; omega⟩)
  have h1 : Filter.Tendsto (fun s : Finset ℤ => ∑ m ∈ s,
      lp.single (E := fun _ : ℤ => ℂ) 2 m ((rotE θ z - z) m)) Filter.atTop (nhds (rotE θ z - z)) := by
    simpa [HasSum] using hs
  have h2 := (h1.comp hcof).const_add z
  have h3 : (fun K : ℕ => rotE (trunc θ K) z) = fun K : ℕ => z + (∑ m ∈ Finset.Icc (-(K : ℤ)) K,
      lp.single (E := fun _ : ℤ => ℂ) 2 m ((rotE θ z - z) m)) := by
    funext K
    rw [← rotE_trunc_sub]; abel
  rw [h3]
  simpa using h2

theorem equivariant {S : E → E} (hS : CanonicalMap S) (hact : ∀ z n, ‖S z n‖ = ‖z n‖)
    (θ : ℤ → ℝ) (z : E) : S (rotE θ z) = rotE θ (S z) := by
  have hcont : Continuous S := continuous_iff_continuousAt.mpr fun w => (hS.differentiable w).continuousAt
  have h1 := (hcont.tendsto (rotE θ z)).comp (tendsto_rotE_trunc θ z)
  have h2 := tendsto_rotE_trunc θ (S z)
  have h3 : (S ∘ fun K : ℕ => rotE (trunc θ K) z) = fun K : ℕ => rotE (trunc θ K) (S z) := by
    funext K
    exact equivariant_finite hS hact (Finset.Icc (-(K : ℤ)) K) (trunc θ K)
      (fun m hm => trunc_zero_outside θ K m hm) z
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-! ### The transition map preserves the phase ratios -/

lemma exists_rotE_of_norm_eq {z z' : E} (hm : ∀ n, ‖z n‖ = ‖z' n‖) : ∃ θ : ℤ → ℝ, z' = rotE θ z := by
  refine ⟨fun n => Complex.arg (z' n) - Complex.arg (z n), ?_⟩
  apply lp.ext; funext n
  rw [rotE_apply]
  have e1 : z n = (‖z n‖ : ℂ) * Complex.exp ((Complex.arg (z n) : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I _).symm
  have e2 : z' n = (‖z n‖ : ℂ) * Complex.exp ((Complex.arg (z' n) : ℂ) * Complex.I) := by
    rw [hm n]; exact (Complex.norm_mul_exp_arg_mul_I _).symm
  have key : Complex.exp (((Complex.arg (z' n) - Complex.arg (z n) : ℝ) : ℂ) * Complex.I) *
      ((‖z n‖ : ℂ) * Complex.exp ((Complex.arg (z n) : ℂ) * Complex.I)) =
      (‖z n‖ : ℂ) * Complex.exp ((Complex.arg (z' n) : ℂ) * Complex.I) := by
    push_cast
    rw [sub_mul, Complex.exp_sub]
    have : Complex.exp ((Complex.arg (z n) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  calc z' n = (‖z n‖ : ℂ) * Complex.exp ((Complex.arg (z' n) : ℂ) * Complex.I) := e2
    _ = _ := key.symm
    _ = _ := by rw [← e1]

/-- the printed ratio step: `S(z')_n z_n = S(z)_n z'_n` whenever `|z_m| = |z'_m|` for all `m`
(that is, `S(z)_n/z_n` depends only on the actions) -/
theorem transition_ratio {S : E → E} (hS : CanonicalMap S) (hact : ∀ z n, ‖S z n‖ = ‖z n‖)
    {z z' : E} (hm : ∀ m, ‖z m‖ = ‖z' m‖) (n : ℤ) :
    S z' n * z n = S z n * z' n := by
  obtain ⟨θ, rfl⟩ := exists_rotE_of_norm_eq hm
  rw [equivariant hS hact, rotE_apply, rotE_apply]
  ring

/-! ### Charts from a physical Hilbert space -/

section Charts

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- DEF-016 for a chart `Φ : H → ℓ²(ℤ)` from a complex Hilbert space (the physical space): a
differentiable bijection with differentiable inverse, bounded real-linear isomorphism as derivative at
every point, and `Ω(DΦ h, DΦ k) = Ω(h, k)` with `Ω = 2 Im⟨·,·⟩` (DEF-015).  For `H = ℓ²(ℤ)` this
contains `RephasingFlow.IsStrongSymplecticDiffeo` (`IsStrongSymplecticDiffeo.toStrongCanonical`). -/
structure IsStrongCanonical (Φ : H → E) : Prop where
  exists_inverse : ∃ Ψ : E → H, (∀ z, Ψ (Φ z) = z) ∧ (∀ w, Φ (Ψ w) = w) ∧
    (∀ w, DifferentiableAt ℝ Ψ w)
  differentiable : ∀ z, DifferentiableAt ℝ Φ z
  deriv_iso : ∀ z, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ z
  symplectic : ∀ z h k, SymplecticBracket.omega (fderiv ℝ Φ z h) (fderiv ℝ Φ z k) =
    SymplecticBracket.omega h k

/-- a global `C¹` strong canonical diffeomorphism: `Φ` and its inverse are `C¹` and `Φ` is strongly
canonical. -/
structure IsC1StrongCanonical (Φ : H → E) : Prop where
  contDiff : ContDiff ℝ 1 Φ
  exists_inverse : ∃ Ψ : E → H, (∀ z, Ψ (Φ z) = z) ∧ (∀ w, Φ (Ψ w) = w) ∧ ContDiff ℝ 1 Ψ
  deriv_iso : ∀ z, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ z
  symplectic : ∀ z h k, SymplecticBracket.omega (fderiv ℝ Φ z h) (fderiv ℝ Φ z k) =
    SymplecticBracket.omega h k

theorem IsC1StrongCanonical.toStrong {Φ : H → E} (h : IsC1StrongCanonical Φ) :
    IsStrongCanonical Φ where
  exists_inverse := by
    obtain ⟨Ψ, h1, h2, h3⟩ := h.exists_inverse
    exact ⟨Ψ, h1, h2, fun w => (h3.differentiable (by norm_num)) w⟩
  differentiable := fun z => (h.contDiff.differentiable (by norm_num)) z
  deriv_iso := h.deriv_iso
  symplectic := h.symplectic

theorem _root_.QuantumNLS.RephasingFlow.IsStrongSymplecticDiffeo.toStrongCanonical {Φ : E → E}
    (h : IsStrongSymplecticDiffeo Φ) : IsStrongCanonical Φ :=
  ⟨h.exists_inverse, h.differentiable, h.deriv_iso, h.symplectic⟩

/-- the transition `Φ₂ Φ₁⁻¹` of two strong canonical charts is a canonical map of `ℓ²(ℤ)` -/
theorem transition_canonical {Φ₁ Φ₂ : H → E} (h₁ : IsStrongCanonical Φ₁) (h₂ : IsStrongCanonical Φ₂)
    (Ψ : E → H) (hl : ∀ z, Ψ (Φ₁ z) = z) (hr : ∀ w, Φ₁ (Ψ w) = w)
    (hd : ∀ w, DifferentiableAt ℝ Ψ w) : CanonicalMap (Φ₂ ∘ Ψ) := by
  -- `DΦ₁(Ψ w) ∘ DΨ(w) = id`
  have hid : ∀ w k, fderiv ℝ Φ₁ (Ψ w) (fderiv ℝ Ψ w k) = k := by
    intro w k
    have h1 := fderiv_comp w (h₁.differentiable (Ψ w)) (hd w)
    have h2 : Φ₁ ∘ Ψ = id := funext hr
    rw [h2] at h1
    have h3 := congrArg (fun L => L k) h1
    simpa using h3.symm
  -- `DΨ(w)` is surjective
  have hsurj : ∀ w k, ∃ h, fderiv ℝ Ψ w h = k := by
    intro w k
    refine ⟨fderiv ℝ Φ₁ (Ψ w) k, ?_⟩
    have h1 := fderiv_comp (Ψ w) (hd (Φ₁ (Ψ w))) (h₁.differentiable (Ψ w))
    have h2 : Ψ ∘ Φ₁ = id := funext hl
    rw [h2] at h1
    have h3 := congrArg (fun L => L k) h1
    simp only [fderiv_id, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h3
    rw [hr w] at h3
    exact h3.symm
  have hfd : ∀ w, fderiv ℝ (Φ₂ ∘ Ψ) w = (fderiv ℝ Φ₂ (Ψ w)).comp (fderiv ℝ Ψ w) :=
    fun w => fderiv_comp w (h₂.differentiable (Ψ w)) (hd w)
  refine ⟨fun w => (h₂.differentiable (Ψ w)).comp w (hd w), ?_, ?_⟩
  · intro w k
    obtain ⟨e, he⟩ := h₂.deriv_iso (Ψ w)
    obtain ⟨h', hh'⟩ := e.surjective k
    obtain ⟨h, hh⟩ := hsurj w h'
    refine ⟨h, ?_⟩
    rw [hfd]
    simp only [ContinuousLinearMap.comp_apply, hh]
    rw [← he]; exact hh'
  · intro w h k
    rw [hfd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [h₂.symplectic, ← h₁.symplectic (Ψ w), hid, hid]

/-- the coordinate actions `|z_n|²` as an array -/
def act (z : E) : ℤ → ℝ := fun n => ‖z n‖ ^ 2

/-- A flow `Ψ_t` on the physical space is a coordinate rotation with frequencies `ω_n` depending only
on the actions in the chart `Φ`: `(Φ(Ψ_t u))_n = exp(-i t ω_n(|Φ u|²)) (Φ u)_n`. -/
def IsRotationFlow (Φ : H → E) (Ψ : ℝ → H → H) (ω : ℤ → (ℤ → ℝ) → ℝ) : Prop :=
  ∀ (t : ℝ) (u : H) (n : ℤ), Φ (Ψ t u) n =
    Complex.exp (-Complex.I * ((t * ω n (act (Φ u)) : ℝ) : ℂ)) * Φ u n

lemma norm_eq_of_sq_eq {a b : ℂ} (h : ‖a‖ ^ 2 = ‖b‖ ^ 2) : ‖a‖ = ‖b‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma norm_exp_neg_I_mul (x : ℝ) : ‖Complex.exp (-Complex.I * (x : ℂ))‖ = 1 := by
  have : -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- on a point with `z ≠ 0`, equality of the characters `exp(-i t a) = exp(-i t b)` for all real `t`
forces `a = b` (no ambiguity modulo `2π`) -/
lemma freq_eq_of_char_eq {a b : ℝ} {w : ℂ} (hw : w ≠ 0)
    (h : ∀ t : ℝ, Complex.exp (-Complex.I * ((t * a : ℝ) : ℂ)) * w =
      Complex.exp (-Complex.I * ((t * b : ℝ) : ℂ)) * w) : a = b := by
  have h1 : ∀ t : ℝ, Complex.exp (-Complex.I * ((t * a : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((t * b : ℝ) : ℂ)) := fun t => mul_right_cancel₀ hw (h t)
  have hder : ∀ c : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-Complex.I * ((t * c : ℝ) : ℂ)))
      (-Complex.I * (c : ℂ)) 0 := by
    intro c
    have h0 : HasDerivAt (fun t : ℝ => -Complex.I * ((t * c : ℝ) : ℂ)) (-Complex.I * (c : ℂ)) 0 := by
      have h5 : HasDerivAt (fun t : ℝ => t * c) c 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
      have := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h5).const_mul (-Complex.I)
      simpa using this
    simpa using h0.cexp
  have h2 := (hder a).unique (by
    have := hder b
    have hf : (fun t : ℝ => Complex.exp (-Complex.I * ((t * b : ℝ) : ℂ))) =
        fun t : ℝ => Complex.exp (-Complex.I * ((t * a : ℝ) : ℂ)) := funext fun t => (h1 t).symm
    rw [hf] at this
    exact this)
  have h3 : (a : ℂ) = (b : ℂ) := by
    have hI : -Complex.I ≠ 0 := by simp
    exact mul_left_cancel₀ hI h2
  exact_mod_cast h3

/-- Core form (for strong canonical charts, no `C¹` assumption used): equal indexed actions give the
same coordinate rotation with the same frequencies. -/
theorem frequency_strong {Φ₁ Φ₂ : H → E} (h₁ : IsStrongCanonical Φ₁) (h₂ : IsStrongCanonical Φ₂)
    (hact : ∀ u n, ‖Φ₁ u n‖ ^ 2 = ‖Φ₂ u n‖ ^ 2) (Ψ : ℝ → H → H) (ω : ℤ → (ℤ → ℝ) → ℝ)
    (hflow : IsRotationFlow Φ₁ Ψ ω) :
    IsRotationFlow Φ₂ Ψ ω ∧
      ∀ ω' : ℤ → (ℤ → ℝ) → ℝ, IsRotationFlow Φ₂ Ψ ω' →
        ∀ (u : H) (n : ℤ), Φ₂ u n ≠ 0 → ω' n (act (Φ₂ u)) = ω n (act (Φ₂ u)) := by
  obtain ⟨Ψ₁, hl, hr, hd⟩ := h₁.exists_inverse
  have hS := transition_canonical h₁ h₂ Ψ₁ hl hr hd
  have hnorm : ∀ u n, ‖Φ₁ u n‖ = ‖Φ₂ u n‖ := fun u n => norm_eq_of_sq_eq (hact u n)
  have hSact : ∀ z n, ‖(Φ₂ ∘ Ψ₁) z n‖ = ‖z n‖ := by
    intro z n
    simp only [Function.comp]
    rw [← hnorm, hr]
  have hSΦ : ∀ v, (Φ₂ ∘ Ψ₁) (Φ₁ v) = Φ₂ v := by intro v; simp [hl]
  have hactEq : ∀ u, act (Φ₂ u) = act (Φ₁ u) := fun u => funext fun n => (hact u n).symm
  have hmain : IsRotationFlow Φ₂ Ψ ω := by
    intro t u n
    rw [hactEq]
    have hm : ∀ m, ‖Φ₁ u m‖ = ‖Φ₁ (Ψ t u) m‖ := by
      intro m
      rw [hflow t u m, norm_mul, norm_exp_neg_I_mul, one_mul]
    have hrat := transition_ratio hS hSact hm n
    rw [hSΦ, hSΦ] at hrat
    by_cases hz : Φ₁ u n = 0
    · have h2z : Φ₂ u n = 0 := by
        have := hnorm u n
        rw [hz, norm_zero] at this
        exact norm_eq_zero.mp this.symm
      have h1t : Φ₁ (Ψ t u) n = 0 := by rw [hflow t u n, hz, mul_zero]
      have h2t : Φ₂ (Ψ t u) n = 0 := by
        have := hnorm (Ψ t u) n
        rw [h1t, norm_zero] at this
        exact norm_eq_zero.mp this.symm
      rw [h2t, h2z, mul_zero]
    · rw [hflow t u n] at hrat
      apply mul_right_cancel₀ hz
      rw [hrat]; ring
  refine ⟨hmain, ?_⟩
  intro ω' hω' u n hn
  apply freq_eq_of_char_eq hn
  intro t
  rw [← hω' t u n, hmain t u n]

/-- **R-E28AD0D3 `lem:frequency`.** Let `Φ₁, Φ₂ : H → ℓ²(ℤ)` be global `C¹` strong canonical
diffeomorphisms (DEF-016 with `Ω = 2 Im⟨·,·⟩`) with `|Φ₁(u)_n|² = |Φ₂(u)_n|²` for all `u, n`.  If a
physical flow `Ψ_t` is a coordinate rotation `(Φ₁ Ψ_t u)_n = exp(-i t ω_n(|Φ₁ u|²)) (Φ₁ u)_n` with
frequencies depending only on the actions in the chart `Φ₁`, then it is the same coordinate rotation
with the same frequencies in the chart `Φ₂`; moreover any frequency array `ω'` that describes the
flow as a coordinate rotation in the chart `Φ₂` agrees with `ω` at every active coordinate
(`(Φ₂ u)_n ≠ 0`), as a real number (no ambiguity modulo `2π`). -/
theorem lem_frequency {Φ₁ Φ₂ : H → E} (h₁ : IsC1StrongCanonical Φ₁) (h₂ : IsC1StrongCanonical Φ₂)
    (hact : ∀ u n, ‖Φ₁ u n‖ ^ 2 = ‖Φ₂ u n‖ ^ 2) (Ψ : ℝ → H → H) (ω : ℤ → (ℤ → ℝ) → ℝ)
    (hflow : IsRotationFlow Φ₁ Ψ ω) :
    IsRotationFlow Φ₂ Ψ ω ∧
      ∀ ω' : ℤ → (ℤ → ℝ) → ℝ, IsRotationFlow Φ₂ Ψ ω' →
        ∀ (u : H) (n : ℤ), Φ₂ u n ≠ 0 → ω' n (act (Φ₂ u)) = ω n (act (Φ₂ u)) :=
  frequency_strong h₁.toStrong h₂.toStrong hact Ψ ω hflow

/-- the same for charts `ℓ²(ℤ) → ℓ²(ℤ)` in the sense of `RephasingFlow.IsStrongSymplecticDiffeo` -/
theorem frequency_ell2 {Φ₁ Φ₂ : E → E} (h₁ : IsStrongSymplecticDiffeo Φ₁)
    (h₂ : IsStrongSymplecticDiffeo Φ₂)
    (hact : ∀ u n, ‖Φ₁ u n‖ ^ 2 = ‖Φ₂ u n‖ ^ 2) (Ψ : ℝ → E → E) (ω : ℤ → (ℤ → ℝ) → ℝ)
    (hflow : IsRotationFlow Φ₁ Ψ ω) :
    IsRotationFlow Φ₂ Ψ ω :=
  (frequency_strong h₁.toStrongCanonical h₂.toStrongCanonical hact Ψ ω hflow).1

/-! ### Non-vacuity: the hypotheses are met by the rephasing flow of `RephasingFlow` -/

theorem U_isC1StrongCanonical (c κ t : ℝ) : IsC1StrongCanonical (U c κ t) where
  contDiff := contDiff_iff_contDiffAt.mpr fun z => (U_analyticAt c κ t z).contDiffAt
  exists_inverse := ⟨U c κ (-t), U_neg_left c κ t, U_neg_right c κ t,
    contDiff_iff_contDiffAt.mpr fun z => (U_analyticAt c κ (-t) z).contDiffAt⟩
  deriv_iso := (U_strongSymplectic c κ t).deriv_iso
  symplectic := (U_strongSymplectic c κ t).symplectic

theorem id_isC1StrongCanonical : IsC1StrongCanonical (id : E → E) := by
  have h : U 0 0 0 = (id : E → E) := funext (U_zero 0 0)
  rw [← h]
  exact U_isC1StrongCanonical 0 0 0

/-- the rephasing flow is a coordinate rotation in the identity chart with frequencies
`ω_n(a) = 2cκ(Σ a - a_n)` depending only on the actions -/
theorem U_isRotationFlow (c κ : ℝ) :
    IsRotationFlow (id : E → E) (fun t => U c κ t)
      (fun n a => 2 * c * κ * ((∑' m, a m) - a n)) := by
  intro t z n
  have h1 : ∑' m, act z m = ‖z‖ ^ 2 := (tsum_sq z).symm
  show U c κ t z n = Complex.exp (-Complex.I * ((t * (2 * c * κ * ((∑' m, act z m) - act z n)) : ℝ) : ℂ)) * z n
  rw [h1, U_apply]
  congr 2
  simp only [act]
  push_cast
  ring

/-- instance of `lem_frequency`: `Φ₁ = id`, `Φ₂ = U_s`, the flow `Ψ_t = U_t` -/
example (c κ s : ℝ) : IsRotationFlow (U c κ s) (fun t => U c κ t)
      (fun n a => 2 * c * κ * ((∑' m, a m) - a n)) :=
  (lem_frequency id_isC1StrongCanonical (U_isC1StrongCanonical c κ s)
    (fun u n => by rw [norm_U_apply]; rfl) _ _ (U_isRotationFlow c κ)).1

end Charts

end

end QuantumNLS.ChartFrequencies
