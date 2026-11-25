import QuantumNLS.Local014ShortTime

/-!
# LOCAL-014 `reset:analytic-egorov` (Proved): the single theorem

Source: `source-text/chapters/local/quantum_periods.tex:186-267` (statement 186-203, proof
204-267), with the conventions of lines 173-182.

The theorem `local014_analytic_egorov` assembles the frozen stages E1 (`Local014Dyson`),
E3 (`Local014Heisenberg`), E2 (`Local014IteratedSymbol`), E5 (`Local014ClassicalSeries`),
E4a (`Local014RealSymbol`), E4b (`Local014OneBody`), E4c (`Local014StateLimits`) and
E6 (`Local014ShortTime`), and carries out the restarts of the proof's last paragraph
("Test it with the rank-one projector onto `phi^t v`; norm conservation gives trace one and the
preceding trace-distance estimate proves one-body condensation at that new vector ... It can
therefore be restarted at the end of each short interval. A finite number of restarts covers
every prescribed finite time ... The same argument applies backwards in time.").

Formal reading of the hypotheses (see the theorem docstring):
* `H_N` self-adjoint with kernel expansions `Hk N` (DEF-050 `IsExpansion`) converging on
  radius `8` (DEF-042 `ConvergesOnRadius 8`, which includes the uniform radius-`8` bound);
* "its real symbol `h`": `symbol Hlim`; the theorem PROVES `Im h = 0` on the unit sphere;
* "the Hamiltonian flow `phi^t` of `h` exists on the unit sphere for all times under
  consideration": `F : H → ℝ` is any real function, differentiable at the points of the unit
  sphere and equal to `h` there (`(F u : ℂ) = h u`), and `phi : ℝ → H` is a solution curve on the
  unit sphere of its Hamiltonian field (DEF-015 `hamField F`), for all real times, with
  `phi 0 = v`. The theorem also proves that `F = Re h = hReal Hlim` is such a function. By E6's
  `pbC_eq_of_sphere`, the Hamiltonian fields of two such functions differ on the sphere only by
  a vector tangent to the gauge orbit, so the conclusions do not depend on the extension of `h`
  off the unit sphere;
* normal states `ρ_N` (E4b `IsNormalState`) whose one-body matrices (E4b `oneBody`, the GP-09
  partial trace normalized as on line 176) converge to `|v⟩⟨v|` in trace norm.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal Nat ComplexOrder
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal QuantumNLS.KernelDefinition
  QuantumNLS.KernelConvergence QuantumNLS.SymplecticBracket QuantumNLS.Local014Dyson
  QuantumNLS.Local014Heisenberg QuantumNLS.Local014IteratedSymbol
  QuantumNLS.Local014ClassicalSeries QuantumNLS.Local014RealSymbol QuantumNLS.Local014OneBody
  QuantumNLS.Local014StateLimits QuantumNLS.Local014ShortTime

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Local014Main

/-! ## 1. Exponentials in a Banach algebra -/

section Banach

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

theorem opExp_smul_mul (a b : ℂ) (A : 𝔸) : opExp (a • A) * opExp (b • A) = opExp ((a + b) • A) := by
  unfold opExp
  rw [add_smul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (((Commute.refl A).smul_left a).smul_right b)
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ 𝔸).symm ▸ edist_lt_top _ _)]

theorem opExp_zero : opExp (0 : 𝔸) = 1 := NormedSpace.exp_zero

theorem star_opExp [StarRing 𝔸] [CStarRing 𝔸] (x : 𝔸) : star (opExp x) = opExp (star x) :=
  NormedSpace.star_exp x

end Banach

section Concrete

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {N : ℕ}

theorem opExp_smul_mulL (a b : ℂ) (A : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    opExp (a • A) * opExp (b • A) = opExp ((a + b) • A) :=
  opExp_smul_mul a b A

theorem opExp_zeroL : opExp (0 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) = 1 := opExp_zero

theorem star_opExpL (x : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    star (opExp x) = opExp (star x) :=
  star_opExp x

theorem zero_smulL (A : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : (0 : ℂ) • A = 0 := by
  ext x; simp

theorem neg_smulL (c : ℂ) (A : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : (-c) • A = -(c • A) := by
  ext x; simp

end Concrete

/-! ## 2. Evolved states -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "REP" => QuantumNLS.RadiusBound.represented
local notation "RB" => QuantumNLS.RadiusBound.radiusBound

/-- `c_N(t) = i t N`. -/
def cN (N : ℕ) (t : ℝ) : ℂ := Complex.I * (t : ℂ) * (N : ℂ)

/-- The evolved state `e^{−itNA} ρ e^{itNA}`. -/
def evolve (N : ℕ) (A ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t : ℝ) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  opExp ((-cN N t) • A) * ρ * opExp (cN N t • A)

theorem heis_eq (N : ℕ) (A X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t : ℝ) :
    heis N A X t = opExp (cN N t • A) * X * opExp ((-cN N t) • A) := by
  rw [heis, cN, neg_smulL]

theorem heis_zero (N : ℕ) (A X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : heis N A X 0 = X := by
  rw [heis_eq]
  have h0 : cN N 0 = 0 := by simp [cN]
  rw [h0, neg_zero, zero_smulL, opExp_zeroL, one_mul, mul_one]

theorem star_opExp_cN {N : ℕ} {A : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (hA : IsSelfAdjoint A)
    (a : ℂ) (ha : star a = -a) : star (opExp (a • A)) = opExp ((-a) • A) := by
  rw [star_opExpL, star_smul, hA.star_eq, ha]

theorem star_cN (N : ℕ) (t : ℝ) : star (cN N t) = -cN N t := by
  simp [cN, Complex.conj_I]

theorem star_neg_cN (N : ℕ) (t : ℝ) : star (-cN N t) = -(-cN N t) := by
  rw [star_neg, star_cN]

theorem evolve_isNormalState {N : ℕ} {A ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}
    (hA : IsSelfAdjoint A) (hρ : IsNormalState ρ) (t : ℝ) : IsNormalState (evolve N A ρ t) := by
  set V := opExp ((-cN N t) • A) with hV
  have hVs : star V = opExp (cN N t • A) := by
    rw [hV, star_opExp_cN hA _ (star_neg_cN N t), neg_neg]
  have hev : evolve N A ρ t = V * ρ * star V := by rw [evolve, hVs]
  have hVV : star V * V = 1 := by
    rw [hVs, hV, opExp_smul_mulL, add_neg_cancel, zero_smulL, opExp_zeroL]
  have htc1 : IsTraceClass (V * ρ) := isTraceClass_mul_left V hρ.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hev, ContinuousLinearMap.star_eq_adjoint]
    exact hρ.1.conj_adjoint V
  · rw [hev]
    exact finite_right _ _ htc1
  · rw [hev, ← tr_comm _ htc1, ← mul_assoc, hVV, one_mul, hρ.2.2]

/-- `Tr(ρ(t₀) e^{isNA}Xe^{−isNA}) = Tr(ρ e^{i(t₀+s)NA}Xe^{−i(t₀+s)NA})`. -/
theorem tr_evolve_heis {N : ℕ} {A ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}
    (hρ : IsTraceClass ρ) (X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (t₀ s : ℝ) :
    tr (evolve N A ρ t₀ * heis N A X s) = tr (ρ * heis N A X (t₀ + s)) := by
  have hc : cN N (t₀ + s) = cN N t₀ + cN N s := by simp [cN]; ring
  have hc' : -cN N (t₀ + s) = -cN N s + -cN N t₀ := by rw [hc]; ring
  set Z := opExp (cN N t₀ • A) * heis N A X s with hZ
  have htc : IsTraceClass (ρ * Z) := finite_right _ _ hρ
  have h1 : evolve N A ρ t₀ * heis N A X s = opExp ((-cN N t₀) • A) * (ρ * Z) := by
    rw [evolve, hZ]; simp only [mul_assoc]
  rw [h1, tr_comm _ htc, mul_assoc]
  congr 2
  rw [hZ, heis_eq, heis_eq, hc', ← opExp_smul_mulL (-cN N s) (-cN N t₀), hc,
    ← opExp_smul_mulL (cN N t₀) (cN N s)]
  simp only [mul_assoc]

/-! ## 3. The one-body projector -/

theorem toSym1_rankOne (w : H) : toSym1 (InnerProductSpace.rankOne ℂ w w) = P w 1 := by
  unfold toSym1 P proj
  congr 1
  have hadj : (fromOne (H := H)).toContinuousLinearMap.adjoint w =
      (htpow 1 w : HilbertTensorPower ℂ H 1) := by
    apply ext_inner_left ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [← (IntrinsicContact.oneEquiv (E := H)).inner_map_map, fromOne,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply,
      IntrinsicContact.oneEquiv_apply]
  ext x
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul, hadj]
  rw [← ContinuousLinearMap.adjoint_inner_left, hadj]

theorem kps_P_self {w : H} (hw : ‖w‖ = 1) : kernelProductSymbol (P w 1) w = 1 := by
  rw [← toSym1_rankOne, kernelProductSymbol_toSym1, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hw]
  simp

/-! ## 4. Restarts -/

/-- Clamp of `t` to `[−τ, τ]`, and the bounds used by the restart. -/
theorem restart_split {τ t : ℝ} (hτ : 0 < τ) (n : ℕ) (ht : |t| ≤ (n + 1 : ℕ) * τ) :
    ∃ t₀ s : ℝ, t = t₀ + s ∧ |s| ≤ τ ∧ |t₀| ≤ n * τ := by
  by_cases h1 : |t| ≤ τ
  · refine ⟨0, t, by ring, h1, by rw [abs_zero]; positivity⟩
  · push_cast at ht
    rcases le_or_gt 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht h1
      refine ⟨t - τ, τ, by ring, by rw [abs_of_pos hτ], ?_⟩
      rw [abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_of_neg h0] at ht h1
      refine ⟨t + τ, -τ, by ring, by rw [abs_neg, abs_of_pos hτ], ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- **LOCAL-014 `reset:analytic-egorov`** (`quantum_periods.tex:186-203`).

Hypotheses: `H_N = HN N` is self-adjoint and has the kernel expansion `Hk N` (DEF-050), the
expansions converge on radius `8` (DEF-042: uniformly bounded radius-`8` norm and kernelwise
operator-norm convergence) with limiting kernels `Hlim`, so `h = symbol Hlim`; `F` is a real
function differentiable on the unit sphere and equal there to `h`; `phi` is a solution curve on the
unit sphere, for all real times, of the Hamiltonian field `X_F` with `phi 0 = v`, `‖v‖ = 1`;
`ρ_N` are normal states on `Sym^N H` whose one-body matrices converge in trace norm to `|v⟩⟨v|`.

Conclusions: (i) `h` is real on the unit sphere, and `F = Re h` is admissible; (ii)
(reset:egorov-limit) for every real `t`, every `q` and bounded `B` on `Sym^q H`,
`Tr(ρ_N e^{itNH_N} Q_{N,q}(B) e^{−itNH_N}) → ⟨(phi t)^{⊗q}, B (phi t)^{⊗q}⟩` (the expression is
taken to be `0` for the finitely many `N < q`); (iii) the one-body matrices of the evolved states
`e^{−itNH_N} ρ_N e^{itNH_N}` converge in trace norm to `|phi t⟩⟨phi t|`. -/
theorem local014_analytic_egorov {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (HN : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hsa : ∀ N, IsSelfAdjoint (HN N))
    (hexp : ∀ N, RadiusBound.IsExpansion (HN N) (Hk N)) (hH : ConvergesOnRadius 8 Hk Hlim)
    (F : H → ℝ) (hFd : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ F u)
    (hF : ∀ u : H, ‖u‖ = 1 → (F u : ℂ) = symbol Hlim u)
    {v : H} (hv : ‖v‖ = 1) {phi : ℝ → H} (hphi0 : phi 0 = v)
    (hphi : ∀ s, HasDerivAt phi (hamField F (phi s)) s) (hn : ∀ s, ‖phi s‖ = 1)
    (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (hρ : ∀ N, IsNormalState (ρ N))
    (hcond : Tendsto (fun N => traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v))
      atTop (𝓝 0)) :
    ((∀ u : H, ‖u‖ = 1 → (symbol Hlim u).im = 0) ∧
      (∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u ∧
        ((hReal Hlim u : ℝ) : ℂ) = symbol Hlim u)) ∧
    (∀ (t : ℝ) (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => if h : q ≤ N then
          tr (ρ N * (opExp ((Complex.I * (t : ℂ) * (N : ℂ)) • HN N) * RadiusBound.Q N q h B *
            opExp (-((Complex.I * (t : ℂ) * (N : ℂ)) • HN N)))) else 0) atTop
        (𝓝 (kernelProductSymbol B (phi t)))) ∧
    (∀ t : ℝ, Tendsto (fun N => traceNorm (oneBody N (evolve N (HN N) (ρ N) t) -
        InnerProductSpace.rankOne ℂ (phi t) (phi t))) atTop (𝓝 0)) := by
  have hrepN : ∀ N, REP (Hk N) = HN N := fun N => (hexp N).symm
  have hsaR : ∀ N, IsSelfAdjoint (REP (Hk N)) := fun N => by rw [hrepN]; exact hsa N
  -- realness and admissibility of `Re h`
  have hreal : ∀ u : H, ‖u‖ = 1 → (symbol Hlim u).im = 0 :=
    fun u hu => symbol_im_eq_zero (by norm_num) hH hsaR u hu
  have hhR : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u := by
    intro u hu
    exact Complex.reCLM.differentiableAt.comp u
      (differentiableAt_symbol (summable_of_converges (by norm_num) hH) (by rw [hu]; norm_num))
  have hadm : ∀ u : H, ‖u‖ = 1 → DifferentiableAt ℝ (hReal Hlim) u ∧
      ((hReal Hlim u : ℝ) : ℂ) = symbol Hlim u := by
    intro u hu
    refine ⟨hhR u hu, Complex.ext (by simp [hReal]) (by simp [hReal, hreal u hu])⟩
  -- the constant `K` and the short time `τ`
  obtain ⟨C, hC⟩ := (saList_converges (R := 8) (by norm_num) hH).1
  set K := max C 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ N, RB 8 (saList Hk N) ≤ K := fun N => (hC N).trans (le_max_left _ _)
  set τ := 1 / (Real.exp 1 * K + 1) with hτdef
  have hEK : 0 ≤ Real.exp 1 * K := mul_nonneg (Real.exp_pos 1).le hK0
  have hτ0 : 0 < τ := by positivity
  have hτ : ∀ s : ℝ, |s| ≤ τ → Real.exp 1 * K * |s| < 1 := by
    intro s hs
    calc Real.exp 1 * K * |s| ≤ Real.exp 1 * K * τ := mul_le_mul_of_nonneg_left hs hEK
      _ < 1 := by
        rw [hτdef, mul_one_div, div_lt_one (by linarith)]
        linarith
  -- one-body condensation as an expectation
  have hqexp_one : ∀ {N : ℕ} (hN : 1 ≤ N) (σ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
      (hσ : IsNormalState σ) (w : H),
      ⟪w, oneBody N σ w⟫_ℂ = qexp σ 1 (P w 1) := by
    intro N hN σ hσ w
    rw [inner_oneBody_eq hN hσ.1 hσ.2.1, toSym1_rankOne, qexp, dif_pos hN]
  have h1 : Tendsto (fun N => qexp (ρ N) 1 (P (phi 0) 1)) atTop (𝓝 1) := by
    rw [hphi0]
    have hreal' : Tendsto (fun N => (traceNorm (oneBody N (ρ N) -
        InnerProductSpace.rankOne ℂ v v)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcond
      rw [ENNReal.toReal_zero] at this
      exact this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hreal'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hγ := oneBody_isNormalState hN (hρ N)
    rw [← hqexp_one hN (ρ N) (hρ N) v]
    have hvv : ⟪v, InnerProductSpace.rankOne ℂ v v v⟫_ℂ = 1 := by
      rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
      simp
    have hdiff : ⟪v, oneBody N (ρ N) v⟫_ℂ - 1 =
        ⟪v, (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) v⟫_ℂ := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, hvv]
    rw [hdiff]
    have hD : IsTraceClass (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) :=
      finite_sub hγ.2.1 (lt_of_le_of_lt (Fidelity.traceNorm_rankOne_le _ _) ENNReal.ofReal_lt_top)
    calc ‖⟪v, (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v) v⟫_ℂ‖
        ≤ ‖oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v‖ := by
          refine (norm_inner_le_norm _ _).trans ?_
          rw [hv, one_mul]
          refine ((oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v).le_opNorm v).trans ?_
          rw [hv, mul_one]
      _ ≤ (traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v)).toReal := by
          have := norm_le_traceNorm (oneBody N (ρ N) - InnerProductSpace.rankOne ℂ v v)
          rw [← ENNReal.ofReal_toReal hD.ne] at this
          exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp this
  -- the restart induction
  have hmain : ∀ n : ℕ, ∀ t : ℝ, |t| ≤ n * τ → ∀ (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t)) atTop
        (𝓝 (kernelProductSymbol B (phi t))) := by
    intro n
    induction n with
    | zero =>
      intro t ht q B
      have ht0 : t = 0 := by simpa using ht
      subst ht0
      exact short_time hH hsaR hK0 hK F hFd hF hphi hn ρ hρ h1 (by simp) q B
    | succ n ih =>
      intro t ht q B
      obtain ⟨t₀, s, rfl, hs, ht₀⟩ := restart_split hτ0 n ht
      set ρ' : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
        fun N => evolve N (REP (Hk N)) (ρ N) t₀ with hρ'def
      have hρ' : ∀ N, IsNormalState (ρ' N) := fun N => evolve_isNormalState (hsaR N) (hρ N) t₀
      have hshift : ∀ (N : ℕ) (X : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (s' : ℝ),
          tr (ρ' N * heis N (REP (Hk N)) X s') = tr (ρ N * heis N (REP (Hk N)) X (t₀ + s')) :=
        fun N X s' => tr_evolve_heis (hρ N).2.1 X t₀ s'
      set ψ : ℝ → H := fun s' => phi (t₀ + s') with hψ
      have hψd : ∀ s', HasDerivAt ψ (hamField F (ψ s')) s' :=
        fun s' => (hphi (t₀ + s')).comp_const_add t₀ s'
      have hψn : ∀ s', ‖ψ s'‖ = 1 := fun s' => hn _
      have h1' : Tendsto (fun N => qexp (ρ' N) 1 (P (ψ 0) 1)) atTop (𝓝 1) := by
        have hψ0 : ψ 0 = phi t₀ := by simp [hψ]
        rw [hψ0]
        have hIH := ih t₀ ht₀ 1 (P (phi t₀) 1)
        rw [kps_P_self (hn t₀)] at hIH
        refine hIH.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hT := tr_evolve_heis (A := REP (Hk N)) (hρ N).2.1
          (REP (testList 1 (P (phi t₀) 1) N)) t₀ 0
        rw [heis_zero, add_zero] at hT
        rw [qexp, dif_pos hN, ← represented_testList hN]
        exact hT.symm
      have hst := short_time hH hsaR hK0 hK F hFd hF hψd hψn ρ' hρ' h1' (hτ s hs) q B
      have hψs : ψ s = phi (t₀ + s) := rfl
      rw [hψs] at hst
      exact hst.congr fun N => hshift N _ s
  have hall : ∀ (t : ℝ) (q : ℕ) (B : BoundedSymmetricKernel H q),
      Tendsto (fun N => tr (ρ N * heis N (REP (Hk N)) (REP (testList q B N)) t)) atTop
        (𝓝 (kernelProductSymbol B (phi t))) := by
    intro t q B
    obtain ⟨n, hn'⟩ := exists_nat_ge (|t| / τ)
    exact hmain n t (by rwa [div_le_iff₀ hτ0] at hn') q B
  refine ⟨⟨hreal, hadm⟩, ?_, ?_⟩
  · intro t q B
    refine (hall t q B).congr' ?_
    filter_upwards [eventually_ge_atTop q] with N hqN
    rw [dif_pos hqN, represented_testList hqN, heis, hrepN]
  · intro t
    have hlimP := hall t 1 (P (phi t) 1)
    rw [kps_P_self (hn t)] at hlimP
    have hre : Tendsto (fun N => 1 - (tr (ρ N * heis N (REP (Hk N))
        (REP (testList 1 (P (phi t) 1) N)) t)).re) atTop (𝓝 0) := by
      have := ((Complex.continuous_re.tendsto (1 : ℂ)).comp hlimP).const_sub 1
      simpa using this
    have hup : Tendsto (fun N => ENNReal.ofReal (2 * √(1 - (tr (ρ N * heis N (REP (Hk N))
        (REP (testList 1 (P (phi t) 1) N)) t)).re))) atTop (𝓝 0) := by
      have hc : Continuous fun x : ℝ => 2 * √x := by fun_prop
      have := ENNReal.tendsto_ofReal ((hc.tendsto 0).comp hre)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hσ := evolve_isNormalState (hsa N) (hρ N) t
    have hγ := oneBody_isNormalState hN hσ
    have hkey : ⟪phi t, oneBody N (evolve N (HN N) (ρ N) t) (phi t)⟫_ℂ =
        tr (ρ N * heis N (REP (Hk N)) (REP (testList 1 (P (phi t) 1) N)) t) := by
      have hT := tr_evolve_heis (A := REP (Hk N)) (hρ N).2.1
        (REP (testList 1 (P (phi t) 1) N)) t 0
      rw [heis_zero, add_zero] at hT
      rw [hqexp_one hN _ hσ, qexp, dif_pos hN, ← represented_testList hN, ← hrepN, hT]
    refine (traceNorm_sub_rankOne_le hγ (phi t) (hn t)).trans (le_of_eq ?_)
    rw [RCLike.re_to_complex, hkey]

end QuantumNLS.Local014Main

#print axioms QuantumNLS.Local014Main.opExp_smul_mul
#print axioms QuantumNLS.Local014Main.star_opExp
#print axioms QuantumNLS.Local014Main.evolve_isNormalState
#print axioms QuantumNLS.Local014Main.tr_evolve_heis
#print axioms QuantumNLS.Local014Main.toSym1_rankOne
#print axioms QuantumNLS.Local014Main.kps_P_self
#print axioms QuantumNLS.Local014Main.restart_split
#print axioms QuantumNLS.Local014Main.local014_analytic_egorov
