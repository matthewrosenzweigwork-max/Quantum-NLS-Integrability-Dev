import QuantumNLS.InverseRootPropertiesR13
import QuantumNLS.ContinuousExhaustionR13
import QuantumNLS.ContinuousTraceLimitR13
import QuantumNLS.EnergyForm

/-! R-6EA807B1 for arbitrary self-adjoint A >= 1. The energy trace is the
trace norm of the unique positive form realization, using the existing
infimum definition. Existence is derived from finiteness, not supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.ArbitraryEnergyTraceR13
open BoundedInverseR13 InverseSquareRootR13 CFCCutoffsR13
open TraceClass EnergyForm EnergyTracePassage EnergyTraceLimit
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

/-- Finite positive form energy; no operator-domain condition on ran ρ. -/
def FiniteEnergy := {ρ : E →L[ℂ] E // ρ.IsPositive ∧ energyTraceNorm (rootInv A hA h) ρ ≠ ⊤}

theorem realization_exists (ρ : FiniteEnergy A hA h) :
    ∃ B : E →L[ℂ] E, ρ.val = rootInv A hA h*B*rootInv A hA h := by
  by_contra hx
  push Not at hx
  exact ρ.property.2 (energyTraceNorm_eq_top hx)

def sandwich (ρ : FiniteEnergy A hA h) : E →L[ℂ] E :=
  (realization_exists A hA h ρ).choose

theorem sandwich_spec (ρ : FiniteEnergy A hA h) :
    ρ.val = rootInv A hA h*sandwich A hA h ρ*rootInv A hA h :=
  (realization_exists A hA h ρ).choose_spec

theorem sandwich_positive (ρ : FiniteEnergy A hA h) : (sandwich A hA h ρ).IsPositive :=
  isPositive_of_realization (rootInv_selfAdjoint A hA h) (rootInv_dense A hA h)
    ρ.property.1 (sandwich_spec A hA h ρ)

theorem sandwich_norm (ρ : FiniteEnergy A hA h) :
    energyTraceNorm (rootInv A hA h) ρ.val = traceNorm (sandwich A hA h ρ) :=
  energyTraceNorm_eq (rootInv_injective A hA h) (rootInv_dense A hA h) (sandwich_spec A hA h ρ)

theorem sandwich_finite (ρ : FiniteEnergy A hA h) : IsTraceClass (sandwich A hA h ρ) := by
  rw [IsTraceClass,← sandwich_norm]
  exact lt_top_iff_ne_top.mpr ρ.property.2

theorem sandwich_trace (ρ : FiniteEnergy A hA h) :
    posTrace (sandwich A hA h ρ) = energyTraceNorm (rootInv A hA h) ρ.val := by
  rw [sandwich_norm,traceNorm_of_isPositive (sandwich_positive A hA h ρ)]

theorem root_half (x : (half A hA h).domain) : rootInv A hA h (half A hA h x) = (x : E) := by
  have hx : (x : E) ∈ (rootInv A hA h).range := by
    simpa only [half_domain] using x.property
  obtain ⟨y,hy⟩ := hx
  have he : x = ⟨rootInv A hA h y,by rw [half_domain]; exact ⟨y,rfl⟩⟩ :=
    Subtype.ext hy.symm
  rw [he,half_root]

/-- Continuous exhaustion maps all vectors into the square-root domain. -/
theorem cutoff_mem (m : ℕ) (x : E) :
    cutoff (inverse A hA h) m x ∈ (half A hA h).domain := by
  rw [half_domain]
  refine ⟨rootCutoff (inverse A hA h) m x,?_⟩
  change (rootInv A hA h*rootCutoff (inverse A hA h) m) x = _
  exact congrArg (fun X : E →L[ℂ] E => X x)
    (root_factor' _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)) m)

/-- The root after cutoff is literally the bounded CFC root cutoff. -/
theorem half_cutoff (m : ℕ) (x : E) :
    half A hA h ⟨cutoff (inverse A hA h) m x,cutoff_mem A hA h m x⟩ =
      rootCutoff (inverse A hA h) m x := by
  apply LinearPMap.inverse_apply_eq (root_ker A hA h)
    (x := ⟨rootCutoff (inverse A hA h) m x,Submodule.mem_top⟩)
  change (rootInv A hA h*rootCutoff (inverse A hA h) m) x = _
  exact congrArg (fun X : E →L[ℂ] E => X x)
    (root_factor' _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)) m)

theorem pure_spec (x : (half A hA h).domain) :
    InnerProductSpace.rankOne ℂ (x : E) (x : E) = rootInv A hA h *
      InnerProductSpace.rankOne ℂ (half A hA h x) (half A hA h x)*rootInv A hA h := by
  have he := rankOne_conjugate (rootInv A hA h) (half A hA h x)
  rw [(rootInv_selfAdjoint A hA h).adjoint_eq,root_half] at he
  exact he.symm

theorem difference_norm (ρ : FiniteEnergy A hA h) (x : (half A hA h).domain) :
    energyTraceNorm (rootInv A hA h) (ρ.val-InnerProductSpace.rankOne ℂ (x : E) (x : E)) =
      traceNorm (sandwich A hA h ρ-
        InnerProductSpace.rankOne ℂ (half A hA h x) (half A hA h x)) := by
  apply energyTraceNorm_eq (rootInv_injective A hA h) (rootInv_dense A hA h)
  rw [mul_sub,sub_mul,← sandwich_spec,← pure_spec]

theorem compressed (ρ : FiniteEnergy A hA h) (x : (half A hA h).domain) (m : ℕ) :
    cutoff (inverse A hA h) m * (sandwich A hA h ρ-
      InnerProductSpace.rankOne ℂ (half A hA h x) (half A hA h x))*cutoff (inverse A hA h) m =
      rootCutoff (inverse A hA h) m *
      (ρ.val-InnerProductSpace.rankOne ℂ (x : E) (x : E))*rootCutoff (inverse A hA h) m := by
  have hR : 0 ≤ inverse A hA h := ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)
  have he : ρ.val-InnerProductSpace.rankOne ℂ (x : E) (x : E) = rootInv A hA h *
      (sandwich A hA h ρ-InnerProductSpace.rankOne ℂ (half A hA h x) (half A hA h x))*rootInv A hA h := by
    rw [mul_sub,sub_mul,← sandwich_spec,← pure_spec]
  rw [he]
  have hs : rootCutoff (inverse A hA h) m*rootInv A hA h = cutoff (inverse A hA h) m :=
    root_factor _ hR m
  have hs' : rootInv A hA h*rootCutoff (inverse A hA h) m = cutoff (inverse A hA h) m :=
    root_factor' _ hR m
  simp only [← mul_assoc,hs]
  rw [mul_assoc _ _ (rootCutoff (inverse A hA h) m),hs']

/-- One arbitrary-A theorem: both source uniform hypotheses imply convergence
of the supremum of the literal form-realization energy trace norm. -/
theorem R_6EA807B1 {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : T → (half A hA h).domain)
    (hf : Continuous (fun t => ((f t : E),half A hA h (f t))))
    (_hunit : ∀ t, ‖(f t : E)‖ = 1)
    (ρ : ℕ → T → FiniteEnergy A hA h)
    (_htrace : ∀ n t, posTrace (ρ n t).val = 1)
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : E) (f t : E)) ≤ ENNReal.ofReal ε)
    (henergy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |(energyTraceNorm (rootInv A hA h) (ρ n t).val).toReal-‖half A hA h (f t)‖^2| ≤ ε) :
    Tendsto (fun n => ⨆ t,
      energyTraceNorm (rootInv A hA h)
        ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : E) (f t : E))) atTop (𝓝 0) := by
  let R := inverse A hA h
  have hR : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)
  have hd : DenseRange R := by
    change Dense (R.range : Set E)
    rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range (inverse_positive A hA h).isSelfAdjoint.isStarNormal]
    exact LinearMap.ker_eq_bot.mpr (inverse_injective A hA h)
  have hg : IsCompact (Set.range (fun t => half A hA h (f t))) := isCompact_range hf.snd
  have hB (n : ℕ) (t : T) : (sandwich A hA h (ρ n t)).IsPositive ∧
      IsTraceClass (sandwich A hA h (ρ n t)) :=
    ⟨sandwich_positive A hA h _,sandwich_finite A hA h _⟩
  have ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |total (sandwich A hA h (ρ n t))-‖half A hA h (f t)‖^2| ≤ ε := by
    simpa only [total,sandwich_trace] using henergy
  have hc (m : ℕ) : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (cutoff R m*(sandwich A hA h (ρ n t)-
        InnerProductSpace.rankOne ℂ (half A hA h (f t)) (half A hA h (f t)))*cutoff R m) ≤
          ENNReal.ofReal ε := by
    intro ε hε
    let c := ‖rootCutoff R m‖^2
    have hc0 : 0 ≤ c := sq_nonneg _
    have heps : 0 < ε/(c+1) := div_pos hε (by positivity)
    filter_upwards [hconv _ heps] with n hn
    intro t
    rw [compressed]
    calc
      _ ≤ ENNReal.ofReal ‖rootCutoff R m‖ *
          traceNorm ((ρ n t).val-InnerProductSpace.rankOne ℂ (f t : E) (f t : E))*
          ENNReal.ofReal ‖rootCutoff R m‖ := TraceIdeal.traceNorm_mul_mul_le _ _ _
      _ ≤ ENNReal.ofReal ‖rootCutoff R m‖ * ENNReal.ofReal (ε/(c+1)) *
          ENNReal.ofReal ‖rootCutoff R m‖ := by gcongr; exact hn t
      _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _),← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have he := (div_mul_cancel₀ ε (show c+1 ≠ 0 by positivity))
        dsimp [c] at *
        nlinarith [div_nonneg hε.le (show 0 ≤ ‖rootCutoff R m‖^2+1 by positivity)]
  obtain ⟨ι,b,_⟩ := exists_hilbertBasis ℂ E
  have hu := ContinuousTraceLimitR13.uniform_gentle_limit b (cutoff R)
    (cutoff_nonneg R) (cutoff_norm R) (fun n t => sandwich A hA h (ρ n t))
    (fun t => half A hA h (f t)) hB hg
    (ContinuousExhaustionR13.uniform_compact R hR hd _ hg) ht hc
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r,_,hr0,hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  filter_upwards [hu r hr] with n hn
  apply iSup_le
  intro t
  rw [difference_norm]
  exact (hn t).trans hrε.le
end QuantumNLS.ArbitraryEnergyTraceR13
