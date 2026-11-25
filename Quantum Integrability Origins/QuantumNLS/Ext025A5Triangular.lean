import QuantumNLS.Ext025AAnalysis

/-! GP-03 triangular implicit construction. Analytic input means an actual
convergent multilinear series. The arbitrary Banach-domain implication from
holomorphy remains a separate obligation; it is not asserted here. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace QuantumNLS.Ext025A5
variable {𝕜 P E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of (p,x) ↦ (p,f(p,x)) is inverted explicitly. -/
def triangularEquiv (A : P →L[𝕜] F) (B : E ≃L[𝕜] F) :
    (P × E) ≃L[𝕜] (P × F) where
  toFun v := (v.1, A v.1 + B v.2)
  invFun v := (v.1, B.symm (v.2 - A v.1))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by ext <;> simp; abel
  map_smul' c v := by ext <;> simp [map_smul, smul_add]
  continuous_toFun := continuous_fst.prodMk
    ((A.continuous.comp continuous_fst).add (B.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (B.symm.continuous.comp (continuous_snd.sub (A.continuous.comp continuous_fst)))

/-- The analytic implicit solution is obtained from the inverse of the
triangular product map; the local equivalence includes uniqueness. -/
theorem analytic_implicit {f : P × E → F} {u : P × E}
    (A : P →L[𝕜] F) (B : E ≃L[𝕜] F)
    (hf : AnalyticAt 𝕜 f u)
    (hd : HasFDerivAt f (A.coprod B.toContinuousLinearMap) u) :
    ∃ ψ : P → E, AnalyticAt 𝕜 ψ u.1 ∧ ψ u.1 = u.2 ∧
      HasFDerivAt ψ (-(B.symm.toContinuousLinearMap.comp A)) u.1 ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2) ∧
      (∀ᶠ p in 𝓝 u.1, f (p, ψ p) = f u) := by
  let T : P × E → P × F := fun v => (v.1, f v)
  let I := triangularEquiv A B
  have ht : AnalyticAt 𝕜 T u := analyticAt_fst.prod hf
  have htd : HasFDerivAt T I.toContinuousLinearMap u := by
    exact hasFDerivAt_fst.prodMk hd
  obtain ⟨g, hg, hgu, hl, hr⟩ :=
    QuantumNLS.Ext025A.gp03_analytic_inverse I ht htd
  change AnalyticAt 𝕜 g (u.1, f u) at hg
  let ψ : P → E := fun p => (g (p, f u)).2
  have hc : ContinuousAt (fun p : P => (p, f u)) u.1 :=
    continuousAt_id.prodMk continuousAt_const
  have hψ : AnalyticAt 𝕜 ψ u.1 := by
    exact analyticAt_snd.comp
      (hg.comp (f := fun p : P => (p, f u)) (analyticAt_id.prod analyticAt_const))
  have hbase : ψ u.1 = u.2 := congrArg Prod.snd hgu
  have hex : ∀ᶠ p in 𝓝 u.1, f (p, ψ p) = f u := by
    filter_upwards [hc.tendsto.eventually hr] with p hp
    have hfst : (g (p, f u)).1 = p := congrArg Prod.fst hp
    have hsnd : f (g (p, f u)) = f u := congrArg Prod.snd hp
    have hpair : (p, ψ p) = g (p, f u) := Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  have huniq : ∀ᶠ v in 𝓝 u, f v = f u ↔ ψ v.1 = v.2 := by
    filter_upwards [hl, (continuousAt_fst : ContinuousAt Prod.fst u).tendsto.eventually hex]
      with v hv he
    constructor
    · intro h
      have h' : g (v.1, f u) = v := by simpa [T, h] using hv
      exact congrArg Prod.snd h'
    · intro h
      simpa [h] using he
  refine ⟨ψ, hψ, hbase, ?_, huniq, hex⟩
  have hginv : HasFDerivAt g I.symm.toContinuousLinearMap (T u) := by
    obtain ⟨q, hq⟩ := ht
    have hs : HasStrictFDerivAt T I.toContinuousLinearMap u := by
      have he := hq.hasFDerivAt.unique htd
      exact he ▸ hq.hasStrictFDerivAt
    exact (hs.to_local_left_inverse hl).hasFDerivAt
  change HasFDerivAt g I.symm.toContinuousLinearMap (u.1, f u) at hginv
  have hcomp := hginv.comp (f := fun p : P => (p, f u)) u.1 ((hasFDerivAt_id u.1).prodMk
    (hasFDerivAt_const (f u) u.1))
  have hsnd := hasFDerivAt_snd.comp u.1 hcomp
  change HasFDerivAt (Prod.snd ∘ g ∘ fun p : P => (p, f u)) _ u.1
  convert hsnd using 1
  ext p
  change -(B.symm (A p)) = B.symm (0 - A p)
  simp
end QuantumNLS.Ext025A5

#print axioms QuantumNLS.Ext025A5.triangularEquiv
#print axioms QuantumNLS.Ext025A5.analytic_implicit
