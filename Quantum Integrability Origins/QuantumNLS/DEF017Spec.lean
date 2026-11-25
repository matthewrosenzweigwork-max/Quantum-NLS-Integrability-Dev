import QuantumNLS.RealAnalyticComplexify

/-! integrator-authored trusted spec for DEF-017 (definitions.tex:103-105). For maps between real
Hilbert spaces: "real analytic near x" means a series of continuous real homogeneous polynomials
converging in norm to f near x (written out here); this is equivalent to Mathlib's real analyticity,
and equivalent to having a local holomorphic extension after complexification, where the
complexification is the genuine one: a complex Hilbert space Cpx E with an isometric real embedding ι,
Re ∘ ι = id, unique decomposition v = ι a + i ι b, and ⟨ι a, ι b⟩ = ⟨a, b⟩. Holomorphic is read as
complex analyticity (AnalyticAt ℂ; Terra's C2 interface qualification). The finite-loss sentences are a
reading convention (Terra R57). -/

open Filter Topology Finset
open QuantumNLS.RealAnalyticComplexify QuantumNLS.RealAnalyticComplexify.Cpx

namespace QuantumNLS.DEF017Spec

def LocRealAnalytic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E) : Prop :=
  ∃ P : ℕ → E → F,
    (∀ n, Continuous (P n) ∧ ∃ M : MultilinearMap ℝ (fun _ : Fin n => E) F, ∀ h, P n h = M (fun _ => h)) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ y, ‖y - x‖ < r →
      Tendsto (fun N => ∑ n ∈ range N, P n (y - x)) atTop (𝓝 (f y))

def Spec : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
    -- genuine complexification
    (Isometry (ofRealCLM : E → Cpx E) ∧ (∀ a : E, reCLM (ofRealCLM a : Cpx E) = a) ∧
      (∀ v : Cpx E, ∃! p : E × E, v = ofRealCLM p.1 + Complex.I • ofRealCLM p.2) ∧
      ∀ a b : E, inner ℂ (ofRealCLM a : Cpx E) (ofRealCLM b) = ((inner ℝ a b : ℝ) : ℂ)) ∧
    -- the polynomial-series definition, its equivalence with real analyticity and with
    -- local holomorphic extension through the genuine complexification
    ∀ (f : E → F) (x : E),
      (LocRealAnalytic f x ↔ AnalyticAt ℝ f x) ∧
      (LocRealAnalytic f x ↔ ∃ g : Cpx E → Cpx F, AnalyticAt ℂ g (ofRealCLM x) ∧
        ∀ᶠ y in 𝓝 x, g (ofRealCLM y) = ofRealCLM (f y))

theorem spec : Spec := by
  intro E F _ _ _ _ _ _
  refine ⟨isGenuineComplexification, fun f x =>
    ⟨(QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly f x).symm,
     isRealAnalyticPoly_iff_exists_holomorphic f x⟩⟩

end QuantumNLS.DEF017Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF017Spec.spec
  IO.println s!"DEF017Spec.spec axioms: {ax}"
