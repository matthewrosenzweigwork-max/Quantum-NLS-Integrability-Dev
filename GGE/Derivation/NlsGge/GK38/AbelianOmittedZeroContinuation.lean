import NlsGge.GK38.AbelianOmittedLocalComplexImplicit
import Mathlib.Topology.Connected.Clopen

/-! Faithful open-and-closed continuation of ACTUAL omitted-period zeros.
The parameter space can be a real trace or a complex overlap. Only actual
local implicit graph uniqueness is used; padded nth seed coordinates are
never compared. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

theorem p6Omitted_zero_branches_eq_of_continuation38 (n : ℤ)
    (χ : X → PotPair) (hχ : Continuous χ) (hW : ∀ x, χ x ∈ gkW)
    (f g : X → P2Space38 n) (hf : Continuous f) (hg : Continuous g)
    (hfzero : ∀ x, p2Fn38 n (χ x,f x)=0)
    (hgzero : ∀ x, p2Fn38 n (χ x,g x)=0)
    (hinv : ∀ x, (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (χ x,t)) (f x)).IsInvertible)
    (x₀ : X) (hbase : f x₀=g x₀) : f=g := by
  have hlocal (x : X) (heq : f x=g x) : f =ᶠ[𝓝 x] g := by
    obtain ⟨ψ,_hψbase,_hψan,_hψzero,hgraph⟩ :=
      p6OmittedFn_local_complex_analytic_zero_of_inverse38 n (χ x) (hW x) (f x)
        (hfzero x) (hinv x)
    have hft : Tendsto (fun q => (χ q,f q)) (𝓝 x) (𝓝 (χ x,f x)) :=
      (hχ.continuousAt.prodMk hf.continuousAt)
    have hgt : Tendsto (fun q => (χ q,g q)) (𝓝 x) (𝓝 (χ x,f x)) := by
      simpa only [heq] using (hχ.continuousAt.prodMk hg.continuousAt).tendsto
    filter_upwards [hft.eventually hgraph,hgt.eventually hgraph] with q hqf hqg
    exact (hqf.mp (hfzero q)).symm.trans (hqg.mp (hgzero q))
  have hopen : IsOpen {x : X | f x=g x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact hlocal x hx
  have hclosed : IsClosed {x : X | f x=g x} := isClosed_eq hf hg
  have hall : {x : X | f x=g x}=univ :=
    (show IsClopen {x : X | f x=g x} from ⟨hclosed,hopen⟩).eq_univ ⟨x₀,hbase⟩
  funext x
  have hx : x ∈ {x : X | f x=g x} := by rw [hall]; exact mem_univ x
  exact hx

end
end NlsGge.GK38
