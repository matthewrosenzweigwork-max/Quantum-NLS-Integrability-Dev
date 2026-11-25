import Mathlib
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.G5033Host

                                                                                                               
                                                                                                                   
                                                                                                                     
                                                                                                      
                                                                                                                       
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open scoped ENNReal BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev CartesianComplex := lp (fun _ : Bool × ℤ => ℂ) 2

def cartesianSequence (φ : PotPair) (j : Bool × ℤ) : ℂ :=
  if j.1 then cartesianX j.2 φ else cartesianY j.2 φ

def birkhoffCartesian (φ : PotPair) : CartesianComplex :=
  if h : Memℓp (cartesianSequence φ) 2 then
    ⟨cartesianSequence φ, h⟩
  else 0

end
end NlsGge.GKDefinitionDesign
