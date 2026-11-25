module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

namespace SatakeHermitian

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_locRepD {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LGrp.IsUnitarisable (GlobalTheory.DiscLocEx.locRepD hV.stable w) := by
  let : MeasurableSpace (GA E N) := borel _
  have : BorelSpace (GA E N) := ⟨rfl⟩
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  have := GlobalTheory.DiscreteUnit.countable_latticeGL (E := E) (N := N)
  have : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  refine GlobalTheory.DiscreteUnit.isUnitarisable_of_embedding (Γ := latticeGL E N) (GlobalTheory.DiscLocEx.locRepD hV.stable w)
    (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp V.subtype) (Subtype.val_injective.comp Subtype.val_injective)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N v.1 (hV.aut _ v.2).level)
    (fun v => GlobalTheory.DiscreteUnit.left_latticeGL (hV.aut _ v.2) (hV.sqInt _ v.2)) (fun v => (hV.sqInt _ v.2).2)
    fun g v x => rfl
  exact GlobalTheory.DiscreteUnit.modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (GlobalTheory.DiscreteUnit.cornerGL_transInv (sLoc E w) g)).trans
      (GlobalTheory.DiscreteUnit.cornerGL_transInv (sFin E) _)) g

theorem herm_of_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : B.map (fun b => (star b)⁻¹) = B := by
  have e := congrArg (Multiset.map (fun b : ℂˣ => b⁻¹)) h
  rw [Multiset.map_map, Multiset.map_map] at e
  simpa [Function.comp_def] using e

theorem herm_of_isSatVec {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {B : Multiset ℂˣ} {φ : Sm E N} (hφ : φ ∈ V)
    (h : GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B) : B.map (fun b => (star b)⁻¹) = B := by
  have h' : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E N).comp (locGL E N w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective h
  exact herm_of_star (_root_.GlobalTheory.LFun.UnitaryParam.map_star_eq_map_inv E w N V _ _ B (isUnitarisable_locRepD hV w) h')

end SatakeHermitian

open SatakeHermitian in
theorem satHerm_holds : SatHerm := by
  intro E _ _ _ N w B
  refine ⟨fun V hV hS => ?_, fun π hN hu hn hB => ?_⟩
  · obtain ⟨φ, hφ, h⟩ := hS.1
    exact herm_of_isSatVec hV hφ h
  · have hD : IsDiscrete π.V := PositivityTheory.RSHS.L1.cuspDiscrete E N hN π hu hn
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
    have h1 := hx.map (ρ' := (finRep E N).comp (locGL E N w)) π.V.subtype (fun _ _ => rfl)
      (fun e => hx.1 (Subtype.ext e))
    exact herm_of_isSatVec hD x.2 h1

end PositivityTheory.Rg.Rs

end
