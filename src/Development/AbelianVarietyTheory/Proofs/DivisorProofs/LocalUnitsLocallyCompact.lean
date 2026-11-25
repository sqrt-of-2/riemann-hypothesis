module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

theorem locCpt_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : LocallyCompactSpace (Qv v) := by
  have ho : IsOpen (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ)) :=
    (Valued.isClopen_integer (v.1.adicCompletion ℚ)).isOpen
  exact (GlobalTheory.LKTrip.LevelExists.isCompact_intCompl v.1).locallyCompactSpace_of_mem_nhds_of_addGroup
    (ho.mem_nhds (zero_mem _))

theorem secCount_Qv {p : ℕ} [Fact p.Prime] (v : AwayP p) : SecondCountableTopology (Qv v) := by
  have := locCpt_Qv v
  let : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  have : ProperSpace (Qv v) := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  exact secondCountable_of_proper

theorem units_topA (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [LocallyCompactSpace K] [SecondCountableTopology K]
    (A : Type) [Ring A] [Algebra K A] [Module.Finite K A] [TopologicalSpace A] [IsModuleTopology K A] :
    T2Space Aˣ ∧ LocallyCompactSpace Aˣ ∧ SigmaCompactSpace Aˣ := by
  let b := Module.finBasis K A
  let e : A ≃ₗ[K] (Fin (Module.finrank K A) → K) := b.equivFun
  have : ContinuousAdd A := IsModuleTopology.toContinuousAdd K A
  have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A ≃ₜ (Fin (Module.finrank K A) → K) := ⟨e.toEquiv, hc1, hc2⟩
  have : T2Space A := h.isEmbedding.t2Space
  have : LocallyCompactSpace A := h.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology A := h.isEmbedding.secondCountableTopology
  have : IsTopologicalRing A := IsModuleTopology.isTopologicalRing K A
  have : LocallyCompactSpace Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology Aᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace Aˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology Aˣ := Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology
  have : T2Space Aˣ := Units.isEmbedding_embedProduct.t2Space
  exact ⟨inferInstance, inferInstance, sigmaCompactSpace_of_locallyCompact_secondCountable⟩

theorem topA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  intro p _ G v
  let : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  have := locCpt_Qv v
  have := secCount_Qv v
  exact units_topA (Qv v) (Qv v ⊗[ℚ] G.C)

end GlobalTheory.OrbFinAf
