module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FunctionFieldTrdeg

theorem trdeg_functionField_eq : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (s : G ⟶ Sp F) (d : ℕ), IsProjOver s → topologicalKrullDim G = d → ∀ (φ : F →+* G.functionField), G.fromSpecStalk (genericPoint G) ≫ s = spMap φ → (letI := φ.toAlgebra; Algebra.trdeg F G.functionField = d) := by
  intro F _ G _ s d hs hd φ hφ
  obtain ⟨N, i, hi, hcomp⟩ := hs
  have : IsProper (PSpace.str F N) := isProper_str F N
  have : LocallyOfFiniteType s := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G)) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ s)
  have hψ : Spec.map ψ = hU.fromSpec ≫ s := Spec.map_preimage _
  let : Algebra F Γ(G, U) := ψ.hom.toAlgebra
  have hft : Algebra.FiniteType F Γ(G, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(G, U) = d :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F s hU ⟨_, hxU⟩ d hd
  let : Algebra F G.functionField := φ.toAlgebra
  have key : CommRingCat.ofHom φ = ψ ≫ G.germToFunctionField U := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ = _
    rw [← hφ, hψ, ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower F Γ(G, U) G.functionField :=
    IsScalarTower.of_algebraMap_eq' congr($(key).hom)
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  have : FaithfulSMul F Γ(G, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(G, U)).injective
  have : FaithfulSMul Γ(G, U) G.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(G, U) G.functionField)
  have : Algebra.IsAlgebraic Γ(G, U) G.functionField := IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(G, U))
  show Algebra.trdeg F G.functionField = d
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top F Γ(G, U) G.functionField, hA]

end GlobalTheory.FunctionFieldTrdeg
