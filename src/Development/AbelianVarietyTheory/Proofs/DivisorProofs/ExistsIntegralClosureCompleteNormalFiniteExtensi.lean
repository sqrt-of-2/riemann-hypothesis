module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_integralClosure_isCN_finite_local : ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀], IsCN V₀ → ∀ (L : Type) [Field L] [Algebra (FractionRing V₀) L] [FiniteDimensional (FractionRing V₀) L], ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ : V₀ →+* V₁) (σ : L →+* FractionRing V₁), IsCN V₁ ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ x : V₀, σ (algebraMap (FractionRing V₀) L (algebraMap V₀ (FractionRing V₀) x)) = algebraMap V₁ (FractionRing V₁) (ρ x) := by
  intro V₀ _ _ _ hV L _ _ _
  obtain ⟨hN, hIC, hC, hCZ⟩ := hV
  have := hN
  have := hIC
  have := hC
  have := hCZ
  let K₀ := FractionRing V₀
  let : Algebra V₀ L := ((algebraMap K₀ L).comp (algebraMap V₀ K₀)).toAlgebra
  have : IsScalarTower V₀ K₀ L := .of_algebraMap_eq fun _ => rfl
  have : CharZero K₀ := IsFractionRing.charZero_of_isFractionRing V₀
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K₀ L).injective
  have : Algebra.IsSeparable K₀ L := inferInstance
  let V₁ := integralClosure V₀ L
  have : Module.Finite V₀ V₁ := IsIntegralClosure.finite V₀ K₀ L V₁
  have hN₁ : IsNoetherianRing V₁ := IsIntegralClosure.isNoetherianRing V₀ K₀ L V₁
  have : IsFractionRing V₁ L := IsIntegralClosure.isFractionRing_of_finite_extension V₀ K₀ L V₁
  have : IsIntegrallyClosed V₁ := integralClosure.isIntegrallyClosedOfFiniteExtension K₀
  have : HenselianLocalRing V₀ := GlobalTheory.henselianLocalRing_of_isAdicComplete V₀
  have : IsLocalRing V₁ := GlobalTheory.TameKummer.isLocalRing_of_finite V₀ V₁
  have hinj : Function.Injective (algebraMap V₀ V₁) := by
    intro a b h
    have h' := congrArg (algebraMap V₁ L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply V₀ K₀ L, IsScalarTower.algebraMap_apply V₀ K₀ L b] at h'
    exact IsFractionRing.injective V₀ K₀ ((algebraMap K₀ L).injective h')
  have : CharZero V₁ := charZero_of_injective_algebraMap hinj
  have : IsLocalHom (algebraMap V₀ V₁) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : (maximalIdeal V₁).comap (algebraMap V₀ V₁) = maximalIdeal V₀ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V₀) (maximalIdeal V₁))
    have hmem : a ∈ (maximalIdeal V₁).comap (algebraMap V₀ V₁) := by
      rw [hm]; exact hna
    exact hmem ha
  have hcompl : IsAdicComplete (maximalIdeal V₁) V₁ :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V₀ V₁
  let e : L ≃ₐ[V₁] FractionRing V₁ := IsLocalization.algEquiv (nonZeroDivisors V₁) L (FractionRing V₁)
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, algebraMap V₀ V₁, e.toRingEquiv.toRingHom,
    ⟨hN₁, inferInstance, hcompl, inferInstance⟩, hinj, RingHom.finite_algebraMap.mpr inferInstance,
    inferInstance, fun x => ?_⟩
  have hx : algebraMap K₀ L (algebraMap V₀ K₀ x) = algebraMap V₁ L (algebraMap V₀ V₁ x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
  rw [hx, AlgEquiv.commutes]

end GlobalTheory.Poinc
