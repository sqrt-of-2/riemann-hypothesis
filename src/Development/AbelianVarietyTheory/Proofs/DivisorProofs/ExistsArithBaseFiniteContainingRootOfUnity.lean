module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_arithBase_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  intro o₁ Ω₁ _ _ _ hb Ω₂ _ _ K ζ hK hζ
  have := hb.ded
  have := hb.ft
  have := hb.char
  have hc₂ : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap Ω₁ Ω₂).injective
  let f : o₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)
  have hf : Function.Injective f := (algebraMap Ω₁ Ω₂).injective.comp hb.inj
  let : Algebra o₁ Ω₂ := f.toAlgebra
  let Q := FractionRing o₁
  let : Algebra Q Ω₂ := (IsFractionRing.lift (K := Q) hf).toAlgebra
  have : IsScalarTower o₁ Q Ω₂ := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsFractionRing.lift_algebraMap (K := Q) hf x).symm)
  have : CharZero Q := (algebraMap Q Ω₂).charZero
  have hpow : (ζ : Ω₂) ^ K = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  have hint : IsIntegral o₁ (ζ : Ω₂) := IsIntegral.of_pow hK (by rw [hpow]; exact isIntegral_one)
  let F : IntermediateField Q Ω₂ := IntermediateField.adjoin Q {(ζ : Ω₂)}
  have : FiniteDimensional Q F := IntermediateField.adjoin.finiteDimensional hint.tower_top
  have : IsDedekindDomain (integralClosure o₁ F) := integralClosure.isDedekindDomain o₁ Q F
  have hfin : Module.Finite o₁ (integralClosure o₁ F) := IsIntegralClosure.finite o₁ Q F _
  let g : integralClosure o₁ F →+* Ω₂ := (algebraMap F Ω₂).comp (algebraMap (integralClosure o₁ F) F)
  have hg : Function.Injective g := (algebraMap F Ω₂).injective.comp Subtype.val_injective
  let zF : F := ⟨ζ, IntermediateField.mem_adjoin_simple_self Q _⟩
  have hzF : zF ^ K = 1 := Subtype.ext (by simpa using hpow)
  let z : integralClosure o₁ F :=
    ⟨zF, IsIntegral.of_pow hK (by rw [hzF]; exact isIntegral_one)⟩
  have hz : z ^ K = 1 := Subtype.ext (by simpa using hzF)
  refine ⟨integralClosure o₁ F, inferInstance, g.toAlgebra,
    @ArithBase.mk _ _ _ _ g.toAlgebra inferInstance ?_ hc₂ hg,
    algebraMap o₁ (integralClosure o₁ F), Units.ofPowEqOne z K hz hK.ne', ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.trans (S := o₁) inferInstance inferInstance
  · exact RingHom.finite_algebraMap.mpr hfin
  · ext x
    rfl
  · ext
    rfl

end GlobalTheory.Poinc
