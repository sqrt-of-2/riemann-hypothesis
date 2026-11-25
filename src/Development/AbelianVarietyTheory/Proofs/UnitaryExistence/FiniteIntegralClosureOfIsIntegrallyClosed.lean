module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormFin

theorem finite_of_semilinear_injective {R S N M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module S M] [Module.Finite S M]
    (φ : R →+* S) (hφ : φ.Finite) (f : N →ₛₗ[φ] M) (hf : Function.Injective f) :
    Module.Finite R N := by
  let := φ.toAlgebra
  let : Module R M := Module.compHom M φ
  have : IsScalarTower R S M := ⟨fun r s m => mul_smul (φ r) s m⟩
  have : Module.Finite R S := hφ
  have : Module.Finite R M := Module.Finite.trans S M
  let g : N →ₗ[R] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smulₛₗ r x }
  exact Module.Finite.of_injective g hf

theorem finite_iterateFrobenius (k P : Type*) [Field k] [PerfectField k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (p : ℕ) [ExpChar k p] [ExpChar P p] (e : ℕ) :
    (iterateFrobenius P p e).Finite := by
  refine RingHom.IsIntegral.to_finite ?_ ?_
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_ne_zero k p)), ?_⟩
    simp [iterateFrobenius_def]
  · refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k P) ?_
    have h : (iterateFrobenius P p e).comp (algebraMap k P) =
        (algebraMap k P).comp (iterateFrobenius k p e) := by
      ext x
      simp [iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (.of_surjective _ (bijective_iterateFrobenius k p e).2)

theorem finite_integralClosure_of_isIntegrallyClosed (k P K F : Type*) [Field k] [PerfectField k]
    [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [Algebra k P] [Algebra.FiniteType k P]
    [Field K] [Algebra P K] [IsFractionRing P K] [Field F] [Algebra K F] [Algebra P F]
    [IsScalarTower P K F] [FiniteDimensional K F] : Module.Finite P (integralClosure P F) := by
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar P p := expChar_of_injective_algebraMap (algebraMap k P).injective p
  have : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective P K) p
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let E := separableClosure K F
  have : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  have : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P K E _
  have : IsScalarTower P E F := .of_algebraMap_eq' rfl
  let e := IsPurelyInseparable.exponent E F
  have hE : ∀ z : F, z ^ p ^ e ∈ E := fun z => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p z
    exact hy ▸ y.2
  let f : integralClosure P F →ₛₗ[iterateFrobenius P p e] integralClosure P E :=
    { toFun := fun z => ⟨⟨z.1 ^ p ^ e, hE _⟩,
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) Subtype.val_injective).mp
          (IsIntegral.pow z.2 _)⟩
      map_add' := fun x y => Subtype.ext (Subtype.ext (add_pow_expChar_pow _ _ _ _))
      map_smul' := fun r x => Subtype.ext (Subtype.ext (by
        change (r • x.1) ^ p ^ e = (r ^ p ^ e) • x.1 ^ p ^ e
        rw [smul_pow])) }
  refine finite_of_semilinear_injective _ (finite_iterateFrobenius k P p e) f fun x y h => ?_
  have h1 : x.1 ^ p ^ e = y.1 ^ p ^ e := congrArg (fun w : integralClosure P E => (w.1.1 : F)) h
  exact Subtype.ext ((iterateFrobenius F p e).injective h1)

theorem finite_integralClosure_of_perfectField (k B F L : Type*) [Field k] [PerfectField k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field F] [Algebra B F]
    [IsFractionRing B F] [Field L] [Algebra F L] [Algebra B L] [IsScalarTower B F L]
    [FiniteDimensional F L] : Module.Finite B (integralClosure B L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin s) k
  let : Algebra P B := g.toRingHom.toAlgebra
  have : Module.Finite P B := hfin
  have : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : Algebra P F := ((algebraMap B F).comp (algebraMap P B)).toAlgebra
  have : IsScalarTower P B F := .of_algebraMap_eq' rfl
  let : Algebra P L := ((algebraMap B L).comp (algebraMap P B)).toAlgebra
  have : IsScalarTower P B L := .of_algebraMap_eq' rfl
  have : IsScalarTower P F L := .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply B F L _
  have : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective B F).comp hinj)
  let K := FractionRing P
  let : Algebra K F := FractionRing.liftAlgebra P F
  have : FiniteDimensional K F := Module.Finite.of_isLocalization P B (nonZeroDivisors P)
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F L := .of_algebraMap_eq' rfl
  have : IsScalarTower P K L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F L, ← IsScalarTower.algebraMap_apply P K F,
      ← IsScalarTower.algebraMap_apply P F L]
  have : FiniteDimensional K L := Module.Finite.trans F L
  have := finite_integralClosure_of_isIntegrallyClosed k P K L
  have h : Module.Finite P ((integralClosure B L).restrictScalars P) := by
    rwa [integralClosure_restrictScalars_of_isIntegral]
  have : Module.Finite P (integralClosure B L) := h
  exact Module.Finite.of_restrictScalars_finite P B _

theorem finite_integralClosure_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (F : Type) [Field F] [Algebra B F] [IsFractionRing B F],
      Module.Finite B (integralClosure B F) :=
  fun k _ _ B _ _ _ _ F _ _ _ => finite_integralClosure_of_perfectField k B F F

end GlobalTheory.NormFin
