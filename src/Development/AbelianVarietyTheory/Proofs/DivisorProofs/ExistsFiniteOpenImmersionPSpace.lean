module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

namespace GlobalTheory.ZMain

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem finite_integralClosure_field (R L : Type*) [CommRing R] [Algebra.FiniteType ℤ R] [Field L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | h0
  · let p := ringChar L
    have : Fact p.Prime := ⟨hp⟩
    have : CharP L p := ringChar.charP L
    let I := RingHom.ker (algebraMap R L)
    let R' := R ⧸ I
    let : Algebra R' L := (Ideal.Quotient.lift I (algebraMap R L) fun _ h => h).toAlgebra
    have : IsScalarTower R R' L := .of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap R' L) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have : IsDomain R' := hinj.isDomain _
    have : FaithfulSMul R' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have : CharP R' p := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff L]⟩
    let : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
    have : Algebra.FiniteType ℤ R' := .trans (S := R) inferInstance inferInstance
    have : Algebra.FiniteType (ZMod p) R' := .of_restrictScalars_finiteType ℤ (ZMod p) R'
    have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing (ZMod p) R'
    have : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R')
      Ideal.Quotient.mk_surjective
    let F := FractionRing R'
    let : Algebra F L := FractionRing.liftAlgebra R' L
    have : Algebra.EssFiniteType R' L := .of_comp R R' L
    have : Algebra.EssFiniteType F L := .of_comp R' F L
    let E := algebraicClosure F L
    have : FiniteDimensional F E := finiteDimensional_algebraicClosure_of_essFiniteType F L
    have : Module.Finite R' (integralClosure R' E) :=
      NormFin.finite_integralClosure_of_perfectField (ZMod p) R' F E
    have : IsScalarTower R' E L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R' F L x, IsScalarTower.algebraMap_apply R' F E x,
        ← IsScalarTower.algebraMap_apply F E L]
    have hmem : ∀ z : integralClosure R' L, (z : L) ∈ E := fun z =>
      mem_algebraicClosure_iff.mpr (z.2.tower_top (A := F)).isAlgebraic
    let ψ : integralClosure R' L →ₗ[R'] integralClosure R' E :=
      { toFun := fun z => ⟨⟨z, hmem z⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom R' E L)
            (IsScalarTower.toAlgHom R' E L).toRingHom.injective).mp z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have : Module.Finite R' (integralClosure R' L) := Module.Finite.of_injective ψ
      fun a b h => Subtype.ext (congrArg (fun w : integralClosure R' E => ((w : E) : L)) h)
    exact finite_integralClosure_of_finite_tower R R' L
  · have : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
    exact finite_integralClosure_of_essFiniteType_field ℤ R L

universe u

theorem isFinite_fromNormalization_int {X Y : Scheme.{u}} {o : CommRingCat.{u}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsIntegral X]
    (hess : (f.residueFieldMap (genericPoint X)).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  let := (f.app U).hom.toAlgebra
  let : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  have : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  have : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  have : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := {genericPoint X}
  have hD : Dense D := dense_iff_closure_eq.mpr (genericPoint_spec X)
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  have : Finite ι := ((Set.finite_singleton _).inter_of_left _).to_subtype
  let (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  have (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    have hx : x.1 = genericPoint X := x.2.1
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType)
      (by rw [hx] at *; exact hess)
  have (x : ι) := finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_finite_openImmersion_pSpace : ∀ (o : Type) [CommRing o] [IsNoetherianRing o]
    [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (f : X ⟶ PSpace o m), IsIntegral X →
    Geo.Tor.IsNormalScheme X → LocallyOfFiniteType f → QuasiCompact f → IsSeparated f →
    LocallyQuasiFinite f → ∃ (Z : Scheme.{0}) (z : Z ⟶ PSpace o m) (i : X ⟶ Z), IsFinite z ∧
      IsOpenImmersion i ∧ i ≫ z = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧
      Dense (Set.range i) := by
  intro o _ _ _ m X f hX hN _ _ _ _
  have : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  have := isProper_str o m
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  refine ⟨f.normalization, f.fromNormalization, f.toNormalization,
    isFinite_fromNormalization_int f (PSpace.str o m)
      (LocallyOfFiniteType.stalkMap f _).residueFieldMap,
    inferInstance, f.toNormalization_fromNormalization,
    (GlobalTheory.IsNormalScheme.normalization_of_isIntegral f).pred _, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

end GlobalTheory.ZMain
