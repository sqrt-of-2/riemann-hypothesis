module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PicardGroup
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
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormCurve

theorem exists_eq_div {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) (z : R) :
    ∃ x y : B, z = algebraMap B R x / algebraMap B R y := by
  obtain ⟨x, r, c, hc, hr, e⟩ := (RingHom.surjective_localRingHom_iff (⊥ : Ideal R)).mp
    (h ⊥ inferInstance) z
  rw [Ideal.mem_bot] at hc hr
  refine ⟨x, r, ?_⟩
  rw [eq_div_iff hr]
  apply mul_left_cancel₀ hc
  rw [← e]
  ring

theorem isIntegrallyClosed_integralClosure {B R : Type} [CommRing B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) : IsIntegrallyClosed (integralClosure B R) := by
  have : IsFractionRing (integralClosure B R) R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, e⟩
  exact (isIntegrallyClosed_iff R).mpr fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

theorem finite_integralClosure (k : Type) {B R : Type} [Field k] [PerfectField k] [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] [Field R] [Algebra B R]
    (h : (algebraMap B R).SurjectiveOnStalks) :
    Module.Finite B (integralClosure B R) ∧ ∀ [Algebra k R] [IsScalarTower k B R],
      ringKrullDim (B ⧸ RingHom.ker (algebraMap B R)) ≤ 1 → Algebra.trdeg k R ≤ 1 := by
  let A := B ⧸ RingHom.ker (algebraMap B R)
  have : (RingHom.ker (algebraMap B R)).IsPrime := RingHom.ker_isPrime _
  let : Algebra A R := (RingHom.kerLift (algebraMap B R)).toAlgebra
  have : IsScalarTower B A R := .of_algebraMap_eq fun x => (RingHom.kerLift_mk _ x).symm
  have : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (RingHom.kerLift_injective _)
  have : IsFractionRing A R := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, e⟩ := exists_eq_div h z
    exact ⟨algebraMap B _ x, algebraMap B _ y, by
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩
  constructor
  · have := NormFin.finite_integralClosure_of_perfectField k A R R
    have : Module.Finite B (integralClosure A R) := Module.Finite.trans A _
    have h' : Module.Finite B ((integralClosure A R).restrictScalars B) := this
    rwa [integralClosure_restrictScalars_of_isIntegral] at h'
  · intro _ _ hd
    have : IsScalarTower k A R := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply k B R, IsScalarTower.algebraMap_apply k B A,
        ← IsScalarTower.algebraMap_apply B A R]
    obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
    have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap k A).injective
    have : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := R), trdeg_eq_zero (R := A) (A := R), add_zero, hs2]
    rw [hs1] at hd
    exact_mod_cast hd

theorem dimensionLEOne_of_injective {k A R : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [CommRing R] [Algebra k R] (g : A →ₐ[k] R)
    (hg : Function.Injective g) (h : Algebra.trdeg k R ≤ 1) : Ring.DimensionLEOne A := by
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  have h1 := (trdeg_le_of_injective g hg).trans h
  rw [hs2] at h1
  have h2 : s ≤ 1 := by exact_mod_cast h1
  have h3 : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hs1]
    exact_mod_cast h2
  exact ⟨fun {p} hp hp' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h3 p hp hp'⟩

section Scheme

variable {k : Type} [Field k] {X Z : Scheme.{0}}

noncomputable def constHom (s : X ⟶ Sp k) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ s.appLE ⊤ U le_top).hom

theorem finiteType_constHom (s : X ⟶ Sp k) [LocallyOfFiniteType s] {U : X.Opens}
    (hU : IsAffineOpen U) : (constHom s U).FiniteType := by
  have h : (s.appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      le_top
  exact h.comp (.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)

theorem appLE_comp_constHom (s : X ⟶ Sp k) (f : Z ⟶ X) (U : X.Opens) (V : Z.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.comp (constHom s U) = constHom (f ≫ s) V := by
  rw [constHom, constHom, ← Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top e]
  rfl

theorem isField_sections [IsIntegral Z] [Subsingleton Z] (V : Z.Opens) [hV : Nonempty V] :
    IsField Γ(Z, V) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => IsUnit.exists_right_inv ?_⟩
  refine Z.toRingedSpace.isUnit_of_isUnit_germ V a fun x hx => ?_
  have h : Z.basicOpen a ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff a).mp h)
  obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h
  rw [Subsingleton.elim y x] at hy
  exact (Z.mem_basicOpen a x hx).mp hy

theorem isAffineOpen_of_subsingleton [IsAffine Z] [Subsingleton Z] (V : Z.Opens)
    [hV : Nonempty V] : IsAffineOpen V := by
  obtain ⟨y, hy⟩ := hV
  have : V = ⊤ := eq_top_iff.mpr fun x _ => Subsingleton.elim y x ▸ hy
  rw [this]
  exact isAffineOpen_top Z

variable [IsIntegral Z] [Subsingleton Z] [IsAffine Z] (f : Z ⟶ X) [SurjectiveOnStalks f]

theorem surjectiveOnStalks_appLE {U : X.Opens} (hU : IsAffineOpen U) (V : Z.Opens) [Nonempty V]
    (e : V ≤ f ⁻¹ᵁ U) : (f.appLE U V e).hom.SurjectiveOnStalks :=
  HasRingHomProperty.appLE @SurjectiveOnStalks f inferInstance ⟨U, hU⟩
    ⟨V, isAffineOpen_of_subsingleton V⟩ e

variable [QuasiCompact f] [QuasiSeparated f]

theorem isFinite_fromNormalization [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s] :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  let := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(X, U) (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    by_cases hne : Nonempty (f ⁻¹ᵁ U)
    · let := (isField_sections (f ⁻¹ᵁ U)).toField
      let := (constHom s U).toAlgebra
      have : Algebra.FiniteType k Γ(X, U) := finiteType_constHom s hU
      refine (finite_integralClosure k ?_).1
      have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
      rwa [← Scheme.Hom.app_eq_appLE] at this
    · have : f ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun x hx => (hne ⟨⟨x, hx⟩⟩).elim
      have : Subsingleton Γ(Z, f ⁻¹ᵁ U) := by rw [this]; infer_instance
      infer_instance
  exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr h)

theorem isIntegrallyClosed_stalk (y : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  have hy : y ∈ f.fromNormalization ⁻¹ᵁ U := hyU
  have hne : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨y, hy⟩
    refine ⟨⟨z, ?_⟩⟩
    rw [← f.toNormalization_fromNormalization]
    exact hz
  let := (f.app U).hom.toAlgebra
  have h1 : IsIntegrallyClosed (integralClosure Γ(X, U) Γ(Z, f ⁻¹ᵁ U)) := by
    let := (isField_sections (f ⁻¹ᵁ U)).toField
    refine isIntegrallyClosed_integralClosure ?_
    have := surjectiveOnStalks_appLE f hU (f ⁻¹ᵁ U) le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  have h2 : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have hV := hU.preimage f.fromNormalization
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  let := f.normalization.presheaf.algebra_section_stalk (⟨y, hy⟩ : f.fromNormalization ⁻¹ᵁ U)
  have := hV.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization (R := Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)) _
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)

theorem isDedekindDomain_sections [PerfectField k] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hd : letI := (constHom (f ≫ s) ⊤).toAlgebra; Algebra.trdeg k Γ(Z, ⊤) ≤ 1)
    (U : f.normalization.Opens) (hU : IsAffineOpen U) [hne : Nonempty U] :
    IsDedekindDomain Γ(f.normalization, U) := by
  have := isFinite_fromNormalization f s
  let := (constHom (f ≫ s) ⊤).toAlgebra
  let := (constHom (f.fromNormalization ≫ s) U).toAlgebra
  have : Algebra.FiniteType k Γ(f.normalization, U) := finiteType_constHom _ hU
  have e : ⊤ ≤ f.toNormalization ⁻¹ᵁ U := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
    exact fun x _ => Subsingleton.elim z x ▸ hz
  have hc := appLE_comp_constHom (f.fromNormalization ≫ s) f.toNormalization U ⊤ e
  rw [f.toNormalization_fromNormalization_assoc] at hc
  let g : Γ(f.normalization, U) →ₐ[k] Γ(Z, ⊤) :=
    { (f.toNormalization.appLE U ⊤ e).hom with commutes' := fun a => congr($hc a) }
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have h : f.normalization.basicOpen a ≠ ⊥ := fun h => h0 ((basicOpen_eq_bot_iff a).mp h)
    obtain ⟨z, hz⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.normalization.basicOpen a).isOpen ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp h)
    have h1 : z ∈ Z.basicOpen (f.toNormalization.appLE U ⊤ e a) := by
      rw [Scheme.basicOpen_appLE]
      exact ⟨trivial, hz⟩
    have ha' : f.toNormalization.appLE U ⊤ e a = 0 := ha
    rw [ha', Scheme.basicOpen_zero] at h1
    exact h1
  exact { Algebra.FiniteType.isNoetherianRing k _, dimensionLEOne_of_injective g hg hd,
    isIntegrallyClosed_sections_of_stalks (isIntegrallyClosed_stalk f) hU with }

end Scheme

end GlobalTheory.NormCurve
