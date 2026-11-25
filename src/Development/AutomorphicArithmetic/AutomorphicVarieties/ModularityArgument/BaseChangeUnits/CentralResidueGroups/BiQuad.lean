module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Bc

private theorem mem_range_resG_iff (k L Ω : Type) [Field k] [Field L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω]
    [IsScalarTower k L Ω] (s : G k Ω) :
    s ∈ (resG k L Ω).range ↔ ∀ x : L, s (algebraMap L Ω x) = algebraMap L Ω x := by
  constructor
  · rintro ⟨t, rfl⟩ x
    exact t.commutes x
  · intro h
    exact ⟨{ s.toRingEquiv with commutes' := h }, AlgEquiv.ext fun _ => rfl⟩

private theorem comm_on (k K M : Type) [Field k] [Field K] [Field M] [Algebra k K] [Algebra k M] [Algebra K M]
    [IsScalarTower k K M] [h : IsAbelianGalois k K] (σ τ : M ≃ₐ[k] M) (x : K) :
    (σ * τ) (algebraMap K M x) = (τ * σ) (algebraMap K M x) := by
  rw [← AlgEquiv.restrictNormal_commutes, ← AlgEquiv.restrictNormal_commutes]
  change algebraMap K M (AlgEquiv.restrictNormalHom K (σ * τ) x) = algebraMap K M (AlgEquiv.restrictNormalHom K (τ * σ) x)
  rw [map_mul, map_mul, h.is_comm.comm]

private theorem exists_compositum (k K K' Ω : Type) [Field k] [Field K] [Field K'] [Field Ω] [Algebra k K] [Algebra k K']
    [Algebra k Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower k K Ω] [IsScalarTower k K' Ω]
    [FiniteDimensional k K] [FiniteDimensional k K'] [IsAbelianGalois k K] [IsAbelianGalois k K'] :
    ∃ (M : Type) (_ : Field M) (_ : Algebra k M) (_ : Algebra K M) (_ : Algebra K' M) (_ : Algebra M Ω)
      (_ : IsScalarTower k K M) (_ : IsScalarTower k K' M) (_ : IsScalarTower K M Ω) (_ : IsScalarTower K' M Ω),
      FiniteDimensional k M ∧ IsAbelianGalois k M ∧
      ∀ s : Ω ≃ₐ[k] Ω, (∀ x : K, s (algebraMap K Ω x) = algebraMap K Ω x) → (∀ x : K', s (algebraMap K' Ω x) = algebraMap K' Ω x) →
        ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x := by
  let a := IsScalarTower.toAlgHom k K Ω
  let b := IsScalarTower.toAlgHom k K' Ω
  let M : IntermediateField k Ω := a.fieldRange ⊔ b.fieldRange
  have hM : M = IntermediateField.adjoin k ((a.fieldRange : Set Ω) ∪ b.fieldRange) := IntermediateField.sup_def _ _
  have ha : ∀ x, a x ∈ M := fun x => (le_sup_left : a.fieldRange ≤ M) ⟨x, rfl⟩
  have hb : ∀ x, b x ∈ M := fun x => (le_sup_right : b.fieldRange ≤ M) ⟨x, rfl⟩
  let iK : Algebra K M := (a.toRingHom.codRestrict M ha).toAlgebra
  let iK' : Algebra K' M := (b.toRingHom.codRestrict M hb).toAlgebra
  have t1 : IsScalarTower k K M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (a.commutes x).symm
  have t2 : IsScalarTower k K' M := IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (b.commutes x).symm
  have t3 : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have t4 : IsScalarTower K' M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hext : ∀ f g : M →ₐ[k] Ω, (∀ x : K, f (algebraMap K M x) = g (algebraMap K M x)) →
      (∀ x : K', f (algebraMap K' M x) = g (algebraMap K' M x)) → f = g := by
    intro f g h1 h2
    refine IntermediateField.algHom_ext_of_eq_adjoin k hM ?_
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact h1 y
    · exact h2 y
  have : FiniteDimensional k a.fieldRange := a.equivFieldRange.toLinearEquiv.finiteDimensional
  have : FiniteDimensional k b.fieldRange := b.equivFieldRange.toLinearEquiv.finiteDimensional
  have : IsGalois k a.fieldRange := IsGalois.of_algEquiv a.equivFieldRange
  have : IsGalois k b.fieldRange := IsGalois.of_algEquiv b.equivFieldRange
  have : FiniteDimensional k M := IntermediateField.finiteDimensional_sup _ _
  have : Normal k M := IntermediateField.normal_sup k Ω _ _
  have : Algebra.IsSeparable k M := inferInstance
  have : IsGalois k M := ⟨⟩
  refine ⟨M, inferInstance, inferInstance, iK, iK', inferInstance, t1, t2, t3, t4, inferInstance, ?_, ?_⟩
  · refine { is_comm := ⟨fun σ τ => ?_⟩ }
    have := hext (M.val.comp (σ * τ : M ≃ₐ[k] M)) (M.val.comp (τ * σ : M ≃ₐ[k] M))
      (fun x => congrArg Subtype.val (comm_on k K M σ τ x)) (fun x => congrArg Subtype.val (comm_on k K' M σ τ x))
    exact AlgEquiv.ext fun x => Subtype.ext (DFunLike.congr_fun this x)
  · intro s h1 h2 x
    exact DFunLike.congr_fun (hext ((s : Ω →ₐ[k] Ω).comp M.val) M.val h1 h2) x

private theorem abelian_of_two (K : Type) [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) : IsAbelianGalois ℚ K := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨h⟩
  have : IsCyclic (K ≃ₐ[ℚ] K) := inferInstance
  exact IsAbelianGalois.of_isCyclic ℚ K

end UpperTheory.V.Z.Bc

theorem UpperTheory.V.Z.Bc.biQuad :
    BiQuad := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ _ _ h h'
  have := abelian_of_two K h
  have := abelian_of_two K' h'
  obtain ⟨M, fM, iQ, iK, iK', iΩ, t1, t2, t3, t4, hfin, hab, hfix⟩ := exists_compositum ℚ K K' Ω
  have : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  obtain rfl : iQ = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have nM : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  have : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  have cM : IsCMField M := IsCMField.of_isAbelianGalois M
  have a1 : IsAbelianGalois K M := IsAbelianGalois.tower_top ℚ K M
  have a2 : IsAbelianGalois K' M := IsAbelianGalois.tower_top ℚ K' M
  refine ⟨M, fM, nM, cM, iK, iK', iΩ, t3, t4, a1.toIsGalois, a2.toIsGalois,
    Group.isSolvable_of_comm a1.is_comm.comm, Group.isSolvable_of_comm a2.is_comm.comm, fun s => ?_, fun s => ?_⟩
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K' M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K Ω s) s.commutes hs
  · rw [mem_range_resG_iff, mem_range_resG_iff]
    constructor
    · intro hs x
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hs _
    · intro hs
      exact hfix (resG ℚ K' Ω s) hs s.commutes
