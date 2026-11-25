module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLimit

section Ring
open TensorProduct IsLocalRing

variable {V A S C : Type} [CommRing V] [CommRing A] [CommRing S] [CommRing C] [Algebra V A]
  [Algebra A S] [Algebra V S] [IsScalarTower V A S] [Algebra V C]

theorem flat_and_formallySmooth_tensor (M : Submonoid A) [IsLocalization M S]
    [Algebra.Smooth C (C ⊗[V] A)] :
    Module.Flat C (C ⊗[V] S) ∧ Algebra.FormallySmooth C (C ⊗[V] S) := by
  let φ : C ⊗[V] A →ₐ[C] C ⊗[V] S :=
    Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom V A S)
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower C (C ⊗[V] A) (C ⊗[V] S) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have := IsLocalization.tensorProduct_tensorProduct_right V C M S (by
    ext a; simp [RingHom.algebraMap_toAlgebra, φ])
  have : Module.Flat (C ⊗[V] A) (C ⊗[V] S) :=
    IsLocalization.flat _ (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  have : Algebra.FormallySmooth (C ⊗[V] A) (C ⊗[V] S) :=
    .of_isLocalization (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  exact ⟨.trans C (C ⊗[V] A) _, .comp C (C ⊗[V] A) _⟩

theorem isSmoothAt_of_smooth_quotient_pow [IsLocalRing V] [IsNoetherianRing V]
    [Algebra.FiniteType V A]
    (h : ∀ e : ℕ, Algebra.Smooth (V ⧸ maximalIdeal V ^ (e + 1))
      ((V ⧸ maximalIdeal V ^ (e + 1)) ⊗[V] A))
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap V A) = maximalIdeal V) :
    Algebra.IsSmoothAt V q := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  have : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let S := Localization.AtPrime q
  have hle : (maximalIdeal V).map (algebraMap V S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq V A S, ← Ideal.comap_comap,
      show (maximalIdeal S).comap (algebraMap A S) = q from
        Localization.AtPrime.under_maximalIdeal, hq]
  have : IsLocalHom (algebraMap V S) :=
    ((IsLocalRing.local_hom_tfae (algebraMap V S)).out 3 1).mp hle
  have : Module.Flat V S := by
    refine LocalFlat.flat_of_relationsLift S (I := maximalIdeal V)
      (hle.trans (IsLocalRing.maximalIdeal_le_jacobson _)) fun n => ?_
    rcases n with _ | e
    · intro F _ _ f x _
      exact LocalFlat.range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
    · have := h e
      have := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := V ⧸ maximalIdeal V ^ (e + 1)) q.primeCompl).1
      refine LocalFlat.relationsLift_of_flat (C := V ⧸ maximalIdeal V ^ (e + 1))
        Ideal.Quotient.mk_surjective Ideal.mk_ker
        (TensorProduct.mk V (V ⧸ maximalIdeal V ^ (e + 1)) S 1)
        (TensorProduct.mk_surjective _ _ _ Ideal.Quotient.mk_surjective) ?_
      exact LinearMap.ker_tensorProductMk _
  have : Algebra.Smooth (ResidueField V) (ResidueField V ⊗[V] A) := by
    have := h 0
    let C := V ⧸ maximalIdeal V ^ (0 + 1)
    let : Algebra C (ResidueField V) :=
      (Ideal.Quotient.factor (S := maximalIdeal V ^ (0 + 1)) (T := maximalIdeal V)
        (by simp)).toAlgebra
    have : IsScalarTower V C (ResidueField V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact .of_equiv (Algebra.TensorProduct.cancelBaseChange V C (ResidueField V) (ResidueField V) A)
  have := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := ResidueField V) q.primeCompl).2
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := V) (S := S) (P := A)
    q.primeCompl

end Ring

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V (IsLocalRing.maximalIdeal V) e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have H := this (X.affineCover.f i ≫ f) (fun e => by
      have := h e
      rw [← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) y (by simpa using hx) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let := φ.hom.toAlgebra
  have : Algebra.FinitePresentation V S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  have hs (e : ℕ) : Algebra.Smooth (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))
      (TensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S) := by
    have H := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S)
    have e1 := H.flip.isoPullback_hom_snd
    have h1 : Smooth (H.flip.isoPullback.hom ≫ pullback.snd _ _) := by
      have : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V S)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))))) := h e
      infer_instance
    rw [e1, HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
    exact RingHom.smooth_algebraMap.mp h1
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  have := isSmoothAt_of_smooth_quotient_pow hs x.asIdeal (congrArg PrimeSpectrum.asIdeal hx)
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth V x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  have : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], (∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e B).hom) → Smooth B.hom := by
  intro V _ _ _ _ B _ h
  have : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨y, hy, hy'⟩ := (IsLocalRing.specializes_closedPoint (R := V) (B.hom x)).mem_closed hc ⟨x, hx, rfl⟩
  exact hy (mem_smoothLocus B.hom h y hy')

end GlobalTheory.SmoothLimit
