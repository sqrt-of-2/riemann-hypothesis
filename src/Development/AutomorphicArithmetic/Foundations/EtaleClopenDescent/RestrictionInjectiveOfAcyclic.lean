module

public import Development.EtaleCohomology.WeilConjectures.AcycPf
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb

open LateralTheory.EWeil.AcycPf

private lemma exact_filtered (R : Type) [CommRing R] (J : Type 1) [Category.{0} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{1} (ULift.{1} R)) := by
  let e : J ≌ ULiftHom.{1} J := ULiftHom.equiv
  have : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm

private lemma mono_of_isColimit {J : Type 1} [Category.{0} J] {A : Type 2} [Category.{1} A] [Abelian A]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {K L : J ⥤ A} (τ : K ⟶ L) [Mono τ]
    {c : Cocone K} {d : Cocone L} (hc : IsColimit c) (hd : IsColimit d) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = τ.app j ≫ d.ι.app j) : Mono m := by
  have key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫
      (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv := by
    refine hc.hom_ext fun j => ?_
    simp [hm]
  have hτ : Mono (colim.map τ) := inferInstance
  have hτ' : Mono (colimMap τ) := hτ
  rw [key]
  infer_instance

private lemma lan_mono {C D : Type 1} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) [RepresentablyFlat G]
    {A : Type 2} [Category.{1} A] [Abelian A]
    [∀ X, HasColimitsOfShape (CostructuredArrow G.op X) A]
    (hA : ∀ (J : Type 1) [Category.{0} J] [IsFiltered J] [HasColimitsOfShape J A], HasExactColimitsOfShape J A)
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Mono φ] : Mono ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ) := by
  have hφ : ∀ c, Mono (φ.app c) := fun c => inferInstance
  have key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X) := by
    intro X
    have : IsFiltered (CostructuredArrow G.op X) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))
    have := hA (CostructuredArrow G.op X)
    have : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) :=
      fun j => hφ _
    have : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) :=
      NatTrans.mono_of_mono_app _
    refine mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_
    intro j
    have h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left :=
      (congr_app (G.op.lanUnit.naturality φ) j.left).symm
    have h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫
        ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom := by
      rw [NatTrans.naturality, reassoc_of% h₂]
    first
      | exact (Category.assoc _ _ _).trans h₃
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_flat (S : Scheme.{0}) : RepresentablyFlat (incl S) := by
  have : PreservesFiniteLimits (incl S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
private lemma incl_cont (S : Scheme.{0}) :
    (incl S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  have := incl_flat S
  have : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full
  have : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful
  have : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)

private lemma restr_inj : RestrInj := by
  intro R _ S G _
  have := incl_cont S
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S)
    (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)
  have : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R))
      S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    have := incl_flat S
    have : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) :=
      inferInstance
    have : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map
        ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) :=
      lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _
    exact (presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _
  exact ⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩

end UpperTheory.Cb

alias UpperTheory.Cb.restrInj := _root_.UpperTheory.Cb.restr_inj
