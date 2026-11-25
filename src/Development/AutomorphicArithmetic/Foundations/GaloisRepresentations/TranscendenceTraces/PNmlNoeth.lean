module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.SetTheory.ZFC.PSet
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_open_irreducible_nhds_of_generizations {Y : Type*} [TopologicalSpace Y] [QuasiSober Y]
    [TopologicalSpace.NoetherianSpace Y] (y : Y) (hG : IsIrreducible {z | z ⤳ y}) :
    ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ IsIrreducible U := by
  have key : ∀ W ∈ irreducibleComponents Y, y ∈ W → W = closure {z | z ⤳ y} := by
    intro W hW hyW
    have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
    have hgen := hW.1.isGenericPoint_genericPoint_closure
    rw [hWc.closure_eq] at hgen
    have hcl : closure {hW.1.genericPoint} = W := hgen
    have hsub : W ⊆ closure {z | z ⤳ y} := by
      rw [← hcl]
      exact closure_mono (Set.singleton_subset_iff.mpr (hgen.specializes hyW))
    exact le_antisymm hsub (hW.2 hG.closure hsub)
  let C := irreducibleComponent y
  refine ⟨(⋃₀ (irreducibleComponents Y \ {C}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_sdiff, Set.mem_singleton_iff,
      not_exists, not_and, and_imp]
    intro W hW hne hyW
    exact hne ((key W hW hyW).trans (key C (irreducibleComponent_mem_irreducibleComponents y)
      mem_irreducibleComponent).symm)
  · apply isIrreducible_iff_closure.mp
    rw [closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents _
      (irreducibleComponent_mem_irreducibleComponents y)]
    exact isIrreducible_irreducibleComponent

private theorem isIntegrallyClosed_affine_of_stalks {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    [IsDomain Γ(X, U)] (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
  let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  change IsIntegrallyClosed (Localization.AtPrime y.asIdeal)
  exact (h _).of_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime y.asIdeal)).toRingEquiv

theorem UpperTheory.Gal.TranscendenceTraces.nmlNoeth_of :
    NmlNoeth := by
  intro S _ hN x
  have : ∀ z : S, IsDomain (S.presheaf.stalk z) := fun z => (hN z).1
  obtain ⟨_, ⟨V : S.Opens, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV.isCompact
  have : IsNoetherian V.toScheme := {}
  have hns : TopologicalSpace.NoetherianSpace V.toScheme := inferInstance
  have hqs : QuasiSober V.toScheme := inferInstance
  have hG : IsIrreducible {z | z ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    have : IrreducibleSpace (Spec (S.presheaf.stalk x)) := PrimeSpectrum.irreducibleSpace
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (S.fromSpecStalk x).continuous.continuousOn
  have hGV : {z | z ⤳ x} ⊆ (V : Set S) := fun z hz => hz.mem_open V.isOpen hxV
  have hG' : IsIrreducible {z : V | z ⤳ ⟨x, hxV⟩} := by
    have he : {z : V | z ⤳ ⟨x, hxV⟩} =
        Set.range (fun z : {z | z ⤳ x} => (⟨z.1, hGV z.2⟩ : V)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z.1, (Topology.IsInducing.subtypeVal.specializes_iff).mpr hz⟩, rfl⟩
      · rintro ⟨w, rfl⟩
        exact (Topology.IsInducing.subtypeVal.specializes_iff).mp w.2
    rw [he, ← Set.image_univ]
    have : IrreducibleSpace {z | z ⤳ x} := isIrreducible_iff_irreducibleSpace.mp hG
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (by fun_prop : Continuous _).continuousOn
  obtain ⟨W, hWo, hxW, hWi⟩ := @exists_open_irreducible_nhds_of_generizations V.toScheme _ hqs hns ⟨x, hxV⟩ hG'
  have hW'o : IsOpen (Subtype.val '' W : Set S) := V.isOpen.isOpenMap_subtypeVal W hWo
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hxU, hUW⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (⟨_, hxW, rfl⟩ : x ∈ Subtype.val '' W) hW'o
  have hUi : IsIrreducible (U : Set S) :=
    ⟨⟨x, hxU⟩, (hWi.image _ continuous_subtypeVal.continuousOn).2.open_subset U.isOpen hUW⟩
  have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp hUi
  have : IsReduced S := isReduced_of_isReduced_stalk S
  have : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨⟨x, hxU⟩, trivial⟩⟩
  have : IsDomain Γ(S, U) :=
    MulEquiv.isDomain Γ(U.toScheme, ⊤) (U.topIso).commRingCatIsoToRingEquiv.symm.toMulEquiv
  exact ⟨U, hU, hxU, inferInstance, isIntegrallyClosed_affine_of_stalks hU fun z => (hN z).2⟩
