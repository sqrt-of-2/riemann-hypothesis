module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryChartHodgeMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system


open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem tb_F {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) :
    IsTranscendenceBasis ℂ (fun j : Fin d => x j.succ / x 0) := by
  refine pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩
  refine (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))
    (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_
  have ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0) := by
    rw [pd.gen]; trivial
  exact isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))

private theorem algHom_finite_of_proper {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F}
    (pd : IsPd ℂ x) [FiniteDimensional F K] [FiniteDimensional F L] (j2 : K →ₐ[ℂ] L) :
    j2.toRingHom.Finite := by
  have hF := tb_F pd
  set t : Fin d → F := fun j => x j.succ / x 0 with ht
  have hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t) := hF.algebraMap_comp
  have hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t) := hF.algebraMap_comp
  let : Algebra K L := j2.toRingHom.toAlgebra
  have : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective
  have hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])
  have halg : Algebra.IsAlgebraic K L := hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _
  obtain ⟨s, hs⟩ := (Module.finite_def (R := F) (M := L)).1 inferInstance
  let S : Set L := (s : Set L) ∪ Set.range (algebraMap F L ∘ t)
  have hSfin : S.Finite := s.finite_toSet.union (Set.finite_range _)
  have : Finite S := hSfin
  have htop : IntermediateField.adjoin K S = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    let P : IntermediateField ℂ L := (IntermediateField.adjoin K S).restrictScalars ℂ
    have hP : ∀ f : F, algebraMap F L f ∈ P := by
      have hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)
      rw [pd.gen] at hle
      exact fun f => hle (IntermediateField.mem_top)
    have hy : y ∈ Submodule.span F (s : Set L) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha =>
      rw [Algebra.smul_def]
      exact mul_mem (hP r) ha
  have : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at this
  change Module.Finite K L
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

private theorem fg_rB {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F L]
    (J : Finset (Fin (d + 1))) : (rB ℂ L x J).FG := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have hbot : rB ℂ L x ∅ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)
      have h : IsIntegral ℂ y := isIntegral_trans (A := rA ℂ x ∅) y hy
      have := minpoly.mem_range_of_degree_eq_one ℂ y
        (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))
      exact Algebra.mem_bot.2 this
    rw [hbot]
    exact Subalgebra.fg_bot
  · have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
    have : IsFractionRing (rA ℂ x J) F := (_root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1
    have : IsNoetherianRing (rA ℂ x J) := (_root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).2
    have := rA_isIntegrallyClosed pd hi
    set_option synthInstance.maxHeartbeats 200000 in
      have : Module.Finite (rA ℂ x J) (integralClosure (rA ℂ x J) L) :=
        IsIntegralClosure.finite (rA ℂ x J) F L (integralClosure (rA ℂ x J) L)
    have hfg : (rA ℂ x J).FG := by
      refine Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩
      refine ((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image
        fun p => x p.2 / x p.1).subset ?_
      rintro _ ⟨i', hi', j, rfl⟩
      exact ⟨(i', j), ⟨hi', trivial⟩, rfl⟩
    have : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg
    set_option synthInstance.maxHeartbeats 200000 in
      have hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L) :=
        Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft

private theorem integralClosure_finiteGenerated {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F K]
    (j2 : K →ₐ[ℂ] L) (hf : j2.toRingHom.Finite) (J : Finset (Fin (d + 1))) : (R2 x j2 J).FG := by
  let : Algebra K L := j2.toRingHom.toAlgebra
  let : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  have : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))
    rw [← IsScalarTower.algebraMap_apply ℂ F K c]
    exact (j2.commutes c).symm
  have : Module.Finite K L := hf
  have : FiniteDimensional F L := Module.Finite.trans K L
  let A := rA ℂ x J
  let B := (rB ℂ K x J).map j2
  let φ : A →+* B :=
    { toFun := fun a => ⟨algebraMap K L (algebraMap F K a),
        Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let : Algebra A B := φ.toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨c, hc, hb⟩ := Subalgebra.mem_map.1 b.2
    have h1 : IsIntegral A (algebraMap K L c) := IsIntegral.algebraMap hc
    have h2 : algebraMap B L b = algebraMap K L c := hb.symm
    rw [← h2] at h1
    exact (isIntegral_algebraMap_iff ).1 h1⟩
  have e : R2 x j2 J = rB ℂ L x J := by
    ext y
    constructor
    · intro hy
      exact isIntegral_trans (A := B) y hy
    · intro hy
      exact IsIntegral.tower_top (A := B) hy
  rw [e]
  exact fg_rB pd J

theorem rYFT_of :
    RYFT := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI
  have pd := h.covZ.pd
  have := h.covZ.fin
  have := h.covY.fin
  have h1 : (rB ℂ K' (xv x) I).FG := fg_rB h.covY.pd I
  have h2 : (R2 (xv x) j2 J).FG := integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J
  exact (Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)

end UpperTheory.Gal.productCup_of_system

end
