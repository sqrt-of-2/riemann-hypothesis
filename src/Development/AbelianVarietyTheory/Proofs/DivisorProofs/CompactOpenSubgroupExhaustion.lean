module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology

namespace GlobalTheory.KSp.GoodSpace

open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel

theorem good_of_addEquiv {X Y : Type} [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y]
    (f : X ≃+ Y) (hf : Continuous f) (hg : Continuous f.symm) (h : Good Y) : Good X := by
  let H : X ≃ₜ Y := { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hg }
  have := h.grp; have := h.t2; have := h.lc; have := h.sc
  refine ⟨?_, H.isEmbedding.t2Space, H.isClosedEmbedding.locallyCompactSpace, H.isInducing.secondCountableTopology,
    ?_, ?_⟩
  · have : ContinuousAdd X := by
      refine ⟨?_⟩
      have : (fun p : X × X => p.1 + p.2) = fun p => f.symm (f p.1 + f p.2) := by
        funext p; simp
      rw [this]; exact hg.comp ((hf.comp continuous_fst).add (hf.comp continuous_snd))
    have : ContinuousNeg X := by
      refine ⟨?_⟩
      have : (fun x : X => -x) = fun x => f.symm (-f x) := by funext x; simp
      rw [this]; exact hg.comp hf.neg
    exact {}
  · intro K hK
    obtain ⟨L, hLc, hLo, hKL⟩ := h.large (f '' K) (hK.image hf)
    refine ⟨L.comap f.toAddMonoidHom, ?_, ?_, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · exact hLo.preimage hf
    · intro x hx; exact hKL ⟨x, hx, rfl⟩
  · intro U hU
    have hU' : f.symm ⁻¹' U ∈ 𝓝 (0 : Y) := by
      apply hg.continuousAt.preimage_mem_nhds; simpa using hU
    obtain ⟨L, hLc, hLo, hLU⟩ := h.small _ hU'
    refine ⟨L.comap f.toAddMonoidHom, ?_, hLo.preimage hf, ?_⟩
    · have : ((L.comap f.toAddMonoidHom : AddSubgroup X) : Set X) = H ⁻¹' (L : Set Y) := rfl
      rw [this]; exact H.isCompact_preimage.mpr hLc
    · intro x hx
      have := hLU hx
      simpa using this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def boxSub (n : Type) [Fintype n] [DecidableEq n] (s : Fˣ) : AddSubgroup (n → F) where
  carrier := box n s
  zero_mem' := fun i _ => by simp [cball]
  add_mem' := fun ha hb i _ => add_mem_cball (ha i trivial) (hb i trivial)
  neg_mem' := fun ha i _ => neg_mem_cball (ha i trivial)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem cball_mono [TopologicalSpace F] [IsNonarchimedeanLocalField F] {s t : Fˣ} (h : valuation F (s : F) ≤ valuation F (t : F)) : cball s ⊆ cball t :=
  fun x hx => show valuation F x ≤ valuation F (t : F) from le_trans hx h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_some_cball [TopologicalSpace F] [IsNonarchimedeanLocalField F] (y : F) : ∃ s : Fˣ, y ∈ cball s := by
  by_cases hy : y = 0
  · exact ⟨1, by simp [cball, hy]⟩
  · exact ⟨Units.mk0 y hy, by simp [cball]⟩

theorem mem_some_box (n : Type) [Fintype n] [DecidableEq n] (x : n → F) : ∃ s : Fˣ, x ∈ box n s := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i⟩
  · choose u hu using fun i => mem_some_cball (x i)
    obtain ⟨j, hj⟩ := Finite.exists_max fun i => valuation F (u i : F)
    exact ⟨u j, fun i _ => cball_mono (hj i) (hu i)⟩

theorem good_pi (n : Type) [Fintype n] [DecidableEq n] : Good (n → F) := by
  have := secondCountable F
  have := t2Space F
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro K hK
    obtain ⟨s, hs⟩ := hK.elim_directed_cover (fun s : Fˣ => box n s) (fun s => isOpen_box s)
      (fun x _ => Set.mem_iUnion.mpr (mem_some_box n x)) (by
        intro s t
        rcases le_total (valuation F (s : F)) (valuation F (t : F)) with h | h
        · exact ⟨t, fun x hx i _ => cball_mono h (hx i trivial), le_rfl⟩
        · exact ⟨s, le_rfl, fun x hx i _ => cball_mono h (hx i trivial)⟩)
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩
  · intro U hU
    obtain ⟨s, hs⟩ := exists_box_subset hU
    exact ⟨boxSub n s, isCompact_box s, isOpen_box s, hs⟩

end GlobalTheory.KSp.GoodSpace

theorem GlobalTheory.KSp.good_of_finiteDimensional : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V], Good V := by
  intro F _ _ _ _ _ V _ _ _ _ _
  have := IsModuleTopology.isTopologicalAddGroup F V
  let b := Module.finBasis F V
  let e := b.equivFun
  exact GlobalTheory.KSp.GoodSpace.good_of_addEquiv e.toAddEquiv
    (IsModuleTopology.continuous_of_linearMap (R := F) e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap (R := F) e.symm.toLinearMap)
    (GlobalTheory.KSp.GoodSpace.good_pi _)
