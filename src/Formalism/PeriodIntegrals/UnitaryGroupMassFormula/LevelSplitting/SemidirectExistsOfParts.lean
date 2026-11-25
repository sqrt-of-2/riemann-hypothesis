module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.UnitaryGroupSecondCountableT2
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace PI.LevelKSplit.W.ExS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.VolSemiDirect.W
open scoped TensorProduct

def SCAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], SecondCountableTopology (Af F)

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def SemiNHS : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    Semi (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

def ConjNH : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
    ConjInv (Nsub (Af F) σ J P) (Hsub (Af F) σ J P)

variable {F E σ M J}

theorem lcsc_HAf [FiniteDimensional F E] (hsc : SecondCountableTopology (Af F)) :
    LCSC (HA (Af F) σ J) := by
  have := hsc
  refine ⟨inferInstance, ?_, ?_, inferInstance⟩
  · have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
    let e := (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun
    have hc1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have hc2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : (Af F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Af F) := ⟨e.toEquiv, hc1, hc2⟩
    have : SecondCountableTopology (Af F ⊗[F] E) := h.secondCountableTopology
    have h4 : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin M → Fin M → Af F ⊗[F] E))
    have : SecondCountableTopology (Matrix (Fin M) (Fin M) (Af F ⊗[F] E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    have : SecondCountableTopology (GL (Fin M) (Af F ⊗[F] E)) :=
      Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
    show SecondCountableTopology ↥(HR (Af F) σ J)
    exact Topology.IsInducing.subtypeVal.secondCountableTopology
  · show T2Space ↥(HR (Af F) σ J)
    infer_instance

theorem existS_of [FiniteDimensional F E] (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x)
    (hPr : ProdHaarG) (hsc : SecondCountableTopology (Af F)) (hS : SemiNHS F E σ M J)
    (hCo : ConjNH F E σ M J) : ExistS F E σ M J := by
  intro r P T hP μN hN μH hH
  obtain ⟨hSc, hNc, hHc⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hinv P T hP
  obtain ⟨hLC, hSC, hT2, hTG⟩ := lcsc_HAf (σ := σ) (J := J) hsc
  have := hLC
  have := hSC
  have := hT2
  have := hTG
  have hsub : ∀ K : Subgroup (HA (Af F) σ J), IsClosed (K : Set (HA (Af F) σ J)) → LCSC K := by
    intro K hK
    refine ⟨?_, ?_, ?_, inferInstance⟩
    · first
        | exact hK.isClosedEmbedding_subtypeVal.locallyCompactSpace
    · first
        | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    · first
        | exact inferInstance
  obtain ⟨μS, hμS, hprod⟩ := hPr (HA (Af F) σ J) _ _ _ (hS hJ hinv r P T hP) (hsub _ hSc)
    (hsub _ hNc) (hsub _ hHc) (hCo hJ hinv r P T hP) μN hN μH hH
  exact ⟨μS, hμS, hprod⟩

end Ext

def SemiNHSAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => SemiNHS F E σ M J

def ConjNHAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ConjNH F E σ M J

theorem existSAll_of (hPr : ProdHaarG) (hsc : SCAf) (hS : SemiNHSAll) (hCo : ConjNHAll) :
    ExistSAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [hσ.2.2.2 τ (σ x), hσ.2.2.2 τ x, star_star]
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact existS_of hJ hinv hPr (hsc F) (hS F E σ hσ M J hJ) (hCo F E σ hσ M J hJ)

end PI.LevelKSplit.W.ExS
