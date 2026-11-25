module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RhoKApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem phiCond_quot {Γ : Type} [Group Γ] [TopologicalSpace Γ] (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : PhiCond Γ l) : PhiCond (Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  have := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc)
  let π : H.comap (QuotientGroup.mk' M) →* H := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtypeVal).subtype_mk _
  have hs : Function.Surjective π :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
    IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M)))}) (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ⟩) ?_
  intro φ φ' e
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem exists_univ_loc (hP : Loc.LocalPublishedTheorems) (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (η : GQ l →* ℤˣ) (Ψ : GQ l →* Oˣ)
    (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ)) : Nonempty (Univ (GCond.noCondition O η Ψ)) := by
  have : IsAdicComplete (maximalIdeal O) O := (dvrFacts l O).2.2.2.1
  have : IsLocalHom (algebraMap ℤ_[l] O) := (dvrFacts l O).2.2.1
  have : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have : CharP (ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue O), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] O)]
    refine map_nonunit _ _ ?_
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois _ _
  have : (Subgroup.normalClosure (∅ : Set (GQ l))).topologicalClosure.Normal :=
    Subgroup.is_normal_topologicalClosure _
  obtain ⟨U⟩ := exists_univ l η Ψ hη hΨ ∅ (fun g hg => hg.elim) _ rfl
    (phiCond_quot l _ fun H hH => Loc.phiCond hP l l H hH)
  refine ⟨{ R := U.R, r := U.r, rep := fun R' _ _ _ => ⟨fun _ => trivial, fun r' _ => ?_⟩ }⟩
  exact (U.rep R').2 r' fun g hg => hg.elim

theorem UpperTheory.V.U3.exists_uLoc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Nonempty (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι))) := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨-, -, -, hη, hΨ, -⟩ := dat_facts D
  exact exists_univ_loc hC.loc l c.O _ _ (hη.comp_continuous D.ι_cont) (hΨ.comp_continuous D.ι_cont)
