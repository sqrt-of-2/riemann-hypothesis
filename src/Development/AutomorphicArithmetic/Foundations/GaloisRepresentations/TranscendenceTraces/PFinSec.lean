module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : p.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg
  have : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _
  have : IsPurelyInseparable L (AlgebraicClosure L) :=
    IsPurelyInseparable.tower_top K L (AlgebraicClosure L)
  have hs : IsSeparable L r := Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)
  obtain ⟨x, rfl⟩ := IsPurelyInseparable.inseparable' r hs
  refine ⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨hH, hS⟩ := hO
  have := hH
  have := hT
  refine ⟨hT, ?_⟩
  have : IsLocalHom (algebraMap O T) := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal O := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)] at h1
    exact (Ideal.mem_comap.1 h1) ha⟩
  let : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra
  have : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨p, hp, h0⟩ := Algebra.IsIntegral.isIntegral (R := O) t
    refine IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp
        (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T) := rfl
    rw [h2, ← Polynomial.hom_eval₂, h0, map_zero]
  exact sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _

private theorem exists_ringHom (hS : SHSec) (B C T : Type) [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra.Etale B C] [Module.FaithfullyFlat B C] [Algebra B T] (hT : SH T) :
    ∃ f : C →+* T, ∀ b, f (algebraMap B C b) = algebraMap B T b := by
  obtain ⟨s⟩ := hS T (T ⊗[B] C) hT
  refine ⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩
  have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) =
      algebraMap T (T ⊗[B] C) (algebraMap B T b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]
  change s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _
  rw [h1]
  exact s.commutes _

end UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

open UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable in
theorem UpperTheory.Gal.TranscendenceTraces.finSec_of :
    SHSec → FinSec := by
  intro hS O B C _ _ _ _ _ _ _ _ hO
  obtain ⟨hH, -⟩ := id hO
  have := hH
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B
  have key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i := by
    intro i
    have := (hT i).2
    have hs := sh_of_finite O (T i) hO (hT i).1
    let : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra
    exact exists_ringHom hS B C (T i) hs
  choose f hf using key
  refine ⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (RingHom.pi f), commutes' := fun b => ?_ }⟩
  have h : RingHom.pi f (algebraMap B C b) = e b := funext fun i => hf i b
  change e.symm (RingHom.pi f (algebraMap B C b)) = b
  rw [h]
  exact e.symm_apply_apply b
