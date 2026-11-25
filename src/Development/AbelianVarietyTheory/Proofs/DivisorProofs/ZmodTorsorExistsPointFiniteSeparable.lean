module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Unramified.Basic
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
public import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TorsorFieldPoint


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor (B D : Type) [CommRing B] [CommRing D]
    [Algebra B D] (q : ℕ) (hq : 0 < q) (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D))
    (h : _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act) : Algebra.FormallyUnramified B D := by
  obtain ⟨-, -, hff, hbij⟩ := h
  have : NeZero q := ⟨hq.ne'⟩
  let g : D →ₐ[B] (Multiplicative (ZMod q) → D) :=
    Pi.algHom B (fun _ ↦ D) fun σ ↦ (act σ : D →ₐ[B] D)
  let F : D ⊗[B] D →ₐ[D] (Multiplicative (ZMod q) → D) :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId D _) g
  have hF : (F : D ⊗[B] D → _) = Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ ↦ D) fun _ ↦ AlgHom.id B D) g := by
    ext x : 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all
  have hFb : Function.Bijective F := by rw [hF]; exact hbij
  have : Algebra.FormallyUnramified D (Multiplicative (ZMod q) → D) :=
    (Algebra.FormallyUnramified.pi_iff _).2 fun _ ↦ inferInstance
  have : Algebra.FormallyUnramified D (D ⊗[B] D) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofBijective F hFb).symm
  exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat D


open IsLocalRing Polynomial in
open scoped TensorProduct in
theorem _root_.GlobalTheory.TorsorFieldPoint.exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K]
    (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    _root_.GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  intro B K _ _ f D _ _ q hq act h
  have := _root_.GlobalTheory.TorsorFieldPoint.formallyUnramified_of_isZTorsor B D q hq act h
  obtain ⟨hfin, -, hff, -⟩ := h
  letI : Algebra B K := f.toAlgebra
  haveI : Nontrivial (K ⊗[B] D) := Module.FaithfullyFlat.rTensor_nontrivial B D K
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] D)
  letI : Field (K ⊗[B] D ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (K ⊗[B] D ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.FormallyUnramified K (K ⊗[B] D ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m) Ideal.Quotient.mk_surjective
  refine ⟨K ⊗[B] D ⧸ m, inferInstance, inferInstance, inferInstance,
    Algebra.FormallyUnramified.isSeparable K _,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext b
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

end GlobalTheory.TorsorFieldPoint
