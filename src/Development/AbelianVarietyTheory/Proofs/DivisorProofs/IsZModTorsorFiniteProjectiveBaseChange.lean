module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.LocAcyc

theorem isZModTorsor_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D]
    [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  intro B B' D _ _ _ _ _ q hq act hD
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have : NeZero q := ⟨hq.ne'⟩
  let act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)) :=
    { toFun := fun g => Algebra.TensorProduct.congr (AlgEquiv.refl : B' ≃ₐ[B'] B') (act g)
      map_one' := by
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext; intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b x => simp [Algebra.TensorProduct.congr_apply, AlgEquiv.mul_apply]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy] }
  have hact : ∀ (g : Multiplicative (ZMod q)) (b : B') (x : D),
      act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x := by
    intro g b x
    simp [act', Algebra.TensorProduct.congr_apply]
  refine ⟨act', hact, inferInstance, inferInstance, inferInstance, ?_⟩
  let Φ := Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))
  let e := (LinearEquiv.ofBijective Φ.toLinearMap h4).lTensor B'
  let dBC := TensorProduct.AlgebraTensorModule.distribBaseChange B B' D D
  let pR := TensorProduct.piRight B B' B' (fun _ : Multiplicative (ZMod q) => D)
  have key : ∀ z, (Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      (dBC z) = pR (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        funext g
        simp [dBC, pR, e, Φ, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, hact, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | add s t hs ht => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
    | add s t hs ht => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hs, ht]
  have hfun : ⇑(Algebra.TensorProduct.productMap
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun _ => AlgHom.id B' _))
      (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => B' ⊗[B] D) (fun g => (act' g).toAlgHom)))
      = fun w => pR (e (dBC.symm w)) := by
    funext w
    rw [← key, dBC.apply_symm_apply]
  rw [hfun]
  exact pR.bijective.comp (e.bijective.comp dBC.symm.bijective)

end GlobalTheory.LocAcyc
