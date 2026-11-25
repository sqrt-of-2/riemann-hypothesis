module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Jacobson.Ideal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfBijectiveBaseChangeQuotientJacobson
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeIffIsBaseChange
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BCCancel

variable {R S T X Y : Type} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
  [IsScalarTower R S T] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

theorem cancel_comm (f : X →ₗ[R] Y) (z : T ⊗[S] (S ⊗[R] X)) :
    AlgebraTensorModule.cancelBaseChange R S T T Y ((f.baseChange S).lTensor T z) =
      f.baseChange T (AlgebraTensorModule.cancelBaseChange R S T T X z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x => simp [LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add (f := _), ha, hb]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem bij_up (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange S)) :
    Function.Bijective (f.baseChange T) := by
  have hl : Function.Bijective ((f.baseChange S).lTensor T) := by
    exact (LinearEquiv.lTensor T (LinearEquiv.ofBijective _ hf)).bijective
  have hfun : ⇑(f.baseChange T) = AlgebraTensorModule.cancelBaseChange R S T T Y ∘
      (f.baseChange S).lTensor T ∘ (AlgebraTensorModule.cancelBaseChange R S T T X).symm := by
    funext z
    simp only [Function.comp_apply, cancel_comm, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).bijective.comp
    (hl.comp (AlgebraTensorModule.cancelBaseChange R S T T X).symm.bijective)

theorem bij_down [Module.FaithfullyFlat S T] (f : X →ₗ[R] Y) (hf : Function.Bijective (f.baseChange T)) :
    Function.Bijective (f.baseChange S) := by
  rw [← Module.FaithfullyFlat.lTensor_bijective_iff_bijective S T]
  have hfun : ⇑((f.baseChange S).lTensor T) = (AlgebraTensorModule.cancelBaseChange R S T T Y).symm ∘
      f.baseChange T ∘ AlgebraTensorModule.cancelBaseChange R S T T X := by
    funext z
    simp only [Function.comp_apply, ← cancel_comm, LinearEquiv.symm_apply_apply]
  rw [hfun]
  exact (AlgebraTensorModule.cancelBaseChange R S T T Y).symm.bijective.comp
    (hf.comp (AlgebraTensorModule.cancelBaseChange R S T T X).bijective)

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP.BCCancel

theorem bij_lin {A B C N N' N'' : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    [Module B N'] [IsScalarTower A B N'] [AddCommGroup N''] [Module A N''] [Module B N''] [Module C N'']
    [IsScalarTower B C N''] [IsScalarTower A B N''] [IsScalarTower A C N'']
    (u : N →ₗ[A] N') (v : N' →ₗ[B] N'') (hv : IsBaseChange C v)
    (hw : IsBaseChange C ((v.restrictScalars A).comp u)) :
    Function.Bijective ((u.liftBaseChange B).baseChange C) := by
  set L := u.liftBaseChange B
  have h0 := TensorProduct.isBaseChange A N B
  have hc : IsBaseChange C ((v ∘ₗ L : B ⊗[A] N →ₗ[B] N'').restrictScalars A ∘ₗ TensorProduct.mk A B N 1) := by
    convert hw using 1
    ext x
    simp [L, LinearMap.liftBaseChange_tmul]
  have h1 : IsBaseChange C (v ∘ₗ L) := IsBaseChange.of_comp h0 hc
  have hfun : ⇑(L.baseChange C) = hv.equiv.symm ∘ h1.equiv := by
    funext z
    simp only [Function.comp_apply]
    rw [LinearEquiv.eq_symm_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c p => simp [IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [hfun]
  exact hv.equiv.symm.bijective.comp h1.equiv.bijective

end GlobalTheory.BSP.BCCancel

namespace GlobalTheory.BSP

theorem semiBC_of_cover : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h →
    ∀ (A : Type) [CommRing A] (k : A →+* B.A) (N : Type) [AddCommGroup N] [Module A N] [Module.Finite A N]
    [Module.Projective A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] [Module.Finite B.A N']
    [Module.Projective B.A N'] (N'' : Type) [AddCommGroup N''] [Module C.A N''] (u : N →ₛₗ[k] N')
    (v : N' →ₛₗ[h.f] N'') (w : N →ₛₗ[h.f.comp k] N''), (∀ x, w x = v (u x)) → SemiBC v → SemiBC w →
    SemiBC u := by
  intro l _ R _ B C h hc A _ k N _ _ _ _ N' _ _ _ _ N'' _ _ u v w hw hv hwb
  let : Algebra A B.A := k.toAlgebra
  let : Algebra B.A C.A := h.f.toAlgebra
  let : Algebra A C.A := (h.f.comp k).toAlgebra
  haveI : IsScalarTower A B.A C.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module A N' := Module.compHom N' k
  haveI : IsScalarTower A B.A N' := ⟨fun a b x => mul_smul (k a) b x⟩
  letI : Module B.A N'' := Module.compHom N'' h.f
  letI : Module A N'' := Module.compHom N'' (h.f.comp k)
  haveI : IsScalarTower B.A C.A N'' := ⟨fun a b x => mul_smul (h.f a) b x⟩
  haveI : IsScalarTower A C.A N'' := ⟨fun a b x => mul_smul (h.f (k a)) b x⟩
  haveI : IsScalarTower A B.A N'' := ⟨fun a b x => by
    show h.f (k a * b) • x = h.f (k a) • (h.f b • x)
    rw [map_mul, mul_smul]⟩
  let u' : N →ₗ[A] N' := { toFun := u, map_add' := u.map_add, map_smul' := fun a x => u.map_smulₛₗ a x }
  let v' : N' →ₗ[B.A] N'' := { toFun := v, map_add' := v.map_add, map_smul' := fun a x => v.map_smulₛₗ a x }
  let w' : N →ₗ[A] N'' := { toFun := w, map_add' := w.map_add, map_smul' := fun a x => w.map_smulₛₗ a x }
  have hv' : IsBaseChange C.A v' := (_root_.GlobalTheory.BSP.semiBC_iff_isBaseChange B.A C.A N' N'' v v' fun _ => rfl).1 hv
  have hw' : IsBaseChange C.A ((v'.restrictScalars A).comp u') := by
    have := (_root_.GlobalTheory.BSP.semiBC_iff_isBaseChange A C.A N N'' w w' fun _ => rfl).1 hwb
    convert this using 1
    ext x
    exact (hw x).symm
  set L := u'.liftBaseChange B.A
  have hC : Function.Bijective (L.baseChange C.A) := BCCancel.bij_lin u' v' hv' hw'
  letI : Algebra (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := (qmap h 1).toAlgebra
  haveI : IsScalarTower B.A (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.FaithfullyFlat (B.A ⧸ adI B ^ 1) (C.A ⧸ adI C ^ 1) := hc.ff 1
  have hQ : Function.Bijective (L.baseChange (C.A ⧸ adI C ^ 1)) := BCCancel.bij_up (S := C.A) L hC
  have hB : Function.Bijective (L.baseChange (B.A ⧸ adI B ^ 1)) :=
    BCCancel.bij_down (T := C.A ⧸ adI C ^ 1) L hQ
  haveI : IsAdicComplete (adI B) B.A := B.complete
  have hJ : adI B ^ 1 ≤ Ideal.jacobson ⊥ := (pow_one (adI B)).le.trans (IsAdicComplete.le_jacobson_bot (adI B))
  have hL : Function.Bijective L := _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient B.A (adI B ^ 1) hJ (B.A ⊗[A] N) N' L hB
  have hu' : IsBaseChange B.A u' :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective L hL) fun x => by
      simp [L, LinearMap.liftBaseChange_tmul]
  exact (_root_.GlobalTheory.BSP.semiBC_iff_isBaseChange A B.A N N' u u' fun _ => rfl).2 hu'

end GlobalTheory.BSP
