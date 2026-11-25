module

public import Formalism.HermitianCurvature.CapelliDeterminantAndBranching
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

section Int

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem ofFn_prod_int {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, mul_apply_eq_comp, mul_apply_eq_comp,
      h, ih (fun k => F k.succ) (fun k => F' k.succ) (fun k y => h k.succ y)]

theorem tm_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (a b : Fin n) (x : V) :
    f (Tm E u a b x) = Tm E' u a b (f x) := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply, hf]

theorem qminor_int {n t : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (a b : Fin t → Fin n) (u : ℂ) (x : V) :
    f (qminor E a b u x) = qminor E' a b u (f x) := by
  unfold qminor

  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, intCast_apply_eq_smul, intCast_apply_eq_smul, map_zsmul,
    ofFn_prod_int _ _ f (fun k y => tm_int f hf _ _ _ y)]

theorem qdet_int {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) :
    f (qdet E u x) = qdet E' u (f x) :=
  qminor_int f hf id id u x

end Int

section Restr

variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def resE (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) : Fin n → Fin n → Module.End ℂ S :=
  fun a b => (E a b).restrict (hS a b)

theorem resE_apply (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (hS : Stab E S) (a b : Fin n) (x : S) :
    ((resE E S hS a b x : S) : V) = E a b x := rfl

theorem glRel_resE {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (S : Submodule ℂ V) (hS : Stab E S) :
    GlRel (resE E S hS) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := LinearMap.congr_fun (hE a b c d) (x : V)
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp only [hbc, hda, ite_true, ite_false, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.zero_apply,
      Submodule.coe_sub, Submodule.coe_zero, sub_zero, zero_sub, resE_apply] at h ⊢ <;> exact h

theorem irr_resE {E : Fin n → Fin n → Module.End ℂ V} (S : Submodule ℂ V) (hS : Stab E S) (hne : S ≠ ⊥)
    (hirr : ∀ S' : Submodule ℂ V, S' ≤ S → Stab E S' → S' = ⊥ ∨ S' = S) : Irr (resE E S hS) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun T hT => ?_⟩
  have hinj := Submodule.map_injective_of_injective S.injective_subtype
  have hst : Stab E (T.map S.subtype) := by
    intro a b v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨resE E S hS a b x, hT a b x hx, rfl⟩
  rcases hirr (T.map S.subtype) (Submodule.map_subtype_le S T) hst with h | h
  · left
    exact hinj (h.trans (Submodule.map_bot _).symm)
  · right
    exact hinj (h.trans (Submodule.map_subtype_top S).symm)

theorem cap_resE {E : Fin n → Fin n → Module.End ℂ V} (m : Fin n → ℂ) (hS : Stab E (CapSp E m)) (w : ℂ)
    (x : CapSp E m) : qdet (resE E (CapSp E m) hS) w x = cpol m w • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  have := qdet_int (CapSp E m).subtype (E := resE E (CapSp E m) hS) (E' := E) (fun a b y => rfl) w x
  simp only [Submodule.subtype_apply] at this
  rw [this]
  exact mem_CapSp.1 x.2 w

end Restr

section Proj

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}

def projI (h : DirectSum.IsInternal S) (i : ι) : V →ₗ[ℂ] S i :=
  (DirectSum.component ℂ ι (fun j => S j) i).comp (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm.toLinearMap

omit [Fintype ι] [DecidableEq ι] S in
theorem projI_apply [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V} (h : DirectSum.IsInternal S) (i : ι) (v : V) :
    projI h i v = (LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h).symm v i := rfl

theorem projI_self (h : DirectSum.IsInternal S) {i : ι} (x : S i) : projI h i (x : V) = x := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_same h x

theorem projI_ne (h : DirectSum.IsInternal S) {i j : ι} (hij : j ≠ i) (x : S j) : projI h i (x : V) = 0 := by
  rw [projI_apply]
  exact DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne h hij x

theorem projI_sum (h : DirectSum.IsInternal S) (y : ∀ j, S j) (i : ι) : projI h i (∑ j, (y j : V)) = y i := by

  rw [map_sum, Finset.sum_eq_single i (fun j _ hj => projI_ne h hj (y j)) (fun hi => absurd (Finset.mem_univ i) hi)]
  exact projI_self h (y i)

theorem sum_projI (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h with he
  have h1 : DirectSum.coeLinearMap S (e.symm v) = v := e.apply_symm_apply v
  conv_rhs => rw [← h1, ← DirectSum.sum_univ_of (e.symm v)]

  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl

theorem projI_comm (h : DirectSum.IsInternal S) (T : Module.End ℂ V) (hT : ∀ j, ∀ v ∈ S j, T v ∈ S j) (i : ι) (v : V) :
    projI h i (T v) = T.restrict (hT i) (projI h i v) := by
  have e : T v = ∑ j, ((T.restrict (hT j) (projI h j v) : S j) : V) := by
    conv_lhs => rw [← sum_projI h v]

    rw [map_sum]
    rfl
  rw [e, projI_sum]

end Proj

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
