module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private def ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] (l : κ) (c : Finset κ → E) : Finset κ → E := fun L =>
  if l ∈ L then 0 else GlobalTheory.cubeSign (insert l L) l • c (insert l L)

private theorem wd_apply' {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (c : Finset κ → E) (t : Finset κ) : wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem wd_ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (l : κ) (c : Finset κ → E) (t : Finset κ) :
    wd w (ctrH l c) t + ctrH l (wd w c) t = w l (c t) := by
  by_cases hi : l ∈ t
  · have h0 : ctrH l (wd w c) t = 0 := ite_eq_left hi
    rw [h0, add_zero, wd_apply', Finset.sum_eq_single l]
    · have h1 : ctrH l c (t.erase l) = GlobalTheory.cubeSign t l • c t := by
        simp only [ctrH]
        rw [ite_eq_right (by simp), Finset.insert_erase hi]
      rw [h1, map_zsmul, smul_smul, GlobalTheory.cubeSign_mul_self, one_smul]
    · intro j _ hji
      have h1 : ctrH l c (t.erase j) = 0 := ite_eq_left (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
      rw [h1, map_zero, smul_zero]
    · intro h; exact absurd hi h
  · have h0 : ctrH l (wd w c) t = GlobalTheory.cubeSign (insert l t) l • wd w c (insert l t) := ite_eq_right hi
    rw [h0, wd_apply' w c (insert l t), Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul,
      GlobalTheory.cubeSign_mul_self, one_smul, Finset.smul_sum, wd_apply']
    have key : ∀ j ∈ t, GlobalTheory.cubeSign t j • w j (ctrH l c (t.erase j)) +
        GlobalTheory.cubeSign (insert l t) l • GlobalTheory.cubeSign (insert l t) j • w j (c ((insert l t).erase j)) = 0 := by
      intro j hj
      have hij : l ≠ j := fun h => hi (h ▸ hj)
      have h2 : ctrH l c (t.erase j) =
          GlobalTheory.cubeSign (insert l (t.erase j)) l • c (insert l (t.erase j)) :=
        ite_eq_right (fun h => hi (Finset.mem_of_mem_erase h))
      rw [h2, map_zsmul, ← Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
      have h1 := GlobalTheory.cubeSign_mul_erase (t := insert l t) (i := l) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := GlobalTheory.cubeSign_mul_self (insert l t) l
      have he := GlobalTheory.cubeSign_mul_self ((insert l t).erase j) l
      have : GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l +
          GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j = 0 := by
        linear_combination (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign ((insert l t).erase j) l) * h1
          - (GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l) * ha
          - (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.htpy_of :
    Htpy := by
  intro S E _ _ _ _ act κ _ _ R M r hS n c hc g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨hcC, hcD⟩ := Submodule.mem_inf.1 hc
  have hD : wd (fun l => act (r l)) c = 0 := hcD
  have hcC' : c ∈ Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n then M else ⊥) := hcC
  have hmem : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) :=
    fun s => (Submodule.mem_pi.1 hcC') s (Set.mem_univ _)
  have hcomm : ∀ (p q : S) (x : E), act p (act q x) = act q (act p x) := by
    intro p q x
    rw [← mul_apply_eq_comp, ← map_mul, mul_comm, map_mul, mul_apply_eq_comp]
  have hstep : ∀ l t, wd (fun l => act (r l)) (ctrH l c) t = act (r l) (c t) := by
    intro l t
    have := wd_ctrH (fun l => act (r l)) l c t
    rw [hD] at this
    have h0 : ctrH l (0 : Finset κ → E) t = 0 := by
      simp [ctrH]
    rw [h0, add_zero] at this
    exact this
  refine Submodule.mem_map.2 ⟨fun L => ∑ l, act (a l) (ctrH l c L), ?_, ?_⟩
  · have : (fun L => ∑ l, act (a l) (ctrH l c L)) ∈
        Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n - 1 then M else ⊥) := by
      refine Submodule.mem_pi.2 fun s _ => ?_
      by_cases hs : (s.card : ℤ) = n - 1
      · rw [ite_eq_left hs]
        refine Submodule.sum_mem _ fun l _ => hS _ (ha l) _ ?_
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := ite_eq_left hl
          rw [this]; exact M.zero_mem
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := ite_eq_right hl
          rw [h1]
          have h2 := hmem (insert l s)
          rw [ite_eq_left (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega)] at h2
          exact zsmul_mem h2 _
      · rw [ite_eq_right hs]
        refine (Submodule.mem_bot _).2 (Finset.sum_eq_zero fun l _ => ?_)
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := ite_eq_left hl
          rw [this, map_zero]
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := ite_eq_right hl
          have h2 := hmem (insert l s)
          rw [ite_eq_right (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega),
            Submodule.mem_bot] at h2
          rw [h1, h2, smul_zero, map_zero]
    exact this
  · show wd (fun l => act (r l)) _ = _
    funext t
    rw [wd_apply']

    simp only [map_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ i ∈ t, GlobalTheory.cubeSign t i • act (r i) (act (a l) (ctrH l c (t.erase i))) =
        act (a l) (act (r l) (c t)) := by
      intro l

      rw [← hstep l t, wd_apply', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, hcomm]
    rw [Finset.sum_congr rfl fun l _ => this l, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, mul_apply_eq_comp]
