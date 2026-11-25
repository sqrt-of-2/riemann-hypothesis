module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShearMeasurability
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.USplit

def coords {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : UT r → ℂ := fun p => A p.1.1 p.1.2

theorem upper_of_lt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : a < b) : upper x a b = x ⟨(a, b), h⟩ := by
  unfold upper
  rw [dite_eq_left h]

theorem upper_diag {r : ℕ} (x : UT r → ℂ) (a : Fin r) : upper x a a = 1 := by
  unfold upper
  rw [dite_eq_right (lt_irrefl a), ite_eq_left rfl]

theorem upper_of_gt {r : ℕ} (x : UT r → ℂ) {a b : Fin r} (h : b < a) : upper x a b = 0 := by
  unfold upper
  rw [dite_eq_right (lt_asymm h), ite_eq_right (ne_of_gt h)]

theorem mul_apply_lt {r : ℕ} (x y : UT r → ℂ) {a b : Fin r} (h : a < b) :
    (upper x * upper y) a b = x ⟨(a, b), h⟩ + y ⟨(a, b), h⟩ +
      ∑ c, if a < c ∧ c < b then upper x a c * upper y c b else 0 := by
  rw [Matrix.mul_apply]
  have key : ∀ c, upper x a c * upper y c b =
      ((if c = a then y ⟨(a, b), h⟩ else 0) + (if c = b then x ⟨(a, b), h⟩ else 0)) +
        (if a < c ∧ c < b then upper x a c * upper y c b else 0) := by
    intro c
    rcases lt_trichotomy c a with hca | hca | hac
    · have hcb : c ≠ b := ne_of_lt (hca.trans h)
      rw [upper_of_gt x hca, zero_mul, ite_eq_right (ne_of_lt hca), ite_eq_right hcb,
        ite_eq_right (fun k => lt_asymm hca k.1)]
      simp
    · subst hca
      rw [upper_diag, one_mul, upper_of_lt y h, ite_eq_left rfl, ite_eq_right (ne_of_lt h),
        ite_eq_right (fun k => lt_irrefl _ k.1)]
      simp
    · rcases lt_trichotomy c b with hcb | hcb | hbc
      · rw [ite_eq_right (ne_of_gt hac), ite_eq_right (ne_of_lt hcb), ite_eq_left ⟨hac, hcb⟩]
        simp
      · subst hcb
        rw [upper_diag, mul_one, upper_of_lt x h, ite_eq_right (ne_of_gt h), ite_eq_left rfl,
          ite_eq_right (fun k => lt_irrefl _ k.2)]
        simp
      · rw [upper_of_gt y hbc, mul_zero, ite_eq_right (ne_of_gt hac), ite_eq_right (ne_of_gt hbc),
          ite_eq_right (fun k => lt_asymm hbc k.2)]
        simp
  rw [Finset.sum_congr rfl (fun c _ => key c), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem upper_coords_mul {r : ℕ} (x y : UT r → ℂ) : upper (coords (upper x * upper y)) = upper x * upper y := by
  ext a b
  rcases lt_trichotomy a b with hab | hab | hba
  · rw [upper_of_lt _ hab]
    rfl
  · subst hab
    rw [upper_diag, Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [upper_diag, upper_diag, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hlt | hgt
      · rw [upper_of_gt x hlt, zero_mul]
      · rw [upper_of_gt y hgt, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · rw [upper_of_gt _ hba, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rcases lt_or_ge c a with hca | hac
    · rw [upper_of_gt x hca, zero_mul]
    · rw [upper_of_gt y (lt_of_lt_of_le hba hac), mul_zero]

theorem continuous_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : a < b
  · simp only [upper, dite_eq_left h]
    exact continuous_apply _
  · simp only [upper, dite_eq_right h]
    exact continuous_const

theorem continuous_upperIn {r : ℕ} (β : Fin r → ℕ) : Continuous (upperIn β) := by
  have hg : Continuous fun (x : UTin β → ℂ) (p : UT r) =>
      if h : β p.1.1 = β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 = β p.1.2
    · simp only [dite_eq_left h]
      exact continuous_apply _
    · simp only [dite_eq_right h]
      exact continuous_const
  exact (continuous_upper r).comp hg

theorem continuous_upperOff {r : ℕ} (β : Fin r → ℕ) : Continuous (upperOff β) := by
  have hg : Continuous fun (x : UToff β → ℂ) (p : UT r) =>
      if h : β p.1.1 ≠ β p.1.2 then x ⟨p, h⟩ else 0 := by
    refine continuous_pi fun p => ?_
    by_cases h : β p.1.1 ≠ β p.1.2
    · simp only [dite_eq_left h]
      exact continuous_apply _
    · simp only [dite_eq_right h]
      exact continuous_const
  exact (continuous_upper r).comp hg

def prodMap {r : ℕ} (β : Fin r → ℕ) (u : UT r → ℂ) : UT r → ℂ :=
  coords (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1))

theorem continuous_prodMap {r : ℕ} (β : Fin r → ℕ) : Continuous (prodMap β) := by
  have h1 : Continuous fun u : UT r → ℂ => upperIn β (fun p => u p.1) :=
    (continuous_upperIn β).comp (continuous_pi fun p => continuous_apply _)
  have h2 : Continuous fun u : UT r → ℂ => upperOff β (fun p => u p.1) :=
    (continuous_upperOff β).comp (continuous_pi fun p => continuous_apply _)
  exact continuous_pi fun p => (h1.matrix_mul h2).matrix_elem p.1.1 p.1.2

private theorem shearCond_prodMap {r : ℕ} (β : Fin r → ℕ) :
    Formalism.FourierDecayAlt.P.ShearMeasurability.ShearCond (fun p : UT r => p.1.2.val - p.1.1.val) (prodMap β) := by
  intro q x y hxy
  obtain ⟨⟨a, b⟩, h⟩ := q
  have e : ∀ u : UT r → ℂ, prodMap β u ⟨(a, b), h⟩ - u ⟨(a, b), h⟩ = ∑ c, if a < c ∧ c < b then
      upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) a c *
      upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) c b else 0 := by
    intro u
    have hin : upperIn β (fun p => u p.1) = upper (fun p => if β p.1.1 = β p.1.2 then u p else 0) := by
      unfold upperIn
      congr 1
    have hoff : upperOff β (fun p => u p.1) =
        upper (fun p => if β p.1.1 ≠ β p.1.2 then u p else 0) := by
      unfold upperOff
      congr 1
    show (upperIn β (fun p => u p.1) * upperOff β (fun p => u p.1)) a b - _ = _
    rw [hin, hoff, mul_apply_lt _ _ h]
    by_cases hb : β a = β b
    · have hb' : ¬ β a ≠ β b := not_not.mpr hb
      simp only [ite_eq_left hb, ite_eq_right hb', add_zero, add_sub_cancel_left]
    · simp only [ite_eq_right hb, ite_eq_left hb, zero_add, add_sub_cancel_left]
  rw [e x, e y]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 : c.val - a.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    have h2 : b.val - c.val < b.val - a.val := by
      have := hc.1; have := hc.2; omega
    rw [upper_of_lt _ hc.1, upper_of_lt _ hc.2, upper_of_lt _ hc.1, upper_of_lt _ hc.2,
      hxy ⟨(a, c), hc.1⟩ h1, hxy ⟨(c, b), hc.2⟩ h2]
  · rfl

theorem prodMap_mp {r : ℕ} (β : Fin r → ℕ) : MeasurePreserving (prodMap β) volume volume := Formalism.FourierDecayAlt.P.ShearMeasurability.shear_mp _ (prodMap β) (continuous_prodMap β).measurable (shearCond_prodMap β)

theorem lebesgue_split : ∀ (r : ℕ) (β : Fin r → ℕ), Monotone β → (∀ (x : UTin β → ℂ) (y : UToff β → ℂ), ∃ u : UT r → ℂ, upper u = upperIn β x * upperOff β y) ∧ ∀ f : (Fin r → Fin r → ℂ) → ℝ≥0∞, Measurable f → ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u)) = ∫⁻ y : UToff β → ℂ, ∫⁻ x : UTin β → ℂ, f (Matrix.of.symm (upperIn β x * upperOff β y)) := by
  intro r β _
  refine ⟨fun x y => ⟨coords (upperIn β x * upperOff β y), ?_⟩, fun f hf => ?_⟩
  · unfold upperIn upperOff
    exact upper_coords_mul _ _
  · have hc : Continuous fun u : UT r → ℂ => (Matrix.of.symm (upper u) : Fin r → Fin r → ℂ) :=
      continuous_upper r
    have hu : Measurable fun u : UT r → ℂ => f (Matrix.of.symm (upper u)) := hf.comp hc.measurable
    have hM : Continuous fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        (Matrix.of.symm (upperIn β z.1 * upperOff β z.2) : Fin r → Fin r → ℂ) :=
      ((continuous_upperIn β).comp continuous_fst).matrix_mul ((continuous_upperOff β).comp continuous_snd)
    have hG : Measurable fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
        f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) := hf.comp hM.measurable
    have hsplit := MeasureTheory.volume_preserving_piEquivPiSubtypeProd (fun _ : UT r => ℂ)
      (fun p : UT r => β p.1.1 = β p.1.2)
    have key : ∀ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) =
        f (Matrix.of.symm (upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1))) := by
      intro v
      have hp : upper (prodMap β v) = upperIn β (fun p => v p.1) * upperOff β (fun p => v p.1) := by
        unfold prodMap upperIn upperOff
        exact upper_coords_mul _ _
      rw [hp]
    calc ∫⁻ u : UT r → ℂ, f (Matrix.of.symm (upper u))
        = ∫⁻ v : UT r → ℂ, f (Matrix.of.symm (upper (prodMap β v))) :=
          ((prodMap_mp β).lintegral_comp hu).symm
      _ = ∫⁻ v : UT r → ℂ, (fun z : (UTin β → ℂ) × (UToff β → ℂ) =>
            f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)))
            (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : UT r => ℂ)
              (fun p : UT r => β p.1.1 = β p.1.2) v) := lintegral_congr fun v => key v
      _ = ∫⁻ z : (UTin β → ℂ) × (UToff β → ℂ), f (Matrix.of.symm (upperIn β z.1 * upperOff β z.2)) :=
          hsplit.lintegral_comp hG
      _ = _ := lintegral_prod_symm _ hG.aemeasurable

end GlobalTheory.Amp.USplit
