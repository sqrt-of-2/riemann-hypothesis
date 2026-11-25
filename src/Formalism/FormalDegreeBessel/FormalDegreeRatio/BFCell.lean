module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BigCellMemUnitary
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

namespace BruhatBigCell

open GBasic

variable {k r : ℕ}

lemma hpk_mul_apply' (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (p j : Fin (2 * r + k + 1)) : (Hpk k r * A) p j = sgn k r p * A (sig k r p) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (sig k r p)]
  · rw [Hpk_eq, ite_eq_left rfl]
  · intro q _ hq; rw [Hpk_eq, ite_eq_right hq, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = sgn k r p * v (sig k r p) := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (sig k r p)]
  · rw [Hpk_eq, ite_eq_left rfl]
  · intro q _ hq; rw [Hpk_eq, ite_eq_right hq, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sgn_of_ne (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : sgn k r p = 1 := by
  unfold sgn; rw [ite_eq_right h]

variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

lemma col_lo (i j : Fin (2 * r + k + 1)) (a : Fin r) (hj : j.val = a.val) :
    bigCell k r c μ i j = if i.val = 2 * r + k - a.val then c a else 0 := by
  have hj' : j.val < r := by omega
  have ha : (⟨j.val, hj'⟩ : Fin r) = a := Fin.ext hj
  unfold bigCell
  rw [dite_eq_left hj', ha]
  simp only [esI, Fin.ext_iff]

lemma col_hi (i j : Fin (2 * r + k + 1)) (a : Fin r) (hj : j.val = 2 * r + k - a.val) :
    bigCell k r c μ i j = if i.val = a.val then (star (c a))⁻¹ else 0 := by
  have ha := a.isLt
  unfold bigCell
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = a := Fin.ext (by simp only; omega)
  rw [e]
  have e2 : (i.val = 2 * r + k - j.val) ↔ i.val = a.val := by omega
  simp only [e2]

lemma col_mid (i j : Fin (2 * r + k + 1)) (h1 : r ≤ j.val) (h2 : j.val ≤ r + k) :
    bigCell k r c μ i j = if hi : r ≤ i.val ∧ i.val ≤ r + k then
      μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0 := by
  unfold bigCell
  rw [dite_eq_right (by omega), dite_eq_left h2]

lemma row_lo (p j : Fin (2 * r + k + 1)) (a : Fin r) (hp : p.val = a.val) :
    bigCell k r c μ p j = if j.val = 2 * r + k - a.val then (star (c a))⁻¹ else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  by_cases h1 : j.val < r
  · rw [col_lo c μ p j ⟨j.val, h1⟩ rfl, ite_eq_right (by simp only; omega), ite_eq_right (by omega)]
  · by_cases h2 : j.val ≤ r + k
    · rw [col_mid c μ p j (by omega) h2, dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega)]
      by_cases h3 : j.val = 2 * r + k - a.val
      · have e : (⟨2 * r + k - j.val, by omega⟩ : Fin r) = a := Fin.ext (by simp only; omega)
        rw [ite_eq_left (by simp only; omega), ite_eq_left h3, e]
      · rw [ite_eq_right (by simp only; omega), ite_eq_right h3]

lemma row_hi (p j : Fin (2 * r + k + 1)) (a : Fin r) (hp : p.val = 2 * r + k - a.val) :
    bigCell k r c μ p j = if j.val = a.val then c a else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  by_cases h1 : j.val < r
  · rw [col_lo c μ p j ⟨j.val, h1⟩ rfl]
    by_cases h3 : j.val = a.val
    · have e : (⟨j.val, h1⟩ : Fin r) = a := Fin.ext h3
      rw [ite_eq_left (by simp only; omega), ite_eq_left h3, e]
    · rw [ite_eq_right (by simp only; omega), ite_eq_right h3]
  · by_cases h2 : j.val ≤ r + k
    · rw [col_mid c μ p j (by omega) h2, dite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega),
        ite_eq_right (by simp only; omega), ite_eq_right (by omega)]

lemma row_mid_out (p j : Fin (2 * r + k + 1)) (h1 : r ≤ p.val) (h2 : p.val ≤ r + k)
    (hj : j.val < r ∨ r + k < j.val) : bigCell k r c μ p j = 0 := by
  have hj' := j.isLt
  rcases hj with hj | hj
  · rw [col_lo c μ p j ⟨j.val, hj⟩ rfl, ite_eq_right (by simp only; omega)]
  · rw [col_hi c μ p j ⟨2 * r + k - j.val, by omega⟩ (by simp only; omega),
      ite_eq_right (by simp only; omega)]

lemma mid_mid (p q : Fin (k + 1)) : bigCell k r c μ (wI k r p) (wI k r q) = μ p q := by
  have hp := p.isLt
  have hq := q.isLt
  rw [col_mid c μ _ _ (by simp [wI]) (by simp only [wI]; omega),
    dite_eq_left ⟨by simp [wI], by simp only [wI]; omega⟩]
  congr 1 <;> apply Fin.ext <;> simp [wI]

lemma sum_mid (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) → f p = 0) :
    ∑ p, f p = ∑ q : Fin (k + 1), f (wI k r q) := by
  have emb : Function.Injective (wI k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp only [wI] at this; omega
  have hm : ∑ q : Fin (k + 1), f (wI k r q) = ∑ x ∈ Finset.univ.map ⟨wI k r, emb⟩, f x := by
    rw [Finset.sum_map]; rfl
  rw [hm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  by_contra hlt
  push Not at hlt
  exact hp (Finset.mem_map.2 ⟨⟨p.val - r, by omega⟩, Finset.mem_univ _,
    Fin.ext (by show r + (p.val - r) = p.val; omega)⟩)

end BruhatBigCell

open GBasic BruhatBigCell in
theorem big_cell_mem_holds : BigCellMem := by
  apply GlobalTheory.bigCell_mem_unitary

namespace BruhatBigCell

open GBasic

lemma star_bvec_dot {m : ℕ} (e : Fin m) (w : Fin m → ℂ) : star (bvec e) ⬝ᵥ w = w e := by
  rw [dotProduct, Finset.sum_eq_single e]
  · simp [bvec]
  · intro p _ hp; simp [bvec, hp]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mulVec_bvec {k r : ℕ} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (e i : Fin (2 * r + k + 1)) : (M *ᵥ bvec e) i = M i e := by
  simp [mulVec, dotProduct, bvec, Pi.single_apply]

lemma dmin_diag {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : Fin (r + 1) → ℂ)
    (hZ : Zhat k r z z' g = diagonal d) (l : Fin (r + 2)) :
    Dmin k r z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Dmin
  rw [hZ, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
  rfl

end BruhatBigCell

open GBasic BruhatBigCell in
theorem big_cell_coordinate_holds : BigCellZhat := by
  intro k r z z' c μ hz hz'
  ext a b
  show herm (Hpk k r) (bigCell k r c μ *ᵥ fvec k r z' b) (fvec k r z a) = _
  rw [diagonal_apply]
  have ha := a.isLt
  have hb := b.isLt
  by_cases hb1 : b.val < r
  · set bb : Fin r := ⟨b.val, hb1⟩
    have hf : fvec k r z' b = bvec (eI k r bb) := by unfold fvec; rw [dite_eq_left hb1]
    rw [hf]
    have hw : ∀ p, (Hpk k r *ᵥ (bigCell k r c μ *ᵥ bvec (eI k r bb))) p =
        if p = eI k r bb then c bb else 0 := by
      intro p
      rw [hpk_mulVec_apply, mulVec_bvec, col_lo c μ _ _ bb rfl]
      by_cases hp : p = eI k r bb
      · subst hp
        rw [ite_eq_left rfl, sgn_of_ne _ (by simp only [eI, bb]; omega),
          ite_eq_left (by rw [sig_lo _ _ _ (by simp [eI])]; simp [eI]), one_mul]
      · rw [ite_eq_right hp, ite_eq_right, mul_zero]
        intro h; apply hp; apply Fin.ext
        have h' : (sig k r p).val = 2 * r + k - b.val := h
        have := sig_val k r p
        show p.val = b.val
        split_ifs at this <;> omega
    rw [herm, dotProduct]
    simp only [hw, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Pi.star_apply, fvec_apply_lt z hz a (eI k r bb) (by show b.val < r; exact hb1)]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left (by simp [eI, bb]), dite_eq_left hb1]
      simp only [star_one, one_mul]
      rfl
    · rw [ite_eq_right hab, ite_eq_right (by simp only [eI, bb]; intro h; exact hab (Fin.ext h)), star_zero, zero_mul]
  · have hbr : b.val = r := by omega
    have hf : fvec k r z' b = z' := by unfold fvec; rw [dite_eq_right hb1]
    rw [hf]
    by_cases ha1 : a.val < r
    · set aa : Fin r := ⟨a.val, ha1⟩
      have hfa : fvec k r z a = bvec (eI k r aa) := by unfold fvec; rw [dite_eq_left ha1]
      rw [hfa, ite_eq_right (by intro h; rw [h] at ha1; exact hb1 ha1)]
      rw [herm, star_bvec_dot, hpk_mulVec_apply, sgn_of_ne _ (by simp only [eI, aa]; omega), one_mul, mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro q _
      have hs : (sig k r (eI k r aa)).val = 2 * r + k - aa.val := by
        rw [sig_lo _ _ _ (by show a.val < r; exact ha1)]; simp [eI]
      rw [row_hi c μ _ _ aa hs]
      by_cases hq : q.val = aa.val
      · rw [hz' q (Or.inl (by simp only [aa] at hq; omega)), mul_zero]
      · rw [ite_eq_right hq, zero_mul]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      have hfa : fvec k r z a = z := by unfold fvec; rw [dite_eq_right ha1]
      rw [hfa, ite_eq_left rfl, dite_eq_right ha1]

open GBasic BruhatBigCell in
theorem big_cell_minors_holds : BigCellMinors := by
  intro k r z z' c μ hz hz'
  have hZ := big_cell_coordinate_holds k r z z' c μ hz hz'
  set d : Fin (r + 1) → ℂ := fun a => if h : a.val < r then c ⟨a.val, h⟩ else
    herm (Hpk k r) (bigCell k r c μ *ᵥ z') z with hd
  have hD := dmin_diag z z' (bigCell k r c μ) d hZ
  have hlo : ∀ (x : Fin (r + 1)) (hx : x.val < r), d x = c ⟨x.val, hx⟩ := by
    intro x hx; simp only [hd]; rw [dite_eq_left hx]
  have part1 : ∀ l : Fin (r + 1), Dmin k r z z' (bigCell k r c μ) ⟨l.val, by omega⟩ =
      ∏ a : Fin r with a.val < l.val, c a := by
    intro l
    rw [hD]
    have hl : l.val ≤ r := by omega
    have hs : (Finset.univ.filter fun a : Fin r => a.val < l.val) =
        Finset.univ.map (Fin.castLEEmb hl) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb]
      constructor
      · intro h; exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
      · rintro ⟨i, hi⟩; rw [← hi]; exact i.isLt
    rw [hs, Finset.prod_map]
    apply Finset.prod_congr rfl
    intro i _
    rw [hlo _ (by simp only [Fin.val_castLE]; omega)]
    rfl
  refine ⟨part1, ?_, ?_⟩
  · intro hc a
    unfold cmin
    have e1 := part1 ⟨a.val + 1, by omega⟩
    have e2 := part1 ⟨a.val, by omega⟩
    simp only at e1 e2
    rw [e1, e2]
    have hs : (Finset.univ.filter fun b : Fin r => b.val < a.val + 1) =
        insert a (Finset.univ.filter fun b : Fin r => b.val < a.val) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hP : (∏ b : Fin r with b.val < a.val, c b) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun b _ => hc b)
    rw [hs, Finset.prod_insert (by simp), mul_div_assoc, div_self hP, mul_one]
  · intro hc
    unfold zeta
    rw [hD, hD]
    show (∏ i : Fin (r + 1), d (Fin.castLE _ i)) / (∏ i : Fin r, d (Fin.castLE _ i)) = _
    rw [Fin.prod_univ_castSucc]
    have e1 : ∀ i : Fin r, d (Fin.castLE (le_refl (r + 1)) (Fin.castSucc i)) = c i := by
      intro i; rw [hlo _ (by simp)]; rfl
    have e2 : ∀ i : Fin r, d (Fin.castLE (Nat.le_succ r) i) = c i := by
      intro i; rw [hlo _ (by simp)]; rfl
    have e3 : d (Fin.castLE (le_refl (r + 1)) (Fin.last r)) =
        herm (Hpk k r) (bigCell k r c μ *ᵥ z') z := by
      simp only [hd]; rw [dite_eq_right (by simp)]
    simp only [e1, e2, e3]
    have hP : (∏ i : Fin r, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun b _ => hc b)
    rw [mul_comm, mul_div_assoc, div_self hP, mul_one]

end Formalism.QuantumDeterminants
