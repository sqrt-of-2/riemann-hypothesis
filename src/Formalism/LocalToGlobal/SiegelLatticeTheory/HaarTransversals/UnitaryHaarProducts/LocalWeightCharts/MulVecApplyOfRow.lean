module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ColOfLeftInv

@[expose] public section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

noncomputable section

namespace WlocSk.UnitaryGroupBasics

variable {k r : ℕ}

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one, Pi.single_apply] at this
  exact this

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e := congrFun (congrFun hU' c) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c] at e
  · rw [conjTranspose_apply, hc c, ite_eq_left rfl, star_one, one_mul, hpk_mul_apply, hpk_row] at e
    have hs : sgn k r c ≠ 0 := by
      intro h0
      have := sgn_mul_self (k := k) (r := r) c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    by_cases hj : j = tau k r c
    · rw [ite_eq_left hj] at e
      rw [ite_eq_left hj.symm]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [ite_eq_right hj] at e
      rw [ite_eq_right (Ne.symm hj)]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro p _ hp
    rw [conjTranspose_apply, hc p, ite_eq_right hp, star_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  by_cases hcr : c.val < r
  · have e : eI k r ⟨c.val, hcr⟩ = c := Fin.ext rfl
    have := (hh.2.1 ⟨c.val, hcr⟩).1
    rw [e] at this
    exact col_of_fix this p
  · have ha : 2 * r + k - c.val < r := by omega
    have e : esI k r ⟨2 * r + k - c.val, ha⟩ = c := by
      apply Fin.ext
      simp only [esI]
      omega
    have := (hh.2.1 ⟨2 * r + k - c.val, ha⟩).2
    rw [e] at this
    exact col_of_fix this p

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  unfold tau
  simp only
  split_ifs
  omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have := row_of_fixed_col hh.1 (tau k r i) (uw_fixed_col hh _ (tau_out i hi)) j
  rw [tau_tau] at this
  exact this

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  have hu := isUnit_of_uh hh.1
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hh.1, fun a => ⟨fix _ (hh.2.1 a).1, fix _ (hh.2.1 a).2⟩, fix _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  refine ⟨uh_mul hh.1 hh'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).1, (hh.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).2, (hh.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hh'.2.2, hh.2.2]

theorem block_mul_col {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [hg q q hq (by omega), ite_eq_left rfl, mul_one]
  · intro p _ hpq
    by_cases hp : q.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p q hq hp, ite_eq_right hpq, mul_zero]
    · push Not at hp
      have hne : i ≠ p := by
        intro e
        subst e
        omega
      rw [hh.1 i p (by omega), ite_eq_right hne, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem conj_col {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') := by
  intro i j hj hi
  have term : ∀ q : Fin (2 * r + k + 1), (h * g) i q * h' q j = h i q * h' q j := by
    intro q
    by_cases h0 : h' q j = 0
    · rw [h0, mul_zero, mul_zero]
    · by_cases hjr : j.val < r
      · have hqj : q = j := by
          by_contra hne
          apply h0
          rw [hh'.1 q j (Or.inl hjr), ite_eq_right hne]
        subst hqj
        rw [block_mul_col hh hg i q hj hi]
      · have hqW : r ≤ q.val ∧ q.val ≤ r + k := by
          by_contra hc
          apply h0
          have hne : q ≠ j := by
            intro e
            subst e
            omega
          rw [hh'.2 q j (by omega), ite_eq_right hne]
        rw [block_mul_col hh hg i q hqW.2 (by omega)]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun q _ => term q), ← Matrix.mul_apply, hinv,
    Matrix.one_apply]

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrow, ite_eq_left rfl, one_mul]
  · intro p _ hp
    rw [hrow, ite_eq_right (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hcol, ite_eq_left rfl, mul_one]
  · intro q _ hq
    rw [hcol, ite_eq_right hq, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hrow, ite_eq_left rfl, one_mul]
  · intro p _ hp
    rw [hrow, ite_eq_right (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem ellA_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

theorem uw_conj_mem {z : Fin (2 * r + k + 1) → ℂ}
    {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : h⁻¹ * m * h ∈ Nset k r := by
  have hinv := uw_inv hh
  have hu := isUnit_of_uh hh.1
  have hm' := (nset_iff m).1 hm
  exact (nset_iff _).2 ⟨uh_mul (uh_mul hinv.1 hm'.1) hh.1,
    conj_col (uw_block hinv) (uw_block hh) (Matrix.nonsing_inv_mul _ hu) hm'.2⟩

theorem psiGen_conj (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h⁻¹ * m * h) = psiGen k r z c m := by
  have hinv := uw_inv hh
  unfold psiGen
  congr 4
  apply Finset.sum_congr rfl
  intro a _
  rw [ellA_conj z (uw_block hinv) (uw_block hh) hh.2.2 a]

end WlocSk.UnitaryGroupBasics
