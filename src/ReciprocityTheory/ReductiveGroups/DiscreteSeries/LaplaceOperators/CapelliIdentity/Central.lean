module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.CapelliCentralStatement
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.BasicCycleRangeLastCastSucc
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ColAnti
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.ProdOfFnUpdateEq

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

open ReciprocityTheory.ChartRestriction.DS

section Ring

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem capelliC_central (hE : GlRelR E) (x : ℂ) (a b : Fin n) : Commute (E a b) (capelliC E x) := by
  have h := cminor_comm E hE a b (id : Fin n → Fin n) id x
  simp only [id, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  by_cases hab : a = b
  · subst hab
    rw [show Function.update (id : Fin n → Fin n) a a = id from Function.update_eq_self a id, sub_self] at h
    exact sub_eq_zero.1 h
  · have h1 : cminor E (Function.update (id : Fin n → Fin n) b a) id x = 0 := by
      apply cminor_rows_not_inj
      intro hinj
      have : Function.update (id : Fin n → Fin n) b a b = Function.update (id : Fin n → Fin n) b a a := by
        simp [Function.update_of_ne hab]
      exact hab (hinj this).symm
    have h2 : cminor E id (Function.update (id : Fin n → Fin n) a b) x = 0 := by
      apply cminor_cols_not_inj E hE
      intro hinj
      have : Function.update (id : Fin n → Fin n) a b a = Function.update (id : Fin n → Fin n) a b b := by
        simp [Function.update_of_ne (Ne.symm hab)]
      exact hab (hinj this)
    rw [h1, h2, sub_self] at h
    exact sub_eq_zero.1 h

end Ring

section Module

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M)

theorem capEntry_apply_end (x : ℂ) (a b : Fin n) (v : M) :
    capEntry E x a b v = E a b v + if a = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem prod_ofFn_apply_highestWeight (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    ∀ (p : ℕ) (r c : Fin p → Fin n), Function.Injective r → (∀ j, (r j : ℕ) < p) →
      (∀ j, (c j : ℕ) = j) →
      (List.ofFn fun j : Fin p => capEntry E (x - ((j : ℕ) : ℂ)) (r j) (c j)).prod v =
        if (∀ j, (r j : ℕ) = j) then (∏ j : Fin p, (x + μ (c j) - ((j : ℕ) : ℂ))) • v else 0 := by
  intro p
  induction p with
  | zero =>
    intro r c _ _ _
    simp
  | succ p ih =>
    intro r c hr hrp hc
    rw [List.ofFn_succ', List.prod_concat, mul_apply_eq_comp]
    have hcl : (c (Fin.last p) : ℕ) = p := by rw [hc]; simp
    have hrl : (r (Fin.last p) : ℕ) ≤ p := by have := hrp (Fin.last p); omega
    rcases lt_or_eq_of_le hrl with hlt | heq
    · have hlt' : r (Fin.last p) < c (Fin.last p) := by
        rw [Fin.lt_def, hcl]; exact hlt
      rw [capEntry_apply_end, hup _ _ hlt', ite_eq_right (ne_of_lt hlt'), add_zero, map_zero]
      rw [ite_eq_right]
      intro hall
      have := hall (Fin.last p)
      simp only [Fin.val_last] at this
      omega
    · have heq' : r (Fin.last p) = c (Fin.last p) := Fin.ext (by rw [heq, hcl])
      rw [capEntry_apply_end, ite_eq_left heq', heq', hd, ← add_smul, map_smul]
      have hr' : Function.Injective (fun j : Fin p => r j.castSucc) :=
        hr.comp (Fin.castSucc_injective p)
      have hrp' : ∀ j : Fin p, (r j.castSucc : ℕ) < p := by
        intro j
        have h1 := hrp j.castSucc
        have h2 : r j.castSucc ≠ r (Fin.last p) := fun h => (Fin.castSucc_lt_last j).ne (hr h)
        have h3 : (r j.castSucc : ℕ) ≠ p := fun h => h2 (Fin.ext (by rw [h, heq]))
        omega
      have hc' : ∀ j : Fin p, (c j.castSucc : ℕ) = j := fun j => by rw [hc]; simp
      have key := ih (fun j => r j.castSucc) (fun j => c j.castSucc) hr' hrp' hc'
      simp only [Fin.val_castSucc] at key ⊢
      rw [key]
      have hiff : (∀ j : Fin (p + 1), (r j : ℕ) = j) ↔ (∀ j : Fin p, (r j.castSucc : ℕ) = j) := by
        constructor
        · intro h j; simpa using h j.castSucc
        · intro h j
          rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
          · simpa using h i
          · simpa using heq
      by_cases hall : ∀ j : Fin p, (r j.castSucc : ℕ) = j
      · rw [ite_eq_left hall, ite_eq_left (hiff.2 hall), smul_smul, Fin.prod_univ_castSucc]
        congr 1
        simp only [Fin.val_castSucc, Fin.val_last]
        ring
      · rw [ite_eq_right hall, ite_eq_right (fun h => hall (hiff.1 h)), smul_zero]

theorem capelliC_hw (μ : Fin n → ℂ) (v : M) (x : ℂ) (hup : ∀ a b, a < b → E a b v = 0)
    (hd : ∀ a, E a a v = μ a • v) :
    capelliC E x v = (∏ a : Fin n, (x + μ a - ((a : ℕ) : ℂ))) • v := by
  unfold capelliC cminor
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => (1 : Equiv.Perm (Fin n)) j) id
      (Equiv.injective _) (fun j => by simp) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, ite_eq_left (fun j => by simp)]
    simp
  · intro σ _ hσ
    rw [LinearMap.smul_apply]
    have := prod_ofFn_apply_highestWeight E μ v x hup hd n (fun j => σ j) id
      (Equiv.injective _) (fun j => (σ j).2) (fun j => rfl)
    simp only [id] at this ⊢
    rw [this, ite_eq_right, smul_zero]
    intro hall
    apply hσ
    ext j
    simpa using hall j
  · intro h; exact absurd (Finset.mem_univ _) h

theorem capelliC_genSub (hE : IsGlRep E) (μ : Fin n → ℝ) (v : M) (hv : IsHWVec E μ v) (x : ℂ) :
    ∀ y ∈ genSub E (Submodule.span ℂ {v}),
      capelliC E x y = (∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ))) • y := by
  have hE' : GlRelR E := (isGlRep_iff_glRelR E).1 hE
  set c : ℂ := ∏ a : Fin n, (x + (μ a : ℂ) - ((a : ℕ) : ℂ)) with hc
  have hv' : capelliC E x v = c • v :=
    capelliC_hw E (fun a => (μ a : ℂ)) v x hv.2 hv.1
  let T : Submodule ℂ M := LinearMap.ker (capelliC E x - c • (1 : Module.End ℂ M))
  have hmem : ∀ w, w ∈ T ↔ capelliC E x w = c • w := by
    intro w
    simp only [T, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, one_apply_eq_self,
      sub_eq_zero]
  have hle : genSub E (Submodule.span ℂ {v}) ≤ T := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact (hmem v).2 hv'
    · intro a b w hw
      rw [hmem] at hw ⊢
      have hcomm := congrArg (fun f : Module.End ℂ M => f w) (capelliC_central E hE' x a b).eq
      simp only [mul_apply_eq_comp] at hcomm
      rw [← hcomm, hw, map_smul]
  intro y hy
  exact (hmem y).1 (hle hy)

end Module

end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
