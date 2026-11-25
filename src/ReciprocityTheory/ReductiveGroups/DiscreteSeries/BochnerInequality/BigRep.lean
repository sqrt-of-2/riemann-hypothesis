module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section BigRepA
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

omit [NormedAddCommGroup M] [InnerProductSpace ℂ M] in
theorem big_ext [NormedAddCommGroup M] [InnerProductSpace ℂ M] {k : ℕ} {F G : Big n k M} (h : ∀ κ, F κ = G κ) : F = G := by
  exact PiLp.ext h

theorem mAct_apply (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) (a b : Fin n) (F : Big n k M) (κ) :
    (mAct E k a b F) κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (factorAd (M := M) k i a b F) κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  change ((if (κ i).1 = a then coord k (Function.update κ i (b, (κ i).2)) else 0) -
      (if (κ i).2 = b then coord k (Function.update κ i ((κ i).1, a)) else 0) :
      Big n k M →ₗ[ℂ] M) F = _
  rw [LinearMap.sub_apply]
  split_ifs <;> rfl

theorem commutator_add_sum_eq {R : Type*} [Ring R] {k : ℕ} (m m' : R) (s s' : Fin k → R)
    (h1 : ∀ j, m * s' j = s' j * m) (h2 : ∀ i, s i * m' = m' * s i)
    (h3 : ∀ i j, i ≠ j → s i * s' j = s' j * s i) :
    (m + ∑ i, s i) * (m' + ∑ j, s' j) - (m' + ∑ j, s' j) * (m + ∑ i, s i) =
      (m * m' - m' * m) + ∑ i, (s i * s' i - s' i * s i) := by
  simp only [add_mul, mul_add, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have e1 : ∑ j, m * s' j = ∑ j, s' j * m := Finset.sum_congr rfl fun j _ => h1 j
  have e2 : ∑ i, s i * m' = ∑ i, m' * s i := Finset.sum_congr rfl fun i _ => h2 i
  have e3 : ∑ x, ∑ i, s i * s' x - ∑ x, ∑ i, s' i * s x = ∑ i, (s i * s' i - s' i * s i) := by
    rw [Finset.sum_comm (f := fun x i => s' i * s x), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_single x (fun i _ hix => sub_eq_zero.2 (h3 i x hix)) (by simp)
  rw [e1, e2, ← e3]
  abel

variable {E : Fin n → Fin n → Module.End ℂ M}

theorem mAct_rel (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    mAct E k a b * mAct E k c d - mAct E k c d * mAct E k a b =
      (if b = c then mAct E k a d else 0) - (if d = a then mAct E k c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  have h := LinearMap.congr_fun (hE a b c d) (F κ)
  clear hE
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
    simp_all [mAct_apply, PiLp.sub_apply]

theorem mAct_factorAd_comm (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    mAct E k a b * factorAd k i c d = factorAd k i c d * mAct E k a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [mul_apply_eq_comp, mAct_apply, factorAd_apply]
  split_ifs <;> simp [map_sub]

theorem factorAd_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k j c d = factorAd k j c d * factorAd k i a b := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  simp only [mul_apply_eq_comp, factorAd_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Function.update_comm hij.symm]
  split_ifs <;> abel

theorem factorAd_commutator (k : ℕ) (i : Fin k) (a b c d : Fin n) :
    factorAd (M := M) k i a b * factorAd k i c d - factorAd k i c d * factorAd k i a b =
      (if b = c then factorAd k i a d else 0) - (if d = a then factorAd k i c b else 0) := by
  apply LinearMap.ext
  intro F
  apply big_ext
  intro κ
  by_cases hbc : b = c <;> by_cases hda : d = a <;>
  simp only [hbc, hda, ite_true, ite_false, LinearMap.sub_apply, LinearMap.zero_apply,
    mul_apply_eq_comp, PiLp.sub_apply, PiLp.zero_apply, factorAd_apply, Function.update_self,
    Function.update_idem] <;>
  generalize κ i = p <;>
  obtain ⟨p1, p2⟩ := p <;>
  simp only <;>
  split_ifs <;> subst_vars <;> first | rfl | abel1 | (simp_all)

end BigRepA
section BigRepB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem bAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    (bAct E k a b F) κ = E a b (F κ) + ∑ i, (factorAd k i a b F) κ := by
  show coord k κ ((mAct E k a b + ∑ i, factorAd k i a b : Module.End ℂ (Big n k M)) F) =
    E a b (F κ) + ∑ i, coord k κ (factorAd k i a b F)

  rw [LinearMap.add_apply, map_add (f := _), LinearMap.sum_apply, map_sum]
  rfl

def swFst {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2))
    (fun κ => by simp [Function.update_idem])

def swSnd {k : ℕ} (i : Fin k) (a b : Fin n) : Equiv.Perm (Fin k → Fin n × Fin n) :=
  Function.Involutive.toPerm (fun κ => Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2))
    (fun κ => by simp [Function.update_idem])

theorem swFst_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swFst i a b κ = Function.update κ i (Equiv.swap a b (κ i).1, (κ i).2) := rfl

theorem swSnd_apply {k : ℕ} (i : Fin k) (a b : Fin n) (κ : Fin k → Fin n × Fin n) :
    swSnd i a b κ = Function.update κ i ((κ i).1, Equiv.swap a b (κ i).2) := rfl

theorem factorAd_adjoint (k : ℕ) (i : Fin k) (a b : Fin n) (F G : Big n k M) :
    inner ℂ (factorAd k i a b F) G = inner ℂ F (factorAd k i b a G) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [factorAd_apply, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
  congr 1
  · rw [← Equiv.sum_comp (swFst i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swFst_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).1 = b
    · have hκ : Function.update κ i (b, (κ i).2) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [ite_eq_left (by rw [h, Equiv.swap_apply_right]), ite_eq_left h, hκ, h, Equiv.swap_apply_right]
    · have h' : Equiv.swap a b (κ i).1 ≠ a := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      rw [ite_eq_right h', ite_eq_right h, inner_zero_left, inner_zero_right]
  · rw [← Equiv.sum_comp (swSnd i a b)]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [swSnd_apply]
    simp only [Function.update_self, Function.update_idem]
    by_cases h : (κ i).2 = a
    · have hκ : Function.update κ i ((κ i).1, a) = κ := by
        conv_rhs => rw [← Function.update_eq_self i κ]
        rw [← h]
      rw [ite_eq_left (by rw [h, Equiv.swap_apply_left]), ite_eq_left h, hκ, h, Equiv.swap_apply_left]
    · have h' : Equiv.swap a b (κ i).2 ≠ b := by
        rwa [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
      rw [ite_eq_right h', ite_eq_right h, inner_zero_left, inner_zero_right]

theorem mem_ncV_iff {k : ℕ} (F : Big n k M) :
    F ∈ ncV ε V k ↔ ∀ κ : Fin k → Fin n × Fin n,
      F κ ∈ (if ∀ i, ε (κ i).1 ≠ ε (κ i).2 then V else ⊥) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  exact Iff.rfl

theorem ncV_mem {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) (κ : Fin k → Fin n × Fin n) :
    F κ ∈ V := by
  have h := (mem_ncV_iff F).1 hF κ
  split_ifs at h
  · exact h
  · rw [(Submodule.mem_bot ℂ).1 h]
    exact V.zero_mem

theorem ncV_eq_zero {k : ℕ} {F : Big n k M} (hF : F ∈ ncV ε V k) {κ : Fin k → Fin n × Fin n}
    (j : Fin k) (hj : ε (κ j).1 = ε (κ j).2) : F κ = 0 := by
  have h := (mem_ncV_iff F).1 hF κ
  rw [ite_eq_right (fun hc => hc j hj)] at h
  exact (Submodule.mem_bot ℂ).1 h

end BigRepB
section BigRep

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem bAct_isGlRep (hE : IsGlRep E) (k : ℕ) : IsGlRep (bAct E k) := by
  intro a b c d
  simp only [bAct]
  rw [commutator_add_sum_eq _ _ _ _ (fun j => mAct_factorAd_comm k j a b c d)
    (fun i => (mAct_factorAd_comm k i c d a b).symm) (fun i j hij => factorAd_comm_of_ne k hij a b c d),
    mAct_rel hE]
  simp only [factorAd_commutator]
  by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, Finset.sum_sub_distrib] <;> abel

theorem bAct_isKUnitary (hU : IsInfUnitary ε E) (k : ℕ) : IsKUnitary ε (bAct E k) := by
  intro a b hab F G
  simp only [bAct, LinearMap.add_apply, LinearMap.sum_apply, inner_add_left, inner_add_right,
    sum_inner, inner_sum, factorAd_adjoint]
  congr 1
  simp [PiLp.inner_apply, mAct_apply, hU a b, adjSign, ite_eq_left hab]

theorem ncV_kStable (hV : IsKStableSub ε E V) (k : ℕ) :
    IsKStableSub ε (bAct E k) (ncV ε V k) := by
  intro a b hab F hF
  rw [mem_ncV_iff]
  intro κ
  rw [bAct_apply]
  split_ifs with hc
  · refine add_mem (hV a b hab _ (ncV_mem hF κ)) (Submodule.sum_mem _ fun i _ => ?_)
    rw [factorAd_apply]
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs <;>
      first | exact ncV_mem hF _ | exact Submodule.zero_mem _
  · push Not at hc
    obtain ⟨j, hj⟩ := hc
    rw [Submodule.mem_bot, ncV_eq_zero hF j hj, map_zero, zero_add]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [factorAd_apply]
    have hzero : ∀ (x : Fin n × Fin n), (i = j → ε x.1 = ε x.2) →
        F (Function.update κ i x) = 0 := by
      intro x hx
      apply ncV_eq_zero hF j
      by_cases hij : i = j
      · rw [hij]
        simpa [Function.update_self] using hx hij
      · rwa [Function.update_of_ne (Ne.symm hij)]
    have z1 : (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) = 0 := by
      split_ifs with h1
      · refine hzero _ ?_
        intro hij
        simpa [← hij, h1, hab] using hj
      · rfl
    have z2 : (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) = 0 := by
      split_ifs with h2
      · refine hzero _ ?_
        intro hij
        simpa [← hij, h2, hab] using hj
      · rfl
    rw [z1, z2, sub_zero]

theorem finiteDimensional_ncV (hV : FiniteDimensional ℂ V) (k : ℕ) :
    FiniteDimensional ℂ (ncV ε V k) := by
  have := hV
  let f : ncV ε V k →ₗ[ℂ] ((Fin k → Fin n × Fin n) → V) :=
    LinearMap.pi fun κ => LinearMap.codRestrict V ((coord k κ).comp (ncV ε V k).subtype)
      (fun F => ncV_mem F.2 κ)
  refine FiniteDimensional.of_injective f ?_
  intro F G h
  exact Subtype.ext (big_ext fun κ => congrArg Subtype.val (congrFun h κ))

end BigRep

end ReciprocityTheory.ChartRestriction.DS
