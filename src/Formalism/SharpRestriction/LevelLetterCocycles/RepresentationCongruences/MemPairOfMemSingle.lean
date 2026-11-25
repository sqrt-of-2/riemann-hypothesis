module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QuotientDistinguishedTorsionFree
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def cont (ϖ : O) (g f : O⟦X⟧) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ k, g}), (k : ℕ∞)

theorem Cont.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b :=
  ENat.forall_natCast_le_iff_le.mp h

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem Cont.mem_pair_mono [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O) (g f : O⟦X⟧) {j k : ℕ} (hjk : j ≤ k)
    (h : f ∈ Ideal.span {C ϖ ^ k, g}) : f ∈ Ideal.span {C ϖ ^ j, g} := by
  refine (Ideal.span_le.2 ?_) h
  intro x hx
  rcases hx with rfl | rfl
  · have e : C ϖ ^ k = C ϖ ^ j * C ϖ ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem Cont.mem_zero [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O) (g f : O⟦X⟧) : f ∈ Ideal.span {C ϖ ^ 0, g} := by
  have h1 : (1 : O⟦X⟧) ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
  simpa using Ideal.mul_mem_left _ f h1

theorem Cont.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  unfold cont
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro hk
    by_contra hnot
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hnot (Cont.mem_zero ϖ g f)
    have hbound : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hj' : j ≤ k - 1 := by
        by_contra hjk
        push Not at hjk
        exact hnot (Cont.mem_pair_mono ϖ g f (by omega) hj)
      exact_mod_cast hj'
    have h3 := le_trans hk hbound
    norm_cast at h3
    omega

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem Cont.residue_unif [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem Cont.C_unif_ne_zero [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 :=
  (map_ne_zero_iff C C_injective).mpr hϖ.ne_zero

omit [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem Cont.C_dvd_of_map_eq_zero [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧)
    (hf : f.map (IsLocalRing.residue O) = 0) : C ϖ ∣ f := by
  have hc (n : ℕ) : ϖ ∣ coeff n f := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq, ← IsLocalRing.residue_eq_zero_iff]
    simpa only [coeff_map, map_zero] using congrArg (coeff n) hf
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

theorem Cont.prime_C_unif {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨Cont.C_unif_ne_zero hϖ, ?_, ?_⟩
  · intro hu
    have h1 := hu.map (PowerSeries.constantCoeff (R := O))
    rw [PowerSeries.constantCoeff_C] at h1
    exact hϖ.not_isUnit h1
  · intro f g hfg
    have hmap : (f * g).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨h, hh⟩ := hfg
      rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]
    rw [map_mul] at hmap
    rcases mul_eq_zero.1 hmap with h | h
    · exact Or.inl (Cont.C_dvd_of_map_eq_zero hϖ f h)
    · exact Or.inr (Cont.C_dvd_of_map_eq_zero hϖ g h)

theorem Cont.not_C_dvd {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) : ¬ (C ϖ ∣ g) := by
  rintro ⟨h, hh⟩
  apply hg
  rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]

theorem Cont.mem_of_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) (n : ℕ)
    (h : O⟦X⟧) (hm : C ϖ ^ n * h ∈ Ideal.span {g}) : h ∈ Ideal.span {g} := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp hm
  obtain ⟨r, rfl⟩ := (Cont.prime_C_unif hϖ).pow_dvd_of_dvd_mul_right n
    (Cont.not_C_dvd hϖ hg) ⟨h, hq⟩
  refine Ideal.mem_span_singleton'.mpr ⟨r, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero n (Cont.C_unif_ne_zero hϖ))
  simpa only [mul_assoc] using hq

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

theorem C2' {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    (∃ (a : O⟦X⟧) (n : ℕ), C ϖ ^ n * (f - C ϖ ^ k * a) ∈ Ideal.span {g}) ↔
      f ∈ Ideal.span {C ϖ ^ k, g} := by
  constructor
  · rintro ⟨a, n, h⟩
    have h1 := Cont.mem_of_pow_mul_mem hϖ hg n _ h
    have h2 : f = C ϖ ^ k * a + (f - C ϖ ^ k * a) := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.span_mono (Set.subset_insert _ _) h1)
  · intro hf
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hf
    refine ⟨u, 0, ?_⟩
    rw [pow_zero, one_mul, ← huv, Ideal.mem_span_singleton']
    exact ⟨v, by ring⟩

theorem mem_iff_le_cont {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  exact Cont.mem_iff_le ϖ g f k

theorem m1 {g g' : O⟦X⟧} (hg : IsDist g) (hg' : IsDist g') (hdvd : g ∣ g') (f : O⟦X⟧) :
    cont ϖ g' f ≤ cont ϖ g f := by
  apply Cont.enat_le_of_forall
  intro k hk
  have h1 := (Cont.mem_iff_le ϖ g' f k).2 hk
  apply (Cont.mem_iff_le ϖ g f k).1
  refine (Ideal.span_le.2 ?_) h1
  intro x hx
  rcases hx with rfl | rfl
  · exact Ideal.subset_span (by simp)
  · obtain ⟨c, rfl⟩ := hdvd
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem m2 {g : O⟦X⟧} (hg : IsDist g) (k f : O⟦X⟧) : cont ϖ g f ≤ cont ϖ g (k * f) := by
  apply Cont.enat_le_of_forall
  intro j hj
  exact (Cont.mem_iff_le ϖ g _ j).1 (Ideal.mul_mem_left _ k ((Cont.mem_iff_le ϖ g f j).2 hj))


end Formalism.MainNotions.N.FrobeniusPowerSeries
