module

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.SumTwoSquares
public import Lib.ClassField.Grunwald
import Lib.Adelic.Reduction.FirstMinimumShortBases
import Lib.ClassField.Global.CMSplittingCharacters
import Lib.ClassField.Places.TameInertia
import Lib.General.NumberTheory.FrobeniusOrbits

/-!
# Split places over ℚ(√−d) and quadratic steps with prescribed splitting

Let `K = ℚ(√-d)` (`New.QuadField` d, d ≡ 3 mod 4). For a CM field `E` containing `K`, we study the
places of `E` above split places of `K` prime to `d` (`New.GaloisRep.IsSplitPrimeToDisc`). For
stably unramified `E`, above each such place of `K` one can be chosen so that neither it nor its
conjugate equals one of two given places. We also construct a quadratic step `E'` over any stably
unramified CM field `E` (`New.HasPrimitiveRoot5040`: `E` contains a primitive 5040th root of unity).
The field `E'` contains `ℚ(√-D)` and has prescribed behaviour at the places over a given integer
`n`.

## Main definitions and results

* `New.GaloisRep.IsSplitPrimeToDisc.isSplit_of_below`: such a place differs from its complex
  conjugate.
* `New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne`: if `E` satisfies
  `New.HasPrimitiveRoot5040`, each such place of `K` has a place of `E` above it such that neither
  it nor its conjugate equals one of two given places.
* `New.GaloisRep.IsQuadraticStep`, `New.GaloisRep.exists_isQuadraticStep`: the step
  `E' = stepField χ`, for a character `χ` of `Gal(Ω/E)`, with the idele character of `χ`.

## Relation to the literature

Known; see `Lib.GaloisRep.Main.OddRank` for sources.
-/

@[expose] public section

namespace New.GaloisRep

section SplitPlaceCount

open NumberField Filter Ideal IsCyclotomicExtension.Rat Set Finset

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {d : ℕ} [HasQuadSubfield d E]
  {w : FinPlace E}

/-- A place `w` of `E` above a split place of `ℚ(√−d)` prime to `d`
(`New.GaloisRep.IsSplitPrimeToDisc`) is split: it differs from its complex conjugate. -/
lemma IsSplitPrimeToDisc.isSplit_of_below (hw : IsSplitPrimeToDisc (w.below (QuadField d))) :
    w.IsSplit :=
  fun h ↦ hw.isSplit_and_prime_q.1 (by rw [← below_star, h])

/-- For a finite set `S` of finite places of the CM field `E` and a nonzero natural number `ℓ`,
almost all finite places `w` satisfy three conditions: neither `w` nor its complex conjugate lies in
`S`, and `ℓ` does not lie in the prime ideal of `w`. -/
lemma eventually_notMem_star_notMem (ℓ : ℕ) [NeZero ℓ] (S : Finset (FinPlace E)) :
    ∀ᶠ w : FinPlace E in cofinite, w ∉ S ∧ star w ∉ S ∧ ↑ℓ ∉ w.asIdeal := by
  filter_upwards [S.eventually_cofinite_notMem, S.finite_toSet.star.eventually_cofinite_notMem,
    (finite_natCast_mem (K := E) ℓ).eventually_cofinite_notMem] with w h h_star h_ℓ
  exact ⟨h, by simpa using h_star, h_ℓ⟩

/-- Let `E` contain a primitive 5040th root of unity and contain `K = ℚ(√−d)`, let `u` be a split
place of `K` prime to `d` (`New.GaloisRep.IsSplitPrimeToDisc`), and let `a`, `b` be places of `E`.
Then some place `v` of `E` lies above `u` such that neither `v` nor its conjugate equals `a` or
`b`. -/
lemma IsSplitPrimeToDisc.exists_place_above_ne [U : HasPrimitiveRoot5040 E]
    {u : FinPlace (QuadField d)} (hu : IsSplitPrimeToDisc u) (a b : FinPlace E) :
    ∃ v : FinPlace E, v.below (QuadField d) = u ∧ v ≠ a ∧ star v ≠ a ∧ v ≠ b ∧ star v ≠ b := by
  classical
  -- Otherwise only `a`, `b` and their conjugates lie over `p = u.q`. For `m = 80 = 16 * 5` and
  -- `m = 63 = 9 * 7`, if `p ∤ m` then `ℚ(ζ_m)` has at most four primes over `p`, unramified of
  -- degree dividing the exponent of `(ℤ/m)ˣ`, too small to sum to `φ(m)`; so `p` divides both.
  by_contra h_none
  obtain ⟨ζ, hζ⟩ := U.exists_primitive_root
  obtain ⟨-, hp, h_over⟩ := hu.isSplit_and_prime_q
  have : Fact u.q.Prime := ⟨hp⟩
  have h_dvd (m₁ m₂ e : ℕ) (k : ℕ+) [NeZero (m₁ * m₂)] (hcop : m₁.Coprime m₂)
      (hm : 5040 = e * (m₁ * m₂)) (hk : 4 * (k : ℕ) < m₁.totient * m₂.totient)
      (h_exp₁ : ∀ x : ZMod m₁, IsUnit x → x ^ (k : ℕ) = 1)
      (h_exp₂ : ∀ x : ZMod m₂, IsUnit x → x ^ (k : ℕ) = 1) : u.q ∣ m₁ * m₂ := by
    by_contra h_not
    obtain ⟨K, hK⟩ : ∃ K : IntermediateField ℚ E, IsCyclotomicExtension {m₁ * m₂} ℚ K :=
      ⟨_, (hζ.pow (by lia) hm).intermediateField_adjoin_isCyclotomicExtension _⟩
    have h_pow : (u.q : ZMod (m₁ * m₂)) ^ (k : ℕ) = 1 := by
      apply (ZMod.chineseRemainder hcop).injective
      have ⟨hu₁, hu₂⟩ := Prod.isUnit_iff.mp
        ((ZMod.isUnit_prime_of_not_dvd hp h_not).map (ZMod.chineseRemainder hcop).toRingHom)
      rw [map_pow, map_one]
      exact Prod.ext (h_exp₁ _ hu₁) (h_exp₂ _ hu₂)
    have h_sum : (m₁ * m₂).totient =
        ((span {(u.q : ℤ)}).primesOver (𝓞 K)).ncard * orderOf (u.q : ZMod (m₁ * m₂)) := by
      rw [← finrank (m₁ * m₂) K, ← RingOfIntegers.rank,
        ← sum_ramification_inertia_eq_finrank (span {(u.q : ℤ)})]
      simp [ramificationIdx_eq_of_not_dvd _ K _ h_not, inertiaDeg_eq_of_not_dvd _ K _ h_not]
    rw [← Nat.totient_mul hcop] at hk
    grw [h_sum, orderOf_le_of_pow_eq_one k.pos h_pow,
      ncard_le_ncard (t := ↑(({a, b, star a, star b} : Finset (FinPlace E)).image
        fun v ↦ (v.below K).asIdeal)) ?_, ncard_coe_finset, card_image_le, card_le_four] at hk
    · exact hk.false
    · rintro P hP
      obtain ⟨v, ⟨⟩⟩ := FinPlace.comap_surjective (algebraMap K E)
        ⟨P, hP.1, ne_bot_of_mem_primesOver (by simpa using hp.ne_zero) hP⟩
      exact mem_image_of_mem _ (by
        grind [=_ below_star, star_star, (h_over (v.below _)).mpr (by simpa using hP.2.over.le)])
  have h_euler {m k : ℕ} (hm : m.totient = k) (x : ZMod m) (hx : IsUnit x) : x ^ k = 1 := by
    simpa [hm] using congrArg Units.val (ZMod.pow_totient hx.unit)
  have h_exp_sixteen (x : ZMod 16) (hx : IsUnit x) : x ^ 4 = 1 := by
    obtain ⟨t, ht⟩ := Nat.coprime_two_right.mp
      (((ZMod.isUnit_iff_coprime x.val 16).mp (by simpa using hx)).coprime_dvd_right (by norm_num))
    obtain ⟨s, hs⟩ := even_iff_two_dvd.mp (Nat.even_mul_succ_self t)
    have h_eq : (2 * t + 1) ^ 4 = 16 * (t ^ 4 + 2 * t ^ 3 + t ^ 2 + s) + 1 := by
      zify at hs ⊢; linear_combination 8 * hs
    rw [← ZMod.natCast_zmod_val x, ht, ← Nat.cast_pow, h_eq]
    simp [show (16 : ZMod 16) = 0 from rfl]
  have hφ_sixteen : (16 : ℕ).totient = 8 := by
    rw [show (16 : ℕ) = 2 ^ 4 from rfl, Nat.totient_prime_pow Nat.prime_two (by norm_num)]; norm_num
  have hφ_five : (5 : ℕ).totient = 4 := Nat.totient_prime (by norm_num)
  have hφ_nine : (9 : ℕ).totient = 6 := by
    rw [show (9 : ℕ) = 3 ^ 2 from rfl, Nat.totient_prime_pow (by norm_num : Nat.Prime 3) two_pos]
    norm_num
  have hφ_seven : (7 : ℕ).totient = 6 := Nat.totient_prime (by norm_num)
  exact hp.not_dvd_one (Nat.dvd_gcd
    (h_dvd 16 5 63 4 (by norm_num) rfl (by simp [hφ_sixteen, hφ_five])
      h_exp_sixteen (h_euler hφ_five))
    (h_dvd 9 7 80 6 (by norm_num) rfl (by simp [hφ_nine, hφ_seven])
      (h_euler hφ_nine) (h_euler hφ_seven)))

end SplitPlaceCount

section QuadraticStep

open NumberField IsDedekindDomain HeightOneSpectrum Ideal Nat ZMod decompGroup QZChar
  Cohomology QuadField algebraMap

/-- For `R ≠ 0` divisible by `4` and `n ≠ 0` there is `D ≡ -1 (mod R)` that is a norm `α * star α`
from `𝓞 E` and such that `-D` is a uniformiser at some place `P` prime to `n`. -/
lemma exists_norm_uniformiser (E : Type*) [Field E] [NumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] {R n : ℕ} (hR : R ≠ 0) (h4 : 4 ∣ R) (hn : n ≠ 0) :
    ∃ (D : ℕ) (α : 𝓞 E) (P : FinPlace E),
      R ∣ D + 1 ∧ α * star α = D ∧ ↑n ∉ P.asIdeal ∧
      P.valuation E ↑(-D : 𝓞 E) = WithZero.exp (-1) := by
  obtain ⟨i, ω, hi_sq, hi_star, hω_trace, hω_norm⟩ :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one_and_mul_star_eq_two (E := E)
  obtain ⟨j, b, hb_odd, hRb⟩ := exists_eq_two_pow_mul_odd hR
  let C : ℕ := 1 + b * (2 + 8 * b)
  have hC_mod_four : C % 4 = 3 := by obtain ⟨t, rfl⟩ := hb_odd; dsimp [C]; ring_nf; omega
  have hC : C.Coprime R := by cases j <;> simp [hRb, C, coprime_mul_iff_right, parity_simps]
  have : NeZero R := ⟨hR⟩
  obtain ⟨q, hq_large, hq, hq_mod⟩ : ∃ q > C * n * absNorm (differentIdeal ℤ (𝓞 E)),
      q.Prime ∧ (q : ZMod R) = (-unitOfCoprime C hC)⁻¹ :=
    forall_exists_prime_gt_and_eq_mod (-unitOfCoprime C hC)⁻¹.isUnit _
  have hD : R ∣ C * q + 1 :=
    (natCast_eq_zero_iff ..).mp (by simp [hq_mod, neg_add_eq_zero])
  have : Fact q.Prime := ⟨hq⟩
  have hq_mod_four : q % 4 ≠ 3 := by grind [h4.trans hD, Nat.mul_mod C q 4]
  obtain ⟨s, t, hst⟩ : ∃ s t : ℕ, s ^ 2 + t ^ 2 = q := Prime.sq_add_sq hq_mod_four
  obtain ⟨P, hP⟩ := FinPlace.exists_natCast_mem E q
  obtain ⟨⟨hCP, hnP⟩, h_different⟩ :
      (↑C ∉ P.asIdeal ∧ ↑n ∉ P.asIdeal) ∧ ↑(absNorm (differentIdeal ℤ (𝓞 E))) ∉ P.asIdeal := by
    simpa [hq.dvd_mul, ← P.natCast_mem_iff_dvd hP, hn, C, NeZero.ne] using
      fun h ↦ eq_zero_of_dvd_of_lt h hq_large
  refine ⟨C * q, (1 + 2 * b * ω) * (s + t * i), P, hD, ?_, hnP, ?_⟩
  · have h_star : star ((1 + 2 * (b : 𝓞 E) * ω) * (s + t * i)) =
        (1 + 2 * (b : 𝓞 E) * star ω) * (s - t * i) := by simp [hi_star, sub_eq_add_neg]
    rw [h_star]; push_cast [C, ← hst]
    linear_combination ((s : 𝓞 E) ^ 2 - (t : 𝓞 E) ^ 2 * i * i) *
        (2 * (b : 𝓞 E) * hω_trace + 4 * (b : 𝓞 E) ^ 2 * hω_norm) -
      (1 + 2 * (b : 𝓞 E) + 8 * (b : 𝓞 E) ^ 2) * (t : 𝓞 E) ^ 2 * hi_sq
  · have h_unram : ↑q ∉ P.asIdeal ^ 2 :=
      fun hq2 ↦ h_different (le_of_dvd (dvd_differentIdeal_of_mem_sq hq2) (absNorm_mem _))
    have hq_val : P.intValuation q = WithZero.exp (-1) := by
      simp [hP, h_unram, intValuation_eq_exp_neg_multiplicity,
        multiplicity_eq_of_dvd_of_not_dvd (k := 1), NeZero.ne]
    exact (valuation_of_algebraMap ..).trans (by simp [hCP, hq_val])

/-- If `c ^ 2` lies in `E`, then every `g ∈ Gal(Ω/E)` sends `c` to `c` or to `-c`. -/
lemma apply_sqrt_eq_or_eq_neg {E : Type*} [Field E] [EmbeddedNumberField E] (g : Gal(Ω/E)) {c : Ω}
    {x : E} (hc : c ^ 2 = algebraMap E Ω x) : g c = c ∨ g c = -c :=
  eq_or_eq_neg_of_sq_eq_sq _ _ (by simp [← map_pow, hc])

/-! ### Kummer sign homomorphism and quadratic character -/

section KummerSign

open scoped Classical

variable {E : Type} [Field E] [EmbeddedNumberField E] {b c : Ω} {x : E}

/-- The Kummer sign homomorphism `Gal(Ω/E) →* ℤˣ` (`{±1}`) sending `g` to `g c / c`. -/
private noncomputable def sqrtSign (hc : c ^ 2 = algebraMap E Ω x) (hc_ne : c ≠ 0) :
    Gal(Ω/E) →* ℤˣ :=
  let ε (g : Gal(Ω/E)) : ℤˣ := if g c = c then 1 else -1
  have hε (g : Gal(Ω/E)) : ((ε g : ℤ) : Ω) * c = g c := by
    by_cases h : g c = c
    · simp [ε, h]
    · dsimp only [ε]; rw [ite_eq_right h]; simp [(apply_sqrt_eq_or_eq_neg g hc).resolve_left h]
  MonoidHom.mk' ε fun g h ↦
      Units.ext <| Int.cast_injective (α := Ω) <| mul_right_cancel₀ hc_ne <| by
    calc ((ε (g * h) : ℤ) : Ω) * c = g (h c) := hε (g * h)
      _ = g (((ε h : ℤ) : Ω) * c) := by rw [hε h]
      _ = ((ε h : ℤ) : Ω) * (((ε g : ℤ) : Ω) * c) := by simp [hε g]
      _ = ((↑(ε g * ε h) : ℤ) : Ω) * c := by push_cast; ring

private lemma sqrtSign_mul_self (hc : c ^ 2 = algebraMap E Ω x) (hc_ne : c ≠ 0) (g : Gal(Ω/E)) :
    ((sqrtSign hc hc_ne g : ℤ) : Ω) * c = g c := by
  by_cases h : g c = c
  · simp [sqrtSign, h]
  · rw [sqrtSign, MonoidHom.mk'_apply, ite_eq_right h]
    simp [(apply_sqrt_eq_or_eq_neg g hc).resolve_left h]

private lemma sqrtSign_conjGal [IsCMField E] (hb : b ^ 2 = algebraMap E Ω x)
    (hb_conj : cmConj b ^ 2 = algebraMap E Ω (star x)) (hb_ne : b ≠ 0) (g : Gal(Ω/E)) :
    sqrtSign hb hb_ne (conjGal g) = sqrtSign hb_conj (by simpa using hb_ne) g :=
  Units.ext <| Int.cast_injective (α := Ω) <| mul_right_cancel₀ hb_ne <| by
    rw [sqrtSign_mul_self]
    calc (conjGal g) b = cmConj (g (cmConj b)) := rfl
      _ = cmConj (((sqrtSign hb_conj (by simpa using hb_ne) g : ℤ) : Ω) * cmConj b) := by
        rw [sqrtSign_mul_self]
      _ = _ := by simp

private noncomputable def signToQZ : ℤˣ →* Multiplicative QZ :=
  (QZ.ofZMod 2).toMultiplicative.comp <|
    MonoidHom.mk' (fun u : ℤˣ ↦ Multiplicative.ofAdd (if u = 1 then 0 else 1)) fun u v ↦ by
      rcases Int.units_eq_one_or u with rfl | rfl
      · simp
      · rcases Int.units_eq_one_or v with rfl | rfl <;>
          simp [← ofAdd_add, show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma signToQZ_eq_one_iff (u : ℤˣ) : signToQZ u = 1 ↔ u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simpa [signToQZ] using (QZ.ofZMod_injective (n := 2)).ne (by decide : (1 : ZMod 2) ≠ 0)

/-- The quadratic character `Gal(Ω/E) → ℚ/ℤ` of `E(b)`, composing `sqrtSign` with `ℤˣ ↪ ℚ/ℤ`. -/
private noncomputable def sqrtChar (hb : b ^ 2 = algebraMap E Ω x) (hb_ne : b ≠ 0) :
    QZChar Gal(Ω/E) :=
  ⟨fun g ↦ Multiplicative.toAdd (signToQZ (sqrtSign hb hb_ne g)),
    ((isLocallyConstant_smul b).comp fun c ↦
      Multiplicative.toAdd (signToQZ (if c = b then 1 else -1))).continuous,
    fun g h ↦ by simp⟩

private lemma two_nsmul_sqrtChar (hb : b ^ 2 = algebraMap E Ω x) (hb_ne : b ≠ 0) :
    2 • sqrtChar hb hb_ne = 0 := by
  ext g; change 2 • Multiplicative.toAdd (signToQZ (sqrtSign hb hb_ne g)) = 0
  rw [← ofAdd_eq_one, ofAdd_nsmul, ofAdd_toAdd, ← map_pow, Int.units_sq, map_one]

private lemma mem_ker_sqrtChar_iff (hb : b ^ 2 = algebraMap E Ω x) (hb_ne : b ≠ 0) (g : Gal(Ω/E)) :
    g ∈ ker (sqrtChar hb hb_ne) ↔ g b = b := by
  change signToQZ (sqrtSign hb hb_ne g) = 1 ↔ _
  rw [signToQZ_eq_one_iff]; simp [sqrtSign]

private lemma symmetrise_sqrtChar_eq_zero_iff [IsCMField E] (hb : b ^ 2 = algebraMap E Ω x)
    (hb_ne : b ≠ 0) (g : Gal(Ω/E)) :
    (symmetrize (sqrtChar hb hb_ne)).val g = 0 ↔
      sqrtSign hb hb_ne g * sqrtSign hb hb_ne (conjGal g) = 1 := by
  rw [← ofAdd_eq_one]
  change Multiplicative.ofAdd (Multiplicative.toAdd (signToQZ (sqrtSign hb hb_ne g)) +
    Multiplicative.toAdd (signToQZ (sqrtSign hb hb_ne (conjGal g)))) = 1 ↔ _
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_toAdd, ← map_mul, signToQZ_eq_one_iff]

/-- `symmetrize (sqrtChar hb hb_ne)` vanishes at `g` iff `g` fixes `c * b * cmConj b`. -/
private lemma symmetrise_sqrtChar_apply_eq_zero_iff [IsCMField E] (hb : b ^ 2 = algebraMap E Ω x)
    (hb_conj : cmConj b ^ 2 = algebraMap E Ω (star x)) (hb_ne : b ≠ 0) {a : E} (ha : a ≠ 0)
    (g : Gal(Ω/E)) :
    (symmetrize (sqrtChar hb hb_ne)).val g = 0 ↔
      g (algebraMap E Ω a * b * cmConj b) = algebraMap E Ω a * b * cmConj b := by
  rw [symmetrise_sqrtChar_eq_zero_iff, sqrtSign_conjGal hb hb_conj hb_ne]
  have h_act : g (algebraMap E Ω a * b * cmConj b) =
      ((↑(sqrtSign hb hb_ne g * sqrtSign hb_conj (by simpa using hb_ne) g) : ℤ) : Ω) *
        (algebraMap E Ω a * b * cmConj b) := by
    rw [_root_.map_mul, _root_.map_mul, AlgEquiv.commutes, ← sqrtSign_mul_self hb hb_ne g,
      ← sqrtSign_mul_self hb_conj (by simpa using hb_ne) g]; push_cast; ring
  rw [h_act]
  exact ⟨fun h ↦ by simp [h], fun h ↦ Units.ext <| Int.cast_injective (α := Ω) <|
    mul_right_cancel₀ (b := algebraMap E Ω a * b * cmConj b) (by simp [ha, hb_ne])
      (by simpa using h)⟩

/-- Inertia at `P` and `star P` surjects onto `{±1}²` under `g ↦ (sqrtSign g, sqrtSign gᶜ)`. -/
private lemma exists_mul_mem_ker_symmetrise_inf_ker [IsCMField E] (hb : b ^ 2 = algebraMap E Ω x)
    (hb_ne : b ≠ 0) {n : ℕ} {P : FinPlace E} (hnP : ↑n ∉ P.asIdeal)
    {σ : decompGroup Gal(Ω/E) (placeOver P)}
    (hσ_inertia : σ ∈ inertiaGroup (decompGroup Gal(Ω/E) (placeOver P)) (placeOver P))
    (hσ_sym : (symmetrize (sqrtChar hb hb_ne)).val σ ≠ 0) {H : Subgroup Gal(Ω/E)}
    (hH : inertiaAbove {v : FinPlace E | ↑n ∉ v.asIdeal ∧ v.q ≤ P.q} ⊆ H) (g : Gal(Ω/E)) :
    ∃ h ∈ H, g * h ∈ ker (symmetrize (sqrtChar hb hb_ne)) ⊓ ker (sqrtChar hb hb_ne) := by
  let s := sqrtSign hb hb_ne
  let Ψ : Gal(Ω/E) →* ℤˣ × ℤˣ := s.prod (s.comp conjGal)
  have hσH : (σ : Gal(Ω/E)) ∈ H := hH ⟨P, ⟨hnP, le_rfl⟩, _, P.isPlaceOver_placeOver, hσ_inertia⟩
  have hσH' : conjGal (σ : Gal(Ω/E)) ∈ H :=
    hH ⟨star P, by simp [hnP], _, P.isPlaceOver_placeOver.conjPlace_star,
      hσ_inertia.conjPlace_conjGal⟩
  have hσ_ne : s σ ≠ s (conjGal σ) := fun h_eq ↦
    hσ_sym ((symmetrise_sqrtChar_eq_zero_iff hb hb_ne σ).mpr (by rw [h_eq, Int.units_mul_self]))
  have ⟨he₁, he₂⟩ : ((-1, 1) : ℤˣ × ℤˣ) ∈ H.map Ψ ∧ ((1, -1) : ℤˣ × ℤˣ) ∈ H.map Ψ := by
    by_cases h_one : s σ = 1
    · have h_neg := (Int.units_eq_one_or (s (conjGal σ))).resolve_left (h_one ▸ hσ_ne.symm)
      constructor
      · exact ⟨conjGal σ, hσH', by simp [Ψ, h_one, h_neg]⟩
      · exact ⟨σ, hσH, Prod.ext h_one h_neg⟩
    · have h_neg := (Int.units_eq_one_or (s σ)).resolve_left h_one
      have h_one' := (Int.units_eq_one_or (s (conjGal σ))).resolve_right (h_neg ▸ hσ_ne.symm)
      constructor
      · exact ⟨σ, hσH, Prod.ext h_neg h_one'⟩
      · exact ⟨conjGal σ, hσH', by simp [Ψ, h_one', h_neg]⟩
  have h_surj : H.map Ψ = ⊤ := eq_top_iff.mpr fun ⟨u, v⟩ _ ↦ by
    have hu : (u, (1 : ℤˣ)) ∈ H.map Ψ := by
      rcases Int.units_eq_one_or u with rfl | rfl <;> [exact one_mem _; exact he₁]
    have hv : ((1 : ℤˣ), v) ∈ H.map Ψ := by
      rcases Int.units_eq_one_or v with rfl | rfl <;> [exact one_mem _; exact he₂]
    simpa using mul_mem hu hv
  obtain ⟨h, hh, hΨ⟩ := Subgroup.mem_map.mp (h_surj.symm ▸ Subgroup.mem_top (Ψ g)⁻¹)
  have hΨ_mul : Ψ (g * h) = 1 := by rw [_root_.map_mul, hΨ, mul_inv_cancel]
  have hs₁ : s (g * h) = 1 := congrArg Prod.fst hΨ_mul
  have hs₂ : s (conjGal (g * h)) = 1 := congrArg Prod.snd hΨ_mul
  exact ⟨h, hh, (symmetrise_sqrtChar_eq_zero_iff hb hb_ne _).mpr (by rw [hs₁, hs₂, one_mul]),
    by change signToQZ (s (g * h)) = 1; rw [hs₁, map_one]⟩

end KummerSign

/-- Local test: if `c ^ 2 = x` and `1 - x * u ^ 2 ∈ w ^ k` with `4 ∉ w ^ k`, then the decomposition
group at `A` over `w` fixes `c`. -/
lemma apply_sqrt_eq_self_of_mem_pow {E : Type*} [Field E] [EmbeddedNumberField E] {A : ClosurePlace}
    {w : FinPlace E} (hA : IsPlaceOver A w) {k : ℕ} (hk : 4 ∉ w.asIdeal ^ k) {g : Gal(Ω/E)}
    (hg : g ∈ decompGroup Gal(Ω/E) A) {c : Ω} {x u : 𝓞 E} (hc : c ^ 2 = algebraMap E Ω x)
    (hu : 1 - x * u ^ 2 ∈ w.asIdeal ^ k) : g c = c := by
  refine (apply_sqrt_eq_or_eq_neg g hc).resolve_right fun h_neg ↦ ?_
  let a : Ω := 1 + c * algebraMap E Ω u
  let a' : Ω := 1 - c * algebraMap E Ω u
  have h_val : A.valuation a' = A.valuation a := by
    rw [← show g • a = a' by simp [a, a', h_neg, sub_eq_add_neg]]; exact val_smul hg a
  have h_two : A.valuation (a' + a) ≤ A.valuation a := A.valuation.map_add_le h_val.le le_rfl
  have h_sum : algebraMap E Ω (4 : 𝓞 E) = (a' + a) * (a' + a) := by norm_num [a, a', map_ofNat]
  have h_prod : algebraMap E Ω (1 - x * u ^ 2 : 𝓞 E) = a * a' := by simp [a, a', ← hc]; ring
  have h_four : A.valuation (algebraMap E Ω (4 : 𝓞 E)) ≤
      A.valuation (algebraMap E Ω (1 - x * u ^ 2 : 𝓞 E)) := by
    simpa only [h_sum, h_prod, _root_.map_mul, h_val] using mul_le_mul' h_two h_two
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := E)] at hk hu
  exact hk (((hA.isEquiv ..).mp h_four).trans hu)

/-- Gluing at the places over `n`: let `α * star α = D` with `D ≡ -1 (mod w ^ k)` for all `w ∣ n`.
Then there is a nonzero real `t` such that at every `w ∣ n` either `α * t` is the inverse of a
square modulo `w ^ k`, or `star w = w` and `w` is prime to `2 * α * t`. -/
lemma exists_real_twist {E : Type*} [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E]
    {n k D : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) {α : 𝓞 E} (hα : α * star α = D)
    (hD : ∀ w : FinPlace E, ↑n ∈ w.asIdeal → ↑(D + 1) ∈ w.asIdeal ^ k) :
    ∃ t : 𝓞 E, t ≠ 0 ∧ star t = t ∧ ∀ w : FinPlace E, ↑n ∈ w.asIdeal →
      (∃ u : 𝓞 E, 1 - α * t * u ^ 2 ∈ w.asIdeal ^ k) ∨
      star w = w ∧ α * t ∉ w.asIdeal ∧ 2 ∉ w.asIdeal := by
  obtain ⟨i, hi, -⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  obtain ⟨_, -⟩ := exists_wellFoundedLT (FinPlace E)
  have : NeZero n := ⟨hn⟩
  obtain ⟨s, h_mod⟩ : ∃ s : 𝓞 E, ∀ w : FinPlace E, ↑n ∈ w.asIdeal →
      s - (if star w < w then α else 1) ∈ w.asIdeal ^ k := by
    simpa using exists_forall_sub_mem_ideal (s := (finite_natCast_mem n).toFinset) asIdeal
      (fun _ ↦ k) (by simp [prime]) (fun _ _ _ _ hne h ↦ hne (HeightOneSpectrum.ext h))
      fun w ↦ if star w.val < w then α else 1
  have h_mod_star (w : FinPlace E) (hw : ↑n ∈ w.asIdeal) :
      star s - (if w < star w then star α else 1) ∈ w.asIdeal ^ k := by
    simpa [starRingEnd_apply, apply_ite star] using le_comap_pow _ k (h_mod (star w) (by simpa))
  by_cases hs_zero : s = 0
  · refine ⟨1, one_ne_zero, star_one _, fun w hw ↦ absurd ?_ (one_notMem w.asIdeal)⟩
    by_cases hlt : star w < w
    · exact pow_le_self hk (neg_mem_iff.mp (by simpa [hs_zero, hlt.not_gt] using h_mod_star w hw))
    · exact pow_le_self hk (neg_mem_iff.mp (by simpa [hs_zero, hlt] using h_mod w hw))
  refine ⟨s * star s, by simpa, by simp [mul_comm], fun w hw ↦ ?_⟩
  let π := Ideal.Quotient.mk (w.asIdeal ^ k)
  have hπα : π α * π (star α) = -1 := by
    rw [← _root_.map_mul, hα]
    exact eq_neg_of_add_eq_zero_left
        (by simpa [π] using Ideal.Quotient.eq_zero_iff_mem.mpr (hD w hw))
  have hπs : π s = π (if star w < w then α else 1) := Ideal.Quotient.eq.mpr (h_mod w hw)
  have hπs' : π (star s) = π (if w < star w then star α else 1) :=
    Ideal.Quotient.eq.mpr (h_mod_star w hw)
  rcases lt_trichotomy w (star w) with hlt | heq | hgt
  · refine .inl ⟨i, Ideal.Quotient.eq_zero_iff_mem.mp <| show π _ = 0 from ?_⟩
    have hπi : π i ^ 2 = -1 := by rw [sq, ← _root_.map_mul, hi, map_neg, map_one]
    simp only [map_sub, map_one, _root_.map_mul, map_pow, hπs, hπs', hlt, hlt.not_gt, ↓reduceIte,
      hπi]
    linear_combination hπα
  · refine .inr ⟨heq.symm, fun h ↦ one_notMem w.asIdeal ?_,
      fun h_two ↦ HasPrimitiveRoot5040.isSplit_of_two_mem h_two heq.symm⟩
    have h_add : α * (s * star s) * star α + 1 ∈ w.asIdeal ^ k :=
      Ideal.Quotient.eq_zero_iff_mem.mp <| show π _ = 0 from by
        simp only [map_add, _root_.map_mul, map_one, hπs, hπs', ← heq, lt_irrefl, ↓reduceIte]
        linear_combination hπα
    simpa using sub_mem (pow_le_self hk h_add) (w.asIdeal.mul_mem_right (star α) h)
  · refine .inl ⟨star α, Ideal.Quotient.eq_zero_iff_mem.mp <| show π _ = 0 from ?_⟩
    simp only [map_sub, map_one, _root_.map_mul, map_pow, hπs, hπs', hgt, hgt.not_gt, ↓reduceIte]
    linear_combination -(π α * π (star α) - 1) * hπα

/-- A place of `ℚ(√-D)` that contains `(D + 1) / 4` is split and prime to `D`. -/
lemma IsSplitPrimeToDisc.of_mem {D : ℕ} [Fact (D % 4 = 3)] {v : FinPlace (QuadField D)}
    (hv_mem : ↑((D + 1) / 4) ∈ v.asIdeal) : IsSplitPrimeToDisc v := by
  have h_prod : betaK D * (1 - betaK D) ∈ v.asIdeal := by rwa [betaK_mul_one_sub D]
  obtain hc | hc := v.isPrime.mem_or_mem h_prod
  · exact ⟨0, by simpa using hc, 1, 1, by simp⟩
  · exact ⟨1, by simpa using neg_mem hc, -1, -1, by simp⟩

/-- A `ℚ/ℤ`-valued character `χ` of `Gal(Ω/E)` and a natural number `D` form a quadratic step over
`E` for the integer `n`. Here `symmetrize χ` is `g ↦ χ g + χ gᶜ`, with `gᶜ` the conjugate of `g` by
complex conjugation, and `stepField χ`, the fixed field of its kernel, contains `ℚ(√-D)`. -/
structure IsQuadraticStep (E : Type) [Field E] [EmbeddedNumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (n : ℕ) (χ : QZChar Gal(Ω/E)) (D : ℕ)
    [HasQuadSubfield D (stepField χ)] : Prop where
  /-- `stepField χ`, with the idele character of `χ`, is a step over `E`. -/
  isStep : IsStep (stepField χ) (ideleChar χ)
  /-- For some `m`, every subgroup that contains the inertia groups at the places prime to `n` of
  norm at most `m` generates `Gal(Ω/E)` together with `ker (symmetrize χ) ⊓ ker χ`. -/
  exists_mul_mem_of_inertiaAbove_subset : ∃ m : ℕ, ∀ H : Subgroup Gal(Ω/E),
    inertiaAbove {x : FinPlace E | ↑n ∉ x.asIdeal ∧ x.q ≤ m} ⊆ H →
    ∀ g : Gal(Ω/E), ∃ h ∈ H, g * h ∈ ker (symmetrize χ) ⊓ ker χ
  /-- The places of `stepField χ` over `n` lie over split places of `QuadField D` prime to `D`. -/
  isSplitPrimeToDisc_below : ∀ u : FinPlace (stepField χ), ↑n ∈ u.asIdeal →
    IsSplitPrimeToDisc (u.below (QuadField D))
  /-- At a place over `n`, the decomposition group fixes `stepField χ`. -/
  decompGroup_le_ker_symmetrise : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → decompGroup Gal(Ω/E) A ≤ ker (symmetrize χ)
  /-- At a place over `n`, the inertia group fixes `stepField χ`, and `χ` vanishes on it. -/
  inertiaGroup_le_ker_inf : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → inertiaGroup Gal(Ω/E) A ≤ ker (symmetrize χ) ⊓ ker χ
  /-- At a split place over `n`, the same holds for the whole decomposition group. -/
  decompGroup_le_ker_inf_of_isSplit : ∀ {A : ClosurePlace} {w : FinPlace E}, IsPlaceOver A w →
    ↑n ∈ w.asIdeal → w.IsSplit → decompGroup Gal(Ω/E) A ≤ ker (symmetrize χ) ⊓ ker χ

/-- For `E` a CM field containing a primitive 5040th root of unity (`HasPrimitiveRoot5040 E`) and
`n ≠ 0`, there are a `ℚ/ℤ`-valued character `χ` of `Gal(Ω/E)` and `D ≡ 3 (mod 4)` forming a
quadratic step over `E` for `n` (`New.GaloisRep.IsQuadraticStep`). -/
lemma exists_isQuadraticStep (E : Type) [Field E] [EmbeddedNumberField E] [IsCMField E]
    [HasPrimitiveRoot5040 E] (n : ℕ) (hn : n ≠ 0) :
    ∃ (χ : QZChar Gal(Ω/E)) (D : ℕ) (_ : HasQuadSubfield D (stepField χ)),
      IsQuadraticStep E n χ D := by
  classical
  -- `χ` is the quadratic character of `E(b)`, `b ^ 2 = α * t`, where `α * star α = D` and `t` is
  -- real; then `stepField χ = E(√-D)`.
  obtain ⟨i, hi_sq, -⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  have hi : i ≠ 0 := fun h ↦ by simp [h] at hi_sq
  let k : ℕ := (span {(4 : 𝓞 E)}).absNorm
  have hk (w : FinPlace E) : 4 ∉ w.asIdeal ^ k := fun h_mem ↦
    not_le.mpr (Nat.lt_pow_self w.one_lt_q) <| by
      simpa [k] using Int.natAbs_le_of_dvd_ne_zero (absNorm_dvd_norm_of_mem h_mem) (by simp)
  obtain ⟨D, α, P, ⟨M, hM⟩, hα, hnP, hP⟩ := exists_norm_uniformiser E (R := 4 * n * (2 * n) ^ k)
    (by positivity) ((dvd_mul_right 4 n).mul_right _) hn
  have hD_mod_four : Fact (D % 4 = 3) := ⟨by rw [mul_assoc, mul_assoc] at hM; omega⟩
  have hD (w : FinPlace E) (hw : 2 ∈ w.asIdeal ∨ ↑n ∈ w.asIdeal) : ↑(D + 1) ∈ w.asIdeal ^ k := by
    simp [hM, pow_mem_pow (w.isPrime.mul_mem_iff_mem_or_mem.mpr hw), mul_mem_left, mul_mem_right]
  obtain ⟨t, ht, ht_real, ht_local⟩ :=
    exists_real_twist hn (by simp [k]) hα fun w hw ↦ hD w (.inr hw)
  obtain ⟨b, hb⟩ := TauCeti.IsAbsolutelyIntegrallyClosed.exists_pow_eq 2 (algebraMap E Ω ↑(α * t))
  have hb_conj : cmConj b ^ 2 = algebraMap E Ω (star ↑(α * t)) := by
    rw [← map_pow, hb, cmConj_algebraMap]
  let y : Ω := algebraMap E Ω (i / t) * b * cmConj b
  have hy : y ^ 2 = algebraMap E Ω (-D : 𝓞 E) := by
    simp_rw [y, mul_pow, hb, hb_conj, ← map_pow, ← _root_.map_mul]
    congr; field_simp (disch := simp [ht]); norm_cast
    rw [sq, hi_sq, star_mul, ht_real]; linear_combination -(t ^ 2) * hα
  have hy_ne : y ≠ 0 := by
    simpa using hy.trans_ne (show algebraMap E Ω (-D : 𝓞 E) ≠ 0 by simp [NeZero.ne])
  have hb_ne : b ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hy_ne)
  let χ : QZChar Gal(Ω/E) := sqrtChar hb hb_ne
  have h_sym (g : Gal(Ω/E)) : (symmetrize χ).val g = 0 ↔ g y = y :=
    symmetrise_sqrtChar_apply_eq_zero_iff hb hb_conj hb_ne (by simp [hi, ht]) g
  have h_dec {A : ClosurePlace} {w : FinPlace E} (hA : IsPlaceOver A w)
      (hw : 2 ∈ w.asIdeal ∨ ↑n ∈ w.asIdeal) : decompGroup Gal(Ω/E) A ≤ ker (symmetrize χ) :=
    fun g hg ↦ (h_sym g).mpr <|
      apply_sqrt_eq_self_of_mem_pow hA (hk w) hg hy (u := 1) (by simpa [add_comm] using hD w hw)
  obtain ⟨h_local, -, h_unif⟩ :=
    P.isPlaceOver_placeOver.isLocalGalois_and_residueCard_eq_and_isUniformizer Gal(Ω/E)
  obtain ⟨σ, hσ_inertia, hσ⟩ := h_local.exists_inertia_smul_eq_of_pow_eq
    (h_unif (π := .mk0 ((-D : 𝓞 E) : E) (by simp [NeZero.ne]))
      (P.isPlaceOver_placeOver.isUniformizer_iff.mpr hP))
    two_pos hy (neg_sq y)
  have hσ_sym : (symmetrize χ).val σ ≠ 0 :=
    mt (h_sym σ).mp (hσ.trans_ne (by simpa [neg_eq_self] using hy_ne))
  have h_sym_ne : symmetrize χ ≠ 0 := fun h_zero ↦ hσ_sym (by simp [h_zero])
  obtain ⟨h_step, -⟩ := isStep_stepField χ prime_two (two_nsmul_sqrtChar hb hb_ne) h_sym_ne
    fun hA hw g hg ↦ h_dec hA (.inl hw) hg.1
  let y' : stepField χ := ⟨y, fun g ↦ (h_sym _).mp g.prop⟩
  let : Algebra (QuadField D) (stepField χ) :=
    (embOfSqrt D (y := y') (Subtype.ext (by simp [y', hy]))).toAlgebra
  let h_quad : HasQuadSubfield D (stepField χ) := {}
  refine ⟨χ, D, h_quad,
    { isStep := h_step
      exists_mul_mem_of_inertiaAbove_subset := ⟨P.q, fun H hH g ↦
        exists_mul_mem_ker_symmetrise_inf_ker hb hb_ne hnP hσ_inertia hσ_sym hH g⟩
      isSplitPrimeToDisc_below := by
        simp +contextual [IsSplitPrimeToDisc.of_mem, hM, mul_assoc, mul_mem_right]
      decompGroup_le_ker_symmetrise := fun hA hw ↦ h_dec hA (.inr hw)
      inertiaGroup_le_ker_inf := fun {A w} hA hw g hg ↦
        ⟨h_dec hA (.inr hw) hg.1, (mem_ker_sqrtChar_iff hb hb_ne g).mpr ?_⟩
      decompGroup_le_ker_inf_of_isSplit := fun {A w} hA hw h_split g hg ↦
        ⟨h_dec hA (.inr hw) hg, (mem_ker_sqrtChar_iff hb hb_ne g).mpr ?_⟩ }⟩
  · rcases ht_local w hw with ⟨u, hu⟩ | ⟨-, hαt, h2⟩
    · exact apply_sqrt_eq_self_of_mem_pow hA (hk w) hg.1 hb hu
    · exact inertia_fixes_root_of_unit hg (hA.valuation_natCast_eq_one_iff.mpr h2) hb
        (hA.valuationVia_eq_one_iff.mpr ((valuation_eq_one_iff_notMem ..).mpr hαt)) (by simp)
  · obtain ⟨u, hu⟩ := (ht_local w hw).resolve_right fun ⟨h_star_eq, _⟩ ↦ h_split h_star_eq
    exact apply_sqrt_eq_self_of_mem_pow hA (hk w) hg hb hu

end QuadraticStep

end New.GaloisRep
