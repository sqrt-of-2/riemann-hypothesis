module

public import Mathlib.NumberTheory.NumberField.Basic
public import Formalism.HermitianLattices.LocS
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

namespace UpperTheory.Reformulated.B.SelectionLemmas

theorem aux1.{u_1} : ∀ {K : Type u_1} [inst : Field K],
  SMulCommClass K K K := by
  intros; infer_instance

theorem aux2.{u_1} : ∀ {K : Type u_1} [inst : Field K],
  SMulCommClass K K K := by
  intros; infer_instance

theorem aux3.{u_1, u_2, u_3} : ∀ {S : Type u_3} {K : Type u_2} {V : Type u_1}
  [inst : CommRing S] [inst_1 : Field K] [inst_2 : Algebra S K] [inst_3 : AddCommGroup V] [inst_4 : Module K V]
  [inst_5 : Module S V] [IsScalarTower S K V], LinearMap.CompatibleSMul V K S K := by
  intros; infer_instance

noncomputable def hdual.{u_1, u_2, u_3} : {S : Type u_1} →
  {K : Type u_2} →
    {V : Type u_3} →
      [inst : CommRing S] →
        [inst_1 : Field K] →
          [inst_2 : StarRing K] →
            [inst_3 : Algebra S K] →
              [inst_4 : AddCommGroup V] →
                [inst_5 : Module K V] →
                  [inst_6 : Module S V] →
                    [IsScalarTower S K V] → (V →ₗ⋆[K] V →ₗ[K] K) → Submodule S V → Submodule S V :=
  fun {S} {K} {V} [CommRing S] [Field K] [StarRing K] [Algebra S K] [AddCommGroup V] [Module K V] [Module S V]
      [IsScalarTower S K V] B L =>
    ⨅ y ∈ L, Submodule.comap ((B y).restrictScalars S) 1

noncomputable def dual.{u_1, u_2, u_3} : {R : Type u_1} →
  {K : Type u_2} →
    {V : Type u_3} →
      [inst : CommRing R] →
        [inst_1 : Field K] →
          [inst_2 : StarRing K] →
            [inst_3 : Algebra R K] →
              [inst_4 : AddCommGroup V] →
                [inst_5 : Module K V] →
                  [inst_6 : Module R V] →
                    [IsScalarTower R K V] → (V →ₗ⋆[K] V →ₗ[K] K) → Submodule R V → Submodule R V :=
  fun {R} {K} {V} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V]
      [IsScalarTower R K V] h L =>
    hdual h L

theorem aux6 : ∀ {K : Type} [inst : Field K],
  RingHomInvPair (RingHom.id K) (RingHom.id K) := by
  intros; infer_instance

theorem aux7 : ∀ {K : Type} [inst : Field K], SMulCommClass K K K := by
  intros; infer_instance

theorem aux8 : ∀ {K : Type} [inst : Field K] {n : ℕ},
  SMulCommClass K K ((Fin n → K) →ₗ[K] K) := by
  intros; infer_instance

noncomputable def hform : {K : Type} →
  [inst : Field K] →
    [inst_1 : StarRing K] → {n : ℕ} → Matrix (Fin n) (Fin n) K → (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  fun {K} [Field K] [StarRing K] {n} H => (Matrix.toLinearMapₛₗ₂' K (starRingEnd K) (RingHom.id K)) H

noncomputable def locS.{u_1, u_4} {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (L : Submodule R W) : Submodule R W :=
  Formalism.HermitianLatticesTheory.locS S L

noncomputable def hcompl.{u_1, u_2} : {R : Type u_1} →
  {K : Type u_2} → [inst : CommRing R] → [inst_1 : Field K] → [StarRing K] → [Algebra R K] → Ideal R → Submonoid R :=
  fun {R} {K} [CommRing R] [Field K] [StarRing K] [Algebra R K] p =>
    Submonoid.closure {s | s ∉ p ∧ ∀ (t : R), (Algebra.algebraMap R K) t = Star.star ((Algebra.algebraMap R K) s) → t ∉ p}

noncomputable def loc.{u_1, u_2, u_4} : {R : Type u_1} →
  {K : Type u_2} →
    [inst : CommRing R] →
      [inst_1 : Field K] →
        [StarRing K] →
          [Algebra R K] →
            {W : Type u_4} →
              [inst_4 : AddCommGroup W] → [inst_5 : Module R W] → Ideal R → Submodule R W → Submodule R W :=
  fun {R} {K} [CommRing R] [Field K] [StarRing K] [Algebra R K] {W} [AddCommGroup W] [Module R W] p L =>
    locS (hcompl (K := K) p) L

noncomputable def IsLocBasis : {K : Type} →
  [inst : Field K] →
    [StarRing K] →
      {D : ℕ} →
        Submodule (NumberField.RingOfIntegers K) (Fin D → K) →
          IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → (Fin D → Fin D → K) → Prop :=
  fun {K} [Field K] [StarRing K] {D} L w e =>
    LinearIndependent K e ∧
      loc (K := K) w.asIdeal
          (Submodule.span (NumberField.RingOfIntegers K) (Set.range e)) =
        loc (K := K) w.asIdeal L

theorem complex_normed_instance_compat : ∀ {K : Type} [inst : Field K],
  RingHomSurjective (RingHom.id (NumberField.RingOfIntegers K)) := by
  intros; infer_instance

theorem padic_embedding_algebra_compat : ∀ {K : Type} [inst : Field K]
  {d d' : ℕ}, LinearMap.CompatibleSMul (Fin d → K) (Fin d' → K) (NumberField.RingOfIntegers K) K := by
  intros; infer_instance

noncomputable def matLat : {K : Type} →
  [inst : Field K] →
    {d d' : ℕ} →
      Matrix (Fin d') (Fin d) K →
        Submodule (NumberField.RingOfIntegers K) (Fin d → K) → Submodule (NumberField.RingOfIntegers K) (Fin d' → K) :=
  fun {K} [Field K] {d d'} φ L => Submodule.map (φ.mulVecLin.restrictScalars (NumberField.RingOfIntegers K)) L

noncomputable def vw : {K : Type} →
  [inst : Field K] → [NumberField K] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → K → ℤ :=
  fun {K} [Field K] [NumberField K] w a =>
    FractionalIdeal.count K w ((FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))) a)

noncomputable def gramR : {K : Type} →
  [inst : Field K] → [StarRing K] → {D m : ℕ} → Matrix (Fin D) (Fin D) K → (Fin m → Fin D → K) → K :=
  fun {K} [Field K] [StarRing K] {D m} Γ e => (Matrix.of fun a b => Star.star (e a) ⬝ᵥ Γ.mulVec (e b)).det

noncomputable def quotGram : {K : Type} →
  [inst : Field K] →
    [StarRing K] → {n D : ℕ} → Matrix (Fin D) (Fin n) K → Matrix (Fin n) (Fin n) K → Matrix (Fin D) (Fin D) K :=
  fun {K} [Field K] [StarRing K] {n D} P H => (P * H⁻¹ * P.conjTranspose)⁻¹

section Helpers
open NumberField IsDedekindDomain Matrix

private theorem star_int {K : Type} [Field K] [StarRing K] (a : 𝓞 K) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = star (algebraMap (𝓞 K) K a) := by
  exact ⟨⟨_, (RingOfIntegers.isIntegral_coe a).map ((starRingEnd K).toIntAlgHom)⟩, rfl⟩

private theorem hcompl_spec {K : Type} [Field K] [StarRing K] (p : Ideal (𝓞 K)) (hp : p.IsPrime)
    (s : 𝓞 K) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p ∧ ∃ t : 𝓞 K, t ∉ p ∧ algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s) := by
  unfold hcompl at hs
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht⟩ := star_int x
    exact ⟨hx.1, t, hx.2 t ht, ht⟩
  | one => exact ⟨(Ideal.ne_top_iff_one p).1 hp.ne_top, 1, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hx, t, ht, ht'⟩ := hx
    obtain ⟨hy, u, hu, hu'⟩ := hy
    refine ⟨fun h => (hp.mem_or_mem h).elim hx hy, t * u, fun h => (hp.mem_or_mem h).elim ht hu, ?_⟩
    rw [map_mul, map_mul, ht', hu', star_mul']

private theorem exists_uniform {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
    (S : Submonoid R) (N L : Submodule R W) (hN : N.FG) (h : N ≤ locS S L) :
    ∃ s ∈ S, ∀ y ∈ N, s • y ∈ L := by
  induction N, hN using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨s, hs, hx⟩ := h (Submodule.mem_span_singleton_self x)
    refine ⟨s, hs, fun y hy => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simpa [smul_smul, mul_comm] using L.smul_mem a hx
  | sup N₁ N₂ _ _ h₁ h₂ =>
    obtain ⟨s, hs, h₁⟩ := h₁ (le_sup_left.trans h)
    obtain ⟨t, ht, h₂⟩ := h₂ (le_sup_right.trans h)
    refine ⟨s * t, S.mul_mem hs ht, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ (h₁ a ha)
    · rw [mul_smul]; exact L.smul_mem _ (h₂ b hb)

private theorem vw_mul {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul]
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.2 ha
  · exact FractionalIdeal.spanSingleton_ne_zero_iff.2 hb

private theorem vw_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : K) (m : ℕ) : vw w (a ^ m) = m * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

private theorem vw_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) : 0 ≤ vw w (algebraMap (𝓞 K) K a) := by
  simpa only [vw, ← FractionalIdeal.coeIdeal_span_singleton] using FractionalIdeal.count_coeIdeal_nonneg K w (Ideal.span {a})

private theorem vw_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ∉ w.asIdeal) : vw w (algebraMap (𝓞 K) K a) = 0 := by
  classical
  have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    intro h
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot] at h
    exact ha (h ▸ w.asIdeal.zero_mem)
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coeIdeal K w h0]
  by_contra hne
  have := (Associates.count_ne_zero_iff_dvd h0 w.irreducible).1 (by exact_mod_cast hne)
  exact ha (Ideal.dvd_span_singleton.1 this)

private theorem det_int {K : Type} [Field K] {D : ℕ} (A : Matrix (Fin D) (Fin D) K)
    (h : ∀ i j, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = A i j) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = A.det := by
  choose B hB using h
  refine ⟨(Matrix.of B).det, ?_⟩
  rw [RingHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j => hB i j)

private theorem core {K : Type} [Field K] [StarRing K] {n D : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (hH : IsUnit H.det) (B : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (c : K)
    (hc : ∀ x ∈ dual (hform H) M, c • x ∈ M) (s t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K s))
    (hs : ∀ y ∈ M, ∀ i, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K s * (B *ᵥ y) i)
    (i j : Fin D) :
    ∃ a : 𝓞 K, algebraMap (𝓞 K) K a =
      ((algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K t * c) • (B * H⁻¹ * Bᴴ)) i j := by
  have hx : algebraMap (𝓞 K) K t • (H⁻¹ *ᵥ star (B j)) ∈ dual (hform H) M := by
    unfold dual hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
    intro y hy
    obtain ⟨a, ha⟩ := hs y hy j
    obtain ⟨b, hb⟩ := star_int a
    refine ⟨b, ?_⟩
    rw [hb, ha, LinearMap.restrictScalars_apply, map_smul]
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    have h2 : ∀ v : Fin n → K, ∑ a, ∑ b, (starRingEnd K) (y a) • (RingHom.id K) (v b) • H a b
        = star y ⬝ᵥ (H *ᵥ v) := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, smul_eq_mul, RingHom.id_apply,
        starRingEnd_apply, Pi.star_apply]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [h2, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec,
      star_mul', ← ht, smul_eq_mul]
    congr 1
    simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]
  obtain ⟨a, ha⟩ := hs _ (hc _ hx) i
  refine ⟨a, ?_⟩
  rw [ha, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.smul_apply,
    Matrix.mul_apply (M := B * H⁻¹)]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply]
  ring

end Helpers

theorem main : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : StarRing K] {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
  (M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)),
  M.FG →
    ∀ (l g : ℕ),
      0 < l →
        (∀ x ∈ dual (hform H) M,
            (l : K) ^ g • x ∈ M) →
          ∀ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (e : Fin D → Fin D → K),
            IsLocBasis
                (matLat P M) w e →
              vw w
                  (gramR
                    (quotGram P H) e) ≤
                ↑g * ↑D * vw w ↑l := by
  open NumberField Matrix in
  intro K _ _ _ n D H P M hM l g hl hc w e he
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hl.ne'
  have hvl : 0 ≤ vw w (l : K) := by simpa using vw_nonneg w (l : 𝓞 K)
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have : gramR (quotGram P H) e = 1 := Matrix.det_isEmpty
    rw [this, vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
    simp
  by_cases hG : gramR (quotGram P H) e = 0
  · rw [hG, vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
    positivity
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  set E : Matrix (Fin D) (Fin D) K := (Matrix.of e)ᵀ with hE
  have hgram : gramR (quotGram P H) e = (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E).det := by
    unfold gramR quotGram
    congr 1
    ext a b
    rw [Matrix.mul_assoc Eᴴ, Matrix.mul_apply]
    rfl
  have hG' := hG
  rw [hgram, Matrix.det_mul, Matrix.det_mul] at hG'
  have hEu : IsUnit E.det := (right_ne_zero_of_mul hG').isUnit
  have hEu' : IsUnit Eᴴ.det := (left_ne_zero_of_mul (left_ne_zero_of_mul hG')).isUnit
  have hA : IsUnit (P * H⁻¹ * Pᴴ).det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.det_zero] at hG'
    all_goals first | exact hG' (by simp)
  have hH : IsUnit H.det := by
    by_contra h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.det_zero] at hA
    all_goals first | exact not_isUnit_zero hA
  have hle : matLat P M ≤ locS (hcompl (K := K) w.asIdeal) (Submodule.span (𝓞 K) (Set.range e)) := by
    intro x hx
    have h1 : x ∈ loc (K := K) w.asIdeal (matLat P M) :=
      ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [← he.2] at h1
    exact h1
  obtain ⟨s, hsS, hs⟩ := exists_uniform _ _ _ (hM.map _) hle
  obtain ⟨hsw, t, htw, ht⟩ := hcompl_spec _ w.isPrime s hsS
  have hs' : ∀ y ∈ M, ∀ i, ∃ a : 𝓞 K,
      algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K s * ((E⁻¹ * P) *ᵥ y) i := by
    intro y hy i
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hs (P *ᵥ y) (Submodule.mem_map_of_mem hy))
    refine ⟨a i, ?_⟩
    have h1 : E *ᵥ (fun i => algebraMap (𝓞 K) K (a i)) = algebraMap (𝓞 K) K s • (P *ᵥ y) := by
      rw [algebraMap_smul, ← ha]
      ext k
      simp [hE, Matrix.mulVec, dotProduct, Finset.sum_apply, Algebra.smul_def, mul_comm]
    have h2 := congrArg (fun v => (E⁻¹ *ᵥ v) i) h1
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hEu, Matrix.one_mulVec,
      Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  obtain ⟨a, ha⟩ := det_int _ (core H hH (E⁻¹ * P) M ((l : K) ^ g) hc s t ht hs')
  have hN : (E⁻¹ * P * H⁻¹ * (E⁻¹ * P)ᴴ) * (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
    calc E⁻¹ * P * H⁻¹ * (Pᴴ * Eᴴ⁻¹) * (Eᴴ * (P * H⁻¹ * Pᴴ)⁻¹ * E)
        = E⁻¹ * ((P * H⁻¹ * Pᴴ) * ((Eᴴ⁻¹ * Eᴴ) * (P * H⁻¹ * Pᴴ)⁻¹)) * E := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hEu', Matrix.one_mul, Matrix.mul_nonsing_inv _ hA,
            Matrix.mul_one, Matrix.nonsing_inv_mul _ hEu]
  have hdet := congrArg Matrix.det hN
  rw [Matrix.det_mul, ← hgram, Matrix.det_one] at hdet
  rw [Matrix.det_smul, Fintype.card_fin] at ha
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := fun h =>
    hsw (((FaithfulSMul.algebraMap_eq_zero_iff _ _).1 h) ▸ w.asIdeal.zero_mem)
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := fun h =>
    htw (((FaithfulSMul.algebraMap_eq_zero_iff _ _).1 h) ▸ w.asIdeal.zero_mem)
  have hkey : algebraMap (𝓞 K) K a * gramR (quotGram P H) e
      = (algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K t * (l : K) ^ g) ^ D := by
    rw [ha, mul_assoc, hdet, mul_one]
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
    refine left_ne_zero_of_mul (b := gramR (quotGram P H) e) ?_
    rw [hkey]
    exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hs0 ht0) (pow_ne_zero _ hl0))
  have hv := congrArg (vw w) hkey
  rw [vw_mul w ha0 hG, vw_pow, vw_mul w (mul_ne_zero hs0 ht0) (pow_ne_zero _ hl0),
    vw_mul w hs0 ht0, vw_pow, vw_eq_zero w s hsw, vw_eq_zero w t htw] at hv
  have := vw_nonneg w a
  linarith

end UpperTheory.Reformulated.B.SelectionLemmas
