module

public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscrete
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem haar_fundamental_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have := hlc
  have := hsc
  have := ht2
  obtain ⟨htg, hlcH, hscH, ht2H, hbH, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hσ M J hJ (AF F)
  have := htg
  have := hlcH
  have := hscH
  have := ht2H
  have := hbH
  obtain ⟨hcount, U, hU, hUd⟩ := rational_countable_discrete F E σ hσ M J hJ
  have := hcount
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hmem : ∀ γ : HA (AF F) σ J, γ ∈ Γ → HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J :=
    fun γ hγ => Subgroup.mem_subgroupOf.1 hγ
  obtain ⟨-, D, hD, hDs⟩ := GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete
    (HA (AF F) σ J) Γ ⟨U, hU, fun γ hγ hγU => hUd γ hγU (hmem γ hγ)⟩
  have hfd : ∀ μ : Measure (HA (AF F) σ J), IsFDH F E σ M J μ D := fun μ =>
    IsFundamentalDomain.mk' hD.nullMeasurableSet hDs
  refine ⟨⟨Measure.haar, inferInstanceAs (Measure.IsHaarMeasure _)⟩, fun μ hμ => ?_⟩
  have : μ.IsHaarMeasure := hμ
  refine ⟨⟨D, hfd μ⟩, ⟨D, hD, hfd μ, fun h => ?_⟩, fun 𝓕 h𝓕 => ?_⟩
  · obtain ⟨γ, hγ, -⟩ := hDs h
    exact ⟨γ, hmem _ γ.2, hγ⟩
  · have : MeasurableConstSMul (HFinIn (AF F) σ J) (HA (AF F) σ J) :=
      ⟨fun c => (continuous_const.mul continuous_id :
        Continuous fun x : HA (AF F) σ J => (show HA (AF F) σ J from c.1) * x).measurable⟩
    have : SMulInvariantMeasure (HFinIn (AF F) σ J) (HA (AF F) σ J) μ :=
      ⟨fun c s hs => measure_preimage_mul μ (show HA (AF F) σ J from c.1) s⟩
    have h𝓕' : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ := h𝓕
    exact h𝓕'.measure_ne_zero (NeZero.ne μ)

end GlobalTheory.CompanionTheory.SW
