module

public import NoCompromise.CapacitaryK.LevelInequality
public import NoCompromise.CapacitaryK.LevelArea
public import NoCompromise.CapacitaryK.FromLevels

@[expose] public section

/-!
# `thm:capacitary-inequalities` for the harmonic `u` (chapter 31, assembly)

All level-set inputs of `capacitary_inequalities_of_p_expansion` are discharged: the canonical
`p`, `F` agree with `∫ Hw`, `∫ w²` at regular levels (`K_p_geometric_of_harmonic`,
`KFhat_eq_levelF`), regular values have full measure (`thm:sard-3d`), and each regular level
satisfies `eq:K-measure-ineq-pointwise` (`K_level_inequality`). The remaining hypotheses are the
properties of the capacitary potential (`hslabs`, `hlevels`), the two named external inputs of
`lem:K-gauss-bonnet-input`, `F(0+) = 0` with `eq:K-p-expansion`, and the endpoint limits.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `thm:capacitary-inequalities` (`eq:capacitary-inequalities`) for the harmonic `u` with the
canonical `p`, `F` based at a regular level `t₀`. -/
theorem capacitary_inequalities_of_harmonic {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hlevels : ∀ t, 0 < t → t < 1 →
      u ⁻¹' {t} ⊆ U ∧ IsCompact (u ⁻¹' {t}) ∧ (u ⁻¹' {t}).Nonempty)
    (h_of_level_connected : ∀ s : ℝ, 0 < s → s < 1 → (∀ x ∈ u ⁻¹' {s}, gradient u x ≠ 0) →
      IsConnected (u ⁻¹' {s}))
    (h_of_total_curvature_bound : ∀ (S : Set E3) (n : E3 → E3), IsCompact S → IsConnected S →
      IsSmoothEmbeddedSurface S → IsUnitNormalField S n →
      ∫ x in S, gaussCurvature S n x ∂(Measure.euclideanHausdorffMeasure 2) ≤ 4 * Real.pi)
    {t₀ F1 p1 : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (hF0 : Tendsto (KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀)) (𝓝[>] 0) (𝓝 0))
    (hpexp : (fun t => Kp μ u t₀ (levelP U u t₀) t - 8 * π * t) =O[𝓝[>] 0] (fun t => t ^ 4))
    (hF1 : Tendsto (KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀)) (𝓝[<] 1) (𝓝 F1))
    (hp1 : Tendsto (Kp μ u t₀ (levelP U u t₀)) (𝓝[<] 1) (𝓝 p1)) :
    4 * π ≤ F1 ∧ 4 * F1 - 8 * π ≤ p1 := by
  refine capacitary_inequalities_of_p_expansion hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ?_ hF0
    hpexp hF1 hp1
  have hN := LiquidDrop.sard_three_dimensional_gradient hU hu
  have hnot : ∀ᵐ s ∂volume, s ∉ u '' {x | x ∈ U ∧ gradient u x = 0} :=
    measure_eq_zero_iff_ae_notMem.mp hN
  filter_upwards [hnot] with t ht h01
  have hR : ∀ x ∈ U, u x = t → gradient u x ≠ 0 := fun x hx hxt h0 => ht ⟨x, ⟨hx, h0⟩, hxt⟩
  obtain ⟨hsub, hcpt, hne⟩ := hlevels t h01.1 h01.2
  have hreg' : ∀ x ∈ u ⁻¹' {t}, gradient u x ≠ 0 := fun x hx => hR x (hsub hx) hx
  have hset : U ∩ u ⁻¹' {t} = u ⁻¹' {t} := inter_eq_right.mpr hsub
  obtain ⟨b, hb, hbR⟩ := exists_regular_value_mem hU hu h01.2
  obtain ⟨hK, hcl⟩ := hslabs t b h01.1 hb.1 hb.2
  have hregab : ∀ x ∈ U, (u x = t ∨ u x = b) → gradient u x ≠ 0 :=
    fun x hx h => h.elim (hR x hx) (hbR x hx)
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hbdd := hK.isBounded.subset subset_closure
  have hfin' := (slab_level_measure_lt_top hU hu1 hb.1 hbdd hcl hregab).1
  have hfin : Measure.euclideanHausdorffMeasure 2 (u ⁻¹' {t}) < ⊤ := by rwa [hset] at hfin'
  have hFpos : 0 < levelF U u t := by
    obtain ⟨x₀, hx₀⟩ := hne
    have hapos := level_measure_pos hU hu1 (hsub hx₀) hx₀ (hreg' x₀ hx₀)
    have hwc : ContinuousOn (fun x => gradNorm u x ^ 2) (U ∩ u ⁻¹' {t}) :=
      ((continuousOn_gradNorm hU hu).mono inter_subset_left).pow 2
    have hLc : IsCompact (U ∩ u ⁻¹' {t}) := by rwa [hset]
    obtain ⟨y, hy, hymin⟩ := hLc.exists_isMinOn ⟨x₀, hsub hx₀, hx₀⟩ hwc
    have hm : 0 < gradNorm u y ^ 2 := by
      have : 0 < gradNorm u y := norm_pos_iff.mpr (hR y hy.1 hy.2)
      positivity
    have hLm : MeasurableSet (U ∩ u ⁻¹' {t}) :=
      measurableSet_coarea_level_of_continuousOn hU.measurableSet hu.continuousOn t
    have hint := slab_level_integrableOn hU hu1 hb.1 hbdd hcl hregab (Or.inl rfl) hwc
    have hle : ∫ x in U ∩ u ⁻¹' {t}, gradNorm u y ^ 2 ∂(Measure.euclideanHausdorffMeasure 2) ≤
        levelF U u t := by
      apply setIntegral_mono_on _ hint hLm (fun x hx => hymin hx)
      exact integrableOn_const (hfin'.ne)
    refine lt_of_lt_of_le ?_ hle
    rw [setIntegral_const, smul_eq_mul]
    apply mul_pos _ hm
    exact ENNReal.toReal_pos hapos.ne' hfin'.ne
  rw [K_p_geometric_of_harmonic hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t hR h01.1 h01.2,
    KFhat_eq_levelF hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t hR h01.1 h01.2]
  exact K_level_inequality hU hu hΔ h01.1 h01.2 hsub hreg' hcpt hfin hFpos
    h_of_level_connected h_of_total_curvature_bound

end LiquidDrop.CapacitaryK
