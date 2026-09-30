module

public import NoCompromise.CapacitaryK.PushforwardDensity

@[expose] public section

/-!
# The lower density of `u_#μ` (chapter 31, density input of `prop:K-measure-inequality`)

From `lem:K-pushforward-density`: the level integral
`D(t) = ∫_{u=t, w>0} Δw / w dH²` (`= ∫(|A|² + |∇_Σ log w|²)` by `laplacianN_gradNorm_div_eq`)
is nonnegative and locally integrable on `(0,1)`, and a Borel representative `d` of it is a lower
density of `u_#μ` on `(0,1)`: `∫_{(a,b]} d ≤ (u_#μ)(a,b]`. This is the hypothesis pair
`hdmeas`, `hdens` of `K_measure_inequality` / `capacitary_inequalities_of_expansions`.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- The level integral of `Δw / w` over the regular part of `{u = t}`. -/
def levelDensity (U : Set E3) (u : E3 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
    laplacianN (gradNorm u) x / gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)

/-- `levelDensity` is integrable on slabs of finite `μ`-mass (coarea formula). -/
lemma integrableOn_levelDensity {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hfin : μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' B) ≠ ⊤) :
    IntegrableOn (levelDensity U u) B := by
  set R := U ∩ {x | 0 < gradNorm u x} with hRdef
  have hA := measurableSet_regular_inter_preimage hU hu hB
  have hnonneg : ∀ x ∈ R, 0 ≤ laplacianN (gradNorm u) x := by
    intro x hx
    apply laplacianN_gradNorm_nonneg_of_pos (hu.contDiffAt (hU.mem_nhds hx.1)) _ hx.2
    filter_upwards [hU.mem_nhds hx.1] with y hy
    exact hΔ y hy
  have hc : ContinuousOn (laplacianN (gradNorm u)) R :=
    continuousOn_laplacianN_gradNorm_regular (isOpen_regularSet hU hu) (hu.mono inter_subset_left)
      (fun _ hx => hx.2)
  have hmeas : AEStronglyMeasurable (laplacianN (gradNorm u)) (volume.restrict (R ∩ u ⁻¹' B)) :=
    (hc.mono inter_subset_left).aestronglyMeasurable hA
  have hnn : 0 ≤ᵐ[volume.restrict (R ∩ u ⁻¹' B)] laplacianN (gradNorm u) := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact hnonneg x hx.1
  have hint : IntegrableOn (laplacianN (gradNorm u)) (R ∩ u ⁻¹' B) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn, ← K_mu_regular_inter_eq hU hu hΔ hμK hμ (u ⁻¹' B)]
    exact lt_top_iff_ne_top.mpr hfin
  obtain ⟨_, hI, _⟩ := coarea_L1_nullMeasurable (by norm_num : 2 ≤ 3) hU
    (hu.of_le (by norm_num)) hA.nullMeasurableSet (fun _ hx => hx.1.1) hint
  have hcut : (R ∩ u ⁻¹' B) ∩ {x | 0 < ‖gradient u x‖} = R ∩ u ⁻¹' B :=
    inter_eq_left.mpr (fun _ hx => hx.1.2)
  rw [hcut] at hI
  have heq : (fun t : ℝ => ∫ x in (R ∩ u ⁻¹' B) ∩ u ⁻¹' {t},
      laplacianN (gradNorm u) x / ‖gradient u x‖ ∂Measure.euclideanHausdorffMeasure (3 - 1)) =
      B.indicator (levelDensity U u) := by
    funext t
    by_cases ht : t ∈ B
    · rw [indicator_of_mem ht]
      have hset : (R ∩ u ⁻¹' B) ∩ u ⁻¹' {t} = R ∩ u ⁻¹' {t} := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hx, _⟩, hxt⟩
          exact ⟨hx, hxt⟩
        · rintro ⟨hx, hxt⟩
          exact ⟨⟨hx, hxt ▸ ht⟩, hxt⟩
      rw [hset]
      rfl
    · rw [indicator_of_notMem ht]
      have hset : (R ∩ u ⁻¹' B) ∩ u ⁻¹' {t} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨_, hxB⟩, hxt⟩
        exact ht ((mem_singleton_iff.mp hxt) ▸ hxB)
      rw [hset, Measure.restrict_empty, integral_zero_measure]
  rw [heq] at hI
  exact (integrable_indicator_iff hB).mp hI

/-- `levelDensity` is nonnegative. -/
lemma levelDensity_nonneg {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) (t : ℝ) :
    0 ≤ levelDensity U u t := by
  apply setIntegral_nonneg (measurableSet_regular_inter_preimage hU hu (measurableSet_singleton t))
  intro x hx
  apply div_nonneg _ (gradNorm_nonneg u x)
  apply laplacianN_gradNorm_nonneg_of_pos (hu.contDiffAt (hU.mem_nhds hx.1.1)) _ hx.1.2
  filter_upwards [hU.mem_nhds hx.1.1] with y hy
  exact hΔ y hy

/-- Density input of `prop:K-measure-inequality`: a Borel representative `d` of `levelDensity`
on `(0,1)` is a lower density of `u_#μ` there. -/
theorem K_pushforward_lower_density {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤) :
    ∃ d : ℝ → ℝ, Measurable d ∧
      (∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → d t = levelDensity U u t) ∧
      ∀ a b, 0 < a → a ≤ b → b < 1 →
        ∫⁻ t in Ioc a b, ENNReal.ofReal (d t) ≤ (μ.map u) (Ioc a b) := by
  have hsub : ∀ a b, 0 < a → a ≤ b → b < 1 →
      μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' Ioc a b) ≤ μ (u ⁻¹' Ioc a b) :=
    fun _ _ _ _ _ => measure_mono inter_subset_right
  have hfin' : ∀ a b, 0 < a → a ≤ b → b < 1 →
      μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' Ioc a b) ≠ ⊤ :=
    fun a b ha hab hb => ne_top_of_le_ne_top (hfin a b ha hab hb) (hsub a b ha hab hb)
  have hint : ∀ a b, 0 < a → a ≤ b → b < 1 → IntegrableOn (levelDensity U u) (Ioc a b) :=
    fun a b ha hab hb =>
      integrableOn_levelDensity hU hu hΔ hμK hμ measurableSet_Ioc (hfin' a b ha hab hb)
  have hloc : LocallyIntegrableOn (levelDensity U u) (Ioo (0 : ℝ) 1) := by
    intro x hx
    refine ⟨Ioc (x / 2) ((1 + x) / 2), ?_, hint _ _ (by linarith [hx.1]) (by linarith [hx.2])
      (by linarith [hx.2])⟩
    apply mem_nhdsWithin_of_mem_nhds
    exact mem_of_superset (Ioo_mem_nhds (by linarith [hx.1]) (by linarith [hx.2]))
      Ioo_subset_Ioc_self
  have hm := hloc.aestronglyMeasurable
  refine ⟨hm.mk _, hm.stronglyMeasurable_mk.measurable, ?_, ?_⟩
  · have h := hm.ae_eq_mk
    rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo] at h
    filter_upwards [h] with t ht ht01
    exact (ht ht01).symm
  · intro a b ha hab hb
    have hIoc : Ioc a b ⊆ Ioo (0 : ℝ) 1 :=
      fun t ht => ⟨lt_trans ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    have hae : levelDensity U u =ᵐ[volume.restrict (Ioc a b)] hm.mk _ :=
      ae_restrict_of_ae_restrict_of_subset hIoc hm.ae_eq_mk
    have hae' : (fun t => ENNReal.ofReal (hm.mk _ t)) =ᵐ[volume.restrict (Ioc a b)]
        fun t => ENNReal.ofReal (levelDensity U u t) := by
      filter_upwards [hae] with t ht
      rw [ht]
    rw [lintegral_congr_ae hae',
      ← ofReal_integral_eq_lintegral_ofReal (hint a b ha hab hb)
        (ae_of_all _ (levelDensity_nonneg hU hu hΔ)),
      Measure.map_apply humeas measurableSet_Ioc]
    obtain ⟨hdens, _, _, _⟩ := K_pushforward_density hU hu hΔ hμU hμK hμ
    have he := hdens (Ioc a b) measurableSet_Ioc (hfin' a b ha hab hb)
    change (μ (U ∩ {x | 0 < gradNorm u x} ∩ u ⁻¹' Ioc a b)).toReal =
      ∫ t in Ioc a b, levelDensity U u t at he
    rw [← he, ENNReal.ofReal_toReal (hfin' a b ha hab hb)]
    exact hsub a b ha hab hb

end LiquidDrop.CapacitaryK
