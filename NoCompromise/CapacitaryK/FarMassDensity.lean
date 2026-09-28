import NoCompromise.CapacitaryK.PotentialAssembly
import NoCompromise.CapacitaryK.MuRegular

/-!
# The far-region mass of `μ = Δ|∇u|` as a translated volume integral

For the capacitary potential and a translation vector `z`, if `|∇u| > 0` on the far region
`{‖y‖ ≥ R}` (translated by `z`) and the translated sublevel `{y | u (y + z) ≤ t}` lies in that far
region, then `μ{0 < u ≤ t} = ∫_{u(y+z) ≤ t} Δ|∇u|(y + z) dy` (`K_mu_restrict_regular`).
This is the volume form of `p(t)` used for `eq:K-p-expansion`.
-/

noncomputable section
open Real Set Filter MeasureTheory Topology Asymptotics Metric
open scoped Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- `laplacianN` of any function is measurable (finite sums of `fderiv` evaluations). -/
theorem measurable_laplacianN (f : E3 → ℝ) : Measurable (laplacianN f) := by
  unfold laplacianN
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_fderiv_apply_const ℝ _ _

/-- The capacitary potential is positive everywhere. -/
theorem capacitary_pos_everywhere
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) (x : E3) : 0 < u x := by
  by_cases hx : x ∈ K
  · rw [hb x hx]; exact one_pos
  · exact ((capacitary_signs hK hzero hu hh hb hinf).1 x hx).1

/-- The far-region `μ`-mass as a translated volume integral of `Δ|∇u|`. -/
theorem capacitary_far_mass_eq_translated_integral
    {K : Set E3} (hK : IsCompact K) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0))
    {μ : Measure E3}
    (hμK : ∀ L : Set E3, IsCompact L → L ⊆ Kᶜ → μ L < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Kᶜ →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (z : E3) {R t : ℝ} (ht1 : t < 1)
    (hreg : ∀ y : E3, R ≤ ‖y‖ → 0 < gradNorm u (y + z))
    (hfar : ∀ y : E3, u (y + z) ≤ t → R ≤ ‖y‖)
    (hint : IntegrableOn (fun y => laplacianN (gradNorm u) (y + z)) {y | u (y + z) ≤ t}) :
    (μ (u ⁻¹' Ioc 0 t)).toReal = ∫ y in {y | u (y + z) ≤ t}, laplacianN (gradNorm u) (y + z) := by
  have hpos := capacitary_pos_everywhere hK hzero hu hh hb hinf
  have hU : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hu3 : ContDiffOn ℝ 3 u Kᶜ := (capacitary_potential_contDiffOn hK hu hh).of_le (by norm_num)
  have hΔ := kelvin_laplacianN_eq_zero_of_distributional hU hu.continuousOn hh
  set V := Kᶜ ∩ {x | 0 < gradNorm u x} with hV
  set Aset := u ⁻¹' Iic t with hA
  have hAeq : u ⁻¹' Ioc 0 t = Aset := by
    ext x; simp only [mem_preimage, mem_Ioc, mem_Iic, Aset]
    exact ⟨fun h => h.2, fun h => ⟨hpos x, h⟩⟩
  have hAm : MeasurableSet Aset := measurableSet_Iic.preimage hu.measurable
  have hAV : Aset ⊆ V := by
    intro x hx
    have hx0 : u x ≤ t := hx
    have hx' : u ((x - z) + z) ≤ t := by simpa using hx0
    refine ⟨fun hxK => ?_, ?_⟩
    · have : u x = 1 := hb x hxK
      simp only [Aset, mem_preimage, mem_Iic] at hx
      linarith
    · have := hreg (x - z) (hfar (x - z) hx')
      simpa using this
  have hpre : (fun y => y + z) ⁻¹' Aset = {y | u (y + z) ≤ t} := rfl
  have hmp : MeasurePreserving (fun y : E3 => y + z) volume volume :=
    measurePreserving_add_right volume z
  have hemb : MeasurableEmbedding (fun y : E3 => y + z) := measurableEmbedding_addRight z
  -- integrability on the untranslated set
  have hintA : IntegrableOn (laplacianN (gradNorm u)) Aset := by
    rw [← hpre] at hint
    exact (hmp.integrableOn_comp_preimage hemb).mp hint
  have htrans : ∫ y in {y | u (y + z) ≤ t}, laplacianN (gradNorm u) (y + z) =
      ∫ x in Aset, laplacianN (gradNorm u) x := by
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hemb _ _
  have hnn : ∀ x ∈ Aset, 0 ≤ laplacianN (gradNorm u) x := by
    intro x hx
    have hxV := hAV hx
    apply laplacianN_gradNorm_nonneg_of_pos (hu3.contDiffAt (hU.mem_nhds hxV.1)) _ hxV.2
    filter_upwards [hU.mem_nhds hxV.1] with y hy
    exact hΔ y hy
  have hrestr := K_mu_restrict_regular hU hu3 hΔ hμK hμ
  have hmass : μ Aset = ENNReal.ofReal (∫ x in Aset, laplacianN (gradNorm u) x) := by
    have h1 : μ Aset = μ.restrict V Aset := by
      rw [Measure.restrict_apply hAm, inter_eq_left.mpr hAV]
    rw [h1, hV, hrestr, withDensity_apply _ hAm, Measure.restrict_restrict hAm,
      inter_eq_left.mpr hAV]
    rw [ofReal_integral_eq_lintegral_ofReal hintA]
    filter_upwards [ae_restrict_mem hAm] with x hx
    exact hnn x hx
  rw [hAeq, hmass, htrans, ENNReal.toReal_ofReal
    (setIntegral_nonneg hAm (fun x hx => hnn x hx))]

end LiquidDrop.CapacitaryK
