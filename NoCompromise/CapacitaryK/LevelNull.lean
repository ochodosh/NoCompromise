import NoCompromise.CapacitaryK.PushforwardDensity
import NoCompromise.CapacitaryK.Representatives

/-!
# Regular levels carry no `μ`-mass (chapter 31, input to `lem:K-slab-H` and `lem:K-p-geometric`)

* `volume_regular_level_eq_zero`: the regular part `U ∩ {w > 0} ∩ {u = t}` of any level of a
  `C¹` function is Lebesgue-null (coarea formula `cor:coarea-L1` with integrand `1`).
* `K_mu_level_null`: for `μ = Δ|∇u|` (`prop:K-mu`) and a regular value `t` (no critical point of
  `u` in `U` on `{u = t}`), `μ {u = t} = 0`: on the regular set `μ = Δw dx` and the level is
  Lebesgue-null, while the critical part of `u_#μ` vanishes on sets of regular values
  (`lem:K-pushforward-density`).
* `K_p_geometric_of_slab`: `lem:K-p-geometric` with the null-level hypothesis discharged.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology Gradient ENNReal

namespace LiquidDrop.CapacitaryK

/-- The regular part of a level set of a `C¹` function on an open set is Lebesgue-null. -/
theorem volume_regular_level_eq_zero {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (t : ℝ) :
    volume ((U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t}) = 0 := by
  set A := (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t} with hAdef
  have hAm : MeasurableSet A :=
    measurableSet_regular_inter_preimage hU hu (measurableSet_singleton t)
  have hn : ∀ n : ℕ, volume (A ∩ closedBall (0 : E3) n) = 0 := by
    intro n
    set An := A ∩ closedBall (0 : E3) n
    have hAnm : MeasurableSet An := hAm.inter measurableSet_closedBall
    have hfin : volume An < ⊤ :=
      (measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top
    have hint : Integrable (fun _ : E3 => (1 : ℝ)) (volume.restrict An) := by
      have : IsFiniteMeasure (volume.restrict An) := isFiniteMeasure_restrict.mpr hfin.ne
      exact integrable_const _
    obtain ⟨_, _, he⟩ := coarea_L1_nullMeasurable (by norm_num : 2 ≤ 3) hU
      (hu.of_le (by norm_num)) hAnm.nullMeasurableSet
      (fun x hx => hx.1.1.1) hint
    have hcut : An ∩ {x | 0 < ‖gradient u x‖} = An := by
      apply inter_eq_left.mpr
      intro x hx
      exact hx.1.1.2
    rw [hcut] at he
    have hzero : (fun s : ℝ => ∫ x in An ∩ u ⁻¹' {s},
        (1 : ℝ) / ‖gradient u x‖ ∂Measure.euclideanHausdorffMeasure (3 - 1)) =ᵐ[volume] 0 := by
      have hne : ∀ᵐ s : ℝ, s ≠ t := by
        rw [ae_iff]
        simp
      filter_upwards [hne] with s hs
      have hempty : An ∩ u ⁻¹' {s} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨⟨_, hxt⟩, _⟩, hxs⟩
        exact hs ((mem_singleton_iff.mp hxs).symm.trans (mem_singleton_iff.mp hxt))
      rw [Pi.zero_apply, hempty, Measure.restrict_empty, integral_zero_measure]
    rw [integral_congr_ae hzero] at he
    simp only [Pi.zero_apply, integral_zero, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ] at he
    have := (ENNReal.toReal_eq_zero_iff _).mp he
    rcases this with h | h
    · exact h
    · exact absurd h hfin.ne
  have hcover : A = ⋃ n : ℕ, A ∩ closedBall (0 : E3) n := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall, dist_zero_right]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
      exact ⟨n, hx, hn⟩
    · rintro ⟨_, hx, _⟩
      exact hx
  rw [hcover]
  exact measure_iUnion_null hn

/-- `μ {u = t} = 0` at a regular value `t` (input to `lem:K-slab-H`, `lem:K-p-geometric`). -/
theorem K_mu_level_null {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t : ℝ} (ht : ∀ x ∈ U, u x = t → gradient u x ≠ 0) :
    μ (u ⁻¹' {t}) = 0 := by
  obtain ⟨_, hsplit, hcrit, _⟩ := K_pushforward_density hU hu hΔ hμU hμK hμ
  rw [hsplit {t} (measurableSet_singleton t),
    hcrit {t} (fun x hx hxt => ht x hx (mem_singleton_iff.mp hxt)), add_zero,
    K_mu_regular_inter_eq hU hu hΔ hμK hμ]
  exact setLIntegral_measure_zero _ _ (volume_regular_level_eq_zero hU hu t)

/-- `lem:K-p-geometric` with the null-level input discharged by `K_mu_level_null`: if the slab
identity `μ{a < u < b} = G b - G a` holds for regular values `0 < a < b < 1`, then
`p(t) = G(t)` at every regular value `t ∈ (0,1)`, where `p = Kp μ u t₀ (G t₀)` for a regular
base level `t₀`. -/
theorem K_p_geometric_of_slab {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (humeas : Measurable u)
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {t₀ : ℝ} {G : ℝ → ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (hslab : ∀ a b, (∀ x ∈ U, u x = a → gradient u x ≠ 0) →
      (∀ x ∈ U, u x = b → gradient u x ≠ 0) → 0 < a → a < b → b < 1 →
      (μ (u ⁻¹' Ioo a b)).toReal = G b - G a) :
    ∀ t, (∀ x ∈ U, u x = t → gradient u x ≠ 0) → 0 < t → t < 1 →
      Kp μ u t₀ (G t₀) t = G t :=
  K_p_geometric (R := {t | ∀ x ∈ U, u x = t → gradient u x ≠ 0}) humeas ht₀ ht₀R
    (fun a b ha hb h0 hab h1 => hslab a b ha hb h0 hab h1)
    (fun _ ht _ _ => K_mu_level_null hU hu hΔ hμU hμK hμ ht)

end LiquidDrop.CapacitaryK
