import NoCompromise.Capacity.FluxIdentity
import NoCompromise.BV.Rellich
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Lipschitz regularity, local H¹, and finite energy of the capacitary potential

The remaining clauses of blueprint `thm:capacitary-potential`: the potential,
extended by the constant `1` on `K`, is globally Lipschitz, belongs to H¹ on
every bounded open set, and has finite exterior energy
(`eq:capacity-finite-energy`). Boundary regularity is represented explicitly
by `hg : ContDiff ℝ 1 g` and `hug : EqOn u g (closure Kᶜ)`; the C² hypothesis
used elsewhere implies it.

The derivative of `g` is bounded on a large ball by compactness and outside it
by the gradient decay of the potential. On a segment, the first and last
points of `K` split it into two pieces lying in `closure Kᶜ`, where the mean
value inequality applies, and a middle piece on which `u` takes the value `1`
at both ends. Rademacher's theorem supplies the weak gradient, and the decay
`|∇u| ≤ C/|x|²` is dominated by an integrable weight `(1 + |x|)⁻⁴` in ℝ³.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped ENNReal NNReal Gradient
namespace LiquidDrop

/-- The Hilbert gradient and the Fréchet derivative have the same norm. -/
lemma capacitary_norm_gradient_eq_norm_fderiv (f : AmbientSpace → ℝ) (x : AmbientSpace) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  change ‖(toDual ℝ AmbientSpace).symm (fderiv ℝ f x)‖ = _
  exact LinearIsometryEquiv.norm_map _ _

/-- On a parameter interval whose interior maps into `Kᶜ`, the mean value
inequality for the extension controls the oscillation of `u`. -/
lemma capacitary_segment_bound {K : Set AmbientSpace} {u g : AmbientSpace → ℝ}
    (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) {L₀ : ℝ}
    (hL : ∀ z ∈ closure Kᶜ, ‖fderiv ℝ g z‖ ≤ L₀) (x y : AmbientSpace) {s t : ℝ}
    (hst : s ≤ t) (hK : ∀ r ∈ Ioo s t, x + r • (y - x) ∈ Kᶜ) :
    |u (x + s • (y - x)) - u (x + t • (y - x))| ≤ L₀ * ((t - s) * ‖y - x‖) := by
  rcases hst.eq_or_lt with rfl | hlt
  · simp
  let γ : ℝ → AmbientSpace := fun r => x + r • (y - x)
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hsub : γ '' Icc s t ⊆ closure Kᶜ := by
    rw [← closure_Ioo hlt.ne]
    exact (image_closure_subset_closure_image hγc).trans
      (closure_mono (image_subset_iff.mpr hK))
  have hderiv : ∀ r, HasDerivAt (fun r => g (γ r)) (fderiv ℝ g (γ r) (y - x)) r := by
    intro r
    have h1 : HasDerivAt γ (y - x) r :=
      (((hasDerivAt_id r).smul_const (y - x)).const_add x).congr_deriv (one_smul ℝ _)
    exact ((hg.differentiable one_ne_zero) (γ r)).hasFDerivAt.comp_hasDerivAt r h1
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => g (γ r)) (f' := fun r => fderiv ℝ g (γ r) (y - x)) (C := L₀ * ‖y - x‖)
    (fun r _ => (hderiv r).hasDerivWithinAt)
    (fun r hr => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hL _ (hsub ⟨r, Ico_subset_Icc_self hr, rfl⟩))
        (norm_nonneg _)))
    t ⟨hlt.le, le_rfl⟩
  have hs : u (γ s) = g (γ s) := hug (hsub ⟨s, left_mem_Icc.mpr hlt.le, rfl⟩)
  have ht : u (γ t) = g (γ t) := hug (hsub ⟨t, right_mem_Icc.mpr hlt.le, rfl⟩)
  change |u (γ s) - u (γ t)| ≤ _
  rw [hs, ht, abs_sub_comm, ← Real.norm_eq_abs]
  calc _ ≤ L₀ * ‖y - x‖ * (t - s) := hmvt
    _ = _ := by ring

/-- A function equal to `1` on the closed set `K` and to a function with
derivative bounded by `L₀` on `closure Kᶜ` is `L₀`-Lipschitz. -/
lemma capacitary_lipschitz_of_fderiv_bound {K : Set AmbientSpace} (hK : IsClosed K)
    {u g : AmbientSpace → ℝ} (hb : ∀ x ∈ K, u x = 1)
    (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) {L₀ : ℝ} (hL₀ : 0 ≤ L₀)
    (hL : ∀ z ∈ closure Kᶜ, ‖fderiv ℝ g z‖ ≤ L₀) :
    LipschitzWith ⟨L₀, hL₀⟩ u := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  change |u x - u y| ≤ L₀ * dist x y
  rw [dist_eq_norm, ← norm_neg (x - y), neg_sub]
  let S : Set ℝ := Icc 0 1 ∩ (fun r : ℝ => x + r • (y - x)) ⁻¹' K
  have hγc : Continuous (fun r : ℝ => x + r • (y - x)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hS : IsCompact S := isCompact_Icc.inter_right (hK.preimage hγc)
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have h := capacitary_segment_bound hg hug hL x y zero_le_one (fun r hr hrK =>
      Set.eq_empty_iff_forall_notMem.mp hSe r ⟨Ioo_subset_Icc_self hr, hrK⟩)
    simpa using h
  · have ha : sInf S ∈ S := hS.sInf_mem hSne
    have hb' : sSup S ∈ S := hS.sSup_mem hSne
    have hab : sInf S ≤ sSup S := csInf_le_csSup hSne hS.bddBelow hS.bddAbove
    have h1 := capacitary_segment_bound hg hug hL x y ha.1.1 (fun r hr hrK => (not_le.mpr hr.2)
      (csInf_le hS.bddBelow ⟨⟨hr.1.le, hr.2.le.trans ha.1.2⟩, hrK⟩))
    have h2 := capacitary_segment_bound hg hug hL x y hb'.1.2 (fun r hr hrK => (not_le.mpr hr.1)
      (le_csSup hS.bddAbove ⟨⟨hb'.1.1.trans hr.1.le, hr.2.le⟩, hrK⟩))
    have hua : u (x + sInf S • (y - x)) = 1 := hb _ ha.2
    have hub : u (x + sSup S • (y - x)) = 1 := hb _ hb'.2
    rw [hua] at h1
    rw [hub] at h2
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero] at h1 h2
    have htri := abs_sub_le (u x) 1 (u y)
    nlinarith [mul_nonneg (mul_nonneg hL₀ (norm_nonneg (y - x))) (sub_nonneg.mpr hab)]

/-- The derivative of the boundary extension is globally bounded: by
compactness on a large ball, and by the potential's gradient decay outside it. -/
lemma capacitary_fderiv_bound_of_c2_extension {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ z, ‖fderiv ℝ g z‖ ≤ L₀ := by
  obtain ⟨C, -, hd⟩ := potential_decay hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : AmbientSpace) (2 * R₀)).exists_bound_of_continuousOn
    (hg.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max M (|C| / (2 * R₀) ^ 2), le_max_of_le_right (by positivity), fun z => ?_⟩
  rcases le_or_gt ‖z‖ (2 * R₀) with hz | hz
  · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
  · have hzK : z ∈ Kᶜ := fun hzK => by
      have : ‖z‖ ≤ R₀ := by simpa using hKR hzK
      linarith
    rw [← capacitary_norm_gradient_eq_norm_fderiv,
      ← capacity_gradient_eq_of_boundary_C2 hK hug hzK]
    refine le_max_of_le_right ((hd z hz.le).trans ?_)
    calc C / ‖z‖ ^ 2 ≤ |C| / ‖z‖ ^ 2 :=
          div_le_div_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      _ ≤ |C| / (2 * R₀) ^ 2 :=
          div_le_div_of_nonneg_left (abs_nonneg C) (by positivity)
            (pow_le_pow_left₀ (by positivity) hz.le 2)

/-- Blueprint `thm:capacitary-potential`: the potential, extended by `1` on `K`,
is globally Lipschitz, under the named C¹ boundary extension hypothesis. -/
theorem capacitary_lipschitz_of_c2_extension {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    ∃ L : ℝ≥0, LipschitzWith L u := by
  obtain ⟨L₀, hL₀, hL⟩ :=
    capacitary_fderiv_bound_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug
  exact ⟨_, capacitary_lipschitz_of_fderiv_bound hK.isClosed hb hg hug hL₀ (fun z _ => hL z)⟩

/-- Blueprint `thm:capacitary-potential`: the extended potential is H¹ on every
bounded open set, with its Rademacher gradient as weak gradient. -/
theorem capacitary_isH1On_of_c2_extension {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    ∀ U : Set AmbientSpace, IsOpen U → Bornology.IsBounded U → IsH1On u U := by
  obtain ⟨L, hL⟩ := capacitary_lipschitz_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug
  intro U hU hUb
  have : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using hUb.measure_lt_top⟩
  obtain ⟨M, hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hL.continuous.continuousOn
  refine ⟨gradient u, hasWeakGradientOn_of_lipschitz hL U, ?_, ?_⟩
  · apply MemLp.of_bound hL.continuous.measurable.aestronglyMeasurable M
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hM x (subset_closure hx)
  · exact MemLp.of_bound (measurable_gradient u).aestronglyMeasurable (L : ℝ)
      (Eventually.of_forall (norm_gradient_le_of_lipschitz hL))

/-- Blueprint `eq:capacity-finite-energy`: `∫_{ℝ³∖K} |∇u|² < ∞`. The squared
gradient is dominated by a multiple of `(1 + |x|)⁻⁴`. -/
theorem capacitary_finite_energy_of_c2_extension {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    IntegrableOn (fun x => ‖gradient u x‖ ^ 2) Kᶜ := by
  obtain ⟨L, hL⟩ := capacitary_lipschitz_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug
  obtain ⟨C, -, hd⟩ := potential_decay hK hR₀ hKR hzero hu hh hb hinf
  set ρ := max (2 * R₀) 1
  set A := 16 * C ^ 2 + (L : ℝ) ^ 2 * (1 + ρ) ^ 4
  have hint : Integrable (fun x : AmbientSpace => A * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul A
  refine (hint.mono' ((measurable_gradient u).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)).integrableOn
  have hpos : 0 < (1 + ‖x‖) ^ 4 := by positivity
  have h4 : (1 + ‖x‖) ^ (4 : ℝ) = (1 + ‖x‖) ^ (4 : ℕ) := by norm_cast
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (by positivity), h4,
    ← div_eq_mul_inv, le_div_iff₀ hpos]
  have hG := norm_gradient_le_of_lipschitz hL x
  have hA1 : (L : ℝ) ^ 2 * (1 + ρ) ^ 4 ≤ A := le_add_of_nonneg_left (by positivity)
  have hA2 : 16 * C ^ 2 ≤ A := le_add_of_nonneg_right (by positivity)
  rcases le_or_gt ‖x‖ ρ with hx | hx
  · have h1 : ‖gradient u x‖ ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hG 2
    have h2 : (1 + ‖x‖) ^ 4 ≤ (1 + ρ) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    exact (mul_le_mul h1 h2 (by positivity) (by positivity)).trans hA1
  · have hx2 : 2 * R₀ ≤ ‖x‖ := (le_max_left _ _).trans hx.le
    have hx1 : 1 ≤ ‖x‖ := (le_max_right _ _).trans hx.le
    have hxpos : 0 < ‖x‖ := by linarith
    have h1 : ‖gradient u x‖ ≤ |C| / ‖x‖ ^ 2 :=
      (hd x hx2).trans (div_le_div_of_nonneg_right (le_abs_self C) (sq_nonneg _))
    have h1' : ‖gradient u x‖ * ‖x‖ ^ 2 ≤ |C| := by
      rwa [le_div_iff₀ (by positivity)] at h1
    have h2 : (1 + ‖x‖) ^ 4 ≤ 16 * ‖x‖ ^ 4 := by
      calc (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
        _ = 16 * ‖x‖ ^ 4 := by ring
    have h3 : (‖gradient u x‖ * ‖x‖ ^ 2) ^ 2 ≤ |C| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1' 2
    calc ‖gradient u x‖ ^ 2 * (1 + ‖x‖) ^ 4 ≤ ‖gradient u x‖ ^ 2 * (16 * ‖x‖ ^ 4) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 16 * (‖gradient u x‖ * ‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ 16 * C ^ 2 := by rw [← sq_abs C]; linarith
      _ ≤ A := hA2

/-- The exterior energy as a finite lower Lebesgue integral. -/
theorem capacitary_energy_lt_top_of_c2_extension {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    ∫⁻ x in Kᶜ, ‖gradient u x‖ₑ ^ 2 < ⊤ := by
  have h := (capacitary_finite_energy_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg
    hug).hasFiniteIntegral
  unfold HasFiniteIntegral at h
  simpa [enorm_pow] using h

/-- Blueprint `thm:capacitary-potential`, remaining clauses bundled: global
Lipschitz bound, H¹ on bounded open sets, and finite exterior energy. -/
theorem capacitary_potential_h1_energy_of_c2_extension {K : Set AmbientSpace}
    (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀) (hKR : K ⊆ closedBall 0 R₀)
    (hzero : (0 : AmbientSpace) ∈ interior K)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0))
    {g : AmbientSpace → ℝ} (hg : ContDiff ℝ 1 g) (hug : EqOn u g (closure Kᶜ)) :
    (∃ L : ℝ≥0, LipschitzWith L u) ∧
      (∀ U : Set AmbientSpace, IsOpen U → Bornology.IsBounded U → IsH1On u U) ∧
      IntegrableOn (fun x => ‖gradient u x‖ ^ 2) Kᶜ ∧
      ∫⁻ x in Kᶜ, ‖gradient u x‖ₑ ^ 2 < ⊤ :=
  ⟨capacitary_lipschitz_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug,
    capacitary_isH1On_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug,
    capacitary_finite_energy_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug,
    capacitary_energy_lt_top_of_c2_extension hK hR₀ hKR hzero hu hh hb hinf hg hug⟩

end LiquidDrop
