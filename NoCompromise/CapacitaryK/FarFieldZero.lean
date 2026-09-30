module

public import NoCompromise.CapacitaryK.CapacitaryHarmonic
public import NoCompromise.Capacity.KelvinLevels

@[expose] public section

/-!
# Vanishing of F at the far field (chapter 31)

The input `F(0+) = 0` to `lem:K-far-field` / `eq:K-far-field-limits`.
Flux conservation and quadratic gradient decay give a quadratic bound for the
geometric level integral and hence the zero limit of its canonical representative.
The capacitary specialization obtains the gradient decay from the positive Kelvin
expansion and the lower reciprocal-distance barrier.
-/

noncomputable section

open Real Set Filter MeasureTheory Topology InnerProductSpace Metric
open scoped Gradient ENNReal RealInnerProductSpace

namespace LiquidDrop.CapacitaryK

/-- A twice continuously differentiable function has a C¹ gradient. -/
lemma farField_contDiffAt_gradient {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) : ContDiffAt ℝ 1 (gradient f) x :=
  (toDual ℝ E3).symm.contDiff.contDiffAt.comp x (hf.fderiv_right (by norm_num))

/-- The divergence of the gradient agrees with the coordinate Laplacian. -/
lemma farField_vecDiv_gradient {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) : vecDiv (gradient f) x = laplacianN f x := by
  classical
  unfold vecDiv laplacianN
  apply Finset.sum_congr rfl
  intro i _
  have hd := (farField_contDiffAt_gradient hf).differentiableAt one_ne_zero
  have he : (fun y => gradient f y i) = poissonCoordinateDerivative i f := by
    funext y
    exact (poissonCoordinateDerivative_eq_gradient i f y).symm
  rw [← he]
  have hh := ((EuclideanSpace.proj i).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  exact (congrArg (fun L : E3 →L[ℝ] ℝ => L (basisVec i)) hh).symm

/-- Harmonic flux is conserved between the boundary levels of a compact regular slab. -/
theorem level_flux_eq {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {a b : ℝ} (hab : a < b)
    (hK : IsCompact (closure (U ∩ u ⁻¹' Ioo a b)))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    (∫ x in U ∩ u ⁻¹' {a}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)) =
      ∫ x in U ∩ u ⁻¹' {b}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  have hX : ContDiffOn ℝ 1 (gradient u) U := fun x hx =>
    (farField_contDiffAt_gradient
      ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))).contDiffWithinAt
  have hGG := slab_gauss_green hU (hu.of_le (by norm_num)) hab
    (hK.isBounded.subset subset_closure) hcl hreg hU hcl hX
  have hdiv : (∫ x in U ∩ u ⁻¹' Ioo a b, vecDiv (gradient u) x) = 0 := by
    calc
      _ = ∫ x in U ∩ u ⁻¹' Ioo a b, (0 : ℝ) :=
        setIntegral_congr_fun
          (hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo).measurableSet
          (fun x hx => (farField_vecDiv_gradient
            ((hu.contDiffAt (hU.mem_nhds hx.1)).of_le (by norm_num))).trans (hΔ x hx.1))
      _ = 0 := by simp
  have hi (x : E3) : ⟪gradient u x, gradient u x⟫ / gradNorm u x = gradNorm u x := by
    rw [real_inner_self_eq_norm_sq]
    change ‖gradient u x‖ ^ 2 / ‖gradient u x‖ = ‖gradient u x‖
    by_cases hx : ‖gradient u x‖ = 0
    · simp [hx]
    · field_simp
  simp_rw [hi] at hGG
  rw [hdiv] at hGG
  linarith

/-- A uniform gradient bound on a regular level bounds its squared-gradient integral
by that bound times the harmonic flux. -/
theorem levelF_le_mul_flux {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t M : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hreg : ∀ x ∈ U, u x = t → gradient u x ≠ 0)
    (hbound : ∀ x ∈ U ∩ u ⁻¹' {t}, gradNorm u x ≤ M) :
    levelF U u t ≤
      M * ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  obtain ⟨b, hb, hbR⟩ := exists_regular_value_mem hU hu ht1
  obtain ⟨hK, hcl⟩ := hslabs t b ht hb.1 hb.2
  have hregab : ∀ x ∈ U, (u x = t ∨ u x = b) → gradient u x ≠ 0 :=
    fun x hx h => h.elim (hreg x hx) (hbR x hx)
  have hw : ContinuousOn (gradNorm u) (U ∩ u ⁻¹' {t}) :=
    (continuousOn_gradNorm hU hu).mono inter_subset_left
  have hi := slab_level_integrableOn hU (hu.of_le (by norm_num)) hb.1
    (hK.isBounded.subset subset_closure) hcl hregab (Or.inl rfl) hw
  have hi2 := slab_level_integrableOn hU (hu.of_le (by norm_num)) hb.1
    (hK.isBounded.subset subset_closure) hcl hregab (Or.inl rfl) (hw.pow 2)
  rw [← integral_const_mul]
  apply setIntegral_mono_on hi2 (hi.const_mul M)
    (measurableSet_coarea_level_of_continuousOn hU.measurableSet hu.continuousOn t)
  intro x hx
  have hnn : 0 ≤ gradNorm u x := norm_nonneg _
  change gradNorm u x ^ 2 ≤ M * gradNorm u x
  nlinarith [hbound x hx]

/-- Quadratic decay of the gradient on small levels gives a uniform quadratic
bound for the geometric squared-gradient integral. -/
theorem levelF_small_bound_of_decay {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (t₁ : ℝ) (ht₁ : 0 < t₁ ∧ t₁ < 1) (M : ℝ)
    (hsmall : ∀ x ∈ U, u x < t₁ → gradient u x ≠ 0 ∧ gradNorm u x ≤ M * u x ^ 2) :
    ∃ C : ℝ, ∀ t, 0 < t → t < t₁ →
      0 ≤ levelF U u t ∧ levelF U u t ≤ C * t ^ 2 := by
  let Φ : ℝ → ℝ := fun t =>
    ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)
  have hs : 0 < t₁ / 2 ∧ t₁ / 2 < t₁ := by constructor <;> linarith [ht₁.1]
  have hreg (t : ℝ) (ht : t < t₁) : ∀ x ∈ U, u x = t → gradient u x ≠ 0 := by
    intro x hx he
    exact (hsmall x hx (he ▸ ht)).1
  have hflux (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < t₁) : Φ a = Φ b := by
    obtain ⟨hK, hcl⟩ := hslabs a b ha hab (hb.trans ht₁.2)
    exact level_flux_eq hU hu hΔ hab hK hcl
      (fun x hx he => he.elim (hreg a (hab.trans hb) x hx) (hreg b hb x hx))
  refine ⟨M * Φ (t₁ / 2), ?_⟩
  intro t ht htt
  have he : Φ t = Φ (t₁ / 2) := by
    rcases lt_trichotomy t (t₁ / 2) with h | h | h
    · exact hflux t (t₁ / 2) ht h hs.2
    · rw [h]
    · exact (hflux (t₁ / 2) t hs.1 h htt).symm
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hb := levelF_le_mul_flux hU hu hslabs ht (htt.trans ht₁.2) (hreg t htt)
    (M := M * t ^ 2) (fun x hx => by
      have hx' : u x = t := hx.2
      simpa only [hx'] using (hsmall x hx.1 (hx' ▸ htt)).2)
  change levelF U u t ≤ (M * t ^ 2) * Φ t at hb
  rw [he] at hb
  nlinarith [hb]

/-- The far-field input `F(0+) = 0` for the canonical representative based at
any regular level, under quadratic small-level gradient decay. -/
theorem KFhat_tendsto_zero_of_decay {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (_hlevels : ∀ t, 0 < t → t < 1 →
      u ⁻¹' {t} ⊆ U ∧ IsCompact (u ⁻¹' {t}) ∧ (u ⁻¹' {t}).Nonempty)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0)
    (t₁ : ℝ) (ht₁ : 0 < t₁ ∧ t₁ < 1) (M : ℝ)
    (hsmall : ∀ x ∈ U, u x < t₁ → gradient u x ≠ 0 ∧ gradNorm u x ≤ M * u x ^ 2) :
    Tendsto (KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := levelF_small_bound_of_decay hU hu hΔ hslabs t₁ ht₁ M hsmall
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ t < t₁ :=
    (eventually_mem_nhdsWithin).and ((eventually_lt_nhds ht₁.1).filter_mono nhdsWithin_le_nhds)
  have hlim : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id.pow 2)).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hev] with t ht
    rw [KFhat_eq_levelF hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      (fun x hx he => (hsmall x hx (he ▸ ht.2)).1) ht.1 (ht.2.trans ht₁.2)]
    exact (hC t ht.1 ht.2).1
  · filter_upwards [hev] with t ht
    rw [KFhat_eq_levelF hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R t
      (fun x hx he => (hsmall x hx (he ▸ ht.2)).1) ht.1 (ht.2.trans ht₁.2)]
    exact (hC t ht.1 ht.2).2

/-- The Kelvin expansion and the lower barrier give regularity and quadratic
gradient decay on all sufficiently small capacitary levels. -/
theorem capacitary_small_level_decay
    {K : Set E3} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E3) ∈ interior K)
    {u : E3 → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E3) (𝓝 0)) :
    ∃ t₁ ∈ Ioo (0 : ℝ) 1, ∃ M : ℝ,
      ∀ x ∈ Kᶜ, u x < t₁ → gradient u x ≠ 0 ∧ gradNorm u x ≤ M * u x ^ 2 := by
  obtain ⟨a, ha, haK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  have hlower := div_norm_le_of_exterior_harmonic hK ha haK hu hh
    (fun x hx => (hb x hx).ge) hinf
  obtain ⟨Cinf, hC, R, C', hR, hexp⟩ :=
    kelvin_expansion_pos hK hR₀ hKR hzero hu hh hb hinf
  let R' := max R (max 1 (|C'| / Cinf + 1))
  have hRR : R ≤ R' := le_max_left _ _
  have hR1 : 1 ≤ R' := (le_max_left _ _).trans (le_max_right _ _)
  have hRC : |C'| / Cinf + 1 ≤ R' :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hR' : 0 < R' := by linarith
  refine ⟨min (1 / 2) (a / R'), ⟨lt_min (by norm_num) (div_pos ha hR'),
    (min_le_left _ _).trans_lt (by norm_num)⟩, (Cinf + |C'|) / a ^ 2, ?_⟩
  intro x hx hxt
  have hx0 : x ≠ 0 := fun he => hx (he ▸ interior_subset hzero)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hl := hlower x hx
  have hlarge : R' < ‖x‖ := by
    have he := (div_lt_div_iff₀ hn hR').mp
      (hl.trans_lt (hxt.trans_le (min_le_right _ _)))
    nlinarith
  have hn1 : 1 ≤ ‖x‖ := hR1.trans hlarge.le
  have hCn : |C'| < Cinf * ‖x‖ := by
    have hc : |C'| / Cinf < ‖x‖ := by linarith
    have he := (div_lt_iff₀ hC).mp hc
    nlinarith
  have he := (hexp x (hRR.trans hlarge.le)).2
  have hlead : ‖(Cinf / ‖x‖ ^ 3) • x‖ = Cinf / ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ Cinf / ‖x‖ ^ 3)]
    field_simp
  have hC'le : C' ≤ |C'| := le_abs_self _
  have hn2 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos hn
  have hn3 : 0 < ‖x‖ ^ 3 := pow_pos hn 3
  have hratio : Cinf / ‖x‖ ^ 2 * ‖x‖ ^ 3 = Cinf * ‖x‖ := by field_simp
  constructor
  · intro hg
    rw [hg, zero_add, hlead] at he
    have hh := (le_div_iff₀ hn3).mp he
    rw [hratio] at hh
    linarith
  · have hw : gradNorm u x ≤ (Cinf + |C'|) / ‖x‖ ^ 2 := by
      have ht := norm_sub_le (gradient u x + (Cinf / ‖x‖ ^ 3) • x)
        ((Cinf / ‖x‖ ^ 3) • x)
      rw [add_sub_cancel_right, hlead] at ht
      have he' : C' / ‖x‖ ^ 3 ≤ |C'| / ‖x‖ ^ 2 := by
        apply (div_le_div_iff₀ hn3 hn2).mpr
        have hm : |C'| ≤ |C'| * ‖x‖ :=
          le_mul_of_one_le_right (abs_nonneg _) hn1
        have hm' := mul_le_mul_of_nonneg_right (hC'le.trans hm) hn2.le
        nlinarith [hm']
      change ‖gradient u x‖ ≤ _
      rw [add_div]
      linarith
    have hup : 0 < u x := (div_pos ha hn).trans_le hl
    have hasq : a ^ 2 ≤ u x ^ 2 * ‖x‖ ^ 2 := by
      have hal := (div_le_iff₀ hn).mp hl
      have hs := mul_self_le_mul_self ha.le hal
      nlinarith [hs]
    have hsq : a ^ 2 / ‖x‖ ^ 2 ≤ u x ^ 2 := (div_le_iff₀ hn2).mpr hasq
    have hconst : 0 ≤ (Cinf + |C'|) / a ^ 2 := by positivity
    calc
      gradNorm u x ≤ (Cinf + |C'|) / ‖x‖ ^ 2 := hw
      _ = ((Cinf + |C'|) / a ^ 2) * (a ^ 2 / ‖x‖ ^ 2) := by field_simp
      _ ≤ ((Cinf + |C'|) / a ^ 2) * u x ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hconst

end LiquidDrop.CapacitaryK
