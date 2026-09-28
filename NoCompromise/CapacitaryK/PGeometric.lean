import NoCompromise.CapacitaryK.SlabH
import NoCompromise.CapacitaryK.LevelNull
import NoCompromise.CapacitaryK.SlabFInput

/-!
# `lem:K-slab-H`, `lem:K-slab-F`, `lem:K-p-geometric` and `def:K-Fhat` (chapter 31)

* `K_slab_H`: for regular values `a < b` whose slab `U ∩ {a < u < b}` has compact closure in `U`,
  `μ{a < u < b} = ∫_{u=b} Hw dH² - ∫_{u=a} Hw dH²` (`eq:K-slab-H`), combining
  `K_slab_H_of_gauss_green` with Gauss-Green on the regular slab (`slab_gauss_green`).
* `K_p_geometric_of_harmonic`: `p(t) = ∫_{u=t} Hw dH²` at every regular value `t ∈ (0,1)`
  (`eq:K-p-geometric`), when all slabs of `(0,1)` have compact closure in `U`.
* `K_slab_F`: `F(b) - F(a) = ∫_{a<u<b} ∇w·∇u = ∫_a^b ∫_{u=t} Hw dH² dt` (`eq:K-slab-F`).
* `KFhat_eq_levelF`: the canonical `F̂` of `def:K-Fhat` is `∫_{u=t} w² dH²` at every regular value.

The hypothesis `hslabs` (every slab `U ∩ {a < u < b}`, `0 < a < b < 1`, has compact closure in
`U = ℝ³ ∖ K`) is a property of the capacitary potential (`u → 0` at infinity, `u → 1` at `K`).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Gradient RealInnerProductSpace ENNReal

namespace LiquidDrop.CapacitaryK

/-- The geometric level integral `∫_{u=t} H w dH²`. -/
def levelP (U : Set E3) (u : E3 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in U ∩ u ⁻¹' {t}, meanCurv u x * gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2)

/-- `lem:K-slab-H`. -/
theorem K_slab_H {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0) {μ : Measure E3}
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    {a b : ℝ} (hab : a < b) (hK : IsCompact (closure (U ∩ u ⁻¹' Ioo a b)))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    (μ (U ∩ u ⁻¹' Ioo a b)).toReal = levelP U u b - levelP U u a :=
  K_slab_H_of_gauss_green hU hu hΔ hμK hμ hab (hK.isBounded.subset subset_closure) hcl hreg
    (fun {_} hV hSV {_} hX => slab_gauss_green hU (hu.of_le (by norm_num)) hab
      (hK.isBounded.subset subset_closure) hcl hreg hV hSV hX)

/-- `lem:K-p-geometric`: with base value `p(t₀) = ∫_{u=t₀} Hw` at a regular base level, the
representative `p = Kp` of `def:K-p` equals `∫_{u=t} Hw dH²` at every regular value `t ∈ (0,1)`. -/
theorem K_p_geometric_of_harmonic {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0) :
    ∀ t, (∀ x ∈ U, u x = t → gradient u x ≠ 0) → 0 < t → t < 1 →
      Kp μ u t₀ (levelP U u t₀) t = levelP U u t := by
  refine K_p_geometric_of_slab hU humeas hu hΔ hμU hμK hμ ht₀ ht₀R ?_
  intro a b ha hb h0 hab h1
  obtain ⟨hK, hcl⟩ := hslabs a b h0 hab h1
  have hU' : μ (u ⁻¹' Ioo a b) = μ (U ∩ u ⁻¹' Ioo a b) := by
    apply le_antisymm
    · calc μ (u ⁻¹' Ioo a b) ≤ μ (U ∩ u ⁻¹' Ioo a b ∪ Uᶜ) := by
            apply measure_mono
            intro x hx
            by_cases hxU : x ∈ U
            · exact Or.inl ⟨hxU, hx⟩
            · exact Or.inr hxU
        _ ≤ μ (U ∩ u ⁻¹' Ioo a b) + μ Uᶜ := measure_union_le _ _
        _ = μ (U ∩ u ⁻¹' Ioo a b) := by rw [hμU, add_zero]
    · exact measure_mono inter_subset_right
  rw [hU']
  exact K_slab_H hU hu hΔ hμK hμ hab hK hcl (fun x hx h => h.elim (ha x hx) (hb x hx))

/-- The geometric level integral `F(t) = ∫_{u=t} w² dH²` (`def:K-F`). -/
def levelF (U : Set E3) (u : E3 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in U ∩ u ⁻¹' {t}, gradNorm u x ^ 2 ∂(Measure.euclideanHausdorffMeasure 2)

/-- On a level, the regular part carries all of `∫ Hw` since `Hw = 0` where `w = 0`. -/
lemma levelP_eq_regular {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ} (hu : ContinuousOn u U)
    (t : ℝ) :
    levelP U u t = ∫ x in (U ∩ {x | 0 < gradNorm u x}) ∩ u ⁻¹' {t},
      meanCurv u x * gradNorm u x ∂(Measure.euclideanHausdorffMeasure 2) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_coarea_level_of_continuousOn hU.measurableSet hu t)
  · exact fun x hx => ⟨hx.1.1, hx.2⟩
  · intro x hx
    have hw : ¬ 0 < gradNorm u x := fun hw => hx.2 ⟨⟨hx.1.1, hw⟩, hx.1.2⟩
    have hz : gradNorm u x = 0 := le_antisymm (not_lt.mp hw) (gradNorm_nonneg u x)
    rw [hz, mul_zero]

/-- `lem:K-slab-F` (`eq:K-slab-F`): for regular values `a < b` whose slab has compact closure
in `U`, `F(b) - F(a) = ∫_{a<u<b} ∇w·∇u dx = ∫_a^b ∫_{u=t} Hw dH² dt`. -/
theorem K_slab_F {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {a b : ℝ} (hab : a < b) (hK : IsCompact (closure (U ∩ u ⁻¹' Ioo a b)))
    (hcl : closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    (hreg : ∀ x ∈ U, (u x = a ∨ u x = b) → gradient u x ≠ 0) :
    levelF U u b - levelF U u a =
        ∫ x in U ∩ u ⁻¹' Ioo a b, ⟪gradient (gradNorm u) x, gradient u x⟫ ∧
      ∫ x in U ∩ u ⁻¹' Ioo a b, ⟪gradient (gradNorm u) x, gradient u x⟫ =
        ∫ t in Ioo a b, levelP U u t := by
  have hS : MeasurableSet (U ∩ u ⁻¹' Ioo a b) :=
    (hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioo).measurableSet
  refine ⟨K_slab_F_gauss_green_of_gauss_green hU hu hΔ hab (hK.isBounded.subset subset_closure)
    hcl hreg (fun {_} hV hSV {_} hX => slab_gauss_green hU (hu.of_le (by norm_num)) hab
      (hK.isBounded.subset subset_closure) hcl hreg hV hSV hX), ?_⟩
  rw [K_slab_F_coarea hU hu hΔ (integrableOn_inner_gradient_gradNorm hU hu hS hK hcl)]
  exact setIntegral_congr_fun measurableSet_Ioo
    (fun t _ => (levelP_eq_regular hU hu.continuousOn t).symm)

/-- `def:K-Fhat`: with base values `p(t₀) = ∫_{u=t₀} Hw` and `F(t₀) = ∫_{u=t₀} w²` at a regular
base level, `F̂(t) = ∫_{u=t} w² dH²` at every regular value `t ∈ (0,1)` (`lem:K-slab-F`,
`lem:K-p-geometric`, and `thm:sard-3d` for the a.e. identification `p = ∫ Hw`). -/
theorem KFhat_eq_levelF {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (humeas : Measurable u) (hu : ContDiffOn ℝ 3 u U) (hΔ : ∀ x ∈ U, laplacianN u x = 0)
    {μ : Measure E3} (hμU : μ Uᶜ = 0)
    (hμK : ∀ K : Set E3, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ φ : E3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        ∫ x, gradNorm u x * laplacianN φ x = ∫ x, φ x ∂μ)
    (hslabs : ∀ a b, 0 < a → a < b → b < 1 →
      IsCompact (closure (U ∩ u ⁻¹' Ioo a b)) ∧ closure (U ∩ u ⁻¹' Ioo a b) ⊆ U)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : ∀ x ∈ U, u x = t₀ → gradient u x ≠ 0) :
    ∀ t, (∀ x ∈ U, u x = t → gradient u x ≠ 0) → 0 < t → t < 1 →
      KFhat μ u t₀ (levelP U u t₀) (levelF U u t₀) t = levelF U u t := by
  have hae : ∀ᵐ s, s ∈ Ioo (0 : ℝ) 1 → Kp μ u t₀ (levelP U u t₀) s = levelP U u s := by
    have hN := LiquidDrop.sard_three_dimensional_gradient hU hu
    have hnot : ∀ᵐ s ∂volume, s ∉ u '' {x | x ∈ U ∧ gradient u x = 0} :=
      measure_eq_zero_iff_ae_notMem.mp hN
    filter_upwards [hnot] with s hs hs01
    exact K_p_geometric_of_harmonic hU humeas hu hΔ hμU hμK hμ hslabs ht₀ ht₀R s
      (fun x hx hxs h0 => hs ⟨x, ⟨hx, h0⟩, hxs⟩) hs01.1 hs01.2
  have key : ∀ a b, (∀ x ∈ U, u x = a → gradient u x ≠ 0) →
      (∀ x ∈ U, u x = b → gradient u x ≠ 0) → 0 < a → a < b → b < 1 →
      ∫ s in a..b, Kp μ u t₀ (levelP U u t₀) s = levelF U u b - levelF U u a := by
    intro a b ha hb h0 hab h1
    rw [intervalIntegral.integral_of_le hab.le]
    have h1' : ∫ s in Ioc a b, Kp μ u t₀ (levelP U u t₀) s = ∫ s in Ioc a b, levelP U u s := by
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [hae] with s hs hsI
      exact hs ⟨h0.trans hsI.1, hsI.2.trans_lt h1⟩
    rw [h1', setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
    obtain ⟨hK, hcl⟩ := hslabs a b h0 hab h1
    obtain ⟨h1F, h2F⟩ := K_slab_F hU hu hΔ hab hK hcl (fun x hx h => h.elim (ha x hx) (hb x hx))
    rw [h1F, h2F]
  intro t ht h0 h1
  rcases lt_trichotomy t₀ t with h | h | h
  · simp only [KFhat]
    rw [key t₀ t ht₀R ht ht₀.1 h h1]
    ring
  · subst h
    simp [KFhat]
  · simp only [KFhat]
    rw [intervalIntegral.integral_symm, key t t₀ ht ht₀R h0 h ht₀.2]
    ring

/-- Every nonempty open interval of values contains a regular value (`thm:sard-3d`). -/
lemma exists_regular_value_mem {U : Set E3} (hU : IsOpen U) {u : E3 → ℝ}
    (hu : ContDiffOn ℝ 3 u U) {a b : ℝ} (hab : a < b) :
    ∃ s ∈ Ioo a b, ∀ x ∈ U, u x = s → gradient u x ≠ 0 := by
  have hN := LiquidDrop.sard_three_dimensional_gradient hU hu
  by_contra h
  push Not at h
  have hsub : Ioo a b ⊆ u '' {x | x ∈ U ∧ gradient u x = 0} := by
    intro s hs
    obtain ⟨x, hx, hxs, h0⟩ := h s hs
    exact ⟨x, ⟨hx, h0⟩, hxs⟩
  have h0 := measure_mono_null hsub hN
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

end LiquidDrop.CapacitaryK
