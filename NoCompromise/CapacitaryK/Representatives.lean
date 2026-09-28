import NoCompromise.CapacitaryK.OneDim

/-!
# Canonical BV representatives through critical values (chapter 31)

`def:K-p`, `def:K-Fhat`, `prop:K-structure` and `lem:K-p-geometric` for an arbitrary measure `μ`
on a measurable space `X` and a measurable `u : X → ℝ`, with `μ` finite on the slabs
`{a < u ≤ b}`, `0 < a ≤ b < 1` (in the application `μ = Δ|∇u|` from `prop:K-mu`, and the slabs
`{a ≤ u ≤ b}` are compact subsets of `ℝ³ ∖ K`).

* `Kp μ u t₀ p₀`: `p(t) = p₀ + μ{t₀ < u ≤ t}` for `t ≥ t₀` and `p₀ - μ{t < u ≤ t₀}` for `t < t₀`.
* `KFhat μ u t₀ p₀ F₀`: `F̂(t) = F₀ + ∫_{t₀}^t p`.
* `K_structure`: `p` is nondecreasing and right-continuous on `(0,1)`, locally integrable, `F̂` is
  its primitive (`F̂ ∈ W^{1,1}_loc`, `F̂' = p` a.e.), and `Dp = u_#μ` on `(0,1)` in increment form
  `p b - p a = (u_#μ)(a, b]`. With `p` defined by `eq:K-p`, `Dp = u_#μ` is immediate from
  additivity of `μ`; the blueprint's appeal to regular endpoints and Sard is not needed.
* `K_p_geometric`: given the conclusions of `lem:K-slab-H` (`μ{a < u < b} = G b - G a` for regular
  `a < b`, and `μ{u = t} = 0` for regular `t`), `p(t) = G(t)` at every regular value when
  `p₀ = G(t₀)`; here `G t = ∫_{u=t} Hw dH²`.
-/

noncomputable section
open Real Set Filter MeasureTheory intervalIntegral Topology

namespace LiquidDrop.CapacitaryK

variable {X : Type*} [MeasurableSpace X]

/-- `def:K-p`: the right-continuous representative through the base level `t₀`
with base value `p₀`. -/
def Kp (μ : Measure X) (u : X → ℝ) (t₀ p₀ t : ℝ) : ℝ :=
  if t₀ ≤ t then p₀ + (μ (u ⁻¹' Ioc t₀ t)).toReal else p₀ - (μ (u ⁻¹' Ioc t t₀)).toReal

/-- `def:K-Fhat`. -/
def KFhat (μ : Measure X) (u : X → ℝ) (t₀ p₀ F₀ t : ℝ) : ℝ :=
  F₀ + ∫ s in t₀..t, Kp μ u t₀ p₀ s

lemma Kp_increment {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ p₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Kp μ u t₀ p₀ b - Kp μ u t₀ p₀ a = ((μ.map u) (Ioc a b)).toReal := by
  have hadd : ∀ x y z, 0 < x → x ≤ y → y ≤ z → z < 1 →
      (μ (u ⁻¹' Ioc x z)).toReal =
        (μ (u ⁻¹' Ioc x y)).toReal + (μ (u ⁻¹' Ioc y z)).toReal := by
    intro x y z hx hxy hyz hz
    rw [← Ioc_union_Ioc_eq_Ioc hxy hyz, preimage_union,
      measure_union ((Ioc_disjoint_Ioc_of_le le_rfl).preimage u)
        (hu measurableSet_Ioc), ENNReal.toReal_add
        (hfin x y hx hxy (lt_of_le_of_lt hyz hz))
        (hfin y z (lt_of_lt_of_le hx hxy) hyz hz)]
  rw [Measure.map_apply hu measurableSet_Ioc]
  by_cases hta : t₀ ≤ a
  · have htb := hta.trans hab
    have hh := hadd t₀ a b ht₀.1 hta hab hb
    simp only [Kp, ite_eq_left hta, ite_eq_left htb]
    linarith
  · by_cases htb : t₀ ≤ b
    · have hh := hadd a t₀ b ha (le_of_not_ge hta) htb hb
      simp only [Kp, ite_eq_right hta, ite_eq_left htb]
      linarith
    · have hh := hadd a b t₀ ha hab (le_of_not_ge htb) ht₀.2
      simp only [Kp, ite_eq_right hta, ite_eq_right htb]
      linarith

lemma Kp_monotoneOn {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ p₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤) :
    MonotoneOn (Kp μ u t₀ p₀) (Ioo 0 1) := by
  intro a ha b hb hab
  have he := Kp_increment hu ht₀ hfin ha.1 hab hb.2 (p₀ := p₀)
  have hn := ENNReal.toReal_nonneg (a := (μ.map u) (Ioc a b))
  linarith

lemma Kp_rightContinuous {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ p₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousWithinAt (Kp μ u t₀ p₀) (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have he : (⋂ r > t, Ioc t r) = (∅ : Set ℝ) := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false]
    intro hx
    have hxt := (hx (t + 1) (by linarith)).1
    have := (hx ((t + x) / 2) (by linarith)).2
    linarith
  have hm := tendsto_measure_biInter_gt (μ := μ.map u)
    (s := fun r => Ioc t r) (a := t)
    (fun r hr => measurableSet_Ioc.nullMeasurableSet)
    (fun i j hi hij => Ioc_subset_Ioc_right hij)
    ⟨(t + 1) / 2, by linarith [ht.2], by
      rw [Measure.map_apply hu measurableSet_Ioc]
      exact hfin _ _ ht.1 (by linarith [ht.2]) (by linarith [ht.2])⟩
  rw [he, measure_empty] at hm
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hm
  have hp := (tendsto_const_nhds (x := Kp μ u t₀ p₀ t)).add hr
  simp only [ENNReal.toReal_zero, add_zero] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with r hr hr1
  have := Kp_increment hu ht₀ hfin ht.1 (le_of_lt hr) hr1 (p₀ := p₀)
  dsimp [Function.comp]
  linarith

/-- `prop:K-structure`. -/
theorem K_structure {μ : Measure X} {u : X → ℝ} (hu : Measurable u) {t₀ p₀ F₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hfin : ∀ a b, 0 < a → a ≤ b → b < 1 → μ (u ⁻¹' Ioc a b) ≠ ⊤) :
    MonotoneOn (Kp μ u t₀ p₀) (Ioo 0 1) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt (Kp μ u t₀ p₀) (Ici t) t) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 → IntervalIntegrable (Kp μ u t₀ p₀) volume a b) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      KFhat μ u t₀ p₀ F₀ b - KFhat μ u t₀ p₀ F₀ a = ∫ t in a..b, Kp μ u t₀ p₀ t) ∧
    (∀ᵐ t, t ∈ Ioo (0 : ℝ) 1 → HasDerivAt (KFhat μ u t₀ p₀ F₀) (Kp μ u t₀ p₀ t) t) ∧
    (∀ a b, 0 < a → a ≤ b → b < 1 →
      Kp μ u t₀ p₀ b - Kp μ u t₀ p₀ a = ((μ.map u) (Ioc a b)).toReal) := by
  have hm := Kp_monotoneOn hu ht₀ hfin (p₀ := p₀)
  have hi : ∀ a b, 0 < a → a ≤ b → b < 1 →
      IntervalIntegrable (Kp μ u t₀ p₀) volume a b := by
    intro a b ha hab hb
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hm.mono (fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
  have hbase : ∀ a ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (Kp μ u t₀ p₀) volume t₀ a := by
    intro a ha
    rcases le_total t₀ a with h | h
    · exact hi _ _ ht₀.1 h ha.2
    · exact (hi _ _ ha.1 h ht₀.2).symm
  have hF : ∀ a b, 0 < a → a ≤ b → b < 1 →
      KFhat μ u t₀ p₀ F₀ b - KFhat μ u t₀ p₀ F₀ a = ∫ t in a..b, Kp μ u t₀ p₀ t := by
    intro a b ha hab hb
    have hh := integral_add_adjacent_intervals
      (hbase a ⟨ha, lt_of_le_of_lt hab hb⟩) (hi a b ha hab hb)
    dsimp [KFhat]
    linarith
  refine ⟨hm, fun t ht => Kp_rightContinuous hu ht₀ hfin ht, hi, hF, ?_,
    fun a b ha hab hb => Kp_increment hu ht₀ hfin ha hab hb⟩
  have hc := countable_not_continuousAt_of_monotoneOn hm
  have hae : ∀ᵐ t ∂volume, t ∉ {x ∈ Ioo (0 : ℝ) 1 | ¬ContinuousAt (Kp μ u t₀ p₀) x} :=
    by
      rw [ae_iff]
      simpa only [not_not, Set.mem_ofPred_eq] using hc.measure_zero volume
  filter_upwards [hae] with t ht hti
  exact hasDerivAt_of_primitive hi hF hti.1 hti.2 (by simpa [hti] using ht)

/-- `lem:K-p-geometric`, from the conclusions of `lem:K-slab-H`. -/
theorem K_p_geometric {μ : Measure X} {u : X → ℝ} (hu : Measurable u)
    {t₀ : ℝ} {G : ℝ → ℝ} {R : Set ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (ht₀R : t₀ ∈ R)
    (hslab : ∀ a b, a ∈ R → b ∈ R → 0 < a → a < b → b < 1 →
      (μ (u ⁻¹' Ioo a b)).toReal = G b - G a)
    (hnull : ∀ t ∈ R, 0 < t → t < 1 → μ (u ⁻¹' {t}) = 0) :
    ∀ t ∈ R, 0 < t → t < 1 → Kp μ u t₀ (G t₀) t = G t := by
  have he : ∀ a b, a ∈ R → b ∈ R → 0 < a → a < b → b < 1 →
      (μ (u ⁻¹' Ioc a b)).toReal = G b - G a := by
    intro a b haR hbR ha hab hb
    have hn : (μ.map u) {b} = 0 := by
      rw [Measure.map_apply hu (measurableSet_singleton b)]
      exact hnull b hbR (lt_trans ha hab) hb
    have hm := measure_congr (Ioo_ae_eq_Ioc' (a := a) hn)
    rw [Measure.map_apply hu measurableSet_Ioo, Measure.map_apply hu measurableSet_Ioc] at hm
    rw [← hm]
    exact hslab a b haR hbR ha hab hb
  intro t htR ht0 ht1
  rcases lt_trichotomy t₀ t with h | h | h
  · rw [Kp, ite_eq_left h.le, he t₀ t ht₀R htR ht₀.1 h ht1]
    ring
  · subst t
    simp [Kp]
  · rw [Kp, ite_eq_right (not_le.mpr h), he t t₀ htR ht₀R ht0 h ht₀.2]
    ring

end LiquidDrop.CapacitaryK
