module

public import NoCompromise.Flow.FlowLocalCk

@[expose] public section

/-!
# Maximal integral curves and the `C^k` local flow on an open set

`cor:flow-manifold` for an open subset `U` of a finite-dimensional real space (the
coordinate form of the corollary): for a `C^k` field `X` on `U`, `1 ≤ k ≤ ∞`,

* through every `x ∈ U` there is a unique maximal integral curve
  (`isFlowCurveOn_maxFlow`, `maxFlow_maximal`), defined on the open interval
  `maxFlowInterval X U x ∋ 0`;
* a maximal curve cannot have a finite endpoint while remaining in a compact subset of `U`
  (`mem_maxFlowInterval_of_mem_compact`, `mem_maxFlowInterval_of_mem_compact_backward`);
* the flow domain `maxFlowDomain X U` is open and the maximal flow is `C^k` on it
  (`isOpen_maxFlowDomain_and_contDiffOn`);
* the group law holds wherever both sides are defined (`maxFlow_add`).

The abstract-manifold version is not formalised here.
-/

open Set Filter
open scoped NNReal Topology

namespace LiquidDrop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : E → E} {U : Set E}

/-- `γ` is an integral curve of `X` in `U` through `x`, on the open order-connected
time set `I ∋ 0`. -/
def IsFlowCurveOn (X : E → E) (U : Set E) (x : E) (I : Set ℝ) (γ : ℝ → E) : Prop :=
  IsOpen I ∧ I.OrdConnected ∧ (0 : ℝ) ∈ I ∧ γ 0 = x ∧
    ∀ t ∈ I, γ t ∈ U ∧ HasDerivAt γ (X (γ t)) t

/-- The maximal existence interval of the integral curve of `X` in `U` through `x`: the union
of all open intervals around `0` carrying an integral curve through `x`. -/
def maxFlowInterval (X : E → E) (U : Set E) (x : E) : Set ℝ :=
  {t | ∃ I : Set ℝ, ∃ γ : ℝ → E, IsFlowCurveOn X U x I γ ∧ t ∈ I}

open Classical in
/-- The maximal local flow: the value at time `t` of the maximal integral curve through `x`
(and `x` itself when `t` lies outside the maximal interval). -/
noncomputable def maxFlow (X : E → E) (U : Set E) (t : ℝ) (x : E) : E :=
  if h : ∃ p : Set ℝ × (ℝ → E), IsFlowCurveOn X U x p.1 p.2 ∧ t ∈ p.1
  then (Classical.choose h).2 t else x

/-- The domain of the maximal local flow. -/
def maxFlowDomain (X : E → E) (U : Set E) : Set (ℝ × E) :=
  {q | q.2 ∈ U ∧ q.1 ∈ maxFlowInterval X U q.2}

omit [FiniteDimensional ℝ E] in
theorem isOpen_maxFlowInterval (x : E) : IsOpen (maxFlowInterval X U x) :=
  isOpen_iff_mem_nhds.mpr fun _ ⟨I, γ, h, ht⟩ =>
    mem_of_superset (h.1.mem_nhds ht) fun _ hs => ⟨I, γ, h, hs⟩

omit [FiniteDimensional ℝ E] in
theorem ordConnected_maxFlowInterval (x : E) : (maxFlowInterval X U x).OrdConnected := by
  refine ⟨fun s ⟨I, γ, h, hs⟩ r ⟨I', γ', h', hr⟩ u hu => ?_⟩
  rcases le_total u 0 with hu0 | hu0
  · exact ⟨I, γ, h, h.2.1.out hs h.2.2.1 ⟨hu.1, hu0⟩⟩
  · exact ⟨I', γ', h', h'.2.1.out h'.2.2.1 hr ⟨hu0, hu.2⟩⟩

omit [FiniteDimensional ℝ E] in
/-- Maximality: every integral curve through `x` on an open interval around `0` lives inside
the maximal interval. -/
theorem subset_maxFlowInterval {x : E} {I : Set ℝ} {γ : ℝ → E}
    (h : IsFlowCurveOn X U x I γ) : I ⊆ maxFlowInterval X U x :=
  fun _ ht => ⟨I, γ, h, ht⟩

section C1

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- Two integral curves through `x` agree on the intersection of their intervals. -/
theorem eqOn_of_isFlowCurveOn (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E}
    {I I' : Set ℝ} {γ γ' : ℝ → E} (h : IsFlowCurveOn X U x I γ)
    (h' : IsFlowCurveOn X U x I' γ') : EqOn γ γ' (I ∩ I') :=
  integralCurve_unique_of_contDiffOn hU hX (h.2.1.inter h'.2.1) ⟨h.2.2.1, h'.2.2.1⟩
    (fun t ht => h.2.2.2.2 t ht.1) (fun t ht => h'.2.2.2.2 t ht.2)
    (h.2.2.2.1.trans h'.2.2.2.1.symm)

omit [CompleteSpace E] in
/-- The maximal flow agrees with every integral curve through `x`. -/
theorem maxFlow_eq_of_isFlowCurveOn (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E}
    {I : Set ℝ} {γ : ℝ → E} (h : IsFlowCurveOn X U x I γ) {t : ℝ} (ht : t ∈ I) :
    maxFlow X U t x = γ t := by
  have hex : ∃ p : Set ℝ × (ℝ → E), IsFlowCurveOn X U x p.1 p.2 ∧ t ∈ p.1 :=
    ⟨(I, γ), h, ht⟩
  rw [maxFlow, dite_eq_left hex]
  have hs := Classical.choose_spec hex
  exact eqOn_of_isFlowCurveOn hU hX hs.1 h ⟨hs.2, ht⟩

omit [CompleteSpace E] in
/-- Local existence of an integral curve on a symmetric open interval. -/
theorem exists_isFlowCurveOn (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E} (hx : x ∈ U) :
    ∃ ε > 0, ∃ γ : ℝ → E, IsFlowCurveOn X U x (Ioo (-ε) ε) γ := by
  obtain ⟨ε, hε, h⟩ :=
    exists_integralCurve_local hU hX isCompact_singleton (singleton_subset_iff.mpr hx)
  obtain ⟨γ, hγ0, hγ⟩ := h x rfl
  exact ⟨ε, hε, γ, isOpen_Ioo, ordConnected_Ioo, ⟨by linarith, hε⟩, hγ0, hγ⟩

omit [CompleteSpace E] in
/-- `cor:flow-manifold` (Euclidean form): the maximal integral curve through `x ∈ U` is an
integral curve of `X` in `U` on the open interval `maxFlowInterval X U x ∋ 0`. -/
theorem isFlowCurveOn_maxFlow (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E}
    (hx : x ∈ U) :
    IsFlowCurveOn X U x (maxFlowInterval X U x) (fun t => maxFlow X U t x) := by
  obtain ⟨ε, hε, γ, hγ⟩ := exists_isFlowCurveOn hU hX hx
  refine ⟨isOpen_maxFlowInterval x, ordConnected_maxFlowInterval x,
    ⟨_, γ, hγ, hγ.2.2.1⟩, ?_, ?_⟩
  · change maxFlow X U 0 x = x
    rw [maxFlow_eq_of_isFlowCurveOn hU hX hγ hγ.2.2.1]
    exact hγ.2.2.2.1
  · rintro t ⟨I, σ, hσ, ht⟩
    have heq : ∀ s ∈ I, maxFlow X U s x = σ s :=
      fun s hs => maxFlow_eq_of_isFlowCurveOn hU hX hσ hs
    have hev : (fun s => maxFlow X U s x) =ᶠ[𝓝 t] σ :=
      mem_of_superset (hσ.1.mem_nhds ht) fun s hs => heq s hs
    change maxFlow X U t x ∈ U ∧ HasDerivAt (fun s => maxFlow X U s x) (X (maxFlow X U t x)) t
    rw [heq t ht]
    exact ⟨(hσ.2.2.2.2 t ht).1, (hσ.2.2.2.2 t ht).2.congr_of_eventuallyEq hev⟩

omit [CompleteSpace E] in
/-- `cor:flow-manifold` (Euclidean form), uniqueness and maximality: every integral curve of
`X` in `U` through `x` on an open interval around `0` is a restriction of the maximal one. -/
theorem maxFlow_maximal (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E} {I : Set ℝ}
    {γ : ℝ → E} (h : IsFlowCurveOn X U x I γ) :
    I ⊆ maxFlowInterval X U x ∧ EqOn γ (fun t => maxFlow X U t x) I :=
  ⟨subset_maxFlowInterval h, fun _ ht => (maxFlow_eq_of_isFlowCurveOn hU hX h ht).symm⟩

omit [CompleteSpace E] in
/-- `cor:flow-manifold` (Euclidean form): a maximal curve cannot have a finite right endpoint
while remaining in a compact subset of `U`. -/
theorem mem_maxFlowInterval_of_mem_compact (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {x : E} (hx : x ∈ U) {b : ℝ} (hb : 0 < b)
    (hJ : Ico 0 b ⊆ maxFlowInterval X U x) (hγK : ∀ t ∈ Ico 0 b, maxFlow X U t x ∈ K) :
    b ∈ maxFlowInterval X U x := by
  have hγ := isFlowCurveOn_maxFlow hU hX hx
  obtain ⟨δ, hδ, γ', hγ'γ, hγ'⟩ := integralCurve_extend_of_mem_compact hU hX hK hKU hb
    (γ := fun t => maxFlow X U t x) (fun t ht => ⟨hγK t ht, (hγ.2.2.2.2 t (hJ ht)).2⟩)
  let σ : ℝ → E := fun t => if t < b / 2 then maxFlow X U t x else γ' t
  have hσ1 : EqOn σ (fun t => maxFlow X U t x) (maxFlowInterval X U x ∩ Iio b) := by
    intro t ht
    by_cases htb : t < b / 2
    · simp [σ, htb]
    · simp only [σ, ite_eq_right htb]
      exact hγ'γ ⟨by linarith, ht.2⟩
  have hσ2 : EqOn σ γ' (Ioo 0 (b + δ)) := by
    intro t ht
    by_cases htb : t < b / 2
    · simp only [σ, ite_eq_left htb]
      exact (hγ'γ ⟨ht.1.le, by linarith⟩).symm
    · simp [σ, htb]
  have hIo : IsOpen ((maxFlowInterval X U x ∩ Iio b) ∪ Ioo 0 (b + δ)) :=
    ((isOpen_maxFlowInterval x).inter isOpen_Iio).union isOpen_Ioo
  have h0 : (0 : ℝ) ∈ maxFlowInterval X U x ∩ Iio b := ⟨hγ.2.2.1, hb⟩
  have hI : IsFlowCurveOn X U x ((maxFlowInterval X U x ∩ Iio b) ∪ Ioo 0 (b + δ)) σ := by
    refine ⟨hIo, ?_, Or.inl h0, ?_, ?_⟩
    · rw [← isPreconnected_iff_ordConnected]
      exact IsPreconnected.union (b / 2) ⟨hJ ⟨by linarith, by linarith⟩, show b / 2 < b by linarith⟩
        ⟨by linarith, by linarith⟩
        ((ordConnected_maxFlowInterval x).inter ordConnected_Iio).isPreconnected
        isPreconnected_Ioo
    · rw [hσ1 h0]
      exact hγ.2.2.2.1
    · rintro t (ht | ht)
      · rw [hσ1 ht]
        refine ⟨(hγ.2.2.2.2 t ht.1).1, (hγ.2.2.2.2 t ht.1).2.congr_of_eventuallyEq ?_⟩
        exact mem_of_superset (((isOpen_maxFlowInterval x).inter isOpen_Iio).mem_nhds ht)
          fun s hs => hσ1 hs
      · rw [hσ2 ht]
        exact ⟨(hγ' t ht).1, (hγ' t ht).2.congr_of_eventuallyEq
          (mem_of_superset (isOpen_Ioo.mem_nhds ht) fun s hs => hσ2 hs)⟩
  exact subset_maxFlowInterval hI (Or.inr ⟨hb, by linarith⟩)

omit [CompleteSpace E] in
/-- `cor:flow-manifold` (Euclidean form): a maximal curve cannot have a finite left endpoint
while remaining in a compact subset of `U`. -/
theorem mem_maxFlowInterval_of_mem_compact_backward (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {x : E} (hx : x ∈ U) {b : ℝ} (hb : b < 0)
    (hJ : Ioc b 0 ⊆ maxFlowInterval X U x) (hγK : ∀ t ∈ Ioc b 0, maxFlow X U t x ∈ K) :
    b ∈ maxFlowInterval X U x := by
  have hγ := isFlowCurveOn_maxFlow hU hX hx
  obtain ⟨δ, hδ, γ', hγ'γ, hγ'⟩ := integralCurve_extend_backward_of_mem_compact hU hX hK hKU hb
    (γ := fun t => maxFlow X U t x) (fun t ht => ⟨hγK t ht, (hγ.2.2.2.2 t (hJ ht)).2⟩)
  let σ : ℝ → E := fun t => if b / 2 < t then maxFlow X U t x else γ' t
  have hσ1 : EqOn σ (fun t => maxFlow X U t x) (maxFlowInterval X U x ∩ Ioi b) := by
    intro t ht
    by_cases htb : b / 2 < t
    · simp [σ, htb]
    · simp only [σ, ite_eq_right htb]
      exact hγ'γ ⟨ht.2, by linarith⟩
  have hσ2 : EqOn σ γ' (Ioo (b - δ) 0) := by
    intro t ht
    by_cases htb : b / 2 < t
    · simp only [σ, ite_eq_left htb]
      exact (hγ'γ ⟨by linarith, ht.2.le⟩).symm
    · simp [σ, htb]
  have hIo : IsOpen ((maxFlowInterval X U x ∩ Ioi b) ∪ Ioo (b - δ) 0) :=
    ((isOpen_maxFlowInterval x).inter isOpen_Ioi).union isOpen_Ioo
  have h0 : (0 : ℝ) ∈ maxFlowInterval X U x ∩ Ioi b := ⟨hγ.2.2.1, hb⟩
  have hI : IsFlowCurveOn X U x ((maxFlowInterval X U x ∩ Ioi b) ∪ Ioo (b - δ) 0) σ := by
    refine ⟨hIo, ?_, Or.inl h0, ?_, ?_⟩
    · rw [← isPreconnected_iff_ordConnected]
      exact IsPreconnected.union (b / 2) ⟨hJ ⟨by linarith, by linarith⟩, show b < b / 2 by linarith⟩
        ⟨by linarith, by linarith⟩
        ((ordConnected_maxFlowInterval x).inter ordConnected_Ioi).isPreconnected
        isPreconnected_Ioo
    · rw [hσ1 h0]
      exact hγ.2.2.2.1
    · rintro t (ht | ht)
      · rw [hσ1 ht]
        refine ⟨(hγ.2.2.2.2 t ht.1).1, (hγ.2.2.2.2 t ht.1).2.congr_of_eventuallyEq ?_⟩
        exact mem_of_superset (((isOpen_maxFlowInterval x).inter isOpen_Ioi).mem_nhds ht)
          fun s hs => hσ1 hs
      · rw [hσ2 ht]
        exact ⟨(hγ' t ht).1, (hγ' t ht).2.congr_of_eventuallyEq
          (mem_of_superset (isOpen_Ioo.mem_nhds ht) fun s hs => hσ2 hs)⟩
  exact subset_maxFlowInterval hI (Or.inr ⟨by linarith, hb⟩)

omit [CompleteSpace E] in
/-- `cor:flow-manifold` (Euclidean form), group law wherever both sides are defined:
`s` lies in the maximal interval at `Φ_t(x)` iff `s + t` lies in that at `x`, and then
`Φ_s(Φ_t(x)) = Φ_{s+t}(x)`. -/
theorem maxFlow_add (hU : IsOpen U) (hX : ContDiffOn ℝ 1 X U) {x : E} (hx : x ∈ U) {t : ℝ}
    (ht : t ∈ maxFlowInterval X U x) (s : ℝ) :
    (s ∈ maxFlowInterval X U (maxFlow X U t x) ↔ s + t ∈ maxFlowInterval X U x) ∧
      (s + t ∈ maxFlowInterval X U x →
        maxFlow X U s (maxFlow X U t x) = maxFlow X U (s + t) x) := by
  have hγ := isFlowCurveOn_maxFlow hU hX hx
  have hy : maxFlow X U t x ∈ U := (hγ.2.2.2.2 t ht).1
  have hshift : IsFlowCurveOn X U (maxFlow X U t x)
      ((fun r => r + t) ⁻¹' maxFlowInterval X U x) (fun r => maxFlow X U (r + t) x) := by
    refine ⟨(isOpen_maxFlowInterval x).preimage (continuous_id.add continuous_const),
      ⟨fun a ha b hb r hr => ?_⟩, by simpa using ht, by simp, fun r hr => ?_⟩
    · exact (ordConnected_maxFlowInterval x).out ha hb ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · exact ⟨(hγ.2.2.2.2 _ hr).1, (hγ.2.2.2.2 _ hr).2.comp_add_const r t⟩
  have hm1 := maxFlow_maximal hU hX hshift
  have hγy := isFlowCurveOn_maxFlow hU hX hy
  have hmt : -t + t ∈ maxFlowInterval X U x := by simpa using hγ.2.2.1
  have hback : IsFlowCurveOn X U x
      ((fun r => r - t) ⁻¹' maxFlowInterval X U (maxFlow X U t x))
      (fun r => maxFlow X U (r - t) (maxFlow X U t x)) := by
    refine ⟨(isOpen_maxFlowInterval _).preimage (continuous_id.sub continuous_const),
      ⟨fun a ha b hb r hr => ?_⟩, by simpa using hm1.1 hmt, ?_, fun r hr => ?_⟩
    · exact (ordConnected_maxFlowInterval _).out ha hb ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · have h1 := hm1.2 hmt
      simp only at h1
      change maxFlow X U (0 - t) (maxFlow X U t x) = x
      rw [zero_sub, ← h1, neg_add_cancel]
      exact hγ.2.2.2.1
    · exact ⟨(hγy.2.2.2.2 _ hr).1, (hγy.2.2.2.2 _ hr).2.comp_sub_const r t⟩
  have hm2 := subset_maxFlowInterval hback
  refine ⟨⟨fun hs => hm2 (show s + t - t ∈ _ by simpa using hs), fun hs => hm1.1 hs⟩,
    fun hs => (hm1.2 hs).symm⟩

end C1

private lemma Ioo_subset_thickening_uIcc {a b δ : ℝ} (hδ : 0 < δ) :
    Ioo (min a b - δ) (max a b + δ) ⊆ Metric.thickening δ (uIcc a b) := by
  intro s hs
  rw [Metric.mem_thickening_iff, ← Icc_min_max]
  have hlh : min a b ≤ max a b := min_le_max
  rcases le_or_gt s (min a b) with h1 | h1
  · exact ⟨min a b, ⟨le_rfl, hlh⟩, by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1]⟩
  rcases le_or_gt s (max a b) with h2 | h2
  · exact ⟨s, ⟨h1.le, h2⟩, by simpa using hδ⟩
  · exact ⟨max a b, ⟨hlh, le_rfl⟩, by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.2]⟩

/-- `cor:flow-manifold` (Euclidean form): for a `C^k` field on an open set, `1 ≤ k ≤ ∞`, the
flow domain is open and the maximal local flow `(t, x) ↦ Φ_t(x)` is `C^k` on it. Near each
point of the domain the flow is that of a compactly supported `C^k` localization. -/
theorem isOpen_maxFlowDomain_and_contDiffOn [CompleteSpace E] (hU : IsOpen U) {k : ℕ∞}
    (hk : 1 ≤ k) (hXk : ContDiffOn ℝ k X U) :
    IsOpen (maxFlowDomain X U) ∧
      ContDiffOn ℝ k (fun q : ℝ × E => maxFlow X U q.1 q.2) (maxFlowDomain X U) := by
  have hk' : (1 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hk
  have hX : ContDiffOn ℝ 1 X U := hXk.of_le hk'
  have key : ∀ q₀ ∈ maxFlowDomain X U, ∃ N ∈ 𝓝 q₀, N ⊆ maxFlowDomain X U ∧
      ∃ F : ℝ × E → E, ContDiff ℝ k F ∧
        EqOn (fun q : ℝ × E => maxFlow X U q.1 q.2) F N := by
    rintro ⟨t₀, x₀⟩ ⟨hx₀, ht₀⟩
    have hγ := isFlowCurveOn_maxFlow hU hX hx₀
    have hsub : uIcc 0 t₀ ⊆ maxFlowInterval X U x₀ :=
      (ordConnected_maxFlowInterval x₀).uIcc_subset hγ.2.2.1 ht₀
    have hcont : ContinuousOn (fun t => maxFlow X U t x₀) (uIcc 0 t₀) := fun s hs =>
      (hγ.2.2.2.2 s (hsub hs)).2.continuousAt.continuousWithinAt
    have hK : IsCompact ((fun t => maxFlow X U t x₀) '' uIcc 0 t₀) :=
      isCompact_uIcc.image_of_continuousOn hcont
    have hKU : (fun t => maxFlow X U t x₀) '' uIcc 0 t₀ ⊆ U := by
      rintro _ ⟨s, hs, rfl⟩
      exact (hγ.2.2.2.2 s (hsub hs)).1
    obtain ⟨Y, hY, hYc, V, hVo, hKV, hVU, hYX⟩ :=
      exists_compactSupport_eq_near_contDiff hU hXk hK hKU
    have hY1 : ContDiff ℝ 1 Y := hY.of_le hk'
    obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY1 hYc
    have hΨ : ContDiff ℝ k (fun q : ℝ × E => globalFlow Y hL hM q.1 q.2) :=
      contDiff_globalFlow_uncurry hL hM hk hY
    have hagree : EqOn (fun s => globalFlow Y hL hM s x₀) (fun t => maxFlow X U t x₀)
        (uIcc 0 t₀) :=
      integralCurve_unique_of_contDiffOn isOpen_univ hY1.contDiffOn ordConnected_uIcc
        left_mem_uIcc (fun s _ => ⟨mem_univ _, hasDerivAt_globalFlow hL hM x₀ s⟩)
        (fun s hs => ⟨mem_univ _, by
          have h := (hγ.2.2.2.2 s (hsub hs)).2
          rwa [← hYX (hKV ⟨s, hs, rfl⟩)] at h⟩)
        (by rw [globalFlow_zero]; exact hγ.2.2.2.1.symm)
    have hmapsV : uIcc 0 t₀ ×ˢ {x₀} ⊆
        (fun q : ℝ × E => globalFlow Y hL hM q.1 q.2) ⁻¹' V := by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      obtain rfl : y = x₀ := hy
      change globalFlow Y hL hM s y ∈ V
      rw [show globalFlow Y hL hM s y = maxFlow X U s y from hagree hs]
      exact hKV ⟨s, hs, rfl⟩
    obtain ⟨u, v, hu, hv, hsu, hxv, huv⟩ := generalized_tube_lemma isCompact_uIcc
      isCompact_singleton (hVo.preimage hΨ.continuous) hmapsV
    obtain ⟨δ, hδ, hδu⟩ := isCompact_uIcc.exists_thickening_subset_open hu hsu
    have hIu : Ioo (min 0 t₀ - δ) (max 0 t₀ + δ) ⊆ u :=
      (Ioo_subset_thickening_uIcc hδ).trans hδu
    have hcurve : ∀ x ∈ v ∩ U, IsFlowCurveOn X U x (Ioo (min 0 t₀ - δ) (max 0 t₀ + δ))
        (fun s => globalFlow Y hL hM s x) := by
      intro x hx
      have hin : ∀ s ∈ Ioo (min 0 t₀ - δ) (max 0 t₀ + δ), globalFlow Y hL hM s x ∈ V :=
        fun s hs => huv (mk_mem_prod (hIu hs) hx.1)
      refine ⟨isOpen_Ioo, ordConnected_Ioo, ⟨?_, ?_⟩, globalFlow_zero hL hM x,
        fun s hs => ⟨hVU (hin s hs), ?_⟩⟩
      · linarith [min_le_left 0 t₀]
      · linarith [le_max_left 0 t₀]
      · rw [← hYX (hin s hs)]
        exact hasDerivAt_globalFlow hL hM x s
    have htI : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), t ∈ Ioo (min 0 t₀ - δ) (max 0 t₀ + δ) :=
      fun t ht => ⟨by linarith [min_le_right 0 t₀, ht.1], by linarith [le_max_right 0 t₀, ht.2]⟩
    refine ⟨Ioo (t₀ - δ) (t₀ + δ) ×ˢ (v ∩ U),
      prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
        ((hv.inter hU).mem_nhds ⟨hxv (mem_singleton x₀), hx₀⟩), ?_,
      fun q : ℝ × E => globalFlow Y hL hM q.1 q.2, hΨ, ?_⟩
    · rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact ⟨hx.2, subset_maxFlowInterval (hcurve x hx) (htI t ht)⟩
    · rintro ⟨t, x⟩ ⟨ht, hx⟩
      exact maxFlow_eq_of_isFlowCurveOn hU hX (hcurve x hx) (htI t ht)
  refine ⟨isOpen_iff_mem_nhds.mpr fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨N, hN, hND, -⟩ := key q hq
    exact mem_of_superset hN hND
  · obtain ⟨N, hN, -, F, hF, hEq⟩ := key q hq
    exact (hF.contDiffAt.congr_of_eventuallyEq
      (mem_of_superset hN fun y hy => hEq hy)).contDiffWithinAt

end LiquidDrop
