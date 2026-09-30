module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import NoCompromise.Surface.MorseSectors

@[expose] public section

/-!
# The two ends of an orbit

Pure topology used for `lem:merge-disjoint`. A curve `γ : ℝ → X` in a compact set `L`,
whose range accumulates at a point `p` it never meets, whose other accumulation points lie on
the curve, which is locally an arc, and which satisfies orbit uniqueness, is injective and
tends to `p` at both ends. In the planar Morse model, two ends of an injective curve cannot
both run into `0` along the same ray, and a preconnected subset of the union of the four rays
lies in one ray.
-/

namespace LiquidDrop

open Set Filter Topology

/-- A curve with the local-arc property, injective, tends to `p` along any filter `l` which
eventually leaves every bounded open interval. -/
theorem orbit_tendsto_of_injective {X : Type*} [MetricSpace X] {L : Set X} (hL : IsCompact L)
    {p : X} {γ : ℝ → X} (hinj : Function.Injective γ) (hγL : ∀ t, γ t ∈ L)
    (hclosed : ∀ q ∈ L, q ≠ p → q ∈ closure (Set.range γ) → q ∈ Set.range γ)
    (harc : ∀ t₀ : ℝ, ∀ ε > 0, ∃ V : Set X, IsOpen V ∧ γ t₀ ∈ V ∧
      ∀ y ∈ V ∩ L, ∃ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), γ t = y)
    {l : Filter ℝ} (hl : ∀ a b : ℝ, ∀ᶠ t in l, t ∉ Set.Ioo a b) :
    Filter.Tendsto γ l (𝓝 p) := by
  rw [tendsto_nhds]
  intro W hWo hpW
  by_contra hne
  have hfr : ∃ᶠ t in l, γ t ∉ W := Filter.not_eventually.mp hne
  set F := l ⊓ 𝓟 {t | γ t ∉ W} with hF
  have : F.NeBot := Filter.frequently_iff_neBot.mp hfr
  have hle : Filter.map γ F ≤ 𝓟 (L \ W) :=
    Filter.tendsto_principal.2
      (Filter.mem_inf_of_right (Filter.mem_principal.2 (fun t ht => ⟨hγL t, ht⟩)))
  obtain ⟨q, ⟨hqL, hqW⟩, hq⟩ := (hL.diff hWo).exists_clusterPt hle
  have hqp : q ≠ p := fun h => hqW (h ▸ hpW)
  have hqcl : q ∈ closure (Set.range γ) := by
    rw [mem_closure_iff_clusterPt]
    exact hq.mono (Filter.tendsto_principal.2 (Filter.Eventually.of_forall
      fun t => Set.mem_range_self t))
  obtain ⟨t₀, rfl⟩ := hclosed q hqL hqp hqcl
  obtain ⟨V, hVo, hqV, hV⟩ := harc t₀ 1 one_pos
  have h1 : ∃ᶠ y in Filter.map γ F, y ∈ V := hq.frequently (hVo.mem_nhds hqV)
  have h2 : ∃ᶠ t in l, γ t ∈ V :=
    (Filter.frequently_map.mp h1).filter_mono inf_le_left
  obtain ⟨t, htV, htI⟩ := (h2.and_eventually (hl (t₀ - 1) (t₀ + 1))).exists
  obtain ⟨s, hs, hst⟩ := hV (γ t) ⟨htV, hγL t⟩
  exact htI (hinj hst ▸ hs)

/-- The orbit through a point: injective, and both ends tend to `p`. -/
theorem orbit_injective_tendsto {X : Type*} [MetricSpace X] {L : Set X} (hL : IsCompact L)
    {p : X} {γ : ℝ → X} (hγc : Continuous γ) (hγL : ∀ t, γ t ∈ L) (hγp : ∀ t, γ t ≠ p)
    (hp : p ∈ closure (Set.range γ))
    (hclosed : ∀ q ∈ L, q ≠ p → q ∈ closure (Set.range γ) → q ∈ Set.range γ)
    (harc : ∀ t₀ : ℝ, ∀ ε > 0, ∃ V : Set X, IsOpen V ∧ γ t₀ ∈ V ∧
      ∀ y ∈ V ∩ L, ∃ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), γ t = y)
    (hper : ∀ t₁ t₂, γ t₁ = γ t₂ → ∀ s, γ (t₁ + s) = γ (t₂ + s)) :
    Function.Injective γ ∧ Filter.Tendsto γ Filter.atTop (𝓝 p) ∧
      Filter.Tendsto γ Filter.atBot (𝓝 p) := by
  have hinj : Function.Injective γ := by
    intro t₁ t₂ h
    by_contra hne
    have hP : Function.Periodic γ (t₂ - t₁) := by
      intro u
      have := hper t₁ t₂ h (u - t₁)
      rw [show t₁ + (u - t₁) = u by ring,
        show t₂ + (u - t₁) = u + (t₂ - t₁) by ring] at this
      exact this.symm
    have hT : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hcpt : IsCompact (Set.range γ) := hP.compact_of_continuous hT hγc
    rw [hcpt.isClosed.closure_eq] at hp
    obtain ⟨t, ht⟩ := hp
    exact hγp t ht
  refine ⟨hinj, ?_, ?_⟩
  · refine orbit_tendsto_of_injective hL hinj hγL hclosed harc (fun a b => ?_)
    filter_upwards [Filter.eventually_ge_atTop b] with t ht h using (not_le.mpr h.2) ht
  · refine orbit_tendsto_of_injective hL hinj hγL hclosed harc (fun a b => ?_)
    filter_upwards [Filter.eventually_le_atBot a] with t ht h using (not_le.mpr h.1) ht

local notation "E2" => EuclideanSpace ℝ (Fin 2)

private lemma ray_cases {ρ : ℝ} {R : Set E2}
    (hR : R = morseRay1 ρ ∨ R = morseRay2 ρ ∨ R = morseRay3 ρ ∨ R = morseRay4 ρ) :
    ∃ a b : ℝ, (a = 1 ∨ a = -1) ∧ (b = 1 ∨ b = -1) ∧
      ∀ x ∈ R, x 1 = b * x 0 ∧ 0 < a * x 0 := by
  rcases hR with rfl | rfl | rfl | rfl
  · exact ⟨1, 1, by norm_num, by norm_num,
      fun x hx => ⟨by rw [hx.2.1]; ring, by linarith [hx.2.2]⟩⟩
  · exact ⟨-1, -1, by norm_num, by norm_num,
      fun x hx => ⟨by rw [hx.2.1]; ring, by linarith [hx.2.2]⟩⟩
  · exact ⟨-1, 1, by norm_num, by norm_num,
      fun x hx => ⟨by rw [hx.2.1]; ring, by linarith [hx.2.2]⟩⟩
  · exact ⟨1, -1, by norm_num, by norm_num,
      fun x hx => ⟨by rw [hx.2.1]; ring, by linarith [hx.2.2]⟩⟩

/-- On a model ray, the first coordinate is nonzero and a point is determined by `|x 0|`. -/
theorem ray_coord_ne_zero_and_eq {ρ : ℝ} {R : Set E2}
    (hR : R = morseRay1 ρ ∨ R = morseRay2 ρ ∨ R = morseRay3 ρ ∨ R = morseRay4 ρ) :
    (∀ x ∈ R, x 0 ≠ 0) ∧ ∀ x ∈ R, ∀ y ∈ R, |x 0| = |y 0| → x = y := by
  obtain ⟨a, b, ha, hb, h⟩ := ray_cases hR
  refine ⟨fun x hx h0 => by have := (h x hx).2; rw [h0, mul_zero] at this; exact lt_irrefl _ this,
    fun x hx y hy hxy => ?_⟩
  obtain ⟨hx1, hx0⟩ := h x hx
  obtain ⟨hy1, hy0⟩ := h y hy
  have h0 : x 0 = y 0 := by
    rcases abs_eq_abs.mp hxy with e | e
    · exact e
    · exfalso
      rw [e] at hx0
      nlinarith
  have h1 : x 1 = y 1 := by rw [hx1, hy1, h0]
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Two ends of an injective curve cannot run into `0` along the same model ray. -/
theorem not_both_ends_same_ray {ρ : ℝ} {β : ℝ → E2} {T₀ T₁ : ℝ} (hT : T₀ < T₁)
    (hinj : Set.InjOn β (Set.Iic T₀ ∪ Set.Ici T₁))
    (hc₀ : ContinuousOn β (Set.Iic T₀)) (hc₁ : ContinuousOn β (Set.Ici T₁))
    (hbot : Filter.Tendsto β Filter.atBot (𝓝 0)) (htop : Filter.Tendsto β Filter.atTop (𝓝 0))
    (R : Set E2)
    (hR : R = morseRay1 ρ ∨ R = morseRay2 ρ ∨ R = morseRay3 ρ ∨ R = morseRay4 ρ)
    (h₀ : ∀ t ≤ T₀, β t ∈ R) (h₁ : ∀ t ≥ T₁, β t ∈ R) : False := by
  obtain ⟨hne, heq⟩ := ray_coord_ne_zero_and_eq hR
  set u : ℝ → ℝ := fun t => |β t 0| with hu
  have c0 : Continuous (fun x : E2 => |x 0|) := (PiLp.continuous_apply _ _ _).abs
  have hu₀ : ContinuousOn u (Set.Iic T₀) := c0.comp_continuousOn hc₀
  have hu₁ : ContinuousOn u (Set.Ici T₁) := c0.comp_continuousOn hc₁
  have hlim : Filter.Tendsto (fun x : E2 => |x 0|) (𝓝 0) (𝓝 0) := by
    simpa using c0.tendsto (0 : E2)
  have hbot' : Filter.Tendsto u Filter.atBot (𝓝 0) := hlim.comp hbot
  have htop' : Filter.Tendsto u Filter.atTop (𝓝 0) := hlim.comp htop
  have hpos₀ : 0 < u T₀ := abs_pos.mpr (hne _ (h₀ T₀ le_rfl))
  have hpos₁ : 0 < u T₁ := abs_pos.mpr (hne _ (h₁ T₁ le_rfl))
  set s₀ := min (u T₀) (u T₁) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hs₀0 : s₀ < u T₀ := by
    have := min_le_left (u T₀) (u T₁); rw [hs₀]; linarith [lt_min hpos₀ hpos₁]
  have hs₀1 : s₀ < u T₁ := by
    have := min_le_right (u T₀) (u T₁); rw [hs₀]; linarith [lt_min hpos₀ hpos₁]
  obtain ⟨a, ha, haT⟩ := ((hbot'.eventually (gt_mem_nhds hs₀pos)).and
    (Filter.eventually_le_atBot T₀)).exists
  obtain ⟨b, hb, hbT⟩ := ((htop'.eventually (gt_mem_nhds hs₀pos)).and
    (Filter.eventually_ge_atTop T₁)).exists
  obtain ⟨t, ht, hts⟩ := intermediate_value_Icc haT (hu₀.mono fun x hx => hx.2)
    ⟨ha.le, hs₀0.le⟩
  obtain ⟨t', ht', hts'⟩ := intermediate_value_Icc' hbT (hu₁.mono fun x hx => hx.1)
    ⟨hb.le, hs₀1.le⟩
  have hβ : β t = β t' :=
    heq _ (h₀ t ht.2) _ (h₁ t' ht'.1) (by simp only [hu] at hts hts'; rw [hts, hts'])
  have := hinj (Or.inl ht.2) (Or.inr ht'.1) hβ
  linarith [ht.2, ht'.1]

/-- A preconnected subset of the union of the four model rays lies in one ray. -/
theorem subset_ray_of_isPreconnected {ρ : ℝ} {C : Set E2} (hC : IsPreconnected C)
    (hsub : C ⊆ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ) :
    C ⊆ morseRay1 ρ ∨ C ⊆ morseRay2 ρ ∨ C ⊆ morseRay3 ρ ∨ C ⊆ morseRay4 ρ := by
  have c0 : Continuous (fun x : E2 => x 0) := PiLp.continuous_apply _ _ _
  have c1 : Continuous (fun x : E2 => x 1) := PiLp.continuous_apply _ _ _
  have hd : ∀ f : E2 → ℝ, Disjoint {x | 0 < f x} {x | f x < 0} := fun f =>
    Set.disjoint_left.2 fun x (h1 : 0 < f x) (h2 : f x < 0) => lt_asymm h1 h2
  have hs0 : C ⊆ {x | 0 < x 0} ∪ {x | x 0 < 0} := by
    intro x hx
    rcases hsub hx with ((h | h) | h) | h
    all_goals first
      | exact Or.inl h.2.2
      | exact Or.inr h.2.2
  have hs1 : C ⊆ {x | 0 < x 1} ∪ {x | x 1 < 0} := by
    intro x hx
    rcases hsub hx with ((h | h) | h) | h
    · exact Or.inl (show 0 < x 1 by linarith [h.2.1, h.2.2])
    · exact Or.inl (show 0 < x 1 by linarith [h.2.1, h.2.2])
    · exact Or.inr (show x 1 < 0 by linarith [h.2.1, h.2.2])
    · exact Or.inr (show x 1 < 0 by linarith [h.2.1, h.2.2])
  rcases hC.subset_or_subset (isOpen_lt continuous_const c0) (isOpen_lt c0 continuous_const)
      (hd _) hs0 with h0 | h0 <;>
  rcases hC.subset_or_subset (isOpen_lt continuous_const c1) (isOpen_lt c1 continuous_const)
      (hd _) hs1 with h1 | h1
  · refine Or.inl fun x hx => ?_
    have a0 : 0 < x 0 := h0 hx
    have a1 : 0 < x 1 := h1 hx
    rcases hsub hx with ((h | h) | h) | h
    · exact h
    all_goals (exfalso; have := h.2.1; have := h.2.2; linarith)
  · refine Or.inr (Or.inr (Or.inr fun x hx => ?_))
    have a0 : 0 < x 0 := h0 hx
    have a1 : x 1 < 0 := h1 hx
    rcases hsub hx with ((h | h) | h) | h
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exact h
  · refine Or.inr (Or.inl fun x hx => ?_)
    have a0 : x 0 < 0 := h0 hx
    have a1 : 0 < x 1 := h1 hx
    rcases hsub hx with ((h | h) | h) | h
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exact h
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exfalso; have := h.2.1; have := h.2.2; linarith
  · refine Or.inr (Or.inr (Or.inl fun x hx => ?_))
    have a0 : x 0 < 0 := h0 hx
    have a1 : x 1 < 0 := h1 hx
    rcases hsub hx with ((h | h) | h) | h
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exfalso; have := h.2.1; have := h.2.2; linarith
    · exact h
    · exfalso; have := h.2.1; have := h.2.2; linarith

end LiquidDrop
