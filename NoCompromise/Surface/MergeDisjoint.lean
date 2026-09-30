module

public import NoCompromise.Surface.MergeDisjointCore
public import NoCompromise.Surface.LevelArc
public import NoCompromise.Surface.MorseCount
public import NoCompromise.Surface.SublevelClosure

@[expose] public section

/-!
# `lem:merge-disjoint`

A saddle of a Morse function with distinct critical values on a compact embedded surface is not
both sub-merging and super-merging (`blueprint/chapters/14-flows.tex`, `lem:merge-disjoint`).
The orbit of the rotated gradient through a point of the ray `r₁` leaves and returns to the
saddle along two distinct rays; level adjacency is constant along the orbit, and the flanking
relations of the Morse model identify either the two lower or the two upper components.
-/

noncomputable section

open Set Filter Topology Function

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {S : Set E₃}

/-- Components of `N` adjoining `p`, when near `p` the set `N` is covered by two preconnected
subsets `P ∋ a`, `Q ∋ b` of `N`, are the components of `a` or of `b`. -/
theorem connectedComponentIn_eq_or_of_local_cover {N V P Q : Set E₃} {p a b x : E₃}
    (hV : IsOpen V) (hpV : p ∈ V) (hNV : N ∩ V ⊆ P ∪ Q) (hP : IsPreconnected P)
    (hQ : IsPreconnected Q) (hPN : P ⊆ N) (hQN : Q ⊆ N) (ha : a ∈ P) (hb : b ∈ Q)
    (hx : p ∈ closure (connectedComponentIn N x)) :
    connectedComponentIn N x = connectedComponentIn N a ∨
      connectedComponentIn N x = connectedComponentIn N b := by
  obtain ⟨y, hyV, hy⟩ := mem_closure_iff.mp hx V hV hpV
  have hyN := connectedComponentIn_subset N x hy
  rw [connectedComponentIn_eq hy]
  rcases hNV ⟨hyN, hyV⟩ with h | h
  · exact Or.inl (connectedComponentIn_eq (hP.subset_connectedComponentIn ha hPN h)).symm
  · exact Or.inr (connectedComponentIn_eq (hQ.subset_connectedComponentIn hb hQN h)).symm

/-- In the situation of `connectedComponentIn_eq_or_of_local_cover`, two distinct components
adjoining `p` force the components of `a` and `b` to differ. -/
theorem connectedComponentIn_ne_of_local_cover {N V P Q : Set E₃} {p a b : E₃}
    (hV : IsOpen V) (hpV : p ∈ V) (hNV : N ∩ V ⊆ P ∪ Q) (hP : IsPreconnected P)
    (hQ : IsPreconnected Q) (hPN : P ⊆ N) (hQN : Q ⊆ N) (ha : a ∈ P) (hb : b ∈ Q)
    (h2 : ∃ x ∈ N, ∃ y ∈ N, connectedComponentIn N x ≠ connectedComponentIn N y ∧
      p ∈ closure (connectedComponentIn N x) ∧ p ∈ closure (connectedComponentIn N y)) :
    connectedComponentIn N a ≠ connectedComponentIn N b := by
  obtain ⟨x, -, y, -, hne, hx, hy⟩ := h2
  intro hab
  rcases connectedComponentIn_eq_or_of_local_cover hV hpV hNV hP hQ hPN hQN ha hb hx with
    h1 | h1 <;>
  rcases connectedComponentIn_eq_or_of_local_cover hV hpV hNV hP hQ hPN hQN ha hb hy with
    h2 | h2 <;>
  exact hne (by rw [h1, h2] <;> first | exact hab | exact hab.symm)

/-- A preconnected set in `L` avoiding `p` and meeting a curve which is locally an arc of `L`,
and whose accumulation points in `L \ {p}` lie on it, is contained in the curve. -/
theorem subset_range_of_local_arc {X : Type*} [TopologicalSpace X] {L R : Set X} {p : X}
    {γ : ℝ → X} (hclosed : ∀ q ∈ L, q ≠ p → q ∈ closure (Set.range γ) → q ∈ Set.range γ)
    (harc : ∀ t₀ : ℝ, ∀ ε > 0, ∃ V : Set X, IsOpen V ∧ γ t₀ ∈ V ∧
      ∀ y ∈ V ∩ L, ∃ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), γ t = y)
    (hR : IsPreconnected R) (hRL : R ⊆ L) (hpR : p ∉ R) (h0 : γ 0 ∈ R) :
    R ⊆ Set.range γ := by
  set u := ⋃₀ {W : Set X | IsOpen W ∧ W ∩ L ⊆ Set.range γ} with hu_def
  have hu : IsOpen u := isOpen_sUnion fun W hW => hW.1
  have huL : ∀ x ∈ u, x ∈ L → x ∈ Set.range γ := by
    rintro x ⟨W, hW, hxW⟩ hxL
    exact hW.2 ⟨hxW, hxL⟩
  have hru : ∀ t, γ t ∈ u := fun t => by
    obtain ⟨V, hV, htV, hVL⟩ := harc t 1 one_pos
    exact ⟨V, ⟨hV, fun y hy => by obtain ⟨s, -, hs⟩ := hVL y hy; exact ⟨s, hs⟩⟩, htV⟩
  have hcov : R ⊆ u ∪ (closure (Set.range γ))ᶜ := by
    intro x hx
    by_cases hxc : x ∈ closure (Set.range γ)
    · obtain ⟨t, rfl⟩ := hclosed x (hRL hx) (fun e => hpR (e ▸ hx)) hxc
      exact Or.inl (hru t)
    · exact Or.inr hxc
  have hdisj : R ∩ (u ∩ (closure (Set.range γ))ᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, mem_compl_iff]
    rintro ⟨hx, hxu, hxc⟩
    exact hxc (subset_closure (huL x hxu (hRL hx)))
  rcases isPreconnected_iff_subset_of_disjoint.mp hR u (closure (Set.range γ))ᶜ hu
      isClosed_closure.isOpen_compl hcov hdisj with h | h
  · exact fun x hx => huL x (h hx) (hRL hx)
  · exact absurd (subset_closure (mem_range_self 0)) (h h0)

/-- The integral curve of the rotated gradient through a regular point of a critical level
`h p` (critical values distinct): it stays in the level `L` and away from `p`, the other points
of `L` are regular, its accumulation points in `L \ {p}` lie on it, it is locally an arc of `L`,
and it satisfies orbit uniqueness. -/
theorem levelTangentField_orbit_props {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p}) {p : E₃}
    (hp : IsSurfaceCriticalPoint S h p) {γ : ℝ → E₃}
    (hγ : ∀ t, γ t ∈ S ∧ HasDerivAt γ (levelTangentField n h (γ t)) t)
    (hγ0 : h (γ 0) = h p) (hγ0p : γ 0 ≠ p) :
    (∀ t, γ t ∈ S ∩ {x | h x = h p}) ∧ (∀ t, γ t ≠ p) ∧
      (∀ q ∈ S ∩ {x | h x = h p}, q ≠ p → ¬ IsSurfaceCriticalPoint S h q) ∧
      (∀ q ∈ S ∩ {x | h x = h p}, q ≠ p → q ∈ closure (Set.range γ) → q ∈ Set.range γ) ∧
      (∀ t₀ : ℝ, ∀ ε > 0, ∃ V : Set E₃, IsOpen V ∧ γ t₀ ∈ V ∧
        ∀ y ∈ V ∩ (S ∩ {x | h x = h p}), ∃ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε), γ t = y) ∧
      (∀ t₁ t₂, γ t₁ = γ t₂ → ∀ s, γ (t₁ + s) = γ (t₂ + s)) := by
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  have hL : ∀ t, γ t ∈ S ∩ {x | h x = h p} := fun t =>
    ⟨(hγ t).1, by
      change h (γ t) = h p
      rw [height_levelTangentField_curve hh1 (fun s => (hγ s).2) t, hγ0]⟩
  have hreg : ∀ q ∈ S ∩ {x | h x = h p}, q ≠ p → ¬ IsSurfaceCriticalPoint S h q :=
    fun q hq hqp hcq => hqp (hinj hcq hp hq.2)
  have hshift : ∀ t₀ : ℝ, ∀ u, (fun v => γ (t₀ + v)) u ∈ S ∧
      HasDerivAt (fun v => γ (t₀ + v)) (levelTangentField n h ((fun v => γ (t₀ + v)) u)) u := by
    intro t₀ u
    refine ⟨(hγ (t₀ + u)).1, ?_⟩
    have := (hγ (t₀ + u)).2.scomp u ((hasDerivAt_id' u).const_add t₀)
    simpa [Function.comp_def] using this
  refine ⟨hL, levelTangentField_curve_ne hS hn hh hγ hp hγ0p, hreg, ?_, ?_, ?_⟩
  · intro q hq hqp hqc
    obtain ⟨δ, hδ0, hδ⟩ := exists_levelTangentField_curve hS hc hn hh hq.1
    obtain ⟨V, hV, hqV, hVL⟩ :=
      levelSet_subset_integralCurve hS hn hh hq.1 (hreg q hq hqp) hδ0 hδ one_pos
    obtain ⟨_, hyV, ⟨t, rfl⟩⟩ := mem_closure_iff.mp hqc V hV hqV
    obtain ⟨s, -, hs⟩ := hVL (γ t) ⟨hyV, (hL t).1⟩ ((hL t).2.trans hq.2.symm)
    exact ⟨t + -s, by rw [levelTangentField_curve_shift hn hh hγ hδ hs.symm (-s), add_neg_cancel,
      hδ0]⟩
  · intro t₀ ε hε
    obtain ⟨V, hV, hqV, hVL⟩ := levelSet_subset_integralCurve hS hn hh (hγ t₀).1
      (hreg _ (hL t₀) (levelTangentField_curve_ne hS hn hh hγ hp hγ0p t₀))
      (γ := fun v => γ (t₀ + v)) (by simp) (hshift t₀) hε
    refine ⟨V, hV, hqV, fun y hy => ?_⟩
    obtain ⟨t, ht, hty⟩ := hVL y ⟨hy.1, hy.2.1⟩ (by rw [hy.2.2]; exact ((hL t₀).2).symm)
    exact ⟨t₀ + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, hty⟩
  · intro t₁ t₂ h12 s
    exact levelTangentField_curve_shift hn hh hγ hγ h12 s

/-- The two ends of an injective curve of level points tending to the saddle `p` at both ends
lie, in the Morse chart, in two distinct rays. -/
theorem orbit_ends_distinct_rays {h : E₃ → ℝ} {p : E₃} {E : OpenPartialHomeomorph S E2}
    {ρ : ℝ} {V : Set E₃} {hp : p ∈ S} (hps : (⟨p, hp⟩ : S) ∈ E.source)
    (hE0 : E ⟨p, hp⟩ = 0)
    (hVE : ∀ x : S, (x : E₃) ∈ V ↔ x ∈ E.source ∧ E x ∈ morseDisk ρ)
    (hmod : ∀ x : S, x ∈ E.source → h x = h p + ((E x) 0 ^ 2 - (E x) 1 ^ 2))
    (hVo : IsOpen V) (hpV : p ∈ V) {γ : ℝ → E₃} (hγS : ∀ t, γ t ∈ S) (hγc : Continuous γ)
    (hinj : Injective γ) (htop : Tendsto γ atTop (𝓝 p)) (hbot : Tendsto γ atBot (𝓝 p))
    (hγp : ∀ t, γ t ≠ p) (hγh : ∀ t, h (γ t) = h p) :
    ∃ T₀ T₁ : ℝ, T₀ < T₁ ∧ ∃ Rj Rk : Set E2,
      (Rj = morseRay1 ρ ∨ Rj = morseRay2 ρ ∨ Rj = morseRay3 ρ ∨ Rj = morseRay4 ρ) ∧
      (Rk = morseRay1 ρ ∨ Rk = morseRay2 ρ ∨ Rk = morseRay3 ρ ∨ Rk = morseRay4 ρ) ∧ Rj ≠ Rk ∧
      (∀ t ≤ T₀, γ t ∈ V ∧ E ⟨γ t, hγS t⟩ ∈ Rj) ∧ (∀ t ≥ T₁, γ t ∈ V ∧ E ⟨γ t, hγS t⟩ ∈ Rk) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (htop.eventually (hVo.mem_nhds hpV))
  obtain ⟨B, hB⟩ := eventually_atBot.mp (hbot.eventually (hVo.mem_nhds hpV))
  have hT : min B (A - 1) < A := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h0V : ∀ t ≤ min B (A - 1), γ t ∈ V := fun t ht => hB t (ht.trans (min_le_left _ _))
  have h1V : ∀ t ≥ A, γ t ∈ V := hA
  have hsrc : ∀ t, γ t ∈ V → (⟨γ t, hγS t⟩ : S) ∈ E.source := fun t ht => ((hVE _).mp ht).1
  have hγ' : Continuous (fun t => (⟨γ t, hγS t⟩ : S)) := hγc.subtype_mk hγS
  have hcont : ∀ I : Set ℝ, (∀ t ∈ I, γ t ∈ V) →
      ContinuousOn (fun t => E ⟨γ t, hγS t⟩) I := fun I hI =>
    E.continuousOn.comp hγ'.continuousOn (fun t ht => hsrc t (hI t ht))
  have hray : ∀ t, γ t ∈ V →
      E ⟨γ t, hγS t⟩ ∈ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ := fun t ht =>
    (saddle_chart_mem hps hE0 hVE hmod (hγS t) ht).2.2 (hγh t) (hγp t)
  obtain ⟨Rj, hRj, hj⟩ := exists_ray_of_isPreconnected isPreconnected_Iic (hcont _ h0V)
    (fun t ht => hray t (h0V t ht))
  obtain ⟨Rk, hRk, hk⟩ := exists_ray_of_isPreconnected isPreconnected_Ici (hcont _ h1V)
    (fun t ht => hray t (h1V t ht))
  refine ⟨min B (A - 1), A, hT, Rj, Rk, hRj, hRk, ?_, fun t ht => ⟨h0V t ht, hj t ht⟩,
    fun t ht => ⟨h1V t ht, hk t ht⟩⟩
  rintro rfl
  have hlim : ∀ l : Filter ℝ, Tendsto γ l (𝓝 p) →
      Tendsto (fun t => E ⟨γ t, hγS t⟩) l (𝓝 0) := by
    intro l hl
    have h1 : Tendsto (fun t => (⟨γ t, hγS t⟩ : S)) l (𝓝 ⟨p, hp⟩) := tendsto_subtype_rng.mpr hl
    have := (E.continuousAt hps).tendsto.comp h1
    rwa [hE0] at this
  refine not_both_ends_same_ray hT ?_ (hcont _ h0V) (hcont _ h1V) (hlim _ hbot) (hlim _ htop)
    Rj hRj (fun t ht => hj t ht) (fun t ht => hk t ht)
  intro s hs t ht hst
  have hs' : γ s ∈ V := hs.elim (h0V s) (h1V s)
  have ht' : γ t ∈ V := ht.elim (h0V t) (h1V t)
  exact hinj (congrArg Subtype.val (E.injOn (hsrc s hs') (hsrc t ht') hst))

/-- `lem:merge-disjoint`: for a smooth Morse function with distinct critical values on a compact
embedded surface, no saddle is both sub-merging and super-merging. -/
theorem merge_disjoint {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hM : IsSurfaceMorse S n h) (hinj : Set.InjOn h {p | IsSurfaceCriticalPoint S h p})
    (p : E₃) : ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p) := by
  rintro ⟨hsub, hsup⟩
  have hp := hsub.1
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  obtain ⟨E, ρ, V, hρ, hD, hVo, hpV, hps, hE0, hVE, hmod⟩ :=
    exists_saddle_chart hS hn hh hp (hM p hp) hsub.2.1
  have hsymm0 : E.symm 0 = ⟨p, hp.1⟩ := by rw [← hE0]; exact E.left_inv hps
  have h0D : (0 : E2) ∈ morseDisk ρ := Metric.mem_ball_self hρ
  -- transport of model sets
  have hTmem : ∀ {M : Set E2}, M ⊆ morseDisk ρ → ∀ {y : E₃},
      y ∈ Subtype.val '' (E.symm '' M) → ∃ hyS : y ∈ S, y ∈ V ∧ E ⟨y, hyS⟩ ∈ M := by
    rintro M hM _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have hzt := hD (hM hz)
    refine ⟨(E.symm z).2, ?_, ?_⟩
    · exact (hVE (E.symm z)).mpr ⟨E.map_target hzt, by rw [E.right_inv hzt]; exact hM hz⟩
    · change E (E.symm z) ∈ M
      rw [E.right_inv hzt]
      exact hz
  have hTin : ∀ {M : Set E2} {x : S}, x ∈ E.source → E x ∈ M →
      (x : E₃) ∈ Subtype.val '' (E.symm '' M) := fun {M x} hx hxM =>
    ⟨E.symm (E x), ⟨E x, hxM, rfl⟩, by rw [E.left_inv hx]⟩
  have hTcl : ∀ {M : Set E2}, M ⊆ morseDisk ρ → ∀ {z : E2}, z ∈ morseDisk ρ → z ∈ closure M →
      ((E.symm z : S) : E₃) ∈ closure (Subtype.val '' (E.symm '' M)) := by
    intro M hM z hz hzM
    exact image_closure_subset_closure_image continuous_subtype_val
      ⟨E.symm z, (morse_model_closure_transport E hD hM hz).mpr hzM, rfl⟩
  have hTcl' : ∀ {M : Set E2}, M ⊆ morseDisk ρ → ∀ {x : S}, (x : E₃) ∈ V → E x ∈ closure M →
      (x : E₃) ∈ closure (Subtype.val '' (E.symm '' M)) := by
    intro M hM x hxV hxM
    obtain ⟨hx, hxD⟩ := (hVE x).mp hxV
    have := hTcl hM hxD hxM
    rwa [E.left_inv hx] at this
  have hconnT : ∀ {M : Set E2}, M ⊆ morseDisk ρ → IsConnected M →
      IsConnected (Subtype.val '' (E.symm '' M)) := fun hM hcM =>
    (morse_model_connected_transport E hD hM hcM).image _ continuous_subtype_val.continuousOn
  have hSm : ∀ {M : Set E2}, M ⊆ morseSm12 ρ ∪ morseSm34 ρ →
      Subtype.val '' (E.symm '' M) ⊆ S ∩ {z | h z < h p} := by
    intro M hM y hy
    obtain ⟨hyS, hyV, hyM⟩ := hTmem (fun z hz => (hM hz).elim (·.1) (·.1)) hy
    have hm := hmod ⟨y, hyS⟩ ((hVE ⟨y, hyS⟩).mp hyV).1
    have hneg : E ⟨y, hyS⟩ ∈ {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 < 0} := by
      rw [morse_saddle_negative_set]; exact hM hyM
    refine ⟨hyS, ?_⟩
    change h y < h p
    change h y = _ at hm
    linarith [hneg.2]
  have hSp : ∀ {M : Set E2}, M ⊆ morseSp23 ρ ∪ morseSp41 ρ →
      Subtype.val '' (E.symm '' M) ⊆ S ∩ {z | h p < h z} := by
    intro M hM y hy
    obtain ⟨hyS, hyV, hyM⟩ := hTmem (fun z hz => (hM hz).elim (·.1) (·.1)) hy
    have hm := hmod ⟨y, hyS⟩ ((hVE ⟨y, hyS⟩).mp hyV).1
    have hpos : E ⟨y, hyS⟩ ∈ {x ∈ morseDisk ρ | 0 < x 0 ^ 2 - x 1 ^ 2} := by
      rw [morse_saddle_positive_set]; exact hM hyM
    refine ⟨hyS, ?_⟩
    change h p < h y
    change h y = _ at hm
    linarith [hpos.2]
  -- the sectors, their base points, and the components they determine
  obtain ⟨⟨z₁, hz₁⟩, -, -, -, ⟨z12, hz12⟩, ⟨z23, hz23⟩, ⟨z34, hz34⟩, ⟨z41, hz41⟩⟩ :=
    morse_rays_sectors_nonempty hρ
  obtain ⟨-, -, -, -, c12, c23, c34, c41⟩ := morse_rays_sectors_connected hρ
  have hfl := morse_rays_flanking hρ
  have hsub12 : morseSm12 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hsub23 : morseSp23 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hsub34 : morseSm34 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hsub41 : morseSp41 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have ha12 : ((E.symm z12 : S) : E₃) ∈ Subtype.val '' (E.symm '' morseSm12 ρ) :=
    ⟨_, ⟨z12, hz12, rfl⟩, rfl⟩
  have ha34 : ((E.symm z34 : S) : E₃) ∈ Subtype.val '' (E.symm '' morseSm34 ρ) :=
    ⟨_, ⟨z34, hz34, rfl⟩, rfl⟩
  have hb23 : ((E.symm z23 : S) : E₃) ∈ Subtype.val '' (E.symm '' morseSp23 ρ) :=
    ⟨_, ⟨z23, hz23, rfl⟩, rfl⟩
  have hb41 : ((E.symm z41 : S) : E₃) ∈ Subtype.val '' (E.symm '' morseSp41 ρ) :=
    ⟨_, ⟨z41, hz41, rfl⟩, rfl⟩
  have hNV : S ∩ {z | h z < h p} ∩ V ⊆ Subtype.val '' (E.symm '' morseSm12 ρ) ∪
      Subtype.val '' (E.symm '' morseSm34 ρ) := by
    rintro y ⟨⟨hyS, hylt⟩, hyV⟩
    have hsrc := ((hVE ⟨y, hyS⟩).mp hyV).1
    rcases (saddle_chart_mem hps hE0 hVE hmod hyS hyV).1 hylt with h1 | h1
    · exact Or.inl (hTin hsrc h1)
    · exact Or.inr (hTin hsrc h1)
  have hPV : S ∩ {z | h p < h z} ∩ V ⊆ Subtype.val '' (E.symm '' morseSp23 ρ) ∪
      Subtype.val '' (E.symm '' morseSp41 ρ) := by
    rintro y ⟨⟨hyS, hygt⟩, hyV⟩
    have hsrc := ((hVE ⟨y, hyS⟩).mp hyV).1
    rcases (saddle_chart_mem hps hE0 hVE hmod hyS hyV).2.1 hygt with h1 | h1
    · exact Or.inl (hTin hsrc h1)
    · exact Or.inr (hTin hsrc h1)
  have hA := connectedComponentIn_ne_of_local_cover hVo hpV hNV
    (hconnT hsub12 c12).isPreconnected (hconnT hsub34 c34).isPreconnected
    (hSm subset_union_left) (hSm subset_union_right) ha12 ha34 hsub.2.2
  have hB := connectedComponentIn_ne_of_local_cover hVo hpV hPV
    (hconnT hsub23 c23).isPreconnected (hconnT hsub41 c41).isPreconnected
    (hSp subset_union_left) (hSp subset_union_right) hb23 hb41 hsup.2.2
  -- the ray `r₁` and the orbit through a point of it
  have hray1D : morseRay1 ρ ⊆ morseDisk ρ := fun x hx => hx.1
  have hq₀T : ((E.symm z₁ : S) : E₃) ∈ Subtype.val '' (E.symm '' morseRay1 ρ) :=
    ⟨_, ⟨z₁, hz₁, rfl⟩, rfl⟩
  have hR1L : Subtype.val '' (E.symm '' morseRay1 ρ) ⊆ S ∩ {x | h x = h p} := by
    intro y hy
    obtain ⟨hyS, hyV, hyM⟩ := hTmem hray1D hy
    have hm := hmod ⟨y, hyS⟩ ((hVE ⟨y, hyS⟩).mp hyV).1
    refine ⟨hyS, ?_⟩
    change h y = h p
    change h y = _ at hm
    rw [hm, hyM.2.1]
    ring
  have hpR1 : p ∉ Subtype.val '' (E.symm '' morseRay1 ρ) := by
    intro hy
    obtain ⟨hyS, -, hyM⟩ := hTmem hray1D hy
    have : E ⟨p, hyS⟩ = 0 := hE0
    rw [this] at hyM
    exact (morse_rays_zero_notMem ρ).1 hyM
  have hR1conn := hconnT hray1D (morse_rays_sectors_connected hρ).1
  have hpcl : p ∈ closure (Subtype.val '' (E.symm '' morseRay1 ρ)) := by
    have := hTcl hray1D h0D (morse_rays_zero_mem_closure hρ).1
    rwa [hsymm0] at this
  obtain ⟨γ, hγ0, hγ⟩ := exists_levelTangentField_curve hS hc hn hh (hR1L hq₀T).1
  obtain ⟨hγL, hγp, hreg, hclosed, harc, hper⟩ := levelTangentField_orbit_props hS hc hn hh
    hinj hp hγ (by rw [hγ0]; exact (hR1L hq₀T).2)
    (by rw [hγ0]; exact fun e => hpR1 (e ▸ hq₀T))
  have hR1range : Subtype.val '' (E.symm '' morseRay1 ρ) ⊆ range γ :=
    subset_range_of_local_arc hclosed harc hR1conn.isPreconnected hR1L hpR1
      (by rw [hγ0]; exact hq₀T)
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).2.continuousAt
  have hLc : IsCompact (S ∩ {x | h x = h p}) :=
    hc.inter_right (isClosed_eq hh.continuous continuous_const)
  obtain ⟨hγinj, htop, hbot⟩ := orbit_injective_tendsto hLc hγc hγL hγp
    (closure_mono hR1range hpcl) hclosed harc hper
  obtain ⟨T₀, T₁, hT, Rj, Rk, hRj, hRk, hjk, hj, hk⟩ := orbit_ends_distinct_rays hps hE0 hVE
    hmod hVo hpV (fun t => (hγ t).1) hγc hγinj htop hbot hγp (fun t => (hγL t).2)
  -- a point of `r₁` outside the compact middle arc: one end runs along `r₁`
  have hK : IsCompact (γ '' Icc T₀ T₁) := isCompact_Icc.image hγc
  have hnot : ¬ Subtype.val '' (E.symm '' morseRay1 ρ) ⊆ γ '' Icc T₀ T₁ := by
    intro hs
    have := closure_mono hs hpcl
    rw [hK.isClosed.closure_eq] at this
    obtain ⟨t, -, ht⟩ := this
    exact hγp t ht
  obtain ⟨y, hyR, hyK⟩ := not_subset.mp hnot
  obtain ⟨t, rfl⟩ := hR1range hyR
  obtain ⟨hyS, -, hE1⟩ := hTmem hray1D hyR
  have hout : t < T₀ ∨ T₁ < t := by
    rcases lt_or_ge t T₀ with h0 | h0
    · exact Or.inl h0
    · rcases lt_or_ge T₁ t with h1 | h1
      · exact Or.inr h1
      · exact absurd ⟨t, ⟨h0, h1⟩, rfl⟩ hyK
  obtain ⟨R', t', hR', hR'1, ht'V, ht'R⟩ : ∃ (R' : Set E2) (t' : ℝ),
      (R' = morseRay1 ρ ∨ R' = morseRay2 ρ ∨ R' = morseRay3 ρ ∨ R' = morseRay4 ρ) ∧
      R' ≠ morseRay1 ρ ∧ γ t' ∈ V ∧ E ⟨γ t', (hγ t').1⟩ ∈ R' := by
    rcases hout with ht | ht
    · have h1 : Rj = morseRay1 ρ := morse_ray_eq_of_mem hRj (Or.inl rfl) (hj t ht.le).2 hE1
      exact ⟨Rk, T₁, hRk, fun e => hjk (h1.trans e.symm), (hk T₁ le_rfl).1, (hk T₁ le_rfl).2⟩
    · have h1 : Rk = morseRay1 ρ := morse_ray_eq_of_mem hRk (Or.inl rfl) (hk t ht.le).2 hE1
      exact ⟨Rj, T₀, hRj, fun e => hjk (e.trans h1.symm), (hj T₀ le_rfl).1, (hj T₀ le_rfl).2⟩
  -- adjacency is constant along the orbit
  have hregC : ∀ q ∈ range γ, q ∈ S ∧ h q = h p ∧ ¬ IsSurfaceCriticalPoint S h q := by
    rintro _ ⟨s, rfl⟩
    exact ⟨(hγL s).1, (hγL s).2, hreg _ (hγL s) (hγp s)⟩
  have hq₀A : ((E.symm z₁ : S) : E₃) ∈
      closure (connectedComponentIn (S ∩ {z | h z < h p}) ((E.symm z12 : S) : E₃)) :=
    closure_mono ((hconnT hsub12 c12).isPreconnected.subset_connectedComponentIn ha12
      (hSm subset_union_left)) (hTcl hsub12 hz₁.1 (hfl.1 hz₁).2)
  have hq₀B : ((E.symm z₁ : S) : E₃) ∈
      closure (connectedComponentIn (S ∩ {z | h p < h z}) ((E.symm z41 : S) : E₃)) :=
    closure_mono ((hconnT hsub41 c41).isPreconnected.subset_connectedComponentIn hb41
      (hSp subset_union_right)) (hTcl hsub41 hz₁.1 (hfl.1 hz₁).1)
  have hy'A := closure_connectedComponentIn_levelBelow_constant hS hh1
    (isPreconnected_range hγc) hregC ⟨0, hγ0⟩ ⟨t', rfl⟩ hq₀A
  have hy'B := closure_connectedComponentIn_levelAbove_constant hS hh1
    (isPreconnected_range hγc) hregC ⟨0, hγ0⟩ ⟨t', rfl⟩ hq₀B
  have hreg' := hreg _ (hγL t') (hγp t')
  rcases hR' with h1 | h1 | h1 | h1
  · exact hR'1 h1
  · rw [h1] at ht'R
    have hB23 : γ t' ∈ closure
        (connectedComponentIn (S ∩ {z | h p < h z}) ((E.symm z23 : S) : E₃)) :=
      closure_mono ((hconnT hsub23 c23).isPreconnected.subset_connectedComponentIn hb23
        (hSp subset_union_left)) (hTcl' hsub23 (x := ⟨γ t', (hγ t').1⟩) ht'V (hfl.2.1 ht'R).2)
    exact hB (connectedComponentIn_levelAbove_eq_of_mem_closure hS hh1 (hγ t').1 (hγL t').2
      hreg' hB23 hy'B)
  · rw [h1] at ht'R
    have hA34 : γ t' ∈ closure
        (connectedComponentIn (S ∩ {z | h z < h p}) ((E.symm z34 : S) : E₃)) :=
      closure_mono ((hconnT hsub34 c34).isPreconnected.subset_connectedComponentIn ha34
        (hSm subset_union_right))
        (hTcl' hsub34 (x := ⟨γ t', (hγ t').1⟩) ht'V (hfl.2.2.1 ht'R).2)
    exact hA (connectedComponentIn_levelBelow_eq_of_mem_closure hS hh1 (hγ t').1 (hγL t').2
      hreg' hy'A hA34)
  · rw [h1] at ht'R
    have hA34 : γ t' ∈ closure
        (connectedComponentIn (S ∩ {z | h z < h p}) ((E.symm z34 : S) : E₃)) :=
      closure_mono ((hconnT hsub34 c34).isPreconnected.subset_connectedComponentIn ha34
        (hSm subset_union_right))
        (hTcl' hsub34 (x := ⟨γ t', (hγ t').1⟩) ht'V (hfl.2.2.2 ht'R).1)
    exact hA (connectedComponentIn_levelBelow_eq_of_mem_closure hS hh1 (hγ t').1 (hγL t').2
      hreg' hy'A hA34)

/-- prop:morse-count: `c₀ - c₁ + c₂ ≤ 2` for every smooth Morse function on a compact connected
embedded surface (`lem:merge-disjoint` discharged). -/
theorem morse_count_le_two_unconditional {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hM : IsSurfaceMorse S n h) :
    (morseCount S n h 0 : ℤ) - morseCount S n h 1 + morseCount S n h 2 ≤ 2 :=
  morse_count_le_two_of_merge_disjoint hS hc hconn hn
    (fun _ hh' hM' hinj' p => merge_disjoint hS hc hn hh' hM' hinj' p) hh hM

open MeasureTheory in
/-- thm:total-curvature-bound, PARTIAL, for a compact connected surface: `∫_Σ κ dH² ≤ 4π`, with
cor:sublevel-stable, lem:sublevel-closure and lem:merge-disjoint discharged. The remaining named
hypotheses are `h_sard_charts` (cor:sard-charts) and `h_total_curvature_index`
(thm:total-curvature-index), exactly as in `total_curvature_le_of_merge_disjoint`. -/
theorem total_curvature_le_of_sard_index {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y)
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_merge_disjoint hS hc hconn hn h_sard_charts
    (fun _ hh' hM' hinj' p => merge_disjoint hS hc hn hh' hM' hinj' p) h_total_curvature_index

end LiquidDrop
