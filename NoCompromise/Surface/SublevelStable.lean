import NoCompromise.Surface.MorseMerge
import NoCompromise.Surface.SurfaceChart

/-!
# Sublevel stability across critical-value-free intervals (`cor:sublevel-stable`)

The component-count form of `cor:sublevel-stable`, allowing a critical value at the lower
level `a`, derived from the regular case `connectedComponentIn_sublevel_of_regular` applied on
critical-value-free subintervals.
-/

noncomputable section
open Set Function InnerProductSpace Filter Topology
namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The connected component in a closed set is closed. -/
theorem isClosed_connectedComponentIn_of_isClosed {F : Set E₃} (hF : IsClosed F) (x : E₃) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine isClosed_of_closure_subset ?_
    exact (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset F x) hF)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- The intersection of a directed family of compact preconnected sets is preconnected. -/
theorem isPreconnected_iInter_of_directed {ι : Type*} [Nonempty ι] (C : ι → Set E₃)
    (hd : Directed (· ⊇ ·) C) (hc : ∀ i, IsCompact (C i)) (hp : ∀ i, IsPreconnected (C i)) :
    IsPreconnected (⋂ i, C i) := by
  have hDc : IsClosed (⋂ i, C i) := isClosed_iInter fun i => (hc i).isClosed
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hDk : IsCompact (⋂ i, C i) := (hc i₀).of_isClosed_subset hDc (iInter_subset C i₀)
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro F1 F2 hF1 hF2 hcov hdisj
  have hdj : Disjoint ((⋂ i, C i) ∩ F1) ((⋂ i, C i) ∩ F2) := by
    rw [Set.disjoint_left]
    rintro q ⟨hq, h1⟩ ⟨-, h2⟩
    have : q ∈ (⋂ i, C i) ∩ (F1 ∩ F2) := ⟨hq, h1, h2⟩
    rw [hdisj] at this
    exact this
  obtain ⟨O1, O2, hO1, hO2, hsub1, hsub2, hO⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hDk.inter_right hF1) (hDk.inter_right hF2) hdj
  have hDO : (⋂ i, C i) ⊆ O1 ∪ O2 := fun q hq =>
    (hcov hq).elim (fun h1 => Or.inl (hsub1 ⟨hq, h1⟩)) (fun h2 => Or.inr (hsub2 ⟨hq, h2⟩))
  have hdir : Directed (· ⊇ ·) (fun i => C i \ (O1 ∪ O2)) := by
    intro i j
    obtain ⟨k, hk1, hk2⟩ := hd i j
    exact ⟨k, sdiff_subset_sdiff_left hk1, sdiff_subset_sdiff_left hk2⟩
  obtain ⟨i, hi⟩ : ∃ i, C i ⊆ O1 ∪ O2 := by
    by_contra hne
    push Not at hne
    have hn : ∀ i, (C i \ (O1 ∪ O2)).Nonempty := fun i => by
      obtain ⟨q, hq, hq'⟩ := not_subset.mp (hne i)
      exact ⟨q, hq, hq'⟩
    obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun i => C i \ (O1 ∪ O2)) hdir hn
      (fun i => (hc i).diff (hO1.union hO2)) (fun i => (hc i).isClosed.sdiff (hO1.union hO2))
    rw [mem_iInter] at hq
    exact (hq i₀).2 (hDO (mem_iInter.mpr fun i => (hq i).1))
  rcases (hp i).subset_or_subset hO1 hO2 hO hi with h | h
  · left
    intro q hq
    rcases hcov hq with h1 | h2
    · exact h1
    · exact absurd (hsub2 ⟨hq, h2⟩) (Set.disjoint_left.mp hO (h (iInter_subset C i hq)))
  · right
    intro q hq
    rcases hcov hq with h1 | h2
    · exact absurd (hsub1 ⟨hq, h1⟩) (Set.disjoint_right.mp hO (h (iInter_subset C i hq)))
    · exact h2

private lemma regular_sublevel {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    (∀ x ∈ S ∩ {x | h x ≤ b}, ∃ y ∈ S ∩ {x | h x ≤ a},
        y ∈ connectedComponentIn (S ∩ {x | h x ≤ b}) x) ∧
      (∀ x ∈ S ∩ {x | h x ≤ a}, ∀ y ∈ S ∩ {x | h x ≤ a},
        y ∈ connectedComponentIn (S ∩ {x | h x ≤ b}) x ↔
          y ∈ connectedComponentIn (S ∩ {x | h x ≤ a}) x) :=
  connectedComponentIn_sublevel_of_regular hS hc hn hh hab hreg

private lemma sublevel_mono {S : Set E₃} {h : E₃ → ℝ} {s t : ℝ} (hst : s ≤ t) :
    S ∩ {x | h x ≤ s} ⊆ S ∩ {x | h x ≤ t} := fun _ hq => ⟨hq.1, le_trans hq.2 hst⟩

private lemma isCompact_componentIn_sublevel {S : Set E₃} (hc : IsCompact S) {h : E₃ → ℝ}
    (hh : Continuous h) (t : ℝ) (x : E₃) :
    IsCompact (connectedComponentIn (S ∩ {x | h x ≤ t}) x) :=
  hc.of_isClosed_subset
    (isClosed_connectedComponentIn_of_isClosed
      (hc.isClosed.inter (isClosed_le hh continuous_const)) x)
    ((connectedComponentIn_subset _ _).trans inter_subset_left)

/-- cor:sublevel-stable (i): no critical value in (a, b]; `a` may be a critical value. -/
theorem componentCount_sublevel_closed {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ioc a b) :
    componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}) := by
  have hcont : Continuous h := hh.continuous
  have hreg' : ∀ {s t : ℝ}, a < s → t ≤ b →
      ∀ x ∈ S, h x ∈ Icc s t → ¬ IsSurfaceCriticalPoint S h x :=
    fun hs ht x _ hx hcrit => hreg x hcrit ⟨lt_of_lt_of_le hs hx.1, le_trans hx.2 ht⟩
  refine componentCount_eq_of_connectedComponentIn (sublevel_mono hab.le) ?_ ?_
  · intro x hx
    have hCk := isCompact_componentIn_sublevel hc hcont b x
    obtain ⟨z, hzC, hzmin⟩ :=
      hCk.exists_isMinOn ⟨x, mem_connectedComponentIn hx⟩ hcont.continuousOn
    have hzT : z ∈ S ∩ {x | h x ≤ b} := connectedComponentIn_subset _ _ hzC
    by_cases hza : h z ≤ a
    · exact ⟨z, ⟨hzT.1, hza⟩, hzC⟩
    · push Not at hza
      have hzb : h z ≤ b := hzT.2
      obtain ⟨y, hy, hyC⟩ := (regular_sublevel hS hc hn hh (a := (a + h z) / 2) (b := b)
        (by linarith) (hreg' (by linarith) le_rfl)).1 z hzT
      rw [← connectedComponentIn_eq hzC] at hyC
      have h1 : h z ≤ h y := isMinOn_iff.mp hzmin y hyC
      have h2 : h y ≤ (a + h z) / 2 := hy.2
      linarith
  · intro x hx y hy
    refine ⟨fun hxy => ?_, fun hxy => connectedComponentIn_mono x (sublevel_mono hab.le) hxy⟩
    have hall : ∀ t : Ioo a b, y ∈ connectedComponentIn (S ∩ {x | h x ≤ (t : ℝ)}) x := by
      rintro ⟨t, ht1, ht2⟩
      exact ((regular_sublevel hS hc hn hh ht2 (hreg' ht1 le_rfl)).2 x
        (sublevel_mono ht1.le hx) y (sublevel_mono ht1.le hy)).mp hxy
    let Cf : Ioo a b → Set E₃ := fun t => connectedComponentIn (S ∩ {x | h x ≤ (t : ℝ)}) x
    have : Nonempty (Ioo a b) := ⟨⟨(a + b) / 2, by linarith, by linarith⟩⟩
    have hdir : Directed (· ⊇ ·) Cf := by
      rintro ⟨s, hs⟩ ⟨t, ht⟩
      refine ⟨⟨min s t, lt_min hs.1 ht.1, lt_of_le_of_lt (min_le_left _ _) hs.2⟩, ?_, ?_⟩
      · exact connectedComponentIn_mono x (sublevel_mono (min_le_left s t))
      · exact connectedComponentIn_mono x (sublevel_mono (min_le_right s t))
    have hDp : IsPreconnected (⋂ t, Cf t) := isPreconnected_iInter_of_directed Cf hdir
      (fun t => isCompact_componentIn_sublevel hc hcont _ x)
      (fun _ => isPreconnected_connectedComponentIn)
    have hxD : x ∈ ⋂ t, Cf t :=
      mem_iInter.mpr fun t => mem_connectedComponentIn (sublevel_mono (le_of_lt t.2.1) hx)
    have hyD : y ∈ ⋂ t, Cf t := mem_iInter.mpr hall
    have hDA : (⋂ t, Cf t) ⊆ S ∩ {x | h x ≤ a} := by
      intro q hq
      rw [mem_iInter] at hq
      have hqt : ∀ t : Ioo a b, q ∈ S ∩ {x | h x ≤ (t : ℝ)} :=
        fun t => connectedComponentIn_subset _ _ (hq t)
      refine ⟨(hqt ⟨(a + b) / 2, by linarith, by linarith⟩).1, ?_⟩
      change h q ≤ a
      by_contra hqa'
      have hqa : a < h q := lt_of_not_ge hqa'
      have hm1 := lt_min hqa hab
      have hm2 := min_le_right (h q) b
      have hm3 := min_le_left (h q) b
      have : h q ≤ (a + min (h q) b) / 2 :=
        (hqt ⟨(a + min (h q) b) / 2, by linarith, by linarith⟩).2
      linarith
    exact hDp.subset_connectedComponentIn hxD hDA hyD

/-- A smooth embedded surface is locally connected (from its projection charts). -/
theorem IsSmoothEmbeddedSurface.locallyConnectedSpace {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) : LocallyConnectedSpace S := by
  choose e P U hU hqU hsrc hmem he0 heP hsm using fun z : S => hS.exists_projection_chart z.2 0
  let _ : ChartedSpace E2 S :=
    { atlas := range e
      chartAt := e
      mem_chart_source := fun z => hmem z
      chart_mem_atlas := fun z => mem_range_self z }
  exact ChartedSpace.locallyConnectedSpace E2 S

/-- Local connectedness in ambient form: a point `z` of a smooth embedded surface `S` and an open
set `O ∋ z` have a preconnected neighbourhood of `z` within `S` contained in `S ∩ O`. -/
theorem IsSmoothEmbeddedSurface.exists_preconnected_nhdsWithin {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) {z : E₃} (hz : z ∈ S) {O : Set E₃} (hO : IsOpen O)
    (hzO : z ∈ O) : ∃ N ⊆ S ∩ O, IsPreconnected N ∧ N ∈ 𝓝[S] z := by
  have := hS.locallyConnectedSpace
  obtain ⟨V, hVsub, hVo, hzV, hVc⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp this) ⟨z, hz⟩
      (Subtype.val ⁻¹' O) ((hO.preimage continuous_subtype_val).mem_nhds hzO)
  refine ⟨Subtype.val '' V, ?_, hVc.isPreconnected.image _ continuous_subtype_val.continuousOn,
    ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.2, hVsub hw⟩
  · rw [nhdsWithin_eq_map_subtype_coe hz]
    exact image_mem_map (hVo.mem_nhds hzV)

/-- cor:sublevel-stable (ii): no critical value in [a, b). -/
theorem componentCount_sublevel_open {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ico a b) :
    componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}) := by
  have hcont : Continuous h := hh.continuous
  have hreg' : ∀ {t : ℝ}, t < b → ∀ x ∈ S, h x ∈ Icc a t → ¬ IsSurfaceCriticalPoint S h x :=
    fun ht x _ hx hcrit => hreg x hcrit ⟨hx.1, lt_of_le_of_lt hx.2 ht⟩
  have hsubU : ∀ {t : ℝ}, t < b → S ∩ {x | h x ≤ t} ⊆ S ∩ {x | h x < b} :=
    fun ht _ hq => ⟨hq.1, lt_of_le_of_lt hq.2 ht⟩
  refine componentCount_eq_of_connectedComponentIn (hsubU hab) ?_ ?_
  · intro x hx
    have hxb : h x < b := hx.2
    have hm := max_lt hxb hab
    have hm1 := le_max_left (h x) a
    have hm2 := le_max_right (h x) a
    have htb : (max (h x) a + b) / 2 < b := by linarith
    have hat : a < (max (h x) a + b) / 2 := by linarith
    have hxt : x ∈ S ∩ {x | h x ≤ (max (h x) a + b) / 2} := ⟨hx.1, by
      change h x ≤ (max (h x) a + b) / 2
      linarith⟩
    obtain ⟨y, hy, hyx⟩ := (regular_sublevel hS hc hn hh hat (hreg' htb)).1 x hxt
    exact ⟨y, hy, connectedComponentIn_mono x (hsubU htb) hyx⟩
  · intro x hx y hy
    refine ⟨fun hxy => ?_, fun hxy => connectedComponentIn_mono x (hsubU hab) hxy⟩
    have key : ∀ z ∈ S ∩ {x | h x < b}, ∃ W : Set E₃, IsOpen W ∧ z ∈ W ∧
        ∀ q ∈ W ∩ S, ((∃ t < b, q ∈ connectedComponentIn (S ∩ {x | h x ≤ t}) x) ↔
          (∃ t < b, z ∈ connectedComponentIn (S ∩ {x | h x ≤ t}) x)) := by
      intro z hz
      have hzb : h z < b := hz.2
      have hcb : (h z + b) / 2 < b := by linarith
      obtain ⟨N, hNsub, hNp, hNnhds⟩ := hS.exists_preconnected_nhdsWithin hz.1
        (isOpen_lt hcont continuous_const) (show h z < (h z + b) / 2 by linarith)
      obtain ⟨W, hWo, hzW, hWN⟩ := mem_nhdsWithin.mp hNnhds
      have hzN : z ∈ N := hWN ⟨hzW, hz.1⟩
      have hNc : N ⊆ S ∩ {x | h x ≤ (h z + b) / 2} :=
        fun q hq => ⟨(hNsub hq).1, (show h q < (h z + b) / 2 from (hNsub hq).2).le⟩
      have htrans : ∀ w ∈ N, ∀ w' ∈ N,
          (∃ t < b, w ∈ connectedComponentIn (S ∩ {x | h x ≤ t}) x) →
            (∃ t < b, w' ∈ connectedComponentIn (S ∩ {x | h x ≤ t}) x) := by
        rintro w hw w' hw' ⟨t, htb, hwt⟩
        refine ⟨max t ((h z + b) / 2), max_lt htb hcb, ?_⟩
        have hU : IsPreconnected (connectedComponentIn (S ∩ {x | h x ≤ t}) x ∪ N) :=
          isPreconnected_connectedComponentIn.union w hwt hw hNp
        have hxK : x ∈ S ∩ {x | h x ≤ t} := connectedComponentIn_nonempty_iff.mp ⟨w, hwt⟩
        have hsub := hU.subset_connectedComponentIn
          (F := S ∩ {x | h x ≤ max t ((h z + b) / 2)}) (Or.inl (mem_connectedComponentIn hxK))
          (union_subset ((connectedComponentIn_subset _ _).trans
            (sublevel_mono (le_max_left _ _))) (hNc.trans (sublevel_mono (le_max_right _ _))))
        exact hsub (Or.inr hw')
      exact ⟨W, hWo, hzW, fun q hq => ⟨htrans q (hWN hq) z hzN, htrans z hzN q (hWN hq)⟩⟩
    choose! W hWo hzW hW using key
    set U := S ∩ {x | h x < b} with hUdef
    set P : E₃ → Prop := fun z => ∃ t < b, z ∈ connectedComponentIn (S ∩ {x | h x ≤ t}) x
      with hPdef
    set O1 := ⋃ z ∈ {z | z ∈ U ∧ P z}, W z with hO1def
    set O2 := ⋃ z ∈ {z | z ∈ U ∧ ¬ P z}, W z with hO2def
    have hO1 : IsOpen O1 := isOpen_biUnion fun z hz => hWo z hz.1
    have hO2 : IsOpen O2 := isOpen_biUnion fun z hz => hWo z hz.1
    have h1 : ∀ q ∈ U, q ∈ O1 → P q := by
      intro q hqU hq
      rw [hO1def, mem_iUnion₂] at hq
      obtain ⟨z, ⟨hzU, hPz⟩, hqW⟩ := hq
      exact (hW z hzU q ⟨hqW, hqU.1⟩).mpr hPz
    have h2 : ∀ q ∈ U, q ∈ O2 → ¬ P q := by
      intro q hqU hq
      rw [hO2def, mem_iUnion₂] at hq
      obtain ⟨z, ⟨hzU, hPz⟩, hqW⟩ := hq
      exact fun hq' => hPz ((hW z hzU q ⟨hqW, hqU.1⟩).mp hq')
    have hcov : connectedComponentIn U x ⊆ O1 ∪ O2 := by
      intro q hq
      have hqU := connectedComponentIn_subset _ _ hq
      by_cases hPq : P q
      · exact Or.inl (mem_biUnion (x := q) ⟨hqU, hPq⟩ (hzW q hqU))
      · exact Or.inr (mem_biUnion (x := q) ⟨hqU, hPq⟩ (hzW q hqU))
    have hdisj : connectedComponentIn U x ∩ (O1 ∩ O2) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr ?_
      rintro q ⟨hq, hq1, hq2⟩
      have hqU := connectedComponentIn_subset _ _ hq
      exact h2 q hqU hq2 (h1 q hqU hq1)
    have hxU : x ∈ U := hsubU hab hx
    have hPx : P x := ⟨(a + b) / 2, by linarith,
      mem_connectedComponentIn (sublevel_mono (by linarith) hx)⟩
    rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn)
      O1 O2 hO1 hO2 hcov hdisj with hs | hs
    · obtain ⟨t, htb, hyt⟩ := h1 y (hsubU hab hy) (hs hxy)
      have hat' : a < max t ((a + b) / 2) :=
        lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have htb' : max t ((a + b) / 2) < b := max_lt htb (by linarith)
      have hyt' := connectedComponentIn_mono x
        (sublevel_mono (S := S) (h := h) (le_max_left t ((a + b) / 2))) hyt
      exact ((regular_sublevel hS hc hn hh hat' (hreg' htb')).2 x hx y hy).mp hyt'
    · exact absurd hPx (h2 x hxU (hs (mem_connectedComponentIn hxU)))

/-- lem:count-submerging, PARTIAL: `count_submerging` with cor:sublevel-stable (i), (ii)
discharged by `componentCount_sublevel_closed` and `componentCount_sublevel_open`; the remaining
named hypothesis is `h_closure` (lem:sublevel-closure), exactly as in `count_submerging`. -/
theorem count_submerging_of_closure {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_closure : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ p, IsSurfaceCriticalPoint S h p →
      (surfaceIndex S n h p = 0 →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1) ∧
      (IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p})) ∧
      (surfaceIndex S n h p ≠ 0 → ¬ IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p})))
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h)
    (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p}) :
    {p | IsSubMergingSaddle S n h p}.ncard + 1 = morseCount S n h 0 ∧
      {p | IsSuperMergingSaddle S n h p}.ncard + 1 = morseCount S n h 2 :=
  count_submerging hS hc hconn hn
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_closed hS hc hn hh' hab hreg)
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_open hS hc hn hh' hab hreg)
    h_closure hh hM hinj

/-- prop:morse-count, PARTIAL: `c₀ - c₁ + c₂ ≤ 2`, with cor:sublevel-stable (i), (ii)
discharged; the remaining named hypotheses are `h_closure` (lem:sublevel-closure) and
`h_merge_disjoint` (lem:merge-disjoint), exactly as in `morse_count_le_two`. -/
theorem morse_count_le_two_of_closure {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_closure : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ p, IsSurfaceCriticalPoint S h p →
      (surfaceIndex S n h p = 0 →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1) ∧
      (IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p})) ∧
      (surfaceIndex S n h p ≠ 0 → ¬ IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p})))
    (h_merge_disjoint : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} →
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p))
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h) :
    (morseCount S n h 0 : ℤ) - morseCount S n h 1 + morseCount S n h 2 ≤ 2 :=
  morse_count_le_two hS hc hconn hn
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_closed hS hc hn hh' hab hreg)
    (fun _ hh' _ _ _ _ hab hreg => componentCount_sublevel_open hS hc hn hh' hab hreg)
    h_closure h_merge_disjoint hh hM

end LiquidDrop
