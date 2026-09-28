import NoCompromise.Surface.MorseBand
import NoCompromise.Surface.TotalCurvature

/-!
# Merging saddles and the Morse count (`sec:morse-count`)

`def:merging-saddle` in chart-free form, the component count `componentCount`, and
`lem:count-submerging` and `prop:morse-count` as precise reductions to the named unproved
inputs `cor:sublevel-stable`, `lem:sublevel-closure` and `lem:merge-disjoint`.
-/

noncomputable section
open Set Function InnerProductSpace
namespace LiquidDrop

/-- The number of connected components of `T`, in `ℕ∞` (no finiteness is presupposed). -/
def componentCount (T : Set E₃) : ℕ∞ := ENat.card (ConnectedComponents T)

theorem componentCount_empty : componentCount (∅ : Set E₃) = 0 := by
  rw [componentCount, ENat.card_eq_zero_iff_empty, ConnectedComponents.isEmpty_iff_isEmpty]
  infer_instance

/-- A nonempty connected set has exactly one component. -/
theorem componentCount_eq_one {T : Set E₃} (hT : IsConnected T) : componentCount T = 1 := by
  have : ConnectedSpace T := isConnected_iff_connectedSpace.mp hT
  apply le_antisymm
  · exact (ENat.card_le_one_iff_subsingleton _).mpr inferInstance
  · exact (ENat.one_le_card_iff_nonempty _).mpr inferInstance

private lemma connectedComponents_mk_eq_mk_iff {T : Set E₃} (x y : T) :
    (ConnectedComponents.mk x = ConnectedComponents.mk y) ↔
      (y : E₃) ∈ connectedComponentIn T x := by
  rw [ConnectedComponents.coe_eq_coe, eq_comm, connectedComponent_eq_iff_mem,
    connectedComponentIn_eq_image x.2]
  exact (Subtype.val_injective.mem_set_image).symm

/-- Bridge from membership in connected components to equality of component counts: if every
point of `T` is joined in `T` to a point of `A ⊆ T`, and the inclusion preserves and reflects
membership in components, then `A` and `T` have the same number of components. -/
theorem componentCount_eq_of_connectedComponentIn {A T : Set E₃} (hAT : A ⊆ T)
    (hsurj : ∀ x ∈ T, ∃ y ∈ A, y ∈ connectedComponentIn T x)
    (hiff : ∀ x ∈ A, ∀ y ∈ A,
      y ∈ connectedComponentIn T x ↔ y ∈ connectedComponentIn A x) :
    componentCount A = componentCount T := by
  have hc : Continuous (Set.inclusion hAT) := continuous_inclusion hAT
  have hF : ∀ a : A, hc.connectedComponentsMap (ConnectedComponents.mk a) =
      ConnectedComponents.mk (Set.inclusion hAT a) := fun a => hc.connectedComponentsMap_mk a
  refine ENat.card_congr (Equiv.ofBijective hc.connectedComponentsMap ⟨?_, ?_⟩)
  · intro u v huv
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe u
    obtain ⟨b, rfl⟩ := ConnectedComponents.surjective_coe v
    rw [hF, hF, connectedComponents_mk_eq_mk_iff] at huv
    rw [connectedComponents_mk_eq_mk_iff]
    exact (hiff a a.2 b b.2).mp huv
  · intro u
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe u
    obtain ⟨y, hy, hyx⟩ := hsurj x x.2
    refine ⟨ConnectedComponents.mk ⟨y, hy⟩, ?_⟩
    rw [hF, connectedComponents_mk_eq_mk_iff]
    change (x : E₃) ∈ connectedComponentIn T y
    rw [← connectedComponentIn_eq hyx]
    exact mem_connectedComponentIn x.2

/-- `cor:sublevel-stable (i)` in the regular case, as an equality of component counts. -/
theorem componentCount_sublevel_of_regular
    {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}) := by
  obtain ⟨h1, h2⟩ := connectedComponentIn_sublevel_of_regular hS hc hn hh hab hreg
  exact componentCount_eq_of_connectedComponentIn
    (fun q hq => ⟨hq.1, le_trans hq.2 hab.le⟩) h1 h2

/-- def:merging-saddle (sub-merging), chart-free form: `p` is an index-one critical point and
two distinct components of `N := S ∩ {h < h p}` both have `p` in their closure.
By lem:local-sectors (iii) the components of `{h < c}` whose closure contains `p` are exactly
`A(S⁻₁₂)` and `A(S⁻₃₄)`, so this is equivalent to `A(S⁻₁₂) ≠ A(S⁻₃₄)`; that equivalence is to be
proved once the surface Morse chart is available. -/
def IsSubMergingSaddle (S : Set E₃) (n : E₃ → E₃) (h : E₃ → ℝ) (p : E₃) : Prop :=
  IsSurfaceCriticalPoint S h p ∧ surfaceIndex S n h p = 1 ∧
    ∃ x ∈ S ∩ {z | h z < h p}, ∃ y ∈ S ∩ {z | h z < h p},
      connectedComponentIn (S ∩ {z | h z < h p}) x ≠
          connectedComponentIn (S ∩ {z | h z < h p}) y ∧
        p ∈ closure (connectedComponentIn (S ∩ {z | h z < h p}) x) ∧
        p ∈ closure (connectedComponentIn (S ∩ {z | h z < h p}) y)

/-- def:merging-saddle (super-merging), chart-free form: as `IsSubMergingSaddle` with the
superlevel set `S ∩ {h > h p}`; equivalent (via lem:local-sectors (iii)) to
`B(S⁺₂₃) ≠ B(S⁺₄₁)`. -/
def IsSuperMergingSaddle (S : Set E₃) (n : E₃ → E₃) (h : E₃ → ℝ) (p : E₃) : Prop :=
  IsSurfaceCriticalPoint S h p ∧ surfaceIndex S n h p = 1 ∧
    ∃ x ∈ S ∩ {z | h p < h z}, ∃ y ∈ S ∩ {z | h p < h z},
      connectedComponentIn (S ∩ {z | h p < h z}) x ≠
          connectedComponentIn (S ∩ {z | h p < h z}) y ∧
        p ∈ closure (connectedComponentIn (S ∩ {z | h p < h z}) x) ∧
        p ∈ closure (connectedComponentIn (S ∩ {z | h p < h z}) y)

theorem isSurfaceCriticalPoint_neg_iff {S : Set E₃} {h : E₃ → ℝ} {p : E₃} :
    IsSurfaceCriticalPoint S (fun x => -h x) p ↔ IsSurfaceCriticalPoint S h p := by
  simp [IsSurfaceCriticalPoint, fderiv_fun_neg]

/-- The critical points of `h'` coincide with those of `h` and the indices agree there, so the
index counts agree. -/
private lemma morseCount_congr {S : Set E₃} {n : E₃ → E₃} {h h' : E₃ → ℝ}
    (hcrit : ∀ x, IsSurfaceCriticalPoint S h' x ↔ IsSurfaceCriticalPoint S h x)
    (hind : ∀ p, IsSurfaceCriticalPoint S h p → surfaceIndex S n h' p = surfaceIndex S n h p)
    (k : ℕ) : morseCount S n h' k = morseCount S n h k := by
  unfold morseCount
  congr 1
  ext p
  constructor
  · rintro ⟨hp, hk⟩
    exact ⟨(hcrit p).mp hp, (hind p ((hcrit p).mp hp)).symm.trans hk⟩
  · rintro ⟨hp, hk⟩
    exact ⟨(hcrit p).mpr hp, (hind p hp).trans hk⟩

/-- prop:morse-count from the conclusion of lem:count-submerging, for one Morse function with
distinct critical values: the sub- and super-merging saddles are disjoint subsets of the finite
set of index-one critical points. -/
theorem morse_count_of_merging_counts {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 2 h) (hM : IsSurfaceMorse S n h)
    (hsub : {p | IsSubMergingSaddle S n h p}.ncard + 1 = morseCount S n h 0)
    (hsup : {p | IsSuperMergingSaddle S n h p}.ncard + 1 = morseCount S n h 2)
    (hdisj : ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p)) :
    (morseCount S n h 0 : ℤ) - morseCount S n h 1 + morseCount S n h 2 ≤ 2 := by
  have hfin : {p | IsSurfaceCriticalPoint S h p}.Finite :=
    finite_criticalPoints_of_isSurfaceMorse hS hc hn hh hM
  set I := {p | IsSurfaceCriticalPoint S h p ∧ surfaceIndex S n h p = 1} with hI
  have hIfin : I.Finite := hfin.subset fun p hp => hp.1
  have hsubI : {p | IsSubMergingSaddle S n h p} ⊆ I := fun p hp => ⟨hp.1, hp.2.1⟩
  have hsupI : {p | IsSuperMergingSaddle S n h p} ⊆ I := fun p hp => ⟨hp.1, hp.2.1⟩
  have hD : Disjoint {p | IsSubMergingSaddle S n h p} {p | IsSuperMergingSaddle S n h p} :=
    Set.disjoint_left.mpr fun p h1 h2 => hdisj p ⟨h1, h2⟩
  have hU := Set.ncard_union_eq hD (hIfin.subset hsubI) (hIfin.subset hsupI)
  have hle := Set.ncard_le_ncard (Set.union_subset hsubI hsupI) hIfin
  have h1 : morseCount S n h 1 = I.ncard := rfl
  omega

open Filter Topology in
/-- The telescoping core of lem:count-submerging for one Morse function `h` with distinct
critical values, from the three sublevel inputs specialised to `h`. -/
private lemma count_submerging_core {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hM : IsSurfaceMorse S n h) (hinj : InjOn h {p | IsSurfaceCriticalPoint S h p})
    (h_stable_closed : ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ioc a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}))
    (h_stable_open : ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ico a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}))
    (h_closure : ∀ p, IsSurfaceCriticalPoint S h p →
      (surfaceIndex S n h p = 0 →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}) + 1) ∧
      (IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) + 1 = componentCount (S ∩ {x | h x < h p})) ∧
      (surfaceIndex S n h p ≠ 0 → ¬ IsSubMergingSaddle S n h p →
        componentCount (S ∩ {x | h x ≤ h p}) = componentCount (S ∩ {x | h x < h p}))) :
    {p | IsSubMergingSaddle S n h p}.ncard + 1 = morseCount S n h 0 := by
  classical
  have hfin : {p | IsSurfaceCriticalPoint S h p}.Finite :=
    finite_criticalPoints_of_isSurfaceMorse hS hc hn (hh.of_le (by norm_cast)) hM
  set F := hfin.toFinset with hF
  have hmemF : ∀ p, p ∈ F ↔ IsSurfaceCriticalPoint S h p := fun p => by simp [hF]
  have hcont : Continuous h := hh.continuous
  -- counting functions below a level
  let sub : ℝ → ℕ := fun t => ∑ q ∈ F.filter (fun q => h q < t),
    if IsSubMergingSaddle S n h q then 1 else 0
  let mn : ℝ → ℕ := fun t => ∑ q ∈ F.filter (fun q => h q < t),
    if surfaceIndex S n h q = 0 then 1 else 0
  let N : ℝ → ℕ∞ := fun t => componentCount (S ∩ {x | h x ≤ t})
  have key : ∀ m : ℕ, ∀ t : ℝ, (∀ q ∈ F, h q ≠ t) → (F.filter (fun q => h q < t)).card = m →
      N t + (sub t : ℕ∞) = (mn t : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro t ht hcard
      have hnone : ∀ q ∈ F, t < h q := by
        intro q hq
        rcases lt_or_gt_of_ne (ht q hq) with hlt | hgt
        · have : q ∈ F.filter (fun q => h q < t) := Finset.mem_filter.mpr ⟨hq, hlt⟩
          rw [Finset.card_eq_zero] at hcard
          simp [hcard] at this
        · exact hgt
      have hsub0 : sub t = 0 := by
        simp only [sub, Finset.card_eq_zero.mp hcard, Finset.sum_empty]
      have hmn0 : mn t = 0 := by
        simp only [mn, Finset.card_eq_zero.mp hcard, Finset.sum_empty]
      obtain ⟨B, hB⟩ := (hc.image_of_continuousOn hcont.continuousOn).bddBelow
      have hBle : ∀ x ∈ S, B ≤ h x := fun x hx => hB ⟨x, hx, rfl⟩
      set a := min t B - 1 with ha
      have hat : a < t := by have := min_le_left t B; linarith
      have hempty : S ∩ {x | h x ≤ a} = ∅ := by
        ext x
        simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and,
          not_le]
        intro hx
        have := hBle x hx
        have := min_le_right t B
        linarith
      have hNt : N t = 0 := by
        have := h_stable_closed a t hat (fun p hp hpi => by
          have := hnone p ((hmemF p).mpr hp)
          exact absurd hpi.2 (not_le.mpr this))
        simp only [N]
        rw [← this, hempty, componentCount_empty]
      rw [hNt, hsub0, hmn0]
      simp
    | succ m ih =>
      intro t ht hcard
      set G := F.filter (fun q => h q < t) with hG
      have hGne : G.Nonempty := by
        rw [← Finset.card_pos, hcard]; exact Nat.succ_pos m
      obtain ⟨p, hpG, hpmax⟩ := G.exists_max_image h hGne
      have hpF : p ∈ F := (Finset.mem_filter.mp hpG).1
      have hpt : h p < t := (Finset.mem_filter.mp hpG).2
      have hpc : IsSurfaceCriticalPoint S h p := (hmemF p).mp hpF
      set c := h p with hcdef
      have hev : ∀ᶠ s in 𝓝[<] c, s < c ∧ ∀ q ∈ F, h q < c → h q < s := by
        refine Filter.Eventually.and (eventually_mem_nhdsWithin (s := Iio c)) ?_
        rw [Filter.eventually_all_finset]
        intro q _
        by_cases hq : h q < c
        · exact Filter.Eventually.mono (nhdsWithin_le_nhds (eventually_gt_nhds hq))
            fun s hs _ => hs
        · exact Eventually.of_forall fun s h' => absurd h' hq
      obtain ⟨s, hsc, hs⟩ := hev.exists
      have hbelow : ∀ q ∈ F, h q < t → q ≠ p → h q < c := by
        intro q hq hqt hqp
        have hle := hpmax q (Finset.mem_filter.mpr ⟨hq, hqt⟩)
        rcases hle.lt_or_eq with hlt | heq
        · exact hlt
        · exact absurd (hinj ((hmemF q).mp hq) hpc heq) hqp
      have hGs : G = insert p (F.filter (fun q => h q < s)) := by
        ext q
        simp only [hG, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hq, hqt⟩
          by_cases hqp : q = p
          · exact Or.inl hqp
          · exact Or.inr ⟨hq, hs q hq (hbelow q hq hqt hqp)⟩
        · rintro (rfl | ⟨hq, hqs⟩)
          · exact ⟨hpF, hpt⟩
          · exact ⟨hq, by linarith⟩
      have hpns : p ∉ F.filter (fun q => h q < s) := by
        simp only [Finset.mem_filter, not_and, not_lt]
        intro _; exact hsc.le
      have hcard' : (F.filter (fun q => h q < s)).card = m := by
        have := Finset.card_insert_of_notMem hpns
        rw [← hGs, hcard] at this
        omega
      have hsreg : ∀ q ∈ F, h q ≠ s := by
        intro q hq hqs
        by_cases hqc : h q < c
        · exact (lt_irrefl s) (hqs ▸ hs q hq hqc)
        · exact hqc (hqs ▸ hsc)
      have ihs := ih s hsreg hcard'
      have hopen := h_stable_open s c hsc (fun q hq hqi => by
        have hqF := (hmemF q).mpr hq
        exact (lt_irrefl (h q)) (lt_of_lt_of_le (hs q hqF hqi.2) hqi.1))
      have hclosed := h_stable_closed c t hpt (fun q hq hqi => by
        have hqF := (hmemF q).mpr hq
        have hqt : h q < t := lt_of_le_of_ne hqi.2 (ht q hqF)
        by_cases hqp : q = p
        · rw [hqp] at hqi; exact (lt_irrefl c) hqi.1
        · exact (lt_irrefl (h q)) (lt_trans (hbelow q hqF hqt hqp) hqi.1))
      have hsub_t : sub t = (if IsSubMergingSaddle S n h p then 1 else 0) + sub s := by
        simp only [sub]
        rw [← hG, hGs, Finset.sum_insert hpns]
      have hmn_t : mn t = (if surfaceIndex S n h p = 0 then 1 else 0) + mn s := by
        simp only [mn]
        rw [← hG, hGs, Finset.sum_insert hpns]
      have hNt : N t = componentCount (S ∩ {x | h x ≤ c}) := hclosed.symm
      have hNs : N s = componentCount (S ∩ {x | h x < c}) := hopen
      obtain ⟨h0, h1, h2⟩ := h_closure p hpc
      rw [hsub_t, hmn_t, hNt]
      by_cases hi0 : surfaceIndex S n h p = 0
      · have hns : ¬ IsSubMergingSaddle S n h p := fun hsp => by
          rw [hsp.2.1] at hi0; exact one_ne_zero hi0
        simp only [hns, hi0, ↓reduceIte]
        rw [h0 hi0, ← hNs]
        push_cast
        rw [← ihs]
        ring
      · by_cases hsp : IsSubMergingSaddle S n h p
        · simp only [hsp, hi0, ↓reduceIte]
          push_cast
          rw [← ihs, hNs, ← h1 hsp]
          ring
        · simp only [hsp, hi0, ↓reduceIte]
          push_cast
          rw [← ihs, hNs, h2 hi0 hsp, ← hcdef]
          ring
  -- the top level
  obtain ⟨B, hB⟩ := (hc.image_of_continuousOn hcont.continuousOn).bddAbove
  have hBle : ∀ x ∈ S, h x ≤ B := fun x hx => hB ⟨x, hx, rfl⟩
  have htop_reg : ∀ q ∈ F, h q ≠ B + 1 := by
    intro q hq he
    have := hBle q ((hmemF q).mp hq).1
    linarith
  have hfilter : F.filter (fun q => h q < B + 1) = F := by
    apply Finset.filter_true_of_mem
    intro q hq
    have := hBle q ((hmemF q).mp hq).1
    linarith
  have htop := key _ (B + 1) htop_reg rfl
  have hNtop : N (B + 1) = 1 := by
    simp only [N]
    have : S ∩ {x | h x ≤ B + 1} = S := by
      apply Set.inter_eq_left.mpr
      intro x hx
      have := hBle x hx
      simp only [Set.mem_ofPred_eq]
      linarith
    rw [this, componentCount_eq_one hconn]
  have hsub_eq : sub (B + 1) = {p | IsSubMergingSaddle S n h p}.ncard := by
    simp only [sub, hfilter]
    rw [← Finset.card_filter]
    have : {p | IsSubMergingSaddle S n h p} =
        ↑(F.filter (fun q => IsSubMergingSaddle S n h q)) := by
      ext q
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun hq => ⟨(hmemF q).mpr hq.1, hq⟩, fun hq => hq.2⟩
    rw [this, Set.ncard_coe_finset]
  have hmn_eq : mn (B + 1) = morseCount S n h 0 := by
    simp only [mn, hfilter]
    rw [← Finset.card_filter, morseCount]
    have : {p | IsSurfaceCriticalPoint S h p ∧ surfaceIndex S n h p = 0} =
        ↑(F.filter (fun q => surfaceIndex S n h q = 0)) := by
      ext q
      simp only [Finset.coe_filter, Set.mem_ofPred_eq]
      exact ⟨fun hq => ⟨(hmemF q).mpr hq.1, hq.2⟩, fun hq => ⟨(hmemF q).mp hq.1, hq.2⟩⟩
    rw [this, Set.ncard_coe_finset]
  rw [hNtop, hsub_eq, hmn_eq] at htop
  have : ((({p | IsSubMergingSaddle S n h p}.ncard + 1 : ℕ)) : ℕ∞) = (morseCount S n h 0 : ℕ∞) := by
    push_cast
    rw [← htop]
    ring
  exact_mod_cast this

section FormNeg

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

private lemma formIndex_bdd' (B : V → V → ℝ) :
    BddAbove {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := by
  refine ⟨Module.finrank ℝ V, ?_⟩
  rintro d ⟨W, rfl, _⟩
  exact Submodule.finrank_le W

omit [FiniteDimensional ℝ V] in
private lemma formIndex_nonempty' (B : V → V → ℝ) :
    Set.Nonempty {d | ∃ W : Submodule ℝ V, Module.finrank ℝ W = d ∧
      ∀ x ∈ W, x ≠ 0 → B x x < 0} := by
  refine ⟨0, ⊥, by simp, ?_⟩
  simp

/-- In dimension two, a form homogeneous of degree two along lines and taking both signs has
index one. -/
private lemma formIndex_eq_one_of_mixed' (B : V → V → ℝ) (h2 : Module.finrank ℝ V = 2)
    (hsmul : ∀ (a : ℝ) (x : V), B (a • x) (a • x) = a ^ 2 * B x x)
    (hn : ∃ x, B x x < 0) (hp : ∃ x, 0 < B x x) : formIndex B = 1 := by
  obtain ⟨v, hv⟩ := hn
  obtain ⟨w, hw⟩ := hp
  have h00 : B 0 0 = 0 := by simpa using hsmul 0 0
  have hv0 : v ≠ 0 := by intro h; rw [h, h00] at hv; exact lt_irrefl _ hv
  have hw0 : w ≠ 0 := by intro h; rw [h, h00] at hw; exact lt_irrefl _ hw
  apply le_antisymm
  · apply csSup_le (formIndex_nonempty' B)
    rintro d ⟨W, rfl, hW⟩
    have hle : Module.finrank ℝ W ≤ 2 := h2 ▸ Submodule.finrank_le W
    have hne : Module.finrank ℝ W ≠ 2 := by
      intro he
      have htop := Submodule.eq_top_of_finrank_eq (he.trans h2.symm)
      exact hw.not_gt (hW w (htop ▸ Submodule.mem_top) hw0)
    omega
  · apply le_csSup (formIndex_bdd' B)
    refine ⟨Submodule.span ℝ {v}, finrank_span_singleton hv0, ?_⟩
    intro x hx hx0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ha : a ≠ 0 := by intro h; simp [h] at hx0
    rw [hsmul]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ha) hv

omit [FiniteDimensional ℝ V] in
/-- A positive semidefinite nondegenerate symmetric form is positive definite. -/
private lemma pos_of_nonneg_of_nondegenerate (B : V → V → ℝ)
    (hquad : ∀ (x y : V) (t : ℝ),
      B (x + t • y) (x + t • y) = B x x + 2 * t * B x y + t ^ 2 * B y y)
    (hnd : IsNondegenerateForm B) (hpsd : ∀ x, 0 ≤ B x x) : ∀ x, x ≠ 0 → 0 < B x x := by
  intro x hx
  rcases (hpsd x).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    apply hx
    apply hnd x
    intro y
    have hq : 0 ≤ B y y := hpsd y
    have key := hpsd (x + (-B x y / (B y y + 1)) • y)
    rw [hquad, ← heq] at key
    have hq1 : 0 < B y y + 1 := by linarith
    have key2 := mul_nonneg (sq_nonneg (B y y + 1)) key
    have e : (B y y + 1) ^ 2 * (0 + 2 * (-B x y / (B y y + 1)) * B x y +
        (-B x y / (B y y + 1)) ^ 2 * B y y) = -(B x y) ^ 2 * (B y y + 2) := by
      field_simp
      ring
    rw [e] at key2
    have hb : (B x y) ^ 2 = 0 := by nlinarith [sq_nonneg (B x y)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hb

/-- In dimension two, for a nondegenerate symmetric bilinear form, `ind (-B) = 2 - ind B`. -/
private lemma formIndex_neg_eq (B : V → V → ℝ) (h2 : Module.finrank ℝ V = 2)
    (hquad : ∀ (x y : V) (t : ℝ),
      B (x + t • y) (x + t • y) = B x x + 2 * t * B x y + t ^ 2 * B y y)
    (hsmul : ∀ (a : ℝ) (x : V), B (a • x) (a • x) = a ^ 2 * B x x)
    (hnd : IsNondegenerateForm B) :
    formIndex (fun x y => -B x y) = 2 - formIndex B := by
  have hquad' : ∀ (x y : V) (t : ℝ), -B (x + t • y) (x + t • y) =
      -B x x + 2 * t * (-B x y) + t ^ 2 * (-B y y) := by
    intro x y t; rw [hquad]; ring
  have hnd' : IsNondegenerateForm (fun x y => -B x y) :=
    fun x hx => hnd x fun y => neg_eq_zero.mp (hx y)
  by_cases hneg : ∃ x, B x x < 0
  · by_cases hpos : ∃ x, 0 < B x x
    · have h1 := formIndex_eq_one_of_mixed' B h2 hsmul hneg hpos
      have h1' := formIndex_eq_one_of_mixed' (fun x y => -B x y) h2
        (fun a x => by rw [hsmul]; ring)
        (by obtain ⟨x, hx⟩ := hpos; exact ⟨x, show -B x x < 0 by linarith⟩)
        (by obtain ⟨x, hx⟩ := hneg; exact ⟨x, show 0 < -B x x by linarith⟩)
      rw [h1, h1']
    · simp only [not_exists, not_lt] at hpos
      have hpd := pos_of_nonneg_of_nondegenerate (fun x y => -B x y) hquad' hnd'
        (fun x => show 0 ≤ -B x x by linarith [hpos x])
      rw [formIndex_eq_zero_of_pos _ hpd, formIndex_eq_finrank_of_neg B (fun x hx => by
        have := hpd x hx
        change 0 < -B x x at this
        linarith), h2]
  · simp only [not_exists, not_lt] at hneg
    have hpd := pos_of_nonneg_of_nondegenerate B hquad hnd hneg
    rw [formIndex_eq_zero_of_pos B hpd, formIndex_eq_finrank_of_neg _ (fun x hx => by
      have := hpd x hx
      change -B x x < 0
      linarith), h2]

end FormNeg

/-- The tangential Hessian of `-h` is minus that of `h`. -/
theorem tangentHessian_neg (S : Set E₃) (n : E₃ → E₃) (h : E₃ → ℝ) (p : E₃) :
    tangentHessian S n (fun x => -h x) p = fun X Y => -tangentHessian S n h p X Y := by
  have h1 : fderiv ℝ (fun x => -h x) = fun x => -fderiv ℝ h x := funext fun x => fderiv_fun_neg
  funext X Y
  simp only [tangentHessian, surfaceHessian, h1, fderiv_fun_neg, neg_apply]
  ring

private lemma tangentHessian_quad {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ 2 h) {p : E₃} (hp : p ∈ S)
    (x y : tangentPlane S p) (t : ℝ) :
    tangentHessian S n h p (x + t • y) (x + t • y) = tangentHessian S n h p x x +
      2 * t * tangentHessian S n h p x y + t ^ 2 * tangentHessian S n h p y y := by
  have hsymm : fderiv ℝ (fderiv ℝ h) p y x = fderiv ℝ (fderiv ℝ h) p x y :=
    (hh.contDiffAt.isSymmSndFDerivAt (by simp)) y x
  have hsff : secondFundamentalForm n p y x = secondFundamentalForm n p x y :=
    secondFundamentalForm_symm hS hn hp y.2 x.2
  simp only [secondFundamentalForm] at hsff
  simp only [tangentHessian, surfaceHessian, Submodule.coe_add, Submodule.coe_smul, map_add,
    map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, secondFundamentalForm, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [hsymm, hsff]
  ring

private lemma tangentHessian_smul {S : Set E₃} {n : E₃ → E₃} {h : E₃ → ℝ} {p : E₃}
    (a : ℝ) (x : tangentPlane S p) :
    tangentHessian S n h p (a • x) (a • x) = a ^ 2 * tangentHessian S n h p x x := by
  simp only [tangentHessian, surfaceHessian, Submodule.coe_smul, map_smul,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, secondFundamentalForm,
    real_inner_smul_left, real_inner_smul_right]
  ring

theorem surfaceIndex_le_two {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    {h : E₃ → ℝ} {p : E₃} (hp : p ∈ S) : surfaceIndex S n h p ≤ 2 :=
  hS.finrank_tangentPlane hp ▸ formIndex_le_finrank _

/-- At a nondegenerate critical point of a `C²` function on a surface,
`ind_p(-h) = 2 - ind_p(h)`. -/
theorem surfaceIndex_neg {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ 2 h) {p : E₃}
    (hp : p ∈ S) (hnd : IsNondegenerateForm (tangentHessian S n h p)) :
    surfaceIndex S n (fun x => -h x) p = 2 - surfaceIndex S n h p := by
  unfold surfaceIndex
  rw [tangentHessian_neg]
  exact formIndex_neg_eq _ (hS.finrank_tangentPlane hp) (tangentHessian_quad hS hn hh hp)
    tangentHessian_smul hnd

theorem isSurfaceMorse_neg {S : Set E₃} {n : E₃ → E₃} {h : E₃ → ℝ}
    (hM : IsSurfaceMorse S n h) : IsSurfaceMorse S n (fun x => -h x) := by
  intro p hp
  rw [isSurfaceCriticalPoint_neg_iff] at hp
  rw [tangentHessian_neg]
  exact fun X hX => hM p hp X fun Y => neg_eq_zero.mp (hX Y)

/-- Super-merging for `h` is sub-merging for `-h` (since `{-h < -c} = {h > c}` and the index-one
points of `h` and `-h` coincide). -/
theorem isSuperMergingSaddle_iff_neg {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ 2 h) (hM : IsSurfaceMorse S n h) {p : E₃} :
    IsSuperMergingSaddle S n h p ↔ IsSubMergingSaddle S n (fun x => -h x) p := by
  simp only [IsSubMergingSaddle, IsSuperMergingSaddle, neg_lt_neg_iff,
    isSurfaceCriticalPoint_neg_iff]
  constructor
  · rintro ⟨hc, hi, rest⟩
    exact ⟨hc, by rw [surfaceIndex_neg hS hn hh hc.1 (hM p hc), hi], rest⟩
  · rintro ⟨hc, hi, rest⟩
    refine ⟨hc, ?_, rest⟩
    rw [surfaceIndex_neg hS hn hh hc.1 (hM p hc)] at hi
    omega

/-- `c₀(-h) = c₂(h)` for a `C²` Morse function on a surface. -/
theorem morseCount_neg_zero {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ 2 h) (hM : IsSurfaceMorse S n h) :
    morseCount S n (fun x => -h x) 0 = morseCount S n h 2 := by
  unfold morseCount
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, isSurfaceCriticalPoint_neg_iff]
  constructor
  · rintro ⟨hc, hi⟩
    rw [surfaceIndex_neg hS hn hh hc.1 (hM p hc)] at hi
    have := surfaceIndex_le_two (n := n) (h := h) hS hc.1
    exact ⟨hc, by omega⟩
  · rintro ⟨hc, hi⟩
    exact ⟨hc, by rw [surfaceIndex_neg hS hn hh hc.1 (hM p hc), hi]⟩

/-- lem:count-submerging, PARTIAL: for a smooth Morse `h` with pairwise distinct critical values
on the compact connected surface `S`, the number of sub-merging saddles is `c₀ - 1` and the
number of super-merging saddles is `c₂ - 1` (telescoping over the critical values; the second
count is the first one applied to `-h`). The named hypotheses are the unproved inputs, each
quantified over all smooth Morse functions with distinct critical values on `S` so that it can
be applied to `-h`:
* `h_stable_closed` (cor:sublevel-stable (i)): for `a < b` with no critical value in `(a, b]`,
  `S ∩ {h ≤ a}` and `S ∩ {h ≤ b}` have the same number of components (the case with no
  critical point in `[a, b]` is `componentCount_sublevel_of_regular`);
* `h_stable_open` (cor:sublevel-stable (ii)): for `a < b` with no critical value in `[a, b)`,
  `S ∩ {h ≤ a}` and `S ∩ {h < b}` have the same number of components;
* `h_closure` (lem:sublevel-closure): at a critical point `p` with `c = h p`,
  `#comp {h ≤ c} = #comp {h < c} + 1` at a minimum, `#comp {h ≤ c} + 1 = #comp {h < c}` at a
  sub-merging saddle, and equality otherwise. -/
theorem count_submerging {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_stable_closed : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ioc a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}))
    (h_stable_open : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ico a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}))
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
      {p | IsSuperMergingSaddle S n h p}.ncard + 1 = morseCount S n h 2 := by
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by norm_cast)
  refine ⟨count_submerging_core hS hc hconn hn hh hM hinj (h_stable_closed h hh hM hinj)
    (h_stable_open h hh hM hinj) (h_closure h hh hM hinj), ?_⟩
  have hh' : ContDiff ℝ (⊤ : ℕ∞) (fun x => -h x) := hh.neg
  have hM' := isSurfaceMorse_neg hM
  have hinj' : InjOn (fun x => -h x) {p | IsSurfaceCriticalPoint S (fun x => -h x) p} := by
    intro a ha b hb hab
    simp only [Set.mem_ofPred_eq, isSurfaceCriticalPoint_neg_iff] at ha hb
    exact hinj ha hb (neg_inj.mp hab)
  have key := count_submerging_core hS hc hconn hn hh' hM' hinj'
    (h_stable_closed _ hh' hM' hinj') (h_stable_open _ hh' hM' hinj')
    (h_closure _ hh' hM' hinj')
  rw [morseCount_neg_zero hS hn hh2 hM] at key
  have hset : {p | IsSuperMergingSaddle S n h p} =
      {p | IsSubMergingSaddle S n (fun x => -h x) p} := by
    ext p
    exact isSuperMergingSaddle_iff_neg hS hn hh2 hM
  rw [hset]
  exact key

/-- prop:morse-count, PARTIAL: `c₀ - c₁ + c₂ ≤ 2` for every smooth Morse function on the compact
connected surface `S`. The reduction to distinct critical values is
`exists_morse_distinct_critical_values` (lem:morse-distinct, proved). The named hypotheses are the
unproved inputs `h_stable_closed`, `h_stable_open` (cor:sublevel-stable (i), (ii)) and
`h_closure` (lem:sublevel-closure) of `count_submerging`, and
* `h_merge_disjoint` (lem:merge-disjoint): no saddle of a smooth Morse function with distinct
  critical values is both sub-merging and super-merging. -/
theorem morse_count_le_two {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_stable_closed : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ioc a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}))
    (h_stable_open : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ico a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}))
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
    (morseCount S n h 0 : ℤ) - morseCount S n h 1 + morseCount S n h 2 ≤ 2 := by
  obtain ⟨h', hh', hcrit, hind, hM', hinj⟩ :=
    exists_morse_distinct_critical_values hS hc hn hh hM
  have hinj' : InjOn h' {p | IsSurfaceCriticalPoint S h' p} := by
    intro a ha b hb
    exact hinj ((hcrit a).mp ha) ((hcrit b).mp hb)
  obtain ⟨hsub, hsup⟩ := count_submerging hS hc hconn hn h_stable_closed h_stable_open
    h_closure hh' hM' hinj'
  have key := morse_count_of_merging_counts hS hc hn (hh'.of_le (by norm_cast)) hM' hsub hsup
    (h_merge_disjoint h' hh' hM' hinj')
  have hcong := fun k => morseCount_congr (S := S) (n := n) hcrit (fun p hp => (hind p hp).2) k
  rw [hcong 0, hcong 1, hcong 2] at key
  exact key

/-- prop:morse-count for height functions, PARTIAL: discharges the hypothesis `h_morse_count` of
`total_curvature_le_of_total_curvature_index` for a compact connected surface, from the named
unproved inputs `h_stable_closed`, `h_stable_open` (cor:sublevel-stable (i), (ii)), `h_closure`
(lem:sublevel-closure) and `h_merge_disjoint` (lem:merge-disjoint) of `morse_count_le_two`. -/
theorem morse_count_height_le_two {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_stable_closed : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ioc a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}))
    (h_stable_open : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ico a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}))
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
      ∀ p, ¬ (IsSubMergingSaddle S n h p ∧ IsSuperMergingSaddle S n h p)) :
    ∀ v : E₃, ‖v‖ = 1 → IsSurfaceMorse S n (fun x => inner ℝ x v) →
      (morseCount S n (fun x => inner ℝ x v) 0 : ℤ) - morseCount S n (fun x => inner ℝ x v) 1 +
        morseCount S n (fun x => inner ℝ x v) 2 ≤ 2 := by
  intro v _ hM
  exact morse_count_le_two hS hc hconn hn h_stable_closed h_stable_open h_closure
    h_merge_disjoint (contDiff_id.inner ℝ contDiff_const) hM

open MeasureTheory in
/-- thm:total-curvature-bound, PARTIAL, for a compact connected surface: `∫_Σ κ dH² ≤ 4π`, with
`h_morse_count` of `total_curvature_le_of_total_curvature_index` discharged by
`morse_count_height_le_two`. The named hypotheses are the unproved inputs:
* `h_sard_charts` (cor:sard-charts): almost every point of `S²` is a regular value of the Gauss
  map;
* `h_stable_closed`, `h_stable_open` (cor:sublevel-stable (i), (ii)), `h_closure`
  (lem:sublevel-closure), `h_merge_disjoint` (lem:merge-disjoint), as in `morse_count_le_two`;
* `h_total_curvature_index` (thm:total-curvature-index). -/
theorem total_curvature_le_of_morse_merge {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hconn : IsConnected S)
    (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y)
    (h_stable_closed : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ioc a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x ≤ b}))
    (h_stable_open : ∀ h : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → IsSurfaceMorse S n h →
      InjOn h {p | IsSurfaceCriticalPoint S h p} → ∀ a b : ℝ, a < b →
      (∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Ico a b) →
      componentCount (S ∩ {x | h x ≤ a}) = componentCount (S ∩ {x | h x < b}))
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
    (h_total_curvature_index :
      Integrable (fun y => (gaussIndexSum S n y : ℝ))
          ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) ∧
        ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) =
          ∫ y in Metric.sphere (0 : E₃) 1, (gaussIndexSum S n y : ℝ) ∂(hausdorffMeasure2 3)) :
    ∫ x in S, gaussCurvature S n x ∂(hausdorffMeasure2 3) ≤ 4 * Real.pi :=
  total_curvature_le_of_total_curvature_index hS hc hn h_sard_charts
    (morse_count_height_le_two hS hc hconn hn h_stable_closed h_stable_open h_closure
      h_merge_disjoint) h_total_curvature_index

end LiquidDrop
