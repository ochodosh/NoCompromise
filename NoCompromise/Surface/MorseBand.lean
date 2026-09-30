module

public import NoCompromise.Surface.Morse
public import NoCompromise.Surface.TangentFlow

@[expose] public section

/-!
# Regular Morse bands

`lem:morse-band`: the flow of the localized band field gives the product
parametrization and the inverse in `eq:band-inverse`. C¹ pending the user's
wording decision: both maps are restrictions of C¹ ambient maps.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- The ambient inverse formula in `eq:band-inverse` is C¹ whenever the flow
and height function are C¹. C¹ pending the user's wording decision. -/
theorem contDiff_morse_band_inverse {Φ : ℝ → E₃ → E₃}
    (hΦ : ContDiff ℝ 1 (fun q : ℝ × E₃ => Φ q.1 q.2))
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) (a : ℝ) :
    ContDiff ℝ 1 (fun q => (Φ (a - h q) q, h q - a)) :=
  (hΦ.comp ((contDiff_const.sub hh).prodMk contDiff_id)).prodMk
    (hh.sub contDiff_const)

/-- Continuation across a regular band for a globally defined integral curve.
The field need only agree with the band field on an open neighbourhood of the band. -/
theorem integralCurve_morse_band {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hSc : IsClosed S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {a b : ℝ}
    {V : Set E₃} (hV : IsOpen V) (hKV : S ∩ h ⁻¹' Icc a b ⊆ V)
    (hreg : ∀ x ∈ V, surfaceGradient n h x ≠ 0)
    {Y : E₃ → E₃} (hY : ContDiffOn ℝ 1 Y V) (heq : EqOn Y (bandField n h) V)
    {γ : ℝ → E₃} (hγ : ∀ t, HasDerivAt γ (Y (γ t)) t)
    (hγS : γ 0 ∈ S) (hγh : h (γ 0) ∈ Icc a b) :
    ∀ t ∈ Icc (a - h (γ 0)) (b - h (γ 0)),
      γ t ∈ S ∧ h (γ t) = h (γ 0) + t := by
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  let I := Icc (a - h (γ 0)) (b - h (γ 0))
  have h0I : (0 : ℝ) ∈ I := by constructor <;> linarith [hγh.1, hγh.2]
  let A : Set I := {t | γ t ∈ S ∧ h (γ t) = h (γ 0) + t}
  have hAc : IsClosed A :=
    (hSc.preimage (hcont.comp continuous_subtype_val)).inter
      (isClosed_eq (hh.continuous.comp (hcont.comp continuous_subtype_val))
        (continuous_const.add continuous_subtype_val))
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    have hsV : γ s ∈ V := hKV ⟨hs.1, by
      change a ≤ h (γ s) ∧ h (γ s) ≤ b
      rw [hs.2]
      have hsI := s.property
      change a - h (γ 0) ≤ (s : ℝ) ∧ (s : ℝ) ≤ b - h (γ 0) at hsI
      constructor <;> linarith [hsI.1, hsI.2]⟩
    obtain ⟨l, u, hslu, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hcont.continuousAt.preimage_mem_nhds (hV.mem_nhds hsV))
    have hmem : ∀ t ∈ Ioo l u, γ t ∈ S :=
      integralCurve_mem_of_tangent hS hSc hV hY
        (fun x hx => (heq hx.2).symm ▸ bandField_mem_tangentPlane hS hn hx.1)
        ordConnected_Ioo hslu (fun t ht => ⟨hlu ht, hγ t⟩) hs.1
    have hd : ∀ t ∈ Ioo l u, HasDerivAt (fun r => h (γ r) - r) 0 t := by
      intro t ht
      have hdt : HasDerivAt γ (bandField n h (γ t)) t := by
        rw [← heq (hlu ht)]
        exact hγ t
      simpa using (hasDerivAt_comp_bandField_curve hn hh hdt (hmem t ht)
        (hreg _ (hlu ht))).fun_sub (hasDerivAt_id' t)
    have hnear : ∀ᶠ t : I in 𝓝 s, (t : ℝ) ∈ Ioo l u :=
      continuous_subtype_val.continuousAt.eventually (isOpen_Ioo.mem_nhds hslu)
    filter_upwards [hnear] with t ht
    refine ⟨hmem t ht, ?_⟩
    have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo l u).isPreconnected
      (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
      (fun r hr => (hd r hr).deriv) ht hslu
    change h (γ t) - (t : ℝ) = h (γ s) - (s : ℝ) at hc
    have hsheight := hs.2
    change h (γ s) = h (γ 0) + (s : ℝ) at hsheight
    change h (γ t) = h (γ 0) + (t : ℝ)
    linarith
  have : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp
    (convex_Icc (a - h (γ 0)) (b - h (γ 0))).isPreconnected
  have hA : A = univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ
    ⟨⟨0, h0I⟩, hγS, by simp⟩
  intro t ht
  exact (show (⟨t, ht⟩ : I) ∈ A from hA ▸ mem_univ _)

/-- `lem:morse-band`, with the inverse from `eq:band-inverse`.
C¹ pending the user's wording decision: `Θ(p,t) = Φ t p` and its displayed
inverse are restrictions of C¹ ambient maps. The field is localized near the
compact regular band to construct a global ambient flow. -/
theorem morse_band {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    ∃ Φ : ℝ → E₃ → E₃, ContDiff ℝ 1 (fun q : ℝ × E₃ => Φ q.1 q.2) ∧
      (∀ p ∈ S, h p = a → ∀ t ∈ Icc 0 (b - a),
        Φ t p ∈ S ∧ h (Φ t p) = a + t ∧
        HasDerivAt (fun s => Φ s p) (bandField n h (Φ t p)) t) ∧
      (∀ q ∈ S, h q ∈ Icc a b →
        Φ (a - h q) q ∈ S ∧ h (Φ (a - h q) q) = a ∧
          Φ (h q - a) (Φ (a - h q) q) = q) ∧
      (∀ p ∈ S, h p = a → ∀ t ∈ Icc 0 (b - a),
        Φ (a - h (Φ t p)) (Φ t p) = p) := by
  let K := S ∩ h ⁻¹' Icc a b
  have hK : IsCompact K := hc.inter_right (isClosed_Icc.preimage hh.continuous)
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  obtain ⟨hW, hX⟩ := contDiffOn_bandField hU hnU hh
  have hKW : K ⊆ U ∩ {x | surfaceGradient n h x ≠ 0} := by
    intro x hx
    exact ⟨hSU hx.1, fun hz => hreg x hx.1 hx.2
      ((isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hx.1).mpr hz)⟩
  obtain ⟨Y, hY, hYc, V, hV, hKV, hVW, heq⟩ :=
    exists_compactSupport_eq_near hW (hX.of_le (by simp)) hK hKW
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  let Φ := globalFlow Y hL hM
  have hΦ : ContDiff ℝ 1 (fun q : ℝ × E₃ => Φ q.1 q.2) :=
    contDiff_one_globalFlow_uncurry hL hM hY
  have hband (p : E₃) (hp : p ∈ S) (hhp : h p ∈ Icc a b) :
      ∀ t ∈ Icc (a - h p) (b - h p), Φ t p ∈ S ∧ h (Φ t p) = h p + t := by
    have H := integralCurve_morse_band hS hc.isClosed hn (hh.of_le (by simp)) hV hKV
      (fun x hx => (hVW hx).2) hY.contDiffOn heq
      (fun t => hasDerivAt_globalFlow hL hM p t)
      (by simpa only [globalFlow_zero] using hp)
      (by simpa only [globalFlow_zero] using hhp)
    simpa only [globalFlow_zero] using H
  have hforward (p : E₃) (hp : p ∈ S) (hhp : h p = a) (t : ℝ)
      (ht : t ∈ Icc 0 (b - a)) :
      Φ t p ∈ S ∧ h (Φ t p) = a + t := by
    have hpband : h p ∈ Icc a b := by rw [hhp]; exact ⟨le_rfl, hab.le⟩
    simpa only [hhp, sub_self] using hband p hp hpband t (by simpa only [hhp, sub_self] using ht)
  refine ⟨Φ, hΦ, ?_, ?_, ?_⟩
  · intro p hp hhp t ht
    have htband := hforward p hp hhp t ht
    refine ⟨htband.1, htband.2, ?_⟩
    have htV : Φ t p ∈ V := hKV ⟨htband.1, by
      change a ≤ h (Φ t p) ∧ h (Φ t p) ≤ b
      rw [htband.2]
      constructor <;> linarith [ht.1, ht.2]⟩
    rw [← heq htV]
    exact hasDerivAt_globalFlow hL hM p t
  · intro q hq hhq
    have ht := hband q hq hhq (a - h q) ⟨le_rfl, by linarith⟩
    refine ⟨ht.1, by linarith [ht.2], ?_⟩
    change globalFlow Y hL hM (h q - a) (globalFlow Y hL hM (a - h q) q) = q
    rw [← globalFlow_add, show h q - a + (a - h q) = 0 by ring, globalFlow_zero]
  · intro p hp hhp t ht
    rw [(hforward p hp hhp t ht).2, show a - (a + t) = -t by ring]
    exact globalFlow_neg_left hL hM t p

/-- `cor:sublevel-stable (i)`, regular case only: the Morse band flow also
controls every partial trajectory and is the identity at time zero.
PARTIAL: a critical point at level `a` is not covered. -/
theorem morse_band_partial {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    ∃ Φ : ℝ → E₃ → E₃, ContDiff ℝ 1 (fun q : ℝ × E₃ => Φ q.1 q.2) ∧
      (∀ p ∈ S, h p = a → ∀ t ∈ Icc 0 (b - a),
        Φ t p ∈ S ∧ h (Φ t p) = a + t ∧
        HasDerivAt (fun s => Φ s p) (bandField n h (Φ t p)) t) ∧
      (∀ q ∈ S, h q ∈ Icc a b →
        Φ (a - h q) q ∈ S ∧ h (Φ (a - h q) q) = a ∧
          Φ (h q - a) (Φ (a - h q) q) = q) ∧
      (∀ p ∈ S, h p = a → ∀ t ∈ Icc 0 (b - a),
        Φ (a - h (Φ t p)) (Φ t p) = p) ∧
      (∀ q ∈ S, h q ∈ Icc a b → ∀ t ∈ Icc (a - h q) (b - h q),
        Φ t q ∈ S ∧ h (Φ t q) = h q + t) ∧
      Φ 0 = id := by
  let K := S ∩ h ⁻¹' Icc a b
  have hK : IsCompact K := hc.inter_right (isClosed_Icc.preimage hh.continuous)
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  obtain ⟨hW, hX⟩ := contDiffOn_bandField hU hnU hh
  have hKW : K ⊆ U ∩ {x | surfaceGradient n h x ≠ 0} := by
    intro x hx
    exact ⟨hSU hx.1, fun hz => hreg x hx.1 hx.2
      ((isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hx.1).mpr hz)⟩
  obtain ⟨Y, hY, hYc, V, hV, hKV, hVW, heq⟩ :=
    exists_compactSupport_eq_near hW (hX.of_le (by simp)) hK hKW
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport hY hYc
  let Φ := globalFlow Y hL hM
  have hΦ : ContDiff ℝ 1 (fun q : ℝ × E₃ => Φ q.1 q.2) :=
    contDiff_one_globalFlow_uncurry hL hM hY
  have hband (p : E₃) (hp : p ∈ S) (hhp : h p ∈ Icc a b) :
      ∀ t ∈ Icc (a - h p) (b - h p), Φ t p ∈ S ∧ h (Φ t p) = h p + t := by
    have H := integralCurve_morse_band hS hc.isClosed hn (hh.of_le (by simp)) hV hKV
      (fun x hx => (hVW hx).2) hY.contDiffOn heq
      (fun t => hasDerivAt_globalFlow hL hM p t)
      (by simpa only [globalFlow_zero] using hp)
      (by simpa only [globalFlow_zero] using hhp)
    simpa only [globalFlow_zero] using H
  have hforward (p : E₃) (hp : p ∈ S) (hhp : h p = a) (t : ℝ)
      (ht : t ∈ Icc 0 (b - a)) :
      Φ t p ∈ S ∧ h (Φ t p) = a + t := by
    have hpband : h p ∈ Icc a b := by rw [hhp]; exact ⟨le_rfl, hab.le⟩
    simpa only [hhp, sub_self] using hband p hp hpband t (by simpa only [hhp, sub_self] using ht)
  refine ⟨Φ, hΦ, ?_, ?_, ?_, hband, ?_⟩
  · intro p hp hhp t ht
    have htband := hforward p hp hhp t ht
    refine ⟨htband.1, htband.2, ?_⟩
    have htV : Φ t p ∈ V := hKV ⟨htband.1, by
      change a ≤ h (Φ t p) ∧ h (Φ t p) ≤ b
      rw [htband.2]
      constructor <;> linarith [ht.1, ht.2]⟩
    rw [← heq htV]
    exact hasDerivAt_globalFlow hL hM p t
  · intro q hq hhq
    have ht := hband q hq hhq (a - h q) ⟨le_rfl, by linarith⟩
    refine ⟨ht.1, by linarith [ht.2], ?_⟩
    change globalFlow Y hL hM (h q - a) (globalFlow Y hL hM (a - h q) q) = q
    rw [← globalFlow_add, show h q - a + (a - h q) = 0 by ring, globalFlow_zero]
  · intro p hp hhp t ht
    rw [(hforward p hp hhp t ht).2, show a - (a + t) = -t by ring]
    exact globalFlow_neg_left hL hM t p
  · funext q
    exact globalFlow_zero hL hM q

/-- `cor:sublevel-stable (i)`, regular case only: the lower closed sublevel
is a deformation retract of the upper closed sublevel.
PARTIAL: a critical point at level `a` is not covered. -/
theorem sublevel_deformation_retract_of_regular
    {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    let T := S ∩ {x | h x ≤ b}
    let A := S ∩ {x | h x ≤ a}
    ∃ H : ℝ → E₃ → E₃,
      ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ T) ∧
      (∀ q ∈ T, H 0 q = q) ∧
      (∀ s ∈ Icc 0 1, ∀ q ∈ T, H s q ∈ T) ∧
      (∀ q ∈ T, H 1 q ∈ A) ∧
      (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q) := by
  classical
  dsimp only
  obtain ⟨Φ, hΦ, _, _, _, hband, hzero⟩ := morse_band_partial hS hc hn hh hab hreg
  have hzero' (q : E₃) : Φ 0 q = q := congrFun hzero q
  let H : ℝ → E₃ → E₃ := fun s q => if h q ≤ a then q else Φ (s * (a - h q)) q
  have hcont : Continuous (fun p : ℝ × E₃ => H p.1 p.2) := by
    apply Continuous.if_le continuous_snd
      (hΦ.continuous.comp
        ((continuous_fst.mul (continuous_const.sub (hh.continuous.comp continuous_snd))).prodMk
          continuous_snd))
      (hh.continuous.comp continuous_snd) continuous_const
    intro p hp
    change h p.2 = a at hp
    simp [hp, hzero']
  have htime (s : ℝ) (hs : s ∈ Icc 0 1) (q : E₃)
      (hqa : a ≤ h q) (hqb : h q ≤ b) :
      s * (a - h q) ∈ Icc (a - h q) (b - h q) := by
    constructor
    · nlinarith [hs.2]
    · have : s * (a - h q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith)
      linarith
  refine ⟨H, hcont.continuousOn, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp [H, hzero']
  · intro s hs q hq
    by_cases hqa : h q ≤ a
    · simpa [H, hqa] using hq
    · have hqband : h q ∈ Icc a b := ⟨(not_le.mp hqa).le, hq.2⟩
      have ht := hband q hq.1 hqband (s * (a - h q)) (htime s hs q hqband.1 hqband.2)
      simp only [H, ite_eq_right hqa]
      refine ⟨ht.1, ?_⟩
      change h (Φ (s * (a - h q)) q) ≤ b
      rw [ht.2]
      have : s * (a - h q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith [hqband.1])
      linarith [hqband.2]
  · intro q hq
    by_cases hqa : h q ≤ a
    · simpa [H, hqa] using (show q ∈ S ∩ {x | h x ≤ a} from ⟨hq.1, hqa⟩)
    · have hqband : h q ∈ Icc a b := ⟨(not_le.mp hqa).le, hq.2⟩
      have ht := hband q hq.1 hqband (a - h q) ⟨le_rfl, by linarith⟩
      simp only [H, ite_eq_right hqa, one_mul]
      exact ⟨ht.1, by change h (Φ (a - h q) q) ≤ a; linarith [ht.2]⟩
  · intro s hs q hq
    have hqa : h q ≤ a := hq.2
    simp [H, hqa]

/-- `cor:sublevel-stable (i)`, regular case only: every upper-sublevel
component meets the lower sublevel, and the inclusion preserves and reflects
membership in connected components.
PARTIAL: a critical point at level `a` is not covered. -/
theorem connectedComponentIn_sublevel_of_regular
    {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    let T := S ∩ {x | h x ≤ b}
    let A := S ∩ {x | h x ≤ a}
    (∀ x ∈ T, ∃ y ∈ A, y ∈ connectedComponentIn T x) ∧
      (∀ x ∈ A, ∀ y ∈ A,
        y ∈ connectedComponentIn T x ↔ y ∈ connectedComponentIn A x) := by
  let T := S ∩ {x | h x ≤ b}
  let A := S ∩ {x | h x ≤ a}
  change (∀ x ∈ T, ∃ y ∈ A, y ∈ connectedComponentIn T x) ∧
    (∀ x ∈ A, ∀ y ∈ A,
      y ∈ connectedComponentIn T x ↔ y ∈ connectedComponentIn A x)
  have hAT : A ⊆ T := fun q hq => ⟨hq.1, le_trans hq.2 hab.le⟩
  obtain ⟨H, hH, hzero, hstay, hlast, hfix⟩ :=
    sublevel_deformation_retract_of_regular hS hc hn hh hab hreg
  have h01 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hr : ContinuousOn (H 1) T :=
    hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun q hq => ⟨h11, hq⟩)
  constructor
  · intro x hx
    refine ⟨H 1 x, hlast x hx, ?_⟩
    have hpath : ContinuousOn (fun s => H s x) (Icc 0 1) :=
      hH.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hx⟩)
    have hp := (convex_Icc (0 : ℝ) 1).isPreconnected.image (fun s => H s x) hpath
    have hsub : (fun s => H s x) '' Icc 0 1 ⊆ connectedComponentIn T x :=
      hp.subset_connectedComponentIn ⟨0, h01, hzero x hx⟩ (by
        rintro q ⟨s, hs, rfl⟩
        exact hstay s hs x hx)
    exact hsub ⟨1, h11, rfl⟩
  · intro x hx y hy
    constructor
    · intro hxy
      have hp := isPreconnected_connectedComponentIn.image (H 1)
        (hr.mono (connectedComponentIn_subset T x))
      have hsub : H 1 '' connectedComponentIn T x ⊆ connectedComponentIn A x :=
        hp.subset_connectedComponentIn
          ⟨x, mem_connectedComponentIn (hAT hx), hfix 1 h11 x hx⟩ (by
            rintro q ⟨z, hz, rfl⟩
            exact hlast z (connectedComponentIn_subset T x hz))
      exact hsub ⟨y, hxy, hfix 1 h11 y hy⟩
    · intro hxy
      exact connectedComponentIn_mono x hAT hxy

end LiquidDrop
