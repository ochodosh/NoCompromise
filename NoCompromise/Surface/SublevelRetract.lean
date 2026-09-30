module

public import NoCompromise.Surface.MorseDischarged

@[expose] public section

/-!
# Deformation retractions of sublevels

Compatible localized band flows give the retraction across a half-open regular
band, allowing critical points at its excluded upper endpoint.

For closed sublevels, a uniform limit of stopped flows gives a retraction under
the explicit gradient-height estimate `h - a ≤ C ‖∇_Σ h‖²`.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- A localized regular-band flow, including the band-field differential equation
at every time for which the height remains in the band. -/
theorem morse_band_trajectories {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ}
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    ∃ Φ : ℝ → E₃ → E₃, ContDiff ℝ 1 (fun p : ℝ × E₃ => Φ p.1 p.2) ∧
      (∀ q, Φ 0 q = q) ∧
      ∀ q ∈ S, h q ∈ Icc a b → ∀ t ∈ Icc (a - h q) (b - h q),
        Φ t q ∈ S ∧ h (Φ t q) = h q + t ∧
          HasDerivAt (fun s => Φ s q) (bandField n h (Φ t q)) t := by
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
  refine ⟨Φ, contDiff_one_globalFlow_uncurry hL hM hY,
    fun q => globalFlow_zero hL hM q, ?_⟩
  intro q hq hhq t ht
  have H := integralCurve_morse_band hS hc.isClosed hn (hh.of_le (by simp)) hV hKV
    (fun x hx => (hVW hx).2) hY.contDiffOn heq
    (fun t => hasDerivAt_globalFlow hL hM q t)
    (by simpa only [globalFlow_zero] using hq)
    (by simpa only [globalFlow_zero] using hhq)
  simp only [globalFlow_zero] at H
  have hb := H t ht
  refine ⟨hb.1, hb.2, ?_⟩
  have htV : Φ t q ∈ V := hKV ⟨hb.1, by
    change a ≤ h (Φ t q) ∧ h (Φ t q) ≤ b
    rw [hb.2]
    constructor <;> linarith [ht.1, ht.2]⟩
  rw [← heq htV]
  exact hasDerivAt_globalFlow hL hM q t

/-- Band-field trajectories with the same initial value agree on an
order-connected time set in the regular part of the surface. -/
theorem bandField_curve_unique {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {I : Set ℝ} (hI : OrdConnected I) {γ₁ γ₂ : ℝ → E₃} {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (h₁ : ∀ t ∈ I, γ₁ t ∈ S ∧ surfaceGradient n h (γ₁ t) ≠ 0 ∧
      HasDerivAt γ₁ (bandField n h (γ₁ t)) t)
    (h₂ : ∀ t ∈ I, γ₂ t ∈ S ∧ surfaceGradient n h (γ₂ t) ≠ 0 ∧
      HasDerivAt γ₂ (bandField n h (γ₂ t)) t)
    (heq : γ₁ t₀ = γ₂ t₀) : EqOn γ₁ γ₂ I := by
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  obtain ⟨hW, hX⟩ := contDiffOn_bandField hU hnU hh
  exact integralCurve_unique_of_contDiffOn hW (hX.of_le (by simp)) hI ht₀
    (fun t ht => ⟨⟨hSU (h₁ t ht).1, (h₁ t ht).2.1⟩, (h₁ t ht).2.2⟩)
    (fun t ht => ⟨⟨hSU (h₂ t ht).1, (h₂ t ht).2.1⟩, (h₂ t ht).2.2⟩) heq

/-- `cor:sublevel-stable (ii)`: if there is no critical value in `[a,b)`,
the lower closed sublevel is a strong deformation retract of the upper open sublevel. -/
theorem sublevel_deformation_retract_open {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ico a b) :
    let T := S ∩ {x | h x < b}
    let A := S ∩ {x | h x ≤ a}
    ∃ H : ℝ → E₃ → E₃,
      ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ T) ∧
      (∀ q ∈ T, H 0 q = q) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ T, H s q ∈ T) ∧
      (∀ q ∈ T, H 1 q ∈ A) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q) := by
  classical
  dsimp only
  have hregular (c : Ioo a b) :
      ∀ q ∈ S, h q ∈ Icc a c → ¬ IsSurfaceCriticalPoint S h q :=
    fun q _ hq hcrit => hreg q hcrit ⟨hq.1, lt_of_le_of_lt hq.2 c.2.2⟩
  choose Φ hΦ hzero hband using fun c : Ioo a b =>
    morse_band_trajectories hS hc hn hh (hregular c)
  have hagree (c d : Ioo a b) (q : E₃) (hq : q ∈ S)
      (hqa : a ≤ h q) (hqc : h q ≤ c) (hqd : h q ≤ d) :
      EqOn (fun t => Φ c t q) (fun t => Φ d t q) (Icc (a - h q) 0) := by
    have hcurve (e : Ioo a b) (hqe : h q ≤ e) :
        ∀ t ∈ Icc (a - h q) 0, Φ e t q ∈ S ∧
          surfaceGradient n h (Φ e t q) ≠ 0 ∧
          HasDerivAt (fun s => Φ e s q) (bandField n h (Φ e t q)) t := by
      intro t ht
      have hb := hband e q hq ⟨hqa, hqe⟩ t ⟨ht.1, by linarith [ht.2]⟩
      refine ⟨hb.1, ?_, hb.2.2⟩
      intro hz
      have hc := (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hb.1).mpr hz
      apply hreg _ hc
      rw [hb.2.1]
      exact ⟨by linarith [ht.1], by linarith [ht.2, e.2.2]⟩
    exact bandField_curve_unique hn hh ordConnected_Icc ⟨by linarith, le_rfl⟩
      (hcurve c hqc) (hcurve d hqd) (by rw [hzero, hzero])
  let cutoff (q : E₃) (hq : h q < b) : Ioo a b :=
    ⟨(max a (h q) + b) / 2, by
      have := max_lt hab hq
      have := le_max_left a (h q)
      constructor <;> linarith⟩
  have hcut (q : E₃) (hq : h q < b) : h q < cutoff q hq := by
    have := max_lt hab hq
    have := le_max_right a (h q)
    change h q < (max a (h q) + b) / 2
    linarith
  let F (c : Ioo a b) (s : ℝ) (q : E₃) :=
    if h q ≤ a then q else Φ c (s * (a - h q)) q
  have hF (c : Ioo a b) : Continuous (fun p : ℝ × E₃ => F c p.1 p.2) := by
    apply Continuous.if_le continuous_snd
      ((hΦ c).continuous.comp
        ((continuous_fst.mul (continuous_const.sub (hh.continuous.comp continuous_snd))).prodMk
          continuous_snd))
      (hh.continuous.comp continuous_snd) continuous_const
    intro p hp
    change h p.2 = a at hp
    simp [hp, hzero]
  have htime {s : ℝ} (hs : s ∈ Icc 0 1) {q : E₃} (hqa : a ≤ h q) :
      s * (a - h q) ∈ Icc (a - h q) 0 := by
    constructor
    · nlinarith [hs.2]
    · exact mul_nonpos_of_nonneg_of_nonpos hs.1 (sub_nonpos.mpr hqa)
  let H (s : ℝ) (q : E₃) := if hq : h q < b then F (cutoff q hq) s q else q
  have hlocal (c : Ioo a b) {s : ℝ} (hs : s ∈ Icc 0 1)
      {q : E₃} (hq : q ∈ S) (hqc : h q < c) : H s q = F c s q := by
    have hqb : h q < b := hqc.trans c.2.2
    dsimp only [H]
    rw [dite_eq_left hqb]
    by_cases hqa : h q ≤ a
    · simp [F, hqa]
    · simp only [F, ite_eq_right hqa]
      exact hagree (cutoff q hqb) c q hq (not_le.mp hqa).le
        (hcut q hqb).le hqc.le (htime hs (not_le.mp hqa).le)
  have hcont : ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2)
      (Icc 0 1 ×ˢ (S ∩ {x | h x < b})) := by
    intro p hp
    let c := cutoff p.2 hp.2.2
    have heq : (fun z : ℝ × E₃ => H z.1 z.2) =ᶠ[
        𝓝[Icc 0 1 ×ˢ (S ∩ {x | h x < b})] p] (fun z => F c z.1 z.2) := by
      have hnear : ∀ᶠ z : ℝ × E₃ in 𝓝 p, h z.2 < c :=
        (isOpen_lt (hh.continuous.comp continuous_snd) continuous_const).mem_nhds
          (hcut p.2 hp.2.2)
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzT
      exact hlocal c hzT.1 hzT.2.1 hz
    exact (hF c).continuousAt.continuousWithinAt.congr_of_eventuallyEq heq
      (hlocal c hp.1 hp.2.1 (hcut p.2 hp.2.2))
  refine ⟨H, hcont, ?_, ?_, ?_, ?_⟩
  · intro q hq
    simp [H, F, hzero]
  · intro s hs q hq
    rw [hlocal (cutoff q hq.2) hs hq.1 (hcut q hq.2)]
    by_cases hqa : h q ≤ a
    · simpa [F, hqa] using hq
    · simp only [F, ite_eq_right hqa]
      have ht := htime hs (not_le.mp hqa).le
      have hb := hband (cutoff q hq.2) q hq.1
        ⟨(not_le.mp hqa).le, (hcut q hq.2).le⟩ (s * (a - h q))
        ⟨ht.1, by linarith [hcut q hq.2, ht.2]⟩
      refine ⟨hb.1, ?_⟩
      change h (Φ _ _ q) < b
      rw [hb.2.1]
      exact lt_of_le_of_lt (by linarith [ht.2]) hq.2
  · intro q hq
    rw [hlocal (cutoff q hq.2) ⟨zero_le_one, le_rfl⟩ hq.1 (hcut q hq.2)]
    by_cases hqa : h q ≤ a
    · simpa [F, hqa] using (show q ∈ S ∩ {x | h x ≤ a} from ⟨hq.1, hqa⟩)
    · simp only [F, ite_eq_right hqa, one_mul]
      have hb := hband (cutoff q hq.2) q hq.1
        ⟨(not_le.mp hqa).le, (hcut q hq.2).le⟩ (a - h q)
        ⟨le_rfl, by linarith [(cutoff q hq.2).2.1]⟩
      exact ⟨hb.1, by change h (Φ _ _ q) ≤ a; linarith [hb.2.1]⟩
  · intro s hs q hq
    have hqb : h q < b := lt_of_le_of_lt hq.2 hab
    have hqa : h q ≤ a := hq.2
    simp [H, hqb, F, hqa]

/-- The gradient-height estimate gives the inverse square-root bound for the
speed of the band field. -/
theorem bandField_norm_le_of_gradient_bound {n : E₃ → E₃} {h : E₃ → ℝ}
    {x : E₃} {a C : ℝ} (hC : 0 < C) (hxa : a < h x)
    (hkey : h x - a ≤ C * ‖surfaceGradient n h x‖ ^ 2) :
    ‖bandField n h x‖ ≤ Real.sqrt C / Real.sqrt (h x - a) := by
  have hg : 0 < ‖surfaceGradient n h x‖ := by
    by_contra hg
    have hz : ‖surfaceGradient n h x‖ = 0 := le_antisymm (not_lt.mp hg) (norm_nonneg _)
    rw [hz] at hkey
    nlinarith
  have hnorm : ‖bandField n h x‖ = 1 / ‖surfaceGradient n h x‖ := by
    simp only [bandField, norm_smul, Real.norm_eq_abs, abs_inv,
      real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖surfaceGradient n h x‖)]
    field_simp
  rw [hnorm]
  have hs := Real.sqrt_le_sqrt hkey
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)] at hs
  apply (div_le_div_iff₀ hg (Real.sqrt_pos.mpr (sub_pos.mpr hxa))).mpr
  simpa using hs

/-- A band-field trajectory satisfying the gradient-height estimate has the
square-root length bound between any two times in its regular interval. -/
theorem bandField_curve_length_of_gradient_bound {S : Set E₃} {n : E₃ → E₃}
    {h : E₃ → ℝ} {a b C : ℝ} (hC : 0 < C)
    (hkey : ∀ x ∈ S, a < h x → h x ≤ b →
      h x - a ≤ C * ‖surfaceGradient n h x‖ ^ 2)
    {γ : ℝ → E₃} {u v z : ℝ} (huv : u ≤ v)
    (hγ : ∀ t ∈ Icc u v, γ t ∈ S ∧ a < h (γ t) ∧ h (γ t) ≤ b ∧
      h (γ t) = z + t ∧ HasDerivAt γ (bandField n h (γ t)) t) :
    ‖γ v - γ u‖ ≤ 2 * Real.sqrt C *
      (Real.sqrt (z + v - a) - Real.sqrt (z + u - a)) := by
  have hcont : ContinuousOn γ (Icc u v) := fun t ht =>
    (hγ t ht).2.2.2.2.continuousAt.continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc u v) : 0 < z + t - a := by
    have hb := hγ t ht
    rw [hb.2.2.2.1] at hb
    linarith [hb.2.1]
  let B (t : ℝ) := 2 * Real.sqrt C *
    (Real.sqrt (z + t - a) - Real.sqrt (z + u - a))
  have hB (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivAt B (Real.sqrt C / Real.sqrt (z + t - a)) t := by
    have hd := (((hasDerivAt_id t).const_add z).sub_const a).sqrt (ne_of_gt (hpos t ht))
    convert (hd.sub_const (Real.sqrt (z + u - a))).const_mul (2 * Real.sqrt C) using 1
    all_goals first | rfl | (simp only [id_eq]; ring)
  apply image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (hcont.sub continuousOn_const)
    (fun t ht => ((hγ t (Ico_subset_Icc_self ht)).2.2.2.2.sub_const (γ u)).hasDerivWithinAt)
    (B := B) (by simp [B])
    (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ ⟨huv, le_rfl⟩
  intro t ht
  have hb := hγ t (Ico_subset_Icc_self ht)
  simpa only [hb.2.2.2.1] using
    bandField_norm_le_of_gradient_bound hC hb.2.1 (hkey _ hb.1 hb.2.1 hb.2.2.1)

/-- `cor:sublevel-stable (i)`, conditional form: under the gradient-height estimate
`hkey` (no Morse hypothesis is needed for this step), the lower closed sublevel is a
strong deformation retract of the upper closed sublevel. The retraction is obtained
as a uniform limit of regular-band flows stopped above level `a`. -/
theorem sublevel_deformation_retract_closed_of_key {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ p, IsSurfaceCriticalPoint S h p → h p ∉ Set.Ioc a b)
    (hkey : ∃ C > 0, ∀ x ∈ S, a < h x → h x ≤ b →
      h x - a ≤ C * ‖surfaceGradient n h x‖ ^ 2) :
    let T := S ∩ {x | h x ≤ b}
    let A := S ∩ {x | h x ≤ a}
    ∃ H : ℝ → E₃ → E₃,
      ContinuousOn (fun p : ℝ × E₃ => H p.1 p.2) (Icc 0 1 ×ˢ T) ∧
      (∀ q ∈ T, H 0 q = q) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ T, H s q ∈ T) ∧
      (∀ q ∈ T, H 1 q ∈ A) ∧ (∀ s ∈ Icc 0 1, ∀ q ∈ A, H s q = q) := by
  classical
  dsimp only
  obtain ⟨C, hC, hkey⟩ := hkey
  have hregular (c : Ioc a b) :
      ∀ q ∈ S, h q ∈ Icc (c : ℝ) b → ¬ IsSurfaceCriticalPoint S h q :=
    fun q _ hq hcrit => hreg q hcrit ⟨lt_of_lt_of_le c.2.1 hq.1, hq.2⟩
  choose Φ hΦ hzero hband using fun c : Ioc a b =>
    morse_band_trajectories hS hc hn hh (hregular c)
  have hagree (c d : Ioc a b) (hcd : (c : ℝ) ≤ d) (q : E₃) (hq : q ∈ S)
      (hqd : d ≤ h q) (hqb : h q ≤ b) :
      EqOn (fun t => Φ c t q) (fun t => Φ d t q) (Icc (d - h q) 0) := by
    have hcurve (e : Ioc a b) (hed : (e : ℝ) ≤ d) :
        ∀ t ∈ Icc (d - h q) 0, Φ e t q ∈ S ∧
          surfaceGradient n h (Φ e t q) ≠ 0 ∧
          HasDerivAt (fun s => Φ e s q) (bandField n h (Φ e t q)) t := by
      intro t ht
      have hb := hband e q hq ⟨hed.trans hqd, hqb⟩ t
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      refine ⟨hb.1, ?_, hb.2.2⟩
      intro hz
      have hc := (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hb.1).mpr hz
      apply hreg _ hc
      rw [hb.2.1]
      exact ⟨by linarith [ht.1, d.2.1], by linarith [ht.2]⟩
    exact bandField_curve_unique hn hh ordConnected_Icc ⟨by linarith, le_rfl⟩
      (hcurve c hcd) (hcurve d le_rfl) (by rw [hzero, hzero])
  let τ (c : Ioc a b) (s : ℝ) (q : E₃) :=
    max (s * min 0 (a - h q)) (min 0 (c - h q))
  let F (c : Ioc a b) (s : ℝ) (q : E₃) := Φ c (τ c s q) q
  have hF (c : Ioc a b) : Continuous (fun p : ℝ × E₃ => F c p.1 p.2) :=
    (hΦ c).continuous.comp
      (((continuous_fst.mul (continuous_const.min
        (continuous_const.sub (hh.continuous.comp continuous_snd)))).max
        (continuous_const.min (continuous_const.sub (hh.continuous.comp continuous_snd)))).prodMk
          continuous_snd)
  have hτzero (c : Ioc a b) (q : E₃) : τ c 0 q = 0 := by
    simp [τ]
  have hτfix (c : Ioc a b) {s : ℝ} (hs : 0 ≤ s) {q : E₃} (hq : h q ≤ c) :
      τ c s q = 0 := by
    dsimp only [τ]
    rw [min_eq_left (sub_nonneg.mpr hq)]
    exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hs (min_le_left _ _))
  have hτband (c : Ioc a b) {s : ℝ} (hs : s ∈ Icc 0 1) {q : E₃} (hq : c ≤ h q) :
      τ c s q ∈ Icc (c - h q) 0 := by
    dsimp only [τ]
    rw [min_eq_right (sub_nonpos.mpr hq)]
    exact ⟨le_max_right _ _, max_le
      (mul_nonpos_of_nonneg_of_nonpos hs.1 (min_le_left _ _)) (sub_nonpos.mpr hq)⟩
  have hτmono (c d : Ioc a b) (hcd : (c : ℝ) ≤ d) (s : ℝ) (q : E₃) :
      τ c s q ≤ τ d s q :=
    max_le_max le_rfl (min_le_min_left 0 (sub_le_sub_right hcd _))
  have hstay (c : Ioc a b) {s : ℝ} (hs : s ∈ Icc 0 1) {q : E₃}
      (hq : q ∈ S ∩ {x | h x ≤ b}) : F c s q ∈ S ∩ {x | h x ≤ b} := by
    by_cases hqc : h q ≤ c
    · simpa only [F, hτfix c hs.1 hqc, hzero] using hq
    · have ht := hτband c hs (not_le.mp hqc).le
      have hb := hband c q hq.1 ⟨(not_le.mp hqc).le, hq.2⟩ (τ c s q)
        ⟨ht.1, ht.2.trans (sub_nonneg.mpr hq.2)⟩
      refine ⟨hb.1, ?_⟩
      change h (Φ _ _ q) ≤ b
      rw [hb.2.1]
      exact le_trans (by linarith [ht.2]) hq.2
  have hlast (c : Ioc a b) {q : E₃} (hq : q ∈ S ∩ {x | h x ≤ b}) :
      h (F c 1 q) ≤ c := by
    by_cases hqc : h q ≤ c
    · simpa only [F, hτfix c zero_le_one hqc, hzero] using hqc
    · have hqc := (not_le.mp hqc).le
      have hτ : τ c 1 q = c - h q := by
        dsimp only [τ]
        rw [one_mul, min_eq_right (by linarith [c.2.1]),
          min_eq_right (sub_nonpos.mpr hqc), max_eq_right (by linarith [c.2.1])]
      have hb := hband c q hq.1 ⟨hqc, hq.2⟩ (c - h q)
        ⟨le_rfl, sub_le_sub_right c.2.2 _⟩
      change h (Φ c (τ c 1 q) q) ≤ c
      rw [hτ, hb.2.1]
      linarith
  have hcompare (c d : Ioc a b) (hcd : (c : ℝ) ≤ d) {s : ℝ} (hs : s ∈ Icc 0 1)
      {q : E₃} (hq : q ∈ S ∩ {x | h x ≤ b}) :
      dist (F c s q) (F d s q) ≤ 2 * Real.sqrt C * Real.sqrt (d - a) := by
    have hnonneg : 0 ≤ 2 * Real.sqrt C * Real.sqrt (d - a) := by positivity
    by_cases hqc : h q ≤ c
    · simp only [F, hτfix c hs.1 hqc, hτfix d hs.1 (hqc.trans hcd), hzero, dist_self]
      exact hnonneg
    have hqc : c ≤ h q := (not_le.mp hqc).le
    have htc := hτband c hs hqc
    have htd0 : τ d s q ≤ 0 := by
      by_cases hqd : h q ≤ d
      · rw [hτfix d hs.1 hqd]
      · exact (hτband d hs (not_le.mp hqd).le).2
    have heq : F d s q = Φ c (τ d s q) q := by
      by_cases hqd : h q ≤ d
      · simp only [F, hτfix d hs.1 hqd, hzero]
      · exact (hagree c d hcd q hq.1 (not_le.mp hqd).le hq.2
          (hτband d hs (not_le.mp hqd).le)).symm
    rw [heq]
    by_cases ht : τ c s q = τ d s q
    · simp only [F, ht, dist_self]
      exact hnonneg
    have hheight : h q + τ d s q ≤ d := by
      by_cases hqd : h q ≤ d
      · rw [hτfix d hs.1 hqd, add_zero]
        exact hqd
      · have hqd : d ≤ h q := (not_le.mp hqd).le
        have hmax : s * min 0 (a - h q) ≤ d - h q := by
          by_contra hmax
          have hlt := lt_of_not_ge hmax
          apply ht
          dsimp only [τ]
          rw [min_eq_right (sub_nonpos.mpr hqc), min_eq_right (sub_nonpos.mpr hqd),
            max_eq_left (by linarith), max_eq_left hlt.le]
        change h q + max (s * min 0 (a - h q)) (min 0 (d - h q)) ≤ d
        rw [min_eq_right (sub_nonpos.mpr hqd), max_eq_right hmax]
        linarith
    have hlength := bandField_curve_length_of_gradient_bound hC hkey
      (hτmono c d hcd s q) (z := h q) (γ := fun t => Φ c t q) (by
        intro t ht
        have hb := hband c q hq.1 ⟨hqc, hq.2⟩ t
          ⟨htc.1.trans ht.1, ht.2.trans (htd0.trans (sub_nonneg.mpr hq.2))⟩
        exact ⟨hb.1, by rw [hb.2.1]; linarith [ht.1, htc.1, c.2.1],
          by rw [hb.2.1]; exact le_trans (by linarith [ht.2]) hq.2,
          hb.2.1, hb.2.2⟩)
    rw [dist_eq_norm, norm_sub_rev]
    refine hlength.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact le_trans (sub_le_self _ (Real.sqrt_nonneg _))
      (Real.sqrt_le_sqrt (by linarith))
  let c (m : ℕ) : Ioc a b := ⟨a + (b - a) / ((m : ℝ) + 1), by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    constructor
    · exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hab) (by positivity))
    · have hdiv : (b - a) / ((m : ℝ) + 1) ≤ b - a :=
        div_le_self (sub_nonneg.mpr hab.le) (by linarith)
      linarith⟩
  have hc_lim : Tendsto (fun m => (c m : ℝ)) atTop (𝓝 a) := by
    have H : Tendsto (fun m : ℕ => a + (b - a) * (1 / ((m : ℝ) + 1))) atTop
        (𝓝 (a + (b - a) * 0)) := tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [mul_zero, add_zero, mul_one_div] using H
  let D := Icc (0 : ℝ) 1 ×ˢ (S ∩ {x | h x ≤ b})
  have hCauchy : UniformCauchySeqOn (fun m (p : ℝ × E₃) => F (c m) p.1 p.2) atTop D := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    have hlim : Tendsto (fun m => 2 * Real.sqrt C * Real.sqrt ((c m : ℝ) - a))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul ((hc_lim.sub_const a).sqrt)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
    refine ⟨N, ?_⟩
    intro m hm k hk p hp
    rcases le_total (c m) (c k) with hmk | hkm
    · exact lt_of_le_of_lt (hcompare (c m) (c k) hmk hp.1 hp.2) (hN k hk)
    · rw [dist_comm]
      exact lt_of_le_of_lt (hcompare (c k) (c m) hkm hp.1 hp.2) (hN m hm)
  have hex : ∀ p : ℝ × E₃, ∃ y : E₃, p ∈ D →
      Tendsto (fun m => F (c m) p.1 p.2) atTop (𝓝 y) := by
    intro p
    by_cases hp : p ∈ D
    · obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hCauchy.cauchySeq hp)
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun hp' => (hp hp').elim⟩
  choose G hG using hex
  have hGcont : ContinuousOn G D :=
    (hCauchy.tendstoUniformlyOn_of_tendsto hG).continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun m => (hF (c m)).continuousOn))
  refine ⟨fun s q => G (s, q), hGcont, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have hg := hG (0, q) ⟨⟨le_rfl, zero_le_one⟩, hq⟩
    simp only [F, hτzero, hzero] at hg
    exact tendsto_nhds_unique hg tendsto_const_nhds
  · intro s hs q hq
    apply (hc.isClosed.inter (isClosed_le hh.continuous continuous_const)).mem_of_tendsto
      (hG (s, q) ⟨hs, hq⟩)
    exact Filter.Eventually.of_forall fun m => hstay (c m) hs hq
  · intro q hq
    have hg := hG (1, q) ⟨⟨zero_le_one, le_rfl⟩, hq⟩
    refine ⟨hc.isClosed.mem_of_tendsto hg
      (Filter.Eventually.of_forall fun m => (hstay (c m) ⟨zero_le_one, le_rfl⟩ hq).1), ?_⟩
    exact le_of_tendsto_of_tendsto (hh.continuous.continuousAt.tendsto.comp hg) hc_lim
      (Filter.Eventually.of_forall fun m => hlast (c m) hq)
  · intro s hs q hq
    have hqb : q ∈ S ∩ {x | h x ≤ b} := ⟨hq.1, le_trans hq.2 hab.le⟩
    have hg := hG (s, q) ⟨hs, hqb⟩
    have hfix (m : ℕ) : F (c m) s q = q := by
      dsimp only [F]
      rw [hτfix (c m) hs.1 (le_trans hq.2 (c m).2.1.le), hzero]
    simp only [hfix] at hg
    exact tendsto_nhds_unique hg tendsto_const_nhds

end LiquidDrop
