module

public import NoCompromise.Flow.FlowBoxCk
public import NoCompromise.Surface.MorseBand

@[expose] public section

/-!
# Smooth regular Morse bands

`lem:morse-band`: the regular band is a smooth product. Both the flow
parametrization and its explicit inverse extend to smooth ambient maps.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace LiquidDrop

/-- `lem:morse-band`, with a smooth ambient flow and the smooth explicit inverse
from `eq:band-inverse`. All the trajectory and inverse identities of `morse_band`
are retained. -/
theorem morse_band_smooth {S : Set E₃} {n : E₃ → E₃} (hS : IsSmoothEmbeddedSurface S)
    (hc : IsCompact S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    ∃ Φ : ℝ → E₃ → E₃, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E₃ => Φ q.1 q.2) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun q => (Φ (a - h q) q, h q - a)) ∧
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
    exists_compactSupport_eq_near_contDiff hW hX hK hKW
  obtain ⟨L, M, hL, hM⟩ := lipschitz_bounded_of_hasCompactSupport (hY.of_le (by simp)) hYc
  let Φ := globalFlow Y hL hM
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × E₃ => Φ q.1 q.2) :=
    contDiff_smooth_globalFlow_uncurry hL hM hY
  have hband (p : E₃) (hp : p ∈ S) (hhp : h p ∈ Icc a b) :
      ∀ t ∈ Icc (a - h p) (b - h p), Φ t p ∈ S ∧ h (Φ t p) = h p + t := by
    have H := integralCurve_morse_band hS hc.isClosed hn (hh.of_le (by simp)) hV hKV
      (fun x hx => (hVW hx).2) (hY.of_le (by simp)).contDiffOn heq
      (fun t => hasDerivAt_globalFlow hL hM p t)
      (by simpa only [globalFlow_zero] using hp)
      (by simpa only [globalFlow_zero] using hhp)
    simpa only [globalFlow_zero] using H
  have hforward (p : E₃) (hp : p ∈ S) (hhp : h p = a) (t : ℝ)
      (ht : t ∈ Icc 0 (b - a)) :
      Φ t p ∈ S ∧ h (Φ t p) = a + t := by
    have hpband : h p ∈ Icc a b := by rw [hhp]; exact ⟨le_rfl, hab.le⟩
    simpa only [hhp, sub_self] using hband p hp hpband t (by simpa only [hhp, sub_self] using ht)
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun q => (Φ (a - h q) q, h q - a)) :=
    (hΦ.comp ((contDiff_const.sub hh).prodMk contDiff_id)).prodMk
      (hh.sub contDiff_const)
  refine ⟨Φ, hΦ, hinv, ?_, ?_, ?_⟩
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

/-- The intrinsic product statement for a regular band: the product map is a
bijection onto the band, with the explicit two-sided inverse, and both maps are
restrictions of smooth ambient maps. -/
theorem morse_band_smooth_bijOn {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b : ℝ} (hab : a < b)
    (hreg : ∀ x ∈ S, h x ∈ Icc a b → ¬ IsSurfaceCriticalPoint S h x) :
    ∃ Φ : ℝ → E₃ → E₃,
      ContDiff ℝ (⊤ : ℕ∞) (fun q : E₃ × ℝ => Φ q.2 q.1) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun q => (Φ (a - h q) q, h q - a)) ∧
      BijOn (fun q : E₃ × ℝ => Φ q.2 q.1)
        ((S ∩ h ⁻¹' {a}) ×ˢ Icc 0 (b - a)) (S ∩ h ⁻¹' Icc a b) ∧
      InvOn (fun q => (Φ (a - h q) q, h q - a)) (fun q : E₃ × ℝ => Φ q.2 q.1)
        ((S ∩ h ⁻¹' {a}) ×ˢ Icc 0 (b - a)) (S ∩ h ⁻¹' Icc a b) := by
  obtain ⟨Φ, hΦ, hinv, hforward, hbackward, hleft⟩ :=
    morse_band_smooth hS hc hn hh hab hreg
  have hmap : MapsTo (fun q : E₃ × ℝ => Φ q.2 q.1)
      ((S ∩ h ⁻¹' {a}) ×ˢ Icc 0 (b - a)) (S ∩ h ⁻¹' Icc a b) := by
    intro q hq
    have ht := hforward q.1 hq.1.1 hq.1.2 q.2 hq.2
    refine ⟨ht.1, ?_⟩
    change a ≤ h (Φ q.2 q.1) ∧ h (Φ q.2 q.1) ≤ b
    rw [ht.2.1]
    constructor <;> linarith [hq.2.1, hq.2.2]
  have hmapinv : MapsTo (fun q => (Φ (a - h q) q, h q - a))
      (S ∩ h ⁻¹' Icc a b) ((S ∩ h ⁻¹' {a}) ×ˢ Icc 0 (b - a)) := by
    intro q hq
    have ht := hbackward q hq.1 hq.2
    refine ⟨⟨ht.1, ht.2.1⟩, ?_⟩
    change 0 ≤ h q - a ∧ h q - a ≤ b - a
    constructor <;> linarith [hq.2.1, hq.2.2]
  have hInv : InvOn (fun q => (Φ (a - h q) q, h q - a))
      (fun q : E₃ × ℝ => Φ q.2 q.1)
      ((S ∩ h ⁻¹' {a}) ×ˢ Icc 0 (b - a)) (S ∩ h ⁻¹' Icc a b) := by
    constructor
    · intro q hq
      apply Prod.ext
      · exact hleft q.1 hq.1.1 hq.1.2 q.2 hq.2
      · change h (Φ q.2 q.1) - a = q.2
        rw [(hforward q.1 hq.1.1 hq.1.2 q.2 hq.2).2.1]
        ring
    · intro q hq
      exact (hbackward q hq.1 hq.2).2.2
  exact ⟨Φ, hΦ.comp (contDiff_snd.prodMk contDiff_fst), hinv,
    hInv.bijOn hmap hmapinv, hInv⟩

end LiquidDrop
