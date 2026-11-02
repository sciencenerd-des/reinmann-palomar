/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinZeta
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

/-! Analytic continuation of the actual order-twelve periodic remainder. -/
noncomputable section
namespace Reinmann.EulerMaclaurinAnalytic
open Polynomial MeasureTheory Set Finset Filter Asymptotics
open EulerMaclaurinFinite EulerMaclaurinZeta
open scoped Topology Interval

/-- A fixed, integrable Mellin kernel; the positive cutoff removes its origin. -/
def cutoff (N : ℝ) : ℝ → ℂ := (Ioi N).indicator (EulerMaclaurinTail.integrand 0)

theorem cutoff_locallyIntegrable {N : ℝ} (hN : 0 < N) :
    LocallyIntegrableOn (cutoff N) (Ioi 0) :=
  ((EulerMaclaurinTail.integrand_integrable (s := 0) (by norm_num) hN).integrable_indicator
    measurableSet_Ioi).locallyIntegrable.locallyIntegrableOn _

theorem cutoff_top (N : ℝ) : cutoff N =O[atTop] (fun t : ℝ => t^(-12 : ℝ)) := by
  refine isBigO_iff.mpr ⟨6112/15015, ?_⟩
  filter_upwards [eventually_gt_atTop (max N 0)] with t ht
  have ht0 : 0 < t := (le_max_right N 0).trans_lt ht
  have htN : N < t := (le_max_left N 0).trans_lt ht
  simpa [cutoff, htN, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _), abs_of_pos ht0] using!
    EulerMaclaurinTail.integrand_norm_le (0 : ℂ) ht0

theorem cutoff_zero {N : ℝ} (hN : 0 < N) (a : ℝ) :
    cutoff N =O[𝓝[>] 0] (fun t : ℝ => t^a) := by
  refine (isBigO_zero (fun t : ℝ => t^a) (𝓝[>] 0)).congr' ?_ (EventuallyEq.refl _ _)
  apply Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_lt_nhds hN] with t ht
  simp [cutoff, not_lt_of_ge ht.le]

theorem integral_eq_mellin {N : ℝ} (hN : 0 < N) (s : ℂ) :
    (∫ t in Ioi N, EulerMaclaurinTail.integrand s t) = mellin (cutoff N) (1-s) := by
  unfold mellin cutoff
  simp only [← indicator_smul]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset
    (by intro t ht; exact hN.trans ht)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN.trans ht).ne'
  dsimp [EulerMaclaurinTail.integrand]
  simp only [neg_zero, zero_sub]
  rw [show (1 : ℂ)-s-1 = -s by ring]
  rw [sub_eq_add_neg (-s) (12 : ℂ), Complex.cpow_add _ _ ht0]
  ring

theorem integral_differentiableAt {N : ℝ} (hN : 0 < N) {s : ℂ} (hs : -11 < s.re) :
    DifferentiableAt ℂ (fun z => ∫ t in Ioi N, EulerMaclaurinTail.integrand z t) s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (s := 1-s) (a := 12) (b := (1-s).re-1) (cutoff_locallyIntegrable hN)
    (cutoff_top N) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    (cutoff_zero hN _) (by linarith)
  have he : (fun z => ∫ t in Ioi N, EulerMaclaurinTail.integrand z t) =
      fun z => mellin (cutoff N) (1-z) := funext (integral_eq_mellin hN)
  rw [he]
  exact hm.comp s ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)

theorem power_differentiableAt (s : ℂ) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (fun z => power z k x) s := by
  have hbase : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  exact ((ascPochhammer ℂ k).hasDerivAt s).differentiableAt.mul
    ((differentiableAt_id.neg.sub_const (k : ℂ)).const_cpow (Or.inl hbase))

theorem correction_differentiableAt (s : ℂ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (fun z => correction z x) s := by
  apply DifferentiableAt.fun_sum
  intro k _
  exact (power_differentiableAt s (k+1) hx).const_mul
    (BernoulliQuadrature.kernel (k+2) 0)

theorem model_differentiableAt {s : ℂ} (hs : s ≠ 1) (N : ℕ) (hN : 0 < N) :
    DifferentiableAt ℂ (fun z => finiteModel z N) s := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbase : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : DifferentiableAt ℂ (fun z => initialSum z N) s := by
    apply DifferentiableAt.fun_sum
    intro n _
    exact power_differentiableAt s 0 (by positivity)
  exact ((hi.add ((((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow
    (Or.inl hbase)).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs))).add
    ((power_differentiableAt s 0 hNr).div_const 2)).add
    (correction_differentiableAt s hNr)

theorem remainder_differentiableAt {s : ℂ} (hs : -11 < s.re) (N : ℕ) (hN : 0 < N) :
    DifferentiableAt ℂ (fun z => EulerMaclaurinTail.remainder z N) s :=
  (((ascPochhammer ℂ 12).hasDerivAt s).differentiableAt.neg.div_const _).mul
    (integral_differentiableAt (by exact_mod_cast hN) hs)

/-- Analytic continuation on the upper half-strip, which contains the entire
unit disk about 1/2+14i used by the hard-tile evaluator. -/
theorem zeta_eq_model_add_remainder_upper {s : ℂ} (hs : -11 < s.re) (him : 0 < s.im)
    (N : ℕ) (hN : 0 < N) :
    riemannZeta s = finiteModel s N + EulerMaclaurinTail.remainder s N := by
  let U : Set ℂ := {z | -11 < z.re} ∩ {z | 0 < z.im}
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hconn : IsPreconnected U :=
    ((convex_halfSpace_re_gt (-11)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hz_ne {z : ℂ} (hz : z ∈ U) : z ≠ 1 := by
    intro h
    have hi := hz.2
    rw [h] at hi
    norm_num at hi
  have hZ : AnalyticOnNhd ℂ riemannZeta U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_riemannZeta (hz_ne hz)).differentiableWithinAt
  have hM : AnalyticOnNhd ℂ (fun z => finiteModel z N + EulerMaclaurinTail.remainder z N) U := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact ((model_differentiableAt (hz_ne hz) N hN).add
      (remainder_differentiableAt hz.1 N hN)).differentiableWithinAt
  have hpoint : (2+Complex.I : ℂ) ∈ U := by
    constructor <;> norm_num
  have hfg : riemannZeta =ᶠ[𝓝 (2+Complex.I)]
      (fun z => finiteModel z N + EulerMaclaurinTail.remainder z N) := by
    have hnhds : {z : ℂ | 1 < z.re} ∈ 𝓝 (2+Complex.I) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnhds] with z hz
    exact EulerMaclaurinZeta.zeta_eq_model_add_remainder hz N hN
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hM hconn hpoint hfg ⟨hs,him⟩

/-- An explicit error bound for the actual zeta function on the upper half-strip. -/
theorem zeta_error_le_upper {s : ℂ} (hs : -11 < s.re) (him : 0 < s.im)
    (N : ℕ) (hN : 0 < N) :
    ‖riemannZeta s - finiteModel s N‖ ≤
      ‖(ascPochhammer ℂ 12).eval s‖ / ((12 : ℕ).factorial : ℝ) *
        ((6112/15015 : ℝ)*(N : ℝ)^(-s.re-11)/(s.re+11)) := by
  rw [zeta_eq_model_add_remainder_upper hs him N hN, add_sub_cancel_left]
  exact EulerMaclaurinTail.remainder_norm_le hs (by exact_mod_cast hN)

def hardCentre : ℂ := 1/2 + 14*Complex.I

/-- The full closed unit disk used for the ordinary jet calculation stays
strictly inside the domain of the continued remainder identity. -/
theorem hard_disk_domain {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) :
    -11 < s.re ∧ 0 < s.im := by
  have hcs : ‖hardCentre - s‖ ≤ 1 := by rw [norm_sub_rev]; exact hs
  have hr := (Complex.re_le_norm (hardCentre - s)).trans hcs
  have hi := (Complex.im_le_norm (hardCentre - s)).trans hcs
  norm_num [hardCentre, Complex.sub_re, Complex.sub_im] at hr hi
  constructor <;> linarith

theorem hard_disk_identity {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) (N : ℕ) (hN : 0 < N) :
    riemannZeta s = finiteModel s N + EulerMaclaurinTail.remainder s N :=
  zeta_eq_model_add_remainder_upper (hard_disk_domain hs).1 (hard_disk_domain hs).2 N hN

theorem hard_disk_error_le {s : ℂ} (hs : ‖s - hardCentre‖ ≤ 1) (N : ℕ) (hN : 0 < N) :
    ‖riemannZeta s - finiteModel s N‖ ≤
      ‖(ascPochhammer ℂ 12).eval s‖ / ((12 : ℕ).factorial : ℝ) *
        ((6112/15015 : ℝ)*(N : ℝ)^(-s.re-11)/(s.re+11)) :=
  zeta_error_le_upper (hard_disk_domain hs).1 (hard_disk_domain hs).2 N hN

end Reinmann.EulerMaclaurinAnalytic
