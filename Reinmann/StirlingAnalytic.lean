/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.StirlingGamma
public import Reinmann.EulerMaclaurinAnalytic
public import Reinmann.GammaHeightMajorant
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Holomorphy and uniform hard-disk bounds for the actual Stirling remainder. -/
noncomputable section
namespace Reinmann.StirlingAnalytic
open MeasureTheory Set Finset Filter
open StirlingCell StirlingSum StirlingGamma
open scoped Topology

def derivIntegrand (w : ℂ) (t : ℝ) : ℂ :=
  (EulerMaclaurinTail.periodicTwelve t : ℂ) * (w + (t : ℂ))^(-13 : ℤ)

theorem tailIntegrand_eq (w : ℂ) (t : ℝ) :
    tailIntegrand w t = -(EulerMaclaurinTail.periodicTwelve t : ℂ)/12 *
      (w + (t : ℂ))^(-12 : ℤ) := by
  norm_num [tailIntegrand, logChain]
  ring

theorem integrand_hasDerivAt {w : ℂ} {t : ℝ} (hne : w + (t : ℂ) ≠ 0) :
    HasDerivAt (fun z => tailIntegrand z t) (derivIntegrand w t) w := by
  have he : (fun z => tailIntegrand z t) =
      fun z => -(EulerMaclaurinTail.periodicTwelve t : ℂ)/12 *
        (z+(t : ℂ))^(-12 : ℤ) := funext (fun z => tailIntegrand_eq z t)
  rw [he]
  have h := ((hasDerivAt_zpow (-12) (w + (t : ℂ)) (Or.inl hne)).comp w
    ((hasDerivAt_id w).add_const (t : ℂ))).const_mul
      (-(EulerMaclaurinTail.periodicTwelve t : ℂ)/12)
  convert h using 1
  all_goals try rfl
  norm_num [derivIntegrand]
  ring

theorem derivIntegrand_measurable (w : ℂ) :
    AEStronglyMeasurable (derivIntegrand w) volume := by
  have hp : Measurable (fun t : ℝ => (w + (t : ℂ))^(-13 : ℤ)) :=
    (measurable_const.add Complex.continuous_ofReal.measurable).pow_const _
  have hb : Measurable (fun t : ℝ => (EulerMaclaurinTail.periodicTwelve t : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp EulerMaclaurinTail.periodicTwelve_measurable
  exact (hb.mul hp).aestronglyMeasurable

theorem derivIntegrand_norm_le {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : a ≤ w.re)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖derivIntegrand w t‖ ≤ ((6112/15015 : ℝ)/a) * (1/(a+t)^12) := by
  have hpos : 0 < a+t := by linarith
  have hn : a+t ≤ ‖w + (t : ℂ)‖ := by
    calc a+t ≤ w.re+t := by linarith
      _ = (w + (t : ℂ)).re := by simp
      _ ≤ ‖w + (t : ℂ)‖ := Complex.re_le_norm _
  have hpow := pow_le_pow_left₀ hpos.le hn 13
  have hi := one_div_le_one_div_of_le (by positivity : 0 < (a+t)^13) hpow
  rw [derivIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_zpow, zpow_neg, zpow_ofNat, ← one_div]
  calc
    _ ≤ (6112/15015 : ℝ) * (1/(a+t)^13) :=
      mul_le_mul (EulerMaclaurinTail.periodicTwelve_abs_le t) hi
        (by positivity) (by norm_num)
    _ = ((6112/15015 : ℝ)/(a+t)) * (1/(a+t)^12) := by
      rw [pow_succ]
      field_simp
    _ ≤ ((6112/15015 : ℝ)/a) * (1/(a+t)^12) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by norm_num) ha (by linarith)

/-- Differentiate the actual periodic integral with a local, integrable bound. -/
theorem tail_hasDerivAt (w : ℂ) (hw : 0 < w.re) :
    HasDerivAt tail (∫ t in Ioi (0 : ℝ), derivIntegrand w t) w := by
  let a : ℝ := w.re/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hball : ∀ z ∈ Metric.ball w a, a ≤ z.re := by
    intro z hz
    have hn : ‖w - z‖ < a := by
      rw [norm_sub_rev]
      simpa only [dist_eq_norm] using! Metric.mem_ball.mp hz
    have hr := (Complex.re_le_norm (w - z)).trans_lt hn
    simp only [Complex.sub_re] at hr
    dsimp [a] at hr ⊢
    linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := tailIntegrand) (F' := derivIntegrand)
    (bound := fun t : ℝ => ((6112/15015 : ℝ)/a) * (1/(a+t)^12))
    (Metric.ball_mem_nhds w ha)
    (Eventually.of_forall (fun z => (tailIntegrand_measurable z).restrict))
    (tailIntegrand_integrableOn w hw)
    (derivIntegrand_measurable w).restrict
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      exact derivIntegrand_norm_le ha (hball z hz) ht.le)
    ((majorant_integral ha).1.const_mul ((6112/15015 : ℝ)/a))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      apply integrand_hasDerivAt
      apply add_ne_zero_of_re_pos
      simp only [Complex.add_re, Complex.ofReal_re]
      have hza := hball z hz
      linarith [show (0 : ℝ) < t from ht])
  exact h.2

theorem tail_differentiableAt (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ tail w := (tail_hasDerivAt w hw).differentiableAt

/-- The *unit* disk for the ordinary jet, not just the smaller final tile. -/
theorem hard_disk_shift_re {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    (47/4 : ℝ) ≤ (s/2+12).re := by
  have hn : ‖EulerMaclaurinAnalytic.hardCentre - s‖ ≤ 1 := by rw [norm_sub_rev]; exact hs
  have hr := (Complex.re_le_norm (EulerMaclaurinAnalytic.hardCentre - s)).trans hn
  norm_num [EulerMaclaurinAnalytic.hardCentre, Complex.sub_re] at hr
  norm_num [Complex.add_re, Complex.div_re]
  linarith

/-- A rational, kernel-checked bound for the logarithmic remainder on the
whole hard unit disk, sufficient as input to a subsequent Cauchy estimate. -/
theorem hard_disk_tail_norm_le {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    ‖tail (s/2+12)‖ ≤ (1/10^14 : ℝ) := by
  have hr := hard_disk_shift_re hs
  have hpos : 0 < (s/2+12).re := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 47/4) hr 11
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 11*(47/4)^11)
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 11))
  calc ‖tail (s/2+12)‖ ≤ (6112/15015 : ℝ)/12 * (1/(11*(s/2+12).re^11)) :=
      tail_norm_le _ hpos
    _ ≤ (6112/15015 : ℝ)/12 * (1/(11*(47/4)^11)) :=
      mul_le_mul_of_nonneg_left hi (by norm_num)
    _ ≤ (1/10^14 : ℝ) := by norm_num

def shiftedTail (s : ℂ) : ℂ := tail (s/2+12)

def relativeError (s : ℂ) : ℂ := Complex.exp (shiftedTail s)-1

def gammaApprox (s : ℂ) : ℂ :=
  Complex.exp (mainTerm (s/2+12)) / ∏ j ∈ range 12, (s/2+(j : ℂ))

def gammaError (s : ℂ) : ℂ := Complex.Gamma (s/2)-gammaApprox s

theorem shiftedTail_differentiableAt {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    DifferentiableAt ℂ shiftedTail s :=
  (tail_differentiableAt _ (by have h := hard_disk_shift_re hs; linarith)).comp s
    ((differentiableAt_id.div_const 2).add_const 12)

theorem shiftedTail_diffContOnCl :
    DiffContOnCl ℂ shiftedTail (Metric.ball EulerMaclaurinAnalytic.hardCentre 1) := by
  apply DifferentiableOn.diffContOnCl
  intro s hs
  rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hs
  exact (shiftedTail_differentiableAt (mem_closedBall_iff_norm.mp hs)).differentiableWithinAt

theorem shiftedTail_coefficient_le (n : ℕ) :
    ‖iteratedDeriv n shiftedTail EulerMaclaurinAnalytic.hardCentre / (n.factorial : ℂ)‖ ≤
      (1/10^14 : ℝ) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) shiftedTail_diffContOnCl
    (fun z hz => hard_disk_tail_norm_le (mem_sphere_iff_norm.mp hz).le)
  simp only [one_pow, div_one] at h
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

theorem relativeError_norm_le {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    ‖relativeError s‖ ≤ (2/10^14 : ℝ) := by
  have ht := hard_disk_tail_norm_le hs
  exact (Complex.norm_exp_sub_one_le (by dsimp [shiftedTail]; linarith :
    ‖shiftedTail s‖ ≤ 1)).trans (by dsimp [shiftedTail]; linarith)

theorem hard_disk_factors_ne {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) (j : ℕ) : s/2+(j : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [Complex.add_im, Complex.div_im] at hi
  have hpos := (EulerMaclaurinAnalytic.hard_disk_domain hs).2
  linarith

theorem gamma_identity {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    Complex.Gamma (s/2) = gammaApprox s*(1+relativeError s) := by
  rw [Gamma_eq_shift (s/2) 12 (by have h := hard_disk_shift_re hs; linarith)
    (fun j _ => hard_disk_factors_ne hs j), Complex.exp_add]
  dsimp [gammaApprox, relativeError, shiftedTail]
  ring

theorem gammaApprox_eq {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    gammaApprox s = Complex.Gamma (s/2) * Complex.exp (-shiftedTail s) := by
  calc gammaApprox s = gammaApprox s *
      (Complex.exp (shiftedTail s)*Complex.exp (-shiftedTail s)) := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [gamma_identity hs]; dsimp [relativeError]; ring

/-- A deliberately coarse bound, sufficient to make the Gamma remainder
absolute without any unproved numerical circle majorant. -/
theorem gamma_norm_le_one {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) : ‖Complex.Gamma (s/2)‖ ≤ 1 := by
  have hn : ‖EulerMaclaurinAnalytic.hardCentre - s‖ ≤ 1 := by rw [norm_sub_rev]; exact hs
  have hrl := (Complex.re_le_norm (EulerMaclaurinAnalytic.hardCentre - s)).trans hn
  have hil := (Complex.im_le_norm (EulerMaclaurinAnalytic.hardCentre - s)).trans hn
  have hru := (Complex.re_le_norm (s - EulerMaclaurinAnalytic.hardCentre)).trans hs
  norm_num [EulerMaclaurinAnalytic.hardCentre, Complex.sub_re, Complex.sub_im] at hrl hil hru
  have hrlo : (47/4 : ℝ) ≤ (s/2).re+12 := by norm_num [Complex.div_re]; linarith
  have hrhi : (s/2).re+12 ≤ (13 : ℝ) := by norm_num [Complex.div_re]; linarith
  have him : (13/2 : ℝ) ≤ |(s/2).im| := by
    norm_num [Complex.div_im]
    exact (by linarith : (13/2 : ℝ) ≤ s.im/2).trans (le_abs_self _)
  have hG := GammaHeightMajorant.gamma_norm_le_height (s := s/2)
    (by norm_num : (0 : ℝ) < 13/2) him 12 (by linarith)
  have hreal : Real.Gamma ((s/2).re+12) ≤ (12 : ℕ).factorial := by
    have h := Real.Gamma_strictMonoOn_Ici.monotoneOn
      (show (s/2).re+12 ∈ Set.Ici (2 : ℝ) by change 2 ≤ (s/2).re+12; linarith)
      (show (13 : ℝ) ∈ Ici (2 : ℝ) by norm_num) hrhi
    have hn := Real.Gamma_nat_eq_factorial 12
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hn
    exact h.trans_eq hn
  calc ‖Complex.Gamma (s/2)‖ ≤ Real.Gamma ((s/2).re+12)/(13/2)^12 := hG
    _ ≤ ((12 : ℕ).factorial : ℝ)/(13/2)^12 :=
      div_le_div_of_nonneg_right hreal (by positivity)
    _ ≤ 1 := by norm_num

theorem gammaApprox_norm_le_two {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) : ‖gammaApprox s‖ ≤ 2 := by
  have ht : ‖shiftedTail s‖ ≤ (1/10^14 : ℝ) := hard_disk_tail_norm_le hs
  have he : ‖Complex.exp (-shiftedTail s)‖ ≤ 2 := by
    have h := Complex.norm_exp_sub_one_le (x := -shiftedTail s) (by rw [norm_neg]; linarith)
    have htri := norm_add_le (Complex.exp (-shiftedTail s)-1) (1 : ℂ)
    simp only [sub_add_cancel, norm_one, norm_neg] at htri h
    linarith
  rw [gammaApprox_eq hs, norm_mul]
  exact (mul_le_mul (gamma_norm_le_one hs) he (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem gammaError_norm_le {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    ‖gammaError s‖ ≤ (4/10^14 : ℝ) := by
  have he : gammaError s = gammaApprox s*relativeError s := by
    rw [gammaError, gamma_identity hs]; ring
  rw [he, norm_mul]
  exact (mul_le_mul (gammaApprox_norm_le_two hs) (relativeError_norm_le hs)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem corr_zero_differentiableAt (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ (fun z => corr z 0) w := by
  have hne : w ≠ 0 := by intro h; simp [h] at hw
  have he : (fun z => corr z 0) = fun z => -∑ k ∈ range 11,
      (bernoulli (k+2) : ℂ) / (((k : ℂ)+1)*((k : ℂ)+2)) * z^(-((k : ℤ)+1)) :=
    funext corr_zero_eq
  rw [he]
  apply DifferentiableAt.neg
  apply DifferentiableAt.fun_sum
  intro k _
  exact ((hasDerivAt_zpow (-((k : ℤ)+1)) w (Or.inl hne)).differentiableAt).const_mul _

theorem mainTerm_differentiableAt (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ mainTerm w :=
  (((((differentiableAt_id.sub_const (1/2 : ℂ)).mul
    (Complex.hasDerivAt_log (Or.inl hw)).differentiableAt).sub differentiableAt_id).add_const
    ((Real.log (2*Real.pi) : ℂ)/2)).sub (corr_zero_differentiableAt w hw))

theorem gammaApprox_differentiableAt {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    DifferentiableAt ℂ gammaApprox s := by
  have hshift : DifferentiableAt ℂ (fun z : ℂ => z/2+12) s :=
    (differentiableAt_id.div_const 2).add_const 12
  have hmain := (mainTerm_differentiableAt (s/2+12)
    (by have h := hard_disk_shift_re hs; linarith)).comp s hshift
  have hprod : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ range 12, (z/2+(j : ℂ))) s := by
    apply DifferentiableAt.fun_finsetProd
    intro j _
    exact (differentiableAt_id.div_const 2).add_const (j : ℂ)
  exact hmain.cexp.div hprod (prod_ne_zero_iff.mpr (fun j _ => hard_disk_factors_ne hs j))

theorem gamma_factor_differentiableAt {s : ℂ}
    (hs : ‖s - EulerMaclaurinAnalytic.hardCentre‖ ≤ 1) :
    DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z/2)) s := by
  have hg : DifferentiableAt ℂ Complex.Gamma (s/2) :=
    Complex.differentiableAt_Gamma (s/2) (by
      intro m h
      have hi := congrArg Complex.im h
      norm_num [Complex.div_im] at hi
      have hpos := (EulerMaclaurinAnalytic.hard_disk_domain hs).2
      linarith)
  exact hg.comp s (differentiableAt_id.div_const 2)

theorem gammaError_diffContOnCl :
    DiffContOnCl ℂ gammaError (Metric.ball EulerMaclaurinAnalytic.hardCentre 1) := by
  apply DifferentiableOn.diffContOnCl
  intro s hs
  rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hs
  have hn := mem_closedBall_iff_norm.mp hs
  exact ((gamma_factor_differentiableAt hn).sub
    (gammaApprox_differentiableAt hn)).differentiableWithinAt

/-- Every ordinary Gamma jet coefficient of the actual approximation error
is bounded by 4e-14. The whole unit circle is proved, with no numeric majorant
hypothesis and no assumption that the Stirling remainder is analytic. -/
theorem gammaError_coefficient_le (n : ℕ) :
    ‖iteratedDeriv n gammaError EulerMaclaurinAnalytic.hardCentre / (n.factorial : ℂ)‖ ≤
      (4/10^14 : ℝ) := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1) gammaError_diffContOnCl
    (fun z hz => gammaError_norm_le (mem_sphere_iff_norm.mp hz).le)
  simp only [one_pow, div_one] at h
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr (h.trans_eq (by ring))

/-- The same bound explicitly compares the ordinary coefficients of the
actual Gamma factor and of the finite Stirling approximant. -/
theorem gamma_coefficient_error_le (n : ℕ) :
    ‖iteratedDeriv n (fun z : ℂ => Complex.Gamma (z/2)) EulerMaclaurinAnalytic.hardCentre /
        (n.factorial : ℂ) -
      iteratedDeriv n gammaApprox EulerMaclaurinAnalytic.hardCentre / (n.factorial : ℂ)‖ ≤
      (4/10^14 : ℝ) := by
  have hF : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (z/2))
      EulerMaclaurinAnalytic.hardCentre := by
    apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
      _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    intro z hz
    exact (gamma_factor_differentiableAt (mem_ball_iff_norm.mp hz).le).differentiableWithinAt
  have hG : AnalyticAt ℂ gammaApprox EulerMaclaurinAnalytic.hardCentre := by
    apply DifferentiableOn.analyticAt (s := Metric.ball EulerMaclaurinAnalytic.hardCentre 1)
      _ (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    intro z hz
    exact (gammaApprox_differentiableAt (mem_ball_iff_norm.mp hz).le).differentiableWithinAt
  have h := gammaError_coefficient_le n
  rw [show gammaError = (fun z : ℂ => Complex.Gamma (z/2)-gammaApprox z) from rfl] at h
  rw [iteratedDeriv_fun_sub hF.contDiffAt hG.contDiffAt, sub_div] at h
  exact h

end Reinmann.StirlingAnalytic
