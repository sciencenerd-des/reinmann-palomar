/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.StirlingSum
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

/-! Complex Stirling formula with an explicit order-twelve remainder.

For `0 < Re w`,

    Gamma w = exp ((w - 1/2) Log w - w + log(2π)/2 - corr w 0 + tail w),

where `corr w 0` is the finite Bernoulli correction and
`‖tail w‖ ≤ (6112/15015)/12 · 1/(11 (Re w)^11)`.
The proof uses Euler's limit `GammaSeq_tendsto_Gamma`, the order-twelve
summation of `∑ Log (w + j)`, and Stirling's constant. -/
noncomputable section
namespace Reinmann.StirlingGamma
open MeasureTheory Set Finset Filter Topology
open scoped Interval Nat
open StirlingCell StirlingSum Stirling

/-- The logarithm of Euler's Gamma sequence, with principal logarithms. -/
def seqLog (w : ℂ) (n : ℕ) : ℂ :=
  w * (Real.log n : ℂ) + (Real.log (n ! : ℝ) : ℂ) - ∑ j ∈ range (n+1), logChain w 0 j

theorem GammaSeq_eq_exp (w : ℂ) (hw : 0 < w.re) {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq w n = Complex.exp (seqLog w n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℂ)^w = Complex.exp ((Real.log n : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log hnr.le]
  have hfact : ((n ! : ℕ) : ℂ) = Complex.exp (Real.log (n ! : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast Nat.factorial_pos n)]
    push_cast; rfl
  have hprod : (∏ j ∈ range (n+1), (w + (j : ℂ))) =
      Complex.exp (∑ j ∈ range (n+1), logChain w 0 j) := by
    rw [Complex.exp_sum]
    apply prod_congr rfl
    intro j _
    have hre : 0 < (w + ((j : ℝ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; positivity
    simp only [logChain]
    rw [Complex.exp_log (add_ne_zero_of_re_pos hre)]
    push_cast; rfl
  rw [Complex.GammaSeq, hpow, hfact, hprod, seqLog, ← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  ring

/-- Antiderivative of `Log (w + t)`. -/
theorem integral_logChain (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    (∫ t in (0 : ℝ)..(n : ℝ), logChain w 0 t) =
      ((w + n) * Complex.log (w + n) - (w + n)) - (w * Complex.log w - w) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) n, HasDerivAt
      (fun t : ℝ => (w + t) * Complex.log (w + t) - (w + t)) (logChain w 0 t) t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rcases mem_uIcc.mp ht with h | h
      · exact h.1
      · linarith [h.1, h.2, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hre : 0 < (w + (t : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    have hlin : HasDerivAt (fun s : ℝ => w + (s : ℂ)) 1 t := by
      simpa using! ((hasDerivAt_id (t : ℂ)).const_add w).comp_ofReal
    have hlog := logChain_hasDerivAt w 0 hre
    have h := (hlin.mul hlog).sub hlin
    convert h using 1
    · first | rfl | (funext y; simp [logChain])
    simp only [logChain, CharP.cast_eq_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul,
      zero_add, Int.reduceNeg, zpow_neg, zpow_one]
    field_simp [add_ne_zero_of_re_pos hre]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (logChain_zero_intervalIntegrable w hw (le_refl 0) (Nat.cast_nonneg n))]
  simp

/-- The exact finite-`n` decomposition of the Gamma-sequence logarithm. -/
theorem seqLog_formula (w : ℂ) (hw : 0 < w.re) {n : ℕ} (hn : 0 < n) :
    seqLog w n = (Real.log (stirlingSeq n) : ℂ) + (Real.log 2 : ℂ)/2 -
      (w + n + 1/2) * Complex.log (1 + w/n) + (w - 1/2) * Complex.log w -
      corr w 0 + corr w n + ∫ t in (0 : ℝ)..(n : ℝ), tailIntegrand w t := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum := finite_sum w hw n
  have hint := integral_logChain w hw n
  have hre : 0 < (w + ((n : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hone : (1 : ℂ) + w/n ≠ 0 := by
    intro h
    have : w + (n : ℂ) = 0 := by
      have := congrArg (fun z => (n : ℂ) * z) h
      simp only [mul_add, mul_one, mul_zero] at this
      rw [mul_div_cancel₀ _ hnc] at this
      linear_combination this
    exact add_ne_zero_of_re_pos (by simpa using! hre) this
  have hlogsplit : Complex.log (w + n) = (Real.log n : ℂ) + Complex.log (1 + w/n) := by
    have h := Complex.log_ofReal_mul hnr hone
    rw [← h]
    congr 1
    push_cast
    field_simp
    ring
  have hst := Stirling.log_stirlingSeq_formula n
  have hl2n : Real.log (2*n) = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hnr.ne'
  have hlne : Real.log (n/Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div hnr.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [hl2n, hlne] at hst
  have hstc : (Real.log (stirlingSeq n) : ℂ) = (Real.log (n ! : ℝ) : ℂ) -
      1/2*((Real.log 2 : ℂ) + (Real.log n : ℂ)) - (n : ℂ)*((Real.log n : ℂ) - 1) := by
    rw [hst]; push_cast; ring
  rw [seqLog, sum_range_succ, hsum, hint]
  simp only [logChain, Complex.ofReal_natCast, Complex.ofReal_zero, add_zero]
  rw [hlogsplit, hstc]
  ring

theorem tendsto_log_stirling :
    Tendsto (fun n : ℕ => (Real.log (stirlingSeq n) : ℂ)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi) : ℂ)) := by
  have h := ((Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    tendsto_stirlingSeq_sqrt_pi)
  exact (Complex.continuous_ofReal.tendsto _).comp h

theorem tendsto_div_nat (w : ℂ) : Tendsto (fun n : ℕ => w / (n : ℂ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (((1 : ℝ)/n : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat
  have h2 := h.const_mul w
  simp only [Complex.ofReal_zero, mul_zero] at h2
  refine h2.congr (fun n => ?_)
  push_cast; ring

theorem tendsto_log_one_add (w : ℂ) :
    Tendsto (fun n : ℕ => Complex.log (1 + w/n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + w/(n : ℂ)) atTop (𝓝 1) := by
    simpa using! (tendsto_div_nat w).const_add 1
  have hc := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
  simpa using! hc

theorem tendsto_nat_mul_log_one_add (w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun n : ℕ => (n : ℂ) * Complex.log (1 + w/n)) atTop (𝓝 w) := by
  have hd : HasDerivAt Complex.log 1 1 := by
    simpa using! Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)
  have ht : Tendsto (fun n : ℕ => w / (n : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_div_nat w, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_ne_zero hw (by exact_mod_cast hn.ne')
  have hc := (hd.tendsto_slope_zero.comp ht).const_mul w
  rw [mul_one] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Function.comp, smul_eq_mul, Complex.log_one, sub_zero]
  field_simp

theorem tendsto_inv_add_nat (w : ℂ) (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => (w + ((n : ℝ) : ℂ))⁻¹) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => (w.re + n)⁻¹) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have hpos : 0 < w.re + n := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  rw [norm_inv]
  apply inv_anti₀ hpos
  calc w.re + n = (w + ((n : ℝ) : ℂ)).re := by simp
    _ ≤ ‖w + ((n : ℝ) : ℂ)‖ := Complex.re_le_norm _

theorem tendsto_corr (w : ℂ) (hw : 0 < w.re) :
    Tendsto (fun n : ℕ => corr w n) atTop (𝓝 0) := by
  have hinv := tendsto_inv_add_nat w hw
  have h : ∀ k ∈ range 11, Tendsto (fun n : ℕ => (-1 : ℂ)^(k+1) *
      BernoulliQuadrature.kernel (k+2) 0 * logChain w (k+1) n) atTop (𝓝 0) := by
    intro k _
    have hp := (hinv.pow (k+1)).const_mul
      ((-1 : ℂ)^(k+1) * BernoulliQuadrature.kernel (k+2) 0 * ((-1 : ℂ)^k * (k.factorial : ℂ)))
    rw [zero_pow (Nat.succ_ne_zero k), mul_zero] at hp
    refine hp.congr (fun n => ?_)
    have he : ((k : ℤ)+1) = ((k+1 : ℕ) : ℤ) := by push_cast; ring
    simp only [logChain]
    rw [zpow_neg, he, zpow_natCast, inv_pow]
    ring
  have hs := tendsto_finsetSum (range 11) h
  rw [sum_const_zero] at hs
  exact hs

/-- The explicit main term of the complex Stirling formula. -/
def mainTerm (w : ℂ) : ℂ :=
  (w - 1/2) * Complex.log w - w + (Real.log (2 * Real.pi) : ℂ)/2 - corr w 0

theorem tendsto_seqLog (w : ℂ) (hw : 0 < w.re) :
    Tendsto (seqLog w) atTop (𝓝 (mainTerm w + tail w)) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hB : Tendsto (fun n : ℕ => (w + n + 1/2) * Complex.log (1 + w/n)) atTop (𝓝 w) := by
    have h := (tendsto_nat_mul_log_one_add w hw0).add
      ((tendsto_log_one_add w).const_mul (w + 1/2))
    rw [mul_zero, add_zero] at h
    refine h.congr (fun n => ?_)
    ring
  have hT : Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(n : ℝ), tailIntegrand w t) atTop
      (𝓝 (tail w)) :=
    intervalIntegral_tendsto_integral_Ioi 0 (tailIntegrand_integrableOn w hw)
      tendsto_natCast_atTop_atTop
  have hlim := (((((tendsto_log_stirling.add_const ((Real.log 2 : ℂ)/2)).sub hB).add_const
    ((w - 1/2) * Complex.log w)).sub_const (corr w 0)).add (tendsto_corr w hw)).add hT
  have hr : Real.log (Real.sqrt Real.pi) + Real.log 2 / 2 = Real.log (2 * Real.pi) / 2 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) Real.pi_pos.ne']; ring
  have hc : (Real.log (Real.sqrt Real.pi) : ℂ) + (Real.log 2 : ℂ)/2 =
      (Real.log (2 * Real.pi) : ℂ)/2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hr
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat] using! this
  have hval : (Real.log (Real.sqrt Real.pi) : ℂ) + (Real.log 2 : ℂ)/2 - w +
      (w - 1/2) * Complex.log w - corr w 0 + 0 + tail w = mainTerm w + tail w := by
    rw [mainTerm]; linear_combination hc
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [seqLog_formula w hw hn]

/-- **Complex Stirling formula with explicit remainder.** For `0 < Re w`,
`Γ(w) = exp((w - 1/2) Log w - w + log(2π)/2 - corr w 0 + tail w)`. -/
theorem Gamma_eq (w : ℂ) (hw : 0 < w.re) :
    Complex.Gamma w = Complex.exp (mainTerm w + tail w) := by
  have h2 : Tendsto (Complex.GammaSeq w) atTop (𝓝 (Complex.exp (mainTerm w + tail w))) := by
    refine ((Complex.continuous_exp.tendsto _).comp (tendsto_seqLog w hw)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (GammaSeq_eq_exp w hw hn).symm
  exact tendsto_nhds_unique (Complex.GammaSeq_tendsto_Gamma w) h2

/-- Stirling with the order-twelve remainder bound packaged. -/
theorem Gamma_eq_exp_main_add (w : ℂ) (hw : 0 < w.re) :
    ∃ r : ℂ, Complex.Gamma w = Complex.exp (mainTerm w + r) ∧
      ‖r‖ ≤ (6112/15015 : ℝ)/12 * (1/(11*w.re^11)) :=
  ⟨tail w, Gamma_eq w hw, tail_norm_le w hw⟩

theorem kernel_zero_eq (n : ℕ) :
    BernoulliQuadrature.kernel n 0 = (bernoulli n : ℂ) / (n.factorial : ℂ) := by
  rw [BernoulliQuadrature.kernel, Complex.ofReal_zero, Polynomial.aeval_def,
    Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero, Polynomial.bernoulli_eval_zero]
  simp

/-- The finite correction is the classical Stirling series:
`-corr w 0 = ∑_{k<11} B_{k+2} / ((k+1)(k+2)) · w^{-(k+1)}`. -/
theorem corr_zero_eq (w : ℂ) :
    corr w 0 = -∑ k ∈ range 11,
      (bernoulli (k+2) : ℂ) / (((k : ℂ)+1)*((k : ℂ)+2)) * w^(-((k : ℤ)+1)) := by
  rw [corr, ← sum_neg_distrib]
  refine sum_congr rfl (fun k _ => ?_)
  have hs : (-1 : ℂ)^(k+1) * (-1)^k = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨k, by ring⟩
  have hf : ((k+2).factorial : ℂ) = ((k : ℂ)+1)*((k : ℂ)+2)*(k.factorial : ℂ) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have h1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
  simp only [logChain, kernel_zero_eq, Complex.ofReal_zero, add_zero]
  rw [hf]
  calc (-1 : ℂ)^(k+1) * ((bernoulli (k+2) : ℂ) /
          (((k : ℂ)+1)*((k : ℂ)+2)*(k.factorial : ℂ))) *
        ((-1 : ℂ)^k * (k.factorial : ℂ) * w^(-((k : ℤ)+1)))
      = ((-1 : ℂ)^(k+1) * (-1)^k) * ((bernoulli (k+2) : ℂ) / (((k : ℂ)+1)*((k : ℂ)+2))) *
          w^(-((k : ℤ)+1)) := by
        field_simp
    _ = _ := by rw [hs]; ring

theorem Gamma_add_nat (w : ℂ) (K : ℕ) (h : ∀ j < K, w + (j : ℂ) ≠ 0) :
    Complex.Gamma (w + K) = (∏ j ∈ range K, (w + (j : ℂ))) * Complex.Gamma w := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hK := h K (Nat.lt_succ_self K)
    rw [prod_range_succ, show w + ((K+1 : ℕ) : ℂ) = (w + K) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hK, ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    ring

/-- Shifted Stirling: the evaluator form used on the hard disk, where `Re w` is small
but `Re (w + K)` is large. -/
theorem Gamma_eq_shift (w : ℂ) (K : ℕ) (hw : 0 < (w + K).re)
    (h : ∀ j < K, w + (j : ℂ) ≠ 0) :
    Complex.Gamma w =
      Complex.exp (mainTerm (w + K) + tail (w + K)) / ∏ j ∈ range K, (w + (j : ℂ)) := by
  have hp : (∏ j ∈ range K, (w + (j : ℂ))) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun j hj => h j (mem_range.mp hj))
  rw [← Gamma_eq _ hw, Gamma_add_nat w K h]
  field_simp

end Reinmann.StirlingGamma
