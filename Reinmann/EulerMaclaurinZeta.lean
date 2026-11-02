/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinFinite
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-! Identifying Euler--Maclaurin with the actual zeta function in its
Dirichlet-series half-plane. Analytic continuation is a separate step. -/
noncomputable section
namespace Reinmann.EulerMaclaurinZeta
open Polynomial MeasureTheory Set Finset Filter EulerMaclaurinFinite
open scoped Topology Interval

theorem cpow_tendsto_zero {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ)^a) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun x : ℝ => x^a.re) atTop (𝓝 0) := by
    simpa only [neg_neg] using! tendsto_rpow_neg_atTop (by linarith : 0 < -a.re)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (Complex.norm_cpow_eq_rpow_re_of_pos hx a).symm

theorem power_tendsto_zero {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    Tendsto (power s k) atTop (𝓝 0) := by
  have h := cpow_tendsto_zero (a := -s-(k : ℂ))
    (by simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re];
        linarith [Nat.cast_nonneg (α := ℝ) k])
  simpa only [mul_zero] using! h.const_mul ((ascPochhammer ℂ k).eval s)

theorem correction_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (correction s) atTop (𝓝 0) := by
  have h : Tendsto (correction s) atTop (𝓝 (∑ k ∈ range 11, (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro k _
    simpa only [mul_zero] using! (power_tendsto_zero hs (k+1)).const_mul
      (BernoulliQuadrature.kernel (k+2) 0)
  simpa using! h

/-- Ordinary negative powers are the actual convergent zeta series here. -/
theorem hasSum_power {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => power s 0 (n+1)) (riemannZeta s) := by
  have h := (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  rw [← zeta_eq_tsum_one_div_nat_cpow hs] at h
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simpa [power, Complex.cpow_neg,
    Complex.zero_cpow (Complex.ne_zero_of_one_lt_re hs)] using! h'


/-- The first N-1 terms; no summability convention enters this finite sum. -/
def initialSum (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ range (N-1), power s 0 (n+1)

def finiteModel (s : ℂ) (N : ℕ) : ℂ :=
  initialSum s N + (N : ℂ)^(1-s)/(s-1) + power s 0 N/2 + correction s N

theorem integral_power {s : ℂ} (hs : 1 < s.re) {N : ℝ} (hN : 0 < N) :
    (∫ t in Ioi N, power s 0 t) = (N : ℂ)^(1-s)/(s-1) := by
  have ha : (-s).re < -1 := by simp only [Complex.neg_re]; linarith
  simp only [power_zero]
  rw [integral_Ioi_cpow_of_lt ha hN]
  rw [show -s+1 = 1-s by ring, show 1-s = -(s-1) by ring, div_neg]
  ring


/-- The actual zeta minus its finite model equals the bounded periodic integral
in the Dirichlet-series half-plane. No EM identity is a hypothesis. -/
theorem zeta_eq_model_add_remainder {s : ℂ} (hs : 1 < s.re) (N : ℕ) (hN : 0 < N) :
    riemannZeta s = finiteModel s N + EulerMaclaurinTail.remainder s N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs0 : 0 < s.re := by linarith
  have hs12 : -11 < s.re := by linarith
  have hT : Tendsto (fun M : ℕ => ((N+M : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.add_comm N] using!
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat N)
  have hsum := (hasSum_nat_add_iff' (N-1)).mpr (hasSum_power hs)
  have hseries : Tendsto (fun M : ℕ => ∑ j ∈ range M, power s 0 ((N+j : ℕ) : ℝ))
      atTop (𝓝 (riemannZeta s - initialSum s N)) := by
    convert hsum.tendsto_sum_nat using 1
    funext M
    apply sum_congr rfl
    intro j _
    congr 1
    exact_mod_cast (show N+j = j+(N-1)+1 by omega)
    rfl
  have hI : IntegrableOn (power s 0) (Ioi (N : ℝ)) := by
    rw [show power s 0 = (fun x : ℝ => (x : ℂ)^(-s)) from funext (power_zero s)]
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith : (-s).re < -1) hNr
  have hi := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hI hT
  have hp := (power_tendsto_zero hs0 0).comp hT
  have hc := (correction_tendsto_zero hs0).comp hT
  have hr := intervalIntegral_tendsto_integral_Ioi (N : ℝ)
    (EulerMaclaurinTail.integrand_integrable hs12 hNr) hT
  have hlimit := (((hi.add ((hp.const_sub (power s 0 N)).div_const (2 : ℂ))).add_const
    (correction s N)).sub hc).sub
      (hr.const_mul ((ascPochhammer ℂ 12).eval s / ((12 : ℕ).factorial : ℂ)))
  have hfinite := fun M => finite_sum s N M hN hs12
  have hRHS := hlimit.congr (f₂ := fun M : ℕ =>
    ∑ j ∈ range M, power s 0 ((N+j : ℕ) : ℝ)) (fun M => by
      dsimp only [Function.comp_apply]
      simpa only [Nat.cast_add] using! (hfinite M).symm)
  have heq := tendsto_nhds_unique hseries hRHS
  simp only [sub_zero] at heq
  rw [integral_power hs hNr] at heq
  dsimp [finiteModel, EulerMaclaurinTail.remainder]
  linear_combination heq

/-- Certified EM error for the actual zeta function, presently for Re s > 1. -/
theorem zeta_error_le {s : ℂ} (hs : 1 < s.re) (N : ℕ) (hN : 0 < N) :
    ‖riemannZeta s - finiteModel s N‖ ≤
      ‖(ascPochhammer ℂ 12).eval s‖ / ((12 : ℕ).factorial : ℝ) *
        ((6112/15015 : ℝ)*(N : ℝ)^(-s.re-11)/(s.re+11)) := by
  rw [zeta_eq_model_add_remainder hs N hN, add_sub_cancel_left]
  exact EulerMaclaurinTail.remainder_norm_le (by linarith) (by exact_mod_cast hN)

end Reinmann.EulerMaclaurinZeta
