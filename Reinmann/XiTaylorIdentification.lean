/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.AnalyticPFLimit
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

/-!
# Actual Xi Taylor coefficient identification

The entire complex Xi function and its critical-line restriction have the
same iterated derivatives after the appropriate powers of `I`. The ordinary
signed moment coefficients therefore agree with the even Taylor coefficients
of `xiCompleted (1/2+z)`. No canonical product, sector theorem or RH input is
assumed in these identities.
-/
noncomputable section
namespace Reinmann
open Complex Filter
open scoped ENNReal

def centeredXi (z : ℂ) : ℂ := xiCompleted (1 / 2 + z)

def criticalXi (z : ℂ) : ℂ := centeredXi (I * z)

theorem differentiable_centeredXi : Differentiable ℂ centeredXi :=
  differentiable_xiCompleted.comp ((differentiable_const _).add differentiable_id)

theorem differentiable_criticalXi : Differentiable ℂ criticalXi :=
  differentiable_centeredXi.comp (differentiable_id.const_mul I)

theorem criticalXi_real (x : ℝ) : criticalXi (x : ℂ) = (Xi x : ℂ) := by
  simpa only [criticalXi, centeredXi, mul_comm I] using! xiCompleted_critical_eq_ofReal_Xi x

/-- Restriction to the real axis commutes with the derivative for an entire
function taking real values there. Both real and complex derivatives exist. -/
theorem complex_deriv_eq_real_deriv {f : ℂ → ℂ} {g : ℝ → ℝ}
    (hf : Differentiable ℂ f) (hr : ∀ x : ℝ, f x = (g x : ℂ)) (x : ℝ) :
    deriv f (x : ℂ) = ((deriv g x : ℝ) : ℂ) := by
  have hc := (hf x).hasDerivAt.comp_ofReal
  have hR := (hf x).hasDerivAt.real_of_complex
  have hfun : (fun y : ℝ => (f y).re) = g := by
    funext y
    rw [hr y]
    rfl
  rw [hfun] at hR
  have hcast := hR.ofReal_comp
  have he : (fun y : ℝ => f y) = fun y : ℝ => (g y : ℂ) := funext hr
  rw [he] at hc
  simpa only [hR.deriv] using! hc.unique hcast

theorem complex_iteratedDeriv_eq_real_iteratedDeriv {f : ℂ → ℂ} {g : ℝ → ℝ}
    (hf : Differentiable ℂ f) (hr : ∀ x : ℝ, f x = (g x : ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n f (x : ℂ) = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simpa using! hr x
  | succ n ih =>
    have hn : Differentiable ℂ (iteratedDeriv n f) :=
      (hf.contDiff : ContDiff ℂ (n + 1) f).differentiable_iteratedDeriv' n
    simpa only [iteratedDeriv_succ] using! complex_deriv_eq_real_deriv hn ih x

theorem criticalXi_iteratedDeriv (n : ℕ) (z : ℂ) :
    iteratedDeriv n criticalXi z = I ^ n * iteratedDeriv n centeredXi (I * z) := by
  exact congrFun (iteratedDeriv_comp_const_mul
    (differentiable_centeredXi.contDiff : ContDiff ℂ n centeredXi) I) z

theorem centeredXi_even_deriv (n : ℕ) :
    iteratedDeriv (2 * n) centeredXi 0 =
      ((-1 : ℝ) ^ n * iteratedDeriv (2 * n) Xi 0 : ℝ) := by
  have h := complex_iteratedDeriv_eq_real_iteratedDeriv
    differentiable_criticalXi criticalXi_real (2 * n) 0
  rw [criticalXi_iteratedDeriv] at h
  simp only [ofReal_zero, mul_zero, pow_mul, I_sq] at h
  have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨n, by omega⟩
  push_cast
  calc
    _ = ((-1 : ℂ) ^ n) * (((-1 : ℂ) ^ n) * iteratedDeriv (2 * n) centeredXi 0) := by
      rw [← mul_assoc, ← pow_two, hs, one_mul]
    _ = _ := by rw [h]

/-- This identifies the actual ordinary folded coefficients, including their
sign and factorial, with the entire Xi Taylor coefficients at even degrees. -/
theorem xiMomentCoeff_eq_centeredXi_taylor (n : ℕ) :
    (XiMomentCoeff n : ℂ) =
      iteratedDeriv (2 * n) centeredXi 0 / ((2 * n).factorial : ℂ) := by
  rw [centeredXi_even_deriv]
  simp only [XiMomentCoeff, XiCoeff, iteratedDeriv_eq_iterate,
    ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one, ofReal_div, ofReal_natCast]
  ring

theorem centeredXi_even (z : ℂ) : centeredXi (-z) = centeredXi z := by
  unfold centeredXi
  rw [show (1 / 2 : ℂ) + -z = 1 - (1 / 2 + z) by ring]
  unfold xiCompleted
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem centeredXi_odd_deriv (n : ℕ) : iteratedDeriv (2 * n + 1) centeredXi 0 = 0 := by
  have he : (fun z => centeredXi (-z)) = centeredXi := funext centeredXi_even
  have h := iteratedDeriv_comp_neg (2 * n + 1) centeredXi 0
  rw [he] at h
  have hp : (-1 : ℂ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, by omega⟩
  simp only [neg_zero, hp, smul_eq_mul, neg_one_mul] at h
  have hz : (2 : ℂ) * iteratedDeriv (2 * n + 1) centeredXi 0 = 0 := by
    rw [two_mul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Global convergence of the actual even Xi series, with its ordinary
coefficient sequence identified rather than postulated. -/
theorem hasSum_centeredXi_even (z : ℂ) :
    HasSum (fun n => (XiMomentCoeff n : ℂ) * z ^ (2 * n)) (centeredXi z) := by
  let a (n : ℕ) : ℂ := iteratedDeriv n centeredXi 0 / (n.factorial : ℂ) * z ^ n
  have ht : HasSum a (centeredXi z) := by
    convert hasSum_taylorSeries_of_entire differentiable_centeredXi 0 z using 1
    all_goals try rfl
    funext n
    simp only [a, sub_zero, smul_eq_mul, div_eq_mul_inv]
    ring
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro i j h
    change 2 * i = 2 * j at h
    omega
  have hs := ht.summable.comp_injective hi
  have ho : HasSum (fun n => a (2 * n + 1)) 0 := by
    simpa only [a, centeredXi_odd_deriv, zero_div, zero_mul] using!
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have hall := hs.hasSum.even_add_odd ho
  have heq := ht.unique hall
  simp only [add_zero] at heq
  have heven : HasSum (fun n => a (2 * n)) (centeredXi z) := by
    rw [heq]
    exact hs.hasSum
  simpa only [a, ← xiMomentCoeff_eq_centeredXi_taylor] using! heven

def foldedXiSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (XiMomentCoeff n : ℂ))

def foldedXi (z : ℂ) : ℂ := foldedXiSeries.sum z

theorem foldedXi_eq_tsum (z : ℂ) :
    foldedXi z = ∑' n, (XiMomentCoeff n : ℂ) * z ^ n := by
  simpa only [FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using!
    (FormalMultilinearSeries.ofScalars_sum_eq (E := ℂ)
      (fun n => (XiMomentCoeff n : ℂ)) z)

theorem foldedXi_sq (z : ℂ) : foldedXi (z ^ 2) = centeredXi z := by
  rw [foldedXi_eq_tsum]
  simpa only [pow_mul] using! (hasSum_centeredXi_even z).tsum_eq

theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

/-- The entire folded function agrees with the square-root formula everywhere,
including zero and the branch cut. Entirety is proved from its series below. -/
theorem foldedXi_eq_sqrt (z : ℂ) : foldedXi z = xiCompleted (1 / 2 + Complex.sqrt z) := by
  have h := foldedXi_sq (Complex.sqrt z)
  simpa only [complex_sqrt_sq, centeredXi] using! h

theorem hasSum_foldedXi (z : ℂ) :
    HasSum (fun n => (XiMomentCoeff n : ℂ) * z ^ n) (foldedXi z) := by
  have h := hasSum_centeredXi_even (Complex.sqrt z)
  have hp (n : ℕ) : Complex.sqrt z ^ (2 * n) = z ^ n := by
    rw [pow_mul, complex_sqrt_sq]
  simpa only [hp, centeredXi, ← foldedXi_eq_sqrt] using! h

theorem foldedXiSeries_radius : foldedXiSeries.radius = ∞ := by
  apply foldedXiSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := (hasSum_foldedXi (r : ℂ)).summable.norm
  simpa only [foldedXiSeries, FormalMultilinearSeries.ofScalars_norm,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg r.coe_nonneg] using! hs

theorem foldedXi_hasFPowerSeries : HasFPowerSeriesOnBall foldedXi foldedXiSeries 0 ∞ := by
  have h := foldedXiSeries.hasFPowerSeriesOnBall
    (by rw [foldedXiSeries_radius]; exact ENNReal.zero_lt_top)
  simpa only [foldedXi, foldedXiSeries_radius] using! h

theorem differentiable_foldedXi : Differentiable ℂ foldedXi := by
  intro z
  have h := foldedXi_hasFPowerSeries.analyticAt_of_mem
    (show z ∈ Metric.eball (0 : ℂ) ∞ by simp)
  exact h.differentiableAt

/-- The exact Taylor identification needed by `AnalyticPFLimit`: no
factorial, sign, degree restriction or Xi-analytic premise is left implicit. -/
theorem foldedXi_taylor (n : ℕ) :
    iteratedDeriv n foldedXi 0 / (n.factorial : ℂ) = (XiMomentCoeff n : ℂ) := by
  have hp := foldedXi_hasFPowerSeries.hasFPowerSeriesAt
  have he := hp.eq_formalMultilinearSeries hp.analyticAt.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [foldedXiSeries, FormalMultilinearSeries.coeff_ofScalars] using! hc.symm

theorem foldedXi_neg_square (t : ℝ) : foldedXi (-(t : ℂ) ^ 2) = (Xi t : ℂ) := by
  have h := foldedXi_sq (I * (t : ℂ))
  have hs : (I * (t : ℂ)) ^ 2 = -(t : ℂ) ^ 2 := by
    rw [mul_pow, I_sq]
    ring
  rw [hs] at h
  exact h.trans (criticalXi_real t)

theorem foldedXi_neg_square_zero_iff (t : ℝ) :
    foldedXi (-(t : ℂ) ^ 2) = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  rw [foldedXi_neg_square, ofReal_eq_zero]
  exact Xi_eq_zero_iff_riemannZeta t

theorem foldedXi_conj (z : ℂ) : foldedXi (star z) = star (foldedXi z) := by
  simp only [foldedXi_eq_tsum]
  rw [RCLike.star_def, conj_tsum]
  apply tsum_congr
  intro n
  simp

/-- Instantiation of the analytic PF-limit bridge for the actual folded Xi.
Polynomial PF positivity and construction of the converging approximants are
still explicit inputs; Taylor identification is now an unconditional theorem. -/
theorem finitePF_xi_of_folded_locallyUniformLimit
    {ι : Type*} {φ : Filter ι} [NeBot φ] {p : ι → Polynomial ℝ} {r : ℕ}
    (h : TendstoLocallyUniformlyOn
      (fun j z => ((p j).map (algebraMap ℝ ℂ)).eval z) foldedXi φ Set.univ)
    (hp : ∀ᶠ j in φ, FinitePF (fun n => (p j).coeff n) r) :
    FinitePF XiMomentCoeff r :=
  finitePF_of_real_polynomial_locallyUniformLimit h hp foldedXi_taylor

end Reinmann
