/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.FinitePFBaseline
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# Analytic limit bridge for finite Pólya frequency

Canonical partial products have unbounded degree. Locally uniform holomorphic
convergence nevertheless implies convergence of every fixed Taylor coefficient.
Finite-order PF is closed under coefficientwise limits. These are genuine limit
theorems, not analytic Xi assertions or a bounded-degree interpolation shortcut.
-/
noncomputable section
namespace Reinmann
open Filter Polynomial

/-- All fixed polynomial derivative orders converge locally uniformly, with
no degree bound on the polynomial family. -/
theorem polynomial_derivatives_locallyUniformLimit
    {ι : Type*} {φ : Filter ι} {p : ι → Polynomial ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn (fun j z => (p j).eval z) f φ Set.univ) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun j z => (derivative^[n] (p j)).eval z)
      (iteratedDeriv n f) φ Set.univ := by
  induction n with
  | zero => simpa using! h
  | succ n ih =>
    have hd := ih.deriv (Eventually.of_forall fun j =>
      (derivative^[n] (p j)).differentiableOn) isOpen_univ
    have hderiv (q : Polynomial ℂ) : deriv (fun z => q.eval z) = fun z => q.derivative.eval z :=
      funext fun z => q.deriv
    simpa only [iteratedDeriv_succ, Function.comp_def,
      Function.iterate_succ_apply', hderiv] using! hd

/-- Cauchy coefficient convergence for a locally uniform entire limit,
including polynomial sequences of unbounded degree. -/
theorem polynomial_coeff_tendsto_of_locallyUniformLimit
    {ι : Type*} {φ : Filter ι} {p : ι → Polynomial ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn (fun j z => (p j).eval z) f φ Set.univ) (n : ℕ) :
    Tendsto (fun j => (p j).coeff n) φ
      (nhds (iteratedDeriv n f 0 / (n.factorial : ℂ))) := by
  have hd := (polynomial_derivatives_locallyUniformLimit h n).tendsto_at (Set.mem_univ 0)
  change Tendsto (fun j => (derivative^[n] (p j)).eval 0) φ (nhds (iteratedDeriv n f 0)) at hd
  simp only [← Polynomial.coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, nsmul_eq_mul] at hd
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simpa only [mul_div_cancel_left₀ _ hf] using! hd.div_const (n.factorial : ℂ)

/-- Nonnegativity of all fixed ordered minors survives a coefficientwise limit. -/
theorem finitePF_of_coefficientwise_limit {ι : Type*} {φ : Filter ι} [NeBot φ]
    {a : ι → ℕ → ℝ} {b : ℕ → ℝ} {r : ℕ}
    (ha : ∀ᶠ j in φ, FinitePF (a j) r)
    (hab : ∀ n, Tendsto (fun j => a j n) φ (nhds (b n))) : FinitePF b r := by
  intro k hk rows cols hr hc
  have hm : Tendsto (fun j => (Matrix.of fun i l : Fin k =>
      sequenceToeplitz (a j) (rows i) (cols l))) φ
      (nhds (Matrix.of fun i l : Fin k => sequenceToeplitz b (rows i) (cols l))) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro l
    simp only [Matrix.of_apply, sequenceToeplitz]
    split_ifs
    · exact hab _
    · exact tendsto_const_nhds
  have hd := (continuous_id.matrix_det.tendsto _).comp hm
  exact ge_of_tendsto hd (ha.mono fun j hj => hj k hk rows cols hr hc)

/-- The analytic PF-limit bridge for real canonical partial-product candidates.
Only the sector positivity of those polynomials and the Taylor identification
with the target sequence remain as inputs. Their degrees may grow without bound. -/
theorem finitePF_of_real_polynomial_locallyUniformLimit
    {ι : Type*} {φ : Filter ι} [NeBot φ]
    {p : ι → Polynomial ℝ} {f : ℂ → ℂ} {b : ℕ → ℝ} {r : ℕ}
    (h : TendstoLocallyUniformlyOn
      (fun j z => ((p j).map (algebraMap ℝ ℂ)).eval z) f φ Set.univ)
    (hp : ∀ᶠ j in φ, FinitePF (fun n => (p j).coeff n) r)
    (hb : ∀ n, iteratedDeriv n f 0 / (n.factorial : ℂ) = (b n : ℂ)) : FinitePF b r := by
  apply finitePF_of_coefficientwise_limit hp
  intro n
  have hc := polynomial_coeff_tendsto_of_locallyUniformLimit h n
  rw [hb n] at hc
  have hr := (Complex.continuous_re.tendsto _).comp hc
  simpa only [Function.comp_def, Polynomial.coeff_map, Complex.coe_algebraMap,
    Complex.ofReal_re] using! hr

end Reinmann
