/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.EulerMaclaurinFinite
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section

/-! Unit-cell Bernoulli quadrature for the complex logarithm `t ↦ Log (w + t)`.

The derivative chain is the actual one: `Log (w+t)`, then
`(-1)^k k! (w+t)^(-(k+1))`. Nothing about Gamma is assumed here. -/
noncomputable section
namespace Reinmann.StirlingCell
open MeasureTheory Set Finset
open scoped Interval

/-- The actual `t`-derivatives of `Log (w + t)`. -/
def logChain (w : ℂ) : ℕ → ℝ → ℂ
  | 0, t => Complex.log (w + t)
  | k+1, t => (-1 : ℂ)^k * (k.factorial : ℂ) * (w + t)^(-((k : ℤ)+1))

theorem add_ne_zero_of_re_pos {w : ℂ} {t : ℝ} (h : 0 < (w + t).re) : w + t ≠ 0 := by
  intro h0
  rw [h0, Complex.zero_re] at h
  exact lt_irrefl 0 h

theorem logChain_hasDerivAt (w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < (w + t).re) :
    HasDerivAt (logChain w k) (logChain w (k+1) t) t := by
  have hne : w + (t : ℂ) ≠ 0 := add_ne_zero_of_re_pos ht
  have hlin : HasDerivAt (fun z : ℂ => w + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add w
  cases k with
  | zero =>
    have hslit : w + (t : ℂ) ∈ Complex.slitPlane := Or.inl ht
    have h := ((Complex.hasDerivAt_log hslit).comp (t : ℂ) hlin).comp_ofReal
    convert h using 1
    · funext y; rfl
    · simp [logChain]
  | succ k =>
    have hz := ((hasDerivAt_zpow (-((k : ℤ)+1)) (w + (t : ℂ)) (Or.inl hne)).comp
      (t : ℂ) hlin).comp_ofReal
    have he : (-((k : ℤ)+1) - 1) = -(((k+1 : ℕ) : ℤ)+1) := by push_cast; ring
    rw [he] at hz
    have h := hz.const_mul ((-1 : ℂ)^k * (k.factorial : ℂ))
    have hf : logChain w (k+1) = fun y : ℝ =>
        (-1 : ℂ)^k * (k.factorial : ℂ) *
          ((fun x : ℂ => x^(-((k : ℤ)+1))) ∘ (fun z => w + z)) y := by
      funext y
      simp [logChain]
    rw [hf]
    convert h using 1
    have hc : ((-((k : ℤ)+1) : ℤ) : ℂ) = -((k : ℂ)+1) := by push_cast; ring
    rw [hc]
    simp only [logChain, Nat.factorial_succ, Nat.cast_mul, mul_one, pow_succ]
    push_cast
    ring

/-- Exact order-`m` quadrature for `Log (w + x + u)` on the unit cell. -/
theorem log_cell (w : ℂ) {x : ℝ} (hw : 0 < w.re) (hx : 0 ≤ x) (m : ℕ) :
    (∫ u in (0 : ℝ)..1, logChain w 0 (x+u)) =
      (∑ k ∈ range m, (-1 : ℂ)^k *
        (BernoulliQuadrature.kernel (k+1) 1 * logChain w k (x+1) -
          BernoulliQuadrature.kernel (k+1) 0 * logChain w k x)) +
      (-1 : ℂ)^m * (∫ u in (0 : ℝ)..1,
        BernoulliQuadrature.kernel m u * logChain w m (x+u)) := by
  have hF : ∀ k u, u ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun v => logChain w k (x+v)) (logChain w (k+1) (x+u)) u := by
    intro k u hu
    have hu0 : 0 ≤ u := (Set.mem_uIcc.mp hu).elim (fun h => h.1) (fun h => by linarith [h.1, h.2])
    have hre : 0 < (w + ((x+u : ℝ) : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    exact HasDerivAt.comp_const_add x u (logChain_hasDerivAt w k hre)
  have h := BernoulliQuadrature.finite_quadrature (fun k v => logChain w k (x+v)) hF m
  simpa only [add_zero] using! h

end Reinmann.StirlingCell
