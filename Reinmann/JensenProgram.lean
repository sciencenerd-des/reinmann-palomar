/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.CompletedZetaConj
public import Reinmann.CriticalLineRealSlice
public import Reinmann.RiemannSpine
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Foundation for the Laguerre–Pólya / Jensen Program (Structure A)

**Correctness note (2026-06-06).** An earlier version of this file built `Ξ` on the
*entire completed zeta* `Λ₀ = completedRiemannZeta₀`.  That was a mathematical
error: `Λ₀ = Λ + 1/s + 1/(1-s)`, so the zeros of `Λ₀` are **not** the Riemann
zeros (at a nontrivial zero `ρ`, `Λ₀(ρ) = 1/ρ + 1/(1-ρ) ≠ 0`).  A Laguerre–Pólya /
Jensen program on `Λ₀` would target the wrong object.

This file now uses **Riemann's `ξ`**, the entire function that removes the poles of
`Λ` by *multiplying* by `s(s-1)/2` (which preserves the zeros), not by adding pole
terms:

  `ξ(s) := (s(s-1)/2) · Λ(s)`,   `Λ = completedRiemannZeta`,
  `Ξ(t) := Re ξ(1/2 + i t) = -((t² + 1/4)/2) · Zslice t`.

Because `Λ(1/2+it)` is real (`completedRiemannZeta_real_on_critical_line`) and the
prefactor `s(s-1)/2 = -(t²+1/4)/2` is a nonzero real scalar, `Ξ` is a genuine
**real, even** function whose **zeros are exactly the critical-line zeros of `ζ`**:

* `xiCompleted_critical_eq_ofReal_Xi`: `ξ(1/2+it) = (Ξ t : ℂ)`.
* `Xi_even`: `Ξ(-t) = Ξ(t)` (functional equation `ξ(1-s) = ξ(s)`).
* `Xi_eq_zero_iff_riemannZeta`: `Ξ t = 0 ↔ ζ(1/2+it) = 0` — the property `Λ₀`
  lacked, and the reason this is the correct target for RH.

`ξ` agrees with the usual product away from 0 and 1 and takes value 1/2
at both poles. The legacy `JensenPoly` lacks the factorial normalization of
the classical criterion; `ClassicalJensenPoly` supplies that normalization.
The full Pólya–Jensen theorem and the CNV Turán
inequalities are recorded as **named external classical inputs**, not axioms and
not proved here.
-/

noncomputable section

open Complex
open Polynomial
open scoped Polynomial

namespace Reinmann

/-- The entire extension of Riemann's ξ, including its values at the two
poles of Λ. Using Λ₀ here is algebraic pole removal, not substitution of Λ₀
for Λ in the definition of the zero set. -/
def xiCompleted (s : ℂ) : ℂ :=
  1 / 2 + s * (s - 1) / 2 * completedRiemannZeta₀ s

@[simp] theorem xiCompleted_zero : xiCompleted 0 = 1 / 2 := by
  simp [xiCompleted]

@[simp] theorem xiCompleted_one : xiCompleted 1 = 1 / 2 := by
  simp [xiCompleted]

/-- ξ is entire; the definition does not multiply pointwise pole values by zero. -/
theorem differentiable_xiCompleted : Differentiable ℂ xiCompleted := by
  unfold xiCompleted
  exact (differentiable_const (1 / 2 : ℂ)).add
    (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
      differentiable_completedZeta₀)

/-- Away from the poles, the entire extension agrees with the usual product. -/
theorem xiCompleted_eq_product {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xiCompleted s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold xiCompleted
  have hsub : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- The real critical-line slice of Riemann's `ξ`:
`Ξ(t) = Re ξ(1/2+it) = -((t²+1/4)/2)·Zslice t`. -/
def Xi (t : ℝ) : ℝ := -((t ^ 2 + 1 / 4) / 2) * Zslice t

/-- On the critical line, Riemann's `ξ` is the real cast of `Ξ`. -/
theorem xiCompleted_critical_eq_ofReal_Xi (t : ℝ) :
    xiCompleted (1 / 2 + (t : ℂ) * I) = (Xi t : ℂ) := by
  have hpre : (1 / 2 + (t : ℂ) * I) * ((1 / 2 + (t : ℂ) * I) - 1)
      = -((t : ℂ) ^ 2 + 1 / 4) := by
    have h : (1 / 2 + (t : ℂ) * I) * ((1 / 2 + (t : ℂ) * I) - 1)
        = (t : ℂ) ^ 2 * I ^ 2 - 1 / 4 := by ring
    rw [h, Complex.I_sq]; ring
  rw [xiCompleted_eq_product (linePoint_ne_zero t) (by
    intro h
    have hr := congrArg Complex.re h
    simp at hr)]
  unfold Xi
  rw [completedRiemannZeta_critical_eq_ofReal, hpre]
  push_cast
  ring

/-- `Ξ` is **even**: `Ξ(-t) = Ξ(t)`, from the functional equation `ξ(1-s) = ξ(s)`
(on the line, `1 - (1/2 + it) = 1/2 - it`). -/
theorem Xi_even (t : ℝ) : Xi (-t) = Xi t := by
  have hz : Zslice (-t) = Zslice t := by
    unfold Zslice
    rw [show (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) by push_cast; ring,
        completedRiemannZeta_one_sub]
  unfold Xi
  rw [hz]; ring

/-- **The zeros of `Ξ` are exactly the critical-line zeros of `ζ`.** This is the
property the old `Λ₀` slice lacked, and is what makes `Ξ` the correct target for
the Laguerre–Pólya / Jensen route to RH. -/
theorem Xi_eq_zero_iff_riemannZeta (t : ℝ) :
    Xi t = 0 ↔ riemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
  unfold Xi
  rw [mul_eq_zero]
  constructor
  · rintro (hc | hz)
    · exfalso
      have hpos : (0 : ℝ) < (t ^ 2 + 1 / 4) / 2 := by positivity
      linarith [hc]
    · exact riemannZeta_critical_zero_of_Zslice_zero hz
  · intro hζ
    right
    have hg : Gammaℝ (1 / 2 + (t : ℂ) * I) ≠ 0 :=
      Gammaℝ_ne_zero_of_re_pos (by rw [linePoint_re]; norm_num)
    have hdef := riemannZeta_def_of_ne_zero (linePoint_ne_zero t)
    rw [hζ] at hdef
    have hΛ : completedRiemannZeta (1 / 2 + (t : ℂ) * I) = 0 := by
      rcases div_eq_zero_iff.mp hdef.symm with h | h
      · exact h
      · exact absurd h hg
    exact (Zslice_eq_zero_iff t).mpr hΛ

/-! ## Jensen polynomial setup -/

/-- The real even Taylor coefficient sequence for `Ξ`, normalized so that
`Ξ(t) = Σ' n, XiCoeff n * t^(2n)` when the Taylor expansion is available.

The definition is deliberately derivative-based.  It is a concrete real sequence
now, while the analytic theorem identifying it with the entire Taylor expansion
is left to the Laguerre--Pólya/Jensen program. -/
def XiCoeff (n : ℕ) : ℝ :=
  deriv^[2 * n] Xi 0 / ((Nat.factorial (2 * n) : ℕ) : ℝ)

/-- Legacy Borel-coefficient diagnostic, NOT the classical Jensen polynomial
of the folded Xi function. Kept for existing Turán diagnostics:

`J_{d,n}(X) = Σ_{k=0}^d binom(d,k) b_{n+k} X^k`. -/
def JensenPoly (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    Polynomial.C ((Nat.choose d k : ℝ) * XiCoeff (n + k)) * Polynomial.X ^ k

/-- A concrete real-rootedness predicate for real polynomials: every complex
root has zero imaginary part.  This avoids depending on a specialized
hyperbolicity API while expressing exactly what the Jensen criterion needs. -/
def PolynomialHyperbolic (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, Polynomial.eval z (p.map (algebraMap ℝ ℂ)) = 0 → z.im = 0

/-- All legacy Borel-coefficient diagnostic polynomials are hyperbolic. -/
def AllJensenHyperbolic : Prop :=
  ∀ d n : ℕ, PolynomialHyperbolic (JensenPoly d n)

/-- Legacy unproved RH equivalence for the Borel-coefficient diagnostics.
This is NOT the classical Pólya--Jensen theorem: the factorial normalization
is missing. Existing conditional reductions requiring this input therefore
remain conditional on an additional, unestablished statement. -/
def DiagnosticJensenRHBridge : Prop :=
  RiemannHypothesis ↔ AllJensenHyperbolic

/-- Compatibility theorem for the legacy diagnostic bridge only. -/
theorem riemannHypothesis_iff_allJensenHyperbolic_of_polyaJensen
    (h : DiagnosticJensenRHBridge) : RiemannHypothesis ↔ AllJensenHyperbolic := h

/-- Exponential-series coefficients of the folded Xi function:
`F(z) = Σ (-1)^n XiCoeff n z^n = Σ XiJensenCoeff n z^n/n!`.
The Taylor-series identity and the classical analytic bridge remain external. -/
def XiJensenCoeff (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * (-1 : ℝ) ^ n * XiCoeff n

/-- Correctly factorial-normalized classical Jensen polynomial of folded Xi. -/
def ClassicalJensenPoly (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C ((Nat.choose d k : ℝ) * XiJensenCoeff (n + k)) * X ^ k

def AllClassicalJensenHyperbolic : Prop :=
  ∀ d n : ℕ, PolynomialHyperbolic (ClassicalJensenPoly d n)

/-- Correct classical Pólya--Jensen interface; still an unproved named input,
not an axiom and not interchangeable with `DiagnosticJensenRHBridge`. -/
def PolyaJensenBridge : Prop :=
  RiemannHypothesis ↔ AllClassicalJensenHyperbolic

theorem riemannHypothesis_iff_classicalJensen_of_polyaJensen
    (h : PolyaJensenBridge) : RiemannHypothesis ↔ AllClassicalJensenHyperbolic := h

/-! ## The `d = 2` Turán fragment -/

/-- The `d = 2` Jensen polynomial has discriminant
`4 * (b_{n+1}^2 - b_n*b_{n+2})`. -/
def JensenQuadraticDiscriminant (n : ℕ) : ℝ :=
  ((2 : ℝ) * XiCoeff (n + 1)) ^ 2 - (4 : ℝ) * XiCoeff n * XiCoeff (n + 2)

/-- The Turán inequality for consecutive `Ξ` coefficients. -/
def XiTuran2 (n : ℕ) : Prop :=
  XiCoeff n * XiCoeff (n + 2) ≤ XiCoeff (n + 1) ^ 2

/-- Nonnegative quadratic Jensen discriminant is exactly the `d = 2` Turán
inequality.  This is the first coefficient-level Jensen fragment; importing the
analytic theorem that `XiTuran2 n` holds for all `n` is the next external
mathematical input. -/
theorem jensenQuadraticDiscriminant_nonneg_iff_turan2 (n : ℕ) :
    0 ≤ JensenQuadraticDiscriminant n ↔ XiTuran2 n := by
  unfold JensenQuadraticDiscriminant XiTuran2
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- A named target for the known Csordas--Norfolk--Varga Turán ladder fragment. -/
def XiTuran2All : Prop :=
  ∀ n : ℕ, XiTuran2 n

/-- If the Turán inequalities are supplied, every quadratic Jensen discriminant
is nonnegative.  This does not prove RH, but it verifies the `d = 2` rung of the
Jensen hyperbolicity program. -/
theorem jensenQuadraticDiscriminants_nonneg_of_turan2All
    (h : XiTuran2All) (n : ℕ) : 0 ≤ JensenQuadraticDiscriminant n :=
  (jensenQuadraticDiscriminant_nonneg_iff_turan2 n).2 (h n)

end Reinmann
