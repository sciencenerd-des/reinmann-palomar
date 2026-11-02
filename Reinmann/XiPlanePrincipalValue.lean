/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.JensenProgram
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

@[expose] public section

/-!
# Principal Values in the Ξ-Plane

The `s = σ + iγ` finite geometry runs into a height-balance obstruction: ordinary
zeta zero symmetry is centered at height `0`, not around every target height
`γ`.  The better coordinate is the critical-line variable `t` for the even real
function

`Ξ(t) = Re ξ(1/2 + i t)`.

In the `t`-plane, the functional equation gives the natural symmetry
`t ↦ -t`.  This file proves the finite algebraic core for that route: a product
over paired roots `±τ` has a derivative zero at the origin, and such finite
critical points transfer through derivative convergence to the limiting `Ξ`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace Reinmann

/-! ## Finite even products -/

/-- The even quadratic factor with roots `±τ`. -/
def xiEvenPairFactor (τ t : ℝ) : ℝ :=
  (t - τ) * (t + τ)

/-- Each paired factor is even in the `Ξ`-coordinate. -/
theorem xiEvenPairFactor_even (τ t : ℝ) :
    xiEvenPairFactor τ (-t) = xiEvenPairFactor τ t := by
  unfold xiEvenPairFactor
  ring

/-- Any paired factor has derivative zero at the origin. -/
theorem deriv_xiEvenPairFactor_zero (τ : ℝ) :
    deriv (xiEvenPairFactor τ) 0 = 0 := by
  have hderiv : HasDerivAt (xiEvenPairFactor τ)
      ((0 + τ) + (0 - τ)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t - τ) 1 0 := (hasDerivAt_id (0 : ℝ)).sub_const τ
    have h2 : HasDerivAt (fun t : ℝ => t + τ) 1 0 := (hasDerivAt_id (0 : ℝ)).add_const τ
    have h3 := h1.mul h2
    convert h3 using 1
    · funext t; simp [xiEvenPairFactor]
    · ring
  rw [hderiv.deriv]
  ring

/-- A finite even zero product in the `Ξ`-plane. -/
def xiEvenProduct (T : Finset ℝ) (t : ℝ) : ℝ :=
  ∏ τ ∈ T, xiEvenPairFactor τ t

/-- A scaled finite even zero product.  The scale is essential for canonical
Hadamard approximants: `Ξ` is not expected to be the limit of monic products
with no normalization factor. -/
def xiEvenScaledProduct (a : ℝ) (T : Finset ℝ) (t : ℝ) : ℝ :=
  a * xiEvenProduct T t

/-- Finite products over paired roots are even. -/
theorem xiEvenProduct_even (T : Finset ℝ) (t : ℝ) :
    xiEvenProduct T (-t) = xiEvenProduct T t := by
  unfold xiEvenProduct
  apply Finset.prod_congr rfl
  intro τ hτ
  exact xiEvenPairFactor_even τ t

/-- Scaled finite products over paired roots are even. -/
theorem xiEvenScaledProduct_even (a : ℝ) (T : Finset ℝ) (t : ℝ) :
    xiEvenScaledProduct a T (-t) = xiEvenScaledProduct a T t := by
  unfold xiEvenScaledProduct
  rw [xiEvenProduct_even]

/-- Every finite even zero product has a derivative zero at the origin. -/
theorem deriv_xiEvenProduct_zero (T : Finset ℝ) :
    deriv (xiEvenProduct T) 0 = 0 := by
  unfold xiEvenProduct
  rw [deriv_fun_finsetProd]
  · apply Finset.sum_eq_zero
    intro τ hτ
    have hfactor : deriv (xiEvenPairFactor τ) 0 = 0 :=
      deriv_xiEvenPairFactor_zero τ
    simp [hfactor]
  · intro τ hτ
    unfold xiEvenPairFactor
    fun_prop

/-- Every scaled finite even zero product has derivative zero at the origin. -/
theorem deriv_xiEvenScaledProduct_zero (a : ℝ) (T : Finset ℝ) :
    deriv (xiEvenScaledProduct a T) 0 = 0 := by
  unfold xiEvenScaledProduct
  rw [deriv_const_mul]
  · simp [deriv_xiEvenProduct_zero]
  · unfold xiEvenProduct xiEvenPairFactor
    fun_prop

/-! ## Finite principal-value fields -/

/-- The logarithmic-derivative field contributed by a paired root `±τ`.

Away from the roots this is the logarithmic derivative of
`(t - τ) * (t + τ)`.  At a root Lean's totalized inverse assigns a value, so
the cancellation theorem below should be read as a principal-value identity. -/
def xiEvenPairField (τ t : ℝ) : ℝ :=
  (t - τ)⁻¹ + (t + τ)⁻¹

/-- The paired principal-value field cancels at the origin. -/
theorem xiEvenPairField_zero (τ : ℝ) :
    xiEvenPairField τ 0 = 0 := by
  unfold xiEvenPairField
  simp

/-- A finite principal-value log-field made from paired `Ξ`-plane roots. -/
def xiEvenPrincipalValueField (T : Finset ℝ) (t : ℝ) : ℝ :=
  ∑ τ ∈ T, xiEvenPairField τ t

/-- Finite symmetric principal-value blocks have zero total field at the
origin.  This is the `t ↦ -t` analogue of the s-plane cancellation that failed
for arbitrary height-balance around `γ`. -/
theorem xiEvenPrincipalValueField_zero (T : Finset ℝ) :
    xiEvenPrincipalValueField T 0 = 0 := by
  unfold xiEvenPrincipalValueField
  apply Finset.sum_eq_zero
  intro τ hτ
  exact xiEvenPairField_zero τ

/-! ## Transfer to Ξ -/

/-- If finite even products have derivatives converging to `Ξ'` at `0`, then
`Ξ'(0) = 0`.  This theorem is elementary; the analytic burden is constructing
canonical `Ξ`-Hadamard approximants and proving derivative convergence. -/
theorem deriv_Xi_zero_of_xiEvenProduct_deriv_tendsto
    {P : ℕ → ℝ → ℝ}
    (hlim : Tendsto (fun n : ℕ => deriv (P n) 0) atTop (𝓝 (deriv Xi 0)))
    (hcrit : ∀ n : ℕ, deriv (P n) 0 = 0) :
    deriv Xi 0 = 0 := by
  have hzero : Tendsto (fun n : ℕ => deriv (P n) 0) atTop (𝓝 (0 : ℝ)) := by
    simp [hcrit]
  exact tendsto_nhds_unique hlim hzero

/-- A concrete witness for the Ξ-plane principal-value/Hadamard route. -/
structure XiEvenHadamardWitness where
  approximants : ℕ → ℝ → ℝ
  zeroPairs : ℕ → Finset ℝ
  approximants_eq : ∀ n : ℕ, approximants n = xiEvenProduct (zeroPairs n)
  derivConverges :
    Tendsto (fun n : ℕ => deriv (approximants n) 0) atTop (𝓝 (deriv Xi 0))

/-- A Ξ-plane even Hadamard witness transfers the finite even-product critical
point to the limiting function. -/
theorem deriv_Xi_zero_of_xiEvenHadamardWitness
    (w : XiEvenHadamardWitness) : deriv Xi 0 = 0 := by
  apply deriv_Xi_zero_of_xiEvenProduct_deriv_tendsto w.derivConverges
  intro n
  rw [w.approximants_eq n]
  exact deriv_xiEvenProduct_zero (w.zeroPairs n)

/-- The next honest target for the Ξ-plane route. -/
def XiEvenHadamardTarget : Prop :=
  Nonempty XiEvenHadamardWitness

/-! ## Stronger Laguerre--Pólya target -/

/-- A finite real-rooted even-product approximation target for `Ξ`.

This is stronger and more relevant than merely proving `Ξ'(0)=0`: the finite
approximants are explicitly products over real paired roots, and the missing
analytic payload is a genuine approximation theorem for canonical `Ξ`
Hadamard products.  This target is the Ξ-plane version of the
Laguerre--Pólya route rather than the obstructed s-plane height-balancing
route. -/
structure XiLaguerrePolyaFiniteWitness where
  approximants : ℕ → ℝ → ℝ
  zeroPairs : ℕ → Finset ℝ
  approximants_eq : ∀ n : ℕ, approximants n = xiEvenProduct (zeroPairs n)
  pointwiseConverges : ∀ t : ℝ, Tendsto (fun n : ℕ => approximants n t) atTop (𝓝 (Xi t))
  complexLocallyUniform : TendstoLocallyUniformly
    (fun (n : ℕ) (z : ℂ) => ∏ τ ∈ zeroPairs n, (z - (τ : ℂ)) * (z + (τ : ℂ)))
    (fun z => xiCompleted (1 / 2 + z * Complex.I)) atTop

/-- The current Ξ-plane target: build canonical finite real-rooted even products
that converge to `Ξ`.  Supplying this would put the attack back onto the
Laguerre--Pólya/Jensen spine, where the remaining bridge is `PolyaJensenBridge`
from `JensenProgram`. -/
def XiLaguerrePolyaFiniteTarget : Prop :=
  Nonempty XiLaguerrePolyaFiniteWitness

/-- The normalized version of the finite real-rooted approximation target.

This is the mathematically correct shape for canonical Ξ-Hadamard products:
finite products over real paired roots, plus a scalar normalization. -/
structure XiLaguerrePolyaScaledFiniteWitness where
  approximants : ℕ → ℝ → ℝ
  scales : ℕ → ℝ
  zeroPairs : ℕ → Finset ℝ
  approximants_eq :
    ∀ n : ℕ, approximants n = xiEvenScaledProduct (scales n) (zeroPairs n)
  pointwiseConverges :
    ∀ t : ℝ, Tendsto (fun n : ℕ => approximants n t) atTop (𝓝 (Xi t))
  complexLocallyUniform : TendstoLocallyUniformly
    (fun (n : ℕ) (z : ℂ) => (scales n : ℂ) *
      ∏ τ ∈ zeroPairs n, (z - (τ : ℂ)) * (z + (τ : ℂ)))
    (fun z => xiCompleted (1 / 2 + z * Complex.I)) atTop

/-- The corrected finite-product target for the Ξ-plane route. -/
def XiLaguerrePolyaScaledFiniteTarget : Prop :=
  Nonempty XiLaguerrePolyaScaledFiniteWitness

/-- The analytic closure theorem needed after constructing normalized finite
real-rooted approximants: such convergence places `Ξ` in the
Laguerre--Pólya/Jensen class, hence all Jensen polynomials are hyperbolic.

The witness explicitly requires locally uniform convergence on ℂ, not merely
pointwise convergence on ℝ. This is intentionally a `Prop`, not an axiom.
Proving it requires the real
entire-function theorem connecting locally uniform limits of real-rooted
polynomials to Jensen hyperbolicity. -/
def XiLaguerrePolyaClosureBridge : Prop :=
  XiLaguerrePolyaScaledFiniteTarget → AllClassicalJensenHyperbolic

/-- If the normalized finite real-rooted approximation theorem and its
Laguerre--Pólya closure bridge are supplied, then the remaining deduction to RH
is exactly the existing Pólya--Jensen bridge. -/
theorem riemannHypothesis_of_xiLaguerrePolyaScaledFinite
    (hfinite : XiLaguerrePolyaScaledFiniteTarget)
    (hclosure : XiLaguerrePolyaClosureBridge)
    (hpolya : PolyaJensenBridge) : RiemannHypothesis :=
  hpolya.mpr (hclosure hfinite)

/-- The unscaled target is a special case of the scaled target, with every scale
equal to `1`. -/
theorem xiLaguerrePolyaScaledFiniteTarget_of_unscaled
    (h : XiLaguerrePolyaFiniteTarget) : XiLaguerrePolyaScaledFiniteTarget := by
  rcases h with ⟨w⟩
  refine ⟨{
    approximants := w.approximants
    scales := fun _ => 1
    zeroPairs := w.zeroPairs
    approximants_eq := ?_
    pointwiseConverges := w.pointwiseConverges
    complexLocallyUniform := by simpa using! w.complexLocallyUniform
  }⟩
  intro n
  rw [w.approximants_eq n]
  funext t
  simp [xiEvenScaledProduct]

/-- A scaled finite-product witness still gives finite criticality at the
origin for every approximant. -/
theorem deriv_scaledApproximants_zero_of_xiLaguerrePolyaScaledFiniteWitness
    (w : XiLaguerrePolyaScaledFiniteWitness) (n : ℕ) :
    deriv (w.approximants n) 0 = 0 := by
  rw [w.approximants_eq n]
  exact deriv_xiEvenScaledProduct_zero (w.scales n) (w.zeroPairs n)

end Reinmann
