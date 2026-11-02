/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.XiPlanePrincipalValue
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Total-Positivity Targets for the Xi Aperture Program

The direct existence theorem for canonical finite real-rooted approximants to
`Xi` is RH-level content.  This file records a more structural route: prove
positivity of finite Hankel determinants of the signed `Xi` moment sequence,
then use an external total-positivity/Edrei-Schoenberg type theorem to obtain
the finite real-rooted approximation target.

The sign is important.  If

`Xi(t) = C * ∏ k, (1 - t^2 / τ_k^2)`,

then the raw Taylor coefficients of `t^(2n)` alternate.  The moment-like
positive sequence is therefore `(-1)^n * XiCoeff n`, not `XiCoeff n` itself.

No positivity theorem is assumed here.  The analytic content is exposed as named
`Prop`s so the verifier can audit exactly what remains missing.

## ⚠ Correction: Hankel is the wrong machine — see `XiToeplitzPositivity`

This Hankel/moment route is **superseded**.  The Hamburger/Stieltjes moment
problem characterizes generating functions that are Cauchy/Stieltjes transforms
(meromorphic, with poles), never entire products; and Hankel positivity forces
*log-convexity* `μ_n² ≤ μ_{n-1}μ_{n+1}` (see
`xiMomentCoeff_logConvex_of_hankelTotalPositive`).  A genuine Laguerre–Pólya
product `C·∏(1 - t²/τ_k²)` instead has *log-concave* normalized coefficients
(Newton/Turán: the proven Csordas–Norfolk–Varga inequalities for Ξ).  The two
demands are compatible only in the degenerate log-affine case, so
`XiHankelTotalPositive` is the wrong target.

The corrected route uses the **Toeplitz** matrix `[μ_{i-j}]` (Pólya frequency
sequences, Aissen–Edrei–Schoenberg–Whitney), formalized in
`Reinmann/XiToeplitzPositivity.lean`, whose `2×2` minor reproduces exactly the
(proven) Turán inequality.  This file is retained for the determinant lemmas and
as the documented obstruction.
-/

noncomputable section

open Matrix

namespace Reinmann

/-! ## Signed moment sequence and Hankel matrices -/

/-- The signed `Xi` coefficient sequence expected to behave like a positive
moment sequence under RH-level real-rootedness:

`mu_n = (-1)^n * b_n`, where `b_n = XiCoeff n`. -/
def XiMomentCoeff (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * XiCoeff n

/-- The contiguous Hankel matrix of the signed `Xi` moment sequence with size `N`
and shift `m`.

Its `(i,j)` entry is `mu_{m+i+j}` where
`mu_n = (-1)^n * XiCoeff n`. -/
def XiHankelMatrix (N m : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => XiMomentCoeff (m + i.val + j.val)

/-- The determinant of a contiguous Hankel matrix of signed `Xi` moments. -/
def XiHankelDet (N m : ℕ) : ℝ :=
  (XiHankelMatrix N m).det

/-- Contiguous Hankel total positivity for the signed `Xi` moment sequence.

This is a conservative first formal target: it asks only for nonnegative
determinants of contiguous Hankel blocks.  Full total positivity would quantify
over arbitrary minors; this version is easier to formalize and already captures
the Stieltjes-moment style positivity suggested by the Aperture Closure Program. -/
def XiHankelTotalPositive : Prop :=
  ∀ N m : ℕ, 0 < N → 0 ≤ XiHankelDet N m

/-- The `1 x 1` Hankel determinant is the signed moment coefficient itself. -/
theorem XiHankelDet_one (m : ℕ) :
    XiHankelDet 1 m = XiMomentCoeff m := by
  simp [XiHankelDet, XiHankelMatrix]

/-- Contiguous Hankel positivity includes nonnegativity of every signed moment
coefficient. -/
theorem xiMomentCoeff_nonneg_of_hankelTotalPositive
    (h : XiHankelTotalPositive) (m : ℕ) : 0 ≤ XiMomentCoeff m := by
  simpa [XiHankelDet_one] using! h 1 m (by decide)

/-- The `2 x 2` contiguous Hankel determinant is the adjacent moment
log-convexity determinant. -/
theorem XiHankelDet_two (m : ℕ) :
    XiHankelDet 2 m =
      XiMomentCoeff m * XiMomentCoeff (m + 2) - XiMomentCoeff (m + 1) ^ 2 := by
  rw [XiHankelDet, Matrix.det_fin_two]
  simp [XiHankelMatrix, sq]

/-- Contiguous Hankel positivity includes adjacent log-convexity of the signed
moment sequence. -/
theorem xiMomentCoeff_logConvex_of_hankelTotalPositive
    (h : XiHankelTotalPositive) (m : ℕ) :
    XiMomentCoeff (m + 1) ^ 2 ≤ XiMomentCoeff m * XiMomentCoeff (m + 2) := by
  have hdet : 0 ≤ XiHankelDet 2 m := h 2 m (by decide)
  rw [XiHankelDet_two] at hdet
  nlinarith

/-! ## Raw-coefficient obstruction marker -/

/-- Raw, unsigned contiguous Hankel positivity.  This is kept only as an
obstruction marker: for a real-rooted even product the raw coefficients are
expected to alternate, so this is not the right positivity target. -/
def XiRawHankelMatrix (N m : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => XiCoeff (m + i.val + j.val)

/-- Determinant of the raw-coefficient Hankel matrix. -/
def XiRawHankelDet (N m : ℕ) : ℝ :=
  (XiRawHankelMatrix N m).det

/-- The likely-wrong raw-coefficient positivity target.  Use
`XiHankelTotalPositive` instead. -/
def XiRawHankelTotalPositive : Prop :=
  ∀ N m : ℕ, 0 < N → 0 ≤ XiRawHankelDet N m

/-! ## Aperture-closure bridge contracts -/

/-- The external analytic theorem that coefficient Hankel positivity forces the
normalized finite real-rooted approximation target for `Xi`.

This is the new total-positivity payload proposed in
`research/XI_LAGUERRE_POLYA_EXISTENCE_PROGRAM.md`. -/
def XiHankelTPToScaledFiniteBridge : Prop :=
  XiHankelTotalPositive → XiLaguerrePolyaScaledFiniteTarget

/-- Intermediate moment-representation target for the signed `Xi` coefficients.
This is a Stieltjes-type representation statement, deliberately separated from
finite-product convergence. -/
def XiSignedMomentRepresentation : Prop :=
  ∃ μ : ℕ → ℝ, ∀ n : ℕ, μ n = XiMomentCoeff n

/-- A placeholder-free bridge target: contiguous Hankel positivity should first
produce a genuine moment representation.  The present lightweight
`XiSignedMomentRepresentation` records the interface; a stronger future version
should replace `ℕ → ℝ` by a positive measure on `[0,∞)`. -/
def XiHankelTPToMomentBridge : Prop :=
  XiHankelTotalPositive → XiSignedMomentRepresentation

/-- The second external bridge: a signed-moment representation compatible with
the xi Fourier kernel should produce normalized finite real-rooted approximants.
This is the Edrei-Schoenberg/Laguerre-Polya payload, kept separate from Hankel
positivity itself. -/
def XiMomentToScaledFiniteBridge : Prop :=
  XiSignedMomentRepresentation → XiLaguerrePolyaScaledFiniteTarget

/-- The two-stage aperture bridge implies the earlier one-stage bridge. -/
theorem xiHankelTPToScaledFiniteBridge_of_moment_bridges
    (hMoment : XiHankelTPToMomentBridge)
    (hFinite : XiMomentToScaledFiniteBridge) :
    XiHankelTPToScaledFiniteBridge := by
  intro hTP
  exact hFinite (hMoment hTP)

/-- A bundled witness for the total-positivity aperture route. -/
structure XiTotalPositivityApertureWitness where
  hankelPositive : XiHankelTotalPositive
  toScaledFinite : XiHankelTPToScaledFiniteBridge
  closure : XiLaguerrePolyaClosureBridge
  polya : PolyaJensenBridge

/-- Total positivity of the `Xi` coefficient Hankel matrices implies RH once the
two external bridges are supplied: total positivity to finite real-rooted
approximants, and finite approximants to Jensen hyperbolicity. -/
theorem riemannHypothesis_of_xiTotalPositivityAperture
    (w : XiTotalPositivityApertureWitness) : RiemannHypothesis :=
  riemannHypothesis_of_xiLaguerrePolyaScaledFinite
    (w.toScaledFinite w.hankelPositive) w.closure w.polya

end Reinmann
