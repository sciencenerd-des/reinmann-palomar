/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.RiemannSpine
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Experiment B: An Honest Hilbert–Pólya Reduction

## First-principles motivation

The Hilbert–Pólya program proposes a self-adjoint operator whose spectrum is the
imaginary parts of the zeta zeros; self-adjointness forces real eigenvalues,
which forces the zeros onto the critical line. The folklore version of this in the
codebase (`HilbertPolyaWitness`) *asserts* "self-adjoint forces critical line" as
a field. That is unsatisfying: it hides the actual mechanism behind an axiom-like
hypothesis.

Here we make the mechanism a **theorem**. The only spectral input needed is:

> *Eigenvalues of a symmetric operator are real.*

and this is provable directly from the inner-product axioms (no spectral theorem,
no completeness, no boundedness). We prove it, then build the Hilbert–Pólya
reduction on top of it. The encoding `μ(s) = -i (s - 1/2)` is chosen so that

  `μ(s)` is real  ⟺  `Re s = 1/2`,

so an eigenvalue at `μ(s)` for every strip zero `s` collapses RH to the reality
that symmetry already guarantees.

## Honest status

This does **not** prove RH. It relocates the entire problem to a single, sharply
stated construction task: *exhibit a complex inner-product space `E`, a symmetric
operator `T`, and for each critical-strip zero `s` a nonzero `v s` with
`T (v s) = μ(s) • v s`.* What it removes is the hand-wave: reality is no longer
assumed, it is derived. The remaining task is exactly the open Hilbert–Pólya
construction.
-/

noncomputable section

open Complex
open scoped InnerProductSpace ComplexConjugate

namespace Reinmann

/-! ### The spectral engine: symmetric ⟹ real eigenvalues (from first principles) -/

section Symmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Eigenvalues of a symmetric operator are fixed by conjugation** (hence real).
Proof from the inner-product axioms alone: `⟪T v, v⟫ = ⟪v, T v⟫` expands to
`conj μ · ⟪v,v⟫ = μ · ⟪v,v⟫`, and `⟪v,v⟫ ≠ 0`. -/
theorem symmetric_eigenvalue_conj_eq {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    {μ : 𝕜} {v : E} (hv : v ≠ 0) (hev : T v = μ • v) :
    (starRingEnd 𝕜) μ = μ := by
  have hsym : ⟪T v, v⟫_𝕜 = ⟪v, T v⟫_𝕜 := hT v v
  rw [hev, inner_smul_left, inner_smul_right] at hsym
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := inner_self_ne_zero.mpr hv
  exact mul_right_cancel₀ hvv hsym

end Symmetric

/-! ### The Hilbert–Pólya reduction -/

section HilbertPolya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The spectral parameter attached to a zero `s`: `μ(s) = -i (s - 1/2)`.
It is real exactly when `Re s = 1/2`. -/
def spectralParam (s : ℂ) : ℂ := -Complex.I * (s - 1 / 2)

/-- `μ(s)` is real iff `s` lies on the critical line. -/
theorem spectralParam_real_iff (s : ℂ) :
    (spectralParam s).im = 0 ↔ s.re = 1 / 2 := by
  unfold spectralParam
  constructor <;> intro h <;>
    · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im, Complex.sub_re, Complex.sub_im] at h ⊢
      norm_num at h ⊢
      linarith

/-- **Honest Hilbert–Pólya reduction.** If there is a complex inner-product space
`E` with a symmetric operator `T` that has, for every critical-strip zero `s`, a
nonzero eigenvector with eigenvalue `μ(s) = -i (s - 1/2)`, then the Riemann
Hypothesis holds.

The reality of `μ(s)` is *proved* (via `symmetric_eigenvalue_conj_eq`), not
assumed; it then pins `Re s = 1/2`. -/
theorem riemannHypothesis_of_symmetric_eigendata
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (v : ℂ → E)
    (hv : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0)
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
        T (v s) = spectralParam s • v s) :
    RiemannHypothesis := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  refine ⟨fun s hpos hlt hz => ?_⟩
  -- The eigenvalue μ(s) is real because T is symmetric.
  have hμ : (starRingEnd ℂ) (spectralParam s) = spectralParam s :=
    symmetric_eigenvalue_conj_eq hT (hv s hz hpos hlt) (heig s hz hpos hlt)
  have him : (spectralParam s).im = 0 := Complex.conj_eq_iff_im.mp hμ
  -- Reality of μ(s) forces s onto the critical line.
  exact (spectralParam_real_iff s).mp him

end HilbertPolya

end Reinmann
