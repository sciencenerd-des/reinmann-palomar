/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.HilbertPolyaExperiment

@[expose] public section

/-!
# Pseudo-Hermitian conditional eigenvector reduction

The proof uses scalar homogeneity, symmetry and nonzero diagonal mass. The
structure below asks for diagonal nonvanishing at every nonzero vector;
this is stronger than ordinary nondegeneracy of an indefinite form. Its
fields do not assert additivity or Hermitian symmetry.

`PseudoHermitianLocal` weakens the interface to the selected zero-indexed
states, separates the action domain from the ambient space, and records
relative defect and approximate-eigenvector budgets. The eigenvalue
non-isotropy mechanism is classical (Mostafazadeh 2002, Proposition 2).

Both files give conditional deductions. They construct no arithmetic
operator, metric or zero-to-state map. The code makes no claim of logical
independence from other RH criteria or of full-spectrum equality.
-/

noncomputable section

open Complex
open scoped ComplexConjugate

namespace Reinmann

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Scalar form laws, global symmetry and diagonal nonvanishing. A positive
sesquilinear metric supplies these properties, but additivity and Hermitian
symmetry are not fields of this structure. No ambient inner product is used. -/
structure PseudoHermitianForm (T : E →ₗ[ℂ] E) where
  /-- The metric form. -/
  η : E → E → ℂ
  /-- Linearity in the left slot. -/
  smul_left : ∀ (c : ℂ) (x y : E), η (c • x) y = c * η x y
  /-- Conjugate-linearity in the right slot. -/
  smul_right : ∀ (c : ℂ) (x y : E), η x (c • y) = conj c * η x y
  /-- `T` is self-adjoint with respect to `η`. -/
  selfAdjoint : ∀ x y : E, η (T x) y = η x (T y)
  /-- Diagonal nonvanishing, stronger than ordinary form nondegeneracy. -/
  nondegenerate : ∀ x : E, x ≠ 0 → η x x ≠ 0

/-- **`η`-self-adjoint ⟹ real eigenvalues.** For an eigenpair `T v = μ • v` with
`v ≠ 0`, the eigenvalue is fixed by conjugation.  Proof from the metric laws:
`μ · η v v = η(Tv,v) = η(v,Tv) = conj μ · η v v`, and `η v v ≠ 0`. -/
theorem PseudoHermitianForm.eigenvalue_conj_eq {T : E →ₗ[ℂ] E}
    (P : PseudoHermitianForm T) {μ : ℂ} {v : E} (hv : v ≠ 0) (hev : T v = μ • v) :
    conj μ = μ := by
  have h1 : P.η (T v) v = μ * P.η v v := by rw [hev, P.smul_left]
  have h2 : P.η v (T v) = conj μ * P.η v v := by rw [hev, P.smul_right]
  have hsa : P.η (T v) v = P.η v (T v) := P.selfAdjoint v v
  rw [h1, h2] at hsa
  exact (mul_right_cancel₀ (P.nondegenerate v hv) hsa).symm

/-- **Pseudo-Hermitian reduction to RH.** If there is a complex vector space `E`, an
operator `T`, and a scalar-homogeneous form `η` with diagonal nonvanishing making
`T` symmetric for `η`, such that every
critical-strip zero `s` has a nonzero eigenvector with eigenvalue
`μ(s) = -i(s - 1/2)`, then RH holds.

Reality of `μ(s)` follows from symmetry and diagonal nonvanishing; it pins
`Re s = 1/2`. -/
theorem riemannHypothesis_of_pseudoHermitian_eigendata
    (T : E →ₗ[ℂ] E) (P : PseudoHermitianForm T)
    (v : ℂ → E)
    (hv : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0)
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
        T (v s) = spectralParam s • v s) :
    RiemannHypothesis := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  refine ⟨fun s hpos hlt hz => ?_⟩
  have hμ : conj (spectralParam s) = spectralParam s :=
    P.eigenvalue_conj_eq (hv s hz hpos hlt) (heig s hz hpos hlt)
  have him : (spectralParam s).im = 0 := Complex.conj_eq_iff_im.mp hμ
  exact (spectralParam_real_iff s).mp him

/-- A bundled pseudo-Hermitian witness for RH. -/
structure PseudoHermitianWitness where
  /-- The carrier space. -/
  E : Type
  [addCommGroup : AddCommGroup E]
  [module : Module ℂ E]
  /-- The operator. -/
  T : E →ₗ[ℂ] E
  /-- The scalar form with global symmetry and diagonal nonvanishing. -/
  form : PseudoHermitianForm T
  /-- Eigenvectors indexed by zeros. -/
  v : ℂ → E
  v_ne : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0
  eig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      T (v s) = spectralParam s • v s

attribute [instance] PseudoHermitianWitness.addCommGroup PseudoHermitianWitness.module

/-- A pseudo-Hermitian witness proves RH. -/
theorem riemannHypothesis_of_pseudoHermitianWitness (W : PseudoHermitianWitness) :
    RiemannHypothesis :=
  riemannHypothesis_of_pseudoHermitian_eigendata W.T W.form W.v W.v_ne W.eig

end Reinmann
