module

public import Reinmann.PseudoHermitian

@[expose] public section

/-!
# Local and domain-explicit pseudo-Hermitian reductions

Only scalar homogeneity, diagonal symmetry at the selected eigenvector and
nonzero diagonal form mass are used by the eigenvalue argument. Global
positivity and symmetry on unrelated vectors are unnecessary. The domain
carrier below is separate from the ambient space; no everywhere-defined
linear operator is assumed.

These are conditional interfaces, not a construction of zeta eigendata.
The non-isotropy mechanism is classical (Mostafazadeh 2002, Proposition 2).
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The two scalar laws actually needed, without global positivity or symmetry. -/
structure ScalarHomogeneousForm (E : Type*) [AddCommGroup E] [Module ℂ E] where
  η : E → E → ℂ
  smul_left : ∀ (c : ℂ) (x y : E), η (c • x) y = c * η x y
  smul_right : ∀ (c : ℂ) (x y : E), η x (c • y) = conj c * η x y

/-- Diagonal symmetry defect of an action value `w` at a state `v`. -/
def ScalarHomogeneousForm.defect (F : ScalarHomogeneousForm E) (v w : E) : ℂ :=
  F.η w v - F.η v w

theorem ScalarHomogeneousForm.defect_eq_of_eigenpair
    (F : ScalarHomogeneousForm E) {v w : E} {μ : ℂ} (heig : w = μ • v) :
    F.defect v w = (μ - conj μ) * F.η v v := by
  rw [ScalarHomogeneousForm.defect, heig, F.smul_left, F.smul_right]
  ring

/-- Nonvanishing is required only at this eigenvector. -/
theorem ScalarHomogeneousForm.eigenvalue_conj_eq_of_local
    (F : ScalarHomogeneousForm E) {v w : E} {μ : ℂ}
    (heig : w = μ • v) (hsym : F.η w v = F.η v w)
    (hmass : F.η v v ≠ 0) : conj μ = μ := by
  have h := F.defect_eq_of_eigenpair heig
  have hz : F.defect v w = 0 := sub_eq_zero.mpr hsym
  rw [hz] at h
  have hsub : μ - conj μ = 0 := (mul_eq_zero.mp h.symm).resolve_right hmass
  exact (sub_eq_zero.mp hsub).symm

/-- Nonreal eigenvalues can survive local symmetry only at isotropic states. -/
theorem ScalarHomogeneousForm.isotropic_of_nonreal
    (F : ScalarHomogeneousForm E) {v w : E} {μ : ℂ}
    (heig : w = μ • v) (hsym : F.η w v = F.η v w)
    (hnonreal : conj μ ≠ μ) : F.η v v = 0 := by
  by_contra hmass
  exact hnonreal (F.eigenvalue_conj_eq_of_local heig hsym hmass)

/-- Exact translation from conjugation defect to distance from the critical line. -/
theorem norm_spectralParam_sub_conj (s : ℂ) :
    ‖spectralParam s - conj (spectralParam s)‖ = 2 * |s.re - 1 / 2| := by
  have him : (spectralParam s).im = -(s.re - 1 / 2) := by
    simp [spectralParam, Complex.mul_im]
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), him, abs_neg]

/-- An exact eigenpair turns the form defect into a critical-line distance. -/
theorem ScalarHomogeneousForm.critical_distance_mass_eq_defect
    (F : ScalarHomogeneousForm E) {v w : E} {s : ℂ}
    (heig : w = spectralParam s • v) :
    2 * |s.re - 1 / 2| * ‖F.η v v‖ = ‖F.defect v w‖ := by
  rw [F.defect_eq_of_eigenpair heig, norm_mul, norm_spectralParam_sub_conj]

/-- A relative diagonal-defect budget gives an explicit horizontal enclosure. -/
theorem ScalarHomogeneousForm.critical_distance_le_of_defect
    (F : ScalarHomogeneousForm E) {v w : E} {s : ℂ} {ε : ℝ}
    (heig : w = spectralParam s • v) (hmass : F.η v v ≠ 0)
    (hdefect : ‖F.defect v w‖ ≤ 2 * ε * ‖F.η v v‖) :
    |s.re - 1 / 2| ≤ ε := by
  have hmasspos : 0 < ‖F.η v v‖ := norm_pos_iff.mpr hmass
  have h := F.critical_distance_mass_eq_defect heig
  nlinarith

/-- Additivity is needed only for the residual extension, not the exact-pair
argument. No positivity or Hermitian symmetry is imposed. -/
structure AdditiveScalarForm (E : Type*) [AddCommGroup E] [Module ℂ E]
    extends ScalarHomogeneousForm E where
  add_left : ∀ x y z : E, η (x + y) z = η x z + η y z
  add_right : ∀ x y z : E, η x (y + z) = η x y + η x z

/-- An approximate eigenpair separates the symmetry defect from the paired
eigenvector residual. -/
theorem AdditiveScalarForm.skew_mass_eq_defect_sub_residual
    (F : AdditiveScalarForm E) {v w r : E} {μ : ℂ}
    (heig : w = μ • v + r) :
    (μ - conj μ) * F.η v v =
      F.toScalarHomogeneousForm.defect v w - F.toScalarHomogeneousForm.defect v r := by
  rw [ScalarHomogeneousForm.defect, ScalarHomogeneousForm.defect, heig,
    F.add_left, F.add_right, F.smul_left, F.smul_right]
  ring

/-- Quantitative local criterion allowing both approximate symmetry and an
approximate eigenvector. The budget must be relative to the diagonal mass. -/
theorem AdditiveScalarForm.critical_distance_le_of_residual_budget
    (F : AdditiveScalarForm E) {v w r : E} {s : ℂ} {ε : ℝ}
    (heig : w = spectralParam s • v + r) (hmass : F.η v v ≠ 0)
    (hbudget : ‖F.toScalarHomogeneousForm.defect v w‖ +
      ‖F.toScalarHomogeneousForm.defect v r‖ ≤ 2 * ε * ‖F.η v v‖) :
    |s.re - 1 / 2| ≤ ε := by
  have hidentity := F.skew_mass_eq_defect_sub_residual heig
  have hnorm := congrArg norm hidentity
  rw [norm_mul, norm_spectralParam_sub_conj] at hnorm
  have htriangle := norm_sub_le (F.toScalarHomogeneousForm.defect v w)
    (F.toScalarHomogeneousForm.defect v r)
  have hmasspos : 0 < ‖F.η v v‖ := norm_pos_iff.mpr hmass
  nlinarith

/-- Recover the two scalar laws from the original stronger interface. -/
def PseudoHermitianForm.toScalarHomogeneousForm {T : E →ₗ[ℂ] E}
    (P : PseudoHermitianForm T) : ScalarHomogeneousForm E where
  η := P.η
  smul_left := P.smul_left
  smul_right := P.smul_right

/-- Domain-explicit local reduction. `ι` represents domain states in the ambient
space, and `action` is defined on that domain only. -/
theorem riemannHypothesis_of_localForm_eigendata
    {D : Type*} (ι action : D → E) (F : ScalarHomogeneousForm E)
    (v : ℂ → D)
    (hmass : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      F.η (ι (v s)) (ι (v s)) ≠ 0)
    (hsym : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      F.η (action (v s)) (ι (v s)) = F.η (ι (v s)) (action (v s)))
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      action (v s) = spectralParam s • ι (v s)) :
    RiemannHypothesis := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  refine ⟨fun s hpos hlt hz => ?_⟩
  have hμ := F.eigenvalue_conj_eq_of_local (heig s hz hpos hlt)
    (hsym s hz hpos hlt) (hmass s hz hpos hlt)
  exact (spectralParam_real_iff s).mp (Complex.conj_eq_iff_im.mp hμ)

/-- Specialization to a genuine linear operator with a specified submodule
domain. Neither boundedness nor an everywhere-defined extension is required. -/
theorem riemannHypothesis_of_localForm_submodule
    (D : Submodule ℂ E) (T : D →ₗ[ℂ] E) (F : ScalarHomogeneousForm E)
    (v : ℂ → D)
    (hmass : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      F.η (v s : E) (v s : E) ≠ 0)
    (hsym : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      F.η (T (v s)) (v s : E) = F.η (v s : E) (T (v s)))
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      T (v s) = spectralParam s • (v s : E)) : RiemannHypothesis :=
  riemannHypothesis_of_localForm_eigendata (fun u : D => (u : E))
    (fun u => T u) F v hmass hsym heig

/-- The old global witness supplies every local hypothesis, proving backwards
compatibility without imposing its global assumptions on the new theorem. -/
theorem riemannHypothesis_of_pseudoHermitian_via_local
    (T : E →ₗ[ℂ] E) (P : PseudoHermitianForm T) (v : ℂ → E)
    (hv : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → v s ≠ 0)
    (heig : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      T (v s) = spectralParam s • v s) : RiemannHypothesis := by
  apply riemannHypothesis_of_localForm_eigendata id (fun x => T x)
    P.toScalarHomogeneousForm v
  · intro s hz hpos hlt
    exact P.nondegenerate (v s) (hv s hz hpos hlt)
  · intro s hz hpos hlt
    exact P.selfAdjoint (v s) (v s)
  · exact heig

/-- Pointwise approximation suffices: for every critical-strip zero and every
positive tolerance, find a domain state with a small relative defect budget.
No uniform-in-zero convergence or exact eigenvector limit is assumed. -/
theorem riemannHypothesis_of_localForm_approximation
    {D : Type*} (ι action : D → E) (F : AdditiveScalarForm E)
    (happrox : ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      ∀ ε : ℝ, 0 < ε → ∃ u : D, ∃ r : E,
        action u = spectralParam s • ι u + r ∧ F.η (ι u) (ι u) ≠ 0 ∧
        ‖F.toScalarHomogeneousForm.defect (ι u) (action u)‖ +
          ‖F.toScalarHomogeneousForm.defect (ι u) r‖ ≤
            2 * ε * ‖F.η (ι u) (ι u)‖) : RiemannHypothesis := by
  rw [← criticalStripObligations_iff_riemannHypothesis]
  refine ⟨fun s hpos hlt hz => ?_⟩
  have hzero : |s.re - 1 / 2| = 0 := by
    by_contra hne
    have hdist : 0 < |s.re - 1 / 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    obtain ⟨u, r, heig, hmass, hbudget⟩ :=
      happrox s hz hpos hlt (|s.re - 1 / 2| / 2) (by positivity)
    have hbound := F.critical_distance_le_of_residual_budget heig hmass hbudget
    linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

end Reinmann
