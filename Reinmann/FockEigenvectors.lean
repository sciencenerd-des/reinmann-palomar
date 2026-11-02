/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.PseudoHermitianLocal
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# Coefficient model for a Fock-space candidate

This file checks the coefficient action, coherent eigenvectors, convergent
pairings and exact masses. It does not assert that the action is symmetric.
The Xi-generated Hilbert subspace and its analytic domain are described in
`research/pseudo_hermitian/FOCK_CANDIDATE.md`; their construction is not yet
formalized here. On arbitrary sequences the total `tsum` pairing below need
not be additive. On coherent vectors its series is proved convergent.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.FockEigenvectors

abbrev Coeff := ℕ → ℂ

def coherent (s : ℂ) : Coeff := fun n => s ^ n / (n.factorial : ℂ)

def derivativeAction : Coeff →ₗ[ℂ] Coeff where
  toFun c n := (n + 1 : ℂ) * c (n + 1)
  map_add' := by intro c d; ext n; simp [mul_add]
  map_smul' := by intro a c; ext n; simp [smul_eq_mul]; ring

def spectralAction : Coeff →ₗ[ℂ] Coeff :=
  (-I) • (derivativeAction - (1 / 2 : ℂ) • LinearMap.id)

theorem derivative_coherent (s : ℂ) : derivativeAction (coherent s) = s • coherent s := by
  ext n
  simp only [derivativeAction, LinearMap.coe_mk, AddHom.coe_mk,
    coherent, Pi.smul_apply, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem spectral_coherent (s : ℂ) :
    spectralAction (coherent s) = spectralParam s • coherent s := by
  ext n
  have hd := congrFun (derivative_coherent s) n
  simp only [Pi.smul_apply, smul_eq_mul] at hd
  change -I * (derivativeAction (coherent s) n - (1 / 2 : ℂ) * coherent s n) =
    spectralParam s * coherent s n
  rw [hd]
  unfold spectralParam
  ring

def pairing (c d : Coeff) : ℂ :=
  ∑' n, (n.factorial : ℂ) * c n * conj (d n)

def scalarForm : ScalarHomogeneousForm Coeff where
  η := pairing
  smul_left := by
    intro a c d
    change (∑' n, (n.factorial : ℂ) * (a * c n) * conj (d n)) = a * pairing c d
    simp_rw [show ∀ n, (n.factorial : ℂ) * (a * c n) * conj (d n) =
      a * ((n.factorial : ℂ) * c n * conj (d n)) by intro n; ring]
    exact tsum_mul_left
  smul_right := by
    intro a c d
    change (∑' n, (n.factorial : ℂ) * c n * conj (a * d n)) = conj a * pairing c d
    simp_rw [map_mul]
    simp_rw [show ∀ n, (n.factorial : ℂ) * c n * (conj a * conj (d n)) =
      conj a * ((n.factorial : ℂ) * c n * conj (d n)) by intro n; ring]
    exact tsum_mul_left

theorem coherent_pairing_term (s t : ℂ) (n : ℕ) :
    (n.factorial : ℂ) * coherent s n * conj (coherent t n) =
      (s * conj t) ^ n / (n.factorial : ℂ) := by
  simp only [coherent, map_div₀, map_pow, map_natCast, mul_pow]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem coherent_pairing_hasSum (s t : ℂ) :
    HasSum (fun n => (n.factorial : ℂ) * coherent s n * conj (coherent t n))
      (Complex.exp (s * conj t)) := by
  simp_rw [coherent_pairing_term]
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp _

theorem coherent_pairing (s t : ℂ) :
    pairing (coherent s) (coherent t) = Complex.exp (s * conj t) :=
  (coherent_pairing_hasSum s t).tsum_eq

theorem coherent_mass_ne_zero (s : ℂ) :
    scalarForm.η (coherent s) (coherent s) ≠ 0 := by
  change pairing (coherent s) (coherent s) ≠ 0
  rw [coherent_pairing]
  exact Complex.exp_ne_zero _

theorem coherent_mass_norm (s : ℂ) :
    ‖scalarForm.η (coherent s) (coherent s)‖ = Real.exp (s * conj s).re := by
  change ‖pairing (coherent s) (coherent s)‖ = _
  rw [coherent_pairing, Complex.norm_exp]

theorem coherent_mass_norm_ge_one (s : ℂ) :
    1 ≤ ‖scalarForm.η (coherent s) (coherent s)‖ := by
  rw [coherent_mass_norm]
  apply Real.one_le_exp_iff.mpr
  simpa only [Complex.mul_conj, Complex.ofReal_re] using! Complex.normSq_nonneg s

def normalized (s : ℂ) : Coeff :=
  (Real.exp (-Complex.normSq s / 2) : ℂ) • coherent s

theorem normalized_mass (s : ℂ) : scalarForm.η (normalized s) (normalized s) = 1 := by
  rw [normalized, scalarForm.smul_left, scalarForm.smul_right]
  change (Real.exp (-Complex.normSq s / 2) : ℂ) *
    (conj (Real.exp (-Complex.normSq s / 2) : ℂ) * pairing (coherent s) (coherent s)) = 1
  rw [coherent_pairing, Complex.mul_conj, ← Complex.ofReal_exp]
  rw [Complex.conj_ofReal]
  norm_cast
  rw [← Real.exp_add, ← Real.exp_add]
  rw [show -Complex.normSq s / 2 + (-Complex.normSq s / 2 + Complex.normSq s) = 0 by ring,
    Real.exp_zero]

theorem normalized_eigen (s : ℂ) :
    spectralAction (normalized s) = spectralParam s • normalized s := by
  rw [normalized, map_smul, spectral_coherent, smul_comm]

theorem normalized_defect_norm (s : ℂ) :
    ‖scalarForm.defect (normalized s) (spectralAction (normalized s))‖ =
      2 * |s.re - 1 / 2| := by
  have h := scalarForm.critical_distance_mass_eq_defect (normalized_eigen s)
  rw [normalized_mass, norm_one, mul_one] at h
  exact h.symm

theorem coherent_relative_defect (s : ℂ) :
    ‖scalarForm.defect (coherent s) (spectralAction (coherent s))‖ =
      2 * |s.re - 1 / 2| * ‖scalarForm.η (coherent s) (coherent s)‖ :=
  (scalarForm.critical_distance_mass_eq_defect (spectral_coherent s)).symm

/-- The diagonal symmetry condition on these states is precisely criticality.
Mass and eigenpair construction alone have not supplied that condition. -/
theorem coherent_diagonal_symmetry_iff (s : ℂ) :
    scalarForm.η (spectralAction (coherent s)) (coherent s) =
      scalarForm.η (coherent s) (spectralAction (coherent s)) ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hc := scalarForm.eigenvalue_conj_eq_of_local (spectral_coherent s) h
      (coherent_mass_ne_zero s)
    exact (spectralParam_real_iff s).mp (Complex.conj_eq_iff_im.mp hc)
  · intro h
    rw [spectral_coherent, scalarForm.smul_left, scalarForm.smul_right]
    have hc : conj (spectralParam s) = spectralParam s :=
      Complex.conj_eq_iff_im.mpr ((spectralParam_real_iff s).mpr h)
    rw [hc]

theorem coherent_cross_defect (s t : ℂ) :
    scalarForm.η (spectralAction (coherent s)) (coherent t) -
      scalarForm.η (coherent s) (spectralAction (coherent t)) =
        (spectralParam s - conj (spectralParam t)) * Complex.exp (s * conj t) := by
  rw [spectral_coherent, spectral_coherent, scalarForm.smul_left, scalarForm.smul_right]
  change spectralParam s * pairing (coherent s) (coherent t) -
    conj (spectralParam t) * pairing (coherent s) (coherent t) = _
  rw [coherent_pairing]
  ring

theorem coherent_cross_symmetry_iff (s t : ℂ) :
    scalarForm.η (spectralAction (coherent s)) (coherent t) =
      scalarForm.η (coherent s) (spectralAction (coherent t)) ↔
        spectralParam s = conj (spectralParam t) := by
  rw [← sub_eq_zero, coherent_cross_defect]
  simp [Complex.exp_ne_zero, sub_eq_zero]

end Reinmann.FockEigenvectors
