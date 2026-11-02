/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
module

public import Reinmann.FockEigenvectors
public import Reinmann.JensenProgram
public import Mathlib.Analysis.Complex.TaylorSeries

@[expose] public section

/-!
# An arithmetic coefficient-domain operator from the entire Xi function

The domain is defined by convergent rows of `xiCompleted(derivativeAction)`,
without supplying a list of zeros. Coherent states belong to it exactly at Xi
zeros. The differential action preserves the domain. Pairing masses are
nonzero, but diagonal symmetry at the zero states is still unproved and
equivalent to RH. This algebraic construction does not assert a closed,
densely defined Hilbert-space operator or a positive form on all raw sequences.
-/

noncomputable section
open Complex
open scoped ComplexConjugate

namespace Reinmann.XiAnnihilator

open FockEigenvectors

def xiTaylor (k : ℕ) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedDeriv k xiCompleted 0

theorem xiTaylor_hasSum (s : ℂ) :
    HasSum (fun k => xiTaylor k * s ^ k) (xiCompleted s) := by
  have h := Complex.hasSum_taylorSeries_of_entire differentiable_xiCompleted 0 s
  convert h using 1
  all_goals try rfl
  ext k
  simp only [xiTaylor, sub_zero, smul_eq_mul]
  ring

def rowTerm (n : ℕ) (c : Coeff) (k : ℕ) : ℂ :=
  xiTaylor k * ((derivativeAction ^ (k + n)) c) 0

def domain : Submodule ℂ Coeff where
  carrier := {c | ∀ n, Summable (rowTerm n c) ∧ ∑' k, rowTerm n c k = 0}
  zero_mem' := by
    intro n
    have hterm : rowTerm n 0 = fun _ => 0 := by
      ext k
      simp [rowTerm]
    rw [hterm]
    exact ⟨summable_zero, tsum_zero⟩
  add_mem' := by
    intro c d hc hd n
    have hterm : rowTerm n (c + d) = fun k => rowTerm n c k + rowTerm n d k := by
      ext k
      simp [rowTerm, map_add, mul_add]
    rw [hterm]
    exact ⟨(hc n).1.add (hd n).1, by rw [(hc n).1.tsum_add (hd n).1, (hc n).2,
      (hd n).2, zero_add]⟩
  smul_mem' := by
    intro a c hc n
    have hterm : rowTerm n (a • c) = fun k => a * rowTerm n c k := by
      ext k
      simp [rowTerm, map_smul, smul_eq_mul]
      ring
    rw [hterm]
    exact ⟨(hc n).1.mul_left a, by rw [tsum_mul_left, (hc n).2, mul_zero]⟩

theorem derivative_mem_domain {c : Coeff} (hc : c ∈ domain) :
    derivativeAction c ∈ domain := by
  intro n
  have hterm : rowTerm n (derivativeAction c) = rowTerm (n + 1) c := by
    ext k
    unfold rowTerm
    rw [show k + (n + 1) = (k + n) + 1 by omega, pow_succ]
    rfl
  rw [hterm]
  exact hc (n + 1)

def derivativeOnDomain : domain →ₗ[ℂ] domain :=
  derivativeAction.restrict (fun _ hc => derivative_mem_domain hc)

def spectralOnDomain : domain →ₗ[ℂ] domain :=
  (-I) • (derivativeOnDomain - (1 / 2 : ℂ) • LinearMap.id)

theorem derivative_power_coherent (s : ℂ) (m : ℕ) :
    (derivativeAction ^ m) (coherent s) = s ^ m • coherent s := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ', Module.End.mul_apply, hm, map_smul, derivative_coherent,
      smul_smul, ← pow_succ]

theorem rowTerm_coherent (s : ℂ) (n k : ℕ) :
    rowTerm n (coherent s) k = s ^ n * (xiTaylor k * s ^ k) := by
  rw [rowTerm, derivative_power_coherent]
  simp only [Pi.smul_apply, smul_eq_mul, coherent, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, mul_one, pow_add]
  ring

theorem coherent_row_hasSum (s : ℂ) (n : ℕ) :
    HasSum (rowTerm n (coherent s)) (s ^ n * xiCompleted s) := by
  have hfun : rowTerm n (coherent s) = fun k => s ^ n * (xiTaylor k * s ^ k) :=
    funext (rowTerm_coherent s n)
  rw [hfun]
  exact (xiTaylor_hasSum s).mul_left (s ^ n)

theorem coherent_mem_domain_iff (s : ℂ) :
    coherent s ∈ domain ↔ xiCompleted s = 0 := by
  constructor
  · intro h
    have heq := (coherent_row_hasSum s 0).tsum_eq
    rw [(h 0).2] at heq
    simpa using! heq.symm
  · intro hz n
    exact ⟨(coherent_row_hasSum s n).summable, by
      rw [(coherent_row_hasSum s n).tsum_eq, hz, mul_zero]⟩

theorem xi_zero_of_strip_zero {s : ℂ} (hz : riemannZeta s = 0)
    (hpos : 0 < s.re) (hlt : s.re < 1) : xiCompleted s = 0 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hpos
  have h1 : s ≠ 1 := by intro h; simp [h] at hlt
  have hγ := Gammaℝ_ne_zero_of_re_pos hpos
  have hΛ : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero h0] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hγ
  rw [xiCompleted_eq_product h0 h1, hΛ, mul_zero]

def zeroState (s : ℂ) (hz : xiCompleted s = 0) : domain :=
  ⟨coherent s, (coherent_mem_domain_iff s).mpr hz⟩

theorem zeroState_mass (s : ℂ) (hz : xiCompleted s = 0) :
    scalarForm.η (zeroState s hz : Coeff) (zeroState s hz : Coeff) ≠ 0 :=
  coherent_mass_ne_zero s

theorem zeroState_eigen (s : ℂ) (hz : xiCompleted s = 0) :
    spectralOnDomain (zeroState s hz) = spectralParam s • zeroState s hz := by
  apply Subtype.ext
  exact spectral_coherent s

def normalizedZeroState (s : ℂ) (hz : xiCompleted s = 0) : domain :=
  (Real.exp (-Complex.normSq s / 2) : ℂ) • zeroState s hz

theorem normalizedZeroState_mass (s : ℂ) (hz : xiCompleted s = 0) :
    scalarForm.η (normalizedZeroState s hz : Coeff)
      (normalizedZeroState s hz : Coeff) = 1 := normalized_mass s

theorem normalizedZeroState_eigen (s : ℂ) (hz : xiCompleted s = 0) :
    spectralOnDomain (normalizedZeroState s hz) =
      spectralParam s • normalizedZeroState s hz := by
  apply Subtype.ext
  exact normalized_eigen s

/-- A fixed Xi-defined operator now has explicit states with exactly unit mass.
This supplies eigendata and mass, but not the missing symmetry identity. -/
theorem strip_zero_unit_mass_eigendata (s : ℂ) (hz : riemannZeta s = 0)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    ∃ v : domain, v ≠ 0 ∧ spectralOnDomain v = spectralParam s • v ∧
      scalarForm.η (v : Coeff) (v : Coeff) = 1 := by
  let hξ := xi_zero_of_strip_zero hz hpos hlt
  refine ⟨normalizedZeroState s hξ, ?_, normalizedZeroState_eigen s hξ,
    normalizedZeroState_mass s hξ⟩
  intro heq
  have hm := normalizedZeroState_mass s hξ
  have hc : (normalizedZeroState s hξ : Coeff) = 0 := congrArg Subtype.val heq
  rw [hc] at hm
  simpa [scalarForm, pairing] using! hm

end Reinmann.XiAnnihilator
