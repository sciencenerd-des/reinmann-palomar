/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile025Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((213/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7270400/114024027), (-1022720/38008009)), 0, by norm_num⟩
  | 1 => ⟨((-21722555187200/13001478733296729), (7435583488000/4333826244432243)), 0, by norm_num⟩
  | 2 => ⟨((2123928887/70368744177664), (-5430858231/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((171322405/2251799813685248), (3227464705/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1476905469/36028797018963968), (-406969263/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((1454210561/576460752303423488), (1342822411/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-2061696905/18446744073709551616), (-1487716025/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2423578543/590295810358705651712), (-128740681/590295810358705651712)), (13/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-2417088943/18889465931478580854784), (2349518279/37778931862957161709568)), (5/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((3920255705/1208925819614629174706176), (-4478209691/1208925819614629174706176)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-1035708955/19342813113834066795298816), (3128207179/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-145079721/309485009821345068724781056), (-7274547709/1237940039285380274899124224)), (65/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((1861967335/19807040628566084398385987584), (3585795859/19807040628566084398385987584)), (3/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (7191/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (7191/1280)))⁻¹=value ((7270400/114024027), (-1022720/38008009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((7270400/114024027), (-1022720/38008009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44806083/16777216), (214390195/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((3635200/114024027), (-511360/38008009)), 0, by norm_num⟩
  | 2 => ⟨((-5430638796800/13001478733296729), (1858895872000/4333826244432243)), 0, by norm_num⟩
  | 3 => ⟨((1415952591/281474976710656), (-1810286077/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((171322405/18014398509481984), (3227464705/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-1181524375/288230376151711744), (-2604603283/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((3877894829/18446744073709551616), (3580859763/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-4712450069/590295810358705651712), (-850123443/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((2423578543/9444732965739290427392), (-128740681/9444732965739290427392)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-2148523505/302231454903657293676544), (522115173/151115727451828646838272)), (19/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((784051141/4835703278458516698824704), (-3582567753/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-1506485753/618970019642690137449562112), (4550119533/618970019642690137449562112)), (33/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-48359907/2475880078570760549798248448), (-4849698473/19807040628566084398385987584)), (11/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (153/20480)), 0, by norm_num⟩
  | 45 => ⟨((97326766913/4080638361600), (-611541/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-266272430965963/11491077626265600), (1991147203921/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((1622418245/68719476736), (-675450093/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-3343054975/137438953472), (1366245891/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((1716988971/68719476736), (-1403310263/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-880010061/34359738368), (1441461069/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3609202287/137438953472), (-739043835/68719476736)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-3704057115/137438953472), (757773321/68719476736)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3804588799/137438953472), (-1555144295/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-3910753729/137438953472), (1597094455/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((2011467493/68719476736), (-410354431/34359738368)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4141709929/137438953472), (1688252073/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((66682975/2147483648), (-217227925/17179869184)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-2200809715/68719476736), (1790391503/137438953472)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((2272100711/68719476736), (-230779981/17179869184)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4696324921/137438953472), (59552639/4294967296)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((2429490177/68719476736), (-984541675/68719476736)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-1258325091/34359738368), (254605557/17179869184)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5220585749/137438953472), (-2109433977/137438953472)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-1355584493/34359738368), (2187386963/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5640299495/137438953472), (-567830121/34359738368)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-1469126037/34359738368), (2361950007/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((3066670323/68719476736), (-307513729/17179869184)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-1603408365/34359738368), (641694707/34359738368)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((3360373431/68719476736), (-1341556577/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-3529360129/68719476736), (1405244139/68719476736)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3716223171/68719476736), (-1475276783/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-3923954389/68719476736), (48520375/2147483648)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((2078125987/34359738368), (-409646959/17179869184)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4417741791/68719476736), (1734587407/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((589285925/8589934592), (-460631859/17179869184)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5053433167/68719476736), (982390993/34359738368)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((2722526105/34359738368), (-2104398825/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-5902318747/68719476736), (2265356563/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((3221605681/34359738368), (-613237313/17179869184)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-221653713/2147483648), (334297353/8589934592)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((3943925041/34359738368), (-1469849667/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-2220662681/17179869184), (407922947/8589934592)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2540806665/17179869184), (-1833524923/34359738368)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-5936382443/34359738368), (2092246445/34359738368)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3567219233/17179869184), (-1217916355/17179869184)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-2233255075/8589934592), (728552387/8589934592)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((745654265/2147483648), (-56657585/536870912)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4477653213/8589934592), (1199532849/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((1115107097/1073741824), (-221711409/1073741824)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-437820639/4294967296), (1715121559/4294967296)), (1/4294967296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (7191/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (7191/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (7191/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((44806083/16777216), (214390195/536870912)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (7191/1280))) (z:=((-43/256), (7191/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((44806083/16777216), (214390195/536870912))) (r:=(1/1073741824)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((205/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2145757077/67108864), (1350235993/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((3907099173/2147483648), (443226519/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((106340355136000/13001478733296729), (-15506279547680/4333826244432243)), 0, by norm_num⟩
  | 3 => ⟨((-2537880169/35184372088832), (2741541345/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((351311235/562949953421312), (-4024005243/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((216219509/72057594037927936), (2907547175/72057594037927936)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-64378209/144115188075855872), (-980102961/1152921504606846976)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2804996157/147573952589676412928), (2258736439/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5924239347/9444732965739290427392), (-817938273/4722366482869645213696)), (201/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5382845829/302231454903657293676544), (-375493749/151115727451828646838272)), (35/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-4221688751/9671406556917033397649408), (2566410485/9671406556917033397649408)), (3/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((664374371/77371252455336267181195264), (-3743033707/309485009821345068724781056)), (505/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-113450503/1237940039285380274899124224), (1061459409/2475880078570760549798248448)), (671/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1252370325/67108864), (243305123/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2833357349/2147483648), (443226519/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((106340355136000/13001478733296729), (-15506279547680/4333826244432243)), 0, by norm_num⟩
  | 3 => ⟨((-2537880169/35184372088832), (2741541345/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((351311235/562949953421312), (-4024005243/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((216219509/72057594037927936), (2907547175/72057594037927936)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-64378209/144115188075855872), (-980102961/1152921504606846976)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2804996157/147573952589676412928), (2258736439/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5924239347/9444732965739290427392), (-817938273/4722366482869645213696)), (201/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5382845829/302231454903657293676544), (-375493749/151115727451828646838272)), (35/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-4221688751/9671406556917033397649408), (2566410485/9671406556917033397649408)), (3/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((664374371/77371252455336267181195264), (-3743033707/309485009821345068724781056)), (505/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-113450503/1237940039285380274899124224), (1061459409/2475880078570760549798248448)), (671/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((657019623/33554432), (243305123/16777216)), (5/134217728), by norm_num⟩
  | 1 => ⟨((2833357349/2147483648), (443226519/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((106340355136000/13001478733296729), (-15506279547680/4333826244432243)), 0, by norm_num⟩
  | 3 => ⟨((-2537880169/35184372088832), (2741541345/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((351311235/562949953421312), (-4024005243/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((216219509/72057594037927936), (2907547175/72057594037927936)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-64378209/144115188075855872), (-980102961/1152921504606846976)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2804996157/147573952589676412928), (2258736439/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5924239347/9444732965739290427392), (-817938273/4722366482869645213696)), (201/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5382845829/302231454903657293676544), (-375493749/151115727451828646838272)), (35/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-4221688751/9671406556917033397649408), (2566410485/9671406556917033397649408)), (3/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((664374371/77371252455336267181195264), (-3743033707/309485009821345068724781056)), (505/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-113450503/1237940039285380274899124224), (1061459409/2475880078570760549798248448)), (671/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((43445110374400/13001478733296729), (-14871166976000/4333826244432243)), 0, by norm_num⟩
  | 1 => ⟨((-2123928887/17592186044416), (5430858231/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-32122951/70368744177664), (-2420598529/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1476905469/4503599627370496), (406969263/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1817763201/72057594037927936), (-3357056027/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((3092545357/2305843009213693952), (2231574037/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-2120631225/36893488147419103232), (3520253/1152921504606846976)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((2417088943/1180591620717411303424), (-2349518279/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1102571917/18889465931478580854784), (2518992951/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((647318097/604462909807314587353088), (-1955129487/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((398969233/38685626227668133590597632), (2500625775/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-2792951003/1237940039285380274899124224), (-1344673447/309485009821345068724781056)), (21/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((1398861117/9903520314283042199192993792), (1160481881/9903520314283042199192993792)), (1/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2123928887/17592186044416), (-5430858231/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((32122951/35184372088832), (2420598529/70368744177664)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-553839551/562949953421312), (-1220907789/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((3635526403/36028797018963968), (3357056027/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-120802553/18014398509481984), (-1394733773/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((6361893675/18446744073709551616), (-10560759/576460752303423488)), (9/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-2114952825/147573952589676412928), (1027914247/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1102571917/2361183241434822606848), (-2518992951/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-728232859/75557863725914323419136), (2199520673/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-498711541/4835703278458516698824704), (-6251564437/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((960076907/38685626227668133590597632), (3697851979/77371252455336267181195264)), (11/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-4196583351/2475880078570760549798248448), (-3481445643/2475880078570760549798248448)), (17/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((3371772431/39614081257132168796771975168), (1017914029/39614081257132168796771975168)), (27/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-171322405/281474976710656), (-3227464705/140737488355328)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((1476905469/1125899906842624), (406969263/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-3635526403/18014398509481984), (-3357056027/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2577121131/144115188075855872), (1859645031/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-2650789031/2305843009213693952), (17601265/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((2114952825/36893488147419103232), (-1027914247/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-1286333903/590295810358705651712), (1469412555/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 7 => ⟨((1941954291/37778931862957161709568), (-5865388461/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((46754207/75557863725914323419136), (293042083/37778931862957161709568)), (17/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-1600128179/9671406556917033397649408), (-770385829/2417851639229258349412352)), (15/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((480858509/38685626227668133590597632), (3191325173/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-3371772431/4951760157141521099596496896), (-1017914029/4951760157141521099596496896)), (23/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1211904987/39614081257132168796771975168), (-516469243/158456325028528675187087900672)), (37/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1476905469/2251799813685248), (-406969263/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((1817763201/9007199254740992), (3357056027/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-3865681697/144115188075855872), (-1394733773/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((5301578063/2305843009213693952), (-17601265/144115188075855872)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-2643691031/18446744073709551616), (1284892809/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((3859001709/590295810358705651712), (-137757427/18446744073709551616)), (7/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-424802501/2361183241434822606848), (5132214903/9444732965739290427392)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-46754207/18889465931478580854784), (-293042083/9444732965739290427392)), (1/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1800144201/2417851639229258349412352), (3466736231/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-2404292545/38685626227668133590597632), (-1994578233/38685626227668133590597632)), (15/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((4636187093/1237940039285380274899124224), (699815895/618970019642690137449562112)), (7/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-3635714961/19807040628566084398385987584), (96837983/4951760157141521099596496896)), (49/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((2361574253/316912650057057350374175801344), (-1306967459/316912650057057350374175801344)), (43/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1454210561/18014398509481984), (-1342822411/18014398509481984)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((3092545357/144115188075855872), (2231574037/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 2 => ⟨((-6361893675/2305843009213693952), (337944289/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((2114952825/9223372036854775808), (-2055828495/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-3859001709/295147905179352825856), (4408237665/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((2039052005/4722366482869645213696), (-6158657883/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((261823559/37778931862957161709568), (6564142659/75557863725914323419136)), (23/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1440115361/604462909807314587353088), (-5546777969/1208925819614629174706176)), (13/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((4327726581/19342813113834066795298816), (3590240819/19342813113834066795298816)), (27/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-4636187093/309485009821345068724781056), (-1399631791/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((3999286457/4951760157141521099596496896), (-426087125/4951760157141521099596496896)), (13/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-177118069/4951760157141521099596496896), (1568360951/79228162514264337593543950336)), (25/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((3139173759/2535301200456458802993406410752), (-499392441/316912650057057350374175801344)), (11/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2061696905/288230376151711744), (-1487716025/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((2120631225/1152921504606846976), (-3520253/36028797018963968)), (5/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-2114952825/9223372036854775808), (2055828495/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 3 => ⟨((1286333903/73786976294838206464), (-1469412555/73786976294838206464)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-424802501/590295810358705651712), (5132214903/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-261823559/18889465931478580854784), (-6564142659/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((420033647/75557863725914323419136), (1617810241/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-1442575527/2417851639229258349412352), (-2393493879/4835703278458516698824704)), (19/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((3477140319/77371252455336267181195264), (1049723843/77371252455336267181195264)), (21/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-1666369357/618970019642690137449562112), (88768151/309485009821345068724781056)), (11/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((5195463357/39614081257132168796771975168), (-2875328409/39614081257132168796771975168)), (45/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-3139173759/633825300114114700748351602688), (499392441/79228162514264337593543950336)), (11/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((2171689/19807040628566084398385987584), (-2035242087/5070602400912917605986812821504)), (21/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2423578543/4611686018427387904), (128740681/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 1 => ⟨((2417088943/18446744073709551616), (-2349518279/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-1102571917/73786976294838206464), (2518992951/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 3 => ⟨((970977145/1180591620717411303424), (-5865388461/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((46754207/2361183241434822606848), (293042083/1180591620717411303424)), (5/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-1440115361/151115727451828646838272), (-5546777969/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((1442575527/1208925819614629174706176), (2393493879/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-3973874651/38685626227668133590597632), (-149960549/4835703278458516698824704)), (13/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((4284949775/618970019642690137449562112), (-7133155/9671406556917033397649408)), (31/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-1855522627/4951760157141521099596496896), (1026903003/4951760157141521099596496896)), (17/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((616623417/39614081257132168796771975168), (-392379775/19807040628566084398385987584)), (9/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-953061229/2535301200456458802993406410752), (3488986435/2535301200456458802993406410752)), (37/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-838852591/81129638414606681695789005144064), (-6285446663/81129638414606681695789005144064)), (9/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2417088943/73786976294838206464), (2349518279/147573952589676412928)), (5/36893488147419103232), by norm_num⟩
  | 1 => ⟨((1102571917/147573952589676412928), (-2518992951/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-728232859/1180591620717411303424), (4399041345/2361183241434822606848)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-46754207/2361183241434822606848), (-293042083/1180591620717411303424)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1800144201/151115727451828646838272), (1733368115/75557863725914323419136)), (11/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-4327726581/2417851639229258349412352), (-3590240819/2417851639229258349412352)), (35/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((3477140319/19342813113834066795298816), (1049723843/19342813113834066795298816)), (13/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-4284949775/309485009821345068724781056), (7133155/4835703278458516698824704)), (17/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((4174925911/4951760157141521099596496896), (-1155265879/2475880078570760549798248448)), (43/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-770779271/19807040628566084398385987584), (1961898875/39614081257132168796771975168)), (49/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((1310459191/1267650600228229401496703205376), (-1199339087/316912650057057350374175801344)), (55/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((157284861/5070602400912917605986812821504), (4714084997/20282409603651670423947251286016)), (29/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-2226157993/324518553658426726783156020576256), (-945501983/81129638414606681695789005144064)), (15/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3920255705/2361183241434822606848), (4478209691/2361183241434822606848)), (15/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((647318097/2361183241434822606848), (-1955129487/2361183241434822606848)), (25/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((124677885/9444732965739290427392), (6251564437/37778931862957161709568)), (43/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-1600128179/151115727451828646838272), (-770385829/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((2404292545/1208925819614629174706176), (1994578233/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-1159046773/4835703278458516698824704), (-699815895/9671406556917033397649408)), (5/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((1666369357/77371252455336267181195264), (-88768151/38685626227668133590597632)), (61/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-1855522627/1237940039285380274899124224), (1026903003/1237940039285380274899124224)), (43/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((770779271/9903520314283042199192993792), (-1961898875/19807040628566084398385987584)), (55/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-1456065767/633825300114114700748351602688), (2665197971/316912650057057350374175801344)), (17/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-768948209/10141204801825835211973625643008), (-5761659441/10141204801825835211973625643008)), (79/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((1484105329/81129638414606681695789005144064), (2521338621/81129638414606681695789005144064)), (87/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-4549264615/2596148429267413814265248164610048), (-3383275489/2596148429267413814265248164610048)), (93/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1035708955/18889465931478580854784), (3128207179/18889465931478580854784)), (11/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-24935577/4722366482869645213696), (-2500625775/37778931862957161709568)), (41/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((960076907/151115727451828646838272), (3697851979/302231454903657293676544)), (19/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-480858509/302231454903657293676544), (-3191325173/2417851639229258349412352)), (47/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((4636187093/19342813113834066795298816), (1399631791/19342813113834066795298816)), (49/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-3999286457/154742504910672534362390528), (426087125/154742504910672534362390528)), (11/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((1298865839/618970019642690137449562112), (-2875328409/2475880078570760549798248448)), (35/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-2466493667/19807040628566084398385987584), (3139038199/19807040628566084398385987584)), (13/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((655229595/158456325028528675187087900672), (-4797356347/316912650057057350374175801344)), (35/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((768948209/5070602400912917605986812821504), (5761659441/5070602400912917605986812821504)), (89/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-816257931/20282409603651670423947251286016), (-2773472483/40564819207303340847894502572032)), (27/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((2729558769/649037107316853453566312041152512), (2029965293/649037107316853453566312041152512)), (63/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-3353745391/10384593717069655257060992658440192), (-1642304225/20769187434139310514121985316880384)), (69/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1817600/342072081), (-255680/114024027)), 0, by norm_num⟩
  | 1 => ⟨((-5430638796800/39004436199890187), (1858895872000/13001478733296729)), 0, by norm_num⟩
  | 2 => ⟨((1415952591/562949953421312), (-1810286077/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((114214937/18014398509481984), (4303286273/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-492301823/144115188075855872), (-135656421/18014398509481984)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((3877894829/18446744073709551616), (3580859763/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-5497858413/590295810358705651712), (-1983621367/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((6462876115/18889465931478580854784), (-343308483/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-3222785257/302231454903657293676544), (1566345519/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((2613503803/9671406556917033397649408), (-2985473127/9671406556917033397649408)), (21/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-1380945273/309485009821345068724781056), (4170942905/309485009821345068724781056)), (15/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-48359907/1237940039285380274899124224), (-4849698473/9903520314283042199192993792)), (11/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2482623113/316912650057057350374175801344), (4781061145/316912650057057350374175801344)), (65/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1314395829/67108864), (1946140023/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((177066147/134217728), (443533557/2147483648)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((2248944435/274877906944), (-1970542893/549755813888)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2537657093/35184372088832), (2749946201/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((349388181/562949953421312), (-505120287/281474976710656)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((462735071/144115188075855872), (5843069817/144115188075855872)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-2103054707/4611686018427387904), (-1967954443/2305843009213693952)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2855487377/147573952589676412928), (2256054341/147573952589676412928)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-3012475693/4722366482869645213696), (-1586928249/9444732965739290427392)), (203/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5464517823/302231454903657293676544), (-844283533/302231454903657293676544)), (141/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4264843291/9671406556917033397649408), (2696752451/9671406556917033397649408)), (193/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((2645407507/309485009821345068724781056), (-121705837/9671406556917033397649408)), (507/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-207505513/2475880078570760549798248448), (4395245797/9903520314283042199192993792)), (337/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1510349431/4503599627370496), (3861943631/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-182743899/72057594037927936), (-3442629019/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((787682917/288230376151711744), (1736402189/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-646315805/2305843009213693952), (-2387239841/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((1374464603/73786976294838206464), (991810683/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-141375415/147573952589676412928), (120157969/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((3007932907/75557863725914323419136), (-1461922485/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-784051141/604462909807314587353088), (3582567753/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((1035708955/38685626227668133590597632), (-6256414359/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((177319659/618970019642690137449562112), (4445556933/1237940039285380274899124224)), (19/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-170680339/2475880078570760549798248448), (-5259167259/39614081257132168796771975168)), (1/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((1492118525/316912650057057350374175801344), (2475694679/633825300114114700748351602688)), (13/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-299713105/1267650600228229401496703205376), (-90481247/1267650600228229401496703205376)), (5/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2628791613/134217728), (973070069/67108864)), (7/134217728), by norm_num⟩
  | 1 => ⟨((5666116693/4294967296), (55441669/268435456)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((1124472593/137438953472), (-1970539581/549755813888)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2537666955/35184372088832), (1374968547/17592186044416)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1397594669/2251799813685248), (-2020473581/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((462597009/144115188075855872), (5843077151/144115188075855872)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2102871117/4611686018427387904), (-3935998115/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((1427647979/73786976294838206464), (564068251/36893488147419103232)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-6024698527/9444732965739290427392), (-1587691971/9444732965739290427392)), (51/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5464604405/302231454903657293676544), (-52699887/18889465931478580854784)), (283/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-4265510011/9671406556917033397649408), (2695468475/9671406556917033397649408)), (387/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1323432327/154742504910672534362390528), (-3893377949/309485009821345068724781056)), (127/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-832363561/9903520314283042199192993792), (137329341/309485009821345068724781056)), (675/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2400557461/4611686018427387904), (-5291892385/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((369323317/2305843009213693952), (341034263/2305843009213693952)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-3141633379/147573952589676412928), (-2266995847/295147905179352825856)), (9/295147905179352825856), by norm_num⟩
  | 3 => ⟨((4308584077/2361183241434822606848), (-114436161/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-4297047009/37778931862957161709568), (2088460693/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((784051141/151115727451828646838272), (-447820969/75557863725914323419136)), (13/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1380945273/9671406556917033397649408), (4170942905/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-607953117/309485009821345068724781056), (-7620954743/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((1462974335/2475880078570760549798248448), (352176379/309485009821345068724781056)), (27/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-1953964735/39614081257132168796771975168), (-405247641/9903520314283042199192993792)), (25/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((3767821891/1267650600228229401496703205376), (568739267/633825300114114700748351602688)), (3/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-1477369889/10141204801825835211973625643008), (629600601/40564819207303340847894502572032)), (41/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((1919247647/324518553658426726783156020576256), (-2124340759/649037107316853453566312041152512)), (9/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2628791613/134217728), (973070069/67108864)), (1/16777216), by norm_num⟩
  | 1 => ⟨((2833058347/2147483648), (887066705/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((562236295/68719476736), (-1970539585/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-2537666891/35184372088832), (2749937091/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((1397594413/2251799813685248), (-2020473519/1125899906842624)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((462597757/144115188075855872), (5843076297/144115188075855872)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2102871775/4611686018427387904), (-1967998063/2305843009213693952)), (65/4611686018427387904), by norm_num⟩
  | 7 => ⟨((713823917/36893488147419103232), (1128134685/73786976294838206464)), (41/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-3012346473/4722366482869645213696), (-1587681223/9444732965739290427392)), (205/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5464589497/302231454903657293676544), (-843210559/302231454903657293676544)), (71/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-4265481265/9671406556917033397649408), (2695477153/9671406556917033397649408)), (97/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((165426223/19342813113834066795298816), (-1946686573/154742504910672534362390528)), (509/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-416152495/4951760157141521099596496896), (4394506497/9903520314283042199192993792)), (169/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2513306703/590295810358705651712), (906798339/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-5170300891/4722366482869645213696), (137323393/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((5156456411/37778931862957161709568), (-19579319/295147905179352825856)), (17/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-784051141/75557863725914323419136), (3582567753/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((1035708955/2417851639229258349412352), (-3128207179/2417851639229258349412352)), (23/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((159587693/19342813113834066795298816), (500125155/4835703278458516698824704)), (1/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((-2048164069/618970019642690137449562112), (-3944375445/618970019642690137449562112)), (5/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((3517136523/9903520314283042199192993792), (1458891507/4951760157141521099596496896)), (3/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-4238799627/158456325028528675187087900672), (-1279663351/158456325028528675187087900672)), (27/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((2031383597/1267650600228229401496703205376), (-108212603/633825300114114700748351602688)), (7/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-1583379309/20282409603651670423947251286016), (1752581125/40564819207303340847894502572032)), (29/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((478350287/162259276829213363391578010288128), (-2435132665/649037107316853453566312041152512)), (7/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-338866215/5192296858534827628530496329220096), (4962114041/20769187434139310514121985316880384)), (13/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2628791613/134217728), (973070069/67108864)), (9/134217728), by norm_num⟩
  | 1 => ⟨((2833058347/2147483648), (887066705/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((562236295/68719476736), (-1970539585/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2537666891/35184372088832), (2749937091/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((698797207/1125899906842624), (-4040947041/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((231298879/72057594037927936), (730384539/18014398509481984)), (45/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1051435895/2305843009213693952), (-3935996155/4611686018427387904)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((356911965/18446744073709551616), (2256269413/147573952589676412928)), (83/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-6024693199/9444732965739290427392), (-1587681299/9444732965739290427392)), (103/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5464589981/302231454903657293676544), (-843210611/302231454903657293676544)), (285/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1066370505/2417851639229258349412352), (2695477571/9671406556917033397649408)), (389/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((20678285/2417851639229258349412352), (-3893374307/309485009821345068724781056)), (255/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-208076409/2475880078570760549798248448), (4394508863/9903520314283042199192993792)), (677/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-520854183/18889465931478580854784), (2025174005/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((3801460077/604462909807314587353088), (-4342506367/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-627702397/1208925819614629174706176), (3791766277/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-80599845/4835703278458516698824704), (-2020707697/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((775819723/77371252455336267181195264), (2988163215/154742504910672534362390528)), (5/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-466287039/309485009821345068724781056), (-3094618349/2475880078570760549798248448)), (31/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((5994262099/39614081257132168796771975168), (1809624941/39614081257132168796771975168)), (23/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-1846712361/158456325028528675187087900672), (787000751/633825300114114700748351602688)), (59/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((3598589337/5070602400912917605986812821504), (-1991569461/5070602400912917605986812821504)), (19/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((-1328750797/40564819207303340847894502572032), (845532175/20282409603651670423947251286016)), (43/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((564777025/649037107316853453566312041152512), (-2067547517/649037107316853453566312041152512)), (3/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((16946517/649037107316853453566312041152512), (4063319055/20769187434139310514121985316880384)), (51/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((-1918843253/332306998946228968225951765070086144), (-3259912561/332306998946228968225951765070086144)), (53/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2628791613/134217728), (973070069/67108864)), (5/67108864), by norm_num⟩
  | 1 => ⟨((2833058347/2147483648), (887066705/4294967296)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((562236295/68719476736), (-1970539585/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2537666891/35184372088832), (2749937091/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((698797207/1125899906842624), (-4040947041/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((231298879/72057594037927936), (730384539/18014398509481984)), (23/72057594037927936), by norm_num⟩
  | 6 => ⟨((-2102871789/4611686018427387904), (-3935996155/4611686018427387904)), (67/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1427647859/73786976294838206464), (2256269413/147573952589676412928)), (21/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-753086649/1180591620717411303424), (-1587681303/9444732965739290427392)), (207/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5464589971/302231454903657293676544), (-421605299/151115727451828646838272)), (143/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1066370503/2417851639229258349412352), (673869385/2417851639229258349412352)), (195/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((330852561/38685626227668133590597632), (-1946687123/154742504910672534362390528)), (511/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-832305693/9903520314283042199192993792), (2197254383/4951760157141521099596496896)), (339/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2033663795/19342813113834066795298816), (-6142383585/19342813113834066795298816)), (11/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((97924383/9671406556917033397649408), (306881103/2417851639229258349412352)), (41/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((-29455573/2417851639229258349412352), (-1815227061/77371252455336267181195264)), (19/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((3776754215/1237940039285380274899124224), (391644923/154742504910672534362390528)), (47/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-4551686935/9903520314283042199192993792), (-1374121797/9903520314283042199192993792)), (49/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((3926394589/79228162514264337593543950336), (-26145073/4951760157141521099596496896)), (11/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-5100769707/1267650600228229401496703205376), (1411461023/633825300114114700748351602688)), (69/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((2421538815/10141204801825835211973625643008), (-770456351/2535301200456458802993406410752)), (13/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-1286574475/162259276829213363391578010288128), (4709918683/162259276829213363391578010288128)), (35/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-754933191/2596148429267413814265248164610048), (-5656646179/2596148429267413814265248164610048)), (11/324518553658426726783156020576256), by norm_num⟩
  | 10 => ⟨((200345159/2596148429267413814265248164610048), (340365321/2596148429267413814265248164610048)), (27/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-2679809235/332306998946228968225951765070086144), (-1992966703/332306998946228968225951765070086144)), (63/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((6585238591/10633823966279326983230456482242756608), (806185615/5316911983139663491615228241121378304)), (17/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2628791613/134217728), (973070069/67108864)), (11/134217728), by norm_num⟩
  | 1 => ⟨((2833058347/2147483648), (887066705/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((562236295/68719476736), (-1970539585/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2537666891/35184372088832), (2749937091/35184372088832)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((698797207/1125899906842624), (-4040947041/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((231298879/72057594037927936), (730384539/18014398509481984)), (47/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2102871789/4611686018427387904), (-3935996155/4611686018427387904)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1427647859/73786976294838206464), (2256269413/147573952589676412928)), (85/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-753086649/1180591620717411303424), (-1587681303/9444732965739290427392)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((5464589971/302231454903657293676544), (-843210599/302231454903657293676544)), (287/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-4265482011/9671406556917033397649408), (2695477541/9671406556917033397649408)), (391/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1323410243/154742504910672534362390528), (-486671781/38685626227668133590597632)), (1/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-832305687/9903520314283042199192993792), (137328399/309485009821345068724781056)), (679/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-477258232180105/4194304), (39300277774771/131072)), (156662781/2097152), by norm_num⟩
  | 1 => ⟨((-848162387/4), (2976463001/8)), 115, by norm_num⟩
  | 2 => ⟨((-2850316347/16), (905527307/4)), (715/8), by norm_num⟩
  | 3 => ⟨((-1507311595/16), (1436674389/16)), (1495/32), by norm_num⟩
  | 4 => ⟨((-4613091385/128), (3323311829/128)), (2365/128), by norm_num⟩
  | 5 => ⟨((-5510961037/512), (2955761317/512)), (755/128), by norm_num⟩
  | 6 => ⟨((-2695734629/1024), (515104877/512)), (3243/2048), by norm_num⟩
  | 7 => ⟨((-1115703741/2048), (1102353929/8192)), (753/2048), by norm_num⟩
  | 8 => ⟨((-1600098597/16384), (396800695/32768)), (4939/65536), by norm_num⟩
  | 9 => ⟨((-4047151761/262144), (33838881/262144)), (7265/524288), by norm_num⟩
  | 10 => ⟨((-4575865391/2097152), (-473434747/2097152)), (4853/2097152), by norm_num⟩
  | 11 => ⟨((-4676087489/16777216), (-1002723593/16777216)), (5951/16777216), by norm_num⟩
  | 12 => ⟨((-4356979319/134217728), (-1425832351/134217728)), (211/4194304), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((201186093734561/1267650600228229401496703205376), (2518603972845/10141204801825835211973625643008)), (53379/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((906376317828743/316912650057057350374175801344), (1543594387507/316912650057057350374175801344)), (65631/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((482003170431107/9903520314283042199192993792), (3481864279751/39614081257132168796771975168)), (148091/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1930216512678863/2475880078570760549798248448), (926761433093/618970019642690137449562112)), (78851/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1811924112984371/154742504910672534362390528), (928878504331/38685626227668133590597632)), (79049/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1587785032689785/9671406556917033397649408), (3492317836185/9671406556917033397649408)), (148639/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((646142730123757/302231454903657293676544), (3064832303615/604462909807314587353088)), (130483/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((30348550693127/1180591620717411303424), (4997394780815/75557863725914323419136)), (212833/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((669249317664177/2361183241434822606848), (470378006707/590295810358705651712)), (160327/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((419471415292665/147573952589676412928), (2599310797089/295147905179352825856)), (221597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1894200261086215/73786976294838206464), (3267595557323/36893488147419103232)), (34841/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1902470102174885/9223372036854775808), (231350154653/288230376151711744)), (315969/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1674028911553081/1152921504606846976), (7467639919487/1152921504606846976)), (318997/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1264969922843159/144115188075855872), (3303712753255/72057594037927936)), (282567/144115188075855872), by norm_num⟩
  | 4 => ⟨((1597930170778727/36028797018963968), (2514879648237/9007199254740992)), (430839/36028797018963968), by norm_num⟩
  | 3 => ⟨((1623378189146235/9007199254740992), (12838395654189/9007199254740992)), (551003/9007199254740992), by norm_num⟩
  | 2 => ⟨((312501051656081/562949953421312), (6621602086165/1125899906842624)), (570141/2251799813685248), by norm_num⟩
  | 1 => ⟨((82310641806109/70368744177664), (20908351690087/1125899906842624)), (226173/281474976710656), by norm_num⟩
  | 0 => ⟨((1528302791893249/1125899906842624), (46185591918491/1125899906842624)), (1008721/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1528302791893249/1125899906842624), (46185591918491/1125899906842624)), (3847965242625999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((518158030883917/281474976710656), (62692579194021/562949953421312)), (2821245/562949953421312), by norm_num⟩
  | 2 => ⟨((1900738447332619/562949953421312), (115408707963411/281474976710656)), (1376931/70368744177664), by norm_num⟩
  | 3 => ⟨((1580748849893467/140737488355328), (194832388785071/70368744177664)), (5213617/35184372088832), by norm_num⟩
  | 4 => ⟨((1042245528797605/8796093022208), (547084288083251/8796093022208)), (36496965/8796093022208), by norm_num⟩
  | 5 => ⟨((698973789098149/68719476736), (253217959103131/17179869184)), (51519425/34359738368), by norm_num⟩
  | 6 => ⟨((-477258232180105/4194304), (39300277774771/131072)), (156662781/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2628791613/134217728), (973070069/67108864)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((716800/18177627), (-1022720/6059209)), 0, by norm_num⟩
  | 1 => ⟨((4449901772800/330426123351129), (733085696000/110142041117043)), 0, by norm_num⟩
  | 2 => ⟨((-1819111771/2199023255552), (4421425739/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-602815921/8796093022208), (-197109473/2199023255552)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((2509592307/281474976710656), (-2261036013/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((734852513/4503599627370496), (58521019/70368744177664)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2644582961/36028797018963968), (-94625853/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((240511517/144115188075855872), (-3541133657/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((4478107079/9223372036854775808), (2416155143/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 9 => ⟨((-73050361/2305843009213693952), (1321145935/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-2830457139/1180591620717411303424), (-1995015317/590295810358705651712)), (25/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3140327187/9444732965739290427392), (-640814273/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((739922725/151115727451828646838272), (2322348809/75557863725914323419136)), (19/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (7191/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (7191/1280)))⁻¹=value ((716800/18177627), (-1022720/6059209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((716800/18177627), (-1022720/6059209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3788800/60472081), (-9204480/60472081)), 0, by norm_num⟩
  | 1 => ⟨((35183723315200/3656872580470561), (34873933824000/3656872580470561)), 0, by norm_num⟩
  | 2 => ⟨((-2258802791/2199023255552), (1906456393/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-14275537/17592186044416), (-6456585109/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((493168551/70368744177664), (1583349783/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-976386027/2251799813685248), (2005281403/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-731505159/36028797018963968), (-3382964313/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((2426341561/576460752303423488), (-85841137/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-2327781349/18446744073709551616), (1488014267/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-380060447/18446744073709551616), (-1454461959/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 10 => ⟨((5066128443/2361183241434822606848), (-1122153499/1180591620717411303424)), (17/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((6048789/1180591620717411303424), (1823463237/9444732965739290427392)), (59/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-35072739/2361183241434822606848), (-106881221/18889465931478580854784)), (51/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (7191/1280)))⁻¹=value ((3788800/60472081), (-9204480/60472081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3788800/60472081), (-9204480/60472081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25525005516800/1099238932331787), (-6074138624000/366412977443929)), 0, by norm_num⟩
  | 1 => ⟨((2114306171/549755813888), (-1583695425/549755813888)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((879382041/4398046511104), (5029938693/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-4765425221/70368744177664), (74540987/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((536918103/281474976710656), (-3844385797/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((2687624569/4503599627370496), (1740063813/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-956538901/18014398509481984), (3193712609/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-732147747/288230376151711744), (-3498213089/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((5641997755/9223372036854775808), (-559873393/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-204342441/18446744073709551616), (2048376915/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-5363521361/1180591620717411303424), (-1433938567/590295810358705651712)), (33/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3091936875/9444732965739290427392), (-388136473/1180591620717411303424)), (15/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1492289011/75557863725914323419136), (5499747387/151115727451828646838272)), (55/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((53/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5427200/69688081), (-9204480/69688081)), 0, by norm_num⟩
  | 1 => ⟨((27633976115200/4856428633462561), (49954553856000/4856428633462561)), 0, by norm_num⟩
  | 2 => ⟨((-7924247875/8796093022208), (-54440225/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((2583561107/70368744177664), (-4118738705/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((2742431113/1125899906842624), (5296005237/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-7304628913/18014398509481984), (-200885273/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((1243879021/72057594037927936), (-3734057285/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((1197822919/1152921504606846976), (154847121/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((-3364181625/18446744073709551616), (-555812377/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((2389627399/295147905179352825856), (-3381615863/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1042188535/2361183241434822606848), (4631837483/4722366482869645213696)), (43/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-6192850879/75557863725914323419136), (-170826955/18889465931478580854784)), (73/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1145083431/302231454903657293676544), (-3058974969/604462909807314587353088)), (31/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (7191/1280)))⁻¹=value ((5427200/69688081), (-9204480/69688081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5427200/69688081), (-9204480/69688081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4395775335/1099511627776), (1952722125/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-187302087/4398046511104), (-2343056661/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((5739454743/35184372088832), (1998530013/35184372088832)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-2124761967/140737488355328), (1243464189/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1500296645/1125899906842624), (-5559465925/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((2814239395/9007199254740992), (-182830113/4503599627370496)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((-559633133/72057594037927936), (588706035/18014398509481984)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((-822931399/288230376151711744), (-2216515553/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((2561898809/9223372036854775808), (-918713755/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 9 => ⟨((650139437/73786976294838206464), (4705811823/147573952589676412928)), (3/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-7375491315/2361183241434822606848), (-587764265/2361183241434822606848)), (45/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((567360051/4722366482869645213696), (-2506984249/9444732965739290427392)), (11/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((2900887517/151115727451828646838272), (1397513353/75557863725914323419136)), (41/151115727451828646838272), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((69/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2355200/27393627), (-1022720/9131209)), 0, by norm_num⟩
  | 1 => ⟨((1933319372800/750410800215129), (2408710144000/250136933405043)), 0, by norm_num⟩
  | 2 => ⟨((-2858822499/4398046511104), (-593027759/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((23664507/549755813888), (-872893083/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-519152435/1125899906842624), (3914868749/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-3150728711/18014398509481984), (-24670751/140737488355328)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((4996608625/288230376151711744), (-325558503/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 7 => ⟨((-2853300581/4611686018427387904), (2462456759/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-612575263/18446744073709551616), (-1486005415/18446744073709551616)), (41/73786976294838206464), by norm_num⟩
  | 9 => ⟨((3505656047/590295810358705651712), (946416353/590295810358705651712)), (17/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1629616687/4722366482869645213696), (2490189083/9444732965739290427392)), (55/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((10468977/151115727451828646838272), (-1158279829/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((4144174067/2417851639229258349412352), (3196084435/2417851639229258349412352)), (35/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (7191/1280)))⁻¹=value ((2355200/27393627), (-1022720/9131209)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((2355200/27393627), (-1022720/9131209))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-636887719/4398046511104), (5281810459/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-2645905961/17592186044416), (-2124439825/17592186044416)), (3/17592186044416), by norm_num⟩
  | 2 => ⟨((4730900755/140737488355328), (-2338822783/140737488355328)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((93873997/562949953421312), (817274081/140737488355328)), (9/1125899906842624), by norm_num⟩
  | 4 => ⟨((-3258183629/4503599627370496), (-683007923/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((2536505561/36028797018963968), (-2376483825/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((527449979/144115188075855872), (6028446081/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1387860555/1152921504606846976), (-415540319/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 8 => ⟨((269149525/4611686018427387904), (-515482253/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1192375785/147573952589676412928), (2900775871/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-2819654277/2361183241434822606848), (211586195/590295810358705651712)), (23/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((112030477/9444732965739290427392), (-2239562911/18889465931478580854784)), (45/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((93046905/9444732965739290427392), (1571953473/302231454903657293676544)), (43/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((85/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((512000/5761793), (-541440/5761793)), 0, by norm_num⟩
  | 1 => ⟨((15506636800/33198258574849), (277217280000/33198258574849)), 0, by norm_num⟩
  | 2 => ⟨((-3633646527/8796093022208), (-3070407857/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((4891350525/140737488355328), (-137232543/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-191534017/140737488355328), (2033689913/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-219791119/9007199254740992), (-5195279069/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((4530623173/576460752303423488), (3032345063/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-5500387779/9223372036854775808), (625152579/4611686018427387904)), (19/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1485116399/73786976294838206464), (-5023833657/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1665239001/2361183241434822606848), (1451078051/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-1386821487/9444732965739290427392), (-2874356429/37778931862957161709568)), (33/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((6104352517/604462909807314587353088), (-531727541/151115727451828646838272)), (97/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-685145839/2417851639229258349412352), (3050521691/4835703278458516698824704)), (9/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (7191/1280)))⁻¹=value ((512000/5761793), (-541440/5761793)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((512000/5761793), (-541440/5761793))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3065171457/70368744177664), (2356183173/35184372088832)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-2096614355/70368744177664), (348149253/140737488355328)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((370562525/140737488355328), (-3459543413/562949953421312)), (5/562949953421312), by norm_num⟩
  | 3 => ⟨((824463693/1125899906842624), (4040225731/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1508497917/9007199254740992), (1281834717/36028797018963968)), (7/18014398509481984), by norm_num⟩
  | 5 => ⟨((209943505/36028797018963968), (-3159986623/144115188075855872)), (19/288230376151711744), by norm_num⟩
  | 6 => ⟨((1198622915/576460752303423488), (2113729223/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-5422633821/18446744073709551616), (2238530313/18446744073709551616)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((150638327/73786976294838206464), (-2554552111/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1875669131/590295810358705651712), (257991041/147573952589676412928)), (17/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-2793294807/9444732965739290427392), (2037140469/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1070072637/151115727451828646838272), (-5308610335/151115727451828646838272)), (33/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((4024976357/1208925819614629174706176), (924247311/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((101/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10342400/116996881), (-9204480/116996881)), 0, by norm_num⟩
  | 1 => ⟨((-11121392844800/13688270163728161), (95196413952000/13688270163728161)), 0, by norm_num⟩
  | 2 => ⟨((-32663475/137438953472), (-373118659/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3357033369/140737488355328), (1590458809/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-2874569285/2251799813685248), (387620007/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((132128163/4503599627370496), (-5811382289/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((2162546199/1152921504606846976), (1360076885/288230376151711744)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-4953371005/18446744073709551616), (-2486269593/18446744073709551616)), (23/18446744073709551616), by norm_num⟩
  | 8 => ⟨((5067797527/295147905179352825856), (-1359298439/295147905179352825856)), (1/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-682096027/1180591620717411303424), (4150869571/4722366482869645213696)), (11/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-341498203/37778931862957161709568), (-1163164519/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((852828209/302231454903657293676544), (715113493/302231454903657293676544)), (81/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-1053193089/4835703278458516698824704), (62066667/9671406556917033397649408)), (109/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (7191/1280)))⁻¹=value ((10342400/116996881), (-9204480/116996881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10342400/116996881), (-9204480/116996881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2566773077/281474976710656), (1403378835/562949953421312)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((-3310504375/1125899906842624), (1582584183/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-1041878499/4503599627370496), (-1114987849/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 3 => ⟨((830872055/4503599627370496), (507687347/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 4 => ⟨((-3224912433/144115188075855872), (759734549/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 5 => ⟨((-605486589/576460752303423488), (-606582897/144115188075855872)), (19/1152921504606846976), by norm_num⟩
  | 6 => ⟨((2490471817/4611686018427387904), (660411945/4611686018427387904)), (25/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-847466601/18446744073709551616), (3598414133/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1435009215/590295810358705651712), (-530064089/73786976294838206464)), (35/590295810358705651712), by norm_num⟩
  | 9 => ⟨((119307007/147573952589676412928), (597124273/4722366482869645213696)), (39/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-1884502791/37778931862957161709568), (647411587/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-2346122359/604462909807314587353088), (-2278904557/302231454903657293676544)), (81/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((248621863/302231454903657293676544), (-132997073/9671406556917033397649408)), (79/4835703278458516698824704), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((117/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1331200/15480009), (-1022720/15480009)), 0, by norm_num⟩
  | 1 => ⟨((-121022873600/79876892880027), (1361444864000/239630678640081)), 0, by norm_num⟩
  | 2 => ⟨((-269450331/2199023255552), (-80906573/274877906944)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2109870491/140737488355328), (1211472985/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-4183622631/4503599627370496), (70425529/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1290188829/36028797018963968), (-2598798619/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-50203809/144115188075855872), (6303380893/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-173685065/2305843009213693952), (-4761016187/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 8 => ⟨((34595181/4611686018427387904), (903298109/295147905179352825856)), (23/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-2000629203/4722366482869645213696), (1097596573/9444732965739290427392)), (29/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((543144545/37778931862957161709568), (-2869914381/151115727451828646838272)), (37/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((22213301/2417851639229258349412352), (6245339191/4835703278458516698824704)), (91/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-3331457489/77371252455336267181195264), (-2136525775/38685626227668133590597632)), (7/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (7191/1280)))⁻¹=value ((1331200/15480009), (-1022720/15480009)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1331200/15480009), (-1022720/15480009))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4273403325/4503599627370496), (-1747803851/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 1 => ⟨((-428298847/4503599627370496), (4359861861/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((-1751390175/18014398509481984), (-211289097/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((3872222641/144115188075855872), (-469728351/72057594037927936)), (15/144115188075855872), by norm_num⟩
  | 4 => ⟨((-1696108249/1152921504606846976), (5141608959/1152921504606846976)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-2086625837/4611686018427387904), (-2457609829/4611686018427387904)), (17/4611686018427387904), by norm_num⟩
  | 6 => ⟨((6859235399/73786976294838206464), (-568034213/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-155587351/36893488147419103232), (3235346651/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-510274387/590295810358705651712), (-2521246525/2361183241434822606848)), (33/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5678868453/37778931862957161709568), (-951348939/37778931862957161709568)), (75/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-1629735513/302231454903657293676544), (2302794511/151115727451828646838272)), (5/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1334010169/1208925819614629174706176), (-2962699167/2417851639229258349412352)), (83/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((6102899691/38685626227668133590597632), (-1520177053/38685626227668133590597632)), (41/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((133/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13619200/164920081), (-9204480/164920081)), 0, by norm_num⟩
  | 1 => ⟨((-50380078284800/27198633117046561), (125357654016000/27198633117046561)), 0, by norm_num⟩
  | 2 => ⟨((-917172667/17592186044416), (-1064308925/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((313344491/35184372088832), (2403008617/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2729004485/4503599627370496), (-936567103/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((4023977113/144115188075855872), (-909115239/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1846590557/2305843009213693952), (749471635/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((-237196157/73786976294838206464), (-5610060035/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((332695127/147573952589676412928), (900087629/295147905179352825856)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1682940869/9444732965739290427392), (-1190181739/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((5510122987/604462909807314587353088), (-1433117705/604462909807314587353088)), (7/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-3000355729/9671406556917033397649408), (3407019111/9671406556917033397649408)), (63/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((230477827/77371252455336267181195264), (-7180941317/309485009821345068724781056)), (35/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (7191/1280)))⁻¹=value ((13619200/164920081), (-9204480/164920081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13619200/164920081), (-9204480/164920081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((255352221/4503599627370496), (-95710215/1125899906842624)), (11/36028797018963968), by norm_num⟩
  | 1 => ⟨((1382984723/72057594037927936), (3629721121/72057594037927936)), (9/36028797018963968), by norm_num⟩
  | 2 => ⟨((-2228550365/144115188075855872), (-1114537629/288230376151711744)), (11/144115188075855872), by norm_num⟩
  | 3 => ⟨((1499625399/576460752303423488), (-332876325/144115188075855872)), (21/1152921504606846976), by norm_num⟩
  | 4 => ⟨((194740567/2305843009213693952), (5703305671/9223372036854775808)), (9/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-1620552117/18446744073709551616), (-773477755/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 6 => ⟨((857024485/73786976294838206464), (-529786429/73786976294838206464)), (35/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-4628163/295147905179352825856), (519809971/295147905179352825856)), (91/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-847575055/4722366482869645213696), (-2136215409/18889465931478580854784)), (55/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1630133831/75557863725914323419136), (-408319277/37778931862957161709568)), (63/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-222469275/1208925819614629174706176), (3152516085/1208925819614629174706176)), (137/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-4346048097/19342813113834066795298816), (-737015327/4835703278458516698824704)), (145/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((3770292637/154742504910672534362390528), (-930517245/77371252455336267181195264)), (147/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((149/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15257600/193796881), (-9204480/193796881)), 0, by norm_num⟩
  | 1 => ⟨((-74035952844800/37557231085328161), (140438274048000/37557231085328161)), 0, by norm_num⟩
  | 2 => ⟨((-197047599/17592186044416), (-6826168083/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1420957327/281474976710656), (4149643699/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-420832931/1125899906842624), (-383445357/2251799813685248)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((2703237095/144115188075855872), (-626351699/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3167216253/4611686018427387904), (2448766231/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((532196365/36893488147419103232), (-5491512471/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 8 => ⟨((186446341/590295810358705651712), (4267629627/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-522817561/9444732965739290427392), (-601136809/9444732965739290427392)), (19/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((2230804605/604462909807314587353088), (1439739561/1208925819614629174706176)), (39/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-6714287847/38685626227668133590597632), (788447051/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((453719521/77371252455336267181195264), (-3544376863/618970019642690137449562112)), (41/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (7191/1280)))⁻¹=value ((15257600/193796881), (-9204480/193796881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15257600/193796881), (-9204480/193796881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((61459979/144115188075855872), (-2705221533/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 1 => ⟨((18508041/4503599627370496), (494868677/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-1895899107/1152921504606846976), (904907751/2305843009213693952)), (27/2305843009213693952), by norm_num⟩
  | 3 => ⟨((1388293755/9223372036854775808), (-829887013/2305843009213693952)), (13/4611686018427387904), by norm_num⟩
  | 4 => ⟨((44548833/1152921504606846976), (1151331669/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-7031125313/590295810358705651712), (-24643977/36893488147419103232)), (35/295147905179352825856), by norm_num⟩
  | 6 => ⟨((2498524303/2361183241434822606848), (-3243080797/2361183241434822606848)), (49/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((693022929/9444732965739290427392), (4129224055/18889465931478580854784)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-520999837/18889465931478580854784), (-1094328383/151115727451828646838272)), (79/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((46145985/18889465931478580854784), (-2714705207/1208925819614629174706176)), (23/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((643402947/9671406556917033397649408), (6972205499/19342813113834066795298816)), (51/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-5587300763/154742504910672534362390528), (-1078337255/77371252455336267181195264)), (219/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((3836829385/1237940039285380274899124224), (-2987035217/1237940039285380274899124224)), (227/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((165/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5632000/75316827), (-1022720/25105609)), 0, by norm_num⟩
  | 1 => ⟨((-11152909107200/5672624429347929), (5759959040000/1890874809782643)), 0, by norm_num⟩
  | 2 => ⟨((403349697/35184372088832), (-677031535/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((761915427/281474976710656), (26340291/4398046511104)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-2010354733/9007199254740992), (-3040649293/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((3396195567/288230376151711744), (508652003/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2197437145/4611686018427387904), (401256591/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2106031823/147573952589676412928), (-2392420061/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-960389623/4722366482869645213696), (132345939/147573952589676412928)), (19/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-805658811/75557863725914323419136), (-1423243363/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((704806491/604462909807314587353088), (2880529867/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-5250525415/77371252455336267181195264), (-1608842683/77371252455336267181195264)), (1/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((3665278773/1237940039285380274899124224), (-374336007/618970019642690137449562112)), (15/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (7191/1280)))⁻¹=value ((5632000/75316827), (-1022720/25105609)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5632000/75316827), (-1022720/25105609))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-808081551/2305843009213693952), (-414593827/576460752303423488)), (23/4611686018427387904), by norm_num⟩
  | 1 => ⟨((2190281049/4611686018427387904), (1006398543/9223372036854775808)), (5/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-2341988779/18446744073709551616), (14689457/144115188075855872)), (29/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-54249897/73786976294838206464), (-5820530653/147573952589676412928)), (59/147573952589676412928), by norm_num⟩
  | 4 => ⟨((3696891203/590295810358705651712), (1343740871/295147905179352825856)), (27/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-2939175439/2361183241434822606848), (1854064049/4722366482869645213696)), (21/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((582922849/9444732965739290427392), (-438817687/2361183241434822606848)), (15/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((599540933/37778931862957161709568), (1629243613/75557863725914323419136)), (5/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-8196575223/2417851639229258349412352), (59901855/604462909807314587353088)), (25/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((522089639/2417851639229258349412352), (-1645051617/4835703278458516698824704)), (119/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((358114669/19342813113834066795298816), (3200167453/77371252455336267181195264)), (135/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-5945118575/1237940039285380274899124224), (-916872275/1237940039285380274899124224)), (293/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((3249455047/9903520314283042199192993792), (-932948595/2475880078570760549798248448)), (77/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((181/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18534400/261380881), (-9204480/261380881)), 0, by norm_num⟩
  | 1 => ⟨((-129400765644800/68319964952336161), (170599514112000/68319964952336161)), 0, by norm_num⟩
  | 2 => ⟨((815781139/35184372088832), (-4288344407/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((745332751/562949953421312), (5324994325/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-2345768953/18014398509481984), (-2600795397/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((4126783201/576460752303423488), (814523195/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2799959205/9223372036854775808), (476943593/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((380292199/36893488147419103232), (-924079835/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2410370827/9444732965739290427392), (952750115/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((587433909/302231454903657293676544), (-1420468347/75557863725914323419136)), (31/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((633725845/2417851639229258349412352), (1694341795/2417851639229258349412352)), (27/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-836825199/38685626227668133590597632), (-3130511043/154742504910672534362390528)), (47/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((2780767677/2475880078570760549798248448), (1665736563/4951760157141521099596496896)), (5/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (7191/1280)))⁻¹=value ((18534400/261380881), (-9204480/261380881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18534400/261380881), (-9204480/261380881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1851201293/36893488147419103232), (-2852422349/73786976294838206464)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((5900004299/147573952589676412928), (-1254474319/147573952589676412928)), (9/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-985948769/147573952589676412928), (1874764243/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-842862981/590295810358705651712), (-985479479/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 4 => ⟨((6741936919/9444732965739290427392), (230844073/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-1949263447/18889465931478580854784), (730183635/9444732965739290427392)), (45/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((9775697/75557863725914323419136), (-1504337687/75557863725914323419136)), (33/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((674163049/302231454903657293676544), (2028984887/1208925819614629174706176)), (45/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-208861607/604462909807314587353088), (64179767/604462909807314587353088)), (57/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((530503207/38685626227668133590597632), (-3216709997/77371252455336267181195264)), (69/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((1866307955/618970019642690137449562112), (2473663633/618970019642690137449562112)), (159/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-5386414589/9903520314283042199192993792), (2166037/77371252455336267181195264)), (351/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((2280762701/79228162514264337593543950336), (-1934878213/39614081257132168796771975168)), (187/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((197/16), (7191/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((20172800/300088081), (-9204480/300088081)), 0, by norm_num⟩
  | 1 => ⟨((-161109703884800/90052856358262561), (185680134144000/90052856358262561)), 0, by norm_num⟩
  | 2 => ⟨((1003137899/35184372088832), (-3403772995/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((591498881/1125899906842624), (259580435/70368744177664)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-2674469987/36028797018963968), (-4176852999/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((4926410019/1152921504606846976), (3179957803/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-6859284333/36893488147419103232), (-501282429/18446744073709551616)), (15/36893488147419103232), by norm_num⟩
  | 7 => ⟨((3934819635/590295810358705651712), (-1143973595/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-3670743455/18889465931478580854784), (3161478135/18889465931478580854784)), (21/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((2396598287/604462909807314587353088), (-5201840767/604462909807314587353088)), (33/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-6209625/4835703278458516698824704), (6771085823/19342813113834066795298816)), (53/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-412034105/77371252455336267181195264), (-3647472705/309485009821345068724781056)), (21/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((3562720157/9903520314283042199192993792), (1557129453/4951760157141521099596496896)), (67/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (7191/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (7191/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (7191/1280)))⁻¹=value ((20172800/300088081), (-9204480/300088081)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20172800/300088081), (-9204480/300088081))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5382040687/1180591620717411303424), (-625487155/590295810358705651712)), (63/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((3065184327/1180591620717411303424), (-2162876521/1180591620717411303424)), (15/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-560202685/4722366482869645213696), (2739712081/2361183241434822606848)), (49/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-2004235989/9444732965739290427392), (-522944819/2361183241434822606848)), (55/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((4874423211/75557863725914323419136), (-344626965/75557863725914323419136)), (53/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-1007037981/151115727451828646838272), (1436351109/151115727451828646838272)), (11/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-316599453/604462909807314587353088), (-4265180225/2417851639229258349412352)), (131/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((2379998963/9671406556917033397649408), (1850392649/19342813113834066795298816)), (181/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-4597312069/154742504910672534362390528), (176934037/9671406556917033397649408)), (235/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((451395381/1237940039285380274899124224), (-1326437837/309485009821345068724781056)), (9/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((937726519/2475880078570760549798248448), (3226733027/9903520314283042199192993792)), (337/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-4233168749/79228162514264337593543950336), (1063382703/79228162514264337593543950336)), (189/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((1284789849/633825300114114700748351602688), (-1723025033/316912650057057350374175801344)), (51/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1839355173/2199023255552), (-1370340379/1099511627776)), (243/549755813888), by norm_num⟩
  | 1 => ⟨((3550906179/2199023255552), (-1065449581/2199023255552)), (283/274877906944), by norm_num⟩
  | 2 => ⟨((3732569499/4398046511104), (1511117011/4398046511104)), (5133/4398046511104), by norm_num⟩
  | 3 => ⟨((2829428971/17592186044416), (303475889/1099511627776)), (1941/2199023255552), by norm_num⟩
  | 4 => ⟨((-295432713/35184372088832), (5619484659/70368744177664)), (17771/35184372088832), by norm_num⟩
  | 5 => ⟨((-701072789/70368744177664), (3339972701/281474976710656)), (32901/140737488355328), by norm_num⟩
  | 6 => ⟨((-5109814887/2251799813685248), (888570803/1125899906842624)), (205511/2251799813685248), by norm_num⟩
  | 7 => ⟨((-5602747843/18014398509481984), (-45338007/1125899906842624)), (557229/18014398509481984), by norm_num⟩
  | 8 => ⟨((-2284421451/72057594037927936), (-2583276893/144115188075855872)), (167437/18014398509481984), by norm_num⟩
  | 9 => ⟨((-186761559/72057594037927936), (-1706929459/576460752303423488)), (725105/288230376151711744), by norm_num⟩
  | 10 => ⟨((-1398397991/9223372036854775808), (-211036537/576460752303423488)), (2863797/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-410527783/147573952589676412928), (-5354759813/147573952589676412928)), (5208861/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1453097311/2361183241434822606848), (-7102551389/2361183241434822606848)), (17593515/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1839355173/2199023255552), (-1370340379/1099511627776)), (973/2199023255552), by norm_num⟩
  | 1 => ⟨((3550906179/2199023255552), (-1065449581/2199023255552)), (2265/2199023255552), by norm_num⟩
  | 2 => ⟨((3732569499/4398046511104), (1511117011/4398046511104)), (2567/2199023255552), by norm_num⟩
  | 3 => ⟨((2829428971/17592186044416), (303475889/1099511627776)), (15529/17592186044416), by norm_num⟩
  | 4 => ⟨((-295432713/35184372088832), (5619484659/70368744177664)), (35545/70368744177664), by norm_num⟩
  | 5 => ⟨((-701072789/70368744177664), (3339972701/281474976710656)), (32907/140737488355328), by norm_num⟩
  | 6 => ⟨((-5109814887/2251799813685248), (888570803/1125899906842624)), (102801/1125899906842624), by norm_num⟩
  | 7 => ⟨((-5602747843/18014398509481984), (-45338007/1125899906842624)), (278975/9007199254740992), by norm_num⟩
  | 8 => ⟨((-2284421451/72057594037927936), (-2583276893/144115188075855872)), (1345261/144115188075855872), by norm_num⟩
  | 9 => ⟨((-186761559/72057594037927936), (-1706929459/576460752303423488)), (2946537/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-1398397991/9223372036854775808), (-211036537/576460752303423488)), (6096529/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-410527783/147573952589676412928), (-5354759813/147573952589676412928)), (26738403/147573952589676412928), by norm_num⟩
  | 12 => ⟨((1453097311/2361183241434822606848), (-7102551389/2361183241434822606848)), (82410695/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile025Gamma
