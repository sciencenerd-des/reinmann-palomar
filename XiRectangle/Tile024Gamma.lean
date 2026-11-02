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
namespace Reinmann.XiRectangle.Tile024Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/340828681), (-8843520/340828681)), 0, by norm_num⟩
  | 1 => ⟨((-200999009484800/116164189792199761), (193793359872000/116164189792199761)), 0, by norm_num⟩
  | 2 => ⟨((597808735/17592186044416), (-2676790097/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-237354319/2251799813685248), (3250035145/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-613589371/18014398509481984), (-424081059/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((1335447675/576460752303423488), (745155151/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3985021919/36893488147419103232), (-978697241/18446744073709551616)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((4912095227/1180591620717411303424), (359215717/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-5202304971/37778931862957161709568), (1669742241/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((4658520217/1208925819614629174706176), (-484681931/151115727451828646838272)), (25/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1591288471/19342813113834066795298816), (740352743/4835703278458516698824704)), (19/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((203775383/309485009821345068724781056), (-7414189831/1237940039285380274899124224)), (7/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1119758513/19807040628566084398385987584), (3982762401/19807040628566084398385987584)), (41/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (6909/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (6909/1280)))⁻¹=value ((21913600/340828681), (-8843520/340828681)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/340828681), (-8843520/340828681))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2865634281/1073741824), (411859685/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((10956800/340828681), (-4421760/340828681)), 0, by norm_num⟩
  | 2 => ⟨((-50249752371200/116164189792199761), (48448339968000/116164189792199761)), 0, by norm_num⟩
  | 3 => ⟨((1594156627/281474976710656), (-3569053463/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-237354319/18014398509481984), (3250035145/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-1963485987/576460752303423488), (-5428237555/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((445149225/2305843009213693952), (3974160805/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-4554310765/590295810358705651712), (-2237022265/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((4912095227/18889465931478580854784), (359215717/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-4624271085/604462909807314587353088), (1484215325/604462909807314587353088)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1863408087/9671406556917033397649408), (-1550982179/9671406556917033397649408)), (21/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-578650353/154742504910672534362390528), (1076876717/154742504910672534362390528)), (29/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((543401021/19807040628566084398385987584), (-4942793221/19807040628566084398385987584)), (19/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (147/20480)), 0, by norm_num⟩
  | 45 => ⟨((97690710713/4080638361600), (-292089/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-44789024836399/1915179604377600), (5729007103337/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((1637710389/68719476736), (-651135317/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-842601045/34359738368), (1318628491/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((3460282575/137438953472), (-676677593/68719476736)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-3547117317/137438953472), (1389373327/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((28416521/1073741824), (-1424576559/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-933243899/34359738368), (1460780489/137438953472)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3834208185/137438953472), (-374747935/34359738368)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-3941108355/137438953472), (1539411943/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((4054089301/137438953472), (-1582106531/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4173716987/137438953472), (1627225631/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((134394279/4294967296), (-418746201/34359738368)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4435475249/137438953472), (862815217/68719476736)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((4579062293/137438953472), (-444858603/34359738368)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-2366126201/68719476736), (1836701221/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4896041803/137438953472), (-1897775779/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-1267892395/34359738368), (981525377/68719476736)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5260143921/137438953472), (-1016487421/68719476736)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5463274747/137438953472), (2108062979/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5682714195/137438953472), (-2188909025/137438953472)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-1480126801/34359738368), (2276201499/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((1544763827/34359738368), (-592685807/34359738368)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-201912433/4294967296), (618369023/34359738368)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((846289561/17179869184), (-646378121/34359738368)), (1/68719476736), by norm_num⟩
  | 20 => ⟨((-1777617749/34359738368), (84630491/4294967296)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((1871644545/34359738368), (-1421526233/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-1976162601/34359738368), (748015441/34359738368)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4186059237/68719476736), (-197346671/8589934592)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-2224568947/34359738368), (835599653/34359738368)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((2373725087/34359738368), (-887556723/34359738368)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5088571835/68719476736), (473199639/17179869184)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5482415165/68719476736), (-2027184861/68719476736)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-1485550965/17179869184), (1091048523/34359738368)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1621494967/17179869184), (-590655915/17179869184)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-1784753587/17179869184), (1287843027/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((1984456303/17179869184), (-1415472541/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-2234301191/17179869184), (1571152585/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((5111630283/34359738368), (-220658243/4294967296)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-186554101/1073741824), (1007020195/17179869184)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3585956549/17179869184), (-146521145/2147483648)), (1/17179869184), by norm_num⟩
  | 4 => ⟨((-4487852905/17179869184), (1402044051/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((5989926939/17179869184), (-1744015807/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-2246076779/4294967296), (288356313/2147483648)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((1117227059/1073741824), (-852338813/4294967296)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-891281525/8589934592), (1647438741/4294967296)), (3/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (6909/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (6909/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (6909/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2865634281/1073741824), (411859685/1073741824)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (6909/1280))) (z:=((-21/128), (6909/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2865634281/1073741824), (411859685/1073741824))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2166997773/67108864), (2596300279/134217728)), (3/134217728), by norm_num⟩
  | 1 => ⟨((1952428979/1073741824), (425789935/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((958722799180800/116164189792199761), (-400989827108640/116164189792199761)), 0, by norm_num⟩
  | 3 => ⟨((-1318141413/17592186044416), (333597141/4398046511104)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1608991273/2251799813685248), (-3975307857/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((55552295/144115188075855872), (5878585927/144115188075855872)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1754139881/4611686018427387904), (-32153087/36028797018963968)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((325532091/18446744073709551616), (2550576813/147573952589676412928)), (33/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-361395911/590295810358705651712), (-2326826191/9444732965739290427392)), (87/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1380593661/75557863725914323419136), (-51750971/302231454903657293676544)), (235/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1157780227/2417851639229258349412352), (245357919/1208925819614629174706176)), (321/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1644531059/154742504910672534362390528), (-1666425395/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-839458931/4951760157141521099596496896), (2053684771/4951760157141521099596496896)), (581/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1269416717/67108864), (1871839121/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((1415558067/1073741824), (425789935/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((958722799180800/116164189792199761), (-400989827108640/116164189792199761)), 0, by norm_num⟩
  | 3 => ⟨((-1318141413/17592186044416), (333597141/4398046511104)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1608991273/2251799813685248), (-3975307857/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((55552295/144115188075855872), (5878585927/144115188075855872)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1754139881/4611686018427387904), (-32153087/36028797018963968)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((325532091/18446744073709551616), (2550576813/147573952589676412928)), (33/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-361395911/590295810358705651712), (-2326826191/9444732965739290427392)), (87/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1380593661/75557863725914323419136), (-51750971/302231454903657293676544)), (235/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1157780227/2417851639229258349412352), (245357919/1208925819614629174706176)), (321/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1644531059/154742504910672534362390528), (-1666425395/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-839458931/4951760157141521099596496896), (2053684771/4951760157141521099596496896)), (581/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((665542819/33554432), (1871839121/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((1415558067/1073741824), (425789935/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((958722799180800/116164189792199761), (-400989827108640/116164189792199761)), 0, by norm_num⟩
  | 3 => ⟨((-1318141413/17592186044416), (333597141/4398046511104)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1608991273/2251799813685248), (-3975307857/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((55552295/144115188075855872), (5878585927/144115188075855872)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1754139881/4611686018427387904), (-32153087/36028797018963968)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((325532091/18446744073709551616), (2550576813/147573952589676412928)), (33/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-361395911/590295810358705651712), (-2326826191/9444732965739290427392)), (87/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1380593661/75557863725914323419136), (-51750971/302231454903657293676544)), (235/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1157780227/2417851639229258349412352), (245357919/1208925819614629174706176)), (321/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1644531059/154742504910672534362390528), (-1666425395/154742504910672534362390528)), (217/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-839458931/4951760157141521099596496896), (2053684771/4951760157141521099596496896)), (581/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((401998018969600/116164189792199761), (-387586719744000/116164189792199761)), 0, by norm_num⟩
  | 1 => ⟨((-597808735/4398046511104), (2676790097/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((178015739/281474976710656), (-4875052717/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((613589371/2251799813685248), (424081059/562949953421312)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3338619187/144115188075855872), (-3725775755/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((2988766439/2305843009213693952), (734022931/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-4298083323/73786976294838206464), (-39289219/9223372036854775808)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((5202304971/2361183241434822606848), (-1669742241/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1310208811/18889465931478580854784), (2181068689/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1989110589/1208925819614629174706176), (-1850881857/604462909807314587353088)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-17511947/1208925819614629174706176), (1274313877/9671406556917033397649408)), (3/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1679637769/1237940039285380274899124224), (-5974143601/1237940039285380274899124224)), (9/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1139684791/9903520314283042199192993792), (2951226747/19807040628566084398385987584)), (7/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((597808735/4398046511104), (-2676790097/8796093022208)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-178015739/140737488355328), (4875052717/140737488355328)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-1840768113/2251799813685248), (-1272243177/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((3338619187/36028797018963968), (1862887877/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-116748689/18014398509481984), (-1835057327/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((6447124985/18446744073709551616), (471470629/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-4552016849/295147905179352825856), (365256115/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 7 => ⟨((1310208811/2361183241434822606848), (-2181068689/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-559437353/37778931862957161709568), (2082242089/75557863725914323419136)), (13/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((87559735/604462909807314587353088), (-796446173/604462909807314587353088)), (11/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((1154750965/77371252455336267181195264), (4107223725/77371252455336267181195264)), (19/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-854763593/618970019642690137449562112), (-553355015/309485009821345068724781056)), (29/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((390474021/4951760157141521099596496896), (1828487337/39614081257132168796771975168)), (3/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((237354319/281474976710656), (-3250035145/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((613589371/562949953421312), (424081059/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-3338619187/18014398509481984), (-1862887877/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((4981277397/288230376151711744), (1223371551/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-5372604153/4611686018427387904), (-196446095/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 5 => ⟨((4552016849/73786976294838206464), (-365256115/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-764288473/295147905179352825856), (2544580137/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((2983665883/37778931862957161709568), (-5552645571/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-262679205/302231454903657293676544), (2389338519/302231454903657293676544)), (15/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-962292471/9671406556917033397649408), (-3422686437/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((1567066587/154742504910672534362390528), (4057936777/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-3123792167/4951760157141521099596496896), (-1828487337/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((4965767325/158456325028528675187087900672), (91273287/19807040628566084398385987584)), (31/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-613589371/1125899906842624), (-424081059/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((3338619187/18014398509481984), (3725775755/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-116748689/4503599627370496), (-1835057327/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((5372604153/2305843009213693952), (196446095/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-5690021061/36893488147419103232), (14267817/288230376151711744)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((2292865419/295147905179352825856), (-1908435103/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-2610707647/9444732965739290427392), (2429282437/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((262679205/75557863725914323419136), (-2389338519/75557863725914323419136)), (7/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((541289515/1208925819614629174706176), (1925261121/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-979416617/19342813113834066795298816), (-2536210485/38685626227668133590597632)), (7/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((2147607115/618970019642690137449562112), (2514170089/1237940039285380274899124224)), (3/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-7448650987/39614081257132168796771975168), (-273819861/9903520314283042199192993792)), (21/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((5411528425/633825300114114700748351602688), (-655199607/316912650057057350374175801344)), (37/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1335447675/18014398509481984), (-745155151/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((2988766439/144115188075855872), (734022931/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-805890623/288230376151711744), (-471470629/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 3 => ⟨((4552016849/18446744073709551616), (-365256115/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-2292865419/147573952589676412928), (1908435103/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((391606147/590295810358705651712), (-2915138925/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-735501773/75557863725914323419136), (6690147853/75557863725914323419136)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-108257903/75557863725914323419136), (-6160835587/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((3525899821/19342813113834066795298816), (4565178873/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-2147607115/154742504910672534362390528), (-314271261/38685626227668133590597632)), (3/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((4096758043/4951760157141521099596496896), (301201847/2475880078570760549798248448)), (23/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-3246917055/79228162514264337593543950336), (1572479057/158456325028528675187087900672)), (21/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((2134747539/1267650600228229401496703205376), (-1527726957/1267650600228229401496703205376)), (19/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3985021919/576460752303423488), (-978697241/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((1074520831/576460752303423488), (314313753/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-4552016849/18446744073709551616), (365256115/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 3 => ⟨((764288473/36893488147419103232), (-2544580137/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-2610707647/2361183241434822606848), (2429282437/1180591620717411303424)), (17/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((735501773/37778931862957161709568), (-6690147853/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((1010407095/302231454903657293676544), (3593820759/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-2350599881/4835703278458516698824704), (-1521726291/2417851639229258349412352)), (17/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((3221410673/77371252455336267181195264), (942813783/38685626227668133590597632)), (19/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-6827930071/2475880078570760549798248448), (-251001539/618970019642690137449562112)), (39/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((1488170317/9903520314283042199192993792), (-45044973/1237940039285380274899124224)), (5/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-2134747539/316912650057057350374175801344), (1527726957/316912650057057350374175801344)), (39/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((146420423/633825300114114700748351602688), (-1843389935/5070602400912917605986812821504)), (37/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4912095227/9223372036854775808), (-359215717/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 1 => ⟨((1300576243/9223372036854775808), (-52179445/1152921504606846976)), (9/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-1310208811/73786976294838206464), (2181068689/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 3 => ⟨((2983665883/2361183241434822606848), (-2776322785/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-262679205/9444732965739290427392), (4778677037/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-108257903/18889465931478580854784), (-6160835587/302231454903657293676544)), (29/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((2350599881/2417851639229258349412352), (1521726291/1208925819614629174706176)), (19/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-3681612197/38685626227668133590597632), (-2155002933/38685626227668133590597632)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((2194691809/309485009821345068724781056), (645432529/618970019642690137449562112)), (7/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-4251915191/9903520314283042199192993792), (1029599383/9903520314283042199192993792)), (15/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((3354603275/158456325028528675187087900672), (-1200356895/79228162514264337593543950336)), (1/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-502012879/633825300114114700748351602688), (3160097031/2535301200456458802993406410752)), (33/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((1193514077/81129638414606681695789005144064), (-6467137957/81129638414606681695789005144064)), (1/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5202304971/147573952589676412928), (1669742241/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 1 => ⟨((2620417623/295147905179352825856), (-2181068689/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-559437353/590295810358705651712), (2082242089/1180591620717411303424)), (23/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((262679205/9444732965739290427392), (-2389338519/9444732965739290427392)), (25/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((541289515/75557863725914323419136), (1925261121/75557863725914323419136)), (23/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-881474955/604462909807314587353088), (-4565178873/2417851639229258349412352)), (17/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((3221410673/19342813113834066795298816), (942813783/9671406556917033397649408)), (3/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-4389383617/309485009821345068724781056), (-645432529/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((2391702295/2475880078570760549798248448), (-579149653/2475880078570760549798248448)), (39/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-2096627047/39614081257132168796771975168), (1500446119/39614081257132168796771975168)), (11/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((1380535417/633825300114114700748351602688), (-2172566709/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-447567779/10141204801825835211973625643008), (1212588367/5070602400912917605986812821504)), (13/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-455332481/162259276829213363391578010288128), (-1116933143/81129638414606681695789005144064)), (53/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4658520217/2361183241434822606848), (484681931/295147905179352825856)), (25/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((994555295/2361183241434822606848), (-1850881857/2361183241434822606848)), (25/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-87559735/4722366482869645213696), (796446173/4722366482869645213696)), (41/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-962292471/151115727451828646838272), (-3422686437/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((979416617/604462909807314587353088), (2536210485/1208925819614629174706176)), (25/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-2147607115/9671406556917033397649408), (-2514170089/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((853491259/38685626227668133590597632), (251001539/77371252455336267181195264)), (29/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-4251915191/2475880078570760549798248448), (1029599383/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((2096627047/19807040628566084398385987584), (-1500446119/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-1533928241/316912650057057350374175801344), (1206981505/158456325028528675187087900672)), (61/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((1094054571/10141204801825835211973625643008), (-2964104897/5070602400912917605986812821504)), (35/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((1214219949/162259276829213363391578010288128), (2978488381/81129638414606681695789005144064)), (39/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-1628442807/1298074214633706907132624082305024), (-307561335/162259276829213363391578010288128)), (83/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1591288471/18889465931478580854784), (740352743/4722366482869645213696)), (19/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((560382305/75557863725914323419136), (-1274313877/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((1154750965/302231454903657293676544), (4107223725/302231454903657293676544)), (9/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-1567066587/1208925819614629174706176), (-507242097/302231454903657293676544)), (47/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((2147607115/9671406556917033397649408), (314271261/2417851639229258349412352)), (51/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-4096758043/154742504910672534362390528), (-301201847/77371252455336267181195264)), (11/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((1488170317/618970019642690137449562112), (-45044973/77371252455336267181195264)), (17/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-3354603275/19807040628566084398385987584), (1200356895/9903520314283042199192993792)), (49/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((1380535417/158456325028528675187087900672), (-2172566709/158456325028528675187087900672)), (33/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-1094054571/5070602400912917605986812821504), (2964104897/2535301200456458802993406410752)), (41/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-166955243/10141204801825835211973625643008), (-6552674439/81129638414606681695789005144064)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((244266421/81129638414606681695789005144064), (184536801/40564819207303340847894502572032)), (7/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-2966364775/10384593717069655257060992658440192), (-1020307237/5192296858534827628530496329220096)), (63/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/1022486043), (-736960/340828681)), 0, by norm_num⟩
  | 1 => ⟨((-50249752371200/348492569376599283), (16149446656000/116164189792199761)), 0, by norm_num⟩
  | 2 => ⟨((1594156627/562949953421312), (-3569053463/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-158236213/18014398509481984), (4333380193/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1636238323/576460752303423488), (-141360353/18014398509481984)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((445149225/2305843009213693952), (3974160805/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-5313362559/590295810358705651712), (-2609859309/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((6549460303/18889465931478580854784), (478954289/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-1734101657/151115727451828646838272), (556580747/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((3105680145/9671406556917033397649408), (-2584970299/9671406556917033397649408)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-2121717961/309485009821345068724781056), (3948547963/309485009821345068724781056)), (13/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((543401021/9903520314283042199192993792), (-4942793221/9903520314283042199192993792)), (19/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1493011351/316912650057057350374175801344), (1327587467/79228162514264337593543950336)), (55/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((665722601/33554432), (1871548907/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((5661612969/4294967296), (852176967/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4538784951/549755813888), (-237650011/68719476736)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2636591881/35184372088832), (2677240761/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((1602599717/2251799813685248), (-3992977901/2251799813685248)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((41687061/72057594037927936), (2954817029/72057594037927936)), (29/144115188075855872), by norm_num⟩
  | 6 => ⟨((-897825263/2305843009213693952), (-2067992331/2305843009213693952)), (45/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2655424387/147573952589676412928), (2554318643/147573952589676412928)), (67/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2945357965/4722366482869645213696), (-1146019947/4722366482869645213696)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((5619427149/302231454903657293676544), (-132531293/302231454903657293676544)), (237/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2348712297/4835703278458516698824704), (521563869/2417851639229258349412352)), (323/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((413255425/38685626227668133590597632), (-1743656539/154742504910672534362390528)), (109/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-1632261257/9903520314283042199192993792), (4273317975/9903520314283042199192993792)), (73/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1700433735/4503599627370496), (475873795/562949953421312)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((63294485/18014398509481984), (-6933408309/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((654495329/288230376151711744), (3618825037/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-148383075/576460752303423488), (-331180067/1152921504606846976)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5313362557/295147905179352825856), (1304929655/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-1146155553/1180591620717411303424), (-335268003/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((6473979519/151115727451828646838272), (-1038950727/75557863725914323419136)), (7/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1863408087/1208925819614629174706176), (1550982179/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((1591288471/38685626227668133590597632), (-2961410971/38685626227668133590597632)), (5/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-124529401/309485009821345068724781056), (566361723/154742504910672534362390528)), (17/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-410578121/9903520314283042199192993792), (-5841384853/39614081257132168796771975168)), (7/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((2431327553/633825300114114700748351602688), (786993799/158456325028528675187087900672)), (11/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-4442726639/20282409603651670423947251286016), (-650128831/5070602400912917605986812821504)), (35/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662890353/134217728), (467887255/33554432)), (7/134217728), by norm_num⟩
  | 1 => ⟨((707701623/536870912), (426088277/2147483648)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((4538786199/549755813888), (-1901196637/549755813888)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-1318300469/17592186044416), (1338615327/17592186044416)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((1602640255/2251799813685248), (-3992957989/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((41617105/72057594037927936), (2954811913/72057594037927936)), (15/72057594037927936), by norm_num⟩
  | 6 => ⟨((-448863239/1152921504606846976), (-4136048075/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((331899615/18446744073709551616), (638626993/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-736290929/1180591620717411303424), (-2292762895/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2809652769/151115727451828646838272), (-65712559/151115727451828646838272)), (119/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4697825549/9671406556917033397649408), (2084829357/9671406556917033397649408)), (81/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((826807643/77371252455336267181195264), (-3485775981/309485009821345068724781056)), (437/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1634430557/9903520314283042199192993792), (66750753/154742504910672534362390528)), (585/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1994652431/4611686018427387904), (-689300007/576460752303423488)), (1/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1356645257/9223372036854775808), (1513966021/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-379525897/18446744073709551616), (-1491348177/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 3 => ⟨((4366306867/2361183241434822606848), (319302859/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-1156067771/9444732965739290427392), (1484215325/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((3726816173/604462909807314587353088), (-1550982179/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-2121717961/9671406556917033397649408), (3948547961/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((213478973/77371252455336267181195264), (-970905811/38685626227668133590597632)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((1759620519/4951760157141521099596496896), (1564656657/1237940039285380274899124224)), (3/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-397985165/9903520314283042199192993792), (-4122348471/79228162514264337593543950336)), (23/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((3490713787/1267650600228229401496703205376), (2043262041/1267650600228229401496703205376)), (5/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-3026753417/20282409603651670423947251286016), (-445065933/20282409603651670423947251286016)), (35/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((4397940561/649037107316853453566312041152512), (-1064959361/649037107316853453566312041152512)), (31/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662890353/134217728), (467887255/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((5661612985/4294967296), (852176555/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((1134696547/137438953472), (-1901196643/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-2636600873/35184372088832), (2677230659/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((1602639979/2251799813685248), (-3992957901/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((83235099/144115188075855872), (2954811543/72057594037927936)), (31/144115188075855872), by norm_num⟩
  | 6 => ⟨((-112215873/288230376151711744), (-258502887/288230376151711744)), (47/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2655197327/147573952589676412928), (638626067/36893488147419103232)), (69/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1472581019/2361183241434822606848), (-1146375479/4722366482869645213696)), (89/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((351205837/18889465931478580854784), (-32860211/75557863725914323419136)), (239/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-4697798917/9671406556917033397649408), (1042422473/4835703278458516698824704)), (325/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((3307184387/309485009821345068724781056), (-871445693/77371252455336267181195264)), (219/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-817181725/4951760157141521099596496896), (2136015971/4951760157141521099596496896)), (293/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2428965741/590295810358705651712), (2386157083/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-5239568243/4722366482869645213696), (-47895429/590295810358705651712)), (15/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((2774562651/18889465931478580854784), (-1781058389/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-3726816173/302231454903657293676544), (3101964357/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((1591288471/2417851639229258349412352), (-2961410971/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-448305843/38685626227668133590597632), (2038902203/19342813113834066795298816)), (15/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-1231734363/618970019642690137449562112), (-273814915/38685626227668133590597632)), (9/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((716373297/2475880078570760549798248448), (463764203/1237940039285380274899124224)), (11/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-3927053011/158456325028528675187087900672), (-2298669795/158456325028528675187087900672)), (3/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1040446487/633825300114114700748351602688), (611965657/2535301200456458802993406410752)), (3/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-3628300963/40564819207303340847894502572032), (878591473/40564819207303340847894502572032)), (13/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((2602358905/649037107316853453566312041152512), (-1862371909/649037107316853453566312041152512)), (25/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-2855895489/20769187434139310514121985316880384), (2247180111/10384593717069655257060992658440192)), (23/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662890353/134217728), (467887255/33554432)), (9/134217728), by norm_num⟩
  | 1 => ⟨((5661612985/4294967296), (852176555/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((1134696547/137438953472), (-1901196643/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2636600873/35184372088832), (2677230659/35184372088832)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((400659995/562949953421312), (-249559869/140737488355328)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((83235097/144115188075855872), (5909623101/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1795453977/4611686018427387904), (-4136046225/4611686018427387904)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((1327598685/73786976294838206464), (2554504323/147573952589676412928)), (35/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2945162155/4722366482869645213696), (-2292751095/9444732965739290427392)), (179/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((87801467/4722366482869645213696), (-131440771/302231454903657293676544)), (15/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-2348899891/4835703278458516698824704), (2084845155/9671406556917033397649408)), (163/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((826796407/77371252455336267181195264), (-871445915/77371252455336267181195264)), (439/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-408591203/2475880078570760549798248448), (4272034085/9903520314283042199192993792)), (587/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4484141659/151115727451828646838272), (1439239103/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((4517352939/604462909807314587353088), (-3759956797/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-964417255/1208925819614629174706176), (56087329/37778931862957161709568)), (21/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((452834185/19342813113834066795298816), (-4118994349/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((933132093/154742504910672534362390528), (6637937333/309485009821345068724781056)), (41/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-3039159441/2475880078570760549798248448), (-3934968995/2475880078570760549798248448)), (15/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((2776704149/19807040628566084398385987584), (1625322077/19807040628566084398385987584)), (21/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-3783441771/316912650057057350374175801344), (-4346347/2475880078570760549798248448)), (29/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((1030767319/1267650600228229401496703205376), (-499199701/2535301200456458802993406410752)), (35/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-3614387367/81129638414606681695789005144064), (2586627653/81129638414606681695789005144064)), (39/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((2379912907/1298074214633706907132624082305024), (-3745300185/1298074214633706907132624082305024)), (43/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((-48222791/1298074214633706907132624082305024), (4180776053/20769187434139310514121985316880384)), (23/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-392475135/166153499473114484112975882535043072), (-3850974877/332306998946228968225951765070086144)), (47/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662890353/134217728), (467887255/33554432)), (5/67108864), by norm_num⟩
  | 1 => ⟨((5661612985/4294967296), (852176555/4294967296)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((1134696547/137438953472), (-1901196643/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2636600873/35184372088832), (2677230659/35184372088832)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((400659995/562949953421312), (-249559869/140737488355328)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((83235097/144115188075855872), (5909623101/144115188075855872)), (33/144115188075855872), by norm_num⟩
  | 6 => ⟨((-224431747/576460752303423488), (-4136046225/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | 7 => ⟨((331899671/18446744073709551616), (2554504323/147573952589676412928)), (71/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2945162151/4722366482869645213696), (-2292751097/9444732965739290427392)), (45/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5619293875/302231454903657293676544), (-131440761/302231454903657293676544)), (241/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1174449941/2417851639229258349412352), (2084845127/9671406556917033397649408)), (327/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((3307185617/309485009821345068724781056), (-1742891799/154742504910672534362390528)), (55/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-1634364835/9903520314283042199192993792), (2136016985/4951760157141521099596496896)), (147/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((390571325/2417851639229258349412352), (-2907435649/9671406556917033397649408)), (5/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((-550168655/38685626227668133590597632), (5004351817/38685626227668133590597632)), (5/4835703278458516698824704), by norm_num⟩
  | 2 => ⟨((-566852111/77371252455336267181195264), (-4032364569/154742504910672534362390528)), (9/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((3077009779/1237940039285380274899124224), (3983975935/1237940039285380274899124224)), (47/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-2108464359/4951760157141521099596496896), (-2468346275/9903520314283042199192993792)), (51/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((4022089637/79228162514264337593543950336), (591424153/79228162514264337593543950336)), (11/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-182630825/39614081257132168796771975168), (88447947/79228162514264337593543950336)), (17/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((411682693/1267650600228229401496703205376), (-2356957857/10141204801825835211973625643008)), (49/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-1355373477/81129638414606681695789005144064), (1066484517/40564819207303340847894502572032)), (33/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((537057047/1298074214633706907132624082305024), (-5820160949/2596148429267413814265248164610048)), (41/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((655649121/20769187434139310514121985316880384), (6433243965/41538374868278621028243970633760768)), (97/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((-1918514943/332306998946228968225951765070086144), (-181173393/20769187434139310514121985316880384)), (7/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((2912299163/5316911983139663491615228241121378304), (2003421789/5316911983139663491615228241121378304)), (63/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662890353/134217728), (467887255/33554432)), (11/134217728), by norm_num⟩
  | 1 => ⟨((5661612985/4294967296), (852176555/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((1134696547/137438953472), (-1901196643/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2636600873/35184372088832), (2677230659/35184372088832)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((400659995/562949953421312), (-249559869/140737488355328)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((83235097/144115188075855872), (5909623101/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 6 => ⟨((-224431747/576460752303423488), (-4136046225/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | 7 => ⟨((331899671/18446744073709551616), (2554504323/147573952589676412928)), (9/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-2945162151/4722366482869645213696), (-2292751097/9444732965739290427392)), (181/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5619293875/302231454903657293676544), (-65720381/151115727451828646838272)), (121/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1174449941/2417851639229258349412352), (260605641/1208925819614629174706176)), (41/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((3307185615/309485009821345068724781056), (-3485783601/309485009821345068724781056)), (441/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-817182415/4951760157141521099596496896), (2136016987/4951760157141521099596496896)), (589/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((332693075144367/4194304), (850989460035075/2097152)), (348247125/4194304), by norm_num⟩
  | 1 => ⟨((192376293/8), (4405124795/8)), (1017/8), by norm_num⟩
  | 2 => ⟨((-293756313/8), (2947102813/8)), (785/8), by norm_num⟩
  | 3 => ⟨((-626140487/16), (5196531999/32)), (1631/32), by norm_num⟩
  | 4 => ⟨((-1311887431/64), (3400297523/64)), (1283/64), by norm_num⟩
  | 5 => ⟨((-951225959/128), (3524122921/256)), (815/128), by norm_num⟩
  | 6 => ⟨((-1068745409/512), (3011732539/1024)), (871/512), by norm_num⟩
  | 7 => ⟨((-1971465413/4096), (4360083763/8192)), (3221/8192), by norm_num⟩
  | 8 => ⟨((-1547017435/16384), (1361086323/16384)), (1315/16384), by norm_num⟩
  | 9 => ⟨((-264605755/16384), (741581847/65536)), (963/65536), by norm_num⟩
  | 10 => ⟨((-5142177213/2097152), (709298341/524288)), (1281/524288), by norm_num⟩
  | 11 => ⟨((-2810098995/8388608), (2378849247/16777216)), (3127/8388608), by norm_num⟩
  | 12 => ⟨((-5587593347/134217728), (1726072477/134217728)), (7063/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609819685414259/10141204801825835211973625643008), (897340639049/5070602400912917605986812821504)), (53379/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((226645088027553/79228162514264337593543950336), (2200728194867/633825300114114700748351602688)), (131199/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((964236600994391/19807040628566084398385987584), (2482183617143/39614081257132168796771975168)), (148013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1930707011862841/2475880078570760549798248448), (2642785772059/2475880078570760549798248448)), (157613/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((113275996805309/9671406556917033397649408), (2648902964321/154742504910672534362390528)), (158003/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1588247553787469/9671406556917033397649408), (155616562231/604462909807314587353088)), (2321/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1292691596785525/604462909807314587353088), (1092586442117/302231454903657293676544)), (65197/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((485742477653665/18889465931478580854784), (890804621853/18889465931478580854784)), (212677/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1338998004711765/4722366482869645213696), (1341617860459/2361183241434822606848)), (160199/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((419644041915441/147573952589676412928), (3707125805295/590295810358705651712)), (55351/147573952589676412928), by norm_num⟩
  | 8 => ⟨((947534622409057/36893488147419103232), (2330291398579/36893488147419103232)), (278461/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1903455819358821/9223372036854775808), (2640048568101/4611686018427387904)), (315633/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1675024866562661/1152921504606846976), (2663335549177/576460752303423488)), (318615/1152921504606846976), by norm_num⟩
  | 5 => ⟨((632926519801809/72057594037927936), (1178446031207/36028797018963968)), (70545/36028797018963968), by norm_num⟩
  | 4 => ⟨((799639254517489/18014398509481984), (1794490941661/9007199254740992)), (215075/18014398509481984), by norm_num⟩
  | 3 => ⟨((1625105824193705/9007199254740992), (4581693850265/4503599627370496)), (549947/9007199254740992), by norm_num⟩
  | 2 => ⟨((625898397443451/1125899906842624), (9456257668035/2251799813685248)), (142195/562949953421312), by norm_num⟩
  | 1 => ⟨((1319827400045501/1125899906842624), (14939716379933/1125899906842624)), (901845/1125899906842624), by norm_num⟩
  | 0 => ⟨((767363210099545/562949953421312), (16521918279735/562949953421312)), (2008249/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((767363210099545/562949953421312), (16521918279735/562949953421312)), (7660861973289107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2091032493576379/1125899906842624), (22521206674035/281474976710656)), (5592813/1125899906842624), by norm_num⟩
  | 2 => ⟨((242267406868689/70368744177664), (20913304399331/70368744177664)), (5417259/281474976710656), by norm_num⟩
  | 3 => ⟨((1655738803094091/140737488355328), (288003549592387/140737488355328)), (10130337/70368744177664), by norm_num⟩
  | 4 => ⟨((1180622239746415/8796093022208), (423535564387965/8796093022208)), (34977827/8796093022208), by norm_num⟩
  | 5 => ⟨((1078680699146881/68719476736), (222060373040725/17179869184)), (99671303/68719476736), by norm_num⟩
  | 6 => ⟨((332693075144367/4194304), (850989460035075/2097152)), (348247125/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2662890353/134217728), (467887255/33554432)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/50831881), (-8843520/50831881)), 0, by norm_num⟩
  | 1 => ⟨((36566369075200/2583880125998161), (19922681856000/2583880125998161)), 0, by norm_num⟩
  | 2 => ⟨((-270562913/274877906944), (582836189/549755813888)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-2477358795/35184372088832), (-1919573405/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((1555424065/140737488355328), (-2086838709/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((349289653/4503599627370496), (4699643167/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1666208971/18014398509481984), (-1180110741/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((125171815/36028797018963968), (-276804905/36028797018963968)), (11/576460752303423488), by norm_num⟩
  | 8 => ⟨((2727035215/4611686018427387904), (1089423727/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-3999402811/73786976294838206464), (3022997779/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1394722077/590295810358705651712), (-829774687/147573952589676412928)), (19/590295810358705651712), by norm_num⟩
  | 11 => ⟨((5114041883/9444732965739290427392), (-764400109/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-749281877/151115727451828646838272), (923596989/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (6909/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (6909/1280)))⁻¹=value ((2252800/50831881), (-8843520/50831881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/50831881), (-8843520/50831881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/56975881), (-8843520/56975881)), 0, by norm_num⟩
  | 1 => ⟨((31533204275200/3246251015726161), (34411905024000/3246251015726161)), 0, by norm_num⟩
  | 2 => ⟨((-1269256361/1099511627776), (1723485383/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((633818223/70368744177664), (-7245901455/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((540693359/70368744177664), (2372964509/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1327471429/2251799813685248), (1018654921/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-269801065/18014398509481984), (-4409812681/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((3032698433/576460752303423488), (1069294377/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-2320841585/9223372036854775808), (1736826859/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-95165125/4611686018427387904), (-4779719379/147573952589676412928)), (13/73786976294838206464), by norm_num⟩
  | 10 => ⟨((3799457039/1180591620717411303424), (-292481161/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-674764203/9444732965739290427392), (2518734529/9444732965739290427392)), (11/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-1379449435/75557863725914323419136), (-2214016211/151115727451828646838272)), (5/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (6909/1280)))⁻¹=value ((3891200/56975881), (-8843520/56975881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/56975881), (-8843520/56975881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-69441750630400/2896191202862161), (-54334586880000/2896191202862161)), 0, by norm_num⟩
  | 1 => ⟨((609953887/137438953472), (-1588867211/549755813888)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1496037673/8796093022208), (2939204129/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-5588535813/70368744177664), (-432392165/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((474037347/140737488355328), (-2229901609/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((3004232511/4503599627370496), (1331166663/2251799813685248)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2792815813/36028797018963968), (807425485/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((-1029949393/576460752303423488), (-4963525669/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((3887456007/4611686018427387904), (110505149/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-619190203/18446744073709551616), (1353214367/18446744073709551616)), (13/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-823612649/147573952589676412928), (-3026617587/590295810358705651712)), (25/590295810358705651712), by norm_num⟩
  | 11 => ⟨((2894403043/4722366482869645213696), (-1641567319/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 12 => ⟨((62800531/4722366482869645213696), (2400698031/37778931862957161709568)), (45/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((27/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/7377409), (-2947840/22132227)), 0, by norm_num⟩
  | 1 => ⟨((2646187212800/489835471979529), (603717632000/54426163553281)), 0, by norm_num⟩
  | 2 => ⟨((-1059558123/1099511627776), (-112293187/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((3302333569/70368744177664), (-2108367325/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((1146454505/562949953421312), (1582040189/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-4135272115/9007199254740992), (-443239355/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((3699702145/144115188075855872), (-1907835663/72057594037927936)), (15/144115188075855872), by norm_num⟩
  | 7 => ⟨((1600814077/2305843009213693952), (6484363407/2305843009213693952)), (27/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-3987937831/18446744073709551616), (-653620159/9223372036854775808)), (25/18446744073709551616), by norm_num⟩
  | 9 => ⟨((2024938983/147573952589676412928), (-1689174307/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 10 => ⟨((901525585/4722366482869645213696), (6566122579/4722366482869645213696)), (77/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-949636507/9444732965739290427392), (-1707035439/37778931862957161709568)), (17/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((2174846189/302231454903657293676544), (-90943155/18889465931478580854784)), (119/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (6909/1280)))⁻¹=value ((614400/7377409), (-2947840/22132227)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/7377409), (-2947840/22132227))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1235743325/274877906944), (1793439453/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((8690615/137438953472), (-2636874529/2199023255552)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((3173623579/17592186044416), (383272999/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-2920020467/140737488355328), (162298415/8796093022208)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-320735745/281474976710656), (-3668687349/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((224471207/562949953421312), (363568257/18014398509481984)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-1328288147/72057594037927936), (5731678959/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 7 => ⟨((-3662444307/1152921504606846976), (-3877082007/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((4050892343/9223372036854775808), (-810808171/4611686018427387904)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((58350679/147573952589676412928), (6958130005/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-5081488417/1180591620717411303424), (-59792847/36893488147419103232)), (19/590295810358705651712), by norm_num⟩
  | 11 => ⟨((689241723/2361183241434822606848), (-3114314013/9444732965739290427392)), (19/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1463984739/75557863725914323419136), (1386157887/37778931862957161709568)), (71/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((35/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1024000/11299183), (-180480/1614169)), 0, by norm_num⟩
  | 1 => ⟨((273751244800/127671536467489), (184811520000/18238790923927)), 0, by norm_num⟩
  | 2 => ⟨((-2918708435/4398046511104), (-746086719/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((431350627/8796093022208), (-764442487/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-1134306589/1125899906842624), (4195126135/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-2930069975/18014398509481984), (-2028056979/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 6 => ⟨((719054093/36028797018963968), (79957549/72057594037927936)), (19/288230376151711744), by norm_num⟩
  | 7 => ⟨((-2228321041/2305843009213693952), (2456774905/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((-581982183/36893488147419103232), (-471795985/4611686018427387904)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((3798034007/590295810358705651712), (1107938405/295147905179352825856)), (45/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-4735660587/9444732965739290427392), (1790732225/9444732965739290427392)), (37/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1831620553/151115727451828646838272), (-5534243641/151115727451828646838272)), (121/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1811161957/1208925819614629174706176), (2825358835/1208925819614629174706176)), (99/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (6909/1280)))⁻¹=value ((1024000/11299183), (-180480/1614169)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((1024000/11299183), (-180480/1614169))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-989751203/4398046511104), (1430410809/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-2718157843/17592186044416), (-2775990355/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((5899096989/140737488355328), (-1936594365/140737488355328)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((-533302091/562949953421312), (979363923/140737488355328)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((-229035629/281474976710656), (-603684723/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((947909183/9007199254740992), (-2303967913/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((228073975/144115188075855872), (4163908511/288230376151711744)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-3558436961/2305843009213693952), (-297290203/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((1096697331/9223372036854775808), (-1180089125/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((2087451607/295147905179352825856), (4921220525/295147905179352825856)), (37/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-2153285585/1180591620717411303424), (-475417/18446744073709551616)), (39/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1391649563/18889465931478580854784), (-1542498341/9444732965739290427392)), (39/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((3521096257/302231454903657293676544), (119739781/9444732965739290427392)), (37/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((43/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/95068681), (-8843520/95068681)), 0, by norm_num⟩
  | 1 => ⟨((327582515200/9038054107079761), (77879574528000/9038054107079761)), 0, by norm_num⟩
  | 2 => ⟨((-3540066645/8796093022208), (-1747837487/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1306199135/35184372088832), (-10988647/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1919577909/1125899906842624), (245047443/140737488355328)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-72719605/36028797018963968), (-1440630571/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((4342240027/576460752303423488), (4216234279/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1588869309/2305843009213693952), (106940873/9223372036854775808)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((1157545059/36893488147419103232), (-1202216199/36893488147419103232)), (1/4611686018427387904), by norm_num⟩
  | 9 => ⟨((36859095/590295810358705651712), (438082645/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-2662726155/18889465931478580854784), (-1271145005/9444732965739290427392)), (37/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((7730297495/604462909807314587353088), (-195134591/604462909807314587353088)), (111/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-2791683423/4835703278458516698824704), (2948667133/4835703278458516698824704)), (83/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (6909/1280)))⁻¹=value ((8806400/95068681), (-8843520/95068681)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/95068681), (-8843520/95068681))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((174437975/4398046511104), (5713162097/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-2435065257/70368744177664), (-303961773/140737488355328)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((2424003397/562949953421312), (-1881152651/281474976710656)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((1510918851/2251799813685248), (699488967/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-3857253303/18014398509481984), (-11405263/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((123685397/9007199254740992), (-231102805/9007199254740992)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((1180478283/576460752303423488), (3479550065/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-3930479909/9223372036854775808), (236328925/4611686018427387904)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1214997243/73786976294838206464), (-3328275695/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 9 => ⟨((2090524173/590295810358705651712), (1104336089/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-2405595671/4722366482869645213696), (1498858807/9444732965739290427392)), (27/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((592720139/75557863725914323419136), (-4006459817/75557863725914323419136)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1318169257/302231454903657293676544), (439959823/151115727451828646838272)), (55/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((51/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/38106627), (-2947840/38106627)), 0, by norm_num⟩
  | 1 => ⟨((-571962982400/484038340439043), (10263199744000/1452115021317129)), 0, by norm_num⟩
  | 2 => ⟨((-1929794743/8796093022208), (-3242033941/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((854222585/35184372088832), (146922981/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1612432287/1125899906842624), (313868221/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((790073109/18014398509481984), (-728347811/9007199254740992)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((1296057685/1152921504606846976), (1553670041/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1198334201/4611686018427387904), (-3740338345/18446744073709551616)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((2909142329/147573952589676412928), (-232532359/295147905179352825856)), (39/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-513597587/590295810358705651712), (3770673675/4722366482869645213696)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((83706915/9444732965739290427392), (-5298817039/75557863725914323419136)), (37/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1394885237/604462909807314587353088), (4287421847/1208925819614629174706176)), (101/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-4692411847/19342813113834066795298816), (-1407270375/19342813113834066795298816)), (137/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (6909/1280)))⁻¹=value ((3481600/38106627), (-2947840/38106627)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/38106627), (-2947840/38106627))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((696956459/70368744177664), (612150811/140737488355328)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((-4446609667/1125899906842624), (2999368319/1125899906842624)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-52030281/1125899906842624), (-5486088277/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((3722715745/18014398509481984), (2080295465/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 4 => ⟨((-4827069309/144115188075855872), (2774597319/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 5 => ⟨((63680585/1152921504606846976), (-402188963/72057594037927936)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((2923472369/4611686018427387904), (1726799713/4611686018427387904)), (9/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-2892906769/36893488147419103232), (1662486095/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-86050885/590295810358705651712), (-3095029115/295147905179352825856)), (53/590295810358705651712), by norm_num⟩
  | 9 => ⟨((2420852327/2361183241434822606848), (1278098271/2361183241434822606848)), (15/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-240931749/2361183241434822606848), (1300244489/18889465931478580854784)), (65/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-418968161/302231454903657293676544), (-3790799853/302231454903657293676544)), (135/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1417063327/1208925819614629174706176), (2166247885/4835703278458516698824704)), (17/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((59/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/136847881), (-8843520/136847881)), 0, by norm_num⟩
  | 1 => ⟨((-33897938124800/18727342534190161), (106858020864000/18727342534190161)), 0, by norm_num⟩
  | 2 => ⟨((-1837631359/17592186044416), (-5460544069/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((4121066247/281474976710656), (1453576513/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-4413959971/4503599627370496), (76991785/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((192381067/4503599627370496), (-1168165707/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-483218851/576460752303423488), (6483294865/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-496607291/9223372036854775808), (-2789443873/18446744073709551616)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((2143677365/295147905179352825856), (2913821683/590295810358705651712)), (11/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-1133717299/2361183241434822606848), (158249707/9444732965739290427392)), (7/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((3121494999/151115727451828646838272), (-1228118959/75557863725914323419136)), (35/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-935103071/2417851639229258349412352), (6697564279/4835703278458516698824704)), (87/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-2141470867/77371252455336267181195264), (-1424460699/19342813113834066795298816)), (107/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (6909/1280)))⁻¹=value ((12083200/136847881), (-8843520/136847881)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/136847881), (-8843520/136847881))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301094111/1125899906842624), (-288224037/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1975363163/9007199254740992), (303476051/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-3261964115/36028797018963968), (-4880403913/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((2455958585/72057594037927936), (-14870355/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 4 => ⟨((-1853132753/576460752303423488), (1432590073/288230376151711744)), (15/576460752303423488), by norm_num⟩
  | 5 => ⟨((-863517897/2305843009213693952), (-1890092791/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 6 => ⟨((4544901765/36893488147419103232), (298530347/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1471762055/147573952589676412928), (3633868107/295147905179352825856)), (21/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1530185727/2361183241434822606848), (-4208310345/2361183241434822606848)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((999758833/4722366482869645213696), (742048745/18889465931478580854784)), (29/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-2293513467/151115727451828646838272), (335819631/18889465931478580854784)), (65/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-2024562117/2417851639229258349412352), (-2772268803/1208925819614629174706176)), (17/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((294385839/1208925819614629174706176), (367406437/9671406556917033397649408)), (35/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((67/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/162652681), (-8843520/162652681)), 0, by norm_num⟩
  | 1 => ⟨((-55037230284800/26455894636487761), (121347244032000/26455894636487761)), 0, by norm_num⟩
  | 2 => ⟨((-162475721/4398046511104), (-2199268647/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2351821545/281474976710656), (2685847653/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-5510942861/9007199254740992), (-1579389525/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((4406263253/144115188075855872), (-665574817/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-598685901/576460752303423488), (703737309/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((391787159/36893488147419103232), (-2941412095/36893488147419103232)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((2029993223/1180591620717411303424), (2155545547/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-3245195833/18889465931478580854784), (-2026540559/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((767906569/75557863725914323419136), (-43851737/302231454903657293676544)), (57/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-4107876797/9671406556917033397649408), (2731287721/9671406556917033397649408)), (1/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1584354809/154742504910672534362390528), (-3630102019/154742504910672534362390528)), (9/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (6909/1280)))⁻¹=value ((13721600/162652681), (-8843520/162652681)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/162652681), (-8843520/162652681))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1505458411/18014398509481984), (-3041798589/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((172561589/18014398509481984), (569567471/9007199254740992)), (15/72057594037927936), by norm_num⟩
  | 2 => ⟨((-2468108107/144115188075855872), (-2568634333/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 3 => ⟨((4420707691/1152921504606846976), (-562482229/288230376151711744)), (25/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-505624191/4611686018427387904), (7200115719/9223372036854775808)), (43/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-855533965/9223372036854775808), (-195300023/2305843009213693952)), (17/18446744073709551616), by norm_num⟩
  | 6 => ⟨((645173191/36893488147419103232), (-631862557/147573952589676412928)), (49/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-936400669/1180591620717411303424), (660217659/295147905179352825856)), (67/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-422486427/2361183241434822606848), (-4364173829/18889465931478580854784)), (41/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5111336563/151115727451828646838272), (-250516565/75557863725914323419136)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-997572565/604462909807314587353088), (2045713223/604462909807314587353088)), (55/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-2105578301/9671406556917033397649408), (-3245214129/9671406556917033397649408)), (119/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((791382389/19342813113834066795298816), (-8703973/4835703278458516698824704)), (247/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((75/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/63911427), (-2947840/63911427)), 0, by norm_num⟩
  | 1 => ⟨((-2920773222400/1361556833725443), (15092940800000/4084670501176329)), 0, by norm_num⟩
  | 2 => ⟨((25034881/35184372088832), (-3474059513/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((2547746537/562949953421312), (1115549125/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-204957899/562949953421312), (-119979303/562949953421312)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((2810017395/144115188075855872), (40499803/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3616751047/4611686018427387904), (2047784583/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((781157589/36893488147419103232), (-165434113/4611686018427387904)), (17/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-24569125/1180591620717411303424), (4545745527/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1645845605/37778931862957161709568), (-45803759/590295810358705651712)), (19/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((267059399/75557863725914323419136), (2542840733/1208925819614629174706176)), (5/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1838381333/9671406556917033397649408), (-105989307/38685626227668133590597632)), (41/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((2375943771/309485009821345068724781056), (-661363761/154742504910672534362390528)), (21/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (6909/1280)))⁻¹=value ((5120000/63911427), (-2947840/63911427)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/63911427), (-2947840/63911427))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((807262035/288230376151711744), (-1530224623/144115188075855872)), (25/576460752303423488), by norm_num⟩
  | 1 => ⟨((2200179717/576460752303423488), (736985429/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 2 => ⟨((-4735816049/2305843009213693952), (-1471085/36028797018963968)), (25/2305843009213693952), by norm_num⟩
  | 3 => ⟨((692609221/2305843009213693952), (-873733291/2305843009213693952)), (31/9223372036854775808), by norm_num⟩
  | 4 => ⟨((1765710019/73786976294838206464), (6618662687/73786976294838206464)), (55/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-2119842863/147573952589676412928), (-818739315/147573952589676412928)), (45/295147905179352825856), by norm_num⟩
  | 6 => ⟨((17586909/9223372036854775808), (-1485945453/1180591620717411303424)), (33/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-72878479/9444732965739290427392), (5859012241/18889465931478580854784)), (23/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-2348985/73786976294838206464), (-1727083723/75557863725914323419136)), (29/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((2634877213/604462909807314587353088), (-1987831271/1208925819614629174706176)), (139/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-272719293/2417851639229258349412352), (4967564441/9671406556917033397649408)), (161/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-3113819373/77371252455336267181195264), (-48374407/1208925819614629174706176)), (89/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1773176655/309485009821345068724781056), (-209926839/154742504910672534362390528)), (47/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((83/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/224092681), (-8843520/224092681)), 0, by norm_num⟩
  | 1 => ⟨((-105368878284800/50217529677767761), (150325690368000/50217529677767761)), 0, by norm_num⟩
  | 2 => ⟨((721757173/35184372088832), (-5451357709/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1283057479/562949953421312), (883984541/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1894932539/9007199254740992), (-3481312935/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((3398904513/288230376151711744), (916085329/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2351789701/4611686018427387904), (1034307421/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2527754335/147573952589676412928), (-2112617673/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1733911347/4722366482869645213696), (1040022655/1180591620717411303424)), (5/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-522364295/151115727451828646838272), (-6143798267/151115727451828646838272)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((2256643449/2417851639229258349412352), (3563354267/2417851639229258349412352)), (9/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-4988787491/77371252455336267181195264), (-2899846583/77371252455336267181195264)), (17/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((3942877779/1237940039285380274899124224), (46180091/309485009821345068724781056)), (63/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (6909/1280)))⁻¹=value ((16998400/224092681), (-8843520/224092681)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/224092681), (-8843520/224092681))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-238168977/1152921504606846976), (-2112046789/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((2385319503/4611686018427387904), (2471411237/9223372036854775808)), (9/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1681492821/9223372036854775808), (1438808069/18446744073709551616)), (27/18446744073709551616), by norm_num⟩
  | 3 => ⟨((121805829/9223372036854775808), (-3479210545/73786976294838206464)), (17/36893488147419103232), by norm_num⟩
  | 4 => ⟨((1707306777/295147905179352825856), (291778515/36893488147419103232)), (63/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-1988125389/1180591620717411303424), (-93909075/2361183241434822606848)), (105/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((753788489/4722366482869645213696), (-3824024631/18889465931478580854784)), (5/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((1450085003/151115727451828646838272), (2618849931/75557863725914323419136)), (113/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-1319150425/302231454903657293676544), (-1937624759/1208925819614629174706176)), (73/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((4477168011/9671406556917033397649408), (-3115023135/9671406556917033397649408)), (179/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((39595307/77371252455336267181195264), (5010784213/77371252455336267181195264)), (105/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-3669987353/618970019642690137449562112), (-602445857/154742504910672534362390528)), (59/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((3380879853/4951760157141521099596496896), (-1477335171/4951760157141521099596496896)), (127/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((91/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2662400/37103983), (-180480/5300569)), 0, by norm_num⟩
  | 1 => ⟨((-2746147635200/1376705554464289), (480509952000/196672222066327)), 0, by norm_num⟩
  | 2 => ⟨((527260787/17592186044416), (-1069740831/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((560222953/562949953421312), (5487088469/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1068914167/9007199254740992), (-2844610575/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1001026911/144115188075855872), (131324025/36028797018963968)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-179429369/576460752303423488), (-115473083/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3358901111/295147905179352825856), (-715719747/147573952589676412928)), (13/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-769115803/2361183241434822606848), (3473294311/9444732965739290427392)), (23/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1639825915/302231454903657293676544), (-5663641809/302231454903657293676544)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((150352915/1208925819614629174706176), (3697839215/4835703278458516698824704)), (35/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1352501817/77371252455336267181195264), (-3917780015/154742504910672534362390528)), (61/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1309979927/1237940039285380274899124224), (3024280869/4951760157141521099596496896)), (13/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (6909/1280)))⁻¹=value ((2662400/37103983), (-180480/5300569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((2662400/37103983), (-180480/5300569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3394980081/73786976294838206464), (-4330598839/73786976294838206464)), (21/36893488147419103232), by norm_num⟩
  | 1 => ⟨((1803633875/36893488147419103232), (433546901/147573952589676412928)), (65/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-451197489/36893488147419103232), (3698519013/295147905179352825856)), (13/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-510535227/1180591620717411303424), (-5301864887/1180591620717411303424)), (67/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((1833049703/2361183241434822606848), (2475871237/4722366482869645213696)), (65/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-1501417891/9444732965739290427392), (923539363/18889465931478580854784)), (111/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((1425274431/151115727451828646838272), (-1845252569/75557863725914323419136)), (87/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((2352674595/1208925819614629174706176), (3865027755/1208925819614629174706176)), (31/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-4758450463/9671406556917033397649408), (-463879491/9671406556917033397649408)), (165/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1575258283/38685626227668133590597632), (-880660935/19342813113834066795298816)), (103/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((481571893/309485009821345068724781056), (2152884817/309485009821345068724781056)), (245/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-113312659/154742504910672534362390528), (-744150195/2475880078570760549798248448)), (279/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((173861603/2475880078570760549798248448), (-917828681/19807040628566084398385987584)), (153/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((99/8), (6909/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/33182209), (-2947840/99546627)), 0, by norm_num⟩
  | 1 => ⟨((-18493104947200/9909530947077129), (6640893952000/3303176982359043)), 0, by norm_num⟩
  | 2 => ⟨((36923965/1099511627776), (-1686707811/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((314833435/1125899906842624), (528033205/140737488355328)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2343461343/36028797018963968), (-4439519311/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((4649084373/1152921504606846976), (3712173709/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-3404496345/18446744073709551616), (-457417725/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4131649645/590295810358705651712), (-309650801/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-262165979/1180591620717411303424), (2630313939/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1655137241/302231454903657293676544), (-2422333203/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1300433035/19342813113834066795298816), (6831026505/19342813113834066795298816)), (51/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-113996093/38685626227668133590597632), (-4018239859/309485009821345068724781056)), (41/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((2894495299/9903520314283042199192993792), (3932795725/9903520314283042199192993792)), (65/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (6909/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (6909/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (6909/1280)))⁻¹=value ((2252800/33182209), (-2947840/99546627)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/33182209), (-2947840/99546627))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-89682963/18446744073709551616), (-1547822297/590295810358705651712)), (17/295147905179352825856), by norm_num⟩
  | 1 => ⟨((4261845137/1180591620717411303424), (-1453557781/1180591620717411303424)), (27/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-1330603991/2361183241434822606848), (772199047/590295810358705651712)), (23/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-1535568365/9444732965739290427392), (-1628446113/4722366482869645213696)), (61/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((2979117241/37778931862957161709568), (1655030877/75557863725914323419136)), (121/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1865681001/151115727451828646838272), (319264419/37778931862957161709568)), (107/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((255219853/1208925819614629174706176), (-2909887745/1208925819614629174706176)), (169/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((308602141/1208925819614629174706176), (2362339137/9671406556917033397649408)), (31/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-3644642213/77371252455336267181195264), (1052465995/154742504910672534362390528)), (167/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((902034005/309485009821345068724781056), (-404281019/77371252455336267181195264)), (213/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((1436331727/4951760157141521099596496896), (3202450485/4951760157141521099596496896)), (257/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-193211329/2475880078570760549798248448), (-648888215/39614081257132168796771975168)), (37/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((1992393037/316912650057057350374175801344), (-922988233/158456325028528675187087900672)), (659/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1491766797/2199023255552), (-2397807357/1099511627776)), (1429/2199023255552), by norm_num⟩
  | 1 => ⟨((2323132615/1099511627776), (-3019103311/2199023255552)), (3099/2199023255552), by norm_num⟩
  | 2 => ⟨((5865719283/4398046511104), (76161709/549755813888)), (6881/4398046511104), by norm_num⟩
  | 3 => ⟨((726190201/2199023255552), (2779548357/8796093022208)), (5195/4398046511104), by norm_num⟩
  | 4 => ⟨((695212333/35184372088832), (3875029209/35184372088832)), (2987/4398046511104), by norm_num⟩
  | 5 => ⟨((-146147695/17592186044416), (5421650277/281474976710656)), (44565/140737488355328), by norm_num⟩
  | 6 => ⟨((-2846863021/1125899906842624), (2140379819/1125899906842624)), (70127/562949953421312), by norm_num⟩
  | 7 => ⟨((-3570442649/9007199254740992), (380446731/4503599627370496)), (191439/4503599627370496), by norm_num⟩
  | 8 => ⟨((-6697154293/144115188075855872), (-498277781/72057594037927936)), (462657/36028797018963968), by norm_num⟩
  | 9 => ⟨((-2620290451/576460752303423488), (-2677919163/1152921504606846976)), (4022255/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-3297650065/9223372036854775808), (-841412359/2305843009213693952)), (1990403/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-1552910243/73786976294838206464), (-758760993/18446744073709551616)), (14500735/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-251148167/295147905179352825856), (-279982709/73786976294838206464)), (12255677/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1491766797/2199023255552), (-2397807357/1099511627776)), (715/1099511627776), by norm_num⟩
  | 1 => ⟨((2323132615/1099511627776), (-3019103311/2199023255552)), (775/549755813888), by norm_num⟩
  | 2 => ⟨((5865719283/4398046511104), (76161709/549755813888)), (3441/2199023255552), by norm_num⟩
  | 3 => ⟨((726190201/2199023255552), (2779548357/8796093022208)), (10391/8796093022208), by norm_num⟩
  | 4 => ⟨((695212333/35184372088832), (3875029209/35184372088832)), (11949/17592186044416), by norm_num⟩
  | 5 => ⟨((-146147695/17592186044416), (5421650277/281474976710656)), (44571/140737488355328), by norm_num⟩
  | 6 => ⟨((-2846863021/1125899906842624), (2140379819/1125899906842624)), (35075/281474976710656), by norm_num⟩
  | 7 => ⟨((-3570442649/9007199254740992), (380446731/4503599627370496)), (383239/9007199254740992), by norm_num⟩
  | 8 => ⟨((-6697154293/144115188075855872), (-498277781/72057594037927936)), (1856393/144115188075855872), by norm_num⟩
  | 9 => ⟨((-2620290451/576460752303423488), (-2677919163/1152921504606846976)), (1017093/288230376151711744), by norm_num⟩
  | 10 => ⟨((-3297650065/9223372036854775808), (-841412359/2305843009213693952)), (8330547/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-1552910243/73786976294838206464), (-758760993/18446744073709551616)), (17452215/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-251148167/295147905179352825856), (-279982709/73786976294838206464)), (96246373/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile024Gamma
