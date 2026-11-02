/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile033Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/119855787), (-3549440/119855787)), 0, by norm_num⟩
  | 1 => ⟨((-2236677324800/1596156630821041), (25805848576000/14365409677389369)), 0, by norm_num⟩
  | 2 => ⟨((279741375/17592186044416), (-1323515173/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((88903709/140737488355328), (1417091017/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-508300305/9007199254740992), (-603430855/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((779254909/288230376151711744), (172407345/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-919691121/9223372036854775808), (8642981/2305843009213693952)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((219056969/73786976294838206464), (-58666173/36893488147419103232)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-628044189/9444732965739290427392), (870690457/9444732965739290427392)), (19/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((196992599/302231454903657293676544), (-1142636267/302231454903657293676544)), (7/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((350221405/9671406556917033397649408), (1202329747/9671406556917033397649408)), (21/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-909606075/309485009821345068724781056), (-1000980063/309485009821345068724781056)), (31/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((339278359/2475880078570760549798248448), (540507337/9903520314283042199192993792)), (45/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (8319/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (8319/1280)))⁻¹=value ((7270400/119855787), (-3549440/119855787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((7270400/119855787), (-3549440/119855787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((180898029/67108864), (243828803/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((3635200/119855787), (-1774720/119855787)), 0, by norm_num⟩
  | 2 => ⟨((-559169331200/1596156630821041), (6451462144000/14365409677389369)), 0, by norm_num⟩
  | 3 => ⟨((93247125/35184372088832), (-1764686897/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((88903709/1125899906842624), (1417091017/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-101660061/18014398509481984), (-120686171/18014398509481984)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((1039006545/4611686018427387904), (57469115/576460752303423488)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-1051075567/147573952589676412928), (19755385/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 8 => ⟨((219056969/1180591620717411303424), (-58666173/590295810358705651712)), (3/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-558261501/151115727451828646838272), (773947073/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((157594079/4835703278458516698824704), (-1828218027/9671406556917033397649408)), (23/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((63676619/38685626227668133590597632), (437210817/77371252455336267181195264)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-303202025/2475880078570760549798248448), (-333660021/2475880078570760549798248448)), (21/2475880078570760549798248448), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (177/20480)), 0, by norm_num⟩
  | 45 => ⟨((93705243953/4080638361600), (-707469/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-250713581042203/11491077626265600), (6696782206027/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((95911097/4294967296), (-369723305/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-398393753/17179869184), (373775561/34359738368)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((410024865/17179869184), (-48304829/4294967296)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-419882181/17179869184), (398014775/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((860399035/34359738368), (-25497957/2147483648)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-883006991/34359738368), (52252607/4294967296)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((226789649/8589934592), (-428892915/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-233148667/8589934592), (110132373/8589934592)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((959409975/34359738368), (-452816235/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-987796949/34359738368), (465772433/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((63620369/2147483648), (-119869873/8589934592)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-524978217/17179869184), (247010133/17179869184)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((271016729/8589934592), (-127368375/8589934592)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-280116311/8589934592), (525924879/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1159390409/34359738368), (-67934155/4294967296)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-300278851/8589934592), (70279033/4294967296)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((1245953351/34359738368), (-582331935/34359738368)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-1294265711/34359738368), (301960639/17179869184)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((673236099/17179869184), (-627172151/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1403062955/34359738368), (652283907/34359738368)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((1464613911/34359738368), (-679489129/34359738368)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-191475797/4294967296), (354530413/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((802726141/17179869184), (-370660803/17179869184)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-843263513/17179869184), (388327731/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((222026595/4294967296), (-407761551/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-234494519/4294967296), (214620525/8589934592)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((62110833/1073741824), (-113276719/4294967296)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-66038259/1073741824), (239889843/8589934592)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((1127915363/17179869184), (-509785085/17179869184)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-302378187/4294967296), (271894253/8589934592)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((1303801215/17179869184), (-582644971/17179869184)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-353495639/4294967296), (627471729/17179869184)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((386107855/4294967296), (-339878507/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-850642519/8589934592), (185381947/4294967296)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((946713809/8589934592), (-12744023/268435456)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-1067107773/8589934592), (226527691/4294967296)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((1222342645/8589934592), (-254779787/4294967296)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1429987435/8589934592), (145526775/2147483648)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((860863767/4294967296), (-339319187/4294967296)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-1080508183/4294967296), (406678891/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((361988483/1073741824), (-507213035/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1092332065/2147483648), (168339131/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1097101097/1073741824), (-62532249/268435456)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-165352017/2147483648), (243828803/536870912)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (8319/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (8319/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (8319/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((180898029/67108864), (243828803/536870912)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (8319/1280))) (z:=((-43/256), (8319/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((180898029/67108864), (243828803/536870912))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1059834453/33554432), (783101465/33554432)), (1/8388608), by norm_num⟩
  | 1 => ⟨((983885983/536870912), (15736145/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((37147067072000/4788469892463123), (-56403346648160/14365409677389369)), 0, by norm_num⟩
  | 3 => ⟨((-525233877/8796093022208), (713529605/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((82134161/281474976710656), (-242727909/140737488355328)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((96537983/9007199254740992), (1254358987/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-168015703/288230376151711744), (-701128695/1152921504606846976)), (55/1152921504606846976), by norm_num⟩
  | 7 => ⟨((362551235/18446744073709551616), (257777107/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1270132539/2361183241434822606848), (78421557/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((918434603/75557863725914323419136), (-610668443/75557863725914323419136)), (135/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-486007719/2417851639229258349412352), (847684913/2417851639229258349412352)), (367/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((101874509/154742504910672534362390528), (-883411963/77371252455336267181195264)), (987/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((642810655/4951760157141521099596496896), (749777767/2475880078570760549798248448)), (331/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((613141077/33554432), (565023871/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((715450527/536870912), (15736145/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((37147067072000/4788469892463123), (-56403346648160/14365409677389369)), 0, by norm_num⟩
  | 3 => ⟨((-525233877/8796093022208), (713529605/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((82134161/281474976710656), (-242727909/140737488355328)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((96537983/9007199254740992), (1254358987/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-168015703/288230376151711744), (-701128695/1152921504606846976)), (55/1152921504606846976), by norm_num⟩
  | 7 => ⟨((362551235/18446744073709551616), (257777107/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1270132539/2361183241434822606848), (78421557/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((918434603/75557863725914323419136), (-610668443/75557863725914323419136)), (135/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-486007719/2417851639229258349412352), (847684913/2417851639229258349412352)), (367/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((101874509/154742504910672534362390528), (-883411963/77371252455336267181195264)), (987/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((642810655/4951760157141521099596496896), (749777767/2475880078570760549798248448)), (331/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((986702737/536870912), 0), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((986702737/1073741824), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((321987769/16777216), (565023871/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((715450527/536870912), (15736145/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((37147067072000/4788469892463123), (-56403346648160/14365409677389369)), 0, by norm_num⟩
  | 3 => ⟨((-525233877/8796093022208), (713529605/8796093022208)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((82134161/281474976710656), (-242727909/140737488355328)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((96537983/9007199254740992), (1254358987/36028797018963968)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-168015703/288230376151711744), (-701128695/1152921504606846976)), (55/1152921504606846976), by norm_num⟩
  | 7 => ⟨((362551235/18446744073709551616), (257777107/36893488147419103232)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-1270132539/2361183241434822606848), (78421557/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((918434603/75557863725914323419136), (-610668443/75557863725914323419136)), (135/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-486007719/2417851639229258349412352), (847684913/2417851639229258349412352)), (367/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((101874509/154742504910672534362390528), (-883411963/77371252455336267181195264)), (987/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((642810655/4951760157141521099596496896), (749777767/2475880078570760549798248448)), (331/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4473354649600/1596156630821041), (-51611697152000/14365409677389369)), 0, by norm_num⟩
  | 1 => ⟨((-279741375/4398046511104), (1323515173/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-266711127/70368744177664), (-531409131/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((508300305/1125899906842624), (603430855/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-974068637/36028797018963968), (-431018363/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((689768341/576460752303423488), (-25928943/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-5989839/144115188075855872), (410663211/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((314022095/295147905179352825856), (-435345229/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-110808337/9444732965739290427392), (1285465801/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-109444189/151115727451828646838272), (-187864023/75557863725914323419136)), (31/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((625354177/9671406556917033397649408), (344086897/4835703278458516698824704)), (25/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-1017835077/309485009821345068724781056), (-405380503/309485009821345068724781056)), (37/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((639136125/4951760157141521099596496896), (-48119271/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((279741375/4398046511104), (-1323515173/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((266711127/35184372088832), (531409131/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-381225229/281474976710656), (-452573141/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((974068637/9007199254740992), (431018363/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1724420853/288230376151711744), (64822357/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((17969517/72057594037927936), (-615994817/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-274769333/36893488147419103232), (761854151/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((110808337/1180591620717411303424), (-642732901/1180591620717411303424)), (15/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((246249425/37778931862957161709568), (105673513/4722366482869645213696)), (13/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-781692721/1208925819614629174706176), (-860217243/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((43735101/1208925819614629174706176), (34837387/2417851639229258349412352)), (35/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-239676047/154742504910672534362390528), (144357813/1237940039285380274899124224)), (7/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((65353231/1237940039285380274899124224), (-76462523/2475880078570760549798248448)), (11/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-88903709/17592186044416), (-1417091017/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((508300305/281474976710656), (603430855/281474976710656)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((-974068637/4503599627370496), (-215509181/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((574806951/36028797018963968), (-43214905/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((-29949195/36028797018963968), (256664507/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 5 => ⟨((274769333/9223372036854775808), (-761854151/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-129276393/295147905179352825856), (749855051/295147905179352825856)), (15/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-328332567/9444732965739290427392), (-1127184139/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((586269541/151115727451828646838272), (161290733/37778931862957161709568)), (7/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-72891835/302231454903657293676544), (-232249247/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((878812173/77371252455336267181195264), (-132327995/154742504910672534362390528)), (41/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-1045651697/2475880078570760549798248448), (76462523/309485009821345068724781056)), (17/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((453137319/39614081257132168796771975168), (-680716649/39614081257132168796771975168)), (29/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-508300305/562949953421312), (-603430855/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((974068637/4503599627370496), (431018363/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1724420853/72057594037927936), (32411179/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((29949195/18014398509481984), (-256664507/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 4 => ⟨((-686923333/9223372036854775808), (952317689/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 5 => ⟨((96957295/73786976294838206464), (-1124782577/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 6 => ⟨((71822749/590295810358705651712), (986286121/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-586269541/37778931862957161709568), (-161290733/9444732965739290427392)), (3/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((656026515/604462909807314587353088), (522560805/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-68657201/1208925819614629174706176), (82704997/19342813113834066795298816)), (23/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((359442771/154742504910672534362390528), (-420543877/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-339852989/4951760157141521099596496896), (510537487/4951760157141521099596496896)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((234502261/316912650057057350374175801344), (-437690409/79228162514264337593543950336)), (31/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-779254909/9007199254740992), (-172407345/4503599627370496)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((689768341/36028797018963968), (-25928943/36028797018963968)), (11/72057594037927936), by norm_num⟩
  | 2 => ⟨((-17969517/9007199254740992), (615994817/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 3 => ⟨((274769333/2305843009213693952), (-761854151/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-96957295/36893488147419103232), (1124782577/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 5 => ⟨((-86187299/295147905179352825856), (-591771673/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((820777357/18889465931478580854784), (903228105/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-131205303/37778931862957161709568), (-104512161/75557863725914323419136)), (19/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((1977327389/9671406556917033397649408), (-148868995/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-359442771/38685626227668133590597632), (420543877/77371252455336267181195264)), (5/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((23364893/77371252455336267181195264), (-140397809/309485009821345068724781056)), (37/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-140701357/39614081257132168796771975168), (525228491/19807040628566084398385987584)), (35/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-127917175/316912650057057350374175801344), (-769386345/633825300114114700748351602688)), (61/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-919691121/144115188075855872), (8642981/36028797018963968)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((5989839/4503599627370496), (-410663211/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 2 => ⟨((-274769333/2305843009213693952), (761854151/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 3 => ⟨((129276393/36893488147419103232), (-749855051/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 4 => ⟨((71822749/147573952589676412928), (493143061/295147905179352825856)), (15/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-410388679/4722366482869645213696), (-903228105/9444732965739290427392)), (5/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((306145707/37778931862957161709568), (243861709/75557863725914323419136)), (25/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-1318218259/2417851639229258349412352), (99245997/2417851639229258349412352)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((134791039/4835703278458516698824704), (-630815815/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-623063813/618970019642690137449562112), (467992697/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((128976243/9903520314283042199192993792), (-240729725/2475880078570760549798248448)), (31/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((127917175/79228162514264337593543950336), (1538772691/316912650057057350374175801344)), (15/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-919286521/5070602400912917605986812821504), (-938263143/5070602400912917605986812821504)), (55/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-219056969/576460752303423488), (58666173/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((314022095/4611686018427387904), (-435345229/4611686018427387904)), (17/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-110808337/36893488147419103232), (642732901/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-328332567/590295810358705651712), (-1127184139/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 4 => ⟨((586269541/4722366482869645213696), (161290733/1180591620717411303424)), (17/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-1049642425/75557863725914323419136), (-104512161/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1318218259/1208925819614629174706176), (-99245997/1208925819614629174706176)), (1/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-616187607/9671406556917033397649408), (90116545/2417851639229258349412352)), (19/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((801082045/309485009821345068724781056), (-9401639/2417851639229258349412352)), (43/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-1439467/38685626227668133590597632), (1375598429/4951760157141521099596496896)), (47/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-6281647/1237940039285380274899124224), (-1209035685/79228162514264337593543950336)), (49/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((196989969/316912650057057350374175801344), (804225551/1267650600228229401496703205376)), (49/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-453554355/10141204801825835211973625643008), (-322355609/20282409603651670423947251286016)), (47/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-628044189/36893488147419103232), (870690457/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 1 => ⟨((110808337/73786976294838206464), (-642732901/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 2 => ⟨((246249425/590295810358705651712), (105673513/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-586269541/4722366482869645213696), (-161290733/1180591620717411303424)), (21/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((656026515/37778931862957161709568), (522560805/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-988663695/604462909807314587353088), (148868995/1208925819614629174706176)), (55/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((134791039/1208925819614629174706176), (-630815815/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-801082045/154742504910672534362390528), (9401639/1208925819614629174706176)), (49/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((12955203/154742504910672534362390528), (-193443529/309485009821345068724781056)), (29/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((31408235/2475880078570760549798248448), (1511294607/39614081257132168796771975168)), (33/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-541722415/316912650057057350374175801344), (-276452533/158456325028528675187087900672)), (37/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((680331533/5070602400912917605986812821504), (483533413/10141204801825835211973625643008)), (75/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-1291422843/162259276829213363391578010288128), (36546993/40564819207303340847894502572032)), (75/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-196992599/590295810358705651712), (1142636267/590295810358705651712)), (7/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-109444189/590295810358705651712), (-1502912185/2361183241434822606848)), (45/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((781692721/9444732965739290427392), (860217243/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-72891835/4722366482869645213696), (-464498493/75557863725914323419136)), (41/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((68657201/37778931862957161709568), (-82704997/604462909807314587353088)), (19/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-359442771/2417851639229258349412352), (420543877/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((623063813/77371252455336267181195264), (-935985393/77371252455336267181195264)), (23/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-1439467/9671406556917033397649408), (1375598429/1237940039285380274899124224)), (61/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-31408235/1237940039285380274899124224), (-1511294607/19807040628566084398385987584)), (75/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((300956897/79228162514264337593543950336), (614338963/158456325028528675187087900672)), (45/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-415758159/1267650600228229401496703205376), (-295492641/2535301200456458802993406410752)), (51/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((430474281/20282409603651670423947251286016), (-194917297/81129638414606681695789005144064)), (55/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-86342551/81129638414606681695789005144064), (219857055/324518553658426726783156020576256)), (57/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((350221405/9444732965739290427392), (1202329747/9444732965739290427392)), (21/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-625354177/18889465931478580854784), (-344086897/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((43735101/4722366482869645213696), (34837387/9444732965739290427392)), (63/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-1757624345/1208925819614629174706176), (33081999/302231454903657293676544)), (77/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((718885541/4835703278458516698824704), (-420543877/4835703278458516698824704)), (39/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-23364893/2417851639229258349412352), (1123182473/77371252455336267181195264)), (33/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((128976243/618970019642690137449562112), (-240729725/154742504910672534362390528)), (13/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((6281647/154742504910672534362390528), (1209035685/9903520314283042199192993792)), (73/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-541722415/79228162514264337593543950336), (-276452533/39614081257132168796771975168)), (3/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((415758159/633825300114114700748351602688), (295492641/1267650600228229401496703205376)), (59/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-1894086837/40564819207303340847894502572032), (107204513/20282409603651670423947251286016)), (137/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((414444245/162259276829213363391578010288128), (-131914233/81129638414606681695789005144064)), (39/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-508256441/5192296858534827628530496329220096), (829463897/5192296858534827628530496329220096)), (83/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1817600/359567361), (-887360/359567361)), 0, by norm_num⟩
  | 1 => ⟨((-559169331200/4788469892463123), (6451462144000/43096229032168107)), 0, by norm_num⟩
  | 2 => ⟨((93247125/70368744177664), (-1764686897/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((237076557/4503599627370496), (944727345/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-169433435/36028797018963968), (-804574473/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((1039006545/4611686018427387904), (57469115/576460752303423488)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-306563707/36893488147419103232), (46095899/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1168303835/4722366482869645213696), (-19555391/147573952589676412928)), (17/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-209348063/37778931862957161709568), (1160920609/151115727451828646838272)), (13/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((262656799/4835703278458516698824704), (-1523515023/4835703278458516698824704)), (19/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((466961873/154742504910672534362390528), (1603106329/154742504910672534362390528)), (57/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-303202025/1237940039285380274899124224), (-333660021/1237940039285380274899124224)), (21/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((904742291/79228162514264337593543950336), (360338225/79228162514264337593543950336)), (61/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((322072577/16777216), (70617633/4194304)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1430775669/1073741824), (125969529/536870912)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1066379497/137438953472), (-540492423/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-524770837/8796093022208), (89421847/1099511627776)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((161620925/562949953421312), (-974054505/562949953421312)), (11/562949953421312), by norm_num⟩
  | 5 => ⟨((394269171/36028797018963968), (1257950807/36028797018963968)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-42602683/72057594037927936), (-700768571/1152921504606846976)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((1468459687/73786976294838206464), (252888259/36893488147419103232)), (73/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1283216793/2361183241434822606848), (174982499/2361183241434822606848)), (95/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((922538615/75557863725914323419136), (-634473365/75557863725914323419136)), (17/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-29919465/151115727451828646838272), (872733449/2417851639229258349412352)), (369/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((3998391/9671406556917033397649408), (-1808531429/154742504910672534362390528)), (991/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((87419631/618970019642690137449562112), (761038337/2475880078570760549798248448)), (665/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6216475/35184372088832), (941166345/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-94830623/4503599627370496), (-755781875/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((33886687/9007199254740992), (321829789/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-692671031/2305843009213693952), (-306501947/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1226254829/73786976294838206464), (-23047949/36893488147419103232)), (7/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-817812685/1180591620717411303424), (438040759/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((781566103/37778931862957161709568), (-67720369/2361183241434822606848)), (3/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-315188159/1208925819614629174706176), (914109015/604462909807314587353088)), (23/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-87555351/4835703278458516698824704), (-300582437/4835703278458516698824704)), (5/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((555870379/309485009821345068724781056), (611710039/309485009821345068724781056)), (17/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-995216521/9903520314283042199192993792), (-24773253/618970019642690137449562112)), (13/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((1363490401/316912650057057350374175801344), (-102654445/316912650057057350374175801344)), (41/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-743574539/5070602400912917605986812821504), (217493399/2535301200456458802993406410752)), (33/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161036287/8388608), (141235273/8388608)), (1/4194304), by norm_num⟩
  | 1 => ⟨((715387823/536870912), (31492371/134217728)), (3/536870912), by norm_num⟩
  | 2 => ⟨((533190007/68719476736), (-540491809/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-524773479/8796093022208), (715373607/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((161630281/562949953421312), (-974054857/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((394244213/36028797018963968), (1257964175/36028797018963968)), (35/36028797018963968), by norm_num⟩
  | 6 => ⟨((-170404769/288230376151711744), (-350400819/576460752303423488)), (57/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1468440449/73786976294838206464), (63236013/9223372036854775808)), (147/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1283259545/2361183241434822606848), (87417865/1180591620717411303424)), (191/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((461337163/37778931862957161709568), (-317162011/37778931862957161709568)), (273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-478954413/2417851639229258349412352), (436318339/1208925819614629174706176)), (185/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((64640023/154742504910672534362390528), (-1808581553/154742504910672534362390528)), (31/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((174657725/1237940039285380274899124224), (761250733/2475880078570760549798248448)), (333/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-413094851/576460752303423488), (-245203649/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((791624035/4611686018427387904), (350287939/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-700717045/36893488147419103232), (52681027/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 3 => ⟨((97358653/73786976294838206464), (-417181675/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-279130751/4722366482869645213696), (386973537/4722366482869645213696)), (9/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((315188159/302231454903657293676544), (-914109015/151115727451828646838272)), (9/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((466961873/4835703278458516698824704), (801553165/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-952920651/77371252455336267181195264), (-524322891/38685626227668133590597632)), (21/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((1066303415/1237940039285380274899124224), (424684337/1237940039285380274899124224)), (5/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-1785523145/39614081257132168796771975168), (16803555/4951760157141521099596496896)), (39/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((584237139/316912650057057350374175801344), (-683550683/633825300114114700748351602688)), (35/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-552395969/10141204801825835211973625643008), (829826011/10141204801825835211973625643008)), (31/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((190579615/324518553658426726783156020576256), (-1422841203/324518553658426726783156020576256)), (13/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161036287/8388608), (141235273/8388608)), (9/33554432), by norm_num⟩
  | 1 => ⟨((715387823/536870912), (31492371/134217728)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1066380011/137438953472), (-540491809/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-524773467/8796093022208), (715373601/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((20203781/70368744177664), (-974054811/562949953421312)), (13/562949953421312), by norm_num⟩
  | 5 => ⟨((394244251/36028797018963968), (1257963957/36028797018963968)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-681618965/1152921504606846976), (-87600157/144115188075855872)), (29/576460752303423488), by norm_num⟩
  | 7 => ⟨((367109885/18446744073709551616), (3952243/576460752303423488)), (37/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1283257511/2361183241434822606848), (43709135/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((115333865/9444732965739290427392), (-317161883/37778931862957161709568)), (137/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-119737489/604462909807314587353088), (436317035/1208925819614629174706176)), (371/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((32315797/77371252455336267181195264), (-1808568891/154742504910672534362390528)), (993/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((43664613/309485009821345068724781056), (380619939/1237940039285380274899124224)), (667/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1121147271/295147905179352825856), (-21072411/147573952589676412928)), (5/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-233660767/295147905179352825856), (250309005/590295810358705651712)), (13/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((334956901/4722366482869645213696), (-928736489/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-157594079/75557863725914323419136), (1828218029/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-350221405/1208925819614629174706176), (-1202329749/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((250141671/4835703278458516698824704), (1101078071/19342813113834066795298816)), (25/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-1492824781/309485009821345068724781056), (-594558071/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((803485415/2475880078570760549798248448), (-30246399/1237940039285380274899124224)), (35/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-1314533561/79228162514264337593543950336), (768994517/79228162514264337593543950336)), (19/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((379772229/633825300114114700748351602688), (-570505383/633825300114114700748351602688)), (5/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-78614091/10141204801825835211973625643008), (146730499/2535301200456458802993406410752)), (39/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-311874255/324518553658426726783156020576256), (-937918593/324518553658426726783156020576256)), (19/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((280163511/2596148429267413814265248164610048), (571893725/5192296858534827628530496329220096)), (35/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161036287/8388608), (141235273/8388608)), (5/16777216), by norm_num⟩
  | 1 => ⟨((715387823/536870912), (31492371/134217728)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1066380011/137438953472), (-540491809/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-524773467/8796093022208), (715373601/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((20203781/70368744177664), (-243513703/140737488355328)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((394244253/36028797018963968), (1257963959/36028797018963968)), (37/36028797018963968), by norm_num⟩
  | 6 => ⟨((-681618971/1152921504606846976), (-350400629/576460752303423488)), (59/1152921504606846976), by norm_num⟩
  | 7 => ⟨((367109891/18446744073709551616), (252943551/36893488147419103232)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-641628775/1180591620717411303424), (174836563/2361183241434822606848)), (193/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((922670965/75557863725914323419136), (-317161917/37778931862957161709568)), (275/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-478949975/2417851639229258349412352), (436317105/1208925819614629174706176)), (93/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((64631445/154742504910672534362390528), (-904284669/77371252455336267181195264)), (497/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((349317171/2475880078570760549798248448), (761240151/2475880078570760549798248448)), (167/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-270672243/18889465931478580854784), (750494131/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((95511563/75557863725914323419136), (-1108010927/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((424510793/1208925819614629174706176), (1457369391/1208925819614629174706176)), (9/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-1010673417/9671406556917033397649408), (-1112200071/9671406556917033397649408)), (19/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((141365983/9671406556917033397649408), (450422781/77371252455336267181195264)), (33/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((-1704363003/1237940039285380274899124224), (16039757/154742504910672534362390528)), (3/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((929468175/9903520314283042199192993792), (-543733497/9903520314283042199192993792)), (35/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-690494961/158456325028528675187087900672), (518641257/79228162514264337593543950336)), (43/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((178668389/2535301200456458802993406410752), (-333478407/633825300114114700748351602688)), (51/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((433158689/40564819207303340847894502572032), (162833089/5070602400912917605986812821504)), (29/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-233469593/162259276829213363391578010288128), (-59572263/40564819207303340847894502572032)), (1/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((36650857/324518553658426726783156020576256), (416783009/10384593717069655257060992658440192)), (65/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-69571601/10384593717069655257060992658440192), (126007141/166153499473114484112975882535043072)), (33/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161036287/8388608), (141235273/8388608)), (11/33554432), by norm_num⟩
  | 1 => ⟨((715387823/536870912), (31492371/134217728)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1066380011/137438953472), (-540491809/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-524773467/8796093022208), (715373601/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((20203781/70368744177664), (-243513703/140737488355328)), (15/562949953421312), by norm_num⟩
  | 5 => ⟨((394244253/36028797018963968), (1257963959/36028797018963968)), (19/18014398509481984), by norm_num⟩
  | 6 => ⟨((-681618971/1152921504606846976), (-350400629/576460752303423488)), (15/288230376151711744), by norm_num⟩
  | 7 => ⟨((367109891/18446744073709551616), (252943551/36893488147419103232)), (75/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-641628775/1180591620717411303424), (87418281/1180591620717411303424)), (97/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((461335483/37778931862957161709568), (-79290479/9444732965739290427392)), (69/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-239474989/1208925819614629174706176), (436317103/1208925819614629174706176)), (373/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((32315731/77371252455336267181195264), (-452142333/38685626227668133590597632)), (995/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((174658577/1237940039285380274899124224), (761240153/2475880078570760549798248448)), (669/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-343838193/4835703278458516698824704), (-1180415823/4835703278458516698824704)), (21/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((613956335/9671406556917033397649408), (168907747/2417851639229258349412352)), (9/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((-85875951/4835703278458516698824704), (-547238931/77371252455336267181195264)), (63/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((431397375/154742504910672534362390528), (-129916157/618970019642690137449562112)), (19/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-11027859/38685626227668133590597632), (412878953/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((183512315/9903520314283042199192993792), (-17229861/618970019642690137449562112)), (33/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((-63312747/158456325028528675187087900672), (472684265/158456325028528675187087900672)), (103/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-394698005/5070602400912917605986812821504), (-1186999537/5070602400912917605986812821504)), (73/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((16620277/1267650600228229401496703205376), (271413849/20282409603651670423947251286016)), (3/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((-102045115/81129638414606681695789005144064), (-18131683/40564819207303340847894502572032)), (59/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((1859564797/20769187434139310514121985316880384), (-26312645/2596148429267413814265248164610048)), (135/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-813780987/166153499473114484112975882535043072), (259019871/83076749736557242056487941267521536)), (39/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((31187053/166153499473114484112975882535043072), (-814345907/2658455991569831745807614120560689152)), (41/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((161036287/8388608), (141235273/8388608)), (3/8388608), by norm_num⟩
  | 1 => ⟨((715387823/536870912), (31492371/134217728)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1066380011/137438953472), (-540491809/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-524773467/8796093022208), (715373601/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((20203781/70368744177664), (-243513703/140737488355328)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((394244253/36028797018963968), (1257963959/36028797018963968)), (39/36028797018963968), by norm_num⟩
  | 6 => ⟨((-681618971/1152921504606846976), (-350400629/576460752303423488)), (61/1152921504606846976), by norm_num⟩
  | 7 => ⟨((367109891/18446744073709551616), (252943551/36893488147419103232)), (151/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-641628775/1180591620717411303424), (87418281/1180591620717411303424)), (195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((461335483/37778931862957161709568), (-79290479/9444732965739290427392)), (277/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-239474989/1208925819614629174706176), (436317103/1208925819614629174706176)), (187/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((64631461/154742504910672534362390528), (-452142333/38685626227668133590597632)), (249/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((174658577/1237940039285380274899124224), (95155019/309485009821345068724781056)), (335/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-195058441360151/2097152), (-823944627479535/4194304)), (938051439/4194304), by norm_num⟩
  | 1 => ⟨((-155691449/2), (-1134350881/4)), (707/2), by norm_num⟩
  | 2 => ⟨((-80357755/4), (-398466793/2)), (2251/8), by norm_num⟩
  | 3 => ⟨(5534690, (-730589005/8)), (301/2), by norm_num⟩
  | 4 => ⟨((216046439/32), (-986342625/32)), (1949/32), by norm_num⟩
  | 5 => ⟨((200274437/64), (-1047499373/128)), (2547/128), by norm_num⟩
  | 6 => ⟨((509632769/512), (-455864887/256)), (2799/512), by norm_num⟩
  | 7 => ⟨((507344835/2048), (-668198547/2048)), (665/512), by norm_num⟩
  | 8 => ⟨((419165339/8192), (-839579551/16384)), (2231/8192), by norm_num⟩
  | 9 => ⟨((297431389/32768), (-456993425/65536)), (3355/65536), by norm_num⟩
  | 10 => ⟨((370874975/262144), (-108129621/131072)), (4581/524288), by norm_num⟩
  | 11 => ⟨((826080067/4194304), (-176782375/2097152)), (717/524288), by norm_num⟩
  | 12 => ⟨((207988085/8388608), (-60793667/8388608)), (6641/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804491015396041/5070602400912917605986812821504), (-1311078214487/5070602400912917605986812821504)), (465851/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((226516414517511/79228162514264337593543950336), (-3212126370715/633825300114114700748351602688)), (572497/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1927311910665099/39614081257132168796771975168), (-1811270728585/19807040628566084398385987584)), (161465/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1929470404970411/2475880078570760549798248448), (-3856659827417/2475880078570760549798248448)), (343875/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((905588141546535/77371252455336267181195264), (-966323019117/38685626227668133590597632)), (689453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((396770526765469/2417851639229258349412352), (-908227247859/2417851639229258349412352)), (324089/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1291668558944995/604462909807314587353088), (-797005934943/151115727451828646838272)), (568977/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((970650656882067/37778931862957161709568), (-2598953664333/37778931862957161709568)), (464009/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((668870570596657/2361183241434822606848), (-3913693999181/4722366482869645213696)), (349515/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((419209782830069/147573952589676412928), (-5406256520869/590295810358705651712)), (483047/295147905179352825856), by norm_num⟩
  | 8 => ⟨((473221147753317/18446744073709551616), (-6795429947297/73786976294838206464)), (1215057/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1900979577146753/9223372036854775808), (-7696928708435/9223372036854775808)), (1377247/9223372036854775808), by norm_num⟩
  | 6 => ⟨((836262640438941/576460752303423488), (-3881278116861/576460752303423488)), (695125/576460752303423488), by norm_num⟩
  | 5 => ⟨((631819674466459/72057594037927936), (-6866816974089/144115188075855872)), (1231261/144115188075855872), by norm_num⟩
  | 4 => ⟨((1595904128450721/36028797018963968), (-10451279853761/36028797018963968)), (938445/18014398509481984), by norm_num⟩
  | 3 => ⟨((1620791935285819/9007199254740992), (-6666381726805/4503599627370496)), (2399557/9007199254740992), by norm_num⟩
  | 2 => ⟨((1247335604365157/2251799813685248), (-13744540960063/2251799813685248)), (1240827/1125899906842624), by norm_num⟩
  | 1 => ⟨((328188766738523/281474976710656), (-2709707059921/140737488355328)), (983659/281474976710656), by norm_num⟩
  | 0 => ⟨((759491749974133/562949953421312), (-47792524285973/1125899906842624)), (8760689/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((759491749974133/562949953421312), (-47792524285973/1125899906842624)), (33419376377585982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2047275014171975/1125899906842624), (-128956500253831/1125899906842624)), (12191171/562949953421312), by norm_num⟩
  | 2 => ⟨((926970767855005/281474976710656), (-234487470227345/562949953421312)), (11782047/140737488355328), by norm_num⟩
  | 3 => ⟨((375490177188761/35184372088832), (-193057152778859/70368744177664)), (21854491/35184372088832), by norm_num⟩
  | 4 => ⟨((233901977085575/2199023255552), (-515079992911833/8796093022208)), (146595339/8796093022208), by norm_num⟩
  | 5 => ⟨((541837471827655/68719476736), (-6687885173401/536870912)), (377767321/68719476736), by norm_num⟩
  | 6 => ⟨((-195058441360151/2097152), (-823944627479535/4194304)), (938051439/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((161036287/8388608), (141235273/8388608)), (3/8388608), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((716800/24009387), (-3549440/24009387)), 0, by norm_num⟩
  | 1 => ⟨((2014120345600/192150221371923), (2544238592000/576450664115769)), 0, by norm_num⟩
  | 2 => ⟨((-265375699/549755813888), (779468173/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-397549993/8796093022208), (-203469837/4398046511104)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((576231885/140737488355328), (-745965227/281474976710656)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((303493427/2251799813685248), (770583419/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-491921547/18014398509481984), (174890767/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((28140475/576460752303423488), (-602673235/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 8 => ⟨((88676439/576460752303423488), (321166143/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-179677415/36893488147419103232), (800656061/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-861094907/1180591620717411303424), (-616231867/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((934471461/18889465931478580854784), (-435611239/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((807191877/302231454903657293676544), (1313267233/302231454903657293676544)), (41/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (8319/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (8319/1280)))⁻¹=value ((716800/24009387), (-3549440/24009387)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((716800/24009387), (-3549440/24009387))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3788800/77967361), (-10648320/77967361)), 0, by norm_num⟩
  | 1 => ⟨((49515856691200/6078909381304321), (40344354816000/6078909381304321)), 0, by norm_num⟩
  | 2 => ⟨((-357957085/549755813888), (108570493/274877906944)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-196176223/17592186044416), (-951032903/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((1115356479/281474976710656), (155380533/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-301685433/2251799813685248), (1158224857/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1030902905/72057594037927936), (-69344199/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((201626325/144115188075855872), (-173756893/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 8 => ⟨((33077981/4611686018427387904), (127035039/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 9 => ⟨((-284024739/36893488147419103232), (-40350641/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 10 => ⟨((397180765/1180591620717411303424), (-557900179/1180591620717411303424)), (37/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((455150575/18889465931478580854784), (650844661/18889465931478580854784)), (7/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-888051267/302231454903657293676544), (244273367/302231454903657293676544)), (43/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (8319/1280)))⁻¹=value ((3788800/77967361), (-10648320/77967361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3788800/77967361), (-10648320/77967361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35079761100800/1871948543617707), (-21080834048000/1871948543617707)), 0, by norm_num⟩
  | 1 => ⟨((642250161/274877906944), (-611094135/274877906944)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((185162771/1099511627776), (1380744803/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-598923763/17592186044416), (274307109/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((9276823/70368744177664), (-1802691519/562949953421312)), (7/562949953421312), by norm_num⟩
  | 5 => ⟨((1210357719/4503599627370496), (191470991/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-234195821/18014398509481984), (729644359/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((-97295603/72057594037927936), (-214458171/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((676333531/4611686018427387904), (-86889271/1152921504606846976)), (21/9223372036854775808), by norm_num⟩
  | 9 => ⟨((208694647/73786976294838206464), (7516083/576460752303423488)), (9/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-1258275671/1180591620717411303424), (-7291461/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 11 => ⟨((479320885/18889465931478580854784), (-761033569/9444732965739290427392)), (11/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((211905393/37778931862957161709568), (534496933/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((53/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5427200/87183361), (-10648320/87183361)), 0, by norm_num⟩
  | 1 => ⟨((41966109491200/7600938435256321), (57790562304000/7600938435256321)), 0, by norm_num⟩
  | 2 => ⟨((-1398923593/2199023255552), (221051407/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((240339989/17592186044416), (-1476967723/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((601879919/281474976710656), (301301379/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-888539243/4503599627370496), (35999579/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((161094949/72057594037927936), (-252902971/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((454108327/576460752303423488), (165297839/288230376151711744)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1098342659/18446744073709551616), (69767485/2305843009213693952)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1621707/295147905179352825856), (-337785575/73786976294838206464)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((1319388845/4722366482869645213696), (674457865/4722366482869645213696)), (39/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-329017605/18889465931478580854784), (476644019/37778931862957161709568)), (15/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-138023525/604462909807314587353088), (-1760668421/1208925819614629174706176)), (45/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (8319/1280)))⁻¹=value ((5427200/87183361), (-10648320/87183361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5427200/87183361), (-10648320/87183361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-349368907/137438953472), (436446539/274877906944)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-79123403/549755813888), (-690955173/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((25201893/274877906944), (171439457/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-324815101/70368744177664), (1398810383/140737488355328)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-119092317/140737488355328), (-227061767/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((462594671/4503599627370496), (-487286243/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((127607285/72057594037927936), (778592009/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1130761797/1152921504606846976), (-44930805/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((184334943/4611686018427387904), (-358081135/4611686018427387904)), (13/9223372036854775808), by norm_num⟩
  | 9 => ⟨((777149551/147573952589676412928), (392837807/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-1325609225/2361183241434822606848), (167045739/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-152423647/18889465931478580854784), (-483647447/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1257141323/302231454903657293676544), (192276697/302231454903657293676544)), (3/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((69/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2355200/33225387), (-3549440/33225387)), 0, by norm_num⟩
  | 1 => ⟨((1175259545600/367975447099923), (8359641088000/1103926341299769)), 0, by norm_num⟩
  | 2 => ⟨((-1138409271/2199023255552), (-215058355/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((414685101/17592186044416), (-106370769/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((256941019/562949953421312), (297844251/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-581948819/4503599627370496), (-456021027/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((1049758967/144115188075855872), (-736103175/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((16898131/1152921504606846976), (164323945/288230376151711744)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-1142658973/36893488147419103232), (-716601011/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1260415165/590295810358705651712), (-142545263/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-227466151/9444732965739290427392), (700266747/4722366482869645213696)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-1067949957/151115727451828646838272), (-494310443/75557863725914323419136)), (75/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1450526071/2417851639229258349412352), (-352074005/2417851639229258349412352)), (27/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (8319/1280)))⁻¹=value ((2355200/33225387), (-3549440/33225387)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((2355200/33225387), (-3549440/33225387))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-46483249/4398046511104), (1689333201/4398046511104)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-857427603/8796093022208), (-95325509/2199023255552)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((234160949/17592186044416), (-898895525/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((266036133/281474976710656), (1329337875/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-1377163781/4503599627370496), (34527/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((444574053/36028797018963968), (-1122009763/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((180571315/72057594037927936), (337173007/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1383332677/4611686018427387904), (667112043/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-23582351/9223372036854775808), (-17826195/576460752303423488)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((792305325/295147905179352825856), (457039547/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-344887433/2361183241434822606848), (925496921/4722366482869645213696)), (17/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-214089889/18889465931478580854784), (-661737607/37778931862957161709568)), (29/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1027664877/604462909807314587353088), (-232014977/604462909807314587353088)), (3/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((85/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8704000/115445761), (-10648320/115445761)), 0, by norm_num⟩
  | 1 => ⟨((18813551411200/13327723732869121), (92682977280000/13327723732869121)), 0, by norm_num⟩
  | 2 => ⟨((-411137493/1099511627776), (-433321925/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((407853243/17592186044416), (-43173635/4398046511104)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-118569821/281474976710656), (405113887/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-113707097/2251799813685248), (-165919671/2251799813685248)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((382028381/72057594037927936), (64688459/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1017159699/4611686018427387904), (131193601/576460752303423488)), (19/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-40236619/18446744073709551616), (-1383597951/73786976294838206464)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1118022643/1180591620717411303424), (357883283/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-601251371/9444732965739290427392), (196630197/9444732965739290427392)), (51/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((108778725/75557863725914323419136), (-562257889/151115727451828646838272)), (69/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((141832211/1208925819614629174706176), (499664185/2417851639229258349412352)), (47/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (8319/1280)))⁻¹=value ((8704000/115445761), (-10648320/115445761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8704000/115445761), (-10648320/115445761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((76156847/2199023255552), (526616987/17592186044416)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-493769915/35184372088832), (217843493/35184372088832)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((38731713/562949953421312), (-1729061275/562949953421312)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((964040959/2251799813685248), (236231621/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-880358637/18014398509481984), (180326047/4503599627370496)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-140256041/72057594037927936), (-1044733445/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((936670381/1152921504606846976), (148459695/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-422781323/9223372036854775808), (20518433/288230376151711744)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-339429379/73786976294838206464), (-1017256131/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((225824079/295147905179352825856), (-334161595/2361183241434822606848)), (13/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-288105363/18889465931478580854784), (1300911783/18889465931478580854784)), (3/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-766355603/151115727451828646838272), (-540213619/151115727451828646838272)), (43/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((271293449/604462909807314587353088), (-344388973/1208925819614629174706176)), (9/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((101/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10342400/134492161), (-10648320/134492161)), 0, by norm_num⟩
  | 1 => ⟨((3210740531200/18088141370449921), (110129184768000/18088141370449921)), 0, by norm_num⟩
  | 2 => ⟨((-272514323/1099511627776), (-499340665/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((325789797/17592186044416), (-38025029/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-753530207/1125899906842624), (872199305/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-88876347/18014398509481984), (-1013856257/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((87105899/36028797018963968), (283713879/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-394051955/2305843009213693952), (92299033/4611686018427387904)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((213188819/36893488147419103232), (-1111925165/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((179674341/2361183241434822606848), (38255735/73786976294838206464)), (35/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-221481485/9444732965739290427392), (-639309573/37778931862957161709568)), (45/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((949954153/604462909807314587353088), (-41959733/151115727451828646838272)), (57/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-119525229/2417851639229258349412352), (88118691/1208925819614629174706176)), (9/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (8319/1280)))⁻¹=value ((10342400/134492161), (-10648320/134492161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10342400/134492161), (-10648320/134492161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354183997/70368744177664), (-61925173/140737488355328)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((-430710843/562949953421312), (507614275/281474976710656)), (9/562949953421312), by norm_num⟩
  | 2 => ⟨((-315095929/1125899906842624), (-192116731/562949953421312)), (7/2251799813685248), by norm_num⟩
  | 3 => ⟨((1329548181/18014398509481984), (-17697533/1125899906842624)), (13/18014398509481984), by norm_num⟩
  | 4 => ⟨((-404015277/144115188075855872), (754761131/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 5 => ⟨((-297021303/288230376151711744), (-528659875/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((1370573969/9223372036854775808), (-69122841/1152921504606846976)), (13/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-90672243/73786976294838206464), (1275873031/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-907152747/590295810358705651712), (-519086337/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 9 => ⟨((167092683/1180591620717411303424), (-465087593/4722366482869645213696)), (29/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((206778213/75557863725914323419136), (1200863531/75557863725914323419136)), (53/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-850728715/604462909807314587353088), (-56841053/151115727451828646838272)), (49/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((783041045/9671406556917033397649408), (-954511387/9671406556917033397649408)), (85/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((117/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/17423929), (-3549440/52271787)), 0, by norm_num⟩
  | 1 => ⟨((-1675158323200/2732339716173369), (4725014528000/910779905391123)), 0, by norm_num⟩
  | 2 => ⟨((-671658985/4398046511104), (-120393239/549755813888)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((933729845/70368744177664), (223815765/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-346141917/562949953421312), (370431173/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((221898899/18014398509481984), (-301238897/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((383314491/576460752303423488), (244389743/144115188075855872)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-765321709/9223372036854775808), (-97315507/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((339613489/73786976294838206464), (-88912717/73786976294838206464)), (33/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-79636847/590295810358705651712), (955326531/4722366482869645213696)), (39/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-259129463/151115727451828646838272), (-1859977495/151115727451828646838272)), (91/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((584386981/1208925819614629174706176), (31126933/75557863725914323419136)), (27/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-627725047/19342813113834066795298816), (26112813/38685626227668133590597632)), (63/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (8319/1280)))⁻¹=value ((1331200/17423929), (-3549440/52271787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1331200/17423929), (-3549440/52271787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((199659425/562949953421312), (-845309249/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 1 => ⟨((284631229/4503599627370496), (973300107/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-978302861/18014398509481984), (-118709833/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 3 => ⟨((511132393/72057594037927936), (-1088482465/144115188075855872)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((69539933/144115188075855872), (109525351/72057594037927936)), (15/576460752303423488), by norm_num⟩
  | 5 => ⟨((-121657579/576460752303423488), (-12039799/288230376151711744)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((618407139/36893488147419103232), (-186685369/9223372036854775808)), (23/36893488147419103232), by norm_num⟩
  | 7 => ⟨((332674253/295147905179352825856), (405356259/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-740086759/2361183241434822606848), (-8704439/295147905179352825856)), (53/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((323018029/18889465931478580854784), (-1006816589/37778931862957161709568)), (27/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((29087431/18889465931478580854784), (793981709/302231454903657293676544)), (13/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-1359248467/4835703278458516698824704), (5669109/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((370793667/38685626227668133590597632), (-901297461/38685626227668133590597632)), (87/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((133/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13619200/182415361), (-10648320/182415361)), 0, by norm_num⟩
  | 1 => ⟨((-36047944908800/33275363928760321), (145021599744000/33275363928760321)), 0, by norm_num⟩
  | 2 => ⟨((-47698475/549755813888), (-854594961/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1254010285/140737488355328), (664473049/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1059302831/2251799813685248), (11795913/140737488355328)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((68070751/4503599627370496), (-37963387/2251799813685248)), (5/36028797018963968), by norm_num⟩
  | 6 => ⟨((-10400579/144115188075855872), (1234212593/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-263335501/9223372036854775808), (-776030159/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 8 => ⟨((169242931/73786976294838206464), (108779185/147573952589676412928)), (31/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-505941797/4722366482869645213696), (93098313/2361183241434822606848)), (17/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((430476139/151115727451828646838272), (-43435373/9444732965739290427392)), (37/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((16856907/604462909807314587353088), (308060201/1208925819614629174706176)), (5/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-655993663/77371252455336267181195264), (-673020165/77371252455336267181195264)), (43/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (8319/1280)))⁻¹=value ((13619200/182415361), (-10648320/182415361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13619200/182415361), (-10648320/182415361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((164519757/36028797018963968), (-1755692977/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 1 => ⟨((41851931/2251799813685248), (259378627/18014398509481984)), (15/36028797018963968), by norm_num⟩
  | 2 => ⟨((-855750541/144115188075855872), (19735625/9007199254740992)), (15/144115188075855872), by norm_num⟩
  | 3 => ⟨((284100103/1152921504606846976), (-355409577/288230376151711744)), (27/1152921504606846976), by norm_num⟩
  | 4 => ⟨((698871485/4611686018427387904), (319445439/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-1029162531/36893488147419103232), (155915467/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 6 => ⟨((255180953/295147905179352825856), (-1068238481/295147905179352825856)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((375259535/1180591620717411303424), (707472657/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-863888785/18889465931478580854784), (267985259/18889465931478580854784)), (11/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((306529905/302231454903657293676544), (-1466540715/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((224911797/604462909807314587353088), (766437613/2417851639229258349412352)), (11/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-832380797/19342813113834066795298816), (325641793/19342813113834066795298816)), (83/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((145664569/309485009821345068724781056), (-1294703149/309485009821345068724781056)), (19/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((149/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15257600/211292161), (-10648320/211292161)), 0, by norm_num⟩
  | 1 => ⟨((-59703819468800/44644377300049921), (162467807232000/44644377300049921)), 0, by norm_num⟩
  | 2 => ⟨((-190942171/4398046511104), (-1452158165/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((403037827/70368744177664), (684929215/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1483604523/4503599627370496), (-141379555/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((914059433/72057594037927936), (-516470955/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-639630371/2305843009213693952), (666879623/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-42056183/9223372036854775808), (-1028375263/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((255895429/295147905179352825856), (1052512507/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-507825567/9444732965739290427392), (-195346165/18889465931478580854784)), (29/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1330972783/604462909807314587353088), (-37078823/37778931862957161709568)), (29/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-529701263/9671406556917033397649408), (879327111/9671406556917033397649408)), (29/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-97032391/309485009821345068724781056), (-721535519/154742504910672534362390528)), (57/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (8319/1280)))⁻¹=value ((15257600/211292161), (-10648320/211292161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15257600/211292161), (-10648320/211292161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-306400463/144115188075855872), (-135071363/36028797018963968)), (29/288230376151711744), by norm_num⟩
  | 1 => ⟨((161334543/72057594037927936), (106555605/576460752303423488)), (33/576460752303423488), by norm_num⟩
  | 2 => ⟨((-931236603/2305843009213693952), (1169559107/2305843009213693952)), (9/576460752303423488), by norm_num⟩
  | 3 => ⟨((-392431971/9223372036854775808), (-599287165/4611686018427387904)), (33/9223372036854775808), by norm_num⟩
  | 4 => ⟨((419396711/18446744073709551616), (441723221/73786976294838206464)), (55/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-755615897/295147905179352825856), (700361239/295147905179352825856)), (39/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-103096849/1180591620717411303424), (-268651137/590295810358705651712)), (49/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((31093075/590295810358705651712), (374938757/18889465931478580854784)), (57/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-188497309/37778931862957161709568), (595379117/151115727451828646838272)), (63/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-54663697/604462909807314587353088), (-1618713917/2417851639229258349412352)), (65/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1218184159/19342813113834066795298816), (125882181/4835703278458516698824704)), (65/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-802935459/154742504910672534362390528), (155958997/38685626227668133590597632)), (125/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-225502313/2475880078570760549798248448), (-745381167/1237940039285380274899124224)), (233/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((165/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/81148587), (-3549440/81148587)), 0, by norm_num⟩
  | 1 => ⟨((-1062272204800/731677019121841), (19990446080000/6585093172096569)), 0, by norm_num⟩
  | 2 => ⟨((-140824427/8796093022208), (-602955327/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((500162073/140737488355328), (310139273/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-494752105/2251799813685248), (-338759023/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((333969711/36028797018963968), (-79079381/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-315516009/1152921504606846976), (643079303/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((15667567/4611686018427387904), (-1155733331/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((530458097/2361183241434822606848), (729414307/1180591620717411303424)), (35/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-100624853/4722366482869645213696), (-39022821/2361183241434822606848)), (33/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((332718053/302231454903657293676544), (32490001/302231454903657293676544)), (61/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-392206831/9671406556917033397649408), (393541425/19342813113834066795298816)), (7/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((595641389/618970019642690137449562112), (-246493733/154742504910672534362390528)), (51/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (8319/1280)))⁻¹=value ((5632000/81148587), (-3549440/81148587)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5632000/81148587), (-3549440/81148587))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-718357933/2305843009213693952), (-24095769/144115188075855872)), (27/2305843009213693952), by norm_num⟩
  | 1 => ⟨((820625883/4611686018427387904), (-397134543/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-186964153/18446744073709551616), (1102144279/18446744073709551616)), (39/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-707758251/73786976294838206464), (-348751879/36893488147419103232)), (37/73786976294838206464), by norm_num⟩
  | 4 => ⟨((702265353/295147905179352825856), (-271956509/590295810358705651712)), (31/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-345637017/2361183241434822606848), (203470873/590295810358705651712)), (23/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-268476825/9444732965739290427392), (-810917927/18889465931478580854784)), (59/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((1949166107/302231454903657293676544), (-275293/4722366482869645213696)), (141/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-479317933/1208925819614629174706176), (47960379/75557863725914323419136)), (5/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-172552429/4835703278458516698824704), (-1416030635/19342813113834066795298816)), (21/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((322981511/38685626227668133590597632), (125657441/154742504910672534362390528)), (171/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-152040469/309485009821345068724781056), (409242919/618970019642690137449562112)), (21/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-595588847/19807040628566084398385987584), (-1416060429/19807040628566084398385987584)), (317/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((181/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18534400/278876161), (-10648320/278876161)), 0, by norm_num⟩
  | 1 => ⟨((-115068632268800/77771913174097921), (197360222208000/77771913174097921)), 0, by norm_num⟩
  | 2 => ⟨((12642641/17592186044416), (-1980449583/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((299116813/140737488355328), (528421899/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1281802629/9007199254740992), (-758345643/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1826333215/288230376151711744), (23318561/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-489081515/2305843009213693952), (545480399/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((706906749/147573952589676412928), (-1177637833/147573952589676412928)), (7/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-32256781/4722366482869645213696), (842070683/2361183241434822606848)), (25/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-124323399/18889465931478580854784), (-452645793/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1081877941/2417851639229258349412352), (41178475/151115727451828646838272)), (19/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-1552956763/77371252455336267181195264), (-4957833/9671406556917033397649408)), (65/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((209451123/309485009821345068724781056), (-56660479/154742504910672534362390528)), (7/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (8319/1280)))⁻¹=value ((18534400/278876161), (-10648320/278876161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18534400/278876161), (-10648320/278876161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-499708675/18446744073709551616), (14449287/18446744073709551616)), (91/73786976294838206464), by norm_num⟩
  | 1 => ⟨((695332873/73786976294838206464), (-481863943/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | 2 => ⟨((455687841/295147905179352825856), (733708255/147573952589676412928)), (75/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-675684729/590295810358705651712), (-469573253/1180591620717411303424)), (37/590295810358705651712), by norm_num⟩
  | 4 => ⟨((219796493/1180591620717411303424), (-76801409/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-10204789/37778931862957161709568), (42945039/1180591620717411303424)), (97/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-79598351/18889465931478580854784), (-56322753/18889465931478580854784)), (65/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((376793893/604462909807314587353088), (-559713375/2417851639229258349412352)), (157/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-178039107/9671406556917033397649408), (1487817965/19342813113834066795298816)), (181/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-932098407/154742504910672534362390528), (-991965127/154742504910672534362390528)), (195/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((1124583413/1237940039285380274899124224), (-206478989/1237940039285380274899124224)), (201/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-170381413/4951760157141521099596496896), (847601751/9903520314283042199192993792)), (25/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-103369347/19807040628566084398385987584), (-140715331/19807040628566084398385987584)), (3/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((197/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20172800/317583361), (-10648320/317583361)), 0, by norm_num⟩
  | 1 => ⟨((-146777570508800/100859191184056321), (214806429696000/100859191184056321)), 0, by norm_num⟩
  | 2 => ⟨((92486911/8796093022208), (-1619151361/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((170157553/140737488355328), (436200145/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-406940867/4503599627370496), (-704065723/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1204868693/288230376151711744), (278931685/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-687082067/4611686018427387904), (362890261/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((600952557/147573952589676412928), (-34562661/9223372036854775808)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-157044685/2361183241434822606848), (884416385/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-155246755/151115727451828646838272), (-1067344531/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((45648449/302231454903657293676544), (1001473657/4835703278458516698824704)), (43/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1279549377/154742504910672534362390528), (-625990433/154742504910672534362390528)), (17/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1636248953/4951760157141521099596496896), (-25116465/2475880078570760549798248448)), (53/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (8319/1280)))⁻¹=value ((20172800/317583361), (-10648320/317583361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20172800/317583361), (-10648320/317583361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-500109955/295147905179352825856), (70690611/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((117120423/590295810358705651712), (-355483321/295147905179352825856)), (99/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((657969197/2361183241434822606848), (721622711/2361183241434822606848)), (67/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-944642933/9444732965739290427392), (152626943/18889465931478580854784)), (67/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((775095/73786976294838206464), (-1242172303/75557863725914323419136)), (119/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((345899465/302231454903657293676544), (228024331/75557863725914323419136)), (93/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1099112027/2417851639229258349412352), (-150835825/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((467734529/9671406556917033397649408), (-47466185/1208925819614629174706176)), (159/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((82312451/154742504910672534362390528), (146247847/19342813113834066795298816)), (187/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-114694953/154742504910672534362390528), (-270141377/618970019642690137449562112)), (205/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((410837231/4951760157141521099596496896), (-196180425/4951760157141521099596496896)), (215/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-203907459/158456325028528675187087900672), (1464020629/158456325028528675187087900672)), (433/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-866721381/1267650600228229401496703205376), (-749551419/1267650600228229401496703205376)), (211/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((380213135/1099511627776), (268010065/1099511627776)), (1383/2199023255552), by norm_num⟩
  | 1 => ⟨((40829337/274877906944), (65832077/137438953472)), (363/274877906944), by norm_num⟩
  | 2 => ⟨((-430893035/4398046511104), (74950383/274877906944)), (3163/2199023255552), by norm_num⟩
  | 3 => ⟨((-395679059/4398046511104), (534727801/8796093022208)), (2347/2199023255552), by norm_num⟩
  | 4 => ⟨((-130367963/4398046511104), (-38510423/70368744177664)), (10613/17592186044416), by norm_num⟩
  | 5 => ⟨((-727435907/140737488355328), (-503780035/140737488355328)), (19459/70368744177664), by norm_num⟩
  | 6 => ⟨((-486733099/1125899906842624), (-69668491/70368744177664)), (120433/1125899906842624), by norm_num⟩
  | 7 => ⟨((137478975/9007199254740992), (-1394419745/9007199254740992)), (323421/9007199254740992), by norm_num⟩
  | 8 => ⟨((46148951/4503599627370496), (-296475707/18014398509481984)), (384659/36028797018963968), by norm_num⟩
  | 9 => ⟨((63916897/36028797018963968), (-710593869/576460752303423488)), (1646157/576460752303423488), by norm_num⟩
  | 10 => ⟨((494878097/2305843009213693952), (-244090137/4611686018427387904)), (1603485/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1543569843/73786976294838206464), (152308729/73786976294838206464)), (5743525/36893488147419103232), by norm_num⟩
  | 12 => ⟨((250270893/147573952589676412928), (223898067/295147905179352825856)), (9532173/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((380213135/1099511627776), (268010065/1099511627776)), (173/274877906944), by norm_num⟩
  | 1 => ⟨((40829337/274877906944), (65832077/137438953472)), (2905/2199023255552), by norm_num⟩
  | 2 => ⟨((-430893035/4398046511104), (74950383/274877906944)), (6327/4398046511104), by norm_num⟩
  | 3 => ⟨((-395679059/4398046511104), (534727801/8796093022208)), (9389/8796093022208), by norm_num⟩
  | 4 => ⟨((-130367963/4398046511104), (-38510423/70368744177664)), (42455/70368744177664), by norm_num⟩
  | 5 => ⟨((-727435907/140737488355328), (-503780035/140737488355328)), (9731/35184372088832), by norm_num⟩
  | 6 => ⟨((-486733099/1125899906842624), (-69668491/70368744177664)), (120479/1125899906842624), by norm_num⟩
  | 7 => ⟨((137478975/9007199254740992), (-1394419745/9007199254740992)), (161891/4503599627370496), by norm_num⟩
  | 8 => ⟨((46148951/4503599627370496), (-296475707/18014398509481984)), (772201/72057594037927936), by norm_num⟩
  | 9 => ⟨((63916897/36028797018963968), (-710593869/576460752303423488)), (52163/18014398509481984), by norm_num⟩
  | 10 => ⟨((494878097/2305843009213693952), (-244090137/4611686018427387904)), (1695719/2305843009213693952), by norm_num⟩
  | 11 => ⟨((1543569843/73786976294838206464), (152308729/73786976294838206464)), (7219265/36893488147419103232), by norm_num⟩
  | 12 => ⟨((250270893/147573952589676412928), (223898067/295147905179352825856)), (42676179/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile033Gamma
