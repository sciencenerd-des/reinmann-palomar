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
namespace Reinmann.XiRectangle.Tile038Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((41/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((425/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((348160000/5896562929), (-182645760/5896562929)), 0, by norm_num⟩
  | 1 => ⟨((-347282545/274877906944), (502724937/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((39466127/4398046511104), (-1294087563/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((246106081/281474976710656), (1300778951/562949953421312)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-138708041/2251799813685248), (-984922883/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 5 => ⟨((1536441423/576460752303423488), (190260351/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 6 => ⟨((-820041025/9223372036854775808), (401976339/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 7 => ⟨((675093879/295147905179352825856), (-596287865/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-342250185/9444732965739290427392), (112237119/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-30417209/75557863725914323419136), (-1017873911/302231454903657293676544)), (15/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((154849921/2417851639229258349412352), (56331237/604462909807314587353088)), (11/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-515919235/154742504910672534362390528), (-544495665/309485009821345068724781056)), (1/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((155580365/1237940039285380274899124224), (1506897/4951760157141521099596496896)), (93/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((425/32), (35673/5120)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((425/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((425/32), (35673/5120)))⁻¹=value ((348160000/5896562929), (-182645760/5896562929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((348160000/5896562929), (-182645760/5896562929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1453797045/536870912), (32422687/67108864)), (1/268435456), by norm_num⟩
  | 1 => ⟨((174080000/5896562929), (-91322880/5896562929)), 0, by norm_num⟩
  | 2 => ⟨((-347282545/1099511627776), (502724937/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((210486011/140737488355328), (-431362521/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((246106081/2251799813685248), (1300778951/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((-443865731/72057594037927936), (-393969153/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((512147141/2305843009213693952), (63420117/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((-937189743/147573952589676412928), (229700765/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((675093879/4722366482869645213696), (-596287865/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-304222387/151115727451828646838272), (12470791/2361183241434822606848)), (19/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-97335069/4835703278458516698824704), (-814299129/4835703278458516698824704)), (49/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((450472497/154742504910672534362390528), (327745379/77371252455336267181195264)), (33/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-1375784627/9903520314283042199192993792), (-181498555/2475880078570760549798248448)), (43/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-14033/553472), (759/81920)), 0, by norm_num⟩
  | 45 => ⟨((1468761791777/65290213785600), (-264561/20971520)), 0, by norm_num⟩
  | 44 => ⟨((-103236390305765/4902859787206656), (19691761264747/1649267441664000)), 0, by norm_num⟩
  | 43 => ⟨((743354761/34359738368), (-384762065/34359738368)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-388426103/17179869184), (48635227/4294967296)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((200154115/8589934592), (-404402681/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-818933941/34359738368), (417354447/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((838431961/34359738368), (-26720737/2147483648)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-53781123/2147483648), (437751781/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((884234991/34359738368), (-449097275/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-909123505/34359738368), (461361681/34359738368)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((467640783/17179869184), (-118570915/8589934592)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-962973099/34359738368), (487870213/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((992385729/34359738368), (-125559365/8589934592)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-1023664827/34359738368), (517486835/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((1056976149/34359738368), (-266849439/17179869184)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1092522707/34359738368), (550959455/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1130540481/34359738368), (-569371559/34359738368)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-1171297721/34359738368), (589055453/34359738368)), (3/34359738368), by norm_num⟩
  | 27 => ⟨((151887635/4294967296), (-610148383/34359738368)), (3/34359738368), by norm_num⟩
  | 26 => ⟨((-157788071/4294967296), (316403603/17179869184)), (3/34359738368), by norm_num⟩
  | 25 => ⟨((656659783/17179869184), (-328606367/17179869184)), (3/34359738368), by norm_num⟩
  | 24 => ⟨((-684313347/17179869184), (683574831/34359738368)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((357197703/8589934592), (-712138449/34359738368)), (3/34359738368), by norm_num⟩
  | 22 => ⟨((-747240139/17179869184), (46449449/2147483648)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((195811477/4294967296), (-97134119/4294967296)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-822891425/17179869184), (203547113/8589934592)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((866757063/17179869184), (-427511687/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-915553313/17179869184), (225041427/8589934592)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((970159355/17179869184), (-237583537/8589934592)), (3/17179869184), by norm_num⟩
  | 16 => ⟨((-1031676189/17179869184), (7862629/268435456)), (3/17179869184), by norm_num⟩
  | 15 => ⟨((275375295/4294967296), (-534761275/17179869184)), (3/17179869184), by norm_num⟩
  | 14 => ⟨((-9229959/134217728), (570528913/17179869184)), (3/17179869184), by norm_num⟩
  | 13 => ⟨((1273836673/17179869184), (-152853651/4294967296)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-690930503/8589934592), (329299725/8589934592)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((94363753/1073741824), (-356828809/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-207971001/2147483648), (24335451/536870912)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((57889879/536870912), (-214207701/4294967296)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-1044571551/8589934592), (29758631/536870912)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((74830581/536870912), (-535776895/8589934592)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1401791237/8589934592), (306206759/4294967296)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((844749725/4294967296), (-44655529/536870912)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-1061717199/4294967296), (428559529/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1425443599/4294967296), (-133789631/1073741824)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-539164201/1073741824), (355830421/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1087882405/1073741824), (-132508449/536870912)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-34725191/536870912), (1037525983/2147483648)), (1/536870912), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-87/512), (35673/81920)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-87/512), (35673/81920)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-87/512), (35673/81920))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((1453797045/536870912), (32422687/67108864)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((425/32), (35673/5120))) (z:=((-87/512), (35673/81920))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((1453797045/536870912), (32422687/67108864))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((409/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((262095833/8388608), (105034221/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((987409151/536870912), (16731017/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1036083081/137438953472), (-281782975/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-469621081/8796093022208), (724220231/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((148959491/1125899906842624), (-1888047455/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 5 => ⟨((504736163/36028797018963968), (1139115453/36028797018963968)), (13/9007199254740992), by norm_num⟩
  | 6 => ⟨((-359928879/576460752303423488), (-139250565/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 7 => ⟨((702459737/36893488147419103232), (116247671/36893488147419103232)), (41/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1105963213/2361183241434822606848), (378772727/2361183241434822606848)), (105/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((169034761/18889465931478580854784), (-182391579/18889465931478580854784)), (73/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-438088287/4835703278458516698824704), (1684158555/4835703278458516698824704)), (789/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-366814543/154742504910672534362390528), (-5906955/604462909807314587353088)), (1045/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((944576145/4951760157141521099596496896), (527743117/2475880078570760549798248448)), (689/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-425/32), (-35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((150684633/8388608), (606487195/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((718973695/536870912), (16731017/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1036083081/137438953472), (-281782975/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-469621081/8796093022208), (724220231/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((148959491/1125899906842624), (-1888047455/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 5 => ⟨((504736163/36028797018963968), (1139115453/36028797018963968)), (13/9007199254740992), by norm_num⟩
  | 6 => ⟨((-359928879/576460752303423488), (-139250565/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 7 => ⟨((702459737/36893488147419103232), (116247671/36893488147419103232)), (41/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1105963213/2361183241434822606848), (378772727/2361183241434822606848)), (105/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((169034761/18889465931478580854784), (-182391579/18889465931478580854784)), (73/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-438088287/4835703278458516698824704), (1684158555/4835703278458516698824704)), (789/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-366814543/154742504910672534362390528), (-5906955/604462909807314587353088)), (1045/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((944576145/4951760157141521099596496896), (527743117/2475880078570760549798248448)), (689/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((633572993/33554432), (606487195/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((718973695/536870912), (16731017/67108864)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1036083081/137438953472), (-281782975/68719476736)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-469621081/8796093022208), (724220231/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((148959491/1125899906842624), (-1888047455/1125899906842624)), (33/1125899906842624), by norm_num⟩
  | 5 => ⟨((504736163/36028797018963968), (1139115453/36028797018963968)), (13/9007199254740992), by norm_num⟩
  | 6 => ⟨((-359928879/576460752303423488), (-139250565/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 7 => ⟨((702459737/36893488147419103232), (116247671/36893488147419103232)), (41/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1105963213/2361183241434822606848), (378772727/2361183241434822606848)), (105/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((169034761/18889465931478580854784), (-182391579/18889465931478580854784)), (73/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-438088287/4835703278458516698824704), (1684158555/4835703278458516698824704)), (789/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-366814543/154742504910672534362390528), (-5906955/604462909807314587353088)), (1045/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((944576145/4951760157141521099596496896), (527743117/2475880078570760549798248448)), (689/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((347282545/137438953472), (-502724937/137438953472)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-39466127/1099511627776), (1294087563/4398046511104)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-184579561/35184372088832), (-487792107/35184372088832)), (3/70368744177664), by norm_num⟩
  | 3 => ⟨((1109664329/2251799813685248), (246230721/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-480137945/18014398509481984), (-237825439/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((615030769/576460752303423488), (-301482255/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-73838393/2305843009213693952), (260875941/9223372036854775808)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((342250185/590295810358705651712), (-112237119/73786976294838206464)), (7/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1069355/147573952589676412928), (572554075/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-774249605/604462909807314587353088), (-281656185/151115727451828646838272)), (33/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((177347237/2417851639229258349412352), (187170385/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-466741095/154742504910672534362390528), (-4520691/618970019642690137449562112)), (77/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((478287897/4951760157141521099596496896), (-249436251/4951760157141521099596496896)), (29/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39466127/1099511627776), (-1294087563/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((184579561/17592186044416), (487792107/17592186044416)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((-832248247/562949953421312), (-738692163/562949953421312)), (5/562949953421312), by norm_num⟩
  | 3 => ⟨((480137945/4503599627370496), (237825439/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-384394231/72057594037927936), (188426409/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((886060717/4611686018427387904), (-782627823/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-18716807/4611686018427387904), (392829917/36893488147419103232)), (11/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-136877441/2361183241434822606848), (-572554075/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((435515403/37778931862957161709568), (1267452833/75557863725914323419136)), (29/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-443368093/604462909807314587353088), (-233962981/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((1283538011/38685626227668133590597632), (3107975/38685626227668133590597632)), (19/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-358715923/309485009821345068724781056), (374154377/618970019642690137449562112)), (15/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((287196353/9903520314283042199192993792), (-827198411/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-246106081/35184372088832), (-1300778951/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((1109664329/562949953421312), (246230721/140737488355328)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((-480137945/2251799813685248), (-237825439/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 3 => ⟨((512525641/36028797018963968), (-62808803/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 4 => ⟨((-738383931/1152921504606846976), (652189853/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((299468913/18446744073709551616), (-392829917/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((159690347/590295810358705651712), (1335959509/590295810358705651712)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-145171801/2361183241434822606848), (-211242139/2361183241434822606848)), (19/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1330104279/302231454903657293676544), (43868059/18889465931478580854784)), (1/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-534807505/2417851639229258349412352), (-2589979/4835703278458516698824704)), (27/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((1315291717/154742504910672534362390528), (-685949691/154742504910672534362390528)), (45/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-287196353/1237940039285380274899124224), (206799603/618970019642690137449562112)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((165846723/79228162514264337593543950336), (-1332667169/79228162514264337593543950336)), (29/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-138708041/140737488355328), (-984922883/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨((480137945/2251799813685248), (237825439/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((-1537576923/72057594037927936), (188426409/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 3 => ⟨((738383931/576460752303423488), (-163047463/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-374336141/9223372036854775808), (122759349/1152921504606846976)), (15/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-7485485/9223372036854775808), (-31311551/4611686018427387904)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((63512663/295147905179352825856), (739347487/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1330104279/75557863725914323419136), (-43868059/4722366482869645213696)), (1/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((1203316887/1208925819614629174706176), (2913727/1208925819614629174706176)), (15/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-205514331/4835703278458516698824704), (428718557/19342813113834066795298816)), (27/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((789789971/618970019642690137449562112), (-142174727/77371252455336267181195264)), (23/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-62192521/4951760157141521099596496896), (999500377/9903520314283042199192993792)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-503791283/316912650057057350374175801344), (-1341181589/316912650057057350374175801344)), (65/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1536441423/18014398509481984), (-190260351/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 1 => ⟨((615030769/36028797018963968), (-301482255/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 2 => ⟨((-886060717/576460752303423488), (782627823/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 3 => ⟨((299468913/4611686018427387904), (-392829917/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 4 => ⟨((7485485/4611686018427387904), (31311551/2305843009213693952)), (19/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-152430391/295147905179352825856), (-110902123/147573952589676412928)), (11/590295810358705651712), by norm_num⟩
  | 6 => ⟨((232768249/4722366482869645213696), (491322261/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-1925307019/604462909807314587353088), (-4661963/604462909807314587353088)), (51/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((92481449/604462909807314587353088), (-385846701/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-197447493/38685626227668133590597632), (142174727/19342813113834066795298816)), (3/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((136823547/2475880078570760549798248448), (-1099450415/2475880078570760549798248448)), (43/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((151137385/19807040628566084398385987584), (402354477/19807040628566084398385987584)), (19/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-484766387/633825300114114700748351602688), (-864750203/1267650600228229401496703205376)), (65/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-820041025/144115188075855872), (401976339/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 1 => ⟨((73838393/72057594037927936), (-260875941/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 2 => ⟨((-18716807/288230376151711744), (392829917/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-159690347/73786976294838206464), (-667979755/36893488147419103232)), (29/73786976294838206464), by norm_num⟩
  | 4 => ⟨((63512663/73786976294838206464), (739347487/590295810358705651712)), (23/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-931072995/9444732965739290427392), (-491322261/9444732965739290427392)), (29/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1123095761/151115727451828646838272), (2719479/151115727451828646838272)), (17/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-986468789/2417851639229258349412352), (128615567/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((592342479/38685626227668133590597632), (-426524181/19342813113834066795298816)), (39/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-114019623/618970019642690137449562112), (1832417359/1237940039285380274899124224)), (77/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-554170411/19807040628566084398385987584), (-1475299749/19807040628566084398385987584)), (73/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((484766387/158456325028528675187087900672), (216187551/79228162514264337593543950336)), (67/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-252093717/1267650600228229401496703205376), (-252330821/5070602400912917605986812821504)), (15/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-675093879/2305843009213693952), (596287865/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 1 => ⟨((342250185/9223372036854775808), (-112237119/1152921504606846976)), (19/9223372036854775808), by norm_num⟩
  | 2 => ⟨((136877441/73786976294838206464), (1145108151/73786976294838206464)), (7/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-145171801/147573952589676412928), (-211242139/147573952589676412928)), (29/590295810358705651712), by norm_num⟩
  | 4 => ⟨((166263035/1180591620717411303424), (701888945/9444732965739290427392)), (25/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-1925307019/151115727451828646838272), (-4661963/151115727451828646838272)), (69/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((986468789/1208925819614629174706176), (-128615567/302231454903657293676544)), (11/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-676962833/19342813113834066795298816), (487456207/9671406556917033397649408)), (51/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((73298329/154742504910672534362390528), (-294495647/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((49479501/618970019642690137449562112), (1053785535/4951760157141521099596496896)), (59/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-761775751/79228162514264337593543950336), (-679446589/79228162514264337593543950336)), (29/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((216080329/316912650057057350374175801344), (216283561/1267650600228229401496703205376)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-365641385/10141204801825835211973625643008), (354715893/40564819207303340847894502572032)), (103/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-342250185/36893488147419103232), (112237119/4611686018427387904)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-136877441/147573952589676412928), (-1145108149/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 2 => ⟨((871030807/1180591620717411303424), (1267452833/1180591620717411303424)), (25/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-1330104279/9444732965739290427392), (-43868059/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((1203316887/75557863725914323419136), (2913727/75557863725914323419136)), (13/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-92481449/75557863725914323419136), (385846701/604462909807314587353088)), (5/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((592342479/9671406556917033397649408), (-426524181/4835703278458516698824704)), (53/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-73298329/77371252455336267181195264), (294495647/38685626227668133590597632)), (33/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-445315509/2475880078570760549798248448), (-1185508727/2475880078570760549798248448)), (19/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((952219689/39614081257132168796771975168), (212327059/9903520314283042199192993792)), (83/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-1188441809/633825300114114700748351602688), (-297389897/633825300114114700748351602688)), (43/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((1096924155/10141204801825835211973625643008), (-33254615/1267650600228229401496703205376)), (87/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-753692397/162259276829213363391578010288128), (331234725/81129638414606681695789005144064)), (21/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((30417209/147573952589676412928), (1017873911/590295810358705651712)), (15/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-774249605/2361183241434822606848), (-1126624739/2361183241434822606848)), (25/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((443368093/4722366482869645213696), (233962981/4722366482869645213696)), (43/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-534807505/37778931862957161709568), (-5179959/151115727451828646838272)), (105/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((205514331/151115727451828646838272), (-428718557/604462909807314587353088)), (13/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-197447493/2417851639229258349412352), (142174727/1208925819614629174706176)), (43/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((114019623/77371252455336267181195264), (-1832417359/154742504910672534362390528)), (123/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((49479501/154742504910672534362390528), (1053785535/1237940039285380274899124224)), (81/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-952219689/19807040628566084398385987584), (-212327059/4951760157141521099596496896)), (49/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((1320490899/316912650057057350374175801344), (330433219/316912650057057350374175801344)), (7/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-1340685079/5070602400912917605986812821504), (325156235/5070602400912917605986812821504)), (61/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((251230799/20282409603651670423947251286016), (-110411575/10141204801825835211973625643008)), (1/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-223827151/649037107316853453566312041152512), (1165935081/1298074214633706907132624082305024)), (129/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((154849921/2361183241434822606848), (56331237/590295810358705651712)), (11/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((-177347237/4722366482869645213696), (-374340769/18889465931478580854784)), (5/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((320884503/37778931862957161709568), (3107975/151115727451828646838272)), (37/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-1315291717/1208925819614629174706176), (685949691/1208925819614629174706176)), (3/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((789789971/9671406556917033397649408), (-142174727/1208925819614629174706176)), (51/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-136823547/77371252455336267181195264), (1099450415/77371252455336267181195264)), (45/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-554170411/1237940039285380274899124224), (-737649875/618970019642690137449562112)), (137/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((761775751/9903520314283042199192993792), (679446589/9903520314283042199192993792)), (95/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-1188441809/158456325028528675187087900672), (-297389897/158456325028528675187087900672)), (121/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((1340685079/2535301200456458802993406410752), (-325156235/2535301200456458802993406410752)), (145/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-276353879/10141204801825835211973625643008), (242905465/10141204801825835211973625643008)), (165/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((537185163/649037107316853453566312041152512), (-1399122097/649037107316853453566312041152512)), (45/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((85212427/5192296858534827628530496329220096), (363916089/2596148429267413814265248164610048)), (47/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87040000/17689688787), (-15220480/5896562929)), 0, by norm_num⟩
  | 1 => ⟨((-463043393/4398046511104), (167574979/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((210486011/281474976710656), (-431362521/70368744177664)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((328141441/4503599627370496), (867185967/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-739776219/144115188075855872), (-656615255/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((512147141/2305843009213693952), (63420117/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-1093388033/147573952589676412928), (133992113/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((225031293/1180591620717411303424), (-795050487/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-114083395/37778931862957161709568), (37412373/4722366482869645213696)), (27/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-162225115/4835703278458516698824704), (-1357165215/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((825866245/154742504910672534362390528), (18777079/2417851639229258349412352)), (59/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-1375784627/4951760157141521099596496896), (-181498555/1237940039285380274899124224)), (43/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1659523893/158456325028528675187087900672), (502299/19807040628566084398385987584)), (125/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((316869047/16777216), (606400583/33554432)), (7/33554432), by norm_num⟩
  | 1 => ⟨((718917171/536870912), (267859919/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1036185857/137438953472), (-564408455/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-117245045/2199023255552), (362956977/4398046511104)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((143179989/1125899906842624), (-946588631/562949953421312)), (17/562949953421312), by norm_num⟩
  | 5 => ⟨((256369231/18014398509481984), (285274333/9007199254740992)), (53/36028797018963968), by norm_num⟩
  | 6 => ⟨((-182099963/288230376151711744), (-554908633/1152921504606846976)), (69/1152921504606846976), by norm_num⟩
  | 7 => ⟨((709491965/36893488147419103232), (110036339/36893488147419103232)), (165/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1113093425/2361183241434822606848), (198739457/1180591620717411303424)), (53/590295810358705651712), by norm_num⟩
  | 9 => ⟨((673604277/75557863725914323419136), (-375386011/37778931862957161709568)), (147/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-412279967/4835703278458516698824704), (1721712713/4835703278458516698824704)), (791/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-409807813/154742504910672534362390528), (-1534867799/154742504910672534362390528)), (1049/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((996436267/4951760157141521099596496896), (1055611809/4951760157141521099596496896)), (1383/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-224518411/2251799813685248), (920240045/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-525026307/18014398509481984), (-1387497549/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 2 => ⟨((36988811/9007199254740992), (525292205/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((-682862855/2305843009213693952), (-21140039/288230376151711744)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((1093388035/73786976294838206464), (-133992113/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-630087621/1180591620717411303424), (556535341/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((212955671/18889465931478580854784), (-1117382875/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((97335069/604462909807314587353088), (814299129/604462909807314587353088)), (27/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-154849921/4835703278458516698824704), (-56331237/1208925819614629174706176)), (11/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1261135909/618970019642690137449562112), (332747351/309485009821345068724781056)), (35/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-912738141/9903520314283042199192993792), (-4420231/19807040628566084398385987584)), (55/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((510173757/158456325028528675187087900672), (-266065335/158456325028528675187087900672)), (11/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-816914071/10141204801825835211973625643008), (588229981/5070602400912917605986812821504)), (65/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((633738091/33554432), (303200305/16777216)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1437834311/1073741824), (66964959/268435456)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1036186421/137438953472), (-282203977/68719476736)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-468982785/8796093022208), (725913309/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((143196673/1125899906842624), (-1893181351/1125899906842624)), (35/1125899906842624), by norm_num⟩
  | 5 => ⟨((512719233/36028797018963968), (285278579/9007199254740992)), (27/18014398509481984), by norm_num⟩
  | 6 => ⟨((-364193427/576460752303423488), (-554942733/1152921504606846976)), (35/576460752303423488), by norm_num⟩
  | 7 => ⟨((354748953/18446744073709551616), (13760755/4611686018427387904)), (83/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1113169035/2361183241434822606848), (99342223/590295810358705651712)), (213/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((42109889/4722366482869645213696), (-750690785/75557863725914323419136)), (295/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-51590705/604462909807314587353088), (860855817/2417851639229258349412352)), (99/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-102327399/38685626227668133590597632), (-383781907/38685626227668133590597632)), (525/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((996037383/4951760157141521099596496896), (264046563/1237940039285380274899124224)), (173/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-450911219/576460752303423488), (-50027829/72057594037927936)), (7/1152921504606846976), by norm_num⟩
  | 1 => ⟨((1560829383/9223372036854775808), (193280357/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1249586325/73786976294838206464), (306267687/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 3 => ⟨((600083449/590295810358705651712), (-530033657/590295810358705651712)), (11/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-76055597/2361183241434822606848), (798130625/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-194670137/302231454903657293676544), (-1628598259/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((825866247/4835703278458516698824704), (600866529/2417851639229258349412352)), (29/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-270243409/19342813113834066795298816), (-570424031/77371252455336267181195264)), (27/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((244483431/309485009821345068724781056), (4735963/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1336169365/39614081257132168796771975168), (348418891/19807040628566084398385987584)), (45/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((10029079/9903520314283042199192993792), (-115545175/79228162514264337593543950336)), (19/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-50543763/5070602400912917605986812821504), (406146185/5070602400912917605986812821504)), (33/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-51178797/40564819207303340847894502572032), (-1089976149/324518553658426726783156020576256)), (27/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((633738091/33554432), (303200305/16777216)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1437834311/1073741824), (66964959/268435456)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1036186419/137438953472), (-564407953/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-58622847/1099511627776), (725913301/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((143196637/1125899906842624), (-236647657/140737488355328)), (9/281474976710656), by norm_num⟩
  | 5 => ⟨((256359605/18014398509481984), (570557061/18014398509481984)), (55/36028797018963968), by norm_num⟩
  | 6 => ⟨((-728386657/1152921504606846976), (-277471223/576460752303423488)), (71/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1418994781/73786976294838206464), (13760721/4611686018427387904)), (167/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-556583585/1180591620717411303424), (397368897/2361183241434822606848)), (107/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((673755675/75557863725914323419136), (-46918091/4722366482869645213696)), (37/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-412720743/4835703278458516698824704), (860852291/2417851639229258349412352)), (793/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-204655569/77371252455336267181195264), (-1535115233/154742504910672534362390528)), (1051/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((31125973/154742504910672534362390528), (264042405/1237940039285380274899124224)), (1385/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((999669059/295147905179352825856), (-245014149/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-720100137/1180591620717411303424), (636040389/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((22816679/590295810358705651712), (-478878375/4722366482869645213696)), (19/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((194670137/151115727451828646838272), (407149565/37778931862957161709568)), (9/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((-619399685/1208925819614629174706176), (-450649897/604462909807314587353088)), (29/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((567511159/9671406556917033397649408), (37434077/1208925819614629174706176)), (37/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-1369107213/309485009821345068724781056), (-1657587/154742504910672534362390528)), (43/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((300638107/1237940039285380274899124224), (-627154003/4951760157141521099596496896)), (47/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-722093689/79228162514264337593543950336), (1039906575/79228162514264337593543950336)), (49/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((69497675/633825300114114700748351602688), (-1116902009/1267650600228229401496703205376)), (3/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((84445015/5070602400912917605986812821504), (899230323/20282409603651670423947251286016)), (45/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-295476655/162259276829213363391578010288128), (-527085839/324518553658426726783156020576256)), (21/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((614628491/5192296858534827628530496329220096), (307603287/10384593717069655257060992658440192)), (37/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((633738091/33554432), (303200305/16777216)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1437834311/1073741824), (66964959/268435456)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1036186419/137438953472), (-564407953/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-58622847/1099511627776), (725913301/8796093022208)), (5/4398046511104), by norm_num⟩
  | 4 => ⟨((35799159/281474976710656), (-1893181257/1125899906842624)), (37/1125899906842624), by norm_num⟩
  | 5 => ⟨((128179803/9007199254740992), (1141114123/36028797018963968)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-364193331/576460752303423488), (-277471223/576460752303423488)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((1418994799/73786976294838206464), (220171527/73786976294838206464)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-139145899/295147905179352825856), (12417779/73786976294838206464)), (215/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((673755683/75557863725914323419136), (-750689523/75557863725914323419136)), (297/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-206360331/2417851639229258349412352), (430426199/1208925819614629174706176)), (397/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-102327855/38685626227668133590597632), (-383778871/38685626227668133590597632)), (263/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((498015861/2475880078570760549798248448), (1056169767/4951760157141521099596496896)), (693/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-590007053/75557863725914323419136), (1547889695/75557863725914323419136)), (35/75557863725914323419136), by norm_num⟩
  | 1 => ⟨((-58990951/75557863725914323419136), (-493514623/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((750787497/1208925819614629174706176), (1092484597/1208925819614629174706176)), (11/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-573243595/4835703278458516698824704), (-37812199/604462909807314587353088)), (49/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((2074404869/154742504910672534362390528), (5022991/154742504910672534362390528)), (91/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-637717197/618970019642690137449562112), (83145417/154742504910672534362390528)), (35/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((510571295/9903520314283042199192993792), (-735287477/9903520314283042199192993792)), (23/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-126359409/158456325028528675187087900672), (1015365463/158456325028528675187087900672)), (29/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-383840977/2535301200456458802993406410752), (-31932895/79228162514264337593543950336)), (67/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((410384243/20282409603651670423947251286016), (732063665/40564819207303340847894502572032)), (9/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-1024380819/649037107316853453566312041152512), (-256336073/649037107316853453566312041152512)), (75/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((945496915/10384593717069655257060992658440192), (-229311285/10384593717069655257060992658440192)), (19/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-649647319/166153499473114484112975882535043072), (285508719/83076749736557242056487941267521536)), (37/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((633738091/33554432), (303200305/16777216)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1437834311/1073741824), (66964959/268435456)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1036186419/137438953472), (-564407953/137438953472)), (7/137438953472), by norm_num⟩
  | 3 => ⟨((-58622847/1099511627776), (725913301/8796093022208)), (11/8796093022208), by norm_num⟩
  | 4 => ⟨((35799159/281474976710656), (-1893181257/1125899906842624)), (19/562949953421312), by norm_num⟩
  | 5 => ⟨((128179803/9007199254740992), (1141114123/36028797018963968)), (57/36028797018963968), by norm_num⟩
  | 6 => ⟨((-364193331/576460752303423488), (-277471223/576460752303423488)), (73/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1418994799/73786976294838206464), (220171527/73786976294838206464)), (169/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-139145899/295147905179352825856), (397368927/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((673755685/75557863725914323419136), (-375344761/37778931862957161709568)), (149/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-206360335/2417851639229258349412352), (860852397/2417851639229258349412352)), (795/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-204655703/77371252455336267181195264), (-1535115487/154742504910672534362390528)), (1053/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((996031703/4951760157141521099596496896), (132021223/618970019642690137449562112)), (1387/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-304055185/2417851639229258349412352), (-884872505/4835703278458516698824704)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((348229735/4835703278458516698824704), (735035905/19342813113834066795298816)), (5/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((-39379499/2417851639229258349412352), (-47677/1208925819614629174706176)), (37/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((1291318923/618970019642690137449562112), (-336723711/309485009821345068724781056)), (95/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-775395087/4951760157141521099596496896), (1116667355/4951760157141521099596496896)), (101/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((134329771/39614081257132168796771975168), (-134926449/4951760157141521099596496896)), (89/39614081257132168796771975168), by norm_num⟩
  | 6 => ⟨((136017495/158456325028528675187087900672), (1448410615/633825300114114700748351602688)), (135/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-186972865/1267650600228229401496703205376), (-667062847/5070602400912917605986812821504)), (47/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((1166781009/81129638414606681695789005144064), (72992401/20282409603651670423947251286016)), (15/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((-329062365/324518553658426726783156020576256), (319229867/1298074214633706907132624082305024)), (9/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((271316993/5192296858534827628530496329220096), (-238478217/5192296858534827628530496329220096)), (163/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-527394309/332306998946228968225951765070086144), (85851337/20769187434139310514121985316880384)), (89/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-167318653/5316911983139663491615228241121378304), (-357283275/1329227995784915872903807060280344576)), (93/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((633738091/33554432), (303200305/16777216)), (3/8388608), by norm_num⟩
  | 1 => ⟨((1437834311/1073741824), (66964959/268435456)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1036186419/137438953472), (-564407953/137438953472)), (1/17179869184), by norm_num⟩
  | 3 => ⟨((-58622847/1099511627776), (725913301/8796093022208)), (3/2199023255552), by norm_num⟩
  | 4 => ⟨((35799159/281474976710656), (-1893181257/1125899906842624)), (39/1125899906842624), by norm_num⟩
  | 5 => ⟨((128179803/9007199254740992), (1141114123/36028797018963968)), (29/18014398509481984), by norm_num⟩
  | 6 => ⟨((-364193331/576460752303423488), (-277471223/576460752303423488)), (37/576460752303423488), by norm_num⟩
  | 7 => ⟨((1418994799/73786976294838206464), (220171527/73786976294838206464)), (85/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-139145899/295147905179352825856), (397368927/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((673755685/75557863725914323419136), (-375344761/37778931862957161709568)), (299/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-206360335/2417851639229258349412352), (860852397/2417851639229258349412352)), (199/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-204655703/77371252455336267181195264), (-767557743/77371252455336267181195264)), (527/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((996031703/4951760157141521099596496896), (1056169783/4951760157141521099596496896)), (347/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((29780287340515/262144), (-937863545563111/8388608)), (439499413/4194304), by norm_num⟩
  | 1 => ⟨((360029291/2), (-485491741/4)), (675/4), by norm_num⟩
  | 2 => ⟨((272128243/2), (-480962721/8)), (547/4), by norm_num⟩
  | 3 => ⟨((530470997/8), -16608641), (1191/16), by norm_num⟩
  | 4 => ⟨(23623767, (-122554251/64)), (979/32), by norm_num⟩
  | 5 => ⟨((843976783/128), (4121669/8)), (2593/256), by norm_num⟩
  | 6 => ⟨((770946127/512), (181761141/512)), (1443/512), by norm_num⟩
  | 7 => ⟨((593353779/2048), (474166057/4096)), (2777/4096), by norm_num⟩
  | 8 => ⟨((392734989/8192), (226998007/8192)), (1179/8192), by norm_num⟩
  | 9 => ⟨((453539473/65536), (709343151/131072)), (1795/65536), by norm_num⟩
  | 10 => ⟨((461161821/524288), (474046163/524288)), (4959/1048576), by norm_num⟩
  | 11 => ⟨((414673735/4194304), (1113965923/8388608)), (785/1048576), by norm_num⟩
  | 12 => ⟨((658304623/67108864), (73220315/4194304)), (3675/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804289009984409/5070602400912917605986812821504), (-506331300961/5070602400912917605986812821504)), (465851/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((905820456742711/316912650057057350374175801344), (-1239892354967/633825300114114700748351602688)), (285545/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1926759370929435/39614081257132168796771975168), (-699123262297/19807040628566084398385987584)), (644109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((120555157452935/154742504910672534362390528), (-186070487251/309485009821345068724781056)), (685771/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1810587483331467/154742504910672534362390528), (-745920800453/77371252455336267181195264)), (42959/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1586529134464037/9671406556917033397649408), (-1402093775883/9671406556917033397649408)), (323031/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((161397966659677/75557863725914323419136), (-307583958585/151115727451828646838272)), (283493/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1940511640722571/75557863725914323419136), (-250736235401/9444732965739290427392)), (462259/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((83571705007501/295147905179352825856), (-1510211968007/4722366482869645213696)), (696171/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1676019954843167/590295810358705651712), (-1043002049789/295147905179352825856)), (240445/147573952589676412928), by norm_num⟩
  | 8 => ⟨((945928340707983/36893488147419103232), (-2621780911583/73786976294838206464)), (1209083/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1899817741979217/9223372036854775808), (-1484633283345/4611686018427387904)), (342429/2305843009213693952), by norm_num⟩
  | 6 => ⟨((208919577307365/144115188075855872), (-374271582311/144115188075855872)), (1381689/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1262609045735103/144115188075855872), (-165512568807/9007199254740992)), (305647/36028797018963968), by norm_num⟩
  | 4 => ⟨((1594343118968411/36028797018963968), (-4029611018563/36028797018963968)), (1861457/36028797018963968), by norm_num⟩
  | 3 => ⟨((809406605119659/4503599627370496), (-2569461187819/4503599627370496)), (2375887/9007199254740992), by norm_num⟩
  | 2 => ⟨((1245315198196745/2251799813685248), (-2647536766047/1125899906842624)), (2451137/2251799813685248), by norm_num⟩
  | 1 => ⟨((1309618547103561/1125899906842624), (-8344743340753/1125899906842624)), (3870727/1125899906842624), by norm_num⟩
  | 0 => ⟨((189034566291147/140737488355328), (-9185280361229/562949953421312)), (1069249/140737488355328), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((189034566291147/140737488355328), (-9185280361229/562949953421312)), (4078861237109136537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1015473406111053/562949953421312), (-49349622751933/1125899906842624)), (23258095/1125899906842624), by norm_num⟩
  | 2 => ⟨((457668299792477/140737488355328), (-44509488988887/281474976710656)), (10743347/140737488355328), by norm_num⟩
  | 3 => ⟨((742392810275389/70368744177664), (-72370845850059/70368744177664)), (36635441/70368744177664), by norm_num⟩
  | 4 => ⟨((242432538674969/2199023255552), (-190878763933115/8796093022208)), (26511439/2199023255552), by norm_num⟩
  | 5 => ⟨((802861661964737/68719476736), (-164402618876541/34359738368)), (218629837/68719476736), by norm_num⟩
  | 6 => ⟨((29780287340515/262144), (-937863545563111/8388608)), (439499413/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((633738091/33554432), (303200305/16777216)), (3/8388608), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((33587200/1315596529), (-182645760/1315596529)), 0, by norm_num⟩
  | 1 => ⟨((16115686821068800/1730794227116847841), (6134559670272000/1730794227116847841)), 0, by norm_num⟩
  | 2 => ⟨((-401201627/1099511627776), (1321822001/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-652098727/17592186044416), (-580578765/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((778003999/281474976710656), (-302837687/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((513793165/4503599627370496), (987792643/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1202028175/72057594037927936), (368897015/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-164212747/1152921504606846976), (-176296883/144115188075855872)), (13/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1599970605/18446744073709551616), (105672443/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-222071599/147573952589676412928), (877711667/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-14523027/36893488147419103232), (-425907559/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((662869671/37778931862957161709568), (-945331731/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((914547237/604462909807314587353088), (116161283/75557863725914323419136)), (17/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((41/32), (35673/5120)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((41/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((41/32), (35673/5120)))⁻¹=value ((33587200/1315596529), (-182645760/1315596529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((33587200/1315596529), (-182645760/1315596529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((59801600/1408985329), (-182645760/1408985329)), 0, by norm_num⟩
  | 1 => ⟨((14891621141708800/1985239657337238241), (10922508681216000/1985239657337238241)), 0, by norm_num⟩
  | 2 => ⟨((-35444627/68719476736), (101547571/274877906944)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-228672965/17592186044416), (-1452072491/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1661138103/562949953421312), (18759391/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-72935493/1125899906842624), (858143753/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-395432595/36028797018963968), (-593924161/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((442226701/576460752303423488), (-154622701/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((170542569/9223372036854775808), (281803365/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-1284772475/295147905179352825856), (-3627727/36893488147419103232)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((466333663/4722366482869645213696), (-165312363/590295810358705651712)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1213135801/75557863725914323419136), (233162707/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-172388013/151115727451828646838272), (117673403/151115727451828646838272)), (13/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((73/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((73/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((73/32), (35673/5120)))⁻¹=value ((59801600/1408985329), (-182645760/1408985329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((59801600/1408985329), (-182645760/1408985329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-31350905346457600/1853656208244323041), (-17057068351488000/1853656208244323041)), 0, by norm_num⟩
  | 1 => ⟨((62190465/34359738368), (-67259117/34359738368)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((663649619/4398046511104), (1018882865/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-846851523/35184372088832), (18182185/2199023255552)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((-13141263/70368744177664), (-615055069/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((25172973/140737488355328), (64824445/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-411162985/72057594037927936), (962821175/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((-262166537/288230376151711744), (-791884259/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((629442733/9223372036854775808), (-127692627/2305843009213693952)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((210157319/73786976294838206464), (892222575/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1162640559/2361183241434822606848), (58835473/590295810358705651712)), (21/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((56301771/37778931862957161709568), (-1411657145/37778931862957161709568)), (1/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((200512411/75557863725914323419136), (114649163/151115727451828646838272)), (45/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((105/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((28672000/518267643), (-60881920/518267643)), 0, by norm_num⟩
  | 1 => ⟨((160251366604800/29844594420086161), (1745606410240000/268601349780775449)), 0, by norm_num⟩
  | 2 => ⟨((-1166024017/2199023255552), (298224101/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((235797623/35184372088832), (-306947437/8796093022208)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1049487209/562949953421312), (764994695/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1183407749/9007199254740992), (323854819/4503599627370496)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((-84946679/144115188075855872), (-1398802613/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((1352156649/2305843009213693952), (539254219/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((-276304603/9223372036854775808), (516029869/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-15023587/18446744073709551616), (-747714329/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1618141059/9444732965739290427392), (210048323/9444732965739290427392)), (37/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-228389661/37778931862957161709568), (713863041/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-468708803/1208925819614629174706176), (-186303289/302231454903657293676544)), (19/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((105/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((105/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((105/32), (35673/5120)))⁻¹=value ((28672000/518267643), (-60881920/518267643)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((28672000/518267643), (-60881920/518267643))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1108656291/549755813888), (406196063/274877906944)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-11052235/68719476736), (-528030913/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1200115427/17592186044416), (-4715035/4398046511104)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-307415939/140737488355328), (1030395407/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-358390499/562949953421312), (-241937417/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((252786617/4503599627370496), (-809280089/18014398509481984)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((168614433/72057594037927936), (428672015/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((-628520613/1152921504606846976), (96233653/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((91297781/9223372036854775808), (-1632724607/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((942512179/295147905179352825856), (532876319/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-991272127/4722366482869645213696), (14829741/73786976294838206464)), (7/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-389327895/37778931862957161709568), (-47532845/2361183241434822606848)), (11/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1029648469/604462909807314587353088), (-24043971/75557863725914323419136)), (1/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((137/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((112230400/1753049329), (-182645760/1753049329)), 0, by norm_num⟩
  | 1 => ⟨((10381905480908800/3073181949907350241), (20498406703104000/3073181949907350241)), 0, by norm_num⟩
  | 2 => ⟨((-1001890823/2199023255552), (-41259789/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((581909279/35184372088832), (-792812399/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((362777753/562949953421312), (891068663/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-464253007/4503599627370496), (-19249415/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((603899463/144115188075855872), (-173759777/36028797018963968)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((135010617/1152921504606846976), (859321825/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-427269389/18446744073709551616), (-430096727/73786976294838206464)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((616904035/590295810358705651712), (-301059231/295147905179352825856)), (25/590295810358705651712), by norm_num⟩
  | 10 => ⟨((371822943/18889465931478580854784), (12852669/147573952589676412928)), (69/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1561658195/302231454903657293676544), (-532662795/302231454903657293676544)), (47/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((621897217/2417851639229258349412352), (-32151019/151115727451828646838272)), (65/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((137/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((137/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((137/32), (35673/5120)))⁻¹=value ((112230400/1753049329), (-182645760/1753049329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((112230400/1753049329), (-182645760/1753049329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((54659131/2199023255552), (670070053/2199023255552)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-677306317/8796093022208), (-394901031/17592186044416)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((555198451/70368744177664), (-736681727/70368744177664)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((515530475/562949953421312), (406004131/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-1711259831/9007199254740992), (363430673/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((1628343/562949953421312), (-358717667/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((988263529/576460752303423488), (533313511/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-308116199/2305843009213693952), (68693147/576460752303423488)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-435895357/73786976294838206464), (-270059025/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 9 => ⟨((793530011/590295810358705651712), (-66396647/1180591620717411303424)), (33/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-76974383/2361183241434822606848), (251622389/2361183241434822606848)), (27/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-68616489/9444732965739290427392), (-100577547/18889465931478580854784)), (43/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((354110981/604462909807314587353088), (-490668743/1208925819614629174706176)), (17/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((169/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((138444800/2003724529), (-182645760/2003724529)), 0, by norm_num⟩
  | 1 => ⟨((7096255499468800/4014911988116271841), (25286355714048000/4014911988116271841)), 0, by norm_num⟩
  | 2 => ⟨((-1530990371/4398046511104), (-602640183/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((642857489/35184372088832), (-783327239/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-139456911/1125899906842624), (1370559545/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-922361541/18014398509481984), (-859272031/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((1136437861/288230376151711744), (-98823325/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-242018477/2305843009213693952), (468984043/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-104109615/18446744073709551616), (-435716783/36893488147419103232)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((432828729/590295810358705651712), (89003705/590295810358705651712)), (25/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-608299475/18889465931478580854784), (33304095/1180591620717411303424)), (33/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-104682883/604462909807314587353088), (-1476257061/604462909807314587353088)), (43/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((567193523/4835703278458516698824704), (369831733/4835703278458516698824704)), (111/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((169/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((169/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((169/32), (35673/5120)))⁻¹=value ((138444800/2003724529), (-182645760/2003724529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((138444800/2003724529), (-182645760/2003724529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((64855585/2199023255552), (5164411/274877906944)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-162580231/17592186044416), (433682575/70368744177664)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-104357303/281474976710656), (-584519721/281474976710656)), (7/562949953421312), by norm_num⟩
  | 3 => ⟨((1361026027/4503599627370496), (319892927/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-833228341/36028797018963968), (1132226615/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 5 => ⟨((-648108139/288230376151711744), (-1089282201/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 6 => ⟨((1043870787/2305843009213693952), (-74098417/1152921504606846976)), (15/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-408810821/36893488147419103232), (1596265575/36893488147419103232)), (29/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-491685747/147573952589676412928), (-729842567/295147905179352825856)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((745096215/2361183241434822606848), (-113836383/590295810358705651712)), (23/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((50520271/9444732965739290427392), (592733369/18889465931478580854784)), (39/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-1572968985/604462909807314587353088), (-329985957/604462909807314587353088)), (63/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((571877003/4835703278458516698824704), (-219039865/1208925819614629174706176)), (51/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((201/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((54886400/768942843), (-60881920/768942843)), 0, by norm_num⟩
  | 1 => ⟨((115681879654400/197091031933640883), (3341589413888000/591273095800922649)), 0, by norm_num⟩
  | 2 => ⟨((-538057951/2199023255552), (-784892159/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1111654739/70368744177664), (-233422783/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-243469329/562949953421312), (837424127/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((-504748647/36028797018963968), (-1573255161/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 6 => ⟨((642370923/288230376151711744), (578667149/576460752303423488)), (17/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1100162103/9223372036854775808), (483329487/9223372036854775808)), (11/4611686018427387904), by norm_num⟩
  | 8 => ⟨((161041411/73786976294838206464), (-972849387/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((432291917/2361183241434822606848), (759538599/2361183241434822606848)), (33/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-363975637/18889465931478580854784), (-79951729/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1033935977/1208925819614629174706176), (-739561779/1208925819614629174706176)), (97/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-121965711/19342813113834066795298816), (538609037/9671406556917033397649408)), (59/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((201/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((201/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((201/32), (35673/5120)))⁻¹=value ((54886400/768942843), (-60881920/768942843)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((54886400/768942843), (-60881920/768942843))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1011265783/281474976710656), (-279804015/281474976710656)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-146685161/562949953421312), (759606175/562949953421312)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((-1058352683/4503599627370496), (-798693245/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 3 => ⟨((767469725/18014398509481984), (-196640571/9007199254740992)), (11/18014398509481984), by norm_num⟩
  | 4 => ⟨((26110065/144115188075855872), (1885010853/288230376151711744)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-835976527/1152921504606846976), (-366580223/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((605889775/9223372036854775808), (-133251043/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((380449481/147573952589676412928), (318342627/36893488147419103232)), (31/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1023819565/1180591620717411303424), (-140021407/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810378889/18889465931478580854784), (-650253767/9444732965739290427392)), (51/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((613640461/151115727451828646838272), (112804559/18889465931478580854784)), (45/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-368909013/604462909807314587353088), (138657565/1208925819614629174706176)), (75/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((219287419/19342813113834066795298816), (-977792279/19342813113834066795298816)), (31/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((233/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((190873600/2662361329), (-182645760/2662361329)), 0, by norm_num⟩
  | 1 => ⟨((-1536628765491200/7088167846154646241), (34862253735936000/7088167846154646241)), 0, by norm_num⟩
  | 2 => ⟨((-707805119/4398046511104), (-808112275/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1698940493/140737488355328), (37515111/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-528389273/1125899906842624), (846351537/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((70807227/18014398509481984), (-532703479/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((503497707/576460752303423488), (688782063/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1333598357/18446744073709551616), (-237434883/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((895190869/295147905179352825856), (-595729911/295147905179352825856)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-93241681/2361183241434822606848), (1665961273/9444732965739290427392)), (51/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-700404589/151115727451828646838272), (-1160199593/151115727451828646838272)), (29/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((64903715/151115727451828646838272), (140515179/1208925819614629174706176)), (33/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-749841105/38685626227668133590597632), (408746735/38685626227668133590597632)), (75/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((233/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((233/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((233/32), (35673/5120)))⁻¹=value ((190873600/2662361329), (-182645760/2662361329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((190873600/2662361329), (-182645760/2662361329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((426445267/2251799813685248), (-2794871/8796093022208)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((351270013/4503599627370496), (1193449951/9007199254740992)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-654919745/18014398509481984), (48028469/36028797018963968)), (15/36028797018963968), by norm_num⟩
  | 3 => ⟨((12673803/4503599627370496), (-416687359/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((644627785/1152921504606846976), (438260857/576460752303423488)), (19/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-1106049337/9223372036854775808), (680011/36028797018963968)), (23/9223372036854775808), by norm_num⟩
  | 6 => ⟨((324396165/73786976294838206464), (-247916117/18446744073709551616)), (27/73786976294838206464), by norm_num⟩
  | 7 => ⟨((79703331/73786976294838206464), (79271261/73786976294838206464)), (27/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1377811521/9444732965739290427392), (467805439/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((142269065/75557863725914323419136), (-1107570119/75557863725914323419136)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((343373029/302231454903657293676544), (55883325/75557863725914323419136)), (11/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-493158121/4835703278458516698824704), (604947029/9671406556917033397649408)), (37/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-88587093/77371252455336267181195264), (-1569438501/154742504910672534362390528)), (31/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((265/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((217088000/3070322929), (-182645760/3070322929)), 0, by norm_num⟩
  | 1 => ⟨((-6883863049011200/9426882888343139041), (39650202746880000/9426882888343139041)), 0, by norm_num⟩
  | 2 => ⟨((-218338067/2199023255552), (-749497127/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((301843977/35184372088832), (432266129/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-444329023/1125899906842624), (41260253/281474976710656)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((345576459/36028797018963968), (-609620489/36028797018963968)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((94645667/576460752303423488), (1018573601/1152921504606846976)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-295905065/9223372036854775808), (-30379027/1152921504606846976)), (11/18446744073709551616), by norm_num⟩
  | 8 => ⟨((283035355/147573952589676412928), (-13407609/590295810358705651712)), (3/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-634006205/9444732965739290427392), (136592447/2361183241434822606848)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((98603345/151115727451828646838272), (-610773199/151115727451828646838272)), (55/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((469785279/4835703278458516698824704), (784808731/4835703278458516698824704)), (29/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-639220667/77371252455336267181195264), (-440700319/154742504910672534362390528)), (61/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((265/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((265/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((265/32), (35673/5120)))⁻¹=value ((217088000/3070322929), (-182645760/3070322929)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((217088000/3070322929), (-182645760/3070322929))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-198569405/36028797018963968), (-1215309591/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 1 => ⟨((262921109/18014398509481984), (414843307/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 2 => ⟨((-458059439/144115188075855872), (716980173/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 3 => ⟨((-245907813/2305843009213693952), (-1749564657/2305843009213693952)), (5/288230376151711744), by norm_num⟩
  | 4 => ⟨((1024693469/9223372036854775808), (101792343/2305843009213693952)), (27/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-464736467/36893488147419103232), (753506873/73786976294838206464)), (17/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-102431575/295147905179352825856), (-574791441/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((124244083/590295810358705651712), (331646011/4722366482869645213696)), (21/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-319192875/18889465931478580854784), (301434905/18889465931478580854784)), (43/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-372426775/604462909807314587353088), (-1339010357/604462909807314587353088)), (79/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((512579465/2417851639229258349412352), (108069405/2417851639229258349412352)), (37/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-952741345/77371252455336267181195264), (1177186949/77371252455336267181195264)), (129/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-434212527/618970019642690137449562112), (-30042177/19342813113834066795298816)), (55/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((297/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((2457600/35663771), (-5534720/106991313)), 0, by norm_num⟩
  | 1 => ⟨((-11862527180800/11447141057463969), (4534042624000/1271904561940441)), 0, by norm_num⟩
  | 2 => ⟨((-124240973/2199023255552), (-329036247/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((818646603/140737488355328), (259950741/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-666463589/2251799813685248), (52179943/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((691630189/72057594037927936), (-609156243/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-258374893/2305843009213693952), (1244088531/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-372421657/36893488147419103232), (-792770801/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((133348299/147573952589676412928), (565831503/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1644533013/37778931862957161709568), (129550815/18889465931478580854784)), (51/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((399686955/302231454903657293676544), (-823418945/604462909807314587353088)), (25/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-199826415/19342813113834066795298816), (392376303/4835703278458516698824704)), (49/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-16855321/9671406556917033397649408), (-947937243/309485009821345068724781056)), (3/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((297/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((297/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((297/32), (35673/5120)))⁻¹=value ((2457600/35663771), (-5534720/106991313)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((2457600/35663771), (-5534720/106991313))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-153104221/72057594037927936), (-146950407/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 1 => ⟨((1648129117/1152921504606846976), (-49428287/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-150719557/1152921504606846976), (443448317/1152921504606846976)), (23/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-960041811/18446744073709551616), (-1169575755/18446744073709551616)), (23/9223372036854775808), by norm_num⟩
  | 4 => ⟨((986719071/73786976294838206464), (-137733927/73786976294838206464)), (17/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-444047289/590295810358705651712), (1042191315/590295810358705651712)), (11/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-340970375/2361183241434822606848), (-116014627/590295810358705651712)), (27/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((1065217121/37778931862957161709568), (-113792787/37778931862957161709568)), (59/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-186253837/151115727451828646838272), (848326809/302231454903657293676544)), (61/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-452586363/2417851639229258349412352), (-602936697/2417851639229258349412352)), (29/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((72101527/2417851639229258349412352), (-160014975/38685626227668133590597632)), (55/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-151952063/154742504910672534362390528), (201110413/77371252455336267181195264)), (49/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-200649903/1237940039285380274899124224), (-57470113/309485009821345068724781056)), (85/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((329/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((5734400/86032607), (-3886080/86032607)), 0, by norm_num⟩
  | 1 => ⟨((-8890862796800/7401609467216449), (22284337152000/7401609467216449)), 0, by norm_num⟩
  | 2 => ⟨((-30747723/1099511627776), (-140152395/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((33520461/8796093022208), (508980439/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-469910615/2251799813685248), (-77597215/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1114444217/144115188075855872), (-513716581/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-408619507/2305843009213693952), (676643519/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-106491027/147573952589676412928), (-1016930279/73786976294838206464)), (23/147573952589676412928), by norm_num⟩
  | 8 => ⟨((791737671/2361183241434822606848), (1046034775/2361183241434822606848)), (11/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1600344915/75557863725914323419136), (-135838073/18889465931478580854784)), (41/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1049697667/1208925819614629174706176), (-144283387/604462909807314587353088)), (37/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-455454545/19342813113834066795298816), (1066380131/38685626227668133590597632)), (67/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((50189277/309485009821345068724781056), (-1795582611/1237940039285380274899124224)), (121/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((329/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((329/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((329/32), (35673/5120)))⁻¹=value ((5734400/86032607), (-3886080/86032607)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5734400/86032607), (-3886080/86032607))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-538966583/2305843009213693952), (-184262909/4611686018427387904)), (33/4611686018427387904), by norm_num⟩
  | 1 => ⟨((816113215/9223372036854775808), (-210706885/2305843009213693952)), (39/9223372036854775808), by norm_num⟩
  | 2 => ⟨((286849523/36893488147419103232), (1349778557/36893488147419103232)), (3/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-1094737771/147573952589676412928), (-430755601/147573952589676412928)), (49/147573952589676412928), by norm_num⟩
  | 4 => ⟨((330614207/295147905179352825856), (-117869707/147573952589676412928)), (39/590295810358705651712), by norm_num⟩
  | 5 => ⟨((24359237/2361183241434822606848), (240340561/1180591620717411303424)), (103/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-885702223/37778931862957161709568), (-123996563/9444732965739290427392)), (65/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((213160569/75557863725914323419136), (-473394035/302231454903657293676544)), (73/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-33876881/2417851639229258349412352), (867231495/2417851639229258349412352)), (77/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-1213736121/38685626227668133590597632), (-395296045/19342813113834066795298816)), (19/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((1023768973/309485009821345068724781056), (-510710447/309485009821345068724781056)), (73/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-104072685/4951760157141521099596496896), (1719816583/4951760157141521099596496896)), (265/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-1043235873/39614081257132168796771975168), (-169405887/9903520314283042199192993792)), (117/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((361/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((295731200/4608780529), (-182645760/4608780529)), 0, by norm_num⟩
  | 1 => ⟨((-700075255/549755813888), (1397991453/549755813888)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((-167690749/17592186044416), (-1879179843/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((681856061/281474976710656), (113935585/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1277995065/9007199254740992), (-503443681/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1631303083/288230376151711744), (-73369843/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-372180409/2305843009213693952), (667841041/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((340749169/147573952589676412928), (-578818241/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((384196153/4722366482869645213696), (1404573255/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-642526823/75557863725914323419136), (-599211585/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1039611001/2417851639229258349412352), (51944987/604462909807314587353088)), (31/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1199086945/77371252455336267181195264), (445874225/77371252455336267181195264)), (53/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((474173821/1237940039285380274899124224), (-609041049/1237940039285380274899124224)), (45/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((361/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((361/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((361/32), (35673/5120)))⁻¹=value ((295731200/4608780529), (-182645760/4608780529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((295731200/4608780529), (-182645760/4608780529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-305879879/18446744073709551616), (494317767/73786976294838206464)), (7/9223372036854775808), by norm_num⟩
  | 1 => ⟨((181189803/73786976294838206464), (-1462993537/147573952589676412928)), (35/73786976294838206464), by norm_num⟩
  | 2 => ⟨((609908861/295147905179352825856), (355091567/147573952589676412928)), (23/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-833095089/1180591620717411303424), (166308047/2361183241434822606848)), (3/73786976294838206464), by norm_num⟩
  | 4 => ⟨((145138943/2361183241434822606848), (-1056729675/9444732965739290427392)), (79/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((678100401/75557863725914323419136), (659684411/37778931862957161709568)), (109/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-803505753/302231454903657293676544), (-89377993/302231454903657293676544)), (141/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((127002197/604462909807314587353088), (-308881197/1208925819614629174706176)), (41/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((112547361/9671406556917033397649408), (173752475/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-1209597327/309485009821345068724781056), (-76611375/77371252455336267181195264)), (89/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((722663441/2475880078570760549798248448), (-699831527/2475880078570760549798248448)), (173/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((85682883/9903520314283042199192993792), (752099417/19807040628566084398385987584)), (321/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-1076776703/316912650057057350374175801344), (-348850369/316912650057057350374175801344)), (9/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((393/32), (35673/5120)), 0, by norm_num⟩
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
  | 0 => ⟨((107315200/1742152443), (-60881920/1742152443)), 0, by norm_num⟩
  | 1 => ⟨((-1301657328025600/1011698378216956083), (6533555421184000/3035095134650868249)), 0, by norm_num⟩
  | 2 => ⟨((8853093/4398046511104), (-390469393/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((419204737/281474976710656), (48723973/17592186044416)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-212265201/2251799813685248), (-533952605/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((567689425/144115188075855872), (51511255/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1147817005/9223372036854775808), (584069243/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((402348049/147573952589676412928), (-1217443961/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-7023379/590295810358705651712), (1649836661/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-50733665/18889465931478580854784), (-844445505/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((872184625/4835703278458516698824704), (605336095/4835703278458516698824704)), (33/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-149760363/19342813113834066795298816), (-54468205/77371252455336267181195264)), (13/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((310431535/1237940039285380274899124224), (-281266109/2475880078570760549798248448)), (81/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((393/32), (35673/5120)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((393/32), (35673/5120)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((393/32), (35673/5120)))⁻¹=value ((107315200/1742152443), (-60881920/1742152443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((107315200/1742152443), (-60881920/1742152443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-116186419/147573952589676412928), (1171314511/1180591620717411303424)), (87/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-111135449/590295810358705651712), (-874581913/1180591620717411303424)), (29/590295810358705651712), by norm_num⟩
  | 2 => ⟨((1086722013/4722366482869645213696), (451133695/4722366482869645213696)), (5/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-235001591/4722366482869645213696), (568149103/18889465931478580854784)), (43/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((66760945/75557863725914323419136), (-1637501829/151115727451828646838272)), (147/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((400510345/302231454903657293676544), (671669125/604462909807314587353088)), (105/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-566579281/2417851639229258349412352), (307658023/4835703278458516698824704)), (139/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((391470547/38685626227668133590597632), (-1127112921/38685626227668133590597632)), (83/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((335778363/154742504910672534362390528), (222892973/77371252455336267181195264)), (91/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1943706791/4951760157141521099596496896), (30673713/1237940039285380274899124224)), (375/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((195678699/9903520314283042199192993792), (-697875113/19807040628566084398385987584)), (93/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((295836787/158456325028528675187087900672), (274690591/79228162514264337593543950336)), (175/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-927534687/2535301200456458802993406410752), (-7362475/316912650057057350374175801344)), (637/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((188965781/8796093022208), (1765665571/8796093022208)), (1787/8796093022208), by norm_num⟩
  | 1 => ⟨((-138009727/1099511627776), (14503269/68719476736)), (1897/4398046511104), by norm_num⟩
  | 2 => ⟨((-1182705983/8796093022208), (250463965/4398046511104)), (257/549755813888), by norm_num⟩
  | 3 => ⟨((-485120037/8796093022208), (-217552519/17592186044416)), (6065/17592186044416), by norm_num⟩
  | 4 => ⟨((-381784685/35184372088832), (-827607873/70368744177664)), (13631/70368744177664), by norm_num⟩
  | 5 => ⟨((-159569233/281474976710656), (-490726273/140737488355328)), (24841/281474976710656), by norm_num⟩
  | 6 => ⟨((550165065/2251799813685248), (-1317157723/2251799813685248)), (76389/2251799813685248), by norm_num⟩
  | 7 => ⟨((682785063/9007199254740992), (-521788173/9007199254740992)), (50929/4503599627370496), by norm_num⟩
  | 8 => ⟨((439444023/36028797018963968), (-151723751/72057594037927936)), (480769/144115188075855872), by norm_num⟩
  | 9 => ⟨((1581231443/1152921504606846976), (107667313/288230376151711744)), (1019971/1152921504606846976), by norm_num⟩
  | 10 => ⟨((1078622467/9223372036854775808), (838498077/9223372036854775808)), (1969317/9223372036854775808), by norm_num⟩
  | 11 => ⟨((274006247/36893488147419103232), (898265881/73786976294838206464)), (3495039/73786976294838206464), by norm_num⟩
  | 12 => ⟨((39047277/147573952589676412928), (1477011093/1180591620717411303424)), (11497203/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((188965781/8796093022208), (1765665571/8796093022208)), (447/2199023255552), by norm_num⟩
  | 1 => ⟨((-138009727/1099511627776), (14503269/68719476736)), (949/2199023255552), by norm_num⟩
  | 2 => ⟨((-1182705983/8796093022208), (250463965/4398046511104)), (4113/8796093022208), by norm_num⟩
  | 3 => ⟨((-485120037/8796093022208), (-217552519/17592186044416)), (3033/8796093022208), by norm_num⟩
  | 4 => ⟨((-381784685/35184372088832), (-827607873/70368744177664)), (6817/35184372088832), by norm_num⟩
  | 5 => ⟨((-159569233/281474976710656), (-490726273/140737488355328)), (24853/281474976710656), by norm_num⟩
  | 6 => ⟨((550165065/2251799813685248), (-1317157723/2251799813685248)), (1195/35184372088832), by norm_num⟩
  | 7 => ⟨((682785063/9007199254740992), (-521788173/9007199254740992)), (102219/9007199254740992), by norm_num⟩
  | 8 => ⟨((439444023/36028797018963968), (-151723751/72057594037927936)), (243267/72057594037927936), by norm_num⟩
  | 9 => ⟨((1581231443/1152921504606846976), (107667313/288230376151711744)), (133261/144115188075855872), by norm_num⟩
  | 10 => ⟨((1078622467/9223372036854775808), (838498077/9223372036854775808)), (584563/2305843009213693952), by norm_num⟩
  | 11 => ⟨((274006247/36893488147419103232), (898265881/73786976294838206464)), (6446519/73786976294838206464), by norm_num⟩
  | 12 => ⟨((39047277/147573952589676412928), (1477011093/1180591620717411303424)), (14680217/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile038Gamma
