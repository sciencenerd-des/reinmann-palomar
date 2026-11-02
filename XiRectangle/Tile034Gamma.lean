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
namespace Reinmann.XiRectangle.Tile034Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8319/640))
  have he : value ((7/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((23/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((215/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((22016000/365045761), (-10648320/365045761)), 0, by norm_num⟩
  | 1 => ⟨((-185658768588800/133258407624069121), (234433413120000/133258407624069121)), 0, by norm_num⟩
  | 2 => ⟨((287711137/17592186044416), (-161342597/2199023255552)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((324779991/562949953421312), (344949511/140737488355328)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-957376405/18014398509481984), (-589937489/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((737250807/288230376151711744), (345856413/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-436418787/4611686018427387904), (5174315/4611686018427387904)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((837426911/295147905179352825856), (-417354327/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-153325089/2361183241434822606848), (198393347/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((221438419/302231454903657293676544), (-1052007511/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((34663733/1208925819614629174706176), (559249217/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-49351027/19342813113834066795298816), (-949885397/309485009821345068724781056)), (29/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1205279205/9903520314283042199192993792), (548077629/9903520314283042199192993792)), (21/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (8319/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (8319/1280)))⁻¹=value ((22016000/365045761), (-10648320/365045761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((22016000/365045761), (-10648320/365045761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((725621647/268435456), (241856389/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((11008000/365045761), (-5324160/365045761)), 0, by norm_num⟩
  | 2 => ⟨((-46414692147200/133258407624069121), (58608353280000/133258407624069121)), 0, by norm_num⟩
  | 3 => ⟨((383614849/140737488355328), (-1720987701/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((324779991/4503599627370496), (344949511/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((-191475281/36028797018963968), (-471949991/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((245750269/1152921504606846976), (115285471/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-62345541/9223372036854775808), (23654011/295147905179352825856)), (9/147573952589676412928), by norm_num⟩
  | 8 => ⟨((837426911/4722366482869645213696), (-417354327/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-17036121/4722366482869645213696), (705398567/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((177150735/4835703278458516698824704), (-841606009/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((201679901/154742504910672534362390528), (1626906813/309485009821345068724781056)), (59/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-526410955/4951760157141521099596496896), (-633256931/4951760157141521099596496896)), (5/618970019642690137449562112), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (177/20480)), 0, by norm_num⟩
  | 45 => ⟨((92789634353/4080638361600), (-699327/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-9954778072673/459643105050624), (6575608855627/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((763402269/34359738368), (-181662727/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-198192357/8589934592), (368283739/34359738368)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((203853023/8589934592), (-381006813/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-208705347/8589934592), (196120985/17179869184)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((26730989/1073741824), (-401925429/34359738368)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-219484345/8589934592), (411831959/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((7046579/268435456), (-422576655/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-463620457/17179869184), (434056359/34359738368)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((238474009/8589934592), (-446163185/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-61382559/2147483648), (229464755/17179869184)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((15813739/536870912), (-118109777/8589934592)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-1043927329/34359738368), (15211621/1073741824)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((538921419/17179869184), (-251002031/17179869184)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1114033241/34359738368), (32388757/2147483648)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((576368167/17179869184), (-267758899/17179869184)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-1194223485/34359738368), (138502343/8589934592)), (1/17179869184), by norm_num⟩
  | 27 => ⟨((1238806001/34359738368), (-573823043/34359738368)), (1/17179869184), by norm_num⟩
  | 26 => ⟨((-643421665/17179869184), (148776449/8589934592)), (1/17179869184), by norm_num⟩
  | 25 => ⟨((1338752865/34359738368), (-618027181/34359738368)), (1/17179869184), by norm_num⟩
  | 24 => ⟨((-1395022039/34359738368), (321391949/17179869184)), (1/17179869184), by norm_num⟩
  | 23 => ⟨((728111797/17179869184), (-334802723/17179869184)), (1/17179869184), by norm_num⟩
  | 22 => ⟨((-761517541/17179869184), (174690307/8589934592)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((199532997/4294967296), (-365284807/17179869184)), (3/17179869184), by norm_num⟩
  | 20 => ⟨((-838440169/17179869184), (191352397/8589934592)), (3/17179869184), by norm_num⟩
  | 19 => ⟨((883029939/17179869184), (-50233493/2147483648)), (3/17179869184), by norm_num⟩
  | 18 => ⟨((-932620711/17179869184), (423049459/17179869184)), (3/17179869184), by norm_num⟩
  | 17 => ⟨((494051195/8589934592), (-446585641/17179869184)), (3/17179869184), by norm_num⟩
  | 16 => ⟨((-1050588987/17179869184), (236445915/8589934592)), (3/17179869184), by norm_num⟩
  | 15 => ⟨((1121493789/17179869184), (-125621765/4294967296)), (3/17179869184), by norm_num⟩
  | 14 => ⟨((-150329615/2147483648), (536028535/17179869184)), (3/17179869184), by norm_num⟩
  | 13 => ⟨((1296402799/17179869184), (-287180423/8589934592)), (3/17179869184), by norm_num⟩
  | 12 => ⟨((-1405976727/17179869184), (618587815/17179869184)), (3/17179869184), by norm_num⟩
  | 11 => ⟨((767855577/8589934592), (-335090049/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-422928179/4294967296), (365570601/8589934592)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((941411153/8589934592), (-100534065/2147483648)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-265291621/2147483648), (446806949/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((303898113/2147483648), (-502605995/8589934592)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-711090675/4294967296), (287135285/4294967296)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((428122193/2147483648), (-41854047/536870912)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-537432705/2147483648), (401432971/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1440739635/4294967296), (-125225897/1073741824)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-271844935/536870912), (83181621/536870912)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1093240211/1073741824), (-247491575/1073741824)), (1/1073741824), by norm_num⟩
  | 0 => ⟨((-149115769/2147483648), (967425555/2147483648)), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (8319/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (8319/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (8319/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((725621647/268435456), (241856389/536870912)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (8319/1280))) (z:=((-41/256), (8319/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((725621647/268435456), (241856389/536870912))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((207/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1075223909/33554432), (785060291/33554432)), (1/8388608), by norm_num⟩
  | 1 => ⟨((985962399/536870912), (62421651/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1027813280345600/133258407624069121), (-515194686361440/133258407624069121)), 0, by norm_num⟩
  | 3 => ⟨((-261304921/4398046511104), (43659303/549755813888)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((171508675/562949953421312), (-946731227/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((355561631/36028797018963968), (1221825935/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-316737943/576460752303423488), (-686909391/1152921504606846976)), (59/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1372811967/73786976294838206464), (524062541/73786976294838206464)), (145/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-150860673/295147905179352825856), (58082791/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((880668445/75557863725914323419136), (-136832817/18889465931478580854784)), (131/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-240206191/1208925819614629174706176), (774720355/2417851639229258349412352)), (351/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((156833847/154742504910672534362390528), (-1630880903/154742504910672534362390528)), (927/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((532112005/4951760157141521099596496896), (700616505/2475880078570760549798248448)), (625/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((624336229/33554432), (566982697/33554432)), (5/33554432), by norm_num⟩
  | 1 => ⟨((717526943/536870912), (62421651/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1027813280345600/133258407624069121), (-515194686361440/133258407624069121)), 0, by norm_num⟩
  | 3 => ⟨((-261304921/4398046511104), (43659303/549755813888)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((171508675/562949953421312), (-946731227/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((355561631/36028797018963968), (1221825935/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-316737943/576460752303423488), (-686909391/1152921504606846976)), (59/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1372811967/73786976294838206464), (524062541/73786976294838206464)), (145/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-150860673/295147905179352825856), (58082791/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((880668445/75557863725914323419136), (-136832817/18889465931478580854784)), (131/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-240206191/1208925819614629174706176), (774720355/2417851639229258349412352)), (351/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((156833847/154742504910672534362390528), (-1630880903/154742504910672534362390528)), (927/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((532112005/4951760157141521099596496896), (700616505/2475880078570760549798248448)), (625/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((327585345/16777216), (566982697/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((717526943/536870912), (62421651/268435456)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1027813280345600/133258407624069121), (-515194686361440/133258407624069121)), 0, by norm_num⟩
  | 3 => ⟨((-261304921/4398046511104), (43659303/549755813888)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((171508675/562949953421312), (-946731227/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((355561631/36028797018963968), (1221825935/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-316737943/576460752303423488), (-686909391/1152921504606846976)), (59/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1372811967/73786976294838206464), (524062541/73786976294838206464)), (145/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-150860673/295147905179352825856), (58082791/1180591620717411303424)), (189/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((880668445/75557863725914323419136), (-136832817/18889465931478580854784)), (131/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-240206191/1208925819614629174706176), (774720355/2417851639229258349412352)), (351/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((156833847/154742504910672534362390528), (-1630880903/154742504910672534362390528)), (927/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((532112005/4951760157141521099596496896), (700616505/2475880078570760549798248448)), (625/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((371317537177600/133258407624069121), (-468866826240000/133258407624069121)), 0, by norm_num⟩
  | 1 => ⟨((-287711137/4398046511104), (161342597/549755813888)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-243584993/70368744177664), (-1034848533/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((239344101/562949953421312), (589937489/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-921563509/36028797018963968), (-432320517/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((654628181/576460752303423488), (-15522945/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-732748547/18446744073709551616), (91296259/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((153325089/147573952589676412928), (-198393347/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-249118221/18889465931478580854784), (591754225/9444732965739290427392)), (19/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-173318665/302231454903657293676544), (-1398123043/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((542861297/9671406556917033397649408), (653046211/9671406556917033397649408)), (3/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-225989851/77371252455336267181195264), (-205529111/154742504910672534362390528)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1152814177/9903520314283042199192993792), (-27340081/9903520314283042199192993792)), (53/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((287711137/4398046511104), (-161342597/549755813888)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((243584993/35184372088832), (1034848533/35184372088832)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((-718032303/562949953421312), (-442453117/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((921563509/9007199254740992), (432320517/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((-409142613/72057594037927936), (19403681/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((549561411/2305843009213693952), (-273888777/2305843009213693952)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-134159453/18446744073709551616), (694376715/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((249118221/2361183241434822606848), (-591754225/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((97491749/18889465931478580854784), (196611053/9444732965739290427392)), (25/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-678576621/1208925819614629174706176), (-816307763/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1242944181/38685626227668133590597632), (8831329/604462909807314587353088)), (17/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-864610633/618970019642690137449562112), (41010121/1237940039285380274899124224)), (53/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((481103017/9903520314283042199192993792), (-493867805/19807040628566084398385987584)), (41/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-324779991/70368744177664), (-344949511/17592186044416)), (3/70368744177664), by norm_num⟩
  | 1 => ⟨((239344101/140737488355328), (1179874979/562949953421312)), (3/562949953421312), by norm_num⟩
  | 2 => ⟨((-921563509/4503599627370496), (-432320517/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 3 => ⟨((136380871/9007199254740992), (-12935787/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((-915935685/1152921504606846976), (456481295/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((134159453/4611686018427387904), (-694376715/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-290637925/590295810358705651712), (1380759859/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-259977997/9444732965739290427392), (-1048592283/9444732965739290427392)), (15/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((254466233/75557863725914323419136), (612230823/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-1035786817/4835703278458516698824704), (-471004213/4835703278458516698824704)), (3/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((792559747/77371252455336267181195264), (-37592611/154742504910672534362390528)), (5/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-481103017/1237940039285380274899124224), (493867805/2475880078570760549798248448)), (33/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((218124237/19807040628566084398385987584), (-1157053367/79228162514264337593543950336)), (13/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-957376405/1125899906842624), (-589937489/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((921563509/4503599627370496), (432320517/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((-409142613/18014398509481984), (19403681/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 3 => ⟨((915935685/576460752303423488), (-456481295/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((-670797265/9223372036854775808), (867970893/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((54494611/36893488147419103232), (-1035569895/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 6 => ⟨((56870187/590295810358705651712), (114689781/295147905179352825856)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-254466233/18889465931478580854784), (-612230823/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((582630085/604462909807314587353088), (132469935/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-247674921/4835703278458516698824704), (46990763/38685626227668133590597632)), (45/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((1323033297/618970019642690137449562112), (-679068231/618970019642690137449562112)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-654372711/9903520314283042199192993792), (867790025/9903520314283042199192993792)), (35/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((75477861/79228162514264337593543950336), (-1523724085/316912650057057350374175801344)), (57/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-737250807/9007199254740992), (-345856413/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((654628181/36028797018963968), (-15522945/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((-549561411/288230376151711744), (273888777/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((134159453/1152921504606846976), (-694376715/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-54494611/18446744073709551616), (517784947/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-272976897/1180591620717411303424), (-1101021897/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((712505453/18889465931478580854784), (857123153/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-116526017/37778931862957161709568), (-26493987/18889465931478580854784)), (9/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((222907429/1208925819614629174706176), (-42291687/9671406556917033397649408)), (19/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-661516649/77371252455336267181195264), (84883529/19342813113834066795298816)), (19/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((719809983/2475880078570760549798248448), (-238642257/618970019642690137449562112)), (35/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-181146867/39614081257132168796771975168), (914234451/39614081257132168796771975168)), (33/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-356842337/1267650600228229401496703205376), (-1369559155/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-436418787/72057594037927936), (5174315/72057594037927936)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((183187137/144115188075855872), (-91296259/144115188075855872)), (7/576460752303423488), by norm_num⟩
  | 2 => ⟨((-134159453/1152921504606846976), (694376715/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((290637925/73786976294838206464), (-345189965/18446744073709551616)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((227480747/590295810358705651712), (917518247/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-712505453/9444732965739290427392), (-53570197/590295810358705651712)), (17/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((1087576159/151115727451828646838272), (61819303/18889465931478580854784)), (11/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1188839621/2417851639229258349412352), (14097229/1208925819614629174706176)), (25/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((496137487/19342813113834066795298816), (-254650587/19342813113834066795298816)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-599841653/618970019642690137449562112), (397737095/309485009821345068724781056)), (15/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((332102589/19807040628566084398385987584), (-1676096495/19807040628566084398385987584)), (29/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((356842337/316912650057057350374175801344), (342389789/79228162514264337593543950336)), (7/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-737652561/5070602400912917605986812821504), (-108284135/633825300114114700748351602688)), (51/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-837426911/2305843009213693952), (417354327/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((613300357/9223372036854775808), (-198393347/2305843009213693952)), (13/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-124559111/36893488147419103232), (1183508451/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-129988999/295147905179352825856), (-1048592283/590295810358705651712)), (1/36893488147419103232), by norm_num⟩
  | 4 => ⟨((254466233/2361183241434822606848), (612230823/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-116526017/9444732965739290427392), (-26493987/4722366482869645213696)), (5/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((1188839621/1208925819614629174706176), (-14097229/604462909807314587353088)), (27/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-1134028541/19342813113834066795298816), (145514621/4835703278458516698824704)), (33/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((385612491/154742504910672534362390528), (-1022752531/309485009821345068724781056)), (39/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-237216135/4951760157141521099596496896), (598605891/2475880078570760549798248448)), (43/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-140188061/39614081257132168796771975168), (-538041097/39614081257132168796771975168)), (45/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((79034203/158456325028528675187087900672), (742519783/1267650600228229401496703205376)), (45/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-757362149/20282409603651670423947251286016), (-333617735/20282409603651670423947251286016)), (11/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-153325089/9223372036854775808), (198393347/9223372036854775808)), (9/18446744073709551616), by norm_num⟩
  | 1 => ⟨((124559111/73786976294838206464), (-1183508451/147573952589676412928)), (11/73786976294838206464), by norm_num⟩
  | 2 => ⟨((389966995/1180591620717411303424), (1572888425/1180591620717411303424)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-508932467/4722366482869645213696), (-612230823/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((582630085/37778931862957161709568), (132469935/18889465931478580854784)), (29/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((-1783259431/1208925819614629174706176), (42291687/1208925819614629174706176)), (45/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((992274973/9671406556917033397649408), (-254650587/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-385612491/77371252455336267181195264), (511376265/77371252455336267181195264)), (21/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((33358519/309485009821345068724781056), (-1346863255/2475880078570760549798248448)), (51/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((43808769/4951760157141521099596496896), (1345102743/39614081257132168796771975168)), (59/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-869376233/633825300114114700748351602688), (-510482351/316912650057057350374175801344)), (65/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((1136043223/10141204801825835211973625643008), (250213301/5070602400912917605986812821504)), (67/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-554082683/81129638414606681695789005144064), (39431027/162259276829213363391578010288128)), (69/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-221438419/590295810358705651712), (1052007511/590295810358705651712)), (27/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-346637329/2361183241434822606848), (-349530761/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 2 => ⟨((678576621/9444732965739290427392), (816307765/9444732965739290427392)), (27/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-517893409/37778931862957161709568), (-471004213/75557863725914323419136)), (31/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((1981399369/1208925819614629174706176), (-46990763/1208925819614629174706176)), (59/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-661516649/4835703278458516698824704), (84883529/1208925819614629174706176)), (49/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((149960413/19342813113834066795298816), (-397737095/38685626227668133590597632)), (37/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-237216135/1237940039285380274899124224), (598605891/618970019642690137449562112)), (51/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-43808769/2475880078570760549798248448), (-1345102743/19807040628566084398385987584)), (1/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((120746699/39614081257132168796771975168), (1134405225/316912650057057350374175801344)), (39/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-1388497273/5070602400912917605986812821504), (-305816257/2535301200456458802993406410752)), (89/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((1477553821/81129638414606681695789005144064), (-52574703/81129638414606681695789005144064)), (3/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-38315393/40564819207303340847894502572032), (647790861/1298074214633706907132624082305024)), (51/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((34663733/1180591620717411303424), (559249217/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-542861297/18889465931478580854784), (-653046211/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((1242944181/151115727451828646838272), (565205057/151115727451828646838272)), (3/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-1585119495/1208925819614629174706176), (37592611/1208925819614629174706176)), (29/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((661516649/4835703278458516698824704), (-84883529/1208925819614629174706176)), (59/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-719809983/77371252455336267181195264), (954569029/77371252455336267181195264)), (13/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((332102589/1237940039285380274899124224), (-838048247/618970019642690137449562112)), (81/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((140188061/4951760157141521099596496896), (538041097/4951760157141521099596496896)), (59/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-869376233/158456325028528675187087900672), (-510482351/79228162514264337593543950336)), (39/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((1388497273/2535301200456458802993406410752), (305816257/1267650600228229401496703205376)), (99/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-1625309203/40564819207303340847894502572032), (57832173/40564819207303340847894502572032)), (117/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((735655545/324518553658426726783156020576256), (-388674517/324518553658426726783156020576256)), (67/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-484440015/5192296858534827628530496329220096), (658533299/5192296858534827628530496329220096)), (9/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504000/1095137283), (-887360/365045761)), 0, by norm_num⟩
  | 1 => ⟨((-46414692147200/399775222872207363), (19536117760000/133258407624069121)), 0, by norm_num⟩
  | 2 => ⟨((383614849/281474976710656), (-1720987701/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((108259997/2251799813685248), (919865363/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-638250937/144115188075855872), (-786583319/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((245750269/1152921504606846976), (115285471/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-145472929/18446744073709551616), (13798173/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1116569215/4722366482869645213696), (-139118109/1180591620717411303424)), (17/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-51108363/9444732965739290427392), (1058097851/151115727451828646838272)), (25/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((295251225/4835703278458516698824704), (-1402676681/4835703278458516698824704)), (37/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((369746485/154742504910672534362390528), (1491331245/154742504910672534362390528)), (27/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-526410955/2475880078570760549798248448), (-633256931/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((401759735/39614081257132168796771975168), (182692543/39614081257132168796771975168)), (7/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((327669665/16777216), (141725283/8388608)), (7/33554432), by norm_num⟩
  | 1 => ⟨((717464611/536870912), (124922009/536870912)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((530122433/68719476736), (-532197557/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-522186951/8796093022208), (175086365/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((169015507/562949953421312), (-474901909/281474976710656)), (13/562949953421312), by norm_num⟩
  | 5 => ⟨((363241327/36028797018963968), (612714303/18014398509481984)), (43/36028797018963968), by norm_num⟩
  | 6 => ⟨((-80320993/144115188075855872), (-686801593/1152921504606846976)), (15/288230376151711744), by norm_num⟩
  | 7 => ⟨((1390258361/73786976294838206464), (515367659/73786976294838206464)), (73/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1219662475/2361183241434822606848), (132698361/2361183241434822606848)), (95/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((885281745/75557863725914323419136), (-569248091/75557863725914323419136)), (33/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-474635093/2417851639229258349412352), (399011203/1208925819614629174706176)), (353/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((61966581/77371252455336267181195264), (-1670459461/154742504910672534362390528)), (465/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((145582993/1237940039285380274899124224), (712034789/2475880078570760549798248448)), (627/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-102297293/562949953421312), (917860107/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-173215995/9007199254740992), (-367946145/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((510600749/144115188075855872), (629266655/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 3 => ⟨((-655334051/2305843009213693952), (-307427923/2305843009213693952)), (5/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1163783433/73786976294838206464), (-13798173/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-781598451/1180591620717411303424), (389530705/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((381609111/18889465931478580854784), (-987557995/37778931862957161709568)), (7/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-177150735/604462909807314587353088), (841606009/604462909807314587353088)), (3/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-34663733/2417851639229258349412352), (-1118498435/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((482543375/309485009821345068724781056), (1160971041/618970019642690137449562112)), (1/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-441935709/4951760157141521099596496896), (-401923595/9903520314283042199192993792)), (25/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((153708557/39614081257132168796771975168), (-29162753/316912650057057350374175801344)), (39/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-342117701/2535301200456458802993406410752), (702389767/10141204801825835211973625643008)), (59/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((163834831/8388608), (566901159/33554432)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1434929201/1073741824), (124921965/536870912)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1060245353/137438953472), (-532196957/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-522189451/8796093022208), (700344287/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((84512193/281474976710656), (-949803923/562949953421312)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((363217475/36028797018963968), (612720247/18014398509481984)), (11/9007199254740992), by norm_num⟩
  | 6 => ⟨((-160636163/288230376151711744), (-686831731/1152921504606846976)), (61/1152921504606846976), by norm_num⟩
  | 7 => ⟨((21722449/1152921504606846976), (257735197/36893488147419103232)), (147/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-609848163/1180591620717411303424), (66280913/1180591620717411303424)), (191/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((885399553/75557863725914323419136), (-569106371/75557863725914323419136)), (265/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-237425441/1208925819614629174706176), (99740535/302231454903657293676544)), (177/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((62266793/77371252455336267181195264), (-1670473701/154742504910672534362390528)), (931/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((581663773/4951760157141521099596496896), (712206271/2475880078570760549798248448)), (1255/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-778058285/1152921504606846976), (-479441261/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((748953201/4611686018427387904), (175673099/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-1330038209/73786976294838206464), (15769341/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 3 => ⟨((744379477/590295810358705651712), (-46372703/73786976294838206464)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-545155873/9444732965739290427392), (705398567/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((354301471/302231454903657293676544), (-420803005/75557863725914323419136)), (17/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((184873243/2417851639229258349412352), (93208203/302231454903657293676544)), (21/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-827217215/77371252455336267181195264), (-248779509/19342813113834066795298816)), (21/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((947005091/1237940039285380274899124224), (53829053/154742504910672534362390528)), (21/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1610280121/39614081257132168796771975168), (38189319/39614081257132168796771975168)), (19/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((268806765/158456325028528675187087900672), (-551877673/633825300114114700748351602688)), (17/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-33237979/633825300114114700748351602688), (88156447/1267650600228229401496703205376)), (15/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((245362951/324518553658426726783156020576256), (-1238328145/324518553658426726783156020576256)), (47/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((163834831/8388608), (566901159/33554432)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1434929201/1073741824), (124921965/536870912)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1060245351/137438953472), (-532196957/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-4079605/68719476736), (700344281/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((84512177/281474976710656), (-949803881/562949953421312)), (15/562949953421312), by norm_num⟩
  | 5 => ⟨((363217517/36028797018963968), (1225440293/36028797018963968)), (45/36028797018963968), by norm_num⟩
  | 6 => ⟨((-160636141/288230376151711744), (-686831375/1152921504606846976)), (31/576460752303423488), by norm_num⟩
  | 7 => ⟨((1390235947/73786976294838206464), (515469445/73786976294838206464)), (37/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-152461815/295147905179352825856), (132562647/2361183241434822606848)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((442698241/37778931862957161709568), (-284553149/37778931862957161709568)), (133/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-118711695/604462909807314587353088), (797922175/2417851639229258349412352)), (355/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((124525471/154742504910672534362390528), (-417615735/38685626227668133590597632)), (233/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((581667517/4951760157141521099596496896), (1424393647/4951760157141521099596496896)), (157/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((532015283/147573952589676412928), (-12615473/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-893255373/1180591620717411303424), (445177949/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 2 => ⟨((654187047/9444732965739290427392), (-846478281/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-177150735/75557863725914323419136), (420803005/37778931862957161709568)), (19/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-277309863/1208925819614629174706176), (-559249217/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((217144519/4835703278458516698824704), (522436969/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-1325807127/309485009821345068724781056), (-602885393/309485009821345068724781056)), (7/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((1449252109/4951760157141521099596496896), (-34370387/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((-302407611/19807040628566084398385987584), (38803899/4951760157141521099596496896)), (9/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((731235539/1267650600228229401496703205376), (-969720917/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-202424435/20282409603651670423947251286016), (1021620721/20282409603651670423947251286016)), (9/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((-435007801/649037107316853453566312041152512), (-417389457/162259276829213363391578010288128)), (69/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((449616799/5192296858534827628530496329220096), (132003517/1298074214633706907132624082305024)), (63/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((163834831/8388608), (566901159/33554432)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1434929201/1073741824), (124921965/536870912)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1060245351/137438953472), (-532196957/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-4079605/68719476736), (700344281/8796093022208)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((84512177/281474976710656), (-474901941/281474976710656)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((363217519/36028797018963968), (1225440295/36028797018963968)), (23/18014398509481984), by norm_num⟩
  | 6 => ⟨((-642544569/1152921504606846976), (-686831377/1152921504606846976)), (63/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1390235969/73786976294838206464), (128867361/18446744073709551616)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-304923639/590295810358705651712), (66281333/1180591620717411303424)), (193/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((442698263/37778931862957161709568), (-142276589/18889465931478580854784)), (267/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-118711701/604462909807314587353088), (797922297/2417851639229258349412352)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((124525367/154742504910672534362390528), (-835231669/77371252455336267181195264)), (933/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((290833973/2475880078570760549798248448), (1424394151/4951760157141521099596496896)), (1257/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-528635997/37778931862957161709568), (684022853/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((53682041/37778931862957161709568), (-63758031/9444732965739290427392)), (5/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((336133167/1208925819614629174706176), (1355755679/1208925819614629174706176)), (27/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-877351593/9671406556917033397649408), (-263857055/2417851639229258349412352)), (7/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((502199669/38685626227668133590597632), (228365679/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-768542785/618970019642690137449562112), (36453441/1237940039285380274899124224)), (5/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((855294253/9903520314283042199192993792), (-438993605/9903520314283042199192993792)), (29/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-166189895/39614081257132168796771975168), (440782235/79228162514264337593543950336)), (37/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((230027767/2535301200456458802993406410752), (-1160932637/2535301200456458802993406410752)), (45/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((302088751/40564819207303340847894502572032), (1159415159/40564819207303340847894502572032)), (13/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-187340333/162259276829213363391578010288128), (-880023447/649037107316853453566312041152512)), (57/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((979215707/10384593717069655257060992658440192), (215672071/5192296858534827628530496329220096)), (59/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-1910372617/332306998946228968225951765070086144), (67975373/332306998946228968225951765070086144)), (15/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((163834831/8388608), (566901159/33554432)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1434929201/1073741824), (124921965/536870912)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1060245351/137438953472), (-532196957/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-4079605/68719476736), (700344281/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((84512177/281474976710656), (-474901941/281474976710656)), (17/562949953421312), by norm_num⟩
  | 5 => ⟨((363217519/36028797018963968), (1225440295/36028797018963968)), (47/36028797018963968), by norm_num⟩
  | 6 => ⟨((-642544569/1152921504606846976), (-686831377/1152921504606846976)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((1390235969/73786976294838206464), (128867361/18446744073709551616)), (75/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-304923639/590295810358705651712), (132562665/2361183241434822606848)), (97/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((885396527/75557863725914323419136), (-284553177/37778931862957161709568)), (67/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-474846807/2417851639229258349412352), (398961147/1208925819614629174706176)), (357/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((62262691/77371252455336267181195264), (-417615833/38685626227668133590597632)), (467/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((290833959/2475880078570760549798248448), (178049269/618970019642690137449562112)), (629/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-136127777/2417851639229258349412352), (-1098112437/4835703278458516698824704)), (5/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((532966989/9671406556917033397649408), (20035739/302231454903657293676544)), (31/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-1220290009/77371252455336267181195264), (-277451753/38685626227668133590597632)), (3/4835703278458516698824704), by norm_num⟩
  | 3 => ⟨((1556228761/618970019642690137449562112), (-2306715/38685626227668133590597632)), (29/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((-324729851/1237940039285380274899124224), (333345693/2475880078570760549798248448)), (59/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((706690569/39614081257132168796771975168), (-468585423/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((-326049615/633825300114114700748351602688), (822773797/316912650057057350374175801344)), (81/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-137632963/2535301200456458802993406410752), (-1056469285/5070602400912917605986812821504)), (59/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((106691349/10141204801825835211973625643008), (1002356377/81129638414606681695789005144064)), (39/40564819207303340847894502572032), by norm_num⟩
  | 9 => ⟨((-1363190219/1298074214633706907132624082305024), (-300242383/649037107316853453566312041152512)), (49/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((1595685963/20769187434139310514121985316880384), (-56778111/20769187434139310514121985316880384)), (29/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((-361123663/83076749736557242056487941267521536), (190795225/83076749736557242056487941267521536)), (67/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((237805253/1329227995784915872903807060280344576), (-646530727/2658455991569831745807614120560689152)), (9/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((163834831/8388608), (566901159/33554432)), (3/8388608), by norm_num⟩
  | 1 => ⟨((1434929201/1073741824), (124921965/536870912)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1060245351/137438953472), (-532196957/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-4079605/68719476736), (700344281/8796093022208)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((84512177/281474976710656), (-474901941/281474976710656)), (9/281474976710656), by norm_num⟩
  | 5 => ⟨((363217519/36028797018963968), (1225440295/36028797018963968)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-642544569/1152921504606846976), (-686831377/1152921504606846976)), (65/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1390235969/73786976294838206464), (128867361/18446744073709551616)), (151/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-304923639/590295810358705651712), (132562665/2361183241434822606848)), (195/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((885396527/75557863725914323419136), (-284553177/37778931862957161709568)), (269/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-474846807/2417851639229258349412352), (398961147/1208925819614629174706176)), (179/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((124525381/154742504910672534362390528), (-417615833/38685626227668133590597632)), (935/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((581667919/4951760157141521099596496896), (1424394151/4951760157141521099596496896)), (1259/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-476523185458757/4194304), (-590030588802593/2097152)), (649032265/2097152), by norm_num⟩
  | 1 => ⟨((-345453365/4), (-804849817/2)), (979/2), by norm_num⟩
  | 2 => ⟨((-25707827/2), -280674907), (1561/4), by norm_num⟩
  | 3 => ⟨((58359443/4), (-1022924911/8)), 209, by norm_num⟩
  | 4 => ⟨((46987543/4), (-686647425/16)), (2709/32), by norm_num⟩
  | 5 => ⟨(4997105, (-1450417135/128)), (3543/128), by norm_num⟩
  | 6 => ⟨((784184705/512), (-1255033997/512)), (487/64), by norm_num⟩
  | 7 => ⟨((191187081/512), (-913628141/2048)), (463/256), by norm_num⟩
  | 8 => ⟨((623650559/8192), (-569226567/8192)), (777/2048), by norm_num⟩
  | 9 => ⟨((219294403/16384), (-612868623/65536)), (1169/16384), by norm_num⟩
  | 10 => ⟨((271670279/131072), (-570889735/524288)), (3193/262144), by norm_num⟩
  | 11 => ⟨((1204245593/4194304), (-454955833/4194304)), (7997/4194304), by norm_num⟩
  | 12 => ⟨((1208054981/33554432), (-298337337/33554432)), (2315/8388608), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609416598245831/10141204801825835211973625643008), (-1273032478679/5070602400912917605986812821504)), (465851/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1812664095145533/633825300114114700748351602688), (-3120573742979/633825300114114700748351602688)), (572747/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((240989101338945/4951760157141521099596496896), (-3519484868627/39614081257132168796771975168)), (646173/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((482527543682489/618970019642690137449562112), (-3747077033645/2475880078570760549798248448)), (86013/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((113238595202863/9671406556917033397649408), (-3755612144567/154742504910672534362390528)), (344915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((396921209123221/2417851639229258349412352), (-1764990484065/4835703278458516698824704)), (162139/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((323049379829391/151115727451828646838272), (-3097858832519/604462909807314587353088)), (284667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1942163833481883/75557863725914323419136), (-2525598438411/37778931862957161709568)), (928645/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1338390631642695/4722366482869645213696), (-3803493185103/4722366482869645213696)), (349771/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((838868214158707/295147905179352825856), (-5254458287443/590295810358705651712)), (241717/147573952589676412928), by norm_num⟩
  | 8 => ⟨((947006310822155/36893488147419103232), (-6605275495791/73786976294838206464)), (608065/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1902257486578431/9223372036854775808), (-3741224154573/4611686018427387904)), (172325/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1673814377856111/1152921504606846976), (-7547383912347/1152921504606846976)), (1391789/1152921504606846976), by norm_num⟩
  | 5 => ⟨((316195006248407/36028797018963968), (-6677768289611/144115188075855872)), (1232823/144115188075855872), by norm_num⟩
  | 4 => ⟨((798820452055757/18014398509481984), (-10166175325859/36028797018963968)), (939837/18014398509481984), by norm_num⟩
  | 3 => ⟨((1623008738296485/9007199254740992), (-3243434086913/2251799813685248)), (600959/2251799813685248), by norm_num⟩
  | 2 => ⟨((1249622684441897/2251799813685248), (-6690807685151/1125899906842624)), (621797/562949953421312), by norm_num⟩
  | 1 => ⟨((10284115943639/8796093022208), (-21123788735253/1125899906842624)), (3946277/1125899906842624), by norm_num⟩
  | 0 => ⟨((763482691597263/562949953421312), (-46648619151967/1125899906842624)), (2199651/281474976710656), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((763482691597263/562949953421312), (-46648619151967/1125899906842624)), (8391002656103038699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2068964722040097/1125899906842624), (-126531366040579/1125899906842624)), (24594739/1125899906842624), by norm_num⟩
  | 2 => ⟨((946932495627797/281474976710656), (-232515280424561/562949953421312)), (93671/1099511627776), by norm_num⟩
  | 3 => ⟨((1568816742946239/140737488355328), (-391111631550747/140737488355328)), (90576655/140737488355328), by norm_num⟩
  | 4 => ⟨((512527279420229/4398046511104), (-272485356917077/4398046511104)), (78836387/4398046511104), by norm_num⟩
  | 5 => ⟨((669458950197831/68719476736), (-248079208131741/17179869184)), (439737585/68719476736), by norm_num⟩
  | 6 => ⟨((-476523185458757/4194304), (-590030588802593/2097152)), (649032265/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((163834831/8388608), (566901159/33554432)), (3/8388608), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2355200/72591361), (-10648320/72591361)), 0, by norm_num⟩
  | 1 => ⟨((53919875891200/5269505691832321), (25078923264000/5269505691832321)), 0, by norm_num⟩
  | 2 => ⟨((-566312133/1099511627776), (740283913/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-721738959/17592186044416), (-428358933/8796093022208)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((149087239/35184372088832), (-624599445/281474976710656)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((423399433/4503599627370496), (97610001/281474976710656)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-242829319/9007199254740992), (91496889/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((198426077/576460752303423488), (-1151723155/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((162506715/1152921504606846976), (132948127/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-480750503/73786976294838206464), (693796625/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-172348467/295147905179352825856), (-744244485/1180591620717411303424)), (17/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((263078519/4722366482869645213696), (-307917737/9444732965739290427392)), (25/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((449552457/302231454903657293676544), (697371839/151115727451828646838272)), (37/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (8319/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (8319/1280)))⁻¹=value ((2355200/72591361), (-10648320/72591361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2355200/72591361), (-10648320/72591361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/26313387), (-3549440/26313387)), 0, by norm_num⟩
  | 1 => ⟨((1804405145600/230798111803923), (4725014528000/692394335411769)), 0, by norm_num⟩
  | 2 => ⟨((-361750007/549755813888), (389973091/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-256029599/35184372088832), (-1877159831/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((1064658501/281474976710656), (241719315/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-345868299/2251799813685248), (1051074031/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-854282863/72057594037927936), (-292966261/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((1610339561/1152921504606846976), (-447601525/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((-42179995/4611686018427387904), (1918917029/18446744073709551616)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-250309123/36893488147419103232), (-239674489/73786976294838206464)), (11/73786976294838206464), by norm_num⟩
  | 10 => ⟨((922501221/2361183241434822606848), (-886459655/2361183241434822606848)), (33/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((291623687/18889465931478580854784), (42320833/1180591620717411303424)), (25/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-1697480341/604462909807314587353088), (81297565/604462909807314587353088)), (75/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (8319/1280)))⁻¹=value ((1331200/26313387), (-3549440/26313387)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((1331200/26313387), (-3549440/26313387))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34660330700800/1910124574849707), (-22534684672000/1910124574849707)), 0, by norm_num⟩
  | 1 => ⟨((331822267/137438953472), (-70949821/34359738368)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((628751523/4398046511104), (1401243287/4398046511104)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-1187448317/35184372088832), (163724099/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((64019705/140737488355328), (-1732637517/562949953421312)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((1115136031/4503599627370496), (15958937/140737488355328)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-136043961/9007199254740992), (315840483/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((-606743703/576460752303423488), (-927922391/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((346103427/2305843009213693952), (-427666007/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((620867/2305843009213693952), (1866942227/147573952589676412928)), (31/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-575322239/590295810358705651712), (-2351677/9223372036854775808)), (25/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((760690387/18889465931478580854784), (-646484401/9444732965739290427392)), (39/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((324573157/75557863725914323419136), (677047447/151115727451828646838272)), (15/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((55/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/88565761), (-10648320/88565761)), 0, by norm_num⟩
  | 1 => ⟨((40833647411200/7843894021509121), (59971338240000/7843894021509121)), 0, by norm_num⟩
  | 2 => ⟨((-1374695867/2199023255552), (153604173/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((551604653/35184372088832), (-1400387691/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((133292355/70368744177664), (77686039/35184372088832)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((-1738029051/9007199254740992), (49164291/1125899906842624)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((15808713/4503599627370496), (-467951397/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((771515999/1152921504606846976), (719409777/1152921504606846976)), (13/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-135556715/2305843009213693952), (376094177/18446744073709551616)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((189948999/295147905179352825856), (-154300855/36893488147419103232)), (31/295147905179352825856), by norm_num⟩
  | 10 => ⟨((545337889/2361183241434822606848), (810680511/4722366482869645213696)), (47/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-1334607985/75557863725914323419136), (79580551/9444732965739290427392)), (35/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((66600797/1208925819614629174706176), (-1607566085/1208925819614629174706176)), (13/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (8319/1280)))⁻¹=value ((5632000/88565761), (-10648320/88565761)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5632000/88565761), (-10648320/88565761))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-707073827/274877906944), (196735535/137438953472)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-217701123/2199023255552), (-1367210357/2199023255552)), (3/2199023255552), by norm_num⟩
  | 2 => ⟨((1546719691/17592186044416), (297118535/17592186044416)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-379814065/70368744177664), (640496239/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-50431209/70368744177664), (-973099521/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((937858103/9007199254740992), (-85932721/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((18870585/144115188075855872), (749662091/72057594037927936)), (15/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1026155485/1152921504606846976), (-86104185/288230376151711744)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((463273419/9223372036854775808), (-599538717/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((70996655/18446744073709551616), (216135973/36893488147419103232)), (21/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-41850817/73786976294838206464), (86221325/590295810358705651712)), (17/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((8463419/2361183241434822606848), (-452735257/9444732965739290427392)), (55/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1081841499/302231454903657293676544), (455777295/302231454903657293676544)), (11/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((71/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/101468161), (-10648320/101468161)), 0, by norm_num⟩
  | 1 => ⟨((30264001331200/10295787696721921), (77417545728000/10295787696721921)), 0, by norm_num⟩
  | 2 => ⟨((-1099199625/2199023255552), (-15826265/137438953472)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((842667571/35184372088832), (-388835939/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((169855741/562949953421312), (1153227135/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-266386039/2251799813685248), (-518447893/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((1046044881/144115188075855872), (-18668249/4503599627370496)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((-49041159/1152921504606846976), (152578315/288230376151711744)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-484271085/18446744073709551616), (-391013491/18446744073709551616)), (25/36893488147419103232), by norm_num⟩
  | 9 => ⟨((605863451/295147905179352825856), (-22803695/36893488147419103232)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-97066953/2361183241434822606848), (1226436147/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-403540269/75557863725914323419136), (-1028979427/151115727451828646838272)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((331625219/604462909807314587353088), (-87748495/2417851639229258349412352)), (53/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (8319/1280)))⁻¹=value ((7270400/101468161), (-10648320/101468161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7270400/101468161), (-10648320/101468161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-149943183/4398046511104), (409580319/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-398747213/4398046511104), (-433593685/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((30581307/2199023255552), (-774602467/70368744177664)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((182343025/281474976710656), (1318806843/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-648929605/2251799813685248), (-82541357/2251799813685248)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((141445909/9007199254740992), (-123711107/4503599627370496)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((285336609/144115188075855872), (366025207/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1380384917/4611686018427387904), (97879057/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((112392433/36893488147419103232), (-1057956685/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1349466831/590295810358705651712), (710163135/590295810358705651712)), (37/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-804403593/4722366482869645213696), (346716955/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((-481751939/75557863725914323419136), (-1360753149/75557863725914323419136)), (53/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1919940639/1208925819614629174706176), (52060885/1208925819614629174706176)), (87/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((87/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2969600/39215787), (-3549440/39215787)), 0, by norm_num⟩
  | 1 => ⟨((630000025600/512625983343123), (10540417024000/1537877950029369)), 0, by norm_num⟩
  | 2 => ⟨((-392201397/1099511627776), (-448350431/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((399916033/17592186044416), (-148182079/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-134971613/281474976710656), (1517363987/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-771637325/18014398509481984), (-655068701/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((177013107/36028797018963968), (58736735/72057594037927936)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1027993149/4611686018427387904), (220762153/1152921504606846976)), (9/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-8323139/36893488147419103232), (-1279301351/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 9 => ⟨((468202887/590295810358705651712), (762943419/1180591620717411303424)), (17/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-1119706709/18889465931478580854784), (107923815/9444732965739290427392)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((522022997/302231454903657293676544), (-470760707/151115727451828646838272)), (31/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((365500613/4835703278458516698824704), (948359149/4835703278458516698824704)), (21/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (8319/1280)))⁻¹=value ((2969600/39215787), (-3549440/39215787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((2969600/39215787), (-3549440/39215787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((136930869/4398046511104), (137632663/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-979687697/70368744177664), (330555193/70368744177664)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((52256933/140737488355328), (-816327123/281474976710656)), (5/281474976710656), by norm_num⟩
  | 3 => ⟨((851813809/2251799813685248), (69066933/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-455470225/9007199254740992), (280453199/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-57041567/72057594037927936), (-1004308923/144115188075855872)), (13/144115188075855872), by norm_num⟩
  | 6 => ⟨((836046539/1152921504606846976), (139014989/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((-246040625/4611686018427387904), (527642525/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-54117175/18446744073709551616), (-1037096473/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1679077189/2361183241434822606848), (41330459/2361183241434822606848)), (51/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-516153605/18889465931478580854784), (1096645331/18889465931478580854784)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-559975315/151115727451828646838272), (-637919183/151115727451828646838272)), (39/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((137666987/302231454903657293676544), (-89671157/604462909807314587353088)), (33/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((103/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10547200/137103361), (-10648320/137103361)), 0, by norm_num⟩
  | 1 => ⟨((1071645491200/18797331597496321), (112309960704000/18797331597496321)), 0, by norm_num⟩
  | 2 => ⟨((-257519573/1099511627776), (-1001006707/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((627949055/35184372088832), (-23969381/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-758025175/1125899906842624), (397539921/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-27495837/18014398509481984), (-120037617/2251799813685248)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((613586461/288230376151711744), (573914541/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-1468421455/9223372036854775808), (28035697/4611686018427387904)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((868872565/147573952589676412928), (-946883731/147573952589676412928)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((53597417/2361183241434822606848), (1122598603/2361183241434822606848)), (17/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-730490733/37778931862957161709568), (-82197471/4722366482869645213696)), (43/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((858140985/604462909807314587353088), (-98363599/1208925819614629174706176)), (107/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-995136049/19342813113834066795298816), (563457527/9671406556917033397649408)), (133/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (8319/1280)))⁻¹=value ((10547200/137103361), (-10648320/137103361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10547200/137103361), (-10648320/137103361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1358294999/281474976710656), (-1504147/140737488355328)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((-501803983/562949953421312), (917869311/562949953421312)), (9/562949953421312), by norm_num⟩
  | 2 => ⟨((-508257041/2251799813685248), (-786498161/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 3 => ⟨((1268275921/18014398509481984), (-52545731/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 4 => ⟨((-71216463/18014398509481984), (668771107/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 5 => ⟨((-116803935/144115188075855872), (-283944297/288230376151711744)), (23/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1327662831/9223372036854775808), (-35297/1125899906842624)), (27/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-293713509/73786976294838206464), (1131908449/73786976294838206464)), (29/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-179169063/147573952589676412928), (-624183915/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1358406919/9444732965739290427392), (-570064553/9444732965739290427392)), (55/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-7380215/9444732965739290427392), (547616667/37778931862957161709568)), (51/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-692575565/604462909807314587353088), (-377694753/604462909807314587353088)), (89/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((444186287/4835703278458516698824704), (-20324797/302231454903657293676544)), (77/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((119/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12185600/159836161), (-10648320/159836161)), 0, by norm_num⟩
  | 1 => ⟨((-17551064268800/25547598363217921), (129756168192000/25547598363217921)), 0, by norm_num⟩
  | 2 => ⟨((-628895857/4398046511104), (-476067237/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((222754423/17592186044416), (245533701/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-674295805/1125899906842624), (650252459/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((475952455/36028797018963968), (-557669835/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((304147819/576460752303423488), (233478795/144115188075855872)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-683242203/9223372036854775808), (-407499953/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1267788817/295147905179352825856), (-115605889/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-40625195/295147905179352825856), (816700059/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-77660079/151115727451828646838272), (-1689071745/151115727451828646838272)), (9/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((947575867/2417851639229258349412352), (988782671/2417851639229258349412352)), (83/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-276228541/9671406556917033397649408), (-98041347/38685626227668133590597632)), (3/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (8319/1280)))⁻¹=value ((12185600/159836161), (-10648320/159836161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12185600/159836161), (-10648320/159836161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((826826979/2251799813685248), (-725754051/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 1 => ⟨((84225455/2251799813685248), (937668467/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-219945453/4503599627370496), (-329334827/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 3 => ⟨((268392601/36028797018963968), (-874051937/144115188075855872)), (11/72057594037927936), by norm_num⟩
  | 4 => ⟨((270907281/1152921504606846976), (836024187/576460752303423488)), (29/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-851711251/4611686018427387904), (-316201381/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 6 => ⟨((335906471/18446744073709551616), (-286256527/18446744073709551616)), (23/36893488147419103232), by norm_num⟩
  | 7 => ⟨((159756251/295147905179352825856), (388530769/147573952589676412928)), (51/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1281350389/4722366482869645213696), (-387520961/4722366482869645213696)), (53/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((756355605/37778931862957161709568), (-759111919/37778931862957161709568)), (13/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((490980561/604462909807314587353088), (1565549171/604462909807314587353088)), (49/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-1190616385/4835703278458516698824704), (-103911151/2417851639229258349412352)), (11/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((64506955/4835703278458516698824704), (-688973889/38685626227668133590597632)), (39/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((135/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1536000/20649529), (-3549440/61948587)), 0, by norm_num⟩
  | 1 => ⟨((-4317569843200/3837627431296569), (1817313280000/426403047921841)), 0, by norm_num⟩
  | 2 => ⟨((-352962425/4398046511104), (-419447227/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1189129659/140737488355328), (674832295/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-254236185/562949953421312), (143488943/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((134846529/9007199254740992), (-551525915/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-136340951/1152921504606846976), (1150876955/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((-13949913/576460752303423488), (-373675999/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((608204923/295147905179352825856), (480227353/590295810358705651712)), (1/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-471988473/4722366482869645213696), (271797789/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((437151643/151115727451828646838272), (-1188865533/302231454903657293676544)), (73/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((12333927/2417851639229258349412352), (554109777/2417851639229258349412352)), (39/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-522656413/77371252455336267181195264), (-648165697/77371252455336267181195264)), (83/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (8319/1280)))⁻¹=value ((1536000/20649529), (-3549440/61948587)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((1536000/20649529), (-3549440/61948587))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4979929/562949953421312), (-202718019/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 1 => ⟨((17645267/1125899906842624), (68776969/4503599627370496)), (15/36028797018963968), by norm_num⟩
  | 2 => ⟨((-1643092423/288230376151711744), (2970923/2251799813685248)), (33/288230376151711744), by norm_num⟩
  | 3 => ⟨((219537945/576460752303423488), (-1257081131/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 4 => ⟨((542547471/4611686018427387904), (672737311/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-483689677/18446744073709551616), (126417747/36893488147419103232)), (7/9223372036854775808), by norm_num⟩
  | 6 => ⟨((396212327/295147905179352825856), (-907952119/295147905179352825856)), (35/295147905179352825856), by norm_num⟩
  | 7 => ⟨((67681571/295147905179352825856), (750137137/2361183241434822606848)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-803086933/18889465931478580854784), (158531617/37778931862957161709568)), (85/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((67961837/37778931862957161709568), (-151712779/37778931862957161709568)), (85/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((621281603/2417851639229258349412352), (839011623/2417851639229258349412352)), (83/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1558053311/38685626227668133590597632), (207580195/38685626227668133590597632)), (151/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((407288839/309485009821345068724781056), (-66586453/19342813113834066795298816)), (137/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((151/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15462400/215132161), (-10648320/215132161)), 0, by norm_num⟩
  | 1 => ⟨((-62849547468800/46281846696529921), (164648583168000/46281846696529921)), 0, by norm_num⟩
  | 2 => ⟨((-21573055/549755813888), (-44380163/274877906944)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((47551033/8796093022208), (169976389/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1413375021/4503599627370496), (-179354221/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((883698317/72057594037927936), (-114132845/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-327344999/1152921504606846976), (153105637/288230376151711744)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-217128961/73786976294838206464), (-1927030773/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((443949897/590295810358705651712), (511024699/590295810358705651712)), (27/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-915239105/18889465931478580854784), (-236085407/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((309869171/151115727451828646838272), (-56665743/75557863725914323419136)), (53/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-266591931/4835703278458516698824704), (751458131/9671406556917033397649408)), (53/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((9019033/154742504910672534362390528), (-1286417317/309485009821345068724781056)), (13/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (8319/1280)))⁻¹=value ((15462400/215132161), (-10648320/215132161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15462400/215132161), (-10648320/215132161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-458908413/288230376151711744), (-529346069/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 1 => ⟨((292615755/144115188075855872), (119472793/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((-986090147/2305843009213693952), (118849663/288230376151711744)), (19/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-197679547/9223372036854775808), (-565482439/4611686018427387904)), (35/9223372036854775808), by norm_num⟩
  | 4 => ⟨((44920009/2305843009213693952), (629978025/73786976294838206464)), (53/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-775169677/295147905179352825856), (507484315/295147905179352825856)), (37/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-18645811/4722366482869645213696), (-244581791/590295810358705651712)), (93/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((100592603/2361183241434822606848), (496341097/18889465931478580854784)), (55/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-760009671/151115727451828646838272), (380209927/151115727451828646838272)), (15/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((59236363/1208925819614629174706176), (-1432718139/2417851639229258349412352)), (123/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((469528183/9671406556917033397649408), (671770363/19342813113834066795298816)), (61/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-809812051/154742504910672534362390528), (22558841/9671406556917033397649408)), (115/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((135036581/2475880078570760549798248448), (-1302064097/2475880078570760549798248448)), (105/1237940039285380274899124224), by norm_num⟩
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
  | 0 => ⟨((167/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17100800/247695361), (-10648320/247695361)), 0, by norm_num⟩
  | 1 => ⟨((-89525320908800/61352991860920321), (182094790656000/61352991860920321)), 0, by norm_num⟩
  | 2 => ⟨((-118091465/8796093022208), (-147135761/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((470043453/140737488355328), (9523613/2199023255552)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-938468265/4503599627370496), (-349975489/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((1277389065/144115188075855872), (-32364349/18014398509481984)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-38529925/144115188075855872), (582318459/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((280445615/73786976294838206464), (-33352613/2305843009213693952)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((424323367/2361183241434822606848), (1371857961/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-706165881/37778931862957161709568), (-611768829/37778931862957161709568)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((150106257/151115727451828646838272), (190056437/1208925819614629174706176)), (29/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1457227349/38685626227668133590597632), (616041803/38685626227668133590597632)), (105/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((148246161/154742504910672534362390528), (-841415219/618970019642690137449562112)), (3/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (8319/1280)))⁻¹=value ((17100800/247695361), (-10648320/247695361)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((17100800/247695361), (-10648320/247695361))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-617564853/2305843009213693952), (-106726899/576460752303423488)), (51/4611686018427387904), by norm_num⟩
  | 1 => ⟨((1579266447/9223372036854775808), (-267643283/4611686018427387904)), (31/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-151829869/9223372036854775808), (969122497/18446744073709551616)), (5/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-539534685/73786976294838206464), (-716590187/73786976294838206464)), (19/36893488147419103232), by norm_num⟩
  | 4 => ⟨((1282803667/590295810358705651712), (-41296929/590295810358705651712)), (15/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-213592579/1180591620717411303424), (662882699/2361183241434822606848)), (43/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-337629559/18889465931478580854784), (-793659377/18889465931478580854784)), (7/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((1689775563/302231454903657293676544), (158491571/151115727451828646838272)), (67/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-137395705/302231454903657293676544), (572893135/1208925819614629174706176)), (19/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-160392287/9671406556917033397649408), (-1337488965/19342813113834066795298816)), (79/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((1068269747/154742504910672534362390528), (362270659/154742504910672534362390528)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-170111659/309485009821345068724781056), (561515741/1237940039285380274899124224)), (153/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-47627691/4951760157141521099596496896), (-327436349/4951760157141521099596496896)), (71/4951760157141521099596496896), by norm_num⟩
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
  | 0 => ⟨((183/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((6246400/94511787), (-3549440/94511787)), 0, by norm_num⟩
  | 1 => ⟨((-4403164774400/2977492627311123), (22171222016000/8932477881933369)), 0, by norm_num⟩
  | 2 => ⟨((39763223/17592186044416), (-1931465117/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((279636763/140737488355328), (1033169831/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1212228985/9007199254740992), (-23639825/281474976710656)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1736439943/288230376151711744), (17881691/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-939597379/4611686018427387904), (483885009/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((702825397/147573952589676412928), (-1076282067/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-12060505/590295810358705651712), (1560444499/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-417812539/75557863725914323419136), (-854041609/75557863725914323419136)), (17/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((119375453/302231454903657293676544), (326027903/1208925819614629174706176)), (29/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-350422645/19342813113834066795298816), (-115672061/77371252455336267181195264)), (49/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((12122947/19342813113834066795298816), (-359970563/1237940039285380274899124224)), (21/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (8319/1280)))⁻¹=value ((6246400/94511787), (-3549440/94511787)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((6246400/94511787), (-3549440/94511787))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1819147487/73786976294838206464), (-20087493/9223372036854775808)), (43/36893488147419103232), by norm_num⟩
  | 1 => ⟨((737313939/73786976294838206464), (-98294067/9223372036854775808)), (55/73786976294838206464), by norm_num⟩
  | 2 => ⟨((55707597/73786976294838206464), (683297993/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-1133227643/1180591620717411303424), (-4667719/9223372036854775808)), (75/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((107564799/590295810358705651712), (-103347249/1180591620717411303424)), (31/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-218803213/37778931862957161709568), (1196216753/37778931862957161709568)), (45/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-477892343/151115727451828646838272), (-30796621/9444732965739290427392)), (15/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((1389389079/2417851639229258349412352), (-111567691/1208925819614629174706176)), (147/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-570702639/19342813113834066795298816), (300938863/4835703278458516698824704)), (85/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-37587883/9671406556917033397649408), (-507377641/77371252455336267181195264)), (91/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((492548775/618970019642690137449562112), (97018043/2475880078570760549798248448)), (373/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-114695155/2475880078570760549798248448), (636485723/9903520314283042199192993792)), (183/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-442891615/158456325028528675187087900672), (-554815277/79228162514264337593543950336)), (343/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((199/16), (8319/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20377600/322652161), (-10648320/322652161)), 0, by norm_num⟩
  | 1 => ⟨((-150929931468800/104104416997969921), (216987205632000/104104416997969921)), 0, by norm_num⟩
  | 2 => ⟨((200341327/17592186044416), (-1578770571/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((157801873/140737488355328), (425285901/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-768054741/9007199254740992), (-692855723/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1141978367/288230376151711744), (147285401/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-654759911/4611686018427387904), (305344559/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((581021109/147573952589676412928), (-500015257/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-323096837/4722366482869645213696), (812070041/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-102314197/151115727451828646838272), (-247802177/37778931862957161709568)), (25/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((78348307/604462909807314587353088), (236898835/1208925819614629174706176)), (5/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1133738675/154742504910672534362390528), (-626581691/154742504910672534362390528)), (31/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((184563559/618970019642690137449562112), (17252483/2475880078570760549798248448)), (3/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (8319/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (8319/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (8319/1280)))⁻¹=value ((20377600/322652161), (-10648320/322652161)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20377600/322652161), (-10648320/322652161))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-961556721/590295810358705651712), (199548459/295147905179352825856)), (67/590295810358705651712), by norm_num⟩
  | 1 => ⟨((377391515/1180591620717411303424), (-620441709/590295810358705651712)), (91/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((490511481/2361183241434822606848), (722469137/2361183241434822606848)), (33/1180591620717411303424), by norm_num⟩
  | 3 => ⟨((-839954027/9444732965739290427392), (-123117599/18889465931478580854784)), (135/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((871593109/75557863725914323419136), (-967450293/75557863725914323419136)), (29/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((318073831/604462909807314587353088), (1683781935/604462909807314587353088)), (43/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-223604195/604462909807314587353088), (-218632705/1208925819614629174706176)), (117/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((231689151/4835703278458516698824704), (-487173091/19342813113834066795298816)), (147/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-35086249/38685626227668133590597632), (62768185/9671406556917033397649408)), (87/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-334449471/618970019642690137449562112), (-156540413/309485009821345068724781056)), (95/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((1524342533/19807040628566084398385987584), (-331384765/19807040628566084398385987584)), (395/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-468853251/158456325028528675187087900672), (1170371093/158456325028528675187087900672)), (197/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-552792463/1267650600228229401496703205376), (-801271129/1267650600228229401496703205376)), (47/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103157799/274877906944), (419449729/1099511627776)), (417/549755813888), by norm_num⟩
  | 1 => ⟨((177515087/2199023255552), (344484461/549755813888)), (901/549755813888), by norm_num⟩
  | 2 => ⟨((-390100957/2199023255552), (698048533/2199023255552)), (3985/2199023255552), by norm_num⟩
  | 3 => ⟨((-1081674209/8796093022208), (253659703/4398046511104)), (5951/4398046511104), by norm_num⟩
  | 4 => ⟨((-1284126873/35184372088832), (-212486089/35184372088832)), (26947/35184372088832), by norm_num⟩
  | 5 => ⟨((-407243241/70368744177664), (-743495853/140737488355328)), (49317/140737488355328), by norm_num⟩
  | 6 => ⟨((-433638617/1125899906842624), (-727010709/562949953421312)), (76041/562949953421312), by norm_num⟩
  | 7 => ⟨((361907643/9007199254740992), (-1716741499/9007199254740992)), (406649/9007199254740992), by norm_num⟩
  | 8 => ⟨((134204689/9007199254740992), (-697992533/36028797018963968)), (120345/9007199254740992), by norm_num⟩
  | 9 => ⟨((688487515/288230376151711744), (-390551949/288230376151711744)), (1025275/288230376151711744), by norm_num⟩
  | 10 => ⟨((1289805341/4611686018427387904), (-50301917/1152921504606846976)), (3977867/4611686018427387904), by norm_num⟩
  | 11 => ⟨((245387931/9223372036854775808), (90275923/18446744073709551616)), (3549041/18446744073709551616), by norm_num⟩
  | 12 => ⟨((1244210523/590295810358705651712), (678855831/590295810358705651712)), (23489643/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103157799/274877906944), (419449729/1099511627776)), (1669/2199023255552), by norm_num⟩
  | 1 => ⟨((177515087/2199023255552), (344484461/549755813888)), (3605/2199023255552), by norm_num⟩
  | 2 => ⟨((-390100957/2199023255552), (698048533/2199023255552)), (1993/1099511627776), by norm_num⟩
  | 3 => ⟨((-1081674209/8796093022208), (253659703/4398046511104)), (11903/8796093022208), by norm_num⟩
  | 4 => ⟨((-1284126873/35184372088832), (-212486089/35184372088832)), (26949/35184372088832), by norm_num⟩
  | 5 => ⟨((-407243241/70368744177664), (-743495853/140737488355328)), (49323/140737488355328), by norm_num⟩
  | 6 => ⟨((-433638617/1125899906842624), (-727010709/562949953421312)), (2377/17592186044416), by norm_num⟩
  | 7 => ⟨((361907643/9007199254740992), (-1716741499/9007199254740992)), (203505/4503599627370496), by norm_num⟩
  | 8 => ⟨((134204689/9007199254740992), (-697992533/36028797018963968)), (241411/18014398509481984), by norm_num⟩
  | 9 => ⟨((688487515/288230376151711744), (-390551949/288230376151711744)), (1036805/288230376151711744), by norm_num⟩
  | 10 => ⟨((1289805341/4611686018427387904), (-50301917/1152921504606846976)), (4162335/4611686018427387904), by norm_num⟩
  | 11 => ⟨((245387931/9223372036854775808), (90275923/18446744073709551616)), (4286911/18446744073709551616), by norm_num⟩
  | 12 => ⟨((1244210523/590295810358705651712), (678855831/590295810358705651712)), (11775369/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile034Gamma
