/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 36 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile011Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/303611449), (-4151040/303611449)), 0, by norm_num⟩
  | 1 => ⟨((-231487365939200/92179911963879601), (90964230144000/92179911963879601)), 0, by norm_num⟩
  | 2 => ⟨((11805178595/140737488355328), (-29712220667/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-24015938349/9007199254740992), (697533637/281474976710656)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((45702622835/576460752303423488), (-7757629195/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-39202272007/18446744073709551616), (81667227537/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((13703277169/295147905179352825856), (-51443465995/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-9142659121/18889465931478580854784), (124811566045/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-8372522953/302231454903657293676544), (-36533830151/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((6413182391/2417851639229258349412352), (82548708003/9671406556917033397649408)), (1/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-23841173221/154742504910672534362390528), (-350459005/1208925819614629174706176)), (23/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((37345438053/4951760157141521099596496896), (2911784457/309485009821345068724781056)), (17/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-833107525/2475880078570760549798248448), (-5704004073/19807040628566084398385987584)), (3/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (3243/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (3243/1280)))⁻¹=value ((21913600/303611449), (-4151040/303611449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/303611449), (-4151040/303611449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((89713768219/34359738368), (804058265/4294967296)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((10956800/303611449), (-2075520/303611449)), 0, by norm_num⟩
  | 2 => ⟨((-57871841484800/92179911963879601), (22741057536000/92179911963879601)), 0, by norm_num⟩
  | 3 => ⟨((62960952507/4503599627370496), (-39616294223/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-24015938349/72057594037927936), (697533637/2251799813685248)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((9140524567/1152921504606846976), (-1551525839/144115188075855872)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-26134848005/147573952589676412928), (27222409179/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((15660888193/4722366482869645213696), (-29396266283/2361183241434822606848)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-9142659121/302231454903657293676544), (124811566045/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-7442242625/4835703278458516698824704), (-16237257845/1208925819614629174706176)), (11/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((20522183651/154742504910672534362390528), (33019483201/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-8669517535/1237940039285380274899124224), (-65249094749/4951760157141521099596496896)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((12448479351/39614081257132168796771975168), (970594819/2475880078570760549798248448)), (23/158456325028528675187087900672), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (69/20480)), 0, by norm_num⟩
  | 45 => ⟨((105394677737/4080638361600), (-5961/1310720)), 0, by norm_num⟩
  | 44 => ⟨((-50262972536191/1915179604377600), (124622479337/25769803776000)), 0, by norm_num⟩
  | 43 => ⟨((7365567609/274877906944), (-5441718495/1099511627776)), (1/2199023255552), by norm_num⟩
  | 42 => ⟨((-15075404013/549755813888), (11116241911/2199023255552)), (1/2199023255552), by norm_num⟩
  | 41 => ⟨((61767694869/2199023255552), (-11372495785/2199023255552)), (1/2199023255552), by norm_num⟩
  | 40 => ⟨((-63308513563/2199023255552), (2911672611/549755813888)), (1/2199023255552), by norm_num⟩
  | 39 => ⟨((64927515805/2199023255552), (-1491957943/274877906944)), (1/2199023255552), by norm_num⟩
  | 38 => ⟨((-66631195943/2199023255552), (6119720783/1099511627776)), (1/2199023255552), by norm_num⟩
  | 37 => ⟨((34213315377/1099511627776), (-784941077/137438953472)), (1/2199023255552), by norm_num⟩
  | 36 => ⟨((-35160750811/1099511627776), (6447900289/1099511627776)), (1/2199023255552), by norm_num⟩
  | 35 => ⟨((72324312249/2199023255552), (-13251099595/2199023255552)), (1/2199023255552), by norm_num⟩
  | 34 => ⟨((-74444555609/2199023255552), (851658445/137438953472)), (1/2199023255552), by norm_num⟩
  | 33 => ⟨((76692871741/2199023255552), (-14023869719/2199023255552)), (1/2199023255552), by norm_num⟩
  | 32 => ⟨((-39540613357/1099511627776), (451408669/68719476736)), (1/2199023255552), by norm_num⟩
  | 31 => ⟨((81623125443/2199023255552), (-14892376871/2199023255552)), (1/2199023255552), by norm_num⟩
  | 30 => ⟨((-84333867143/2199023255552), (7684135305/1099511627776)), (1/2199023255552), by norm_num⟩
  | 29 => ⟨((87230853553/2199023255552), (-1984448977/274877906944)), (1/2199023255552), by norm_num⟩
  | 28 => ⟨((-45166981495/1099511627776), (4104390217/549755813888)), (1/2199023255552), by norm_num⟩
  | 27 => ⟨((46833003607/1099511627776), (-16997853833/2199023255552)), (1/2199023255552), by norm_num⟩
  | 26 => ⟨((-97253293315/2199023255552), (17620686049/2199023255552)), (1/2199023255552), by norm_num⟩
  | 25 => ⟨((3160197497/68719476736), (-4572728703/549755813888)), (1/2199023255552), by norm_num⟩
  | 24 => ⟨((-105320646625/2199023255552), (9507083233/1099511627776)), (1/2199023255552), by norm_num⟩
  | 23 => ⟨((54938994759/1099511627776), (-9898497469/1099511627776)), (1/2199023255552), by norm_num⟩
  | 22 => ⟨((-114847613765/2199023255552), (20647081201/2199023255552)), (1/2199023255552), by norm_num⟩
  | 21 => ⟨((7518007657/137438953472), (-2696685817/274877906944)), (1/1099511627776), by norm_num⟩
  | 20 => ⟨((-493241327/8589934592), (5646744337/549755813888)), (1/549755813888), by norm_num⟩
  | 19 => ⟨((16609695347/274877906944), (-2962555783/274877906944)), (1/549755813888), by norm_num⟩
  | 18 => ⟨((-8763451711/137438953472), (12464732313/1099511627776)), (1/549755813888), by norm_num⟩
  | 17 => ⟨((74205399453/1099511627776), (-13146508387/1099511627776)), (1/1099511627776), by norm_num⟩
  | 16 => ⟨((-1231438369/17179869184), (13907245049/1099511627776)), (1/1099511627776), by norm_num⟩
  | 15 => ⟨((84028671239/1099511627776), (-3690378903/274877906944)), (1/549755813888), by norm_num⟩
  | 14 => ⟨((-89985018485/1099511627776), (7863859211/549755813888)), (1/549755813888), by norm_num⟩
  | 13 => ⟨((24212626637/274877906944), (-8414710665/549755813888)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((-52425286459/549755813888), (18097316817/1099511627776)), (1/549755813888), by norm_num⟩
  | 11 => ⟨((28572986649/274877906944), (-19572138305/1099511627776)), (1/549755813888), by norm_num⟩
  | 10 => ⟨((-62801472405/549755813888), (10654569519/549755813888)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((34850099483/274877906944), (-11692603935/549755813888)), (1/549755813888), by norm_num⟩
  | 8 => ⟨((-78303146363/549755813888), (12955317113/549755813888)), (1/549755813888), by norm_num⟩
  | 7 => ⟨((89331685387/549755813888), (-14524754353/549755813888)), (1/549755813888), by norm_num⟩
  | 6 => ⟨((-103981959437/549755813888), (16528604997/549755813888)), (1/549755813888), by norm_num⟩
  | 5 => ⟨((31098351213/137438953472), (-4794306729/137438953472)), (1/274877906944), by norm_num⟩
  | 4 => ⟨((-4837829377/17179869184), (11421955429/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((102516608915/274877906944), (-3532752209/68719476736)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((-38005111223/68719476736), (9275916807/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((74220271395/68719476736), (-6779009567/68719476736)), (1/68719476736), by norm_num⟩
  | 0 => ⟨((-44413239035/274877906944), (51459728961/274877906944)), (1/137438953472), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (3243/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (3243/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (3243/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((89713768219/34359738368), (804058265/4294967296)), (1/34359738368), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (3243/1280))) (z:=((-21/128), (3243/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((89713768219/34359738368), (804058265/4294967296))) (r:=(1/34359738368)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((35586484683/1073741824), (9691132617/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((15354190553/8589934592), (208354779/2147483648)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((860588401843200/92179911963879601), (-168908437425120/92179911963879601)), 0, by norm_num⟩
  | 3 => ⟨((-31419852741/281474976710656), (25622922103/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((8620617137/4503599627370496), (-45196563321/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-42995763643/1152921504606846976), (20959912785/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((13820794089/18446744073709551616), (-39904820193/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-16891809885/1180591620717411303424), (76920782693/2361183241434822606848)), (95/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((16803720583/75557863725914323419136), (-37196989161/37778931862957161709568)), (115/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-550710849/604462909807314587353088), (71709064971/2417851639229258349412352)), (145/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-11084340013/77371252455336267181195264), (-34234483355/38685626227668133590597632)), (197/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((11797371003/1237940039285380274899124224), (64340612885/2475880078570760549798248448)), (63/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-17783596391/39614081257132168796771975168), (-59028913603/79228162514264337593543950336)), (161/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21225187787/1073741824), (13941414085/2147483648)), (5/4294967296), by norm_num⟩
  | 1 => ⟨((11059223257/8589934592), (208354779/2147483648)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((860588401843200/92179911963879601), (-168908437425120/92179911963879601)), 0, by norm_num⟩
  | 3 => ⟨((-31419852741/281474976710656), (25622922103/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((8620617137/4503599627370496), (-45196563321/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-42995763643/1152921504606846976), (20959912785/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((13820794089/18446744073709551616), (-39904820193/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-16891809885/1180591620717411303424), (76920782693/2361183241434822606848)), (95/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((16803720583/75557863725914323419136), (-37196989161/37778931862957161709568)), (115/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-550710849/604462909807314587353088), (71709064971/2417851639229258349412352)), (145/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-11084340013/77371252455336267181195264), (-34234483355/38685626227668133590597632)), (197/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((11797371003/1237940039285380274899124224), (64340612885/2475880078570760549798248448)), (63/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-17783596391/39614081257132168796771975168), (-59028913603/79228162514264337593543950336)), (161/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((126297950309/68719476736), 0), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((126297950309/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((88847562095/4294967296), (13941414085/2147483648)), (3/2147483648), by norm_num⟩
  | 1 => ⟨((11059223257/8589934592), (208354779/2147483648)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((860588401843200/92179911963879601), (-168908437425120/92179911963879601)), 0, by norm_num⟩
  | 3 => ⟨((-31419852741/281474976710656), (25622922103/562949953421312)), (5/562949953421312), by norm_num⟩
  | 4 => ⟨((8620617137/4503599627370496), (-45196563321/36028797018963968)), (17/36028797018963968), by norm_num⟩
  | 5 => ⟨((-42995763643/1152921504606846976), (20959912785/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 6 => ⟨((13820794089/18446744073709551616), (-39904820193/36893488147419103232)), (71/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-16891809885/1180591620717411303424), (76920782693/2361183241434822606848)), (95/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((16803720583/75557863725914323419136), (-37196989161/37778931862957161709568)), (115/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-550710849/604462909807314587353088), (71709064971/2417851639229258349412352)), (145/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-11084340013/77371252455336267181195264), (-34234483355/38685626227668133590597632)), (197/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((11797371003/1237940039285380274899124224), (64340612885/2475880078570760549798248448)), (63/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-17783596391/39614081257132168796771975168), (-59028913603/79228162514264337593543950336)), (161/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((462974731878400/92179911963879601), (-181928460288000/92179911963879601)), 0, by norm_num⟩
  | 1 => ⟨((-11805178595/35184372088832), (29712220667/140737488355328)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((9005976881/562949953421312), (-2092600911/140737488355328)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-45702622835/72057594037927936), (7757629195/9007199254740992)), (3/72057594037927936), by norm_num⟩
  | 4 => ⟨((6125355001/288230376151711744), (-25521008605/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-20554915753/36893488147419103232), (77165198993/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 6 => ⟨((7999826731/1180591620717411303424), (-109210120289/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((8372522953/18889465931478580854784), (73067660301/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-3607415095/75557863725914323419136), (-92867296503/604462909807314587353088)), (1/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((29801466527/9671406556917033397649408), (56073440799/9671406556917033397649408)), (13/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-51349977323/309485009821345068724781056), (-64059258053/309485009821345068724781056)), (19/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((2499322575/309485009821345068724781056), (34224024437/4951760157141521099596496896)), (15/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-29069683523/79228162514264337593543950336), (-16669715387/79228162514264337593543950336)), (11/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11805178595/35184372088832), (-29712220667/140737488355328)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((-9005976881/281474976710656), (2092600911/70368744177664)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((34276967127/18014398509481984), (-23272887585/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-24501420005/288230376151711744), (51042017211/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((25693644691/9223372036854775808), (-24114124685/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-187495939/4611686018427387904), (81907590217/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-457872349/147573952589676412928), (-15983550691/590295810358705651712)), (1/295147905179352825856), by norm_num⟩
  | 7 => ⟨((3607415095/9444732965739290427392), (46433648251/37778931862957161709568)), (15/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-16763324921/604462909807314587353088), (-63082620899/1208925819614629174706176)), (13/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((32093735827/19342813113834066795298816), (40037036283/19342813113834066795298816)), (11/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-54985096651/618970019642690137449562112), (-47058033601/618970019642690137449562112)), (9/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((87209050569/19807040628566084398385987584), (50009146161/19807040628566084398385987584)), (29/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-32564822715/158456325028528675187087900672), (-22559997625/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((24015938349/1125899906842624), (-697533637/35184372088832)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-11425655709/4503599627370496), (7757629195/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 2 => ⟨((24501420005/144115188075855872), (-51042017211/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-8564548231/1152921504606846976), (32152166247/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((4999891707/36893488147419103232), (-68256325181/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((457872349/36893488147419103232), (15983550691/147573952589676412928)), (1/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-65760171/36893488147419103232), (-54172589627/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((22351099895/151115727451828646838272), (84110161199/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-48140603741/4835703278458516698824704), (-7506944303/604462909807314587353088)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((45820913875/77371252455336267181195264), (39215028001/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-79941629689/2475880078570760549798248448), (-22920858657/1237940039285380274899124224)), (25/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((32564822715/19807040628566084398385987584), (22559997625/39614081257132168796771975168)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-25046361981/316912650057057350374175801344), (-1844586241/158456325028528675187087900672)), (9/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((45702622835/36028797018963968), (-7757629195/4503599627370496)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-24501420005/144115188075855872), (25521008605/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 2 => ⟨((6423411173/576460752303423488), (-48228249371/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-4999891707/18446744073709551616), (68256325181/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-2289361745/73786976294838206464), (-79917753455/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 5 => ⟨((197280513/36893488147419103232), (10157360555/590295810358705651712)), (13/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-2444651551/4722366482869645213696), (-36798195525/37778931862957161709568)), (15/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((48140603741/1208925819614629174706176), (60055554425/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-25774264055/9671406556917033397649408), (-44116906501/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((49963518555/309485009821345068724781056), (28651073321/309485009821345068724781056)), (17/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-89553262467/9903520314283042199192993792), (-15509998367/4951760157141521099596496896)), (29/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((75139085943/158456325028528675187087900672), (5533758723/79228162514264337593543950336)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-118924603099/5070602400912917605986812821504), (4874735871/5070602400912917605986812821504)), (47/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39202272007/576460752303423488), (-81667227537/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((-10277457877/1152921504606846976), (4822824937/144115188075855872)), (3/1152921504606846976), by norm_num⟩
  | 2 => ⟨((5999870049/18446744073709551616), (-40953795109/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((457872349/9223372036854775808), (15983550691/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-197280513/18446744073709551616), (-10157360555/295147905179352825856)), (13/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((46937309779/37778931862957161709568), (88315669259/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((-16849211309/151115727451828646838272), (-21019444049/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((5154852811/604462909807314587353088), (35293525201/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-11241791675/19342813113834066795298816), (-25785965989/77371252455336267181195264)), (15/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((89553262467/2475880078570760549798248448), (15509998367/1237940039285380274899124224)), (31/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-82652994537/39614081257132168796771975168), (-12174269191/39614081257132168796771975168)), (15/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((71354761859/633825300114114700748351602688), (-2924841523/633825300114114700748351602688)), (29/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-57914978431/10141204801825835211973625643008), (13449064023/10141204801825835211973625643008)), (27/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13703277169/4611686018427387904), (-51443465995/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-1999956683/9223372036854775808), (109210120289/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-457872349/9223372036854775808), (-15983550691/36893488147419103232)), (9/147573952589676412928), by norm_num⟩
  | 3 => ⟨((65760171/4611686018427387904), (54172589627/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-2444651551/1180591620717411303424), (-73596391049/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((16849211309/75557863725914323419136), (42038888097/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-48111959569/2417851639229258349412352), (-20587889701/1208925819614629174706176)), (1/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((29978111133/19342813113834066795298816), (17190643993/19342813113834066795298816)), (5/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-33582473425/309485009821345068724781056), (-23264997551/618970019642690137449562112)), (3/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((8609686931/1237940039285380274899124224), (5072612163/4951760157141521099596496896)), (13/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-130817063409/316912650057057350374175801344), (2681104729/158456325028528675187087900672)), (55/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((57914978431/2535301200456458802993406410752), (-13449064023/2535301200456458802993406410752)), (7/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-749291203/633825300114114700748351602688), (21150380325/40564819207303340847894502572032)), (27/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9142659121/147573952589676412928), (-124811566045/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 1 => ⟨((1046565369/36893488147419103232), (36533830151/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-28859320759/2361183241434822606848), (-92867296503/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 3 => ⟨((44702199789/18889465931478580854784), (5256885075/1180591620717411303424)), (9/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-12035150935/37778931862957161709568), (-60055554425/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((5154852811/151115727451828646838272), (35293525201/1208925819614629174706176)), (15/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-29978111133/9671406556917033397649408), (-17190643993/9671406556917033397649408)), (21/19342813113834066795298816), by norm_num⟩
  | 7 => ⟨((76759939257/309485009821345068724781056), (13294284315/154742504910672534362390528)), (7/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((-88556779861/4951760157141521099596496896), (-1630482481/618970019642690137449562112)), (35/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((46720379789/39614081257132168796771975168), (-3830149613/79228162514264337593543950336)), (41/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-91009251821/1267650600228229401496703205376), (21134243465/1267650600228229401496703205376)), (45/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((41103974565/10141204801825835211973625643008), (-36257794843/20282409603651670423947251286016)), (49/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-68878225097/324518553658426726783156020576256), (47385034913/324518553658426726783156020576256)), (25/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8372522953/1180591620717411303424), (-36533830151/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((14429660379/2361183241434822606848), (92867296503/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-16763324921/9444732965739290427392), (-15770655225/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((12035150935/37778931862957161709568), (30027777213/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-51548528109/1208925819614629174706176), (-22058453251/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((11241791675/2417851639229258349412352), (25785965989/9671406556917033397649408)), (17/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-33582473425/77371252455336267181195264), (-23264997551/154742504910672534362390528)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((88556779861/2475880078570760549798248448), (1630482481/309485009821345068724781056)), (9/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-105120854525/39614081257132168796771975168), (2154459157/19807040628566084398385987584)), (3/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((14220195597/79228162514264337593543950336), (-13208902165/316912650057057350374175801344)), (15/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-56517965027/5070602400912917605986812821504), (12463616977/2535301200456458802993406410752)), (35/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((51658668823/81129638414606681695789005144064), (-35538776185/81129638414606681695789005144064)), (5/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-43235283205/1298074214633706907132624082305024), (21809009063/649037107316853453566312041152512)), (43/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6413182391/4722366482869645213696), (-82548708003/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((14900733263/18889465931478580854784), (1752295025/1180591620717411303424)), (13/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((-32093735827/151115727451828646838272), (-10009259071/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((45820913875/1208925819614629174706176), (19607514001/604462909807314587353088)), (17/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((-49963518555/9671406556917033397649408), (-14325536661/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((89553262467/154742504910672534362390528), (15509998367/77371252455336267181195264)), (37/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((-8609686931/154742504910672534362390528), (-5072612163/618970019642690137449562112)), (31/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((46720379789/9903520314283042199192993792), (-3830149613/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-14220195597/39614081257132168796771975168), (13208902165/158456325028528675187087900672)), (31/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((62797738919/2535301200456458802993406410752), (-27696926615/2535301200456458802993406410752)), (41/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-31569186503/20282409603651670423947251286016), (43436282003/40564819207303340847894502572032)), (51/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((57647044273/649037107316853453566312041152512), (-58157357501/649037107316853453566312041152512)), (15/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-23559339703/5192296858534827628530496329220096), (69800567975/10384593717069655257060992658440192)), (17/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23841173221/151115727451828646838272), (-350459005/1180591620717411303424)), (23/302231454903657293676544), by norm_num⟩
  | 1 => ⟨((51349977323/604462909807314587353088), (32029629027/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-54985096651/2417851639229258349412352), (-47058033603/2417851639229258349412352)), (21/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((9992703711/2417851639229258349412352), (11460429329/4835703278458516698824704)), (31/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((-44776631233/77371252455336267181195264), (-484687449/2417851639229258349412352)), (37/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((82652994537/1237940039285380274899124224), (12174269191/1237940039285380274899124224)), (19/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((-130817063409/19807040628566084398385987584), (2681104729/9903520314283042199192993792)), (67/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((91009251821/158456325028528675187087900672), (-21134243465/158456325028528675187087900672)), (53/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-56517965027/1267650600228229401496703205376), (12463616977/633825300114114700748351602688)), (39/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((63138373007/20282409603651670423947251286016), (-43436282003/20282409603651670423947251286016)), (27/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-63411748701/324518553658426726783156020576256), (63973093251/324518553658426726783156020576256)), (35/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((7067801911/649037107316853453566312041152512), (-41880340785/2596148429267413814265248164610048)), (11/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-21529476319/41538374868278621028243970633760768), (25001568031/20769187434139310514121985316880384)), (13/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/910834347), (-345920/303611449)), 0, by norm_num⟩
  | 1 => ⟨((-57871841484800/276539735891638803), (7580352512000/92179911963879601)), 0, by norm_num⟩
  | 2 => ⟨((62960952507/9007199254740992), (-39616294223/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-8005312783/36028797018963968), (59522870357/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 4 => ⟨((30468415223/4611686018427387904), (-41374022373/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-26134848005/147573952589676412928), (27222409179/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 6 => ⟨((18271036225/4722366482869645213696), (-68591287993/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-6095106081/151115727451828646838272), (83207710697/151115727451828646838272)), (11/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-11163363937/4835703278458516698824704), (-97423547069/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((17101819709/77371252455336267181195264), (27516236001/38685626227668133590597632)), (11/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-31788230961/2475880078570760549798248448), (-59811670187/2475880078570760549798248448)), (1/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((12448479351/19807040628566084398385987584), (970594819/1237940039285380274899124224)), (23/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-71091842133/2535301200456458802993406410752), (-1901334691/79228162514264337593543950336)), (33/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((88873395057/4294967296), (27877934695/4294967296)), (7/4294967296), by norm_num⟩
  | 1 => ⟨((88459405039/68719476736), (1668251007/17179869184)), (3/68719476736), by norm_num⟩
  | 2 => ⟨((82181499039/8796093022208), (-16156454621/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-31482394247/281474976710656), (25739177709/562949953421312)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((34601485795/18014398509481984), (-45519797871/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-43199942143/1152921504606846976), (42345175713/1152921504606846976)), (13/576460752303423488), by norm_num⟩
  | 6 => ⟨((55568661297/73786976294838206464), (-80881379261/73786976294838206464)), (9/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-33878855803/2361183241434822606848), (78220903173/2361183241434822606848)), (97/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((16629293021/75557863725914323419136), (-75916221245/75557863725914323419136)), (29/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-834205765/1208925819614629174706176), (73428829721/2417851639229258349412352)), (73/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-12077722231/77371252455336267181195264), (-70338081403/77371252455336267181195264)), (199/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((25150801925/2475880078570760549798248448), (66281802523/2475880078570760549798248448)), (253/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-37788812849/79228162514264337593543950336), (-30465124147/39614081257132168796771975168)), (81/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-16789587335/18014398509481984), (5282172563/9007199254740992)), (3/72057594037927936), by norm_num⟩
  | 1 => ⟨((12808500453/144115188075855872), (-23809148143/288230376151711744)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-24374732179/4611686018427387904), (66198435797/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 3 => ⟨((34846464007/147573952589676412928), (-72593091145/147573952589676412928)), (7/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-18271036225/2361183241434822606848), (68591287993/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((8533148513/75557863725914323419136), (-116490794975/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((10419139675/1208925819614629174706176), (90928643931/1208925819614629174706176)), (3/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-5130545913/4835703278458516698824704), (-66038966401/19342813113834066795298816)), (3/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((23841173221/309485009821345068724781056), (89717505279/618970019642690137449562112)), (19/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-45644424287/9903520314283042199192993792), (-28470781357/4951760157141521099596496896)), (17/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((19550256587/79228162514264337593543950336), (33463490561/158456325028528675187087900672)), (7/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-62015324849/5070602400912917605986812821504), (-8890514873/1267650600228229401496703205376)), (21/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((723662727/1267650600228229401496703205376), (8021332489/40564819207303340847894502572032)), (17/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44436695527/2147483648), (13938968607/2147483648)), (1/536870912), by norm_num⟩
  | 1 => ⟨((88459411147/68719476736), (6672998351/68719476736)), (1/17179869184), by norm_num⟩
  | 2 => ⟨((20545363137/2199023255552), (-16156391489/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-62964655565/562949953421312), (6434725197/140737488355328)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((17300673199/9007199254740992), (-45518751251/36028797018963968)), (19/36028797018963968), by norm_num⟩
  | 5 => ⟨((-43199811937/1152921504606846976), (42343398205/1152921504606846976)), (27/1152921504606846976), by norm_num⟩
  | 6 => ⟨((55569297231/73786976294838206464), (-80875829417/73786976294838206464)), (73/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-4235170119/295147905179352825856), (4888302611/147573952589676412928)), (49/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((4158778405/18889465931478580854784), (-75905269401/75557863725914323419136)), (117/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-419888797/604462909807314587353088), (18353731993/604462909807314587353088)), (147/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-1507328773/9671406556917033397649408), (-4395108863/4835703278458516698824704)), (25/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((25120521005/2475880078570760549798248448), (16566109559/618970019642690137449562112)), (127/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-37743583929/79228162514264337593543950336), (-60914581629/79228162514264337593543950336)), (325/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((18571224517/18446744073709551616), (-50436903465/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-19912265147/147573952589676412928), (82963532735/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((10440592129/1180591620717411303424), (-39195021711/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-2031702027/9444732965739290427392), (55471807131/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-7442242625/302231454903657293676544), (-64949031379/302231454903657293676544)), (9/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((20522183651/4835703278458516698824704), (33019483201/2417851639229258349412352)), (11/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((-15894115481/38685626227668133590597632), (-59811670187/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((39123792247/1237940039285380274899124224), (48807053755/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-10473351743/4951760157141521099596496896), (-35853739887/19807040628566084398385987584)), (7/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((81210544445/633825300114114700748351602688), (11642340905/158456325028528675187087900672)), (7/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-72779794259/10141204801825835211973625643008), (-6302475527/2535301200456458802993406410752)), (25/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((61065415877/162259276829213363391578010288128), (8994553861/162259276829213363391578010288128)), (23/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-96649836169/5192296858534827628530496329220096), (3961690105/5192296858534827628530496329220096)), (39/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44436695529/2147483648), (3484742151/536870912)), (9/4294967296), by norm_num⟩
  | 1 => ⟨((44229705569/34359738368), (3336499185/34359738368)), (5/68719476736), by norm_num⟩
  | 2 => ⟨((41090726313/4398046511104), (-16156391781/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-31482327843/281474976710656), (25738902441/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((69202691909/36028797018963968), (-22759379497/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((-10799951761/288230376151711744), (21171706975/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((55569266915/73786976294838206464), (-40437943229/36893488147419103232)), (37/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-33881286329/2361183241434822606848), (19553233717/590295810358705651712)), (99/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((16634953809/75557863725914323419136), (-18976351543/18889465931478580854784)), (59/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-839622697/1208925819614629174706176), (18353776405/604462909807314587353088)), (37/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-6029592725/38685626227668133590597632), (-1098780221/1208925819614629174706176)), (201/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((25121452789/2475880078570760549798248448), (33132287741/1237940039285380274899124224)), (255/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-294883271/618970019642690137449562112), (-30457260589/39614081257132168796771975168)), (163/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8352473703/4722366482869645213696), (62712034737/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((4876084865/37778931862957161709568), (-66566168557/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((4465345575/151115727451828646838272), (77938837655/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-20522183651/2417851639229258349412352), (-33019483201/1208925819614629174706176)), (3/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((23841173221/19342813113834066795298816), (89717505279/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-20539990929/154742504910672534362390528), (-25623703221/154742504910672534362390528)), (15/309485009821345068724781056), by norm_num⟩
  | 6 => ⟨((1832836555/154742504910672534362390528), (25097617921/2475880078570760549798248448)), (21/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-4568093125/4951760157141521099596496896), (-41912427259/79228162514264337593543950336)), (25/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((81877268541/1267650600228229401496703205376), (886285621/39614081257132168796771975168)), (15/633825300114114700748351602688), by norm_num⟩
  | 9 => ⟨((-5247809177/1267650600228229401496703205376), (-12367511559/20282409603651670423947251286016)), (33/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((9967014355/40564819207303340847894502572032), (-102137323/10141204801825835211973625643008)), (35/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-17650279141/1298074214633706907132624082305024), (4098762369/1298074214633706907132624082305024)), (35/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((58458986047/83076749736557242056487941267521536), (-25783320777/83076749736557242056487941267521536)), (17/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44436695529/2147483648), (3484742151/536870912)), (5/2147483648), by norm_num⟩
  | 1 => ⟨((44229705569/34359738368), (3336499185/34359738368)), (3/34359738368), by norm_num⟩
  | 2 => ⟨((41090726313/4398046511104), (-16156391779/8796093022208)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-62964655691/562949953421312), (12869451213/281474976710656)), (9/562949953421312), by norm_num⟩
  | 4 => ⟨((69202691953/36028797018963968), (-22759379455/18014398509481984)), (21/36028797018963968), by norm_num⟩
  | 5 => ⟨((-43199807197/1152921504606846976), (42343413759/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((55569267789/73786976294838206464), (-40437942855/36893488147419103232)), (75/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-33881288507/2361183241434822606848), (78212933619/2361183241434822606848)), (25/590295810358705651712), by norm_num⟩
  | 8 => ⟨((16634958689/75557863725914323419136), (-37952702241/37778931862957161709568)), (119/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-1679255403/2417851639229258349412352), (36707552073/1208925819614629174706176)), (149/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-12059166439/77371252455336267181195264), (-70321934923/77371252455336267181195264)), (101/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((6280354781/618970019642690137449562112), (16566145825/618970019642690137449562112)), (1/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-37745002937/79228162514264337593543950336), (-60914545767/79228162514264337593543950336)), (327/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7216720121/1208925819614629174706176), (-31490439457/604462909807314587353088)), (11/1208925819614629174706176), by norm_num⟩
  | 1 => ⟨((24875374121/4835703278458516698824704), (80047232003/4835703278458516698824704)), (7/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((-28898391783/19342813113834066795298816), (-6796780703/2417851639229258349412352)), (13/19342813113834066795298816), by norm_num⟩
  | 3 => ⟨((20747465585/77371252455336267181195264), (25882528507/77371252455336267181195264)), (17/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-44432401333/1237940039285380274899124224), (-9506673455/309485009821345068724781056)), (17/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((38759578031/9903520314283042199192993792), (44452574365/19807040628566084398385987584)), (15/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((-3618313635/9903520314283042199192993792), (-10026665611/79228162514264337593543950336)), (3/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((76331769847/2535301200456458802993406410752), (11243192327/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((-90609221409/40564819207303340847894502572032), (3714084473/40564819207303340847894502572032)), (21/20282409603651670423947251286016), by norm_num⟩
  | 9 => ⟨((98057106339/649037107316853453566312041152512), (-22770902049/649037107316853453566312041152512)), (53/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((-48715821707/5192296858534827628530496329220096), (21486100647/5192296858534827628530496329220096)), (31/5192296858534827628530496329220096), by norm_num⟩
  | 11 => ⟨((44527337437/83076749736557242056487941267521536), (-30632749843/83076749736557242056487941267521536)), (35/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((-1164586753/41538374868278621028243970633760768), (9399168889/332306998946228968225951765070086144)), (19/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44436695529/2147483648), (3484742151/536870912)), (11/4294967296), by norm_num⟩
  | 1 => ⟨((44229705569/34359738368), (3336499185/34359738368)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((41090726313/4398046511104), (-16156391779/8796093022208)), (5/8796093022208), by norm_num⟩
  | 3 => ⟨((-62964655691/562949953421312), (12869451213/281474976710656)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((4325168247/2251799813685248), (-45518758911/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 5 => ⟨((-5399975899/144115188075855872), (21171706881/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((27784633881/36893488147419103232), (-80875885719/73786976294838206464)), (19/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-8470322109/590295810358705651712), (78212933629/2361183241434822606848)), (101/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((2079369815/9444732965739290427392), (-75905404475/75557863725914323419136)), (15/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-839627519/1208925819614629174706176), (73415104061/2417851639229258349412352)), (75/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-12059167165/77371252455336267181195264), (-70321934603/77371252455336267181195264)), (203/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((25121420451/2475880078570760549798248448), (66264582387/2475880078570760549798248448)), (257/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-18872502579/39614081257132168796771975168), (-30457271763/39614081257132168796771975168)), (41/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23406638795/77371252455336267181195264), (44041147225/77371252455336267181195264)), (23/154742504910672534362390528), by norm_num⟩
  | 1 => ⟨((-25207030715/154742504910672534362390528), (-62891700037/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 2 => ⟨((6747865785/154742504910672534362390528), (46200343613/1237940039285380274899124224)), (11/618970019642690137449562112), by norm_num⟩
  | 3 => ⟨((-19621149025/2475880078570760549798248448), (-11251549043/2475880078570760549798248448)), (31/9903520314283042199192993792), by norm_num⟩
  | 4 => ⟨((87921045161/79228162514264337593543950336), (15227309753/39614081257132168796771975168)), (37/79228162514264337593543950336), by norm_num⟩
  | 5 => ⟨((-40573271511/316912650057057350374175801344), (-186755911/9903520314283042199192993792)), (19/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((16054095383/1267650600228229401496703205376), (-2632238329/5070602400912917605986812821504)), (67/10141204801825835211973625643008), by norm_num⟩
  | 7 => ⟨((-89350497337/81129638414606681695789005144064), (5187261533/20282409603651670423947251286016)), (53/81129638414606681695789005144064), by norm_num⟩
  | 8 => ⟨((55487856263/649037107316853453566312041152512), (-6118226187/162259276829213363391578010288128)), (39/649037107316853453566312041152512), by norm_num⟩
  | 9 => ⟨((-30993799621/5192296858534827628530496329220096), (1332643839/324518553658426726783156020576256)), (27/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((62255992331/166153499473114484112975882535043072), (-62807105693/166153499473114484112975882535043072)), (69/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((-6938982611/332306998946228968225951765070086144), (20558510277/664613997892457936451903530140172288)), (11/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((21137075385/21267647932558653966460912964485513216), (-6136470999/2658455991569831745807614120560689152)), (13/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44436695529/2147483648), (3484742151/536870912)), (3/1073741824), by norm_num⟩
  | 1 => ⟨((44229705569/34359738368), (3336499185/34359738368)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((41090726313/4398046511104), (-16156391779/8796093022208)), (3/4398046511104), by norm_num⟩
  | 3 => ⟨((-62964655691/562949953421312), (12869451213/281474976710656)), (11/562949953421312), by norm_num⟩
  | 4 => ⟨((4325168247/2251799813685248), (-45518758911/36028797018963968)), (23/36028797018963968), by norm_num⟩
  | 5 => ⟨((-5399975899/144115188075855872), (21171706881/576460752303423488)), (31/1152921504606846976), by norm_num⟩
  | 6 => ⟨((55569267763/73786976294838206464), (-80875885719/73786976294838206464)), (77/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-33881288439/2361183241434822606848), (39106466815/1180591620717411303424)), (51/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((8317479263/37778931862957161709568), (-37952702239/37778931862957161709568)), (121/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-419813763/604462909807314587353088), (73415104071/2417851639229258349412352)), (151/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-376848973/2417851639229258349412352), (-8790241829/9671406556917033397649408)), (51/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((25121420399/2475880078570760549798248448), (1035384101/38685626227668133590597632)), (129/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-37745005079/79228162514264337593543950336), (-60914543709/79228162514264337593543950336)), (329/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((994912464503011/1048576), (104808948646309/524288)), (862329/262144), by norm_num⟩
  | 1 => ⟨((76925657717/64), (22365864727/64)), (301/64), by norm_num⟩
  | 2 => ⟨((49016353963/64), (36276398589/128)), (217/64), by norm_num⟩
  | 3 => ⟨((5236053217/16), (9415856211/64)), (421/256), by norm_num⟩
  | 4 => ⟨((54000780781/512), (14316086295/256)), (155/256), by norm_num⟩
  | 5 => ⟨((55995230983/2048), (8579216431/512)), (23/128), by norm_num⟩
  | 6 => ⟨((12158811215/2048), (33964115229/8192)), (367/8192), by norm_num⟩
  | 7 => ⟨((72765444601/65536), (57310281041/65536)), (317/32768), by norm_num⟩
  | 8 => ⟨((47842644945/262144), (42179543557/262144)), (121/65536), by norm_num⟩
  | 9 => ⟨((14037638159/524288), (55114824347/2097152)), (663/2097152), by norm_num⟩
  | 10 => ⟨((59528579351/16777216), (8100959611/2097152)), (103/2097152), by norm_num⟩
  | 11 => ⟨((1798647023/4194304), (17332692241/33554432)), (941/134217728), by norm_num⟩
  | 12 => ⟨((51150498097/1073741824), (68085647461/1073741824)), (497/536870912), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1610929992048265/10141204801825835211973625643008), (135245450077/5070602400912917605986812821504)), (455/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((226815687742739/79228162514264337593543950336), (332139817203/633825300114114700748351602688)), (4471/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1930012935636549/39614081257132168796771975168), (187335941777/19807040628566084398385987584)), (1261/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1932346635814205/2475880078570760549798248448), (398950571619/2475880078570760549798248448)), (5371/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((453514915483445/38685626227668133590597632), (399914423949/154742504910672534362390528)), (673/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1589792892939419/9671406556917033397649408), (375946971075/9671406556917033397649408)), (5061/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323512035724731/151115727451828646838272), (164992255991/302231454903657293676544)), (4443/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1945182534551373/75557863725914323419136), (33635357887/4722366482869645213696)), (3623/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((83791544647577/295147905179352825856), (405330549165/4722366482869645213696)), (2729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((420219931680417/147573952589676412928), (140029299513/147573952589676412928)), (3771/295147905179352825856), by norm_num⟩
  | 8 => ⟨((118622909937455/4611686018427387904), (352177251371/36893488147419103232)), (2371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1906740051617013/9223372036854775808), (99778517485/1152921504606846976)), (10749/9223372036854775808), by norm_num⟩
  | 6 => ⟨((839170163463851/576460752303423488), (402790159161/576460752303423488)), (10849/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1268789596093767/144115188075855872), (356622485445/72057594037927936)), (9607/144115188075855872), by norm_num⟩
  | 4 => ⟨((1603755405881379/36028797018963968), (1086822040531/36028797018963968)), (14641/36028797018963968), by norm_num⟩
  | 3 => ⟨((815415174247569/4503599627370496), (694361798011/4503599627370496)), (18711/9007199254740992), by norm_num⟩
  | 2 => ⟨((1257718598978425/2251799813685248), (1435087927913/2251799813685248)), (19343/2251799813685248), by norm_num⟩
  | 1 => ⟨((1329220061289595/1125899906842624), (284047087663/140737488355328)), (7661/281474976710656), by norm_num⟩
  | 0 => ⟨((777827658538629/562949953421312), (2523728504959/562949953421312)), (8517/140737488355328), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((777827658538629/562949953421312), (2523728504959/562949953421312)), (32489777148199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((268678189555391/140737488355328), (3487034365789/281474976710656)), (188899/1125899906842624), by norm_num⟩
  | 2 => ⟨((1025809548460125/281474976710656), (26628017631015/562949953421312)), (362963/562949953421312), by norm_num⟩
  | 3 => ⟨((934459591378479/70368744177664), (48521675108865/140737488355328)), (334989/70368744177664), by norm_num⟩
  | 4 => ⟨((775047705730351/4398046511104), (80542763028343/8796093022208)), (570497/4398046511104), by norm_num⟩
  | 5 => ⟨((532087407013667/17179869184), (55444079281753/17179869184)), (413125/8589934592), by norm_num⟩
  | 6 => ⟨((994912464503011/1048576), (104808948646309/524288)), (862329/262144), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((44436695529/2147483648), (3484742151/536870912)), (3/1073741824), by norm_num⟩, 1, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/13614649), (-4151040/13614649)), 0, by norm_num⟩
  | 1 => ⟨((6078012620800/185358667393201), (9351462912000/185358667393201)), 0, by norm_num⟩
  | 2 => ⟨((-91514405799/8796093022208), (3627664327/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((6465333551/8796093022208), (-58205652373/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((3366843639/17592186044416), (17516215541/70368744177664)), (5/281474976710656), by norm_num⟩
  | 5 => ⟨((-60552314061/1125899906842624), (9661992817/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 6 => ⟨((7073625949/2251799813685248), (-80243453997/9007199254740992)), (3/2251799813685248), by norm_num⟩
  | 7 => ⟨((39567957885/36028797018963968), (21904646253/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 8 => ⟨((-19904502943/72057594037927936), (4815004907/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 9 => ⟨((14604026155/1152921504606846976), (-54924151743/1152921504606846976)), (23/1152921504606846976), by norm_num⟩
  | 10 => ⟨((28659189191/4611686018427387904), (54163724905/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-25998660079/18446744073709551616), (4256842829/9223372036854775808)), (43/36893488147419103232), by norm_num⟩
  | 12 => ⟨((13649492815/295147905179352825856), (-74684912691/295147905179352825856)), (41/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (3243/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (3243/1280)))⁻¹=value ((2252800/13614649), (-4151040/13614649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/13614649), (-4151040/13614649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/19758649), (-4151040/19758649)), 0, by norm_num⟩
  | 1 => ⟨((1044847820800/390404210305201), (16152526848000/390404210305201)), 0, by norm_num⟩
  | 2 => ⟨((-40546402543/8796093022208), (-16681267943/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((14994111315/17592186044416), (-15583834369/140737488355328)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-40698285371/562949953421312), (56539195869/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-15452735779/4503599627370496), (-78739296289/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((78341318565/36028797018963968), (12260222113/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 7 => ⟨((-6432783289/18014398509481984), (13601136583/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 8 => ⟨((14554751053/576460752303423488), (-53960504815/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 9 => ⟨((700461095/288230376151711744), (33484660207/4611686018427387904)), (35/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-18483683911/18446744073709551616), (-33918609483/73786976294838206464)), (29/36893488147419103232), by norm_num⟩
  | 11 => ⟨((86745272523/590295810358705651712), (-35411723105/590295810358705651712)), (3/18446744073709551616), by norm_num⟩
  | 12 => ⟨((-19287525717/2361183241434822606848), (25197937015/1180591620717411303424)), (79/2361183241434822606848), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (3243/1280)))⁻¹=value ((3891200/19758649), (-4151040/19758649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/19758649), (-4151040/19758649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-8465037721600/269007070849201), (-25503989760000/269007070849201)), 0, by norm_num⟩
  | 1 => ⟨((66221884835/2199023255552), (19960057435/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-6371000407/1099511627776), (10154466135/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-2063444213/17592186044416), (-54309693781/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((37109320455/140737488355328), (20897632115/140737488355328)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((-14172282529/281474976710656), (14673408445/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 6 => ⟨((8709174155/9007199254740992), (-46251838055/4503599627370496)), (15/9007199254740992), by norm_num⟩
  | 7 => ⟨((52433524463/36028797018963968), (5051126045/4503599627370496)), (15/36028797018963968), by norm_num⟩
  | 8 => ⟨((-86895387299/288230376151711744), (4093768229/36028797018963968)), (15/144115188075855872), by norm_num⟩
  | 9 => ⟨((11802181775/1152921504606846976), (-63295316795/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 10 => ⟨((33280110169/4611686018427387904), (29201775545/4611686018427387904)), (55/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-57418899691/36893488147419103232), (9620302005/18446744073709551616)), (13/9223372036854775808), by norm_num⟩
  | 12 => ⟨((8030216765/147573952589676412928), (-80984396945/295147905179352825856)), (49/147573952589676412928), by norm_num⟩
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
  | 0 => ⟨((27/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/3242161), (-1383680/9726483)), 0, by norm_num⟩
  | 1 => ⟨((-741407948800/94604471549289), (283377664000/10511607949921)), 0, by norm_num⟩
  | 2 => ⟨((-10335295933/8796093022208), (-27371702807/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((46819550461/140737488355328), (14866948449/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-104818972177/2251799813685248), (8206671883/2251799813685248)), (9/2251799813685248), by norm_num⟩
  | 5 => ⟨((37392122469/9007199254740992), (-32933271571/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-9603492209/72057594037927936), (23120656907/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((-38066811413/1152921504606846976), (-81032496307/1152921504606846976)), (7/288230376151711744), by norm_num⟩
  | 8 => ⟨((37482775899/4611686018427387904), (19881145441/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-79451037635/73786976294838206464), (12517774475/73786976294838206464)), (13/18446744073709551616), by norm_num⟩
  | 10 => ⟨((26550924601/295147905179352825856), (-54699144045/590295810358705651712)), (35/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-4563050553/2361183241434822606848), (17919882141/1180591620717411303424)), (47/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((-2116908561/2361183241434822606848), (-59527091397/37778931862957161709568)), (63/18889465931478580854784), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (3243/1280)))⁻¹=value ((614400/3242161), (-1383680/9726483)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/3242161), (-1383680/9726483))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-42772124347/2199023255552), (-3708057159/274877906944)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((86206024651/8796093022208), (-23479081773/8796093022208)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-10378448323/8796093022208), (46608697619/17592186044416)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-44820446881/140737488355328), (-85960521929/140737488355328)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((81465412073/562949953421312), (14551500281/562949953421312)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-48151930863/2251799813685248), (350898297/17592186044416)), (5/1125899906842624), by norm_num⟩
  | 6 => ⟨((-12076592013/18014398509481984), (-24745933499/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 7 => ⟨((4006843949/4503599627370496), (34476458705/72057594037927936)), (21/72057594037927936), by norm_num⟩
  | 8 => ⟨((-22957522333/144115188075855872), (23741421813/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 9 => ⟨((1939728733/576460752303423488), (-71470891621/2305843009213693952)), (5/288230376151711744), by norm_num⟩
  | 10 => ⟨((38315889343/9223372036854775808), (30894351575/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 11 => ⟨((-62911776889/73786976294838206464), (22013833021/73786976294838206464)), (9/9223372036854775808), by norm_num⟩
  | 12 => ⟨((9103380337/295147905179352825856), (-10968617075/73786976294838206464)), (133/590295810358705651712), by norm_num⟩
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
  | 0 => ⟨((35/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/41877049), (-4151040/41877049)), 0, by norm_num⟩
  | 1 => ⟨((-17074545459200/1753687232948401), (29754654720000/1753687232948401)), 0, by norm_num⟩
  | 2 => ⟨((-537745793/70368744177664), (-136138896171/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((27173479459/281474976710656), (46498567913/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-9260368755/562949953421312), (-42123987223/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((67424516165/36028797018963968), (-16645599/1125899906842624)), (7/72057594037927936), by norm_num⟩
  | 6 => ⟨((-45952411055/288230376151711744), (13549186071/144115188075855872)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((41435671505/4611686018427387904), (-73547002397/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1582853745/73786976294838206464), (66784652665/36893488147419103232)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-27021838375/295147905179352825856), (-45411714249/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 10 => ⟨((73013431255/4722366482869645213696), (20377981817/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-132299658559/75557863725914323419136), (65327707/2361183241434822606848)), (79/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((44876431429/302231454903657293676544), (-26943913015/302231454903657293676544)), (11/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (3243/1280)))⁻¹=value ((7168000/41877049), (-4151040/41877049)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/41877049), (-4151040/41877049))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41046725717/8796093022208), (-6702674905/17592186044416)), (3/17592186044416), by norm_num⟩
  | 1 => ⟨((64429507435/35184372088832), (-28623068519/17592186044416)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((-2170313987/140737488355328), (112653839767/140737488355328)), (7/140737488355328), by norm_num⟩
  | 3 => ⟨((-43180474363/281474976710656), (-20019783275/140737488355328)), (5/281474976710656), by norm_num⟩
  | 4 => ⟨((6686666341/140737488355328), (-3011226827/562949953421312)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((-49396976575/9007199254740992), (37588755863/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 6 => ⟨((-21751187907/36028797018963968), (-33510150595/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 7 => ⟨((99029570487/288230376151711744), (35448305995/288230376151711744)), (37/288230376151711744), by norm_num⟩
  | 8 => ⟨((-15738050149/288230376151711744), (10489392985/288230376151711744)), (19/576460752303423488), by norm_num⟩
  | 9 => ⟨((3439706243/9223372036854775808), (-52848991141/4611686018427387904)), (73/9223372036854775808), by norm_num⟩
  | 10 => ⟨((58260299381/36893488147419103232), (42826386395/36893488147419103232)), (35/18446744073709551616), by norm_num⟩
  | 11 => ⟨((-22803784103/73786976294838206464), (33794716805/295147905179352825856)), (33/73786976294838206464), by norm_num⟩
  | 12 => ⟨((13363099739/1180591620717411303424), (-63301479495/1180591620717411303424)), (123/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((43/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/57851449), (-4151040/57851449)), 0, by norm_num⟩
  | 1 => ⟨((-30160773939200/3346790151399601), (36555718656000/3346790151399601)), 0, by norm_num⟩
  | 2 => ⟨((5172874711/17592186044416), (-81251980533/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((5360716405/281474976710656), (27706434137/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-22432506997/4503599627370496), (-61327112027/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((22459957895/36028797018963968), (12232523741/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-34373426817/576460752303423488), (-1002036333/288230376151711744)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((86020353743/18446744073709551616), (-34581482411/18446744073709551616)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-42452214219/147573952589676412928), (45745598933/147573952589676412928)), (9/73786976294838206464), by norm_num⟩
  | 9 => ⟨((25438860597/2361183241434822606848), (-40038746947/1180591620717411303424)), (33/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((3746841269/9444732965739290427392), (56060284341/18889465931478580854784)), (15/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-20652955373/151115727451828646838272), (-7996043661/37778931862957161709568)), (55/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((21755429117/1208925819614629174706176), (27094801613/2417851639229258349412352)), (51/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (3243/1280)))⁻¹=value ((8806400/57851449), (-4151040/57851449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/57851449), (-4151040/57851449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-25955126633/35184372088832), (19480705789/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((14652366821/70368744177664), (-15009839253/35184372088832)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((30705970737/562949953421312), (45850941167/281474976710656)), (9/562949953421312), by norm_num⟩
  | 3 => ⟨((-49038507737/1125899906842624), (-11871301565/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 4 => ⟨((49180363771/4503599627370496), (-37658668141/9007199254740992)), (17/9007199254740992), by norm_num⟩
  | 5 => ⟨((-8260559089/9007199254740992), (42766789461/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 6 => ⟨((-34694978225/144115188075855872), (-65347978161/144115188075855872)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((110354454435/1152921504606846976), (5748454911/288230376151711744)), (51/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-31593039829/2305843009213693952), (52452186973/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-4822998133/36893488147419103232), (-57709875265/18446744073709551616)), (51/18446744073709551616), by norm_num⟩
  | 10 => ⟨((65798190773/147573952589676412928), (21901317371/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 11 => ⟨((-49238712489/590295810358705651712), (19485592251/590295810358705651712)), (93/590295810358705651712), by norm_num⟩
  | 12 => ⟨((14357058051/4722366482869645213696), (-4273526041/295147905179352825856)), (87/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((51/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/25700883), (-1383680/25700883)), 0, by norm_num⟩
  | 1 => ⟨((-1701161369600/220178462326563), (4817420288000/660535386979689)), 0, by norm_num⟩
  | 2 => ⟨((23010567003/70368744177664), (-24698532017/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-7323552589/2251799813685248), (31721879671/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-11678512459/9007199254740992), (-70332998021/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((55605305283/288230376151711744), (16540499225/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-88757250167/4611686018427387904), (-23876169483/2305843009213693952)), (11/4611686018427387904), by norm_num⟩
  | 7 => ⟨((116755894671/73786976294838206464), (13522620661/73786976294838206464)), (17/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-66178006825/590295810358705651712), (4454027523/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((64045598231/9444732965739290427392), (-23905443775/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-48815812567/151115727451828646838272), (79398672631/151115727451828646838272)), (17/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((18705902887/2417851639229258349412352), (-26767942733/604462909807314587353088)), (53/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((12921983499/19342813113834066795298816), (15511687337/4835703278458516698824704)), (21/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (3243/1280)))⁻¹=value ((3481600/25700883), (-1383680/25700883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/25700883), (-1383680/25700883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-23933134871/281474976710656), (5433712317/70368744177664)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((5021614965/562949953421312), (-10769216063/140737488355328)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((39664417553/2251799813685248), (13822264213/562949953421312)), (9/2251799813685248), by norm_num⟩
  | 3 => ⟨((-80070130889/9007199254740992), (-15318236167/9007199254740992)), (7/4503599627370496), by norm_num⟩
  | 4 => ⟨((34265672151/18014398509481984), (-23029708693/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-13092525179/144115188075855872), (36660728661/72057594037927936)), (23/144115188075855872), by norm_num⟩
  | 6 => ⟨((-37220507297/576460752303423488), (-49213048255/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((47757751027/2305843009213693952), (7345881187/4611686018427387904)), (55/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-49611863263/18446744073709551616), (3145228355/1152921504606846976)), (57/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-11423564039/147573952589676412928), (-99455834727/147573952589676412928)), (113/147573952589676412928), by norm_num⟩
  | 10 => ⟨((58890657665/590295810358705651712), (35281130389/590295810358705651712)), (109/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-84477543041/4722366482869645213696), (17944469923/2361183241434822606848)), (13/295147905179352825856), by norm_num⟩
  | 12 => ⟨((3019489871/4722366482869645213696), (-29481112861/9444732965739290427392)), (195/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((59/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/99630649), (-4151040/99630649)), 0, by norm_num⟩
  | 1 => ⟨((-64386294579200/9926266220161201), (50157846528000/9926266220161201)), 0, by norm_num⟩
  | 2 => ⟨((5067831143/17592186044416), (-62141676985/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-18623373721/2251799813685248), (18451439971/562949953421312)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-6531380693/36028797018963968), (-9727088369/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((16137212653/288230376151711744), (73323847237/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-55753811957/9223372036854775808), (-3774010749/576460752303423488)), (7/9223372036854775808), by norm_num⟩
  | 7 => ⟨((74221463631/147573952589676412928), (20001785729/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-85346364821/2361183241434822606848), (-7036986791/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((87497478629/37778931862957161709568), (-7396018735/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-19990780037/151115727451828646838272), (43515981179/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((63078886085/9671406556917033397649408), (-68873779115/9671406556917033397649408)), (9/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-4780627137/19342813113834066795298816), (43924580963/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (3243/1280)))⁻¹=value ((12083200/99630649), (-4151040/99630649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/99630649), (-4151040/99630649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-15976338893/2251799813685248), (58130534647/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((-4379669645/2251799813685248), (-11914833019/1125899906842624)), (15/9007199254740992), by norm_num⟩
  | 2 => ⟨((31504335069/9007199254740992), (25626626855/9007199254740992)), (15/18014398509481984), by norm_num⟩
  | 3 => ⟨((-25586808813/18014398509481984), (4644599161/72057594037927936)), (23/72057594037927936), by norm_num⟩
  | 4 => ⟨((9447233497/36028797018963968), (-38593095007/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-164140741/1152921504606846976), (100523376889/1152921504606846976)), (39/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-30426439111/2305843009213693952), (-29869469009/2305843009213693952)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((67299132851/18446744073709551616), (-1467610955/9223372036854775808)), (49/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-31760383135/73786976294838206464), (39001080237/73786976294838206464)), (51/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-6604520659/295147905179352825856), (-70557466485/590295810358705651712)), (103/590295810358705651712), by norm_num⟩
  | 10 => ⟨((87064626473/4722366482869645213696), (46629493637/4722366482869645213696)), (199/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-7500567005/2361183241434822606848), (27433747741/18889465931478580854784)), (191/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((16602919481/151115727451828646838272), (-84542081325/151115727451828646838272)), (359/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((67/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/125435449), (-4151040/125435449)), 0, by norm_num⟩
  | 1 => ⟨((-85525586739200/15734051865831601), (56958910464000/15734051865831601)), 0, by norm_num⟩
  | 2 => ⟨((33412511749/140737488355328), (-20262443683/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-37023370357/4503599627370496), (88620940609/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((4469256833/36028797018963968), (-43678452969/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((15304847465/1152921504606846976), (78815400791/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-34259717205/18446744073709551616), (-32461074683/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((47169605109/295147905179352825856), (47745501879/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-53920064755/4722366482869645213696), (-14647909013/2361183241434822606848)), (5/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((109886342959/151115727451828646838272), (22725461097/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-51090844075/1208925819614629174706176), (9203963903/2417851639229258349412352)), (29/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((10873243893/4835703278458516698824704), (-35106719209/38685626227668133590597632)), (17/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-66830041419/618970019642690137449562112), (13438027729/154742504910672534362390528)), (5/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (3243/1280)))⁻¹=value ((13721600/125435449), (-4151040/125435449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/125435449), (-4151040/125435449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-12573140403/36028797018963968), (3708205277/2251799813685248)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((-20577157709/36028797018963968), (-21421262129/18014398509481984)), (19/72057594037927936), by norm_num⟩
  | 2 => ⟨((38023771549/72057594037927936), (36183581887/144115188075855872)), (21/144115188075855872), by norm_num⟩
  | 3 => ⟨((-107370685753/576460752303423488), (28277412283/576460752303423488)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((33662750123/1152921504606846976), (-25212531681/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18414514785/9223372036854775808), (57267604119/4611686018427387904)), (57/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-10084922519/4611686018427387904), (-7501091751/4611686018427387904)), (17/9223372036854775808), by norm_num⟩
  | 7 => ⟨((79741717495/147573952589676412928), (-6298353691/73786976294838206464)), (73/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-34081712117/590295810358705651712), (50573285907/590295810358705651712)), (77/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-22020830995/4722366482869645213696), (-42445434969/2361183241434822606848)), (39/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((27352715699/9444732965739290427392), (12996917931/9444732965739290427392)), (153/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-72627214493/151115727451828646838272), (8940372991/37778931862957161709568)), (147/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((19193181033/1208925819614629174706176), (-51821512953/604462909807314587353088)), (555/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((75/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/51505683), (-1383680/51505683)), 0, by norm_num⟩
  | 1 => ⟨((-4049971609600/884278460432163), (7084441600000/2652835381296489)), 0, by norm_num⟩
  | 2 => ⟨((53977997583/281474976710656), (-54677349561/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-15587514301/2251799813685248), (27541528219/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((25907455039/144115188075855872), (-101009906045/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((276443941/576460752303423488), (85896283925/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-19339930633/36893488147419103232), (-68071546029/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((7502460715/147573952589676412928), (49977559245/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-17303204745/4722366482869645213696), (-16647567529/4722366482869645213696)), (17/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((69353008387/302231454903657293676544), (38081046649/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-63337381325/4835703278458516698824704), (-15378899171/4835703278458516698824704)), (19/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((107348734341/154742504910672534362390528), (-2764340871/154742504910672534362390528)), (39/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-84775197587/2475880078570760549798248448), (12634700679/1237940039285380274899124224)), (5/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (3243/1280)))⁻¹=value ((5120000/51505683), (-1383680/51505683)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/51505683), (-1383680/51505683))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504956113/576460752303423488), (99771011041/576460752303423488)), (25/576460752303423488), by norm_num⟩
  | 1 => ⟨((-824327885/9007199254740992), (-64181453557/576460752303423488)), (21/576460752303423488), by norm_num⟩
  | 2 => ⟨((75222023733/1152921504606846976), (17393926343/1152921504606846976)), (25/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-11899893039/576460752303423488), (23073461473/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((24156869761/9223372036854775808), (-54480119903/9223372036854775808)), (29/9223372036854775808), by norm_num⟩
  | 5 => ⟨((554823077/1152921504606846976), (13923167781/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-22525391441/73786976294838206464), (-25309855609/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 7 => ⟨((81340640595/1180591620717411303424), (-21932626693/1180591620717411303424)), (47/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-15613827121/2361183241434822606848), (56274104561/4722366482869645213696)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-14693394921/18889465931478580854784), (-11063589209/4722366482869645213696)), (203/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((59689100295/151115727451828646838272), (6233071541/37778931862957161709568)), (201/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-38242158763/604462909807314587353088), (10137146131/302231454903657293676544)), (97/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((19043649991/9671406556917033397649408), (-27722331145/2417851639229258349412352)), (23/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((83/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/186875449), (-4151040/186875449)), 0, by norm_num⟩
  | 1 => ⟨((-135857234739200/34922433438951601), (70561038336000/34922433438951601)), 0, by norm_num⟩
  | 2 => ⟨((21742594007/140737488355328), (-38027465053/281474976710656)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-12443048983/2251799813685248), (70799225579/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 4 => ⟨((738670169/4503599627370496), (-60364480827/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-12947522285/4611686018427387904), (96254019737/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-3841427523/36893488147419103232), (-72343799939/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((18446435969/1180591620717411303424), (51278518037/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-45071224027/37778931862957161709568), (-4254603115/2361183241434822606848)), (17/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((11223680195/151115727451828646838272), (10381788307/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-80097780707/19342813113834066795298816), (-22240926027/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4136926683/19342813113834066795298816), (18135339857/309485009821345068724781056)), (29/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-102778074277/9903520314283042199192993792), (-2869161551/9903520314283042199192993792)), (27/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (3243/1280)))⁻¹=value ((16998400/186875449), (-4151040/186875449)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/186875449), (-4151040/186875449))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21735499505/4611686018427387904), (71624015675/4611686018427387904)), (23/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-25789969617/2305843009213693952), (-5043144875/576460752303423488)), (21/4611686018427387904), by norm_num⟩
  | 2 => ⟨((126834277367/18446744073709551616), (3628588633/18446744073709551616)), (51/18446744073709551616), by norm_num⟩
  | 3 => ⟨((-2271640945/1152921504606846976), (52985068391/36893488147419103232)), (43/36893488147419103232), by norm_num⟩
  | 4 => ⟨((26665301037/147573952589676412928), (-100743238099/147573952589676412928)), (31/73786976294838206464), by norm_num⟩
  | 5 => ⟨((11314339579/147573952589676412928), (47127973687/295147905179352825856)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-86981896627/2361183241434822606848), (-17980375655/1180591620717411303424)), (95/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((2272334917/295147905179352825856), (-6934194321/2361183241434822606848)), (105/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-6180035385/9444732965739290427392), (54775632497/37778931862957161709568)), (113/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-32985311539/302231454903657293676544), (-81310926285/302231454903657293676544)), (231/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((57478699683/1208925819614629174706176), (5215722111/302231454903657293676544)), (231/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-71218195529/9671406556917033397649408), (10153616807/2417851639229258349412352)), (447/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((16456184419/77371252455336267181195264), (-105182241113/77371252455336267181195264)), (851/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((91/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/222510649), (-4151040/222510649)), 0, by norm_num⟩
  | 1 => ⟨((-165049590579200/49510988918401201), (77362102272000/49510988918401201)), 0, by norm_num⟩
  | 2 => ⟨((17596545219/140737488355328), (-54342097525/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-19526201737/4503599627370496), (5864612149/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((9582605031/72057594037927936), (-74530467511/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((-14560289091/4611686018427387904), (27830048243/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((2898551345/147573952589676412928), (-78936729261/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 7 => ⟨((9838623011/2361183241434822606848), (106649100715/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-29101549443/75557863725914323419136), (-17131017625/18889465931478580854784)), (13/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((14863215185/604462909807314587353088), (20785840255/604462909807314587353088)), (3/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-26122659727/19342813113834066795298816), (-46837667985/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((83994944649/1237940039285380274899124224), (47173065579/1237940039285380274899124224)), (35/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-7915190911/2475880078570760549798248448), (-2384104383/2475880078570760549798248448)), (15/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (3243/1280)))⁻¹=value ((18636800/222510649), (-4151040/222510649)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/222510649), (-4151040/222510649))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12626709137/18446744073709551616), (22374075723/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((-42057637335/36893488147419103232), (-5243480893/9223372036854775808)), (37/73786976294838206464), by norm_num⟩
  | 2 => ⟨((93355291765/147573952589676412928), (-113700431/1152921504606846976)), (23/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-48347943065/295147905179352825856), (24656186755/147573952589676412928)), (41/295147905179352825856), by norm_num⟩
  | 4 => ⟨((4545490295/590295810358705651712), (-20386890185/295147905179352825856)), (59/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((45911785305/4722366482869645213696), (70401836323/4722366482869645213696)), (77/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-9245899633/2361183241434822606848), (-10597224393/9444732965739290427392)), (93/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((28882319029/37778931862957161709568), (-28646808497/75557863725914323419136)), (105/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((-16996471283/302231454903657293676544), (47346007067/302231454903657293676544)), (225/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-32075884265/2417851639229258349412352), (-16672619311/604462909807314587353088)), (233/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((98977978125/19342813113834066795298816), (30751484599/19342813113834066795298816)), (467/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-59386203839/77371252455336267181195264), (9096116121/19342813113834066795298816)), (455/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((12509698653/618970019642690137449562112), (-89555189553/618970019642690137449562112)), (435/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((99/8), (3243/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/29046961), (-1383680/87140883)), 0, by norm_num⟩
  | 1 => ⟨((-21880700108800/7593533490019689), (3117154304000/2531177830006563)), 0, by norm_num⟩
  | 2 => ⟨((7174996895/70368744177664), (-39762879307/562949953421312)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-30563187319/9007199254740992), (63925290477/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((14902963259/144115188075855872), (-23713876079/144115188075855872)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-12468594487/4611686018427387904), (66426241669/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((14068773829/295147905179352825856), (-88764801951/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((5093302553/9444732965739290427392), (113723836097/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-4401607303/37778931862957161709568), (-8739223735/18889465931478580854784)), (9/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((9902566811/1208925819614629174706176), (82283984853/4835703278458516698824704)), (7/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-8757238191/19342813113834066795298816), (-46022039841/77371252455336267181195264)), (11/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((55160230671/2475880078570760549798248448), (24105010981/1237940039285380274899124224)), (17/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-20174326035/19807040628566084398385987584), (-45810599271/79228162514264337593543950336)), (13/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (3243/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (3243/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (3243/1280)))⁻¹=value ((2252800/29046961), (-1383680/87140883)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/29046961), (-1383680/87140883))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21352992189/295147905179352825856), (6139099071/73786976294838206464)), (31/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-7445567789/73786976294838206464), (-4226804471/147573952589676412928)), (15/295147905179352825856), by norm_num⟩
  | 2 => ⟨((15240589197/295147905179352825856), (-10261651297/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-28135907875/2361183241434822606848), (78595111275/4722366482869645213696)), (69/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-1602060987/9444732965739290427392), (-117481474827/18889465931478580854784)), (101/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((4942918249/4722366482869645213696), (23454924895/18889465931478580854784)), (67/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-112418550023/302231454903657293676544), (-19549708607/302231454903657293676544)), (163/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((20615399205/302231454903657293676544), (-1586297235/37778931862957161709568)), (93/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-5060360677/1208925819614629174706176), (18390762199/1208925819614629174706176)), (101/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-13784892403/9671406556917033397649408), (-24678758831/9671406556917033397649408)), (105/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((77005811695/154742504910672534362390528), (20067919533/154742504910672534362390528)), (423/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-22403361617/309485009821345068724781056), (29451467535/618970019642690137449562112)), (415/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((4207669025/2475880078570760549798248448), (-17284210797/1237940039285380274899124224)), (199/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14296917365/274877906944), (51349918219/549755813888)), (79/137438953472), by norm_num⟩
  | 1 => ⟨((-35331683831/1099511627776), (85694280707/1099511627776)), (357/274877906944), by norm_num⟩
  | 2 => ⟨((-29661934517/1099511627776), (4597988013/549755813888)), (3375/2199023255552), by norm_num⟩
  | 3 => ⟨((-4642063929/1099511627776), (-18495731463/8796093022208)), (11071/8796093022208), by norm_num⟩
  | 4 => ⟨((-58011540419/140737488355328), (-12117205609/70368744177664)), (55715/70368744177664), by norm_num⟩
  | 5 => ⟨((-36460160335/281474976710656), (-26167669195/562949953421312)), (228421/562949953421312), by norm_num⟩
  | 6 => ⟨((-33029505827/4503599627370496), (-95974926073/4503599627370496)), (795981/4503599627370496), by norm_num⟩
  | 7 => ⟨((53719348191/72057594037927936), (-14845113447/36028797018963968)), (4863139/72057594037927936), by norm_num⟩
  | 8 => ⟨((-98673343059/288230376151711744), (-4084162379/72057594037927936)), (832381/36028797018963968), by norm_num⟩
  | 9 => ⟨((4635602263/576460752303423488), (-83462560361/1152921504606846976)), (4158107/576460752303423488), by norm_num⟩
  | 10 => ⟨((67739085665/9223372036854775808), (42908282325/9223372036854775808)), (4798417/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-28234060007/18446744073709551616), (14391422241/36893488147419103232)), (20687019/36893488147419103232), by norm_num⟩
  | 12 => ⟨((4243297489/73786976294838206464), (-84449746621/295147905179352825856)), (328417/2305843009213693952), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14296917365/274877906944), (51349918219/549755813888)), (317/549755813888), by norm_num⟩
  | 1 => ⟨((-35331683831/1099511627776), (85694280707/1099511627776)), (1429/1099511627776), by norm_num⟩
  | 2 => ⟨((-29661934517/1099511627776), (4597988013/549755813888)), (211/137438953472), by norm_num⟩
  | 3 => ⟨((-4642063929/1099511627776), (-18495731463/8796093022208)), (22143/17592186044416), by norm_num⟩
  | 4 => ⟨((-58011540419/140737488355328), (-12117205609/70368744177664)), (27859/35184372088832), by norm_num⟩
  | 5 => ⟨((-36460160335/281474976710656), (-26167669195/562949953421312)), (57111/140737488355328), by norm_num⟩
  | 6 => ⟨((-33029505827/4503599627370496), (-95974926073/4503599627370496)), (398081/2251799813685248), by norm_num⟩
  | 7 => ⟨((53719348191/72057594037927936), (-14845113447/36028797018963968)), (2433011/36028797018963968), by norm_num⟩
  | 8 => ⟨((-98673343059/288230376151711744), (-4084162379/72057594037927936)), (3335289/144115188075855872), by norm_num⟩
  | 9 => ⟨((4635602263/576460752303423488), (-83462560361/1152921504606846976)), (8362331/1152921504606846976), by norm_num⟩
  | 10 => ⟨((67739085665/9223372036854775808), (42908282325/9223372036854775808)), (19562603/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-28234060007/18446744073709551616), (14391422241/36893488147419103232)), (22162759/36893488147419103232), by norm_num⟩
  | 12 => ⟨((4243297489/73786976294838206464), (-84449746621/295147905179352825856)), (53843293/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile011Gamma
