/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile003Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/17179869184), (-116429082519/34359738368)), (3/68719476736), by norm_num⟩
  | 1 => ⟨((-75496061613/34359738368), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-420213142587357/2251799813685248), (52964619598677/1125899906842624)), (54497/2251799813685248), by norm_num⟩
  | 1 => ⟨((14088480295/34359738368), (-7102976313/68719476736)), (31/549755813888), by norm_num⟩
  | 2 => ⟨((-61911110323/137438953472), (62427336509/549755813888)), (9/137438953472), by norm_num⟩
  | 3 => ⟨((11336051101/34359738368), (-91444585383/1099511627776)), (7/137438953472), by norm_num⟩
  | 4 => ⟨((-398525601425/2199023255552), (50231072617/1099511627776)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((350260098459/4398046511104), (-5518447365/274877906944)), (59/4398046511104), by norm_num⟩
  | 6 => ⟨((-128266682799/4398046511104), (64668096955/8796093022208)), (45/8796093022208), by norm_num⟩
  | 7 => ⟨((322092237599/35184372088832), (-20298618857/8796093022208)), (59/35184372088832), by norm_num⟩
  | 8 => ⟨((-353854490311/140737488355328), (89201248477/140737488355328)), (67/140737488355328), by norm_num⟩
  | 9 => ⟨((345554570183/562949953421312), (-87108966881/562949953421312)), (17/140737488355328), by norm_num⟩
  | 10 => ⟨((-303704397767/2251799813685248), (76559185175/2251799813685248)), (31/1125899906842624), by norm_num⟩
  | 11 => ⟨((242657006189/9007199254740992), (-61170081195/9007199254740992)), (13/2251799813685248), by norm_num⟩
  | 12 => ⟨((-177723979287/36028797018963968), (5600183575/4503599627370496)), (79/72057594037927936), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677669/5070602400912917605986812821504), (3770608760371/10141204801825835211973625643008)), (29/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779416448882107/633825300114114700748351602688), (4465461856691/633825300114114700748351602688)), (69/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472617451125045/9903520314283042199192993792), (156965164101/1237940039285380274899124224)), (77/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472572377780541/618970019642690137449562112), (2667957442007/1237940039285380274899124224)), (41/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771954789259903/154742504910672534362390528), (5334901471831/154742504910672534362390528)), (41/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550268739268419/9671406556917033397649408), (5000393375063/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259413552197509/604462909807314587353088), (4374267443319/604462909807314587353088)), (17/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944402762129175/37778931862957161709568), (7106165660305/75557863725914323419136)), (109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298297872896303/4722366482869645213696), (2663928833593/2361183241434822606848)), (83/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811244098569687/295147905179352825856), (915366698211/73786976294838206464)), (113/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456192651953397/18446744073709551616), (9149360893819/73786976294838206464)), (141/73786976294838206464), by norm_num⟩
  | 7 => ⟨((114006826100341/576460752303423488), (10287110092271/9223372036854775808)), (79/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797675323581019/576460752303423488), (2569927223729/288230376151711744)), (79/576460752303423488), by norm_num⟩
  | 5 => ⟨((597883501166589/72057594037927936), (8986418870803/144115188075855872)), (139/144115188075855872), by norm_num⟩
  | 4 => ⟨((186675111891087/4503599627370496), (13462975352941/36028797018963968)), (209/36028797018963968), by norm_num⟩
  | 3 => ⟨((372858588571229/2251799813685248), (16799576327409/9007199254740992)), (131/4503599627370496), by norm_num⟩
  | 2 => ⟨((1116109316574825/2251799813685248), (16755861875611/2251799813685248)), (263/2251799813685248), by norm_num⟩
  | 1 => ⟨((555575892787039/562949953421312), (6256126798091/281474976710656)), (397/1125899906842624), by norm_num⟩
  | 0 => ⟨((68509833264705/70368744177664), (49611883366561/1125899906842624)), (201/281474976710656), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((68509833264705/70368744177664), (49611883366561/1125899906842624)), (766755224132449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((266253587631213/281474976710656), (48301300486615/562949953421312)), (1637/1125899906842624), by norm_num⟩
  | 2 => ⟨((999132780340765/1125899906842624), (182757198413903/1125899906842624)), (3379/1125899906842624), by norm_num⟩
  | 3 => ⟨((214243316238731/281474976710656), (162180231714057/562949953421312)), (7095/1125899906842624), by norm_num⟩
  | 4 => ⟨((1117672117722537/2251799813685248), (123442698448121/281474976710656)), (14889/1125899906842624), by norm_num⟩
  | 5 => ⟨((243318765602167/4503599627370496), (980324885744437/2251799813685248)), (111359/4503599627370496), by norm_num⟩
  | 6 => ⟨((-420213142587357/2251799813685248), (52964619598677/1125899906842624)), (54497/2251799813685248), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-28311023105/17179869184), (-116429082519/34359738368)), (3/68719476736), by norm_num⟩, -1, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7417145753/4294967296), (-244024095273/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-316464885461/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1469348179355703/9007199254740992), (637620858492283/9007199254740992)), (17329/1125899906842624), by norm_num⟩
  | 1 => ⟨((206500196179/549755813888), (-89610368881/549755813888)), (21/549755813888), by norm_num⟩
  | 2 => ⟨((-237742136711/549755813888), (103167749781/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((91236916661/274877906944), (-79184174241/549755813888)), (43/1099511627776), by norm_num⟩
  | 4 => ⟨((-105040382117/549755813888), (22791037401/274877906944)), (13/549755813888), by norm_num⟩
  | 5 => ⟨((48372883605/549755813888), (-83965284757/2199023255552)), (13/1099511627776), by norm_num⟩
  | 6 => ⟨((-148510240925/4398046511104), (32222868835/2199023255552)), (21/4398046511104), by norm_num⟩
  | 7 => ⟨((97702133403/8796093022208), (-10599413919/2199023255552)), (29/17592186044416), by norm_num⟩
  | 8 => ⟨((-224967475927/70368744177664), (97624209937/70368744177664)), (35/70368744177664), by norm_num⟩
  | 9 => ⟨((230225225101/281474976710656), (-99905800229/281474976710656)), (19/140737488355328), by norm_num⟩
  | 10 => ⟨((-212045268539/1125899906842624), (23004160631/281474976710656)), (37/1125899906842624), by norm_num⟩
  | 11 => ⟨((355092563183/9007199254740992), (-77045872503/4503599627370496)), (65/9007199254740992), by norm_num⟩
  | 12 => ⟨((-136271807103/18014398509481984), (118269785001/36028797018963968)), (13/9007199254740992), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (3558953033283/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779295718369243/633825300114114700748351602688), (4214252636885/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890334072310187/39614081257132168796771975168), (1185072247905/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945072703311705/1237940039285380274899124224), (5035666856505/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771810809561667/154742504910672534362390528), (5034665327469/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550133890862011/9671406556917033397649408), (2359467334651/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314823923089461/151115727451828646838272), (2064001907891/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236076781298895/9444732965739290427392), (1676502820343/18889465931478580854784)), (37/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162269329340809/590295810358705651712), (5027763025019/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622291597476973/590295810358705651712), (6910338048641/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((228065673394327/9223372036854775808), (8633668786163/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823834071119365/9223372036854775808), (18959041179/18014398509481984)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797538204178381/576460752303423488), (2424929918045/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195528063468983/144115188075855872), (8479032960393/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493044524383951/36028797018963968), (6351054649825/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490992450644903/9007199254740992), (15848874021659/9007199254740992)), (175/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115672740751817/2251799813685248), (1975718198487/281474976710656)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110510199746393/1125899906842624), (23600852266215/1125899906842624)), (265/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094927021657095/1125899906842624), (1461593013537/35184372088832)), (535/1125899906842624), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1094927021657095/1125899906842624), (1461593013537/35184372088832)), (2040867332076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531431635816643/562949953421312), (45484332678907/562949953421312)), (543/562949953421312), by norm_num⟩
  | 2 => ⟨((996005976459129/1125899906842624), (21468882955471/140737488355328)), (2227/1125899906842624), by norm_num⟩
  | 3 => ⟨((854897910044927/1125899906842624), (303872635236511/1125899906842624)), (1155/281474976710656), by norm_num⟩
  | 4 => ⟨((567112453134657/1125899906842624), (461462123239787/1125899906842624)), (19021/2251799813685248), by norm_num⟩
  | 5 => ⟨((193035353595825/2251799813685248), (1859496853308279/4503599627370496)), (17377/1125899906842624), by norm_num⟩
  | 6 => ⟨((-1469348179355703/9007199254740992), (637620858492283/9007199254740992)), (17329/1125899906842624), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-244024095273/68719476736)), (1/34359738368), by norm_num⟩, -1, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-123586581311/68719476736), (-63531226955/17179869184)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-329564216829/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-316572118343347/2251799813685248), (787582889582237/9007199254740992)), (65671/4503599627370496), by norm_num⟩
  | 1 => ⟨((92664402597/274877906944), (-57633706295/274877906944)), (21/549755813888), by norm_num⟩
  | 2 => ⟨((-13887470809/34359738368), (138199591879/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((177603736555/549755813888), (-110462716023/549755813888)), (23/549755813888), by norm_num⟩
  | 4 => ⟨((-106468790079/549755813888), (66219506143/549755813888)), (15/549755813888), by norm_num⟩
  | 5 => ⟨((204240806745/2199023255552), (-63514976299/1099511627776)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((-81624677501/2199023255552), (50767420473/2199023255552)), (51/8796093022208), by norm_num⟩
  | 7 => ⟨((27961061189/2199023255552), (-34781416447/4398046511104)), (37/17592186044416), by norm_num⟩
  | 8 => ⟨((-134095392895/35184372088832), (166804388159/70368744177664)), (23/35184372088832), by norm_num⟩
  | 9 => ⟨((142909648323/140737488355328), (-177768646155/281474976710656)), (51/281474976710656), by norm_num⟩
  | 10 => ⟨((-274145896121/1125899906842624), (170508238507/1125899906842624)), (51/1125899906842624), by norm_num⟩
  | 11 => ⟨((29880597653/562949953421312), (-74338345289/2251799813685248)), (23/2251799813685248), by norm_num⟩
  | 12 => ⟨((-191068116961/18014398509481984), (14854630563/2251799813685248)), (39/18014398509481984), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122365965/10141204801825835211973625643008), (1683743569237/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779186460156657/633825300114114700748351602688), (1993531268627/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945105617459095/19807040628566084398385987584), (560589471871/4951760157141521099596496896)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945007494480231/1237940039285380274899124224), (4764133908959/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442920125268161/38685626227668133590597632), (4763147734227/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387502960653195/2417851639229258349412352), (2232201641139/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314797254014063/151115727451828646838272), (122040789275/18889465931478580854784)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((29506892478963/1180591620717411303424), (6344156983733/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324506243982109/1180591620717411303424), (4756399406775/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622113625217531/590295810358705651712), (3268628654975/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456075846103427/18446744073709551616), (1020923068859/9223372036854775808)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455896238400731/2305843009213693952), (4591275778089/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797414042285597/576460752303423488), (9175358251605/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((149413959012789/18014398509481984), (8020348449695/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492721718719841/36028797018963968), (6007174385889/18014398509481984)), (35/9007199254740992), by norm_num⟩
  | 3 => ⟨((745296027674059/4503599627370496), (14989645501117/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((278819250458695/562949953421312), (7473618838129/1125899906842624)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109928192736189/1125899906842624), (22314935118435/1125899906842624)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((1093809175195219/1125899906842624), (44206778583311/1125899906842624)), (267/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093809175195219/1125899906842624), (44206778583311/1125899906842624)), (1018526317405523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((66306086869335/70368744177664), (85893567849825/1125899906842624)), (135/140737488355328), by norm_num⟩
  | 2 => ⟨((496547499525999/562949953421312), (80934602967881/562949953421312)), (2201/1125899906842624), by norm_num⟩
  | 3 => ⟨((852683290474777/1125899906842624), (71388006135519/281474976710656)), (4517/1125899906842624), by norm_num⟩
  | 4 => ⟨((1146689561321805/2251799813685248), (216258513219955/562949953421312)), (18267/2251799813685248), by norm_num⟩
  | 5 => ⟨((982916937777/8796093022208), (881006839592743/2251799813685248)), (255/17592186044416), by norm_num⟩
  | 6 => ⟨((-316572118343347/2251799813685248), (787582889582237/9007199254740992)), (65671/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-123586581311/68719476736), (-63531226955/17179869184)), (1/34359738368), by norm_num⟩, -1, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-128071113533/68719476736), (-263346227203/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-170761484711/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-538457985589715/4503599627370496), (889903233572909/9007199254740992)), (124013/9007199254740992), by norm_num⟩
  | 1 => ⟨((163332254519/549755813888), (-134968656175/549755813888)), (5/137438953472), by norm_num⟩
  | 2 => ⟨((-202932702689/549755813888), (167692255621/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((168089607457/549755813888), (-138899867037/549755813888)), (3/68719476736), by norm_num⟩
  | 4 => ⟨((-208843491665/1099511627776), (172576601627/1099511627776)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((207582632481/2199023255552), (-21441837249/274877906944)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((-171941154611/4398046511104), (71041285285/2199023255552)), (15/2199023255552), by norm_num⟩
  | 7 => ⟨((122073633847/8796093022208), (-100874835551/8796093022208)), (45/17592186044416), by norm_num⟩
  | 8 => ⟨((-151670792255/35184372088832), (31333068707/8796093022208)), (15/17592186044416), by norm_num⟩
  | 9 => ⟨((167505671223/140737488355328), (-138417334735/140737488355328)), (35/140737488355328), by norm_num⟩
  | 10 => ⟨((-166494382519/562949953421312), (137581662211/562949953421312)), (37/562949953421312), by norm_num⟩
  | 11 => ⟨((150444726645/2251799813685248), (-248638245321/4503599627370496)), (69/4503599627370496), by norm_num⟩
  | 12 => ⟨((-124613700555/9007199254740992), (102973804865/9007199254740992)), (59/18014398509481984), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115840927/10141204801825835211973625643008), (3192692471335/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779086678579041/633825300114114700748351602688), (1889850454597/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945049524744461/19807040628566084398385987584), (2125725310283/19807040628566084398385987584)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889895877819577/2475880078570760549798248448), (4516305494109/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771561486516729/154742504910672534362390528), (564417144633/19342813113834066795298816)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549900369051977/9671406556917033397649408), (2116049926431/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629545789617651/302231454903657293676544), (3702058781141/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888282976004677/75557863725914323419136), (6013917214347/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297906537017345/4722366482869645213696), (4508750945553/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405487761168945/147573952589676412928), (6196791797765/590295810358705651712)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824100567894663/73786976294838206464), (7741879610227/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911678673575457/4611686018427387904), (8703964736177/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594601180093131/1152921504606846976), (4348452438515/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195113919454411/144115188075855872), (950231595207/18014398509481984)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492426664912387/36028797018963968), (5693454742485/18014398509481984)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490225989277683/9007199254740992), (887867736983/562949953421312)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((557457525922701/1125899906842624), (3541072991575/562949953421312)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109395520476361/1125899906842624), (2642823878611/140737488355328)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((68299038533905/70368744177664), (41870593762517/1125899906842624)), (533/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((68299038533905/70368744177664), (41870593762517/1125899906842624)), (2033237937545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((33096444238819/35184372088832), (81278167750259/1125899906842624)), (1075/1125899906842624), by norm_num⟩
  | 2 => ⟨((495184991504913/562949953421312), (9556864976829/70368744177664)), (1089/562949953421312), by norm_num⟩
  | 3 => ⟨((850387568533005/1125899906842624), (538013421460695/2251799813685248)), (8847/2251799813685248), by norm_num⟩
  | 4 => ⟨((1156043094670017/2251799813685248), (203179662123391/562949953421312)), (17593/2251799813685248), by norm_num⟩
  | 5 => ⟨((150085285338669/1125899906842624), (834477182021705/2251799813685248)), (7691/562949953421312), by norm_num⟩
  | 6 => ⟨((-538457985589715/4503599627370496), (889903233572909/9007199254740992)), (124013/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-128071113533/68719476736), (-263346227203/68719476736)), (1/34359738368), by norm_num⟩, -1, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-66098241637/34359738368), (-271829018733/68719476736)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-176261977699/68719476736), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-451632209467375/4503599627370496), (956547768627713/9007199254740992)), (116927/9007199254740992), by norm_num⟩
  | 1 => ⟨((141407927915/549755813888), (-149749547395/549755813888)), (5/137438953472), by norm_num⟩
  | 2 => ⟨((-181352086923/549755813888), (192050002685/549755813888)), (7/137438953472), by norm_num⟩
  | 3 => ⟨((77526486471/274877906944), (-164199510329/549755813888)), (13/274877906944), by norm_num⟩
  | 4 => ⟨((-49712877915/274877906944), (210581714257/1099511627776)), (35/1099511627776), by norm_num⟩
  | 5 => ⟨((204017622825/2199023255552), (-216052573071/2199023255552)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((-174431623525/4398046511104), (184721302825/4398046511104)), (35/4398046511104), by norm_num⟩
  | 7 => ⟨((255661874675/17592186044416), (-67685826713/4398046511104)), (27/8796093022208), by norm_num⟩
  | 8 => ⟨((-81969970147/17592186044416), (173610717737/35184372088832)), (37/35184372088832), by norm_num⟩
  | 9 => ⟨((186887842009/140737488355328), (-98956155313/70368744177664)), (45/140737488355328), by norm_num⟩
  | 10 => ⟨((-191743140111/562949953421312), (203054021589/562949953421312)), (3/35184372088832), by norm_num⟩
  | 11 => ⟨((44710131275/562949953421312), (-94695142219/1125899906842624)), (23/1125899906842624), by norm_num⟩
  | 12 => ⟨((-152905629981/9007199254740992), (80962748063/4503599627370496)), (41/9007199254740992), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418255/10141204801825835211973625643008), (3031896964715/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444748714384703/158456325028528675187087900672), (1794493025311/316912650057057350374175801344)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889995812105537/39614081257132168796771975168), (1009228442169/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889786264795395/2475880078570760549798248448), (4288377501133/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885725979873325/77371252455336267181195264), (2143714396971/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774898889657877/4835703278458516698824704), (2009228323261/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157375238098543/75557863725914323419136), (3515141890479/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118008589165283/4722366482869645213696), (2855108273909/37778931862957161709568)), (37/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297797525079581/4722366482869645213696), (66890779401/73786976294838206464)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810900698495907/295147905179352825856), (735462989467/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823913873617027/73786976294838206464), (7350604092637/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823147817977535/9223372036854775808), (4131948043077/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99649517351675/72057594037927936), (8256982130139/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194931833942339/144115188075855872), (3608542605595/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492154942687571/36028797018963968), (2702522410135/9007199254740992)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((186236099001629/1125899906842624), (13485443058857/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((8707668185443/17592186044416), (13444735269313/2251799813685248)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((554452190894617/562949953421312), (20065493664417/1125899906842624)), (33/140737488355328), by norm_num⟩
  | 0 => ⟨((545919358300203/562949953421312), (39725514085615/1125899906842624)), (133/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((545919358300203/562949953421312), (39725514085615/1125899906842624)), (507355810069949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((528703155299517/562949953421312), (19261860691135/281474976710656)), (535/562949953421312), by norm_num⟩
  | 2 => ⟨((123475873665469/140737488355328), (72360297482581/562949953421312)), (2157/1125899906842624), by norm_num⟩
  | 3 => ⟨((1696098546144115/2251799813685248), (126970447672007/562949953421312)), (1085/281474976710656), by norm_num⟩
  | 4 => ⟨((581491824673753/1125899906842624), (765092493181493/2251799813685248)), (531/70368744177664), by norm_num⟩
  | 5 => ⟨((340689452439133/2251799813685248), (790292329185677/2251799813685248)), (7275/562949953421312), by norm_num⟩
  | 6 => ⟨((-451632209467375/4503599627370496), (956547768627713/9007199254740992)), (116927/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66098241637/34359738368), (-271829018733/68719476736)), (1/34359738368), by norm_num⟩, -1, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34003994769/17179869184), (-139841428487/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-362709277535/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-745668806931897/9007199254740992), (996368418074371/9007199254740992)), (110147/9007199254740992), by norm_num⟩
  | 1 => ⟨((30027202307/137438953472), (-160490318403/549755813888)), (5/137438953472), by norm_num⟩
  | 2 => ⟨((-4952719271/17179869184), (211771575557/549755813888)), (7/137438953472), by norm_num⟩
  | 3 => ⟨((34854693583/137438953472), (-186292442893/549755813888)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((-183967069143/1099511627776), (122909109217/549755813888)), (19/549755813888), by norm_num⟩
  | 5 => ⟨((48549964223/549755813888), (-259491348445/2199023255552)), (21/1099511627776), by norm_num⟩
  | 6 => ⟨((-85417425957/2199023255552), (114135424181/2199023255552)), (39/4398046511104), by norm_num⟩
  | 7 => ⟨((128812276599/8796093022208), (-43029989679/2199023255552)), (31/8796093022208), by norm_num⟩
  | 8 => ⟨((-21246436419/4398046511104), (227117219311/35184372088832)), (43/35184372088832), by norm_num⟩
  | 9 => ⟨((199362004479/140737488355328), (-266389049913/140737488355328)), (53/140737488355328), by norm_num⟩
  | 10 => ⟨((-210451103667/562949953421312), (281206389881/562949953421312)), (29/281474976710656), by norm_num⟩
  | 11 => ⟨((50490229787/562949953421312), (-67465434941/562949953421312)), (29/1125899906842624), by norm_num⟩
  | 12 => ⟨((-177662147991/9007199254740992), (118696767051/4503599627370496)), (53/9007199254740992), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987295/10141204801825835211973625643008), (2883023578589/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778909818146169/633825300114114700748351602688), (3412445287895/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889900197801429/39614081257132168796771975168), (959580804679/9903520314283042199192993792)), (51/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889684743639771/2475880078570760549798248448), (2038696806377/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771350516234923/154742504910672534362390528), (2038232916087/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774851379243867/4835703278458516698824704), (1910350563159/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258918843991627/604462909807314587353088), (1671064045721/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944001303662295/37778931862957161709568), (5429110953931/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297696545677627/4722366482869645213696), (4070217339445/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810831384843519/295147905179352825856), (1398480957409/147573952589676412928)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823740918291549/73786976294838206464), (873558580679/9223372036854775808)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911476847465721/4611686018427387904), (7856617268885/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((24909354977827/18014398509481984), (3924929089835/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((74672693964189/9007199254740992), (3430513274951/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491903112088709/36028797018963968), (642272041287/2251799813685248)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((744788106519071/4503599627370496), (12818889290837/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((557136126557011/1125899906842624), (12779114028971/2251799813685248)), (175/2251799813685248), by norm_num⟩
  | 1 => ⟨((1108448697298421/1125899906842624), (19069415188333/1125899906842624)), (263/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090960056904623/1125899906842624), (18871451001229/562949953421312)), (531/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090960056904623/1125899906842624), (18871451001229/562949953421312)), (2025608543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527919627617455/562949953421312), (2285727080739/35184372088832)), (533/562949953421312), by norm_num⟩
  | 2 => ⟨((1970773047774235/2251799813685248), (137183654862709/1125899906842624)), (1069/562949953421312), by norm_num⟩
  | 3 => ⟨((1691388800212305/2251799813685248), (480252015219999/2251799813685248)), (8527/2251799813685248), by norm_num⟩
  | 4 => ⟨((584011522555439/1125899906842624), (90182625791801/281474976710656)), (257/35184372088832), by norm_num⟩
  | 5 => ⟨((749419948541635/4503599627370496), (748452927676867/2251799813685248)), (55207/4503599627370496), by norm_num⟩
  | 6 => ⟨((-745668806931897/9007199254740992), (996368418074371/9007199254740992)), (110147/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34003994769/17179869184), (-139841428487/34359738368)), (1/34359738368), by norm_num⟩, -1, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-34892961149/17179869184), (-143497302725/34359738368)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((-372191585589/137438953472), 0), (1/137438953472), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-75447988714453/1125899906842624), (1015968487804599/9007199254740992)), (103633/9007199254740992), by norm_num⟩
  | 1 => ⟨((99764131353/549755813888), (-335851277797/1099511627776)), (9/274877906944), by norm_num⟩
  | 2 => ⟨((-135083137987/549755813888), (227375530095/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((60968653165/274877906944), (-102624058333/274877906944)), (27/549755813888), by norm_num⟩
  | 4 => ⟨((-20638271683/137438953472), (277911101807/1099511627776)), (39/1099511627776), by norm_num⟩
  | 5 => ⟨((178846322501/2199023255552), (-301038886055/2199023255552)), (11/549755813888), by norm_num⟩
  | 6 => ⟨((-80720803269/2199023255552), (271742805307/4398046511104)), (21/2199023255552), by norm_num⟩
  | 7 => ⟨((15613999109/1099511627776), (-3285237315/137438953472)), (17/4398046511104), by norm_num⟩
  | 8 => ⟨((-42283493427/8796093022208), (142345401145/17592186044416)), (49/35184372088832), by norm_num⟩
  | 9 => ⟨((203565907339/140737488355328), (-342647548619/140737488355328)), (61/140737488355328), by norm_num⟩
  | 10 => ⟨((-110253339261/281474976710656), (185581352589/281474976710656)), (35/281474976710656), by norm_num⟩
  | 11 => ⟨((27142870687/281474976710656), (-91375203491/562949953421312)), (9/281474976710656), by norm_num⟩
  | 12 => ⟨((-49002837615/2251799813685248), (164965758793/4503599627370496)), (67/9007199254740992), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (1372212885961/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778830625560205/633825300114114700748351602688), (3248118822765/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236226394484493/4951760157141521099596496896), (228342126487/2475880078570760549798248448)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889590199172901/2475880078570760549798248448), (1940505374995/1237940039285380274899124224)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771256042140531/154742504910672534362390528), (3880104830643/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774807131882171/4835703278458516698824704), (3636635932443/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629420742907151/302231454903657293676544), (795273577893/151115727451828646838272)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887877040286313/75557863725914323419136), (645934340615/9444732965739290427392)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297602492825615/4722366482869645213696), (3874028414833/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621533645821691/590295810358705651712), (5324226288121/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823579811429053/73786976294838206464), (6651440199919/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455693214757191/2305843009213693952), (3738794513091/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594018393740467/1152921504606846976), (7470991216721/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((74662868333299/9007199254740992), (6529699851781/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491668443220997/36028797018963968), (2444931883855/9007199254740992)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489284878415345/9007199254740992), (12198749037035/9007199254740992)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113983911656137/2251799813685248), (12159940556735/2251799813685248)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((554011818227307/562949953421312), (9071544751211/562949953421312)), (263/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090139551400973/1125899906842624), (17950046605141/562949953421312)), (265/562949953421312), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1090139551400973/1125899906842624), (17950046605141/562949953421312)), (1010896922874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((527185151016333/562949953421312), (8689962417987/140737488355328)), (2121/2251799813685248), by norm_num⟩
  | 2 => ⟨((1966184984090783/2251799813685248), (260412159016865/2251799813685248)), (1059/562949953421312), by norm_num⟩
  | 3 => ⟨((843340708178763/1125899906842624), (454763761522533/2251799813685248)), (4189/1125899906842624), by norm_num⟩
  | 4 => ⟨((1171544693031249/2251799813685248), (340634891579273/1125899906842624)), (249/35184372088832), by norm_num⟩
  | 5 => ⟨((806811018283319/4503599627370496), (1417777893276807/4503599627370496)), (26225/2251799813685248), by norm_num⟩
  | 6 => ⟨((-75447988714453/1125899906842624), (1015968487804599/9007199254740992)), (103633/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-143497302725/34359738368)), (1/34359738368), by norm_num⟩, -1, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile003Terms1
