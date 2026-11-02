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
namespace Reinmann.XiRectangle.Tile015Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨15,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4371/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4371/640))
  have he : value ((3/4), (4371/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4978472343/2147483648), (-90670427545/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53103704991/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-564755446937117/9007199254740992), (-683574339223621/9007199254740992)), (630791/4503599627370496), by norm_num⟩
  | 1 => ⟨((26637009617/137438953472), (16120584889/68719476736)), (121/274877906944), by norm_num⟩
  | 2 => ⟨((-20584031889/68719476736), (-49829412265/137438953472)), (95/137438953472), by norm_num⟩
  | 3 => ⟨((21208705477/68719476736), (51341609579/137438953472)), (25/34359738368), by norm_num⟩
  | 4 => ⟨((-32778504505/137438953472), (-9918693427/34359738368)), (79/137438953472), by norm_num⟩
  | 5 => ⟨((40527899593/274877906944), (6131820493/34359738368)), (99/274877906944), by norm_num⟩
  | 6 => ⟨((-10439454849/137438953472), (-50543246561/549755813888)), (13/68719476736), by norm_num⟩
  | 7 => ⟨((288114269/8589934592), (44637520243/1099511627776)), (47/549755813888), by norm_num⟩
  | 8 => ⟨((-28498349981/2199023255552), (-34494117521/2199023255552)), (147/4398046511104), by norm_num⟩
  | 9 => ⟨((39150937619/8796093022208), (47387902955/8796093022208)), (103/8796093022208), by norm_num⟩
  | 10 => ⟨((-12101721027/8796093022208), (-14647801981/8796093022208)), (129/35184372088832), by norm_num⟩
  | 11 => ⟨((54410085023/140737488355328), (65857422213/140737488355328)), (147/140737488355328), by norm_num⟩
  | 12 => ⟨((-7007661779/70368744177664), (-33928014655/281474976710656)), (77/281474976710656), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790477973085591/5070602400912917605986812821504), (-2945593229829/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444596758149687/158456325028528675187087900672), (-3484554625865/633825300114114700748351602688)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944656082499025/19807040628566084398385987584), (-1959660649393/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472265019067605/618970019642690137449562112), (-2081646429517/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770725981091451/154742504910672534362390528), (-4162183833063/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387279349325005/2417851639229258349412352), (-3900869290405/9671406556917033397649408)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258406793483489/604462909807314587353088), (-853020724653/151115727451828646838272)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471792697197733/18889465931478580854784), (-5542427151067/75557863725914323419136)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297072912422761/4722366482869645213696), (-4154889434487/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620805648846381/590295810358705651712), (-5709836498285/590295810358705651712)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911335039858903/36893488147419103232), (-3566296580301/36893488147419103232)), (1491/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455437443796073/2305843009213693952), (-4008852537187/4611686018427387904)), (839/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796497883127723/576460752303423488), (-2002408191565/288230376151711744)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596855804492391/72057594037927936), (-3499677429767/72057594037927936)), (23/2251799813685248), by norm_num⟩
  | 4 => ⟨((1490328049332661/36028797018963968), (-10480903504469/36028797018963968)), (2211/36028797018963968), by norm_num⟩
  | 3 => ⟨((743805600200697/4503599627370496), (-408420199515/281474976710656)), (2771/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224625939114613/4503599627370496), (-26044013259319/4503599627370496)), (695/562949953421312), by norm_num⟩
  | 1 => ⟨((2211048226240883/2251799813685248), (-4853676768609/281474976710656)), (2097/562949953421312), by norm_num⟩
  | 0 => ⟨((2170336722587899/2251799813685248), (-76715962378861/2251799813685248)), (16971/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2170336722587899/2251799813685248), (-76715962378861/2251799813685248)), (64739235884856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089207096447273/2251799813685248), (-147881236464821/2251799813685248)), (2117/140737488355328), by norm_num⟩
  | 2 => ⟨((1928642770708713/2251799813685248), (-274406745018841/2251799813685248)), (67303/2251799813685248), by norm_num⟩
  | 3 => ⟨((809211336892967/1125899906842624), (-235026480505905/1125899906842624)), (131693/2251799813685248), by norm_num⟩
  | 4 => ⟨((1065077876946515/2251799813685248), (-675676732326139/2251799813685248)), (61071/562949953421312), by norm_num⟩
  | 5 => ⟨((602053373691873/4503599627370496), (-639176124977399/2251799813685248)), (47211/281474976710656), by norm_num⟩
  | 6 => ⟨((-564755446937117/9007199254740992), (-683574339223621/9007199254740992)), (630791/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4978472343/2147483648), (-90670427545/4294967296)), (1/2147483648), by norm_num⟩, -3, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2525033459/1073741824), (-91974343741/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-53867380457/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-718911142850769/9007199254740992), (-467627438745549/9007199254740992)), (1217103/9007199254740992), by norm_num⟩
  | 1 => ⟨((17197736589/68719476736), (11186547313/68719476736)), (119/274877906944), by norm_num⟩
  | 2 => ⟨((-26961701801/68719476736), (-8768838599/34359738368)), (95/137438953472), by norm_num⟩
  | 3 => ⟨((56358840033/137438953472), (18329761805/68719476736)), (101/137438953472), by norm_num⟩
  | 4 => ⟨((-44178204235/137438953472), (-7184107765/34359738368)), (81/137438953472), by norm_num⟩
  | 5 => ⟨((13852050385/68719476736), (18020582675/137438953472)), (103/274877906944), by norm_num⟩
  | 6 => ⟨((-57910698481/549755813888), (-9417238791/137438953472)), (55/274877906944), by norm_num⟩
  | 7 => ⟨((51879617179/1099511627776), (4218242537/137438953472)), (101/1099511627776), by norm_num⟩
  | 8 => ⟨((-81334119795/4398046511104), (-52905100305/4398046511104)), (5/137438953472), by norm_num⟩
  | 9 => ⟨((28335851353/4398046511104), (18431515111/4398046511104)), (113/8796093022208), by norm_num⟩
  | 10 => ⟨((-71077518417/35184372088832), (-46233527217/35184372088832)), (9/2199023255552), by norm_num⟩
  | 11 => ⟨((20260286171/35184372088832), (6589316235/17592186044416)), (167/140737488355328), by norm_num⟩
  | 12 => ⟨((-21175336701/140737488355328), (-13773841961/140737488355328)), (89/281474976710656), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (-3341055246471/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778333796604915/633825300114114700748351602688), (-247009850501/39614081257132168796771975168)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944626091595921/19807040628566084398385987584), (-4445250115509/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472249055881553/618970019642690137449562112), (-4721943342309/2475880078570760549798248448)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442665497788013/38685626227668133590597632), (-4720666793649/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549057261079693/9671406556917033397649408), (-4424269083179/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629177014385489/302231454903657293676544), (-967469936421/151115727451828646838272)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235885596695607/9444732965739290427392), (-3143006677335/37778931862957161709568)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297008162787061/4722366482869645213696), (-4712287147423/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810358115761363/295147905179352825856), (-3237891998389/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822557729122353/73786976294838206464), (-2022329019613/18446744073709551616)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1821622586215953/9223372036854775808), (-9093040236979/9223372036854775808)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398216896585537/288230376151711744), (-567734092337/72057594037927936)), (841/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193598339824689/144115188075855872), (-3968914250009/72057594037927936)), (737/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490155929802273/36028797018963968), (-11885864701661/36028797018963968)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((185924023826073/1125899906842624), (-14820838271085/9007199254740992)), (347/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112088203624411/2251799813685248), (-7383093684827/1125899906842624)), (2787/2251799813685248), by norm_num⟩
  | 1 => ⟨((276293173507543/281474976710656), (-11006481025317/562949953421312)), (4207/1125899906842624), by norm_num⟩
  | 0 => ⟨((1084409160550311/1125899906842624), (-10870624835403/281474976710656)), (8525/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1084409160550311/1125899906842624), (-10870624835403/281474976710656)), (32520298484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((521384046930445/562949953421312), (-83760235386995/1125899906842624)), (17081/1125899906842624), by norm_num⟩
  | 2 => ⟨((1919086259757899/2251799813685248), (-155151449014277/1125899906842624)), (68363/2251799813685248), by norm_num⟩
  | 3 => ⟨((796386109029133/1125899906842624), (-528908497416629/2251799813685248)), (67683/1125899906842624), by norm_num⟩
  | 4 => ⟨((1002388900763199/2251799813685248), (-748228821638851/2251799813685248)), (255089/2251799813685248), by norm_num⟩
  | 5 => ⟨((1543685800167/17592186044416), (-1332296523844987/4503599627370496)), (793257/4503599627370496), by norm_num⟩
  | 6 => ⟨((-718911142850769/9007199254740992), (-467627438745549/9007199254740992)), (1217103/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-91974343741/4294967296)), (1/2147483648), by norm_num⟩, -3, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5118613975/2147483648), (-93222757017/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-54598549065/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1593850755362101/18014398509481984), (-468749526198055/18014398509481984)), (2269301/18014398509481984), by norm_num⟩
  | 1 => ⟨((38645503983/137438953472), (5682797345/68719476736)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((-61408745979/137438953472), (-18060235869/137438953472)), (91/137438953472), by norm_num⟩
  | 3 => ⟨((32526716729/68719476736), (19132133927/137438953472)), (49/68719476736), by norm_num⟩
  | 4 => ⟨((-103371656689/274877906944), (-30401475755/274877906944)), (79/137438953472), by norm_num⟩
  | 5 => ⟨((32852068949/137438953472), (9661752647/137438953472)), (51/137438953472), by norm_num⟩
  | 6 => ⟨((-17400940593/137438953472), (-20470380005/549755813888)), (109/549755813888), by norm_num⟩
  | 7 => ⟨((31600643373/549755813888), (18587419881/1099511627776)), (101/1099511627776), by norm_num⟩
  | 8 => ⟨((-100428545713/4398046511104), (-29535910475/4398046511104)), (163/4398046511104), by norm_num⟩
  | 9 => ⟨((17731518021/2199023255552), (1303704353/549755813888)), (117/8796093022208), by norm_num⟩
  | 10 => ⟨((-90162750023/35184372088832), (-26516752721/35184372088832)), (151/35184372088832), by norm_num⟩
  | 11 => ⟨((52098558739/70368744177664), (30644242747/140737488355328)), (177/140737488355328), by norm_num⟩
  | 12 => ⟨((-55190674719/281474976710656), (-2028938605/35184372088832)), (95/281474976710656), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790435469823053/5070602400912917605986812821504), (-1859841949281/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889141304795499/316912650057057350374175801344), (-549976023823/79228162514264337593543950336)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944597249332333/19807040628566084398385987584), (-1237183367893/9903520314283042199192993792)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59029212529873/77371252455336267181195264), (-2628374066297/1237940039285380274899124224)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221325052422043/19342813113834066795298816), (-5255306973019/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548999379139163/9671406556917033397649408), (-2462659675139/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629151611909157/302231454903657293676544), (-4308123825927/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887001919099539/75557863725914323419136), (-1749458009029/18889465931478580854784)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648472881441575/2361183241434822606848), (-5245864198429/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620630011271797/590295810358705651712), (-3604493061647/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822449324250503/73786976294838206464), (-4502559622323/36893488147419103232)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910749883371463/4611686018427387904), (-10122356976271/9223372036854775808)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398185922338009/288230376151711744), (-10111859909193/1152921504606846976)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((596744360574225/72057594037927936), (-8836075996231/144115188075855872)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((744994546324463/18014398509481984), (-6615265303357/18014398509481984)), (1109/18014398509481984), by norm_num⟩
  | 3 => ⟨((185897430903051/1125899906842624), (-1031058510855/562949953421312)), (695/2251799813685248), by norm_num⟩
  | 2 => ⟨((555934601425155/1125899906842624), (-8217591687051/1125899906842624)), (2793/2251799813685248), by norm_num⟩
  | 1 => ⟨((1104828682127841/1125899906842624), (-24498701084781/1125899906842624)), (1055/281474976710656), by norm_num⟩
  | 0 => ⟨((270914971845685/281474976710656), (-12095739841245/281474976710656)), (2141/281474976710656), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((270914971845685/281474976710656), (-12095739841245/281474976710656)), (8167267919444949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1040925426534631/1125899906842624), (-93135583328593/1125899906842624)), (17223/1125899906842624), by norm_num⟩
  | 2 => ⟨((119332489081841/140737488355328), (-172212816099679/1125899906842624)), (34697/1125899906842624), by norm_num⟩
  | 3 => ⟨((391561580848499/562949953421312), (-73010340873367/281474976710656)), (138909/2251799813685248), by norm_num⟩
  | 4 => ⟨((468952635297607/1125899906842624), (-101565136712137/281474976710656)), (66325/562949953421312), by norm_num⟩
  | 5 => ⟨((194933641590783/4503599627370496), (-676852188739735/2251799813685248)), (103115/562949953421312), by norm_num⟩
  | 6 => ⟨((-1593850755362101/18014398509481984), (-468749526198055/18014398509481984)), (2269301/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5118613975/2147483648), (-93222757017/4294967296)), (1/2147483648), by norm_num⟩, -3, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5184362399/2147483648), (-94420200195/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-55299865591/17179869184), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-805607321608345/9007199254740992), (-11653457792869/18014398509481984)), (2041345/18014398509481984), by norm_num⟩
  | 1 => ⟨((19784163909/68719476736), (572372949/274877906944)), (51/137438953472), by norm_num⟩
  | 2 => ⟨((-31841383461/68719476736), (-230299681/68719476736)), (83/137438953472), by norm_num⟩
  | 3 => ⟨((68328972969/137438953472), (247102025/68719476736)), (91/137438953472), by norm_num⟩
  | 4 => ⟨((-54985619807/137438953472), (-795390735/274877906944)), (149/274877906944), by norm_num⟩
  | 5 => ⟨((70796752925/274877906944), (256026401/137438953472)), (49/137438953472), by norm_num⟩
  | 6 => ⟨((-37980992745/274877906944), (-274705731/274877906944)), (107/549755813888), by norm_num⟩
  | 7 => ⟨((69860628201/1099511627776), (252641039/549755813888)), (25/274877906944), by norm_num⟩
  | 8 => ⟨((-56218171807/2199023255552), (-813220133/4398046511104)), (163/4398046511104), by norm_num⟩
  | 9 => ⟨((20106590461/2199023255552), (145425257/2199023255552)), (59/4398046511104), by norm_num⟩
  | 10 => ⟨((-103552988729/35184372088832), (-748969351/35184372088832)), (77/17592186044416), by norm_num⟩
  | 11 => ⟨((121208804369/140737488355328), (438334425/70368744177664)), (91/70368744177664), by norm_num⟩
  | 12 => ⟨((-130052030049/562949953421312), (-940629389/562949953421312)), (197/562949953421312), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058242031/10141204801825835211973625643008), (-2041426968103/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889116656452023/316912650057057350374175801344), (-4829137779961/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889138934095789/39614081257132168796771975168), (-5431606624929/39614081257132168796771975168)), (51/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888875621672495/2475880078570760549798248448), (-2884828554463/1237940039285380274899124224)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221317635072587/19342813113834066795298816), (-1442013539233/38685626227668133590597632)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548943579677589/9671406556917033397649408), (-2702923958355/4835703278458516698824704)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314563557526827/151115727451828646838272), (-2364207193519/302231454903657293676544)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((943460993719693/37778931862957161709568), (-3840240893431/37778931862957161709568)), (579/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296885537204799/4722366482869645213696), (-5757569368221/4722366482869645213696)), (869/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810273375789131/295147905179352825856), (-7912122186495/590295810358705651712)), (1195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911172288328963/36893488147419103232), (-617709462345/4611686018427387904)), (1495/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821381002150899/9223372036854775808), (-5554711037969/4611686018427387904)), (421/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398155943251623/288230376151711744), (-11097742161089/1152921504606846976)), (843/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193382502310827/144115188075855872), (-4848695957315/72057594037927936)), (739/72057594037927936), by norm_num⟩
  | 4 => ⟨((372456797382359/9007199254740992), (-7259920763225/18014398509481984)), (2221/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486972583001005/9007199254740992), (-9051956386051/4503599627370496)), (2785/9007199254740992), by norm_num⟩
  | 2 => ⟨((555827825968489/1125899906842624), (-2254395407589/281474976710656)), (2799/2251799813685248), by norm_num⟩
  | 1 => ⟨((138061472903085/140737488355328), (-26881166928563/1125899906842624)), (529/140737488355328), by norm_num⟩
  | 0 => ⟨((541460330914593/562949953421312), (-53077805974183/1125899906842624)), (1075/140737488355328), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((541460330914593/562949953421312), (-53077805974183/1125899906842624)), (4100800097417787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((519539925005543/562949953421312), (-102103308517349/1125899906842624)), (17355/1125899906842624), by norm_num⟩
  | 2 => ⟨((237423824842347/281474976710656), (-188459897465241/1125899906842624)), (17591/562949953421312), by norm_num⟩
  | 3 => ⟨((384760680512609/562949953421312), (-635862842352623/2251799813685248)), (142261/2251799813685248), by norm_num⟩
  | 4 => ⟨((109042272212293/281474976710656), (-869189235914821/2251799813685248)), (274807/2251799813685248), by norm_num⟩
  | 5 => ⟨((608842802827/562949953421312), (-1346881635791687/4503599627370496)), (850137/4503599627370496), by norm_num⟩
  | 6 => ⟨((-805607321608345/9007199254740992), (-11653457792869/18014398509481984)), (2041345/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5184362399/2147483648), (-94420200195/4294967296)), (1/2147483648), by norm_num⟩, -3, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5247531779/2147483648), (-47785336265/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1511711758601455/18014398509481984), (403172089177907/18014398509481984)), (531911/4503599627370496), by norm_num⟩
  | 1 => ⟨((37577078607/137438953472), (-20043542297/274877906944)), (107/274877906944), by norm_num⟩
  | 2 => ⟨((-61214874859/137438953472), (8162974471/68719476736)), (89/137438953472), by norm_num⟩
  | 3 => ⟨((66481323951/137438953472), (-17730505909/137438953472)), (49/68719476736), by norm_num⟩
  | 4 => ⟨((-13537660713/34359738368), (3610481245/34359738368)), (81/137438953472), by norm_num⟩
  | 5 => ⟨((70571208803/274877906944), (-2352659289/34359738368)), (107/274877906944), by norm_num⟩
  | 6 => ⟨((-76642603695/549755813888), (20440509559/549755813888)), (59/274877906944), by norm_num⟩
  | 7 => ⟨((71345429075/1099511627776), (-19027758123/1099511627776)), (7/68719476736), by norm_num⟩
  | 8 => ⟨((-14528143467/549755813888), (15498568217/2199023255552)), (93/2199023255552), by norm_num⟩
  | 9 => ⟨((84149500327/8796093022208), (-5610647939/2199023255552)), (137/8796093022208), by norm_num⟩
  | 10 => ⟨((-27416719569/8796093022208), (14624026101/17592186044416)), (91/17592186044416), by norm_num⟩
  | 11 => ⟨((32482297859/35184372088832), (-17325995931/70368744177664)), (55/35184372088832), by norm_num⟩
  | 12 => ⟨((-17638410367/70368744177664), (294009205/4398046511104)), (121/281474976710656), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((6174971645405/39614081257132168796771975168), (1876386049397/5070602400912917605986812821504)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889094966113789/316912650057057350374175801344), (4438506378379/633825300114114700748351602688)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944545124966373/19807040628566084398385987584), (4992234675041/39614081257132168796771975168)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944412025247153/1237940039285380274899124224), (331432776769/154742504910672534362390528)), (867/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770489684487743/154742504910672534362390528), (2650717046745/77371252455336267181195264)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548895581744153/9671406556917033397649408), (4968511303651/9671406556917033397649408)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258212417679565/604462909807314587353088), (4345864592955/604462909807314587353088)), (89/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((471713597563765/18889465931478580854784), (3529531492867/37778931862957161709568)), (1157/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324208785882325/1180591620717411303424), (41341421109/36893488147419103232)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810238977032059/295147905179352825856), (3635937066541/295147905179352825856)), (597/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455564829869273/18446744073709551616), (9083521216377/73786976294838206464)), (747/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821286103346473/9223372036854775808), (10210273477235/9223372036854775808)), (841/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592530141238801/1152921504606846976), (1274927471397/144115188075855872)), (421/288230376151711744), by norm_num⟩
  | 5 => ⟨((1193301996676291/144115188075855872), (4456145177151/72057594037927936)), (369/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489709267273463/36028797018963968), (6672026422537/18014398509481984)), (2219/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486830125253181/9007199254740992), (2079680515015/1125899906842624)), (2781/9007199254740992), by norm_num⟩
  | 2 => ⟨((555760287651575/1125899906842624), (16573606881401/2251799813685248)), (1397/1125899906842624), by norm_num⟩
  | 1 => ⟨((1104307493541195/1125899906842624), (12350576330463/562949953421312)), (4221/1125899906842624), by norm_num⟩
  | 0 => ⟨((1082624620130567/1125899906842624), (48767292090333/1125899906842624)), (8567/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1082624620130567/1125899906842624), (48767292090333/1125899906842624)), (32680515769576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((519450180351835/562949953421312), (93785727760031/1125899906842624)), (8609/562949953421312), by norm_num⟩
  | 2 => ⟨((950811160239639/1125899906842624), (346155198367457/2251799813685248)), (8661/281474976710656), by norm_num⟩
  | 3 => ⟨((388172164232723/562949953421312), (584649174908847/2251799813685248)), (69165/1125899906842624), by norm_num⟩
  | 4 => ⟨((918832746617087/2251799813685248), (25195904867075/70368744177664)), (131299/1125899906842624), by norm_num⟩
  | 5 => ⟨((43117506732917/1125899906842624), (1315971898777511/4503599627370496)), (804705/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1511711758601455/18014398509481984), (403172089177907/18014398509481984)), (531911/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5247531779/2147483648), (-47785336265/2147483648)), (1/2147483648), by norm_num⟩, -4, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-165884901/67108864), (-48338860153/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/34359738368), by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1321071913922255/18014398509481984), (23549030722613/562949953421312)), (1076039/9007199254740992), by norm_num⟩
  | 1 => ⟨((66437340035/274877906944), (-37897345515/274877906944)), (55/137438953472), by norm_num⟩
  | 2 => ⟨((-27370829321/68719476736), (15612933559/68719476736)), (23/34359738368), by norm_num⟩
  | 3 => ⟨((30069929443/68719476736), (-8576280335/34359738368)), (103/137438953472), by norm_num⟩
  | 4 => ⟨((-1548524719/4294967296), (28266020901/137438953472)), (87/137438953472), by norm_num⟩
  | 5 => ⟨((65327166167/274877906944), (-4658009687/34359738368)), (117/274877906944), by norm_num⟩
  | 6 => ⟨((-71769227535/549755813888), (40938773463/549755813888)), (65/274877906944), by norm_num⟩
  | 7 => ⟨((33791380851/549755813888), (-38550719665/1099511627776)), (125/1099511627776), by norm_num⟩
  | 8 => ⟨((-55685439381/2199023255552), (31764220771/2199023255552)), (105/2199023255552), by norm_num⟩
  | 9 => ⟨((81568944005/8796093022208), (-46528751039/8796093022208)), (39/2199023255552), by norm_num⟩
  | 10 => ⟨((-53767586555/17592186044416), (30670234601/17592186044416)), (13/2199023255552), by norm_num⟩
  | 11 => ⟨((4027481681/4398046511104), (-9189462717/17592186044416)), (63/35184372088832), by norm_num⟩
  | 12 => ⟨((-35397126937/140737488355328), (40382626669/281474976710656)), (141/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (3417017893609/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778148129941629/633825300114114700748351602688), (2020605887847/316912650057057350374175801344)), (725/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889043333387433/39614081257132168796771975168), (2272684748517/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888774347172517/2475880078570760549798248448), (37720589015/19342813113834066795298816)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770440144733169/154742504910672534362390528), (4826863503319/154742504910672534362390528)), (867/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774424655948003/4835703278458516698824704), (1130931811945/2417851639229258349412352)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258172105101139/604462909807314587353088), (3956804445279/604462909807314587353088)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886789207417535/75557863725914323419136), (6427076371531/75557863725914323419136)), (289/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296786540583239/4722366482869645213696), (4817918612139/4722366482869645213696)), (217/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620411586279679/590295810358705651712), (51724672369/4611686018427387904)), (1193/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911088525360023/36893488147419103232), (8270130257299/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227649312447429/1152921504606846976), (9295902144287/9223372036854775808)), (1681/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592439720948353/1152921504606846976), (4642957892415/576460752303423488)), (1683/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193224207236541/144115188075855872), (2028487695423/36028797018963968)), (1475/144115188075855872), by norm_num⟩
  | 4 => ⟨((372398808002239/9007199254740992), (1518562241125/4503599627370496)), (2215/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486692199361039/9007199254740992), (15146424337573/9007199254740992)), (2777/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111389541994847/2251799813685248), (7543864984895/1125899906842624)), (697/562949953421312), by norm_num⟩
  | 1 => ⟨((1104128053849377/1125899906842624), (2810652350145/140737488355328)), (2105/562949953421312), by norm_num⟩
  | 0 => ⟨((270583364189525/281474976710656), (44387092882085/1125899906842624)), (8533/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270583364189525/281474976710656), (44387092882085/1125899906842624)), (32550816062545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1038702899339419/1125899906842624), (85339088106391/1125899906842624)), (17079/1125899906842624), by norm_num⟩
  | 2 => ⟨((1903581209350031/2251799813685248), (157459748782945/1125899906842624)), (17051/562949953421312), by norm_num⟩
  | 3 => ⟨((195646117675717/281474976710656), (532440614286483/2251799813685248)), (16799/281474976710656), by norm_num⟩
  | 4 => ⟨((60125815642947/140737488355328), (46260745935289/140737488355328)), (250381/2251799813685248), by norm_num⟩
  | 5 => ⟨((167694576275641/2251799813685248), (632431938722765/2251799813685248)), (757075/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1321071913922255/18014398509481984), (23549030722613/562949953421312)), (1076039/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-48338860153/2147483648)), (1/2147483648), by norm_num⟩, -4, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨15,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile015Terms3
