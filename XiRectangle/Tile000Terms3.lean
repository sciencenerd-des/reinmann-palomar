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
namespace Reinmann.XiRectangle.Tile000Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨0,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (141/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (141/640))
  have he : value ((3/4), (141/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-318622229945/137438953472), (-46797640023/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-424829639927/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((172228049812927/2251799813685248), (-139557912238173/2251799813685248)), (5811/2251799813685248), by norm_num⟩
  | 1 => ⟨((-259943463687/1099511627776), (210634488003/1099511627776)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((6277314701/17179869184), (-40692509035/137438953472)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-206970093161/549755813888), (167709697281/549755813888)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((79969168067/274877906944), (-64799724267/274877906944)), (11/549755813888), by norm_num⟩
  | 5 => ⟨((-49437618691/274877906944), (40059739735/274877906944)), (15/1099511627776), by norm_num⟩
  | 6 => ⟨((101875852111/1099511627776), (-165101808255/2199023255552)), (17/2199023255552), by norm_num⟩
  | 7 => ⟨((-179944333627/4398046511104), (145810485269/4398046511104)), (17/4398046511104), by norm_num⟩
  | 8 => ⟨((278107787241/17592186044416), (-28169150007/2199023255552)), (7/4398046511104), by norm_num⟩
  | 9 => ⟨((-47757943165/8796093022208), (77397367597/17592186044416)), (21/35184372088832), by norm_num⟩
  | 10 => ⟨((236194927693/140737488355328), (-11961927451/8796093022208)), (7/35184372088832), by norm_num⟩
  | 11 => ⟨((-132743372503/281474976710656), (215126257891/562949953421312)), (33/562949953421312), by norm_num⟩
  | 12 => ⟨((1068529687/8796093022208), (-110827399329/1125899906842624)), (9/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98809746635703/633825300114114700748351602688), (-443536199699/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778392947415429/633825300114114700748351602688), (-1049381904297/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944659574335179/19807040628566084398385987584), (-18442450849/618970019642690137449562112)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889067930541417/2475880078570760549798248448), (-1253790171261/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770734323291301/154742504910672534362390528), (-313364190711/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774562868083943/4835703278458516698824704), (-587380795333/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258414607633269/604462909807314587353088), (-1027562404555/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887184456478483/75557863725914323419136), (-834562736363/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81067750674363/295147905179352825856), (-625631945263/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620822284802679/590295810358705651712), (-53735798363/18446744073709551616)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911346467664725/36893488147419103232), (-537004859119/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821778316478183/9223372036854775808), (-2414581231523/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796513918221479/576460752303423488), (-1206078880899/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596871815382529/72057594037927936), (-65872338423/4503599627370496)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490383978677237/36028797018963968), (-3156433788861/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487694877239525/9007199254740992), (-3936042841357/9007199254740992)), (43/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224834372716279/4503599627370496), (-3921829486187/2251799813685248)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((552865706120271/562949953421312), (-5847335616455/1125899906842624)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((271446152253821/281474976710656), (-23107566010131/2251799813685248)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((271446152253821/281474976710656), (-23107566010131/2251799813685248)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046980038019947/1125899906842624), (-44568508040763/2251799813685248)), (1011/2251799813685248), by norm_num⟩
  | 2 => ⟨((1946301985418239/2251799813685248), (-82888963680379/2251799813685248)), (1921/2251799813685248), by norm_num⟩
  | 3 => ⟨((104949960892469/140737488355328), (-71643559787119/1125899906842624)), (3463/2251799813685248), by norm_num⟩
  | 4 => ⟨((9711604228943/17592186044416), (-213702514823109/2251799813685248)), (2803/1125899906842624), by norm_num⟩
  | 5 => ⟨((332976402211951/1125899906842624), (-235945008932033/2251799813685248)), (3627/1125899906842624), by norm_num⟩
  | 6 => ⟨((172228049812927/2251799813685248), (-139557912238173/2251799813685248)), (5811/2251799813685248), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-318622229945/137438953472), (-46797640023/68719476736)), (1/68719476736), by norm_num⟩, 0, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-323204282741/137438953472), (-94941258055/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-430939043655/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((661003783217035/9007199254740992), (-4268962261043/70368744177664)), (5667/2251799813685248), by norm_num⟩
  | 1 => ⟨((-252999699583/1099511627776), (209145413711/1099511627776)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((198319773669/549755813888), (-163943558745/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-207276834415/549755813888), (21418503341/68719476736)), (3/137438953472), by norm_num⟩
  | 4 => ⟨((162478828851/549755813888), (-134315186679/549755813888)), (11/549755813888), by norm_num⟩
  | 5 => ⟨((-203780571229/1099511627776), (168457796377/1099511627776)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((212984267469/2199023255552), (-176066148723/2199023255552)), (9/1099511627776), by norm_num⟩
  | 7 => ⟨((-23850390669/549755813888), (157729825983/4398046511104)), (9/2199023255552), by norm_num⟩
  | 8 => ⟨((299131047961/17592186044416), (-247280478525/17592186044416)), (31/17592186044416), by norm_num⟩
  | 9 => ⟨((-208427482375/35184372088832), (172299224473/35184372088832)), (23/35184372088832), by norm_num⟩
  | 10 => ⟨((261409266171/140737488355328), (-108048644349/70368744177664)), (31/140737488355328), by norm_num⟩
  | 11 => ⟨((-298053542571/562949953421312), (246389745015/562949953421312)), (37/562949953421312), by norm_num⟩
  | 12 => ⟨((155757526461/1125899906842624), (-128758936727/1125899906842624)), (21/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316693/5070602400912917605986812821504), (-899829238647/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889170779086963/316912650057057350374175801344), (-1064414297007/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59039417080675/1237940039285380274899124224), (-1197221603811/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236125816148871/309485009821345068724781056), (-158967862775/309485009821345068724781056)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885336468487973/77371252455336267181195264), (-1271399864343/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549068202467395/9671406556917033397649408), (-595786511181/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629182140805141/302231454903657293676544), (-1042262187321/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471775676653581/18889465931478580854784), (-105812091875/4722366482869645213696)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297022724563417/4722366482869645213696), (-634574072595/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810369029374853/295147905179352825856), (-872054606873/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822587716489421/73786976294838206464), (-1089341642369/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821660032847725/9223372036854775808), (-1224511059311/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592909662179877/1152921504606846976), (-611632205611/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193640351201779/144115188075855872), (-1068955545961/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((372557326215741/9007199254740992), (-1600635849105/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((371875490992219/2251799813685248), (-1995908580043/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112224915222233/2251799813685248), (-1988597878955/1125899906842624)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2210889212236251/2251799813685248), (-11858740661985/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170434741259221/2251799813685248), (-23427652133713/2251799813685248)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170434741259221/2251799813685248), (-23427652133713/2251799813685248)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((130735370062487/140737488355328), (-45162265125095/2251799813685248)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((1942199751276909/2251799813685248), (-41952613429355/1125899906842624)), (961/1125899906842624), by norm_num⟩
  | 3 => ⟨((1672040189311497/2251799813685248), (-144738186534549/2251799813685248)), (3459/2251799813685248), by norm_num⟩
  | 4 => ⟨((616122542325463/1125899906842624), (-214946340561033/2251799813685248)), (5583/2251799813685248), by norm_num⟩
  | 5 => ⟨((1307599379286185/4503599627370496), (-470497546025749/4503599627370496)), (14353/4503599627370496), by norm_num⟩
  | 6 => ⟨((661003783217035/9007199254740992), (-4268962261043/70368744177664)), (5667/2251799813685248), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-323204282741/137438953472), (-94941258055/137438953472)), (1/68719476736), by norm_num⟩, 0, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-327591294391/137438953472), (-96229942727/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-436788392521/137438953472), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((317623638479071/4503599627370496), (-535240585510301/9007199254740992)), (11049/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3850650867/17179869184), (103822228573/549755813888)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((195801211795/549755813888), (-41244078899/137438953472)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-207422263711/549755813888), (87383935283/274877906944)), (13/549755813888), by norm_num⟩
  | 4 => ⟨((82399889961/274877906944), (-138855425119/549755813888)), (3/137438953472), by norm_num⟩
  | 5 => ⟨((-209497028729/1099511627776), (88258003133/549755813888)), (17/1099511627776), by norm_num⟩
  | 6 => ⟨((110965472433/1099511627776), (-186992456611/2199023255552)), (5/549755813888), by norm_num⟩
  | 7 => ⟨((-100758355629/2199023255552), (169792026565/4398046511104)), (5/1099511627776), by norm_num⟩
  | 8 => ⟨((160107739023/8796093022208), (-134902050097/8796093022208)), (17/8796093022208), by norm_num⟩
  | 9 => ⟨((-226147117009/35184372088832), (190544878681/35184372088832)), (13/17592186044416), by norm_num⟩
  | 10 => ⟨((287483084573/140737488355328), (-121112376309/70368744177664)), (35/140737488355328), by norm_num⟩
  | 11 => ⟨((-166115766925/281474976710656), (34991059221/70368744177664)), (11/140737488355328), by norm_num⟩
  | 12 => ⟨((87987474893/562949953421312), (-148271293047/1125899906842624)), (25/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580870939646191/10141204801825835211973625643008), (-456021533067/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778292358804691/633825300114114700748351602688), (-1078805259257/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889206007776885/39614081257132168796771975168), (-1213404947211/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888947744688795/2475880078570760549798248448), (-161116173763/309485009821345068724781056)), (27/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885307083534517/77371252455336267181195264), (-161072125627/19342813113834066795298816)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549013121182569/9671406556917033397649408), (-301916666387/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629158050491917/302231454903657293676544), (-1056334204809/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943512221071887/37778931862957161709568), (-857920955189/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296964051616111/4722366482869645213696), (-643134111725/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405164356177713/147573952589676412928), (-883811467629/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822486985800677/73786976294838206464), (-276004487309/9223372036854775808)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821546795822141/9223372036854775808), (-1240994755323/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796398265658203/576460752303423488), (-2479428441121/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298385370252287/36028797018963968), (-2166622150127/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490081237901421/36028797018963968), (-3244186410859/36028797018963968)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487317296669209/9007199254740992), (-2022597768647/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112040871186403/2251799813685248), (-8060356289731/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105170093543755/1125899906842624), (-12015718547133/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((271168632845701/281474976710656), (-11866897285627/1125899906842624)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((271168632845701/281474976710656), (-11866897285627/1125899906842624)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2089667134049687/2251799813685248), (-45729540162595/2251799813685248)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((1938279554762423/2251799813685248), (-84873900914477/2251799813685248)), (15/17592186044416), by norm_num⟩
  | 3 => ⟨((416302998002391/562949953421312), (-36528412933437/562949953421312)), (3451/2251799813685248), by norm_num⟩
  | 4 => ⟨((1221947778122563/2251799813685248), (-54025718357519/562949953421312)), (5553/2251799813685248), by norm_num⟩
  | 5 => ⟨((642355466841741/2251799813685248), (-234538100970545/2251799813685248)), (7093/2251799813685248), by norm_num⟩
  | 6 => ⟨((317623638479071/4503599627370496), (-535240585510301/9007199254740992)), (11049/4503599627370496), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-327591294391/137438953472), (-96229942727/137438953472)), (1/68719476736), by norm_num⟩, 0, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-41474899193/17179869184), (-6091625819/8589934592)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-221199462363/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((152849875669069/2251799813685248), (-524621535442685/9007199254740992)), (21569/9007199254740992), by norm_num⟩
  | 1 => ⟨((-120118351959/549755813888), (206139108599/1099511627776)), (11/1099511627776), by norm_num⟩
  | 2 => ⟨((96661514811/274877906944), (-165884048307/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-207427608813/549755813888), (177986717609/549755813888)), (7/274877906944), by norm_num⟩
  | 4 => ⟨((166920928855/549755813888), (-143229285615/549755813888)), (13/549755813888), by norm_num⟩
  | 5 => ⟨((-107459548511/549755813888), (5762966061/34359738368)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((230599295235/2199023255552), (-98934784711/1099511627776)), (23/2199023255552), by norm_num⟩
  | 7 => ⟨((-212077284761/4398046511104), (5686764049/137438953472)), (23/4398046511104), by norm_num⟩
  | 8 => ⟨((85331305615/4398046511104), (-18304987319/1099511627776)), (5/2199023255552), by norm_num⟩
  | 9 => ⟨((-244151890443/35184372088832), (13093662479/2199023255552)), (31/35184372088832), by norm_num⟩
  | 10 => ⟨((39294730887/17592186044416), (-16858749445/8796093022208)), (11/35184372088832), by norm_num⟩
  | 11 => ⟨((-183977977159/281474976710656), (157865370257/281474976710656)), (27/281474976710656), by norm_num⟩
  | 12 => ⟨((24675094291/140737488355328), (-5293218999/35184372088832)), (31/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (-230939557159/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444561292592017/158456325028528675187087900672), (-1092607237769/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889152930969735/39614081257132168796771975168), (-614462936983/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236111420399101/309485009821345068724781056), (-163176536915/309485009821345068724781056)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442639449939091/38685626227668133590597632), (-1305050827299/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548960291892225/9671406556917033397649408), (-1223101228479/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258269890415015/604462909807314587353088), (-534914903859/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886949378196651/75557863725914323419136), (-1737754203079/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162113472292981/590295810358705651712), (-1302686651021/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405145022264879/147573952589676412928), (-895086317161/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822390376348383/73786976294838206464), (-2236184604385/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821438192785029/9223372036854775808), (-1256802022833/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796344015719791/576460752303423488), (-1255488562683/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193446659554625/144115188075855872), (-2194153301469/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((93121202331327/2251799813685248), (-102666736857/1125899906842624)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487140200526449/9007199254740992), (-4096374525807/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111864380636047/2251799813685248), (-8161944862643/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209813734183203/2251799813685248), (-6083094202231/1125899906842624)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2168308176783647/2251799813685248), (-12013572522403/1125899906842624)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2168308176783647/2251799813685248), (-12013572522403/1125899906842624)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2087655846331335/2251799813685248), (-23136272926569/1125899906842624)), (253/562949953421312), by norm_num⟩
  | 2 => ⟨((1934526221090881/2251799813685248), (-21449764381329/562949953421312)), (1919/2251799813685248), by norm_num⟩
  | 3 => ⟨((1658686619972341/2251799813685248), (-73710160876143/1125899906842624)), (861/562949953421312), by norm_num⟩
  | 4 => ⟨((606072648070493/1125899906842624), (-108590521109579/1125899906842624)), (2763/1125899906842624), by norm_num⟩
  | 5 => ⟨((1263103944866123/4503599627370496), (-467634781985547/4503599627370496)), (14031/4503599627370496), by norm_num⟩
  | 6 => ⟨((152849875669069/2251799813685248), (-524621535442685/9007199254740992)), (21569/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-6091625819/8589934592)), (1/68719476736), by norm_num⟩, 0, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-20990127117/8589934592), (-49326798725/68719476736)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((36828308550161/562949953421312), (-1029050086193115/18014398509481984)), (42101/18014398509481984), by norm_num⟩
  | 1 => ⟨((-117177914637/549755813888), (51158821461/274877906944)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((95444239503/274877906944), (-166680379091/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-103655515433/274877906944), (181020255357/549755813888)), (13/549755813888), by norm_num⟩
  | 4 => ⟨((168859837989/549755813888), (-73722683411/274877906944)), (13/549755813888), by norm_num⟩
  | 5 => ⟨((-220064661425/1099511627776), (48039123919/274877906944)), (19/1099511627776), by norm_num⟩
  | 6 => ⟨((238997303843/2199023255552), (-208688137773/2199023255552)), (11/1099511627776), by norm_num⟩
  | 7 => ⟨((-222478939499/4398046511104), (48566149943/1099511627776)), (11/2199023255552), by norm_num⟩
  | 8 => ⟨((181214465641/8796093022208), (-79116602497/4398046511104)), (19/8796093022208), by norm_num⟩
  | 9 => ⟨((-262406321397/35184372088832), (229128469951/35184372088832)), (15/17592186044416), by norm_num⟩
  | 10 => ⟨((42747256365/17592186044416), (-74652267471/35184372088832)), (21/70368744177664), by norm_num⟩
  | 11 => ⟨((-50645341081/70368744177664), (22111299473/35184372088832)), (27/281474976710656), by norm_num⟩
  | 12 => ⟨((110004940295/562949953421312), (-96054331019/562949953421312)), (1/35184372088832), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (-935013852795/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889099917497507/316912650057057350374175801344), (-1105866500883/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944550969288065/19807040628566084398385987584), (-621918212049/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944418598021205/1237940039285380274899124224), (-41288965499/77371252455336267181195264)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442625911600641/38685626227668133590597632), (-660438296557/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387227384444375/2417851639229258349412352), (-309482125499/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258225495214119/604462909807314587353088), (-1082794295829/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886877263452417/75557863725914323419136), (-1758803927993/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648426858150089/2361183241434822606848), (-1318458584605/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810252896376621/295147905179352825856), (-452958526391/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911148782218283/36893488147419103232), (-2263224077021/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910666929862825/4611686018427387904), (-2543972138069/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592583798722657/1152921504606846976), (-635320292881/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193355568696731/144115188075855872), (-1110298711263/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((372450706565969/9007199254740992), (-1662429126755/18014398509481984)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486970080266051/9007199254740992), (-1036381868459/2251799813685248)), (43/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223389698762627/4503599627370496), (-8259502541277/4503599627370496)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209308076372215/2251799813685248), (-12310664725645/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167308550654663/2251799813685248), (-12154359349647/1125899906842624)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2167308550654663/2251799813685248), (-12154359349647/1125899906842624)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1042862560737493/1125899906842624), (-46793230528087/2251799813685248)), (1011/2251799813685248), by norm_num⟩
  | 2 => ⟨((1930926385864047/2251799813685248), (-2708883573771/70368744177664)), (479/562949953421312), by norm_num⟩
  | 3 => ⟨((1652439316137479/2251799813685248), (-74332074985195/1125899906842624)), (1717/1125899906842624), by norm_num⟩
  | 4 => ⟨((1202795491664013/2251799813685248), (-109094283078917/1125899906842624)), (2747/1125899906842624), by norm_num⟩
  | 5 => ⟨((1242659969915805/4503599627370496), (-466180380888797/4503599627370496)), (13869/4503599627370496), by norm_num⟩
  | 6 => ⟨((36828308550161/562949953421312), (-1029050086193115/18014398509481984)), (42101/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-49326798725/68719476736)), (1/68719476736), by norm_num⟩, 0, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((-169866138629/68719476736), (-99796356445/137438953472)), (1/68719476736), by norm_num⟩
  | 1 => ⟨((-226488184839/68719476736), 0), (1/137438953472), by norm_num⟩
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
  | 0 => ⟨((142157341480211/2251799813685248), (-252455415691749/4503599627370496)), (41149/18014398509481984), by norm_num⟩
  | 1 => ⟨((-228773147863/1099511627776), (50784415653/274877906944)), (5/549755813888), by norm_num⟩
  | 2 => ⟨((94249871835/274877906944), (-10461071833/34359738368)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-207088134807/549755813888), (91941296547/274877906944)), (13/549755813888), by norm_num⟩
  | 4 => ⟨((85316088651/274877906944), (-75755878667/274877906944)), (3/137438953472), by norm_num⟩
  | 5 => ⟨((-224950328191/1099511627776), (99871607091/549755813888)), (9/549755813888), by norm_num⟩
  | 6 => ⟨((247133194891/2199023255552), (-109720174839/1099511627776)), (11/1099511627776), by norm_num⟩
  | 7 => ⟨((-14544833831/274877906944), (103319942051/2199023255552)), (23/4398046511104), by norm_num⟩
  | 8 => ⟨((23968699775/1099511627776), (-170262837003/8796093022208)), (21/8796093022208), by norm_num⟩
  | 9 => ⟨((-35109744155/4398046511104), (62350948345/8796093022208)), (33/35184372088832), by norm_num⟩
  | 10 => ⟨((185145582627/70368744177664), (-164398843349/70368744177664)), (3/8796093022208), by norm_num⟩
  | 11 => ⟨((-110947206691/140737488355328), (98514867025/140737488355328)), (31/281474976710656), by norm_num⟩
  | 12 => ⟨((15235995583/70368744177664), (-54114821765/281474976710656)), (9/281474976710656), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98797241905021/633825300114114700748351602688), (-236461158403/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889078106351933/316912650057057350374175801344), (-1118624072317/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944526436566807/19807040628566084398385987584), (-629091369271/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472196268988523/618970019642690137449562112), (-334120550931/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442612884936755/38685626227668133590597632), (-167012912429/19342813113834066795298816)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548860702055893/9671406556917033397649408), (-156524300643/1208925819614629174706176)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258182778220777/604462909807314587353088), (-547633916345/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943403937535535/37778931862957161709568), (-1779056321613/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648400849197495/2361183241434822606848), (-1333632925965/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620434306107939/590295810358705651712), (-916337273655/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911104131528657/36893488147419103232), (-2289238251913/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((910616736946861/4611686018427387904), (-2573188129597/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592483510582329/1152921504606846976), (-642608703555/288230376151711744)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596633963181435/72057594037927936), (-2246036848161/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((744835791027945/18014398509481984), (-1681438847363/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((743403204063925/4503599627370496), (-2096404018793/4503599627370496)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111531750646341/2251799813685248), (-1044166922153/562949953421312)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((552205409560913/562949953421312), (-3112400860409/562949953421312)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((270793381649329/281474976710656), (-12289707422349/1125899906842624)), (519/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((270793381649329/281474976710656), (-12289707422349/1125899906842624)), (1979836470793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520967203515683/562949953421312), (-47293318521877/2251799813685248)), (1011/2251799813685248), by norm_num⟩
  | 2 => ⟨((963734109459581/1125899906842624), (-43766355686825/1125899906842624)), (957/1125899906842624), by norm_num⟩
  | 3 => ⟨((1646448204165811/2251799813685248), (-37462592869749/562949953421312)), (1713/1125899906842624), by norm_num⟩
  | 4 => ⟨((298465314148947/562949953421312), (-27391519609751/281474976710656)), (5467/2251799813685248), by norm_num⟩
  | 5 => ⟨((152909440423173/562949953421312), (-464718738461521/4503599627370496)), (13723/4503599627370496), by norm_num⟩
  | 6 => ⟨((142157341480211/2251799813685248), (-252455415691749/4503599627370496)), (41149/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-169866138629/68719476736), (-99796356445/137438953472)), (1/68719476736), by norm_num⟩, 0, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile000Terms3
