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
namespace Reinmann.XiRectangle.Tile000Terms1
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
  | 0 => ⟨((-226488184839/137438953472), (-8316363037/17179869184)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((767136855809427/4503599627370496), (-403362616202859/4503599627370496)), (19673/4503599627370496), by norm_num⟩
  | 1 => ⟨((-205758295137/549755813888), (108188263415/549755813888)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((226048591533/549755813888), (-118856955677/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-331119680659/1099511627776), (87051808067/549755813888)), (9/549755813888), by norm_num⟩
  | 4 => ⟨((22735759387/137438953472), (-95636186093/1099511627776)), (3/274877906944), by norm_num⟩
  | 5 => ⟨((-319715643581/4398046511104), (168107342853/4398046511104)), (23/4398046511104), by norm_num⟩
  | 6 => ⟨((58540589153/2199023255552), (-30780798779/2199023255552)), (19/8796093022208), by norm_num⟩
  | 7 => ⟨((-294004162877/35184372088832), (77294088671/17592186044416)), (13/17592186044416), by norm_num⟩
  | 8 => ⟨((20187286641/8796093022208), (-169832471311/140737488355328)), (31/140737488355328), by norm_num⟩
  | 9 => ⟨((-39427557651/70368744177664), (82924462221/281474976710656)), (33/562949953421312), by norm_num⟩
  | 10 => ⟨((17326239739/140737488355328), (-145762933163/2251799813685248)), (1/70368744177664), by norm_num⟩
  | 11 => ⟨((-221496086035/9007199254740992), (29115809019/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 12 => ⟨((324451096013/72057594037927936), (-85298628221/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395457292338837/2535301200456458802993406410752), (-157640772267/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889713404794373/316912650057057350374175801344), (-746764143781/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890482057819003/39614081257132168796771975168), (-839987574715/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890303293055459/2475880078570760549798248448), (-892336754539/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771969428861321/154742504910672534362390528), (-446084000845/77371252455336267181195264)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550283374704647/9671406556917033397649408), (-836228245587/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259427268494169/604462909807314587353088), (-731520508287/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888829518929495/75557863725914323419136), (-1188384918519/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298317360273299/4722366482869645213696), (-55687179673/295147905179352825856)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811258706847487/295147905179352825856), (-76540043841/36893488147419103232)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912405378502671/36893488147419103232), (-765042671841/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((912079684374011/4611686018427387904), (-1720362712099/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99712938663331/72057594037927936), (-859567212465/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195823313081551/144115188075855872), (-93928871821/9007199254740992)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((746749651215979/18014398509481984), (-2251534451791/36028797018963968)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491581692415033/9007199254740992), (-2809597197175/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2232586024435691/4503599627370496), (-5604757590073/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2223035494999407/2251799813685248), (-8371134512759/2251799813685248)), (129/1125899906842624), by norm_num⟩
  | 0 => ⟨((548624041565571/562949953421312), (-16598801119423/2251799813685248)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((548624041565571/562949953421312), (-16598801119423/2251799813685248)), (1972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2138528422586665/2251799813685248), (-16176395965461/1125899906842624)), (127/281474976710656), by norm_num⟩
  | 2 => ⟨((253811255960539/281474976710656), (-61450724592679/2251799813685248)), (245/281474976710656), by norm_num⟩
  | 3 => ⟨((457313480660923/562949953421312), (-55411268777139/1125899906842624)), (3643/2251799813685248), by norm_num⟩
  | 4 => ⟨((185067976425777/281474976710656), (-90026902172409/1125899906842624)), (3139/1125899906842624), by norm_num⟩
  | 5 => ⟨((479525442694629/1125899906842624), (-236768423305437/2251799813685248)), (9261/2251799813685248), by norm_num⟩
  | 6 => ⟨((767136855809427/4503599627370496), (-403362616202859/4503599627370496)), (19673/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-226488184839/137438953472), (-8316363037/17179869184)), (1/68719476736), by norm_num⟩, 0, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-34860585039/68719476736)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((350004443336069/2251799813685248), (-778135377476471/9007199254740992)), (18499/4503599627370496), by norm_num⟩
  | 1 => ⟨((-196756595143/549755813888), (54679044205/274877906944)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((113262200731/274877906944), (-125903152085/549755813888)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-173863903335/549755813888), (754955003/4294967296)), (9/549755813888), by norm_num⟩
  | 4 => ⟨((100084108007/549755813888), (-55627140345/549755813888)), (3/274877906944), by norm_num⟩
  | 5 => ⟨((-92180870057/1099511627776), (102468979299/2199023255552)), (13/2199023255552), by norm_num⟩
  | 6 => ⟨((141502864835/4398046511104), (-19661962019/1099511627776)), (11/4398046511104), by norm_num⟩
  | 7 => ⟨((-2909128457/274877906944), (1616905023/274877906944)), (1/1099511627776), by norm_num⟩
  | 8 => ⟨((107176253099/35184372088832), (-14892245611/8796093022208)), (5/17592186044416), by norm_num⟩
  | 9 => ⟨((-6855067853/8796093022208), (121922356427/281474976710656)), (23/281474976710656), by norm_num⟩
  | 10 => ⟨((202040026237/1125899906842624), (-28073660041/281474976710656)), (23/1125899906842624), by norm_num⟩
  | 11 => ⟨((-338337710983/9007199254740992), (188049428701/9007199254740992)), (21/4503599627370496), by norm_num⟩
  | 12 => ⟨((129841894951/18014398509481984), (-18041658803/4503599627370496)), (17/18014398509481984), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (-660799621515/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889652443383551/316912650057057350374175801344), (-782470721411/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945172456698067/19807040628566084398385987584), (-220036433963/9903520314283042199192993792)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890157600034883/2475880078570760549798248448), (-934990096357/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((55369492550933/4835703278458516698824704), (-934804808537/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550146839070331/9671406556917033397649408), (-27380709069/302231454903657293676544)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259307827202865/604462909807314587353088), (-383231546485/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944317739085625/37778931862957161709568), (-622566860001/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298171874613497/4722366482869645213696), (-466763852685/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622317443863953/590295810358705651712), (-1283076621045/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((912280452049181/36893488147419103232), (-100191263199/4611686018427387904)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((56996201079829/288230376151711744), (-901181614045/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12461924001709/9007199254740992), (-1801014804425/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149447233888687/18014398509481984), (-787186150315/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493131561343831/36028797018963968), (-1179265224931/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((745561376740545/4503599627370496), (-735717872301/2251799813685248)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231670355464909/4503599627370496), (-5869897932261/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((34713554718209/35184372088832), (-8765337951149/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2191782151077293/2251799813685248), (-8686630309753/1125899906842624)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((2191782151077293/2251799813685248), (-8686630309753/1125899906842624)), (1972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1066615055744003/1125899906842624), (-33820415385441/2251799813685248)), (1015/2251799813685248), by norm_num⟩
  | 2 => ⟨((2020395800911195/2251799813685248), (-64079167290791/2251799813685248)), (1955/2251799813685248), by norm_num⟩
  | 3 => ⟨((905474151804177/1125899906842624), (-114988268258465/2251799813685248)), (905/562949953421312), by norm_num⟩
  | 4 => ⟨((725266836921733/1125899906842624), (-184952328419223/2251799813685248)), (6193/2251799813685248), by norm_num⟩
  | 5 => ⟨((459596932770563/1125899906842624), (-238280133782211/2251799813685248)), (8997/2251799813685248), by norm_num⟩
  | 6 => ⟨((350004443336069/2251799813685248), (-778135377476471/9007199254740992)), (18499/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-34860585039/68719476736)), (1/68719476736), by norm_num⟩, 0, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-123586581311/68719476736), (-9075889565/17179869184)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1287935648387447/9007199254740992), (-751661540438103/9007199254740992)), (17497/4503599627370496), by norm_num⟩
  | 1 => ⟨((-94248498625/274877906944), (3437815961/17179869184)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((225998029321/549755813888), (-65948181133/274877906944)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-45159967181/137438953472), (52712277263/274877906944)), (5/274877906944), by norm_num⟩
  | 4 => ⟨((108288871823/549755813888), (-126398520467/1099511627776)), (7/549755813888), by norm_num⟩
  | 5 => ⟨((-207732299073/2199023255552), (121236165887/2199023255552)), (15/2199023255552), by norm_num⟩
  | 6 => ⟨((332080198637/8796093022208), (-193807752715/8796093022208)), (27/8796093022208), by norm_num⟩
  | 7 => ⟨((-56878109893/4398046511104), (132780198305/17592186044416)), (5/4398046511104), by norm_num⟩
  | 8 => ⟨((68193875419/17592186044416), (-79598252459/35184372088832)), (27/70368744177664), by norm_num⟩
  | 9 => ⟨((-290705371557/281474976710656), (169660687373/281474976710656)), (31/281474976710656), by norm_num⟩
  | 10 => ⟨((139416207247/562949953421312), (-162731424093/1125899906842624)), (1/35184372088832), by norm_num⟩
  | 11 => ⟨((-121565623385/2251799813685248), (70947802285/2251799813685248)), (15/2251799813685248), by norm_num⟩
  | 12 => ⟨((194334422433/18014398509481984), (-113416933143/18014398509481984)), (13/9007199254740992), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122365965/10141204801825835211973625643008), (-344075946101/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889597303331841/316912650057057350374175801344), (-25461350301/19807040628566084398385987584)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890220865972861/39614081257132168796771975168), (-229115930705/9903520314283042199192993792)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118126613831937/154742504910672534362390528), (-486782033091/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((13841343806809/1208925819614629174706176), (-973363158071/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550023345242189/9671406556917033397649408), (-912314552859/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259199795979629/604462909807314587353088), (-399030945045/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888459975938173/75557863725914323419136), (-324112672087/18889465931478580854784)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324510072591685/1180591620717411303424), (-971988254857/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405534146111213/147573952589676412928), (-1335915743529/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824334933160357/73786976294838206464), (-417260741439/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227953044907993/1152921504606846976), (-1876502955655/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594872374338335/1152921504606846976), (-937520533537/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149419488737739/18014398509481984), (-1639017803079/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((93299938627289/2251799813685248), (-2455244174915/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((745353885447209/4503599627370496), (-3063319177721/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115421238298567/2251799813685248), (-6109463727701/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2220430887765327/2251799813685248), (-4560688016811/1125899906842624)), (129/1125899906842624), by norm_num⟩
  | 0 => ⟨((547332417307901/562949953421312), (-18072174137943/2251799813685248)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((547332417307901/562949953421312), (-18072174137943/2251799813685248)), (1972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2128447550253517/2251799813685248), (-17570810152509/1125899906842624)), (507/1125899906842624), by norm_num⟩
  | 2 => ⟨((1005652015151911/1125899906842624), (-33216583106357/1125899906842624)), (975/1125899906842624), by norm_num⟩
  | 3 => ⟨((28039588267521/35184372088832), (-118675997872831/2251799813685248)), (225/140737488355328), by norm_num⟩
  | 4 => ⟨((22247946716553/35184372088832), (-189153645214411/2251799813685248)), (3059/1125899906842624), by norm_num⟩
  | 5 => ⟨((442229066630667/1125899906842624), (-239213035227521/2251799813685248)), (17531/4503599627370496), by norm_num⟩
  | 6 => ⟨((1287935648387447/9007199254740992), (-751661540438103/9007199254740992)), (17497/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-123586581311/68719476736), (-9075889565/17179869184)), (1/68719476736), by norm_num⟩, 0, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-128071113533/68719476736), (-75241779201/137438953472)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1192850923855149/9007199254740992), (-727174289673855/9007199254740992)), (33301/9007199254740992), by norm_num⟩
  | 1 => ⟨((-90457861111/274877906944), (110288099851/549755813888)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((28097417575/68719476736), (-34256954089/137438953472)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-11636576629/34359738368), (113500444023/549755813888)), (5/274877906944), by norm_num⟩
  | 4 => ⟨((231326453169/1099511627776), (-141019004053/1099511627776)), (7/549755813888), by norm_num⟩
  | 5 => ⟨((-57482464175/549755813888), (140167624367/2199023255552)), (1/137438953472), by norm_num⟩
  | 6 => ⟨((95225704983/2199023255552), (-58050576979/2199023255552)), (15/4398046511104), by norm_num⟩
  | 7 => ⟨((-135215421453/8796093022208), (164857445439/17592186044416)), (23/17592186044416), by norm_num⟩
  | 8 => ⟨((167998849961/35184372088832), (-204827681219/70368744177664)), (31/70368744177664), by norm_num⟩
  | 9 => ⟨((-185538426411/140737488355328), (113106148249/140737488355328)), (19/140737488355328), by norm_num⟩
  | 10 => ⟨((23052283479/70368744177664), (-56211643983/281474976710656)), (21/562949953421312), by norm_num⟩
  | 11 => ⟨((-333281585511/4503599627370496), (101585954857/2251799813685248)), (41/4503599627370496), by norm_num⟩
  | 12 => ⟨((276057876029/18014398509481984), (-84143871583/9007199254740992)), (9/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115840927/10141204801825835211973625643008), (-713122558937/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444773484797285/158456325028528675187087900672), (-844237272641/633825300114114700748351602688)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890107631820483/39614081257132168796771975168), (-474805789477/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889905530565529/2475880078570760549798248448), (-504385246369/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221446467453699/19342813113834066795298816), (-1008554775133/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549910618869739/9671406556917033397649408), (-945290965189/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629550592469671/302231454903657293676544), (-826900529441/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888299778988623/75557863725914323419136), (-1343284014947/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297920182883287/4722366482869645213696), (-1007087485595/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621971502001753/590295810358705651712), (-1384135347701/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456032169520677/18446744073709551616), (-864627382053/36893488147419103232)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823392456947841/9223372036854775808), (-121509693031/576460752303423488)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797320320111755/576460752303423488), (-1942585646877/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298788332907869/36028797018963968), (-1697998481273/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492495528425289/36028797018963968), (-1271736976739/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((186291133649757/1125899906842624), (-3173185175607/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((557521762718071/1125899906842624), (-3163967904915/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2219302681863933/2251799813685248), (-9445947507043/2251799813685248)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((2187092919394131/2251799813685248), (-73081441493/8796093022208)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2187092919394131/2251799813685248), (-73081441493/8796093022208)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2124089978142599/2251799813685248), (-36342476784843/2251799813685248)), (1015/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003036607523865/2251799813685248), (-68562658412543/2251799813685248)), (1949/2251799813685248), by norm_num⟩
  | 3 => ⟨((1779667441393737/2251799813685248), (-3811770752079/70368744177664)), (3587/2251799813685248), by norm_num⟩
  | 4 => ⟨((349979811284943/562949953421312), (-192803904085733/2251799813685248)), (6059/2251799813685248), by norm_num⟩
  | 5 => ⟨((853806157988583/2251799813685248), (-479456289546399/4503599627370496)), (17143/4503599627370496), by norm_num⟩
  | 6 => ⟨((1192850923855149/9007199254740992), (-727174289673855/9007199254740992)), (33301/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-128071113533/68719476736), (-75241779201/137438953472)), (1/68719476736), by norm_num⟩, 0, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-66098241637/34359738368), (-19416358481/34359738368)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((17360914765727/140737488355328), (-88063388698909/1125899906842624)), (31727/9007199254740992), by norm_num⟩
  | 1 => ⟨((-86972396823/274877906944), (110292056767/549755813888)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((55769948337/137438953472), (-141446770069/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-190729457537/549755813888), (30233650167/137438953472)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((244605699779/1099511627776), (-155095563139/1099511627776)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((-3921257703/34359738368), (159124906007/2199023255552)), (19/2199023255552), by norm_num⟩
  | 6 => ⟨((214566985083/4398046511104), (-136049108473/4398046511104)), (9/2199023255552), by norm_num⟩
  | 7 => ⟨((-78621921503/4398046511104), (99702592389/8796093022208)), (29/17592186044416), by norm_num⟩
  | 8 => ⟨((201661247041/35184372088832), (-127866050143/35184372088832)), (21/35184372088832), by norm_num⟩
  | 9 => ⟨((-229889282677/140737488355328), (36441104795/35184372088832)), (13/70368744177664), by norm_num⟩
  | 10 => ⟨((58965436789/140737488355328), (-149551341327/562949953421312)), (29/562949953421312), by norm_num⟩
  | 11 => ⟨((-219990340661/2251799813685248), (139487860671/2251799813685248)), (29/2251799813685248), by norm_num⟩
  | 12 => ⟨((94044013821/4503599627370496), (-119259766201/9007199254740992)), (27/9007199254740992), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418255/10141204801825835211973625643008), (-368046672799/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779001342831763/633825300114114700748351602688), (-871345161149/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((236250434605077/4951760157141521099596496896), (-490049010119/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889794885439811/2475880078570760549798248448), (-8133982883/19342813113834066795298816)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442865279120315/38685626227668133590597632), (-1040920005255/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549806933013655/9671406556917033397649408), (-975618408197/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259010483154567/604462909807314587353088), (-426711044475/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472038108084105/18889465931478580854784), (-693176763571/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297809711160561/4722366482869645213696), (-129920639447/590295810358705651712)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((50681864548167/18446744073709551616), (-1428477297933/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227992371962709/9223372036854775808), (-446155641215/18446744073709551616)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911589584920839/4611686018427387904), (-2006361943709/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594427513103177/1152921504606846976), (-2004690221621/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597483512620615/72057594037927936), (-876112541951/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((746108214080117/18014398509481984), (-2624584469465/36028797018963968)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489980821868497/9007199254740992), (-3274172818457/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((34834256827919/70368744177664), (-6528713288639/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((554566362918749/562949953421312), (-4872066060993/1125899906842624)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092518576965479/1125899906842624), (-4823342262193/562949953421312)), (517/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1092518576965479/1125899906842624), (-4823342262193/562949953421312)), (1972207076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120088606880377/2251799813685248), (-2340168514307/140737488355328)), (1013/2251799813685248), by norm_num⟩
  | 2 => ⟨((498864699052591/562949953421312), (-70505231595951/2251799813685248)), (971/1125899906842624), by norm_num⟩
  | 3 => ⟨((55190363663789/70368744177664), (-124958074613869/2251799813685248)), (3565/2251799813685248), by norm_num⟩
  | 4 => ⟨((1378215386581457/2251799813685248), (-196009795577831/2251799813685248)), (5989/2251799813685248), by norm_num⟩
  | 5 => ⟨((1652951386297207/4503599627370496), (-479871637868095/4503599627370496)), (4187/1125899906842624), by norm_num⟩
  | 6 => ⟨((17360914765727/140737488355328), (-88063388698909/1125899906842624)), (31727/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66098241637/34359738368), (-19416358481/34359738368)), (1/68719476736), by norm_num⟩, 0, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-272031958151/137438953472), (-79909387707/137438953472)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((1040007317479483/9007199254740992), (-341744339301633/4503599627370496)), (15203/4503599627370496), by norm_num⟩
  | 1 => ⟨((-167519466189/549755813888), (110093127867/549755813888)), (7/549755813888), by norm_num⟩
  | 2 => ⟨((110523368775/274877906944), (-145271038019/549755813888)), (11/549755813888), by norm_num⟩
  | 3 => ⟨((-194451670973/549755813888), (3993527059/17179869184)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((256584553769/1099511627776), (-168626349697/1099511627776)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((-67714134729/549755813888), (89002920827/1099511627776)), (5/549755813888), by norm_num⟩
  | 6 => ⟨((238268644767/4398046511104), (-39147301761/1099511627776)), (5/1099511627776), by norm_num⟩
  | 7 => ⟨((-179658460969/8796093022208), (118070827025/8796093022208)), (17/8796093022208), by norm_num⟩
  | 8 => ⟨((59266122281/8796093022208), (-155797840737/35184372088832)), (3/4398046511104), by norm_num⟩
  | 9 => ⟨((-139028172803/70368744177664), (713818461/549755813888)), (31/140737488355328), by norm_num⟩
  | 10 => ⟨((293522654767/562949953421312), (-192901922971/562949953421312)), (35/562949953421312), by norm_num⟩
  | 11 => ⟨((-281681132171/2251799813685248), (92559860675/1125899906842624)), (9/562949953421312), by norm_num⟩
  | 12 => ⟨((123895442745/4503599627370496), (-40711796457/2251799813685248)), (17/4503599627370496), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987305/10141204801825835211973625643008), (-757360972187/10141204801825835211973625643008)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778915619464293/633825300114114700748351602688), (-112054792925/79228162514264337593543950336)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((472476763306635/9903520314283042199192993792), (-504159196367/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889692453991585/2475880078570760549798248448), (-267780501097/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771358705999489/154742504910672534362390528), (-133859845463/19342813113834066795298816)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774855472729227/4835703278458516698824704), (-1003690473729/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629463258154575/302231454903657293676544), (-877970882765/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888016027947305/75557863725914323419136), (-1426218587823/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648853722186837/2361183241434822606848), (-534620268905/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621679108005735/590295810358705651712), (-367379512431/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911881683842197/36893488147419103232), (-1835866622533/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822981732994095/9223372036854775808), (-1031966687335/4611686018427387904)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24909847326053/18014398509481984), (-1031082051719/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194794573081625/144115188075855872), (-901202575063/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491958092660583/36028797018963968), (-2699635813549/36028797018963968)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((744829250746747/4503599627370496), (-3367605087657/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228749590059011/4503599627370496), (-6714435729725/4503599627370496)), (43/1125899906842624), by norm_num⟩
  | 1 => ⟨((2217305654737187/2251799813685248), (-2504968307369/562949953421312)), (129/1125899906842624), by norm_num⟩
  | 0 => ⟨((545783846847427/562949953421312), (-9916778452309/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545783846847427/562949953421312), (-9916778452309/1125899906842624)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058195031532199/1125899906842624), (-38457539318663/2251799813685248)), (507/1125899906842624), by norm_num⟩
  | 2 => ⟨((994233121766559/1125899906842624), (-18072466648517/562949953421312)), (1941/2251799813685248), by norm_num⟩
  | 3 => ⟨((438401778974753/562949953421312), (-31918014780489/562949953421312)), (1777/1125899906842624), by norm_num⟩
  | 4 => ⟨((679198422448837/1125899906842624), (-198851274449067/2251799813685248)), (5939/2251799813685248), by norm_num⟩
  | 5 => ⟨((1603783913564471/4503599627370496), (-479827633298225/4503599627370496)), (8215/2251799813685248), by norm_num⟩
  | 6 => ⟨((1040007317479483/9007199254740992), (-341744339301633/4503599627370496)), (15203/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272031958151/137438953472), (-79909387707/137438953472)), (1/68719476736), by norm_num⟩, 0, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-34892961149/17179869184), (-20499614675/34359738368)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((244395571923351/2251799813685248), (-41497287894609/562949953421312)), (7307/2251799813685248), by norm_num⟩
  | 1 => ⟨((-323161854343/1099511627776), (27435727253/137438953472)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((27348078895/68719476736), (-74297326705/274877906944)), (5/274877906944), by norm_num⟩
  | 3 => ⟨((-49373313701/137438953472), (134133927017/549755813888)), (11/549755813888), by norm_num⟩
  | 4 => ⟨((133705412097/549755813888), (-11351294001/68719476736)), (17/1099511627776), by norm_num⟩
  | 5 => ⟨((-144832387247/1099511627776), (98367596807/1099511627776)), (5/549755813888), by norm_num⟩
  | 6 => ⟨((261475583607/4398046511104), (-177589593543/4398046511104)), (5/1099511627776), by norm_num⟩
  | 7 => ⟨((-202311144791/8796093022208), (34351538179/2199023255552)), (9/4398046511104), by norm_num⟩
  | 8 => ⟨((34241796021/4398046511104), (-46512844937/8796093022208)), (27/35184372088832), by norm_num⟩
  | 9 => ⟨((-82425335645/35184372088832), (111963661409/70368744177664)), (9/35184372088832), by norm_num⟩
  | 10 => ⟨((178569557415/281474976710656), (-60640643159/140737488355328)), (21/281474976710656), by norm_num⟩
  | 11 => ⟨((-175845573043/1125899906842624), (29857801073/281474976710656)), (11/562949953421312), by norm_num⟩
  | 12 => ⟨((79366439907/2251799813685248), (-3369017675/140737488355328)), (21/4503599627370496), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798647/10141204801825835211973625643008), (-194290164713/2535301200456458802993406410752)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778835819373423/633825300114114700748351602688), (-229948846691/158456325028528675187087900672)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889817292624365/39614081257132168796771975168), (-517293018701/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889597101182171/2475880078570760549798248448), (-549509973725/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771263373243853/154742504910672534362390528), (-274690963981/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387405398075469/2417851639229258349412352), (-514909549883/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258848353593005/604462909807314587353088), (-900819789495/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((14749133230083/590295810358705651712), (-1463322498869/75557863725914323419136)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648806124207953/2361183241434822606848), (-1097046118579/4722366482869645213696)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101346766892281/36893488147419103232), (-753857213877/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823599905550309/73786976294838206464), (-1883557699539/73786976294838206464)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((455699488734621/2305843009213693952), (-132344444999/576460752303423488)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99627912297943/72057594037927936), (-1057824284775/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((9333078586363/1125899906842624), (-1849099278447/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 4 => ⟨((372929412348383/9007199254740992), (-1384733922673/18014398509481984)), (69/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489358520232437/9007199254740992), (-3454529990973/9007199254740992)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228151342883971/4503599627370496), (-3443596849157/2251799813685248)), (173/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216412561434333/2251799813685248), (-1284536631443/281474976710656)), (259/2251799813685248), by norm_num⟩
  | 0 => ⟨((1090683122652333/1125899906842624), (-10167801265613/1125899906842624)), (259/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1090683122652333/1125899906842624), (-10167801265613/1125899906842624)), (988010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056476053179327/1125899906842624), (-39399059072619/2251799813685248)), (507/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981976501990019/2251799813685248), (-9242420701665/281474976710656)), (485/562949953421312), by norm_num⟩
  | 3 => ⟨((871028543659345/1125899906842624), (-130159070381851/2251799813685248)), (443/281474976710656), by norm_num⟩
  | 4 => ⟨((1340181970676917/2251799813685248), (-201389599252547/2251799813685248)), (2947/1125899906842624), by norm_num⟩
  | 5 => ⟨((24362872050881/70368744177664), (-239718209727003/2251799813685248)), (16141/4503599627370496), by norm_num⟩
  | 6 => ⟨((244395571923351/2251799813685248), (-41497287894609/562949953421312)), (7307/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-34892961149/17179869184), (-20499614675/34359738368)), (1/68719476736), by norm_num⟩, 0, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨0,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile000Terms1
