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
namespace Reinmann.XiRectangle.Tile001Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨1,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/640))
  have he : value ((3/4), (423/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-159311114973/68719476736), (-70196460035/34359738368)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-403300590644341/9007199254740992), (-789665261832341/9007199254740992)), (77463/9007199254740992), by norm_num⟩
  | 1 => ⟨((38043800267/274877906944), (148980032243/549755813888)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((-7349687607/34359738368), (-230251802183/549755813888)), (27/549755813888), by norm_num⟩
  | 3 => ⟨((60581857099/274877906944), (118619682585/274877906944)), (29/549755813888), by norm_num⟩
  | 4 => ⟨((-46815273049/274877906944), (-183329237337/549755813888)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((7235399823/68719476736), (56667845555/274877906944)), (31/1099511627776), by norm_num⟩
  | 6 => ⟨((-59639808053/1099511627776), (-58387572117/549755813888)), (17/1099511627776), by norm_num⟩
  | 7 => ⟨((105342387773/4398046511104), (51565275475/1099511627776)), (1/137438953472), by norm_num⟩
  | 8 => ⟨((-40702224093/4398046511104), (-318780911225/17592186044416)), (13/4398046511104), by norm_num⟩
  | 9 => ⟨((55916578941/17592186044416), (218970073315/35184372088832)), (37/35184372088832), by norm_num⟩
  | 10 => ⟨((-138272415483/140737488355328), (-270738317053/140737488355328)), (3/8796093022208), by norm_num⟩
  | 11 => ⟨((155420329595/562949953421312), (304314047913/562949953421312)), (7/70368744177664), by norm_num⟩
  | 12 => ⟨((-160136945631/2251799813685248), (-313549213751/2251799813685248)), (15/562949953421312), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580955946171239/10141204801825835211973625643008), (-1330608599107/5070602400912917605986812821504)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111149264246605/39614081257132168796771975168), (-3148145712913/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944656788176961/19807040628566084398385987584), (-885235286801/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889061663564531/2475880078570760549798248448), (-940339854445/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770727666992139/154742504910672534362390528), (-3760357810413/154742504910672534362390528)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193639885315839/1208925819614629174706176), (-3524271520267/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314602093166909/151115727451828646838272), (-1541336984493/302231454903657293676544)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943586775465991/37778931862957161709568), (-2503675799691/37778931862957161709568)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648537577660593/2361183241434822606848), (-3753769970101/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620809010848119/590295810358705651712), (-5158601405995/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822674698660283/73786976294838206464), (-6444005503199/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821755543151321/9223372036854775808), (-905458895705/1152921504606846976)), (105/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593002247371815/1152921504606846976), (-3618191371783/576460752303423488)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((37303690009445/4503599627370496), (-6323642792931/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((745169676058061/18014398509481984), (-9469098384327/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((743814055298015/4503599627370496), (-5903887111953/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2224668060955427/4503599627370496), (-5882479420843/1125899906842624)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211132010129163/2251799813685248), (-35081378410113/2251799813685248)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((2170585783288015/2251799813685248), (-69312233347995/2251799813685248)), (529/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2170585783288015/2251799813685248), (-69312233347995/2251799813685248)), (2017979148482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((8164716224155/8796093022208), (-133624798615539/2251799813685248)), (1053/1125899906842624), by norm_num⟩
  | 2 => ⟨((483051818361379/562949953421312), (-248066626501381/2251799813685248)), (4161/2251799813685248), by norm_num⟩
  | 3 => ⟨((1630645794557841/2251799813685248), (-212859125892111/1125899906842624)), (4029/1125899906842624), by norm_num⟩
  | 4 => ⟨((1100350778230101/2251799813685248), (-308284809652929/1125899906842624)), (7359/1125899906842624), by norm_num⟩
  | 5 => ⟨((368866599354253/2251799813685248), (-1205156615278181/4503599627370496)), (44889/4503599627370496), by norm_num⟩
  | 6 => ⟨((-403300590644341/9007199254740992), (-789665261832341/9007199254740992)), (77463/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-159311114973/68719476736), (-70196460035/34359738368)), (1/34359738368), by norm_num⟩, 0, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-161602141371/68719476736), (-142411887083/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-412344634637405/9007199254740992), (-23499512860133/281474976710656)), (4703/562949953421312), by norm_num⟩
  | 1 => ⟨((157825221787/1099511627776), (143911302051/549755813888)), (31/1099511627776), by norm_num⟩
  | 2 => ⟨((-61857508755/274877906944), (-112808263797/274877906944)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((64651286971/274877906944), (29475804887/68719476736)), (29/549755813888), by norm_num⟩
  | 4 => ⟨((-101356868175/549755813888), (-92421215733/274877906944)), (3/68719476736), by norm_num⟩
  | 5 => ⟨((127121549563/1099511627776), (1811163671/8589934592)), (1/34359738368), by norm_num⟩
  | 6 => ⟨((-132862961125/2199023255552), (-60574860955/549755813888)), (35/2199023255552), by norm_num⟩
  | 7 => ⟨((119026013177/4398046511104), (217065287035/4398046511104)), (33/4398046511104), by norm_num⟩
  | 8 => ⟨((-186602687931/17592186044416), (-340303475989/17592186044416)), (27/8796093022208), by norm_num⟩
  | 9 => ⟨((65010183187/17592186044416), (237115462361/35184372088832)), (39/35184372088832), by norm_num⟩
  | 10 => ⟨((-2547988167/2199023255552), (-37173708037/17592186044416)), (51/140737488355328), by norm_num⟩
  | 11 => ⟨((92965261497/281474976710656), (169538831323/281474976710656)), (61/562949953421312), by norm_num⟩
  | 12 => ⟨((-194328026471/2251799813685248), (-354392016659/2251799813685248)), (33/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580912518633377/10141204801825835211973625643008), (-2699487715951/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444584175497087/158456325028528675187087900672), (-3193242891033/633825300114114700748351602688)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((59039237916187/1237940039285380274899124224), (-897913745881/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((118062505076805/154742504910672534362390528), (-953804281559/618970019642690137449562112)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442666522120809/38685626227668133590597632), (-1907093285143/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549061356748727/9671406556917033397649408), (-3574705237063/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629178933347619/302231454903657293676544), (-3126772739405/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887091486402683/75557863725914323419136), (-5078954508563/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297013613660143/4722366482869645213696), (-3807421787661/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620724402046699/590295810358705651712), (-5232290868085/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911284477098139/36893488147419103232), (-6535994746411/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821636603472549/9223372036854775808), (-7346990666945/9223372036854775808)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592883336402451/1152921504606846976), (-7339491982509/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((596807032857603/72057594037927936), (-200425848557/4503599627370496)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((372545848947235/9007199254740992), (-2400900820949/9007199254740992)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((743716640547897/4503599627370496), (-5987540891923/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112139377210025/2251799813685248), (-11931034669689/2251799813685248)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105274473986893/1125899906842624), (-35573472509077/2251799813685248)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((2169423347671671/2251799813685248), (-17568009857133/562949953421312)), (1059/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2169423347671671/2251799813685248), (-17568009857133/562949953421312)), (4039772994231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((260983429417467/281474976710656), (-8462664070883/140737488355328)), (2107/2251799813685248), by norm_num⟩
  | 2 => ⟨((120482972394945/140737488355328), (-251090465465839/2251799813685248)), (2081/1125899906842624), by norm_num⟩
  | 3 => ⟨((101393535713455/140737488355328), (-1679330320323/8796093022208)), (8055/2251799813685248), by norm_num⟩
  | 4 => ⟨((1086697307225461/2251799813685248), (-77431304274959/281474976710656)), (14683/2251799813685248), by norm_num⟩
  | 5 => ⟨((708048905818353/4503599627370496), (-1195763699265531/4503599627370496)), (44501/4503599627370496), by norm_num⟩
  | 6 => ⟨((-412344634637405/9007199254740992), (-23499512860133/281474976710656)), (4703/562949953421312), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-161602141371/68719476736), (-142411887083/68719476736)), (1/34359738368), by norm_num⟩, 0, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-163795647195/68719476736), (-144344914091/68719476736)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-104929520826345/2251799813685248), (-716839115713311/9007199254740992)), (73167/9007199254740992), by norm_num⟩
  | 1 => ⟨((40706990427/274877906944), (278094884941/1099511627776)), (15/549755813888), by norm_num⟩
  | 2 => ⟨((-129369006849/549755813888), (-55237532143/137438953472)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((68523611291/274877906944), (29257975101/68719476736)), (29/549755813888), by norm_num⟩
  | 4 => ⟨((-54442931333/274877906944), (-46491709919/137438953472)), (25/549755813888), by norm_num⟩
  | 5 => ⟨((138418053167/1099511627776), (59101262715/274877906944)), (17/549755813888), by norm_num⟩
  | 6 => ⟨((-18329167669/274877906944), (-250435992467/2199023255552)), (19/1099511627776), by norm_num⟩
  | 7 => ⟨((133145329183/4398046511104), (227399732891/4398046511104)), (9/1099511627776), by norm_num⟩
  | 8 => ⟨((-105785755851/8796093022208), (-90336074017/4398046511104)), (15/4398046511104), by norm_num⟩
  | 9 => ⟨((149419034035/35184372088832), (255193694265/35184372088832)), (11/8796093022208), by norm_num⟩
  | 10 => ⟨((-189944693377/140737488355328), (-40550964877/17592186044416)), (29/70368744177664), by norm_num⟩
  | 11 => ⟨((54877678213/140737488355328), (187451853457/281474976710656)), (35/281474976710656), by norm_num⟩
  | 12 => ⟨((-29067369241/281474976710656), (-198577360295/1125899906842624)), (39/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455775/1267650600228229401496703205376), (-2736129198411/10141204801825835211973625643008)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778287369893615/633825300114114700748351602688), (-1618207888891/316912650057057350374175801344)), (47/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889200118282689/39614081257132168796771975168), (-910051152017/9903520314283042199192993792)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944470560523161/1237940039285380274899124224), (-3866776113235/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885303566008759/77371252455336267181195264), (-966429364071/38685626227668133590597632)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193625761127415/1208925819614629174706176), (-3622985597465/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258309511398291/604462909807314587353088), (-1584494111563/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((471753229125301/18889465931478580854784), (-1286874691045/18889465931478580854784)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296954692777337/4722366482869645213696), (-1929390545495/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810321698250877/295147905179352825856), (-5302830520653/590295810358705651712)), (75/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911233856665721/36893488147419103232), (-1656012580633/18446744073709551616)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821522729692977/9223372036854775808), (-3722944866593/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592769490517465/1152921504606846976), (-7438186958227/1152921504606846976)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193514482156911/144115188075855872), (-6499755972661/144115188075855872)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490034084156139/36028797018963968), (-9732338734077/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((371811688552261/2251799813685248), (-1516900220711/1125899906842624)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223906043271359/4503599627370496), (-24179918425645/4503599627370496)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((552497688507279/562949953421312), (-36044293821625/2251799813685248)), (131/562949953421312), by norm_num⟩
  | 0 => ⟨((2168310547389575/2251799813685248), (-35595010910815/1125899906842624)), (1059/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2168310547389575/2251799813685248), (-35595010910815/1125899906842624)), (4039772994231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1042833066725349/1125899906842624), (-137101063999209/2251799813685248)), (527/562949953421312), by norm_num⟩
  | 2 => ⟨((480860520121581/562949953421312), (-126985997736287/1125899906842624)), (4163/2251799813685248), by norm_num⟩
  | 3 => ⟨((201790121418035/281474976710656), (-216937767020045/1125899906842624)), (2013/562949953421312), by norm_num⟩
  | 4 => ⟨((1073711883618319/2251799813685248), (-155523232859637/562949953421312)), (14649/2251799813685248), by norm_num⟩
  | 5 => ⟨((680218187267727/4503599627370496), (-148314377046549/562949953421312)), (44129/4503599627370496), by norm_num⟩
  | 6 => ⟨((-104929520826345/2251799813685248), (-716839115713311/9007199254740992)), (73167/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-163795647195/68719476736), (-144344914091/68719476736)), (1/34359738368), by norm_num⟩, 0, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-41474899193/17179869184), (-18274877457/8589934592)), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-212834893003029/4503599627370496), (-1367980029977909/18014398509481984)), (17801/2251799813685248), by norm_num⟩
  | 1 => ⟨((167258079047/1099511627776), (4199369285/17179869184)), (15/549755813888), by norm_num⟩
  | 2 => ⟨((-67297873395/274877906944), (-216275972339/549755813888)), (13/274877906944), by norm_num⟩
  | 3 => ⟨((144415665157/549755813888), (232055166287/549755813888)), (15/274877906944), by norm_num⟩
  | 4 => ⟨((-58107011663/274877906944), (-186739191199/549755813888)), (13/274877906944), by norm_num⟩
  | 5 => ⟨((74815702039/549755813888), (120218053621/549755813888)), (35/1099511627776), by norm_num⟩
  | 6 => ⟨((-40137075769/549755813888), (-257977991009/2199023255552)), (39/2199023255552), by norm_num⟩
  | 7 => ⟨((9228304491/274877906944), (118628445515/2199023255552)), (19/2199023255552), by norm_num⟩
  | 8 => ⟨((-59409532461/4398046511104), (-190925117705/8796093022208)), (1/274877906944), by norm_num⟩
  | 9 => ⟨((169983918049/35184372088832), (136569832387/17592186044416)), (3/2199023255552), by norm_num⟩
  | 10 => ⟨((-109431424885/70368744177664), (-175840532751/70368744177664)), (33/70368744177664), by norm_num⟩
  | 11 => ⟨((32022378913/70368744177664), (205821396329/281474976710656)), (5/35184372088832), by norm_num⟩
  | 12 => ⟨((-68717374225/562949953421312), (-220837838961/1125899906842624)), (45/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580831058241955/10141204801825835211973625643008), (-692818671477/2535301200456458802993406410752)), (39/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889120026234527/316912650057057350374175801344), (-819455428327/158456325028528675187087900672)), (23/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889146889662149/39614081257132168796771975168), (-3686766988885/39614081257132168796771975168)), (13/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944442284418993/1237940039285380274899124224), (-489528044941/309485009821345068724781056)), (55/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885275291711507/77371252455336267181195264), (-1957569197695/77371252455336267181195264)), (55/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387238269639901/2417851639229258349412352), (-1834644362949/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258263131102611/604462909807314587353088), (-3209474471909/604462909807314587353088)), (45/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943468777885385/37778931862957161709568), (-5213234593263/75557863725914323419136)), (73/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296898178592253/4722366482869645213696), (-3908035456687/4722366482869645213696)), (55/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810282849936101/295147905179352825856), (-2685239064667/295147905179352825856)), (19/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911185304084449/36893488147419103232), (-6708494210367/73786976294838206464)), (47/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821413507969203/9223372036854775808), (-1885182569195/2305843009213693952)), (53/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796330147962139/576460752303423488), (-1883207297773/288230376151711744)), (53/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193418967616141/144115188075855872), (-3291172569445/72057594037927936)), (93/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489890874315783/36028797018963968), (-9855777688017/36028797018963968)), (139/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487067851510095/9007199254740992), (-6144361909579/4503599627370496)), (87/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223548571265925/4503599627370496), (-12242319810769/2251799813685248)), (87/1125899906842624), by norm_num⟩
  | 1 => ⟨((276181924432433/281474976710656), (-36495592830335/2251799813685248)), (525/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083621661473107/1125899906842624), (-72069635429063/2251799813685248)), (265/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1083621661473107/1125899906842624), (-72069635429063/2251799813685248)), (1010896922874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2083555367573129/2251799813685248), (-69363375563649/1125899906842624)), (2109/2251799813685248), by norm_num⟩
  | 2 => ⟨((959667425140967/1125899906842624), (-64180853284693/562949953421312)), (1041/562949953421312), by norm_num⟩
  | 3 => ⟨((1606687830181543/2251799813685248), (-54704928778079/281474976710656)), (8049/2251799813685248), by norm_num⟩
  | 4 => ⟨((1061336579851139/2251799813685248), (-624522608338563/2251799813685248)), (1827/281474976710656), by norm_num⟩
  | 5 => ⟨((654060669983735/4503599627370496), (-294355068841129/1125899906842624)), (10943/1125899906842624), by norm_num⟩
  | 6 => ⟨((-212834893003029/4503599627370496), (-1367980029977909/18014398509481984)), (17801/2251799813685248), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41474899193/17179869184), (-18274877457/8589934592)), (1/34359738368), by norm_num⟩, 0, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-20990127117/8589934592), (-147980396175/68719476736)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-430406784301191/9007199254740992), (-1306453280498781/18014398509481984)), (17383/4503599627370496), by norm_num⟩
  | 1 => ⟨((171180035873/1099511627776), (259799249895/1099511627776)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((-34857567641/137438953472), (-105806379583/274877906944)), (15/549755813888), by norm_num⟩
  | 3 => ⟨((151425760607/549755813888), (229818266013/549755813888)), (9/274877906944), by norm_num⟩
  | 4 => ⟨((-15417492075/68719476736), (-93596262109/274877906944)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((80370684087/549755813888), (243956526039/1099511627776)), (23/1099511627776), by norm_num⟩
  | 6 => ⟨((-43642574597/549755813888), (-132472318819/1099511627776)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((81252412117/2199023255552), (246632916187/4398046511104)), (27/4398046511104), by norm_num⟩
  | 8 => ⟨((-2068189083/137438953472), (-100444231299/4398046511104)), (3/1099511627776), by norm_num⟩
  | 9 => ⟨((95834448943/17592186044416), (290895113119/35184372088832)), (37/35184372088832), by norm_num⟩
  | 10 => ⟨((-62447577265/35184372088832), (-47388218049/17592186044416)), (13/35184372088832), by norm_num⟩
  | 11 => ⟨((73985540107/140737488355328), (112287555759/140737488355328)), (33/281474976710656), by norm_num⟩
  | 12 => ⟨((-40175338681/281474976710656), (-243895797787/1125899906842624)), (19/562949953421312), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580792741223529/10141204801825835211973625643008), (-1402520779193/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778194591617073/633825300114114700748351602688), (-414699937831/79228162514264337593543950336)), (23/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944547874800831/19807040628566084398385987584), (-466437280731/4951760157141521099596496896)), (27/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888830235638801/2475880078570760549798248448), (-1981863849625/1237940039285380274899124224)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770496253740899/154742504910672534362390528), (-3962615173109/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774451074113661/4835703278458516698824704), (-3713769994609/9671406556917033397649408)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258218570815369/604462909807314587353088), (-3248367384811/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886865152360507/75557863725914323419136), (-164886960467/2361183241434822606848)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296843882227659/4722366482869645213696), (-1977675177191/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620491052469617/590295810358705651712), (-2717730538611/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822277314124805/73786976294838206464), (-6789610432375/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821308573181159/9223372036854775808), (-7631831539257/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796277693774423/576460752303423488), (-7623737568085/1152921504606846976)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193327202705003/144115188075855872), (-6661673279917/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489753287290115/36028797018963968), (-4987168644875/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((743447987229773/4503599627370496), (-3109041995163/2251799813685248)), (87/9007199254740992), by norm_num⟩
  | 2 => ⟨((555801285468991/1125899906842624), (-24777268822327/4503599627370496)), (175/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208941078859933/2251799813685248), (-36928912947537/2251799813685248)), (263/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083109046567289/1125899906842624), (-72913925432757/2251799813685248)), (531/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083109046567289/1125899906842624), (-72913925432757/2251799813685248)), (2025612837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2081528010623043/2251799813685248), (-140285529427601/2251799813685248)), (1057/2251799813685248), by norm_num⟩
  | 2 => ⟨((1915391769298909/2251799813685248), (-129677717003955/1125899906842624)), (2087/2251799813685248), by norm_num⟩
  | 3 => ⟨((1599369698345653/2251799813685248), (-441217963162275/2251799813685248)), (4033/2251799813685248), by norm_num⟩
  | 4 => ⟨((1049520533133651/2251799813685248), (-626761434439099/2251799813685248)), (7311/2251799813685248), by norm_num⟩
  | 5 => ⟨((629419586467771/4503599627370496), (-1168485743399357/4503599627370496)), (21771/4503599627370496), by norm_num⟩
  | 6 => ⟨((-430406784301191/9007199254740992), (-1306453280498781/18014398509481984)), (17383/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-20990127117/8589934592), (-147980396175/68719476736)), (1/68719476736), by norm_num⟩, 0, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-169866138629/68719476736), (-149694534667/68719476736)), (1/68719476736), by norm_num⟩
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
  | 0 => ⟨((-868204720646193/18014398509481984), (-78045403872301/1125899906842624)), (67741/18014398509481984), by norm_num⟩
  | 1 => ⟨((174649726901/1099511627776), (125598105129/549755813888)), (15/1099511627776), by norm_num⟩
  | 2 => ⟨((-143904252139/549755813888), (-12935964537/34359738368)), (7/274877906944), by norm_num⟩
  | 3 => ⟨((158094979791/549755813888), (113692876849/274877906944)), (17/549755813888), by norm_num⟩
  | 4 => ⟨((-130263815681/549755813888), (-46839146865/137438953472)), (1/34359738368), by norm_num⟩
  | 5 => ⟨((171731314411/1099511627776), (15437418701/68719476736)), (23/1099511627776), by norm_num⟩
  | 6 => ⟨((-188666132361/2199023255552), (-67838951561/549755813888)), (27/2199023255552), by norm_num⟩
  | 7 => ⟨((2775949975/68719476736), (255526991435/4398046511104)), (7/1099511627776), by norm_num⟩
  | 8 => ⟨((-146385252253/8796093022208), (-105271909829/4398046511104)), (25/8796093022208), by norm_num⟩
  | 9 => ⟨((214427516007/35184372088832), (77102009193/8796093022208)), (39/35184372088832), by norm_num⟩
  | 10 => ⟨((-35335905617/17592186044416), (-203292515473/70368744177664)), (27/70368744177664), by norm_num⟩
  | 11 => ⟨((169398371529/281474976710656), (60910815189/70368744177664)), (17/140737488355328), by norm_num⟩
  | 12 => ⟨((-93051566321/562949953421312), (-133834740159/562949953421312)), (39/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98797241905021/633825300114114700748351602688), (-1418766950413/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778150847148501/633825300114114700748351602688), (-3355872216939/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889046540393053/39614081257132168796771975168), (-3774536801535/39614081257132168796771975168)), (13/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888777953888873/2475880078570760549798248448), (-4009433167153/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885221987708477/77371252455336267181195264), (-4008294780057/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774426570473213/4835703278458516698824704), (-939141790103/2417851639229258349412352)), (13/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258175693101059/604462909807314587353088), (-3285787452163/604462909807314587353088)), (23/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886795482949047/75557863725914323419136), (-667142362265/9444732965739290427392)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296791636202453/4722366482869645213696), (-2000436244429/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1620419224023629/590295810358705651712), (-2748990479241/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911093771692723/36893488147419103232), (-429228174621/4611686018427387904)), (47/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821207601571811/9223372036854775808), (-7719476544175/9223372036854775808)), (53/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796227220837981/576460752303423488), (-3855597395507/576460752303423488)), (53/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74577431513741/9007199254740992), (-3368993699009/72057594037927936)), (47/144115188075855872), by norm_num⟩
  | 4 => ⟨((744810449184141/18014398509481984), (-5044193659737/18014398509481984)), (35/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486730592335025/9007199254740992), (-12577995210707/9007199254740992)), (11/1125899906842624), by norm_num⟩
  | 2 => ⟨((555718673539457/1125899906842624), (-6264681039643/1125899906842624)), (175/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208446214076629/2251799813685248), (-37345621905527/2251799813685248)), (263/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165231682746483/2251799813685248), (-36862794759771/1125899906842624)), (531/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2165231682746483/2251799813685248), (-36862794759771/1125899906842624)), (2025612837981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((259947218051957/281474976710656), (-141782569912929/2251799813685248)), (1057/2251799813685248), by norm_num⟩
  | 2 => ⟨((1911600343768157/2251799813685248), (-261877521389827/2251799813685248)), (2087/2251799813685248), by norm_num⟩
  | 3 => ⟨((1592342274963191/2251799813685248), (-444626699826097/2251799813685248)), (2015/1125899906842624), by norm_num⟩
  | 4 => ⟨((1038218852416819/2251799813685248), (-628828447722241/2251799813685248)), (1823/562949953421312), by norm_num⟩
  | 5 => ⟨((303078970297991/2251799813685248), (-1159715078389273/4503599627370496)), (21595/4503599627370496), by norm_num⟩
  | 6 => ⟨((-868204720646193/18014398509481984), (-78045403872301/1125899906842624)), (67741/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-169866138629/68719476736), (-149694534667/68719476736)), (1/68719476736), by norm_num⟩, 0, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨1,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile001Terms3
