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
namespace Reinmann.XiRectangle.Tile036Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨36,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8601/640))
  have he : value ((7/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2772588722239781/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log16 : Sound J_log16 F_log16 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log16_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog16 : Sound J_negLog16 F_negLog16 c := by
  apply sound_round (sound_scale (A_log16 hcre) S_log16)
  intro k
  fin_cases k <;> norm_num [J_negLog16, J_log16, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/4194304), (-312567865/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg16 : Sound J_arg16 F_arg16 c := by
  apply sound_round (sound_mul (A_negLog16 hcre) (A_variable hcre) S_negLog16 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg16, J_negLog16, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term16 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((360468965551493/4503599627370496), (675496235846011/18014398509481984)), (36072569/4503599627370496), by norm_num⟩
  | 1 => ⟨((-953132809/4294967296), (-223263889/2147483648)), (97/4294967296), by norm_num⟩
  | 2 => ⟨((1321322639/4294967296), (619018941/4294967296)), (137/4294967296), by norm_num⟩
  | 3 => ⟨((-152645177/536870912), (-286047489/2147483648)), (129/4294967296), by norm_num⟩
  | 4 => ⟨((846444593/4294967296), (396546021/4294967296)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((-938737093/8589934592), (-219891805/4294967296)), (103/8589934592), by norm_num⟩
  | 6 => ⟨((216894323/4294967296), (406446359/17179869184)), (97/17179869184), by norm_num⟩
  | 7 => ⟨((-1374534295/68719476736), (-321973883/34359738368)), (39/17179869184), by norm_num⟩
  | 8 => ⟨((952754571/137438953472), (223175289/68719476736)), (55/68719476736), by norm_num⟩
  | 9 => ⟨((-293510731/137438953472), (-275010351/274877906944)), (69/274877906944), by norm_num⟩
  | 10 => ⟨((325513817/549755813888), (304996239/1099511627776)), (155/2199023255552), by norm_num⟩
  | 11 => ⟨((-1312750455/8796093022208), (-307501503/4398046511104)), (159/8796093022208), by norm_num⟩
  | 12 => ⟨((303309759/8796093022208), (284191733/17592186044416)), (149/35184372088832), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (570698549039/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444556823990907/158456325028528675187087900672), (168750094969/158456325028528675187087900672)), (92267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944566424251347/19807040628566084398385987584), (759215923513/39614081257132168796771975168)), (103805/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944435029990691/1237940039285380274899124224), (806467379117/2475880078570760549798248448)), (55149/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885268267609647/77371252455336267181195264), (201560749731/38685626227668133590597632)), (110303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548940397452309/9671406556917033397649408), (188903623741/2417851639229258349412352)), (103415/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258252523812241/604462909807314587353088), (660924464961/604462909807314587353088)), (45247/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943460617167837/37778931862957161709568), (1073555805549/75557863725914323419136)), (18383/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296886737641383/4722366482869645213696), (100597052409/590295810358705651712)), (27577/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810275633578869/295147905179352825856), (1105933511199/590295810358705651712)), (151689/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911177256174445/36893488147419103232), (1381466475505/73786976294838206464)), (47409/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910699035037719/4611686018427387904), (1552844077725/9223372036854775808)), (213373/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592648188561215/1152921504606846976), (193901701141/144115188075855872)), (106707/576460752303423488), by norm_num⟩
  | 5 => ⟨((298353027779285/36028797018963968), (338869979551/36028797018963968)), (5837/4503599627370496), by norm_num⟩
  | 4 => ⟨((1489888040988147/36028797018963968), (2029561608519/36028797018963968)), (280269/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487077297152551/9007199254740992), (316320358549/1125899906842624)), (350501/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223606214293341/4503599627370496), (2521004758499/2251799813685248)), (701497/4503599627370496), by norm_num⟩
  | 1 => ⟨((1104819003182567/1125899906842624), (7515402476751/2251799813685248)), (1053493/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167988752859639/2251799813685248), (7420713241261/1125899906842624)), (66001/70368744177664), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167988752859639/2251799813685248), (7420713241261/1125899906842624)), (251773834496951081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((521799821638453/562949953421312), (7144517353397/562949953421312)), (4094687/2251799813685248), by norm_num⟩
  | 2 => ⟨((1934267926157733/2251799813685248), (26489089184845/1125899906842624)), (7694687/2251799813685248), by norm_num⟩
  | 3 => ⟨((1660265579585725/2251799813685248), (22753796892595/562949953421312)), (13581347/2251799813685248), by norm_num⟩
  | 4 => ⟨((1220445091826795/2251799813685248), (134212093121491/2251799813685248)), (1320319/140737488355328), by norm_num⟩
  | 5 => ⟨((1306930862398359/4503599627370496), (290964568552575/4503599627370496)), (12708623/1125899906842624), by norm_num⟩
  | 6 => ⟨((360468965551493/4503599627370496), (675496235846011/18014398509481984)), (36072569/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-312567865/8388608)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term16Value_checks : CertifiedScalarExp.Checks term16Value := by
  constructor
  · norm_num [term16Value, CertifiedScalarExp.reduced, term16ValuePoly, term16ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term16ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value, term16ValueSquares, term16ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term16Value, CertifiedScalarExp.roundingCheck, term16ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term16 : Sound J_term16 F_term16 c := by
  apply exp_sound (A_arg16 hcre) S_arg16 term16Value term16Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term16Value,J_arg16]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term16,J_arg16,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((354151668007027/125000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log17 : Sound J_log17 F_log17 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log17_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog17 : Sound J_negLog17 F_negLog17 c := by
  apply sound_round (sound_scale (A_log17 hcre) S_log17)
  intro k
  fin_cases k <;> norm_num [J_negLog17, J_log17, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41591753/16777216), (-638804767/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg17 : Sound J_arg17 F_arg17 c := by
  apply sound_round (sound_mul (A_negLog17 hcre) (A_variable hcre) S_negLog17 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg17, J_negLog17, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term17 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1404169095163349/18014398509481984), (-555346144982303/18014398509481984)), (130646927/18014398509481984), by norm_num⟩
  | 1 => ⟨((-948503165/4294967296), (93782789/1073741824)), (45/2147483648), by norm_num⟩
  | 2 => ⟨((167956989/536870912), (-531413299/4294967296)), (65/2147483648), by norm_num⟩
  | 3 => ⟨((-317238655/1073741824), (501869083/4294967296)), (125/4294967296), by norm_num⟩
  | 4 => ⟨((898804791/4294967296), (-177737773/2147483648)), (45/2147483648), by norm_num⟩
  | 5 => ⟨((-1018602291/8589934592), (50356903/1073741824)), (13/1073741824), by norm_num⟩
  | 6 => ⟨((480986267/8589934592), (-380458265/17179869184)), (101/17179869184), by norm_num⟩
  | 7 => ⟨((-778706691/34359738368), (307976981/34359738368)), (83/34359738368), by norm_num⟩
  | 8 => ⟨((551560547/68719476736), (-218141123/68719476736)), (119/137438953472), by norm_num⟩
  | 9 => ⟨((-86816039/34359738368), (68671149/68719476736)), (19/68719476736), by norm_num⟩
  | 10 => ⟨((787098753/1099511627776), (-311296025/1099511627776)), (11/137438953472), by norm_num⟩
  | 11 => ⟨((-810915887/4398046511104), (320715655/4398046511104)), (93/4398046511104), by norm_num⟩
  | 12 => ⟨((1531665141/35184372088832), (-302885291/17592186044416)), (89/17592186044416), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (-490588785427/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444536408901821/158456325028528675187087900672), (-290099396181/316912650057057350374175801344)), (46129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472260250914587/9903520314283042199192993792), (-20393241851/1237940039285380274899124224)), (51897/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472193125983647/618970019642690137449562112), (-173298741799/618970019642690137449562112)), (110285/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770439011892435/154742504910672534362390528), (-692997896945/154742504910672534362390528)), (55145/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193606125510435/1208925819614629174706176), (-324738109977/4835703278458516698824704)), (51701/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157271573668491/75557863725914323419136), (-142020618153/151115727451828646838272)), (45241/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886791405920867/75557863725914323419136), (-922741918927/75557863725914323419136)), (147043/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296789423248339/4722366482869645213696), (-172928385139/1180591620717411303424)), (110291/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810208776146389/295147905179352825856), (-950549260331/590295810358705651712)), (151663/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822187507289837/73786976294838206464), (-1187351904693/73786976294838206464)), (189599/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821210379663523/9223372036854775808), (-1334624220989/9223372036854775808)), (213327/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796230367858177/576460752303423488), (-83324523779/72057594037927936)), (213363/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193248356753093/144115188075855872), (-582467285677/72057594037927936)), (186733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489642942224641/36028797018963968), (-1744189474399/36028797018963968)), (70045/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486771853894065/9007199254740992), (-543656679973/2251799813685248)), (350367/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111499054844983/2251799813685248), (-4332469158801/4503599627370496)), (701163/4503599627370496), by norm_num⟩
  | 1 => ⟨((552183193493939/562949953421312), (-6456903906393/2251799813685248)), (526413/1125899906842624), by norm_num⟩
  | 0 => ⟨((541551451314983/562949953421312), (-12747570210343/2251799813685248)), (2110035/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((541551451314983/562949953421312), (-12747570210343/2251799813685248)), (8049144753462981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2083793178096177/2251799813685248), (-12263017531479/1125899906842624)), (2041775/1125899906842624), by norm_num⟩
  | 2 => ⟨((1928054375126223/2251799813685248), (-5674037301111/281474976710656)), (1911677/562949953421312), by norm_num⟩
  | 3 => ⟨((1649939390752543/2251799813685248), (-77732326836869/2251799813685248)), (13402943/2251799813685248), by norm_num⟩
  | 4 => ⟨((1206260726203733/2251799813685248), (-56956052311375/1125899906842624)), (20566559/2251799813685248), by norm_num⟩
  | 5 => ⟨((640416152109845/2251799813685248), (-122042552104803/2251799813685248)), (48230599/4503599627370496), by norm_num⟩
  | 6 => ⟨((1404169095163349/18014398509481984), (-555346144982303/18014398509481984)), (130646927/18014398509481984), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-638804767/16777216)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term17Value_checks : CertifiedScalarExp.Checks term17Value := by
  constructor
  · norm_num [term17Value, CertifiedScalarExp.reduced, term17ValuePoly, term17ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term17ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value, term17ValueSquares, term17ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term17Value, CertifiedScalarExp.roundingCheck, term17ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term17 : Sound J_term17 F_term17 c := by
  apply exp_sound (A_arg17 hcre) S_arg17 term17Value term17Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term17Value,J_arg17]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term17,J_arg17,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((722592939474041/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log18 : Sound J_log18 F_log18 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log18_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog18 : Sound J_negLog18 F_negLog18 c := by
  apply sound_round (sound_scale (A_log18 hcre) S_log18)
  intro k
  fin_cases k <;> norm_num [J_negLog18, J_log18, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-84861685/33554432), (-1303384555/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-775878261/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg18 : Sound J_arg18 F_arg18 c := by
  apply sound_round (sound_mul (A_negLog18 hcre) (A_variable hcre) S_negLog18 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg18, J_negLog18, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term18 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2318624599847/70368744177664), (-1307952931894491/18014398509481984)), (198464143/18014398509481984), by norm_num⟩
  | 1 => ⟨((-409038517/4294967296), (901334337/4294967296)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((591136689/4294967296), (-162824457/536870912)), (101/2147483648), by norm_num⟩
  | 3 => ⟨((-284767465/2147483648), (39218601/134217728)), (197/4294967296), by norm_num⟩
  | 4 => ⟨((411541919/4294967296), (-453425347/2147483648)), (9/268435456), by norm_num⟩
  | 5 => ⟨((-59475457/1073741824), (524227127/4294967296)), (21/1073741824), by norm_num⟩
  | 6 => ⟨((458416483/17179869184), (-1010140855/17179869184)), (41/4294967296), by norm_num⟩
  | 7 => ⟨((-189284865/17179869184), (208548757/8589934592)), (137/34359738368), by norm_num⟩
  | 8 => ⟨((136775907/34359738368), (-1205566875/137438953472)), (25/17179869184), by norm_num⟩
  | 9 => ⟨((-175703653/137438953472), (774341433/274877906944)), (65/137438953472), by norm_num⟩
  | 10 => ⟨((406279101/1099511627776), (-223813461/274877906944)), (19/137438953472), by norm_num⟩
  | 11 => ⟨((-427017323/4398046511104), (235237857/1099511627776)), (81/2199023255552), by norm_num⟩
  | 12 => ⟨((411412937/17592186044416), (-453283239/8796093022208)), (79/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (-1491197070155/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778067103939001/633825300114114700748351602688), (-881715301743/316912650057057350374175801344)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888952592403335/39614081257132168796771975168), (-1983424483907/39614081257132168796771975168)), (25983/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888678481472785/2475880078570760549798248448), (-1053422465813/1237940039285380274899124224)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770344893362429/154742504910672534362390528), (-526558416767/38685626227668133590597632)), (110455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774380332989715/4835703278458516698824704), (-493486207087/2417851639229258349412352)), (6473/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258095191626407/604462909807314587353088), (-1726552753655/604462909807314587353088)), (90637/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235833180476679/9444732965739290427392), (-2804431963217/75557863725914323419136)), (73657/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648347392462393/2361183241434822606848), (-1051130151389/2361183241434822606848)), (110511/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620287154044671/590295810358705651712), (-2888880500991/590295810358705651712)), (75997/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822024104356271/73786976294838206464), (-3608511335763/73786976294838206464)), (95027/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821025995464951/9223372036854775808), (-2028008976983/4611686018427387904)), (26737/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796137829180943/576460752303423488), (-4051575790101/1152921504606846976)), (214003/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596542818312085/72057594037927936), (-885034376917/36028797018963968)), (93687/72057594037927936), by norm_num⟩
  | 4 => ⟨((744698656511279/18014398509481984), (-2650119469791/18014398509481984)), (281301/36028797018963968), by norm_num⟩
  | 3 => ⟨((23225970622167/140737488355328), (-6607890224229/9007199254740992)), (176025/4503599627370496), by norm_num⟩
  | 2 => ⟨((1111185300708259/2251799813685248), (-1645461536577/562949953421312)), (352685/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103885797280955/1125899906842624), (-19615797074449/2251799813685248)), (8291/17592186044416), by norm_num⟩
  | 0 => ⟨((2164204872004419/2251799813685248), (-19357746802313/1125899906842624)), (2135337/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164204872004419/2251799813685248), (-19357746802313/1125899906842624)), (8145664223677825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2079351730160989/2251799813685248), (-74418924250697/2251799813685248)), (1044493/562949953421312), by norm_num⟩
  | 2 => ⟨((1917650678889545/2251799813685248), (-137439498801767/2251799813685248)), (1998045/562949953421312), by norm_num⟩
  | 3 => ⟨((812348968185417/1125899906842624), (-234089146452241/2251799813685248)), (14588021/2251799813685248), by norm_num⟩
  | 4 => ⟨((573951032470023/1125899906842624), (-337795705334335/2251799813685248)), (24083869/2251799813685248), by norm_num⟩
  | 5 => ⟨((534493876780973/2251799813685248), (-86099213909821/562949953421312)), (248283/17592186044416), by norm_num⟩
  | 6 => ⟨((2318624599847/70368744177664), (-1307952931894491/18014398509481984)), (198464143/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-1303384555/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term18Value_checks : CertifiedScalarExp.Checks term18Value := by
  constructor
  · norm_num [term18Value, CertifiedScalarExp.reduced, term18ValuePoly, term18ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term18ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value, term18ValueSquares, term18ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term18Value, CertifiedScalarExp.roundingCheck, term18ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term18 : Sound J_term18 F_term18 c := by
  apply exp_sound (A_arg18 hcre) S_arg18 term18Value term18Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term18Value,J_arg18]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term18,J_arg18,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((73610974479161/25000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log19 : Sound J_log19 F_log19 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log19_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog19 : Sound J_negLog19 F_negLog19 c := by
  apply sound_round (sound_scale (A_log19 hcre) S_log19)
  intro k
  fin_cases k <;> norm_num [J_negLog19, J_log19, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-86449105/33554432), (-663882817/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg19 : Sound J_arg19 F_arg19 c := by
  apply sound_round (sound_mul (A_negLog19 hcre) (A_variable hcre) S_negLog19 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg19, J_negLog19, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term19 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-405627000209931/18014398509481984), (-654270317337705/9007199254740992)), (239002161/18014398509481984), by norm_num⟩
  | 1 => ⟨((71188447/1073741824), (918607247/4294967296)), (169/4294967296), by norm_num⟩
  | 2 => ⟨((-104805019/1073741824), (-338097873/1073741824)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((205727989/2147483648), (1327344741/4294967296)), (249/4294967296), by norm_num⟩
  | 4 => ⟨((-302876755/4294967296), (-977071399/4294967296)), (185/4294967296), by norm_num⟩
  | 5 => ⟨((356720849/8589934592), (1150770845/8589934592)), (55/2147483648), by norm_num⟩
  | 6 => ⟨((-350114257/17179869184), (-1129458177/17179869184)), (109/8589934592), by norm_num⟩
  | 7 => ⟨((294540019/34359738368), (475088669/17179869184)), (185/34359738368), by norm_num⟩
  | 8 => ⟨((-108406889/34359738368), (-1398869595/137438953472)), (275/137438953472), by norm_num⟩
  | 9 => ⟨((70932771/68719476736), (228827009/68719476736)), (181/274877906944), by norm_num⟩
  | 10 => ⟨((-334171545/1099511627776), (-134753433/137438953472)), (215/1099511627776), by norm_num⟩
  | 11 => ⟨((89449793/1099511627776), (577124743/2199023255552)), (29/549755813888), by norm_num⟩
  | 12 => ⟨((-175586305/8796093022208), (-1132872393/17592186044416)), (115/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (-609422834577/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777991443632859/633825300114114700748351602688), (-2882492000963/633825300114114700748351602688)), (23121/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1888867339645035/39614081257132168796771975168), (-3242074999227/39614081257132168796771975168)), (104063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888587718732495/2475880078570760549798248448), (-3443798980757/2475880078570760549798248448)), (27647/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442563481617583/38685626227668133590597632), (-860695107109/38685626227668133590597632)), (27653/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548675167791123/9671406556917033397649408), (-201657799503/604462909807314587353088)), (25931/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629010082096091/302231454903657293676544), (-176382983099/37778931862957161709568)), (2837/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((471635779674869/18889465931478580854784), (-2291965329079/37778931862957161709568)), (147571/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648301343343967/2361183241434822606848), (-3436175295285/4722366482869645213696)), (865/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1620159943891533/590295810358705651712), (-4721861973017/590295810358705651712)), (38077/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227733028811315/9223372036854775808), (-5898011637435/73786976294838206464)), (95243/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820844955591497/9223372036854775808), (-6629333307197/9223372036854775808)), (214435/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398023286193933/288230376151711744), (-6621927791641/1152921504606846976)), (107305/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192924284121427/144115188075855872), (-5785864840119/144115188075855872)), (46995/36028797018963968), by norm_num⟩
  | 4 => ⟨((372287997511147/9007199254740992), (-8662176354111/36028797018963968)), (282363/36028797018963968), by norm_num⟩
  | 3 => ⟨((743074864075931/4503599627370496), (-2699671415937/2251799813685248)), (88411/2251799813685248), by norm_num⟩
  | 2 => ⟨((2221728711710897/4503599627370496), (-21510473949391/4503599627370496)), (44335/281474976710656), by norm_num⟩
  | 1 => ⟨((2206766368712913/2251799813685248), (-8012297656587/562949953421312)), (1069239/2251799813685248), by norm_num⟩
  | 0 => ⟨((2162027091216563/2251799813685248), (-31618314643885/1125899906842624)), (2159369/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162027091216563/2251799813685248), (-31618314643885/1125899906842624)), (8237339028365325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2074057491028591/2251799813685248), (-121431136859031/2251799813685248)), (2133923/1125899906842624), by norm_num⟩
  | 2 => ⟨((1903796655918971/2251799813685248), (-223692317155325/2251799813685248)), (8322239/2251799813685248), by norm_num⟩
  | 3 => ⟨((1587354005720493/2251799813685248), (-47280477905595/281474976710656)), (15725619/2251799813685248), by norm_num⟩
  | 4 => ⟨((263858307387075/562949953421312), (-33329275337757/140737488355328)), (27453811/2251799813685248), by norm_num⟩
  | 5 => ⟨((184200235027745/1125899906842624), (-999785490541665/4503599627370496)), (77477429/4503599627370496), by norm_num⟩
  | 6 => ⟨((-405627000209931/18014398509481984), (-654270317337705/9007199254740992)), (239002161/18014398509481984), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-663882817/16777216)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term19Value_checks : CertifiedScalarExp.Checks term19Value := by
  constructor
  · norm_num [term19Value, CertifiedScalarExp.reduced, term19ValuePoly, term19ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term19ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value, term19ValueSquares, term19ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term19Value, CertifiedScalarExp.roundingCheck, term19ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term19 : Sound J_term19 F_term19 c := by
  apply exp_sound (A_arg19 hcre) S_arg19 term19Value term19Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term19Value,J_arg19]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term19,J_arg19,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2995732273553991/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log20 : Sound J_log20 F_log20 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log20_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog20 : Sound J_negLog20 F_negLog20 c := by
  apply sound_round (sound_scale (A_log20 hcre) S_log20)
  intro k
  fin_cases k <;> norm_num [J_negLog20, J_log20, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-87955083/33554432), (-675447919/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-804160759/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg20 : Sound J_arg20 F_arg20 c := by
  apply sound_round (sound_mul (A_negLog20 hcre) (A_variable hcre) S_negLog20 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg20, J_negLog20, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term20 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1095007122050933/18014398509481984), (-718778386330529/18014398509481984)), (29874165/2251799813685248), by norm_num⟩
  | 1 => ⟨((782095951/4294967296), (128344751/1073741824)), (43/1073741824), by norm_num⟩
  | 2 => ⟨((-1171475041/4294967296), (-384486513/2147483648)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((1169808529/4294967296), (11998111/67108864)), (131/2147483648), by norm_num⟩
  | 4 => ⟨((-876108291/4294967296), (-287545027/2147483648)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((1049834353/8589934592), (344563167/4294967296)), (239/8589934592), by norm_num⟩
  | 6 => ⟨((-1048340885/17179869184), (-43009125/1073741824)), (241/17179869184), by norm_num⟩
  | 7 => ⟨((897299607/34359738368), (294500169/17179869184)), (209/34359738368), by norm_num⟩
  | 8 => ⟨((-168004337/17179869184), (-220560915/34359738368)), (79/34359738368), by norm_num⟩
  | 9 => ⟨((447374235/137438953472), (587325735/274877906944)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((-1072170747/1099511627776), (-87973533/137438953472)), (1/4294967296), by norm_num⟩
  | 11 => ⟨((1167976913/4398046511104), (383338403/2199023255552)), (281/4398046511104), by norm_num⟩
  | 12 => ⟨((-583157689/8796093022208), (-382793075/8796093022208)), (283/17592186044416), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (-3335625572769/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777918428687989/633825300114114700748351602688), (-3943978100021/633825300114114700748351602688)), (92589/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888785002776873/39614081257132168796771975168), (-4435952746233/39614081257132168796771975168)), (104187/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944249986465437/1237940039285380274899124224), (-4711937918313/2475880078570760549798248448)), (13841/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770165885269021/154742504910672534362390528), (-4710518667813/154742504910672534362390528)), (110761/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548592315571653/9671406556917033397649408), (-2207301856211/4835703278458516698824704)), (103873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628973677604733/302231454903657293676544), (-3861271176075/604462909807314587353088)), (90923/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943212108662537/37778931862957161709568), (-3135870445773/37778931862957161709568)), (147815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648256498934455/2361183241434822606848), (-146916718319/147573952589676412928)), (55459/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620035789687441/590295810358705651712), (-3230161302471/295147905179352825856)), (152605/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821707791721681/73786976294838206464), (-8069387005637/73786976294838206464)), (190895/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820667252121707/9223372036854775808), (-9069793319501/9223372036854775808)), (214947/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397978327275511/288230376151711744), (-4529733707747/576460752303423488)), (107593/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192764536199879/144115188075855872), (-1978857059987/36028797018963968)), (188557/144115188075855872), by norm_num⟩
  | 4 => ⟨((744453801136443/18014398509481984), (-740622380797/2251799813685248)), (283373/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485835942476311/9007199254740992), (-7385968203177/4503599627370496)), (355159/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221076394433261/4503599627370496), (-7355646041613/1125899906842624)), (356577/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102863287706787/1125899906842624), (-2739469490309/140737488355328)), (1076843/2251799813685248), by norm_num⟩
  | 0 => ⟨((2159705504403831/2251799813685248), (-86458707455175/2251799813685248)), (136391/140737488355328), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2159705504403831/2251799813685248), (-86458707455175/2251799813685248)), (520290375292730287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1034029030768077/1125899906842624), (-82922711539349/1125899906842624)), (2176795/1125899906842624), by norm_num⟩
  | 2 => ⟨((1887094676757305/2251799813685248), (-304625626205613/2251799813685248)), (2159495/562949953421312), by norm_num⟩
  | 3 => ⟨((192530965998061/281474976710656), (-510575934967925/2251799813685248)), (16815027/2251799813685248), by norm_num⟩
  | 4 => ⟨((937772205752643/2251799813685248), (-349237715989893/1125899906842624)), (1914283/140737488355328), by norm_num⟩
  | 5 => ⟨((347765177368967/4503599627370496), (-1163532997082431/4503599627370496)), (44511823/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1095007122050933/18014398509481984), (-718778386330529/18014398509481984)), (29874165/2251799813685248), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-675447919/16777216)), (1/16777216), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term20Value_checks : CertifiedScalarExp.Checks term20Value := by
  constructor
  · norm_num [term20Value, CertifiedScalarExp.reduced, term20ValuePoly, term20ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term20ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value, term20ValueSquares, term20ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term20Value, CertifiedScalarExp.roundingCheck, term20ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term20 : Sound J_term20 F_term20 c := by
  apply exp_sound (A_arg20 hcre) S_arg20 term20Value term20Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term20Value,J_arg20]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term20,J_arg20,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3044522437723423/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log21 : Sound J_log21 F_log21 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log21_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog21 : Sound J_negLog21 F_negLog21 c := by
  apply sound_round (sound_scale (A_log21 hcre) S_log21)
  intro k
  fin_cases k <;> norm_num [J_negLog21, J_log21, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5586723/2097152), (-83795/2048)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-817257769/268435456), 0), (1/536870912), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg21 : Sound J_arg21 F_arg21 c := by
  apply sound_round (sound_mul (A_negLog21 hcre) (A_variable hcre) S_negLog21 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg21, J_negLog21, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term21 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1251587056648271/18014398509481984), (93822459379663/18014398509481984)), (52217901/4503599627370496), by norm_num⟩
  | 1 => ⟨((454245195/2147483648), (-136205951/8589934592)), (305/8589934592), by norm_num⟩
  | 2 => ⟨((-1382959689/4294967296), (103670519/4294967296)), (117/2147483648), by norm_num⟩
  | 3 => ⟨((1403483935/4294967296), (-52604537/2147483648)), (239/4294967296), by norm_num⟩
  | 4 => ⟨((-1068234583/4294967296), (80077847/4294967296)), (23/536870912), by norm_num⟩
  | 5 => ⟨((1300905663/8589934592), (-97519521/8589934592)), (113/4294967296), by norm_num⟩
  | 6 => ⟨((-20628315/268435456), (49483395/8589934592)), (231/17179869184), by norm_num⟩
  | 7 => ⟨((1148404441/34359738368), (-21521901/8589934592)), (203/34359738368), by norm_num⟩
  | 8 => ⟨((-218521443/17179869184), (131047821/137438953472)), (311/137438953472), by norm_num⟩
  | 9 => ⟨((1182743887/274877906944), (-88661785/274877906944)), (53/68719476736), by norm_num⟩
  | 10 => ⟨((-1440356121/1099511627776), (53986559/549755813888)), (65/274877906944), by norm_num⟩
  | 11 => ⟨((199327115/549755813888), (-59768469/2199023255552)), (145/2199023255552), by norm_num⟩
  | 12 => ⟨((-1618282331/17592186044416), (121310963/17592186044416)), (37/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (3994810079603/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777849055882019/633825300114114700748351602688), (4723051807907/633825300114114700748351602688)), (92665/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944353389050491/19807040628566084398385987584), (2656089744931/19807040628566084398385987584)), (104279/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888416615076287/2475880078570760549798248448), (2821326905301/1237940039285380274899124224)), (110831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110630140817123/9671406556917033397649408), (2820462533903/77371252455336267181195264)), (55435/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((96782101197589/604462909807314587353088), (5286530885029/9671406556917033397649408)), (51991/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628939102457385/302231454903657293676544), (4623878633421/604462909807314587353088)), (45513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117894456450689/4722366482869645213696), (7510361493541/75557863725914323419136)), (73997/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162053479515977/590295810358705651712), (5629761005267/4722366482869645213696)), (13883/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619917919700395/590295810358705651712), (120875497505/9223372036854775808)), (152823/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821559297376207/73786976294838206464), (9662708804811/73786976294838206464)), (191195/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820498608590497/9223372036854775808), (5430236339889/4611686018427387904)), (215323/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591742686263101/1152921504606846976), (2711971841847/288230376151711744)), (215609/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192613021268635/144115188075855872), (9477754107777/144115188075855872)), (47245/36028797018963968), by norm_num⟩
  | 4 => ⟨((1488675906890409/36028797018963968), (14188364351353/36028797018963968)), (284115/36028797018963968), by norm_num⟩
  | 3 => ⟨((185692327624443/1125899906842624), (8843025642003/4503599627370496)), (178137/4503599627370496), by norm_num⟩
  | 2 => ⟨((1110229398119941/2251799813685248), (17612070730643/2251799813685248)), (357973/2251799813685248), by norm_num⟩
  | 1 => ⟨((1102371659377169/1125899906842624), (26233595275373/1125899906842624)), (135305/281474976710656), by norm_num⟩
  | 0 => ⟨((134844669551275/140737488355328), (51731796056821/1125899906842624)), (1099559/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((134844669551275/140737488355328), (51731796056821/1125899906842624)), (4194484714988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((257802946831611/281474976710656), (99131468467931/1125899906842624)), (2208083/1125899906842624), by norm_num⟩
  | 2 => ⟨((1871517522787497/2251799813685248), (354666083929/2199023255552)), (4433595/1125899906842624), by norm_num⟩
  | 3 => ⟨((187110301009425/281474976710656), (301844825485907/1125899906842624)), (8799837/1125899906842624), by norm_num⟩
  | 4 => ⟨((833207169443967/2251799813685248), (802604577000997/2251799813685248)), (16417705/1125899906842624), by norm_num⟩
  | 5 => ⟨((11115570728277/1125899906842624), (1187913568020657/4503599627370496)), (95412657/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1251587056648271/18014398509481984), (93822459379663/18014398509481984)), (52217901/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-83795/2048)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term21Value_checks : CertifiedScalarExp.Checks term21Value := by
  constructor
  · norm_num [term21Value, CertifiedScalarExp.reduced, term21ValuePoly, term21ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term21ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value, term21ValueSquares, term21ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term21Value, CertifiedScalarExp.roundingCheck, term21ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term21 : Sound J_term21 F_term21 c := by
  apply exp_sound (A_arg21 hcre) S_arg21 term21Value term21Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term21Value,J_arg21]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term21,J_arg21,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term16Jet : Jet 12 := J_term16
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨36,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile036Terms2
