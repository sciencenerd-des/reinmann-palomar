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
namespace Reinmann.XiRectangle.Tile013Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨13,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3807/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3807/640))
  have he : value ((3/4), (3807/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-8931133415/4294967296), (-70835051901/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-47632711549/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-398380357261889/4503599627370496), (795501706026173/9007199254740992)), (200079/1125899906842624), by norm_num⟩
  | 1 => ⟨((16854017421/68719476736), (-67309541585/274877906944)), (69/137438953472), by norm_num⟩
  | 2 => ⟨((-23364629313/68719476736), (23327709487/68719476736)), (49/68719476736), by norm_num⟩
  | 3 => ⟨((43187005155/137438953472), (-21559381413/68719476736)), (23/34359738368), by norm_num⟩
  | 4 => ⟨((-7483737715/34359738368), (14943824441/68719476736)), (129/274877906944), by norm_num⟩
  | 5 => ⟨((16599461431/137438953472), (-66292926579/549755813888)), (145/549755813888), by norm_num⟩
  | 6 => ⟨((-15341159853/274877906944), (15316918383/274877906944)), (17/137438953472), by norm_num⟩
  | 7 => ⟨((3038194771/137438953472), (-48534303049/2199023255552)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((-4211832279/549755813888), (33641415319/4398046511104)), (155/8796093022208), by norm_num⟩
  | 9 => ⟨((41520635295/17592186044416), (-41455026095/17592186044416)), (97/17592186044416), by norm_num⟩
  | 10 => ⟨((-2877991129/4398046511104), (11493773783/17592186044416)), (55/35184372088832), by norm_num⟩
  | 11 => ⟨((46426098891/281474976710656), (-46352738279/281474976710656)), (113/281474976710656), by norm_num⟩
  | 12 => ⟨((-42906826067/1125899906842624), (21419513233/562949953421312)), (107/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326629/10141204801825835211973625643008), (3070236374175/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778754584751953/633825300114114700748351602688), (1816718103945/316912650057057350374175801344)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889725545708833/39614081257132168796771975168), (2043429053779/19807040628566084398385987584)), (815/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889499152803729/2475880078570760549798248448), (2170682006721/1237940039285380274899124224)), (433/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442791224900297/38685626227668133590597632), (4340326088755/154742504910672534362390528)), (433/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774764357766461/4835703278458516698824704), (1016988278913/2417851639229258349412352)), (813/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258766529101011/604462909807314587353088), (1779178305547/302231454903657293676544)), (711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887755044548099/75557863725914323419136), (2890131520953/37778931862957161709568)), (1155/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297510829018759/4722366482869645213696), (2166694810125/2361183241434822606848)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621407337065039/590295810358705651712), (2977737092661/295147905179352825856)), (149/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227927689946989/9223372036854775808), (7439939505403/73786976294838206464)), (373/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822594223587863/9223372036854775808), (8363880088093/9223372036854775808)), (1679/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593839063440187/1152921504606846976), (4178159570585/576460752303423488)), (1681/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194448199695427/144115188075855872), (456454906893/9007199254740992)), (1473/144115188075855872), by norm_num⟩
  | 4 => ⟨((372857587184825/9007199254740992), (1367241201741/4503599627370496)), (553/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488984552502329/9007199254740992), (13642712753523/9007199254740992)), (693/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113679547447303/2251799813685248), (13598223910007/2251799813685248)), (2783/2251799813685248), by norm_num⟩
  | 1 => ⟨((138444634519991/140737488355328), (20286324161697/1125899906842624)), (2099/562949953421312), by norm_num⟩
  | 0 => ⟨((544583431862535/562949953421312), (40129865703493/1125899906842624)), (4249/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((544583431862535/562949953421312), (40129865703493/1125899906842624)), (16208650829124273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1052201926401719/1125899906842624), (19410304461501/281474976710656)), (2131/140737488355328), by norm_num⟩
  | 2 => ⟨((244493477733449/281474976710656), (290236240323839/2251799813685248)), (4277/140737488355328), by norm_num⟩
  | 3 => ⟨((1661557472352753/2251799813685248), (252103645554259/1125899906842624)), (34131/562949953421312), by norm_num⟩
  | 4 => ⟨((1113131028029581/2251799813685248), (372044347399169/1125899906842624)), (262617/2251799813685248), by norm_num⟩
  | 5 => ⟨((608751005013895/4503599627370496), (735649953208351/2251799813685248)), (866397/4503599627370496), by norm_num⟩
  | 6 => ⟨((-398380357261889/4503599627370496), (795501706026173/9007199254740992)), (200079/1125899906842624), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/4294967296), (-70835051901/4294967296)), (1/2147483648), by norm_num⟩, -3, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9126418991/4294967296), (-36191955313/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-48674234621/17179869184), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-444152459052055/9007199254740992), (489946180257125/4503599627370496)), (371757/2251799813685248), by norm_num⟩
  | 1 => ⟨((2400166843/17179869184), (-10590530821/34359738368)), (131/274877906944), by norm_num⟩
  | 2 => ⟨((-13600369455/68719476736), (60010466485/137438953472)), (47/68719476736), by norm_num⟩
  | 3 => ⟨((200691397/1073741824), (-14168537869/34359738368)), (45/68719476736), by norm_num⟩
  | 4 => ⟨((-36390498817/274877906944), (10035622639/34359738368)), (129/274877906944), by norm_num⟩
  | 5 => ⟨((20620409369/274877906944), (-90985791925/549755813888)), (37/137438953472), by norm_num⟩
  | 6 => ⟨((-2434250791/68719476736), (10740923325/137438953472)), (71/549755813888), by norm_num⟩
  | 7 => ⟨((31528008337/2199023255552), (-17389329881/549755813888)), (117/2199023255552), by norm_num⟩
  | 8 => ⟨((-22331393483/4398046511104), (49267681463/4398046511104)), (21/1099511627776), by norm_num⟩
  | 9 => ⟨((14059911557/8796093022208), (-62038156689/17592186044416)), (27/4398046511104), by norm_num⟩
  | 10 => ⟨((-31867783231/70368744177664), (17576733337/17592186044416)), (125/70368744177664), by norm_num⟩
  | 11 => ⟨((16416041581/140737488355328), (-72434378815/281474976710656)), (131/281474976710656), by norm_num⟩
  | 12 => ⟨((-484480709/17592186044416), (34203674771/562949953421312)), (125/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572619/10141204801825835211973625643008), (2600486250079/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778686492028785/633825300114114700748351602688), (769321211323/158456325028528675187087900672)), (181/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889649069170125/39614081257132168796771975168), (432661828065/4951760157141521099596496896)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889418061246541/2475880078570760549798248448), (1838413739899/1237940039285380274899124224)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771083993283239/154742504910672534362390528), (3675929859007/154742504910672534362390528)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387363265640901/2417851639229258349412352), (861307685139/2417851639229258349412352)), (203/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314675132332411/151115727451828646838272), (3013623642869/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887648163231381/75557863725914323419136), (4895351591467/75557863725914323419136)), (577/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297430990034393/4722366482869645213696), (3669950744031/4722366482869645213696)), (867/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621298081211399/590295810358705651712), (1260910866117/147573952589676412928)), (1191/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823285732999863/73786976294838206464), (6300747840359/73786976294838206464)), (1489/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227805317401361/1152921504606846976), (7083110195269/9223372036854775808)), (1677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398422180328285/288230376151711744), (442285967913/72057594037927936)), (1679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194318157409701/144115188075855872), (6184657774425/144115188075855872)), (735/72057594037927936), by norm_num⟩
  | 4 => ⟨((745619146039849/18014398509481984), (9262309533031/36028797018963968)), (69/1125899906842624), by norm_num⟩
  | 3 => ⟨((1488749726934747/9007199254740992), (5776117193437/4503599627370496)), (1383/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113452556638645/2251799813685248), (23027640924813/4503599627370496)), (5549/4503599627370496), by norm_num⟩
  | 1 => ⟨((1107236061132037/1125899906842624), (17174922828017/1125899906842624)), (8365/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088602025981371/1125899906842624), (265374805259/8796093022208)), (8451/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1088602025981371/1125899906842624), (265374805259/8796093022208)), (32238010886764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2103029834970327/2251799813685248), (131370848361875/2251799813685248)), (33705/2251799813685248), by norm_num⟩
  | 2 => ⟨((1956424438887439/2251799813685248), (30672887957371/281474976710656)), (33445/1125899906842624), by norm_num⟩
  | 3 => ⟨((1673054458313105/2251799813685248), (213195461679507/1125899906842624)), (130811/2251799813685248), by norm_num⟩
  | 4 => ⟨((581157788772303/1125899906842624), (158401122287719/562949953421312)), (121961/1125899906842624), by norm_num⟩
  | 5 => ⟨((843345707162787/4503599627370496), (654097547452053/2251799813685248)), (48635/281474976710656), by norm_num⟩
  | 6 => ⟨((-444152459052055/9007199254740992), (489946180257125/4503599627370496)), (371757/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9126418991/4294967296), (-36191955313/2147483648)), (1/2147483648), by norm_num⟩, -3, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4655269565/2147483648), (-18461053369/1073741824)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-176167424722569/18014398509481984), (2053873404799709/18014398509481984)), (2657859/18014398509481984), by norm_num⟩
  | 1 => ⟨((7769612871/274877906944), (-22645788893/68719476736)), (119/274877906944), by norm_num⟩
  | 2 => ⟨((-5614267403/137438953472), (16363687163/34359738368)), (87/137438953472), by norm_num⟩
  | 3 => ⟨((10818213295/274877906944), (-126125704617/274877906944)), (85/137438953472), by norm_num⟩
  | 4 => ⟨((-7817164545/274877906944), (91137543643/274877906944)), (125/274877906944), by norm_num⟩
  | 5 => ⟨((9037804651/549755813888), (-26342138223/137438953472)), (147/549755813888), by norm_num⟩
  | 6 => ⟨((-8707538439/1099511627776), (25379524121/274877906944)), (9/68719476736), by norm_num⟩
  | 7 => ⟨((7190863767/2199023255552), (-83835725427/2199023255552)), (121/2199023255552), by norm_num⟩
  | 8 => ⟨((-5196067387/4398046511104), (121158206539/8796093022208)), (177/8796093022208), by norm_num⟩
  | 9 => ⟨((1668729603/4398046511104), (-77820501871/17592186044416)), (115/17592186044416), by norm_num⟩
  | 10 => ⟨((-3858599133/35184372088832), (44986036159/35184372088832)), (135/70368744177664), by norm_num⟩
  | 11 => ⟨((8111117061/281474976710656), (-47282315787/140737488355328)), (9/17592186044416), by norm_num⟩
  | 12 => ⟨((-7814714559/1125899906842624), (91108980133/1125899906842624)), (141/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (2157594052143/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889310997145071/316912650057057350374175801344), (638251951669/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889576612452521/39614081257132168796771975168), (1435793099943/19807040628566084398385987584)), (407/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944670604687385/1237940039285380274899124224), (3050385225731/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771007291369555/154742504910672534362390528), (381203242447/19342813113834066795298816)), (865/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549381313756687/9671406556917033397649408), (2858217792779/9671406556917033397649408)), (811/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629318954127903/302231454903657293676544), (2500134285999/604462909807314587353088)), (355/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887546702136383/75557863725914323419136), (2030603475371/37778931862957161709568)), (1153/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40542348589737/147573952589676412928), (761145843235/1180591620717411303424)), (433/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621194231014991/590295810358705651712), (4184155114615/590295810358705651712)), (595/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823156554252875/73786976294838206464), (5226975050201/73786976294838206464)), (93/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822298083682887/9223372036854775808), (1468980942551/2305843009213693952)), (1675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593545352211257/1152921504606846976), (5870398938667/1152921504606846976)), (419/288230376151711744), by norm_num⟩
  | 5 => ⟨((597096964617181/72057594037927936), (5130389297897/144115188075855872)), (367/36028797018963968), by norm_num⟩
  | 4 => ⟨((745527191650283/18014398509481984), (7683178545983/36028797018963968)), (551/9007199254740992), by norm_num⟩
  | 3 => ⟨((744262042933929/4503599627370496), (9582295534471/9007199254740992)), (345/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113233255605649/2251799813685248), (19099685213773/4503599627370496)), (2767/2251799813685248), by norm_num⟩
  | 1 => ⟨((276730716065449/281474976710656), (28487707430345/2251799813685248)), (521/140737488355328), by norm_num⟩
  | 0 => ⟨((544019040212859/562949953421312), (14082698568929/562949953421312)), (8407/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((544019040212859/562949953421312), (14082698568929/562949953421312)), (32070164207076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2101489781943663/2251799813685248), (27218249553143/562949953421312)), (33339/2251799813685248), by norm_num⟩
  | 2 => ⟨((488987292199131/562949953421312), (101605609824991/1125899906842624)), (16363/562949953421312), by norm_num⟩
  | 3 => ⟨((840315006716925/1125899906842624), (176512500688957/1125899906842624)), (7845/140737488355328), by norm_num⟩
  | 4 => ⟨((1198992278997573/2251799813685248), (526960175769141/2251799813685248)), (226721/2251799813685248), by norm_num⟩
  | 5 => ⟨((1030194115125083/4503599627370496), (1122339878077135/4503599627370496)), (695107/4503599627370496), by norm_num⟩
  | 6 => ⟨((-176167424722569/18014398509481984), (2053873404799709/18014398509481984)), (2657859/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-18461053369/1073741824)), (1/2147483648), by norm_num⟩, -3, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-592793865/268435456), (-2350798171/134217728)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-101170152965/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((14466748309235/562949953421312), (962301093920427/9007199254740992)), (1150711/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10399525787/137438953472), (-21617407613/68719476736)), (105/274877906944), by norm_num⟩
  | 2 => ⟨((7655192273/68719476736), (15912784401/34359738368)), (79/137438953472), by norm_num⟩
  | 3 => ⟨((-7513415507/68719476736), (-62472296877/137438953472)), (5/8589934592), by norm_num⟩
  | 4 => ⟨((11061396743/137438953472), (45986466511/137438953472)), (15/34359738368), by norm_num⟩
  | 5 => ⟨((-26055686187/549755813888), (-13540434451/68719476736)), (9/34359738368), by norm_num⟩
  | 6 => ⟨((25573126013/1099511627776), (26579321995/274877906944)), (143/1099511627776), by norm_num⟩
  | 7 => ⟨((-21513859729/2199023255552), (-5590085123/137438953472)), (61/1099511627776), by norm_num⟩
  | 8 => ⟨((15836561795/4398046511104), (16459664533/1099511627776)), (23/1099511627776), by norm_num⟩
  | 9 => ⟨((-10362175521/8796093022208), (-86159071707/17592186044416)), (61/8796093022208), by norm_num⟩
  | 10 => ⟨((12204317405/35184372088832), (101476051657/70368744177664)), (73/35184372088832), by norm_num⟩
  | 11 => ⟨((-3266806171/35184372088832), (-54325462173/140737488355328)), (159/281474976710656), by norm_num⟩
  | 12 => ⟨((25650430473/1125899906842624), (833114627/8796093022208)), (79/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (27166468321/158456325028528675187087900672)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889280359142125/316912650057057350374175801344), (2057152529123/633825300114114700748351602688)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889507759311011/39614081257132168796771975168), (1156924604107/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889268159488079/2475880078570760549798248448), (2457910831405/2475880078570760549798248448)), (865/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885467180645527/77371252455336267181195264), (1228643921521/77371252455336267181195264)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((193664133628583/1208925819614629174706176), (1151522812141/4835703278458516698824704)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629289160627131/302231454903657293676544), (1007251706901/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887450111457157/75557863725914323419136), (3272328190705/75557863725914323419136)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((648641460052517/2361183241434822606848), (2453161737961/4722366482869645213696)), (865/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810547623133599/295147905179352825856), (3371336111527/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911516664905307/36893488147419103232), (4211529761539/73786976294838206464)), (1487/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822160151651615/9223372036854775808), (4734342962285/9223372036854775808)), (1673/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398352072018243/288230376151711744), (1182452921441/288230376151711744)), (837/576460752303423488), by norm_num⟩
  | 5 => ⟨((298518743128895/36028797018963968), (1033373172065/36028797018963968)), (733/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490877892090555/36028797018963968), (6190066820381/36028797018963968)), (2201/36028797018963968), by norm_num⟩
  | 3 => ⟨((744153431268911/4503599627370496), (3859905530403/4503599627370496)), (2755/9007199254740992), by norm_num⟩
  | 2 => ⟨((556510548087591/1125899906842624), (1923302524041/562949953421312)), (345/281474976710656), by norm_num⟩
  | 1 => ⟨((276654301913187/281474976710656), (22947028869491/2251799813685248)), (2077/562949953421312), by norm_num⟩
  | 0 => ⟨((2174953271710965/2251799813685248), (11341516679035/562949953421312)), (4183/562949953421312), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2174953271710965/2251799813685248), (11341516679035/562949953421312)), (15956880809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1049907639520273/1125899906842624), (87635743310101/2251799813685248)), (32997/2251799813685248), by norm_num⟩
  | 2 => ⟨((488669569541257/562949953421312), (10215099476997/140737488355328)), (64109/2251799813685248), by norm_num⟩
  | 3 => ⟨((842449225325617/1125899906842624), (283751448037335/2251799813685248)), (3769/70368744177664), by norm_num⟩
  | 4 => ⟨((612480711646689/1125899906842624), (424631330247527/2251799813685248)), (105443/1125899906842624), by norm_num⟩
  | 5 => ⟨((1172589778101555/4503599627370496), (57749027634887/281474976710656)), (617953/4503599627370496), by norm_num⟩
  | 6 => ⟨((14466748309235/562949953421312), (962301093920427/9007199254740992)), (1150711/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-2350798171/134217728)), (1/2147483648), by norm_num⟩, -3, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-9649929107/4294967296), (-76536000229/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((122653343237625/2251799813685248), (408152989285303/4503599627370496)), (484653/4503599627370496), by norm_num⟩
  | 1 => ⟨((-22426548999/137438953472), (-74628728183/274877906944)), (91/274877906944), by norm_num⟩
  | 2 => ⟨((16795984155/68719476736), (13972980597/34359738368)), (35/68719476736), by norm_num⟩
  | 3 => ⟨((-2096511325/8589934592), (-27906205955/68719476736)), (9/17179869184), by norm_num⟩
  | 4 => ⟨((50244693105/274877906944), (20899880453/68719476736)), (55/137438953472), by norm_num⟩
  | 5 => ⟨((-15051964871/137438953472), (-50088357109/274877906944)), (67/274877906944), by norm_num⟩
  | 6 => ⟨((15030552315/274877906944), (3126068915/34359738368)), (69/549755813888), by norm_num⟩
  | 7 => ⟨((-25730006091/1099511627776), (-668918967/17179869184)), (15/274877906944), by norm_num⟩
  | 8 => ⟨((38540104823/4398046511104), (64124868411/4398046511104)), (23/1099511627776), by norm_num⟩
  | 9 => ⟨((-12828426205/4398046511104), (-42689097297/8796093022208)), (125/17592186044416), by norm_num⟩
  | 10 => ⟨((30744424321/35184372088832), (51154042601/35184372088832)), (77/35184372088832), by norm_num⟩
  | 11 => ⟨((-16745829849/70368744177664), (-55725024125/140737488355328)), (43/70368744177664), by norm_num⟩
  | 12 => ⟨((8361003821/140737488355328), (1738929721/17592186044416)), (87/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (41912739883/316912650057057350374175801344)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889251173333049/316912650057057350374175801344), (793399260569/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944721077862857/19807040628566084398385987584), (111549906335/2475880078570760549798248448)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889198539181295/2475880078570760549798248448), (1895913793307/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770864834851499/154742504910672534362390528), (1895425034923/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549247987665853/9671406556917033397649408), (888220915231/4835703278458516698824704)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258521474668929/604462909807314587353088), (1553867648655/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887357922376755/75557863725914323419136), (1262031144469/37778931862957161709568)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1297213941445395/4722366482869645213696), (1892196053169/4722366482869645213696)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((810500332731509/295147905179352825856), (2600387988073/590295810358705651712)), (297/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822915500617761/73786976294838206464), (3248413907415/73786976294838206464)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113876758666797/576460752303423488), (1825810012477/4611686018427387904)), (1671/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593276955028393/1152921504606846976), (3648066162797/1152921504606846976)), (209/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193960819472799/144115188075855872), (3188064144025/144115188075855872)), (183/18014398509481984), by norm_num⟩
  | 4 => ⟨((745354092688369/18014398509481984), (596764946709/4503599627370496)), (2197/36028797018963968), by norm_num⟩
  | 3 => ⟨((372024346348409/2251799813685248), (5953714733157/9007199254740992)), (1375/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112815585965965/2251799813685248), (5932861331841/2251799813685248)), (5507/4503599627370496), by norm_num⟩
  | 1 => ⟨((138289849854875/140737488355328), (1105916072477/140737488355328)), (4141/1125899906842624), by norm_num⟩
  | 0 => ⟨((271729720185565/281474976710656), (34975642199181/2251799813685248)), (16653/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((271729720185565/281474976710656), (34975642199181/2251799813685248)), (63526162154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2098031667378557/2251799813685248), (33764711801943/1125899906842624)), (32671/2251799813685248), by norm_num⟩
  | 2 => ⟨((1952738705966339/2251799813685248), (31459028537911/562949953421312)), (7855/281474976710656), by norm_num⟩
  | 3 => ⟨((1686363815769057/2251799813685248), (54561921805599/562949953421312)), (29003/562949953421312), by norm_num⟩
  | 4 => ⟨((1241758192341735/2251799813685248), (163444814397065/1125899906842624)), (196251/2251799813685248), by norm_num⟩
  | 5 => ⟨((318657673322653/1125899906842624), (180263748171443/1125899906842624)), (273425/2251799813685248), by norm_num⟩
  | 6 => ⟨((122653343237625/2251799813685248), (408152989285303/4503599627370496)), (484653/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-76536000229/4294967296)), (1/2147483648), by norm_num⟩, -3, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((-4903546613/2147483648), (-77782508153/4294967296)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((678411684677071/9007199254740992), (618710173024599/9007199254740992)), (49767/562949953421312), by norm_num⟩
  | 1 => ⟨((-31516107117/137438953472), (-57485260139/274877906944)), (19/68719476736), by norm_num⟩
  | 2 => ⟨((23987873817/68719476736), (43753791083/137438953472)), (59/137438953472), by norm_num⟩
  | 3 => ⟨((-48687746713/137438953472), (-1387597903/4294967296)), (61/137438953472), by norm_num⟩
  | 4 => ⟨((4632216791/17179869184), (16898291801/68719476736)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((-45129241461/274877906944), (-20578891419/137438953472)), (15/68719476736), by norm_num⟩
  | 6 => ⟨((45798996075/549755813888), (41768597779/549755813888)), (63/549755813888), by norm_num⟩
  | 7 => ⟨((-39838877479/1099511627776), (-36332980895/1099511627776)), (57/1099511627776), by norm_num⟩
  | 8 => ⟨((60645178189/4398046511104), (27654143891/2199023255552)), (89/4398046511104), by norm_num⟩
  | 9 => ⟨((-2564383413/549755813888), (-37419405143/8796093022208)), (31/4398046511104), by norm_num⟩
  | 10 => ⟨((49966866175/35184372088832), (22784843713/17592186044416)), (77/35184372088832), by norm_num⟩
  | 11 => ⟨((-55318270987/140737488355328), (-50450158491/140737488355328)), (11/17592186044416), by norm_num⟩
  | 12 => ⟨((56139239079/562949953421312), (25599439919/281474976710656)), (91/562949953421312), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307151/10141204801825835211973625643008), (481578447195/5070602400912917605986812821504)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444611651825871/158456325028528675187087900672), (284863343363/158456325028528675187087900672)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944689749008827/19807040628566084398385987584), (40050951421/1237940039285380274899124224)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889132028894121/2475880078570760549798248448), (1361415241147/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770798395976325/154742504910672534362390528), (170132329981/19342813113834066795298816)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387296444262611/2417851639229258349412352), (1275613713637/9671406556917033397649408)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629233558079827/302231454903657293676544), (1115783381865/604462909807314587353088)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887269731777183/75557863725914323419136), (906219196359/37778931862957161709568)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648573961309265/2361183241434822606848), (1358708197059/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620910091073425/590295810358705651712), (933607935787/295147905179352825856)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822802584523217/73786976294838206464), (1166254494965/36893488147419103232)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227737690323817/1152921504606846976), (2621996818621/9223372036854775808)), (835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593150856250447/1152921504606846976), (2619404507341/1152921504606846976)), (835/576460752303423488), by norm_num⟩
  | 5 => ⟨((149231382978025/18014398509481984), (2289065935117/144115188075855872)), (731/72057594037927936), by norm_num⟩
  | 4 => ⟨((745272355260671/18014398509481984), (856945307119/9007199254740992)), (1097/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487895062788783/9007199254740992), (1068641087713/2251799813685248)), (343/1125899906842624), by norm_num⟩
  | 2 => ⟨((1112616281609769/2251799813685248), (8518716990185/4503599627370496)), (2747/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106027341888731/1125899906842624), (12702307537393/2251799813685248)), (8257/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172731380379427/2251799813685248), (25103106330921/2251799813685248)), (16579/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172731380379427/2251799813685248), (25103106330921/2251799813685248)), (63243874556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((262019932714021/281474976710656), (3027706245173/140737488355328)), (8091/562949953421312), by norm_num⟩
  | 2 => ⟨((487558630759337/562949953421312), (22547493092533/562949953421312)), (61647/2251799813685248), by norm_num⟩
  | 3 => ⟨((210680387787187/281474976710656), (156223121326363/2251799813685248)), (111721/2251799813685248), by norm_num⟩
  | 4 => ⟨((1250694120467191/2251799813685248), (116930990338783/1125899906842624)), (91373/1125899906842624), by norm_num⟩
  | 5 => ⟨((83796545089763/281474976710656), (519566264206339/4503599627370496)), (3765/35184372088832), by norm_num⟩
  | 6 => ⟨((678411684677071/9007199254740992), (618710173024599/9007199254740992)), (49767/562949953421312), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4903546613/2147483648), (-77782508153/4294967296)), (1/2147483648), by norm_num⟩, -3, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨13,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile013Terms2
