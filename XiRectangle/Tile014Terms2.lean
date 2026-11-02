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
namespace Reinmann.XiRectangle.Tile014Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨14,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4089/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4089/640))
  have he : value ((3/4), (4089/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-8931133415/4294967296), (-76082092783/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((118739770067427/2251799813685248), (1020815591852115/9007199254740992)), (1201825/9007199254740992), by norm_num⟩
  | 1 => ⟨((-20093783409/137438953472), (-86373956221/274877906944)), (13/34359738368), by norm_num⟩
  | 2 => ⟨((27855898633/137438953472), (14967466057/34359738368)), (37/68719476736), by norm_num⟩
  | 3 => ⟨((-25744316799/137438953472), (-55331503453/137438953472)), (35/68719476736), by norm_num⟩
  | 4 => ⟨((35689201209/274877906944), (76705751229/274877906944)), (99/274877906944), by norm_num⟩
  | 5 => ⟨((-39580590711/549755813888), (-85069400315/549755813888)), (7/34359738368), by norm_num⟩
  | 6 => ⟨((18290116571/549755813888), (39310409987/549755813888)), (53/549755813888), by norm_num⟩
  | 7 => ⟨((-7244424419/549755813888), (-62280913941/2199023255552)), (43/1099511627776), by norm_num⟩
  | 8 => ⟨((20085809443/4398046511104), (43169839901/4398046511104)), (61/4398046511104), by norm_num⟩
  | 9 => ⟨((-24750972773/17592186044416), (-53196538333/17592186044416)), (77/17592186044416), by norm_num⟩
  | 10 => ⟨((13724853595/35184372088832), (29498424449/35184372088832)), (87/70368744177664), by norm_num⟩
  | 11 => ⟨((-27675181303/281474976710656), (-59481453783/281474976710656)), (45/140737488355328), by norm_num⟩
  | 12 => ⟨((12788649261/562949953421312), (13743133995/281474976710656)), (85/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326629/10141204801825835211973625643008), (1478872316449/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889380006007951/316912650057057350374175801344), (875077285031/316912650057057350374175801344)), (723/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944865978760631/19807040628566084398385987584), (984282487447/19807040628566084398385987584)), (813/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944753182062551/1237940039285380274899124224), (2091156530261/2475880078570760549798248448)), (27/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771172559188477/154742504910672534362390528), (2090657466635/154742504910672534362390528)), (27/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1549536372374193/9671406556917033397649408), (979730635939/4835703278458516698824704)), (405/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629386852236487/302231454903657293676544), (856999340407/302231454903657293676544)), (709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471941898904409/18889465931478580854784), (696063649239/18889465931478580854784)), (9/590295810358705651712), by norm_num⟩
  | 10 => ⟨((162190127662251/590295810358705651712), (521830552229/1180591620717411303424)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((405355653981243/147573952589676412928), (2868657017319/590295810358705651712)), (1189/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823442512483239/73786976294838206464), (3583705932233/73786976294838206464)), (1485/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911310220724371/4611686018427387904), (4028762515541/9223372036854775808)), (209/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593868526556213/1152921504606846976), (2012566045547/576460752303423488)), (1673/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18663712857415/2251799813685248), (3517910334345/144115188075855872)), (1465/144115188075855872), by norm_num⟩
  | 4 => ⟨((372870437385203/9007199254740992), (1317178739243/9007199254740992)), (1099/18014398509481984), by norm_num⟩
  | 3 => ⟨((186132684302581/1125899906842624), (3285826298471/4503599627370496)), (2751/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227550773275983/4503599627370496), (6550335592411/2251799813685248)), (5511/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215495634154033/2251799813685248), (19544733698959/2251799813685248)), (8291/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179468828486513/2251799813685248), (38666242227195/2251799813685248)), (2085/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179468828486513/2251799813685248), (38666242227195/2251799813685248)), (7953644872569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((263599658548519/281474976710656), (37424228004959/1125899906842624)), (32863/2251799813685248), by norm_num⟩
  | 2 => ⟨((1972388309476553/2251799813685248), (70095138394415/1125899906842624)), (31869/1125899906842624), by norm_num⟩
  | 3 => ⟨((859459687786145/1125899906842624), (61397478887797/562949953421312)), (119595/2251799813685248), by norm_num⟩
  | 4 => ⟨((642679112838305/1125899906842624), (187471933215599/1125899906842624)), (208675/2251799813685248), by norm_num⟩
  | 5 => ⟨((1342537517015205/4503599627370496), (856092410977873/4503599627370496)), (153861/1125899906842624), by norm_num⟩
  | 6 => ⟨((118739770067427/2251799813685248), (1020815591852115/9007199254740992)), (1201825/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8931133415/4294967296), (-76082092783/4294967296)), (1/2147483648), by norm_num⟩, -3, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-9126418991/4294967296), (-77745681783/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((197167639266145/2251799813685248), (731750775534717/9007199254740992)), (116945/1125899906842624), by norm_num⟩
  | 1 => ⟨((-34095336095/137438953472), (-63269227959/274877906944)), (83/274877906944), by norm_num⟩
  | 2 => ⟨((48299680597/137438953472), (22406902615/68719476736)), (15/34359738368), by norm_num⟩
  | 3 => ⟨((-45614433193/137438953472), (-165321707/536870912)), (59/137438953472), by norm_num⟩
  | 4 => ⟨((32308855201/137438953472), (59954133291/274877906944)), (43/137438953472), by norm_num⟩
  | 5 => ⟨((-18307575937/137438953472), (-16986285047/137438953472)), (51/274877906944), by norm_num⟩
  | 6 => ⟨((69159024589/1099511627776), (32083846307/549755813888)), (99/1099511627776), by norm_num⟩
  | 7 => ⟨((-55983506093/2199023255552), (-25971537567/1099511627776)), (41/1099511627776), by norm_num⟩
  | 8 => ⟨((39653304127/4398046511104), (4598931675/549755813888)), (15/1099511627776), by norm_num⟩
  | 9 => ⟨((-3120729733/1099511627776), (-723875255/274877906944)), (77/17592186044416), by norm_num⟩
  | 10 => ⟨((56586835985/70368744177664), (3281428851/4398046511104)), (89/70368744177664), by norm_num⟩
  | 11 => ⟨((-58299119567/281474976710656), (-54091566593/281474976710656)), (47/140737488355328), by norm_num⟩
  | 12 => ⟨((27528973917/562949953421312), (25542158045/562949953421312)), (91/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572619/10141204801825835211973625643008), (974325887145/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778690850173829/633825300114114700748351602688), (576484164605/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472413554334127/9903520314283042199192993792), (1296848708193/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236177981416469/309485009821345068724781056), (172200389345/309485009821345068724781056)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885545071623339/77371252455336267181195264), (1377267270295/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387364802568899/2417851639229258349412352), (1290831342333/9671406556917033397649408)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258706290418339/604462909807314587353088), (282280206517/151115727451828646838272)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((471914560088987/18889465931478580854784), (917076492971/37778931862957161709568)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648719586609155/2361183241434822606848), (171878774149/590295810358705651712)), (27/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1621310348151769/590295810358705651712), (1889717125711/590295810358705651712)), (1187/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823302587317915/73786976294838206464), (295090399101/9223372036854775808)), (371/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911231794017281/4611686018427387904), (663464521481/2305843009213693952)), (835/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593712375035167/1152921504606846976), (1325707911187/576460752303423488)), (835/576460752303423488), by norm_num⟩
  | 5 => ⟨((597170889204471/72057594037927936), (2317244208939/144115188075855872)), (731/72057594037927936), by norm_num⟩
  | 4 => ⟨((745639777646351/18014398509481984), (3470384311247/36028797018963968)), (1097/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488811474909219/9007199254740992), (2164201609375/4503599627370496)), (2745/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227058970273061/4503599627370496), (8628140150437/4503599627370496)), (5495/4503599627370496), by norm_num⟩
  | 1 => ⟨((276847287687201/281474976710656), (804423268571/140737488355328)), (4129/1125899906842624), by norm_num⟩
  | 0 => ⟨((2178114944265009/2251799813685248), (25457155667897/2251799813685248)), (4145/562949953421312), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2178114944265009/2251799813685248), (25457155667897/2251799813685248)), (15811922313499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2106553439975951/2251799813685248), (12312064967263/562949953421312)), (32451/2251799813685248), by norm_num⟩
  | 2 => ⟨((1969598708295443/2251799813685248), (1439738484543/35184372088832)), (7767/281474976710656), by norm_num⟩
  | 3 => ⟨((429748313690671/562949953421312), (161191284146249/2251799813685248)), (14223/281474976710656), by norm_num⟩
  | 4 => ⟨((325179347874781/562949953421312), (246102454125763/2251799813685248)), (190013/2251799813685248), by norm_num⟩
  | 5 => ⟨((362221211829619/1125899906842624), (568629129865875/4503599627370496)), (522101/4503599627370496), by norm_num⟩
  | 6 => ⟨((197167639266145/2251799813685248), (731750775534717/9007199254740992)), (116945/1125899906842624), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9126418991/4294967296), (-77745681783/4294967296)), (1/2147483648), by norm_num⟩, -3, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-4655269565/2147483648), (-79314155215/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((956111092688217/9007199254740992), (384979622263047/9007199254740992)), (696701/9007199254740992), by norm_num⟩
  | 1 => ⟨((-10541978835/34359738368), (-16978976861/137438953472)), (63/274877906944), by norm_num⟩
  | 2 => ⟨((30470237897/68719476736), (24537777599/137438953472)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((-58713543383/137438953472), (-23641099791/137438953472)), (3/8589934592), by norm_num⟩
  | 4 => ⟨((10606497975/34359738368), (34165783581/274877906944)), (9/34359738368), by norm_num⟩
  | 5 => ⟨((-12262688879/68719476736), (-9875181595/137438953472)), (43/274877906944), by norm_num⟩
  | 6 => ⟨((47258306149/549755813888), (38057261315/1099511627776)), (85/1099511627776), by norm_num⟩
  | 7 => ⟨((-4878359765/137438953472), (-15714233327/1099511627776)), (9/274877906944), by norm_num⟩
  | 8 => ⟨((56401093159/4398046511104), (22709988103/4398046511104)), (27/2199023255552), by norm_num⟩
  | 9 => ⟨((-72453389681/17592186044416), (-29173470327/17592186044416)), (71/17592186044416), by norm_num⟩
  | 10 => ⟨((83766892519/70368744177664), (33728869885/70368744177664)), (85/70368744177664), by norm_num⟩
  | 11 => ⟨((-88042712867/281474976710656), (-35450535615/281474976710656)), (91/281474976710656), by norm_num⟩
  | 12 => ⟨((84825390253/1125899906842624), (533673057/17592186044416)), (45/562949953421312), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (62328357447/1267650600228229401496703205376)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((1778625297887227/633825300114114700748351602688), (295004119021/316912650057057350374175801344)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889580514493197/39614081257132168796771975168), (663633954653/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236168199742369/309485009821345068724781056), (352477600139/1237940039285380274899124224)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885505976335787/77371252455336267181195264), (88097488529/19342813113834066795298816)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193673246664835/1208925819614629174706176), (20642030539/302231454903657293676544)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314660568686783/151115727451828646838272), (577790737107/604462909807314587353088)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((235944292475221/9444732965739290427392), (469280561285/37778931862957161709568)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297361357012931/4722366482869645213696), (703615765777/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810601764086205/295147905179352825856), (30218006333/18446744073709551616)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227896166001521/9223372036854775808), (1207977518635/73786976294838206464)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822314036145263/9223372036854775808), (678977112429/4611686018427387904)), (417/2305843009213693952), by norm_num⟩
  | 6 => ⟨((796781639243541/576460752303423488), (84792486515/72057594037927936)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((149276478779091/18014398509481984), (1185662664257/144115188075855872)), (365/36028797018963968), by norm_num⟩
  | 4 => ⟨((745542826625145/18014398509481984), (443908423631/9007199254740992)), (1095/18014398509481984), by norm_num⟩
  | 3 => ⟨((744285438694769/4503599627370496), (2214545558783/9007199254740992)), (1369/4503599627370496), by norm_num⟩
  | 2 => ⟨((1113291546983881/2251799813685248), (4414137249005/4503599627370496)), (5479/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214077709336747/2251799813685248), (6583946239177/2251799813685248)), (8227/2251799813685248), by norm_num⟩
  | 0 => ⟨((2176766203839697/2251799813685248), (13019601797855/2251799813685248)), (8243/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2176766203839697/2251799813685248), (13019601797855/2251799813685248)), (31444553855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2104157557590951/2251799813685248), (25171535239307/2251799813685248)), (32065/2251799813685248), by norm_num⟩
  | 2 => ⟨((1965914285131737/2251799813685248), (47042259962953/2251799813685248)), (60643/2251799813685248), by norm_num⟩
  | 3 => ⟨((857670823753455/1125899906842624), (82139673610415/2251799813685248)), (54211/1125899906842624), by norm_num⟩
  | 4 => ⟨((1303690507410813/2251799813685248), (125142210422319/2251799813685248)), (173095/2251799813685248), by norm_num⟩
  | 5 => ⟨((747823299411223/2251799813685248), (72451694334667/1125899906842624)), (54917/562949953421312), by norm_num⟩
  | 6 => ⟨((956111092688217/9007199254740992), (384979622263047/9007199254740992)), (696701/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-79314155215/4294967296)), (1/2147483648), by norm_num⟩, -3, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-592793865/268435456), (-80797803803/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1978115058513073/18014398509481984), (73919461090257/18014398509481984)), (247563/4503599627370496), by norm_num⟩
  | 1 => ⟨((-11109235923/34359738368), (-3321095925/274877906944)), (23/137438953472), by norm_num⟩
  | 2 => ⟨((65420934561/137438953472), (1222345537/68719476736)), (35/137438953472), by norm_num⟩
  | 3 => ⟨((-4013082287/8589934592), (-4798829127/274877906944)), (71/274877906944), by norm_num⟩
  | 4 => ⟨((23632551825/68719476736), (883116221/68719476736)), (27/137438953472), by norm_num⟩
  | 5 => ⟨((-111335370833/549755813888), (-4160450919/549755813888)), (33/274877906944), by norm_num⟩
  | 6 => ⟨((109273401881/1099511627776), (63803093/17179869184)), (67/1099511627776), by norm_num⟩
  | 7 => ⟨((-11491030853/274877906944), (-3435233171/2199023255552)), (59/2199023255552), by norm_num⟩
  | 8 => ⟨((67669278309/4398046511104), (2528708613/4398046511104)), (45/4398046511104), by norm_num⟩
  | 9 => ⟨((-88554693665/17592186044416), (-827292023/4398046511104)), (61/17592186044416), by norm_num⟩
  | 10 => ⟨((52148778363/35184372088832), (3897457407/70368744177664)), (37/35184372088832), by norm_num⟩
  | 11 => ⟨((-55835962083/140737488355328), (-2086513729/140737488355328)), (81/281474976710656), by norm_num⟩
  | 12 => ⟨((109603722131/1125899906842624), (2047870785/562949953421312)), (41/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (48654181577/10141204801825835211973625643008)), (19/316912650057057350374175801344), by norm_num⟩
  | 17 => ⟨((889281491389121/316912650057057350374175801344), (57566988179/633825300114114700748351602688)), (721/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889510433746997/39614081257132168796771975168), (64750424701/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944635583686119/1237940039285380274899124224), (68781834155/2475880078570760549798248448)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885468778043927/77371252455336267181195264), (68764412691/154742504910672534362390528)), (431/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193664532826371/1208925819614629174706176), (8056016605/1208925819614629174706176)), (101/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258581313947815/604462909807314587353088), (56373619207/604462909807314587353088)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943727673046195/37778931862957161709568), (91572464217/75557863725914323419136)), (1149/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162160896353767/590295810358705651712), (17162257367/1180591620717411303424)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810550809064707/295147905179352825856), (11792896951/73786976294838206464)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823042084259713/73786976294838206464), (117855158557/73786976294838206464)), (1481/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822171084429361/9223372036854775808), (33121410685/2305843009213693952)), (833/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796710286660911/576460752303423488), (132358998475/1152921504606846976)), (1665/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194087240127577/144115188075855872), (115671812363/144115188075855872)), (1457/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490899320785741/36028797018963968), (86611752083/18014398509481984)), (1093/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488338926471559/9007199254740992), (27004115269/1125899906842624)), (683/2251799813685248), by norm_num⟩
  | 2 => ⟨((556530518985895/1125899906842624), (430580131543/4503599627370496)), (683/562949953421312), by norm_num⟩
  | 1 => ⟨((138337084770331/140737488355328), (10033885919/35184372088832)), (8197/2251799813685248), by norm_num⟩
  | 0 => ⟨((271928247723303/281474976710656), (158700981565/281474976710656)), (16397/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((271928247723303/281474976710656), (158700981565/281474976710656)), (62549599654387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2101641789632381/2251799813685248), (613273411843/562949953421312)), (31701/2251799813685248), by norm_num⟩
  | 2 => ⟨((245186770567771/281474976710656), (4579025268469/2251799813685248)), (14811/562949953421312), by norm_num⟩
  | 3 => ⟨((1708605874588795/2251799813685248), (3988689975373/1125899906842624)), (51727/1125899906842624), by norm_num⟩
  | 4 => ⟨((1296416483537605/2251799813685248), (1513255992477/281474976710656)), (78865/1125899906842624), by norm_num⟩
  | 5 => ⟨((1492627481517495/4503599627370496), (27878997065887/4503599627370496)), (366629/4503599627370496), by norm_num⟩
  | 6 => ⟨((1978115058513073/18014398509481984), (73919461090257/18014398509481984)), (247563/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-80797803803/4294967296)), (1/2147483648), by norm_num⟩, -3, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-9649929107/4294967296), (-82205333579/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((912527613899495/9007199254740992), (-34084061120749/1125899906842624)), (299257/4503599627370496), by norm_num⟩
  | 1 => ⟨((-83425550033/274877906944), (24928398905/274877906944)), (57/274877906944), by norm_num⟩
  | 2 => ⟨((3905009573/8589934592), (-9334851141/68719476736)), (11/34359738368), by norm_num⟩
  | 3 => ⟨((-31195635217/68719476736), (18643143221/137438953472)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((46726885607/137438953472), (-13962466457/137438953472)), (71/274877906944), by norm_num⟩
  | 5 => ⟨((-27996247851/137438953472), (16731124553/274877906944)), (45/274877906944), by norm_num⟩
  | 6 => ⟨((27956421075/274877906944), (-16707323265/549755813888)), (47/549755813888), by norm_num⟩
  | 7 => ⟨((-95714231849/2199023255552), (14300190717/1099511627776)), (83/2199023255552), by norm_num⟩
  | 8 => ⟨((71683553347/4398046511104), (-669367857/137438953472)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((-95442104109/17592186044416), (14259533455/8796093022208)), (87/17592186044416), by norm_num⟩
  | 10 => ⟨((57183798307/35184372088832), (-17087097831/35184372088832)), (27/17592186044416), by norm_num⟩
  | 11 => ⟨((-62293581859/140737488355328), (18613952885/140737488355328)), (15/35184372088832), by norm_num⟩
  | 12 => ⟨((62204964537/562949953421312), (-4646868283/140737488355328)), (61/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (-378232581091/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222312948499505/79228162514264337593543950336), (-447491399689/633825300114114700748351602688)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944721810817033/19807040628566084398385987584), (-503329520059/39614081257132168796771975168)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236150023481501/309485009821345068724781056), (-534665090821/2475880078570760549798248448)), (431/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885433292980945/77371252455336267181195264), (-534527308263/154742504910672534362390528)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549249738099101/9671406556917033397649408), (-125243251881/2417851639229258349412352)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157315389372619/75557863725914323419136), (-438205093873/604462909807314587353088)), (707/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887360791485215/75557863725914323419136), (-711809107587/75557863725914323419136)), (575/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324304067812261/1180591620717411303424), (-133404262855/1180591620717411303424)), (431/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810502078906401/295147905179352825856), (-366667014105/295147905179352825856)), (1185/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911460149386779/36893488147419103232), (-458041900227/36893488147419103232)), (741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822034130630727/9223372036854775808), (-257448068935/2305843009213693952)), (1667/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796641844055557/576460752303423488), (-257197682141/288230376151711744)), (417/288230376151711744), by norm_num⟩
  | 5 => ⟨((596983771362235/72057594037927936), (-899066455285/144115188075855872)), (1459/144115188075855872), by norm_num⟩
  | 4 => ⟨((372679982245117/9007199254740992), (-336588021325/9007199254740992)), (2189/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488114956708647/9007199254740992), (-419753537433/2251799813685248)), (2737/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225674946274349/4503599627370496), (-3346279728105/4503599627370496)), (5475/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212724686011927/2251799813685248), (-2495075228779/1125899906842624)), (8219/2251799813685248), by norm_num⟩
  | 0 => ⟨((2174096735092621/2251799813685248), (-2465959028483/562949953421312)), (16463/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2174096735092621/2251799813685248), (-2465959028483/562949953421312)), (62801369673918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099031756531705/2251799813685248), (-9523463746847/1125899906842624)), (31935/2251799813685248), by norm_num⟩
  | 2 => ⟨((1956466779465427/2251799813685248), (-1109670846145/70368744177664)), (30039/1125899906842624), by norm_num⟩
  | 3 => ⟨((1699307955194019/2251799813685248), (-3856531354927/140737488355328)), (106293/2251799813685248), by norm_num⟩
  | 4 => ⟨((1280682262931097/2251799813685248), (-46564952149329/1125899906842624)), (166253/2251799813685248), by norm_num⟩
  | 5 => ⟨((1449039892086679/4503599627370496), (-211865754422579/4503599627370496)), (202861/2251799813685248), by norm_num⟩
  | 6 => ⟨((912527613899495/9007199254740992), (-34084061120749/1125899906842624)), (299257/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-82205333579/4294967296)), (1/2147483648), by norm_num⟩, -3, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-4903546613/2147483648), (-83544175423/4294967296)), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((189179493591313/2251799813685248), (-65002716215253/1125899906842624)), (182237/2251799813685248), by norm_num⟩
  | 1 => ⟨((-70307765259/274877906944), (6039496705/34359738368)), (35/137438953472), by norm_num⟩
  | 2 => ⟨((53513392219/137438953472), (-18387383231/68719476736)), (55/137438953472), by norm_num⟩
  | 3 => ⟨((-54307574443/137438953472), (37320533879/137438953472)), (29/68719476736), by norm_num⟩
  | 4 => ⟨((41335157233/137438953472), (-3550725087/17179869184)), (23/68719476736), by norm_num⟩
  | 5 => ⟨((-50338325465/274877906944), (4324104879/34359738368)), (29/137438953472), by norm_num⟩
  | 6 => ⟨((51085387119/549755813888), (-35106224873/549755813888)), (61/549755813888), by norm_num⟩
  | 7 => ⟨((-22218658189/549755813888), (30537625523/1099511627776)), (55/1099511627776), by norm_num⟩
  | 8 => ⟨((67645203393/4398046511104), (-23243121525/2199023255552)), (43/2199023255552), by norm_num⟩
  | 9 => ⟨((-11441518863/2199023255552), (7862689445/2199023255552)), (15/2199023255552), by norm_num⟩
  | 10 => ⟨((1741698045/1099511627776), (-19150507549/17592186044416)), (75/35184372088832), by norm_num⟩
  | 11 => ⟨((-30851716525/70368744177664), (42403018129/140737488355328)), (85/140737488355328), by norm_num⟩
  | 12 => ⟨((62619162135/562949953421312), (-21516156687/281474976710656)), (11/70368744177664), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394307151/10141204801825835211973625643008), (-784287124487/10141204801825835211973625643008)), (607/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778446841632087/633825300114114700748351602688), (-115980404511/79228162514264337593543950336)), (361/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889379774715301/39614081257132168796771975168), (-260904115231/9903520314283042199192993792)), (203/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472283085021947/618970019642690137449562112), (-1108584289157/2475880078570760549798248448)), (863/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885399363252039/77371252455336267181195264), (-554146966609/77371252455336267181195264)), (863/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549186107448315/9671406556917033397649408), (-519358582201/4835703278458516698824704)), (809/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258467425769719/604462909807314587353088), (-908569239241/604462909807314587353088)), (177/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943635136659531/37778931862957161709568), (-1475847240937/75557863725914323419136)), (1151/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162143545295369/590295810358705651712), (-1106380130795/4722366482869645213696)), (863/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620910750238239/590295810358705651712), (-1520452038443/590295810358705651712)), (593/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911401745070593/36893488147419103232), (-474833727397/18446744073709551616)), (1483/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821902653513499/9223372036854775808), (-2135061670301/9223372036854775808)), (1669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796576063514277/576460752303423488), (-533237761483/288230376151711744)), (1669/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298463083179225/36028797018963968), (-465990116485/36028797018963968)), (1461/144115188075855872), by norm_num⟩
  | 4 => ⟨((745273463423961/18014398509481984), (-2791204174823/36028797018963968)), (2193/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487898378823645/9007199254740992), (-1740365872743/4503599627370496)), (1371/4503599627370496), by norm_num⟩
  | 2 => ⟨((278155102973411/562949953421312), (-1734176182949/1125899906842624)), (5489/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106035558323287/1125899906842624), (-2585843871611/562949953421312)), (8245/2251799813685248), by norm_num⟩
  | 0 => ⟨((2172780239691469/2251799813685248), (-20441312072317/2251799813685248)), (16543/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172780239691469/2251799813685248), (-20441312072317/2251799813685248)), (63106545455168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((32755438103233/35184372088832), (-39447981720373/2251799813685248)), (16113/1125899906842624), by norm_num⟩
  | 2 => ⟨((1950936725818247/2251799813685248), (-73449423526833/2251799813685248)), (61133/2251799813685248), by norm_num⟩
  | 3 => ⟨((1687876190072933/2251799813685248), (-127271684612287/2251799813685248)), (109919/2251799813685248), by norm_num⟩
  | 4 => ⟨((4913999678195/8796093022208), (-190797463275373/2251799813685248)), (88605/1125899906842624), by norm_num⟩
  | 5 => ⟨((1373230298356465/4503599627370496), (-426361417856063/4503599627370496)), (114015/1125899906842624), by norm_num⟩
  | 6 => ⟨((189179493591313/2251799813685248), (-65002716215253/1125899906842624)), (182237/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4903546613/2147483648), (-83544175423/4294967296)), (1/2147483648), by norm_num⟩, -3, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨14,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile014Terms2
