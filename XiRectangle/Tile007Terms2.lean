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
namespace Reinmann.XiRectangle.Tile007Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨7,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (423/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (423/128))
  have he : value ((3/4), (423/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-17862266831/8589934592), (-9838201653/1073741824)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-271851921206987/2251799813685248), (-291882043265757/9007199254740992)), (47607/562949953421312), by norm_num⟩
  | 1 => ⟨((11501061567/34359738368), (24696925701/274877906944)), (67/274877906944), by norm_num⟩
  | 2 => ⟨((-63775427189/137438953472), (-8559302209/68719476736)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((14735252515/34359738368), (7910474925/68719476736)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((-81709589885/274877906944), (-21932493565/274877906944)), (33/137438953472), by norm_num⟩
  | 5 => ⟨((90618834965/549755813888), (6080978431/137438953472)), (19/137438953472), by norm_num⟩
  | 6 => ⟨((-83749586615/1099511627776), (-2810008703/137438953472)), (9/137438953472), by norm_num⟩
  | 7 => ⟨((16585939953/549755813888), (17807996433/2199023255552)), (59/2199023255552), by norm_num⟩
  | 8 => ⟨((-91971980123/8796093022208), (-12343562519/4398046511104)), (21/2199023255552), by norm_num⟩
  | 9 => ⟨((56666772189/17592186044416), (7605249385/8796093022208)), (53/17592186044416), by norm_num⟩
  | 10 => ⟨((-62845461399/70368744177664), (-4217245735/17592186044416)), (61/70368744177664), by norm_num⟩
  | 11 => ⟨((31680839549/140737488355328), (17007546129/281474976710656)), (63/281474976710656), by norm_num⟩
  | 12 => ⟨((-29279312815/562949953421312), (-15718310197/1125899906842624)), (15/281474976710656), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326477/10141204801825835211973625643008), (-1875340024075/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889375552613255/316912650057057350374175801344), (-4438699510495/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889721434970045/39614081257132168796771975168), (-1248150407365/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889494529507313/2475880078570760549798248448), (-2651755431031/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771159988916829/154742504910672534362390528), (-5302241468779/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387380951653127/2417851639229258349412352), (-4969502805217/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258761928861935/604462909807314587353088), (-4346966560751/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943873498938245/37778931862957161709568), (-1765323200339/18889465931478580854784)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297504294609773/4722366482869645213696), (-2646879051307/2361183241434822606848)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621397541595221/590295810358705651712), (-7275324417713/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823408060784967/73786976294838206464), (-9088767309107/73786976294838206464)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822577415063329/9223372036854775808), (-2554364114941/2305843009213693952)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796910087208065/576460752303423488), (-5104100528537/576460752303423488)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194429336364425/144115188075855872), (-8921767802021/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491397395679499/36028797018963968), (-13361845999681/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488935238351567/9007199254740992), (-8332960660417/4503599627370496)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((278404526637905/562949953421312), (-16611389859913/2251799813685248)), (1397/2251799813685248), by norm_num⟩
  | 1 => ⟨((1107434798843053/1125899906842624), (-774403886647/35184372088832)), (2111/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088803047798983/1125899906842624), (-49018223727615/1125899906842624)), (1071/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1088803047798983/1125899906842624), (-49018223727615/1125899906842624)), (4085541845226199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1050794376523839/1125899906842624), (-94806280856687/1125899906842624)), (2165/281474976710656), by norm_num⟩
  | 2 => ⟨((243178941615573/281474976710656), (-44241013867173/281474976710656)), (2203/140737488355328), by norm_num⟩
  | 3 => ⟨((1625117259245453/2251799813685248), (-305774475697803/1125899906842624)), (35993/1125899906842624), by norm_num⟩
  | 4 => ⟨((31461139059835/70368744177664), (-882706135551155/2251799813685248)), (143005/2251799813685248), by norm_num⟩
  | 5 => ⟨((104089371657617/2251799813685248), (-789297600918657/2251799813685248)), (479977/4503599627370496), by norm_num⟩
  | 6 => ⟨((-271851921206987/2251799813685248), (-291882043265757/9007199254740992)), (47607/562949953421312), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-17862266831/8589934592), (-9838201653/1073741824)), (1/4294967296), by norm_num⟩, -1, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-18252837983/8589934592), (-40213283681/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-1073793339361435/9007199254740992), (-66545541922399/9007199254740992)), (691063/9007199254740992), by norm_num⟩
  | 1 => ⟨((23210797255/68719476736), (5753714519/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((-65761140509/137438953472), (-1018843797/34359738368)), (23/68719476736), by norm_num⟩
  | 3 => ⟨((62105113603/137438953472), (3848802455/137438953472)), (89/274877906944), by norm_num⟩
  | 4 => ⟨((-87978518297/274877906944), (-5452239237/274877906944)), (65/274877906944), by norm_num⟩
  | 5 => ⟨((99704764811/549755813888), (96545981/8589934592)), (19/137438953472), by norm_num⟩
  | 6 => ⟨((-5885101461/68719476736), (-5835421049/1099511627776)), (37/549755813888), by norm_num⟩
  | 7 => ⟨((19055711989/549755813888), (147616007/68719476736)), (61/2199023255552), by norm_num⟩
  | 8 => ⟨((-107977794975/8796093022208), (-6691642253/8796093022208)), (11/1099511627776), by norm_num⟩
  | 9 => ⟨((67983139907/17592186044416), (2106538903/8796093022208)), (29/8796093022208), by norm_num⟩
  | 10 => ⟨((-38522147831/35184372088832), (-596827413/8796093022208)), (17/17592186044416), by norm_num⟩
  | 11 => ⟨((79375609655/281474976710656), (4919096409/281474976710656)), (9/35184372088832), by norm_num⟩
  | 12 => ⟨((-37481339411/562949953421312), (-4645616529/1125899906842624)), (69/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572467/10141204801825835211973625643008), (-1002913084795/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778679496747609/633825300114114700748351602688), (-4747187933627/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944820402910809/19807040628566084398385987584), (-83430646663/618970019642690137449562112)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889408767610355/2475880078570760549798248448), (-2836025194409/1237940039285380274899124224)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221384265251901/19342813113834066795298816), (-5670662579099/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193680399364765/1208925819614629174706176), (-332173235539/604462909807314587353088)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629345641130053/302231454903657293676544), (-2324475532389/302231454903657293676544)), (357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943815994276989/37778931862957161709568), (-7551781648209/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297417855320361/4722366482869645213696), (-5661418238095/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621278391756153/590295810358705651712), (-1945130374355/147573952589676412928)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823258680491933/73786976294838206464), (-9719760171457/73786976294838206464)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455602188575535/2305843009213693952), (-2731657752599/2305843009213693952)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593650755517507/1152921504606846976), (-10916509898845/1152921504606846976)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194280244364777/144115188075855872), (-9540563866143/144115188075855872)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491172062850219/36028797018963968), (-14288091137167/36028797018963968)), (1111/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488650620063621/9007199254740992), (-17820315714139/9007199254740992)), (1393/9007199254740992), by norm_num⟩
  | 2 => ⟨((556664543622583/1125899906842624), (-17760663584331/2251799813685248)), (1399/2251799813685248), by norm_num⟩
  | 1 => ⟨((138373795362165/140737488355328), (-26492024434957/1125899906842624)), (529/281474976710656), by norm_num⟩
  | 0 => ⟨((1087871119762875/1125899906842624), (-26194565671475/562949953421312)), (4297/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1087871119762875/1125899906842624), (-26194565671475/562949953421312)), (16391758445357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1048689093013933/1125899906842624), (-50619617810685/562949953421312)), (8705/1125899906842624), by norm_num⟩
  | 2 => ⟨((967669882869503/1125899906842624), (-188593109451315/1125899906842624)), (17783/1125899906842624), by norm_num⟩
  | 3 => ⟨((1600173578140417/2251799813685248), (-324177790625323/1125899906842624)), (73051/2251799813685248), by norm_num⟩
  | 4 => ⟨((237608879287681/562949953421312), (-921468652809981/2251799813685248)), (145891/2251799813685248), by norm_num⟩
  | 5 => ⟨((48159870891349/4503599627370496), (-1555727165885719/4503599627370496)), (485113/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1073793339361435/9007199254740992), (-66545541922399/9007199254740992)), (691063/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18252837983/8589934592), (-40213283681/4294967296)), (1/4294967296), by norm_num⟩, -1, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-4655269565/2147483648), (-20512281521/2147483648)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-511203375919877/4503599627370496), (130545643021079/9007199254740992)), (675353/9007199254740992), by norm_num⟩
  | 1 => ⟨((45091790781/137438953472), (-11515058585/274877906944)), (31/137438953472), by norm_num⟩
  | 2 => ⟨((-65166019293/137438953472), (8320700031/137438953472)), (47/137438953472), by norm_num⟩
  | 3 => ⟨((62784673913/137438953472), (-1002079849/17179869184)), (47/137438953472), by norm_num⟩
  | 4 => ⟨((-45367762077/137438953472), (11585533179/274877906944)), (35/137438953472), by norm_num⟩
  | 5 => ⟨((52451879291/274877906944), (-1674324895/68719476736)), (83/549755813888), by norm_num⟩
  | 6 => ⟨((-101070287035/1099511627776), (12905123707/1099511627776)), (41/549755813888), by norm_num⟩
  | 7 => ⟨((83465915203/2199023255552), (-10657315741/2199023255552)), (35/1099511627776), by norm_num⟩
  | 8 => ⟨((-120623762025/8796093022208), (1925225277/1099511627776)), (13/1099511627776), by norm_num⟩
  | 9 => ⟨((9684653197/2199023255552), (-9660793/17179869184)), (69/17592186044416), by norm_num⟩
  | 10 => ⟨((-44787596937/35184372088832), (5718688409/35184372088832)), (41/35184372088832), by norm_num⟩
  | 11 => ⟨((94147494757/281474976710656), (-1502648679/35184372088832)), (89/281474976710656), by norm_num⟩
  | 12 => ⟨((-90707086641/1125899906842624), (180967221/17592186044416)), (11/140737488355328), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996580325/5070602400912917605986812821504), (3926846823665/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((111163370242455/39614081257132168796771975168), (2323252278731/316912650057057350374175801344)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59048971252941/1237940039285380274899124224), (5226297261447/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889330488549017/2475880078570760549798248448), (5551709360399/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770995904280295/154742504910672534362390528), (5550323960799/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549369930928247/9671406556917033397649408), (1300489226045/2417851639229258349412352)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258627241380089/604462909807314587353088), (4550240681741/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943764022076565/37778931862957161709568), (7391382264917/75557863725914323419136)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648670001870529/2361183241434822606848), (5541123136413/4722366482869645213696)), (435/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810585759577555/295147905179352825856), (7615123072393/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823125349543359/73786976294838206464), (2378255844975/18446744073709551616)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822259113924297/9223372036854775808), (10694067947771/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398375390219827/288230376151711744), (2670991794983/288230376151711744)), (843/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194150199915537/144115188075855872), (2334278160143/36028797018963968)), (739/144115188075855872), by norm_num⟩
  | 4 => ⟨((11648265596863/281474976710656), (13982963517845/36028797018963968)), (1111/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488409784016967/9007199254740992), (8719498305981/4503599627370496)), (87/562949953421312), by norm_num⟩
  | 2 => ⟨((556545432487135/1125899906842624), (8689744329333/1125899906842624)), (699/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106639540256201/1125899906842624), (25920652238347/1125899906842624)), (1057/562949953421312), by norm_num⟩
  | 0 => ⟨((1087195375144493/1125899906842624), (3203007813003/70368744177664)), (1073/281474976710656), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1087195375144493/1125899906842624), (3203007813003/70368744177664)), (4093171239757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((261872171374019/281474976710656), (12371598077893/140737488355328)), (8681/1125899906842624), by norm_num⟩
  | 2 => ⟨((965838017693555/1125899906842624), (184160015352545/1125899906842624)), (1105/70368744177664), by norm_num⟩
  | 3 => ⟨((399204298581231/562949953421312), (631916720431451/2251799813685248)), (72235/2251799813685248), by norm_num⟩
  | 4 => ⟨((477508346315077/1125899906842624), (896221305671891/2251799813685248)), (142991/2251799813685248), by norm_num⟩
  | 5 => ⟨((96673117921505/4503599627370496), (1520395022693761/4503599627370496)), (470221/4503599627370496), by norm_num⟩
  | 6 => ⟨((-511203375919877/4503599627370496), (130545643021079/9007199254740992)), (675353/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4655269565/2147483648), (-20512281521/2147483648)), (1/4294967296), by norm_num⟩, -2, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-18969403681/8589934592), (-83583934969/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-943867817653265/9007199254740992), (297849560065695/9007199254740992)), (676811/9007199254740992), by norm_num⟩
  | 1 => ⟨((21203317211/68719476736), (-13381955789/137438953472)), (63/274877906944), by norm_num⟩
  | 2 => ⟨((-15607968421/34359738368), (19701176121/137438953472)), (3/8589934592), by norm_num⟩
  | 3 => ⟨((61275614139/137438953472), (-19336303635/137438953472)), (49/137438953472), by norm_num⟩
  | 4 => ⟨((-22552788343/68719476736), (7116820767/68719476736)), (37/137438953472), by norm_num⟩
  | 5 => ⟨((53124247269/274877906944), (-16764035579/274877906944)), (45/274877906944), by norm_num⟩
  | 6 => ⟨((-104280736265/1099511627776), (32907119871/1099511627776)), (91/1099511627776), by norm_num⟩
  | 7 => ⟨((43864037805/1099511627776), (-13841858063/1099511627776)), (79/2199023255552), by norm_num⟩
  | 8 => ⟨((-64577491349/4398046511104), (5094563303/1099511627776)), (15/1099511627776), by norm_num⟩
  | 9 => ⟨((21127164745/4398046511104), (-13333894019/8796093022208)), (81/17592186044416), by norm_num⟩
  | 10 => ⟨((-99532235831/70368744177664), (31408669835/70368744177664)), (49/35184372088832), by norm_num⟩
  | 11 => ⟨((26642417715/70368744177664), (-16814711227/140737488355328)), (27/70368744177664), by norm_num⟩
  | 12 => ⟨((-26148991073/281474976710656), (16503297053/562949953421312)), (55/562949953421312), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171716351/10141204801825835211973625643008), (1847051167457/5070602400912917605986812821504)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889276376954889/316912650057057350374175801344), (4370813330951/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889498353143565/39614081257132168796771975168), (2458096190575/19807040628566084398385987584)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((472314395155635/618970019642690137449562112), (5222274860643/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770923125052259/154742504910672534362390528), (1305236990923/38685626227668133590597632)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549301837070293/9671406556917033397649408), (4893229106089/9671406556917033397649408)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629283897919933/302231454903657293676544), (535020762853/75557863725914323419136)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887431701072033/75557863725914323419136), (434539242399/4722366482869645213696)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297267970185783/4722366482869645213696), (1303039911491/1180591620717411303424)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621072836289427/590295810358705651712), (7162964688845/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911501270146595/36893488147419103232), (4474037668555/36893488147419103232)), (187/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822121701036355/9223372036854775808), (10058845569687/9223372036854775808)), (421/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593365080982967/1152921504606846976), (5024587886429/576460752303423488)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194031827688389/144115188075855872), (8782156040871/144115188075855872)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((186350316073781/4503599627370496), (13151502967793/36028797018963968)), (555/18014398509481984), by norm_num⟩
  | 3 => ⟨((186024262102725/1125899906842624), (16401381824837/9007199254740992)), (1391/9007199254740992), by norm_num⟩
  | 2 => ⟨((556440313702607/1125899906842624), (16344451722827/2251799813685248)), (1397/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106337731997359/1125899906842624), (1523411335581/70368744177664)), (1055/562949953421312), by norm_num⟩
  | 0 => ⟨((67915343476829/70368744177664), (24091079044991/562949953421312)), (4281/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((67915343476829/70368744177664), (24091079044991/562949953421312)), (16330723289107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046697762075475/1125899906842624), (93004581917057/1125899906842624)), (8631/1125899906842624), by norm_num⟩
  | 2 => ⟨((120673066303505/140737488355328), (86462115472007/562949953421312)), (17475/1125899906842624), by norm_num⟩
  | 3 => ⟨((1602388447605187/2251799813685248), (74135532152971/281474976710656)), (70671/2251799813685248), by norm_num⟩
  | 4 => ⟨((246014297916807/562949953421312), (844081571066963/2251799813685248)), (137807/2251799813685248), by norm_num⟩
  | 5 => ⟨((56820072615231/1125899906842624), (737742791623057/2251799813685248)), (447519/4503599627370496), by norm_num⟩
  | 6 => ⟨((-943867817653265/9007199254740992), (297849560065695/9007199254740992)), (676811/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-18969403681/8589934592), (-83583934969/8589934592)), (1/4294967296), by norm_num⟩, -2, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-9649929107/4294967296), (-42520000127/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-423439699552197/4503599627370496), (108930085301471/2251799813685248)), (668679/9007199254740992), by norm_num⟩
  | 1 => ⟨((77423826529/274877906944), (-39834640149/274877906944)), (63/274877906944), by norm_num⟩
  | 2 => ⟨((-57985263969/137438953472), (29833479275/137438953472)), (49/137438953472), by norm_num⟩
  | 3 => ⟨((28951387777/68719476736), (-29791038899/137438953472)), (51/137438953472), by norm_num⟩
  | 4 => ⟨((-10841325841/34359738368), (22311494173/137438953472)), (79/274877906944), by norm_num⟩
  | 5 => ⟨((3247770971/17179869184), (-13367852633/137438953472)), (49/274877906944), by norm_num⟩
  | 6 => ⟨((-25945206173/274877906944), (26697671707/549755813888)), (51/549755813888), by norm_num⟩
  | 7 => ⟨((44414223701/1099511627776), (-22851164789/1099511627776)), (89/2199023255552), by norm_num⟩
  | 8 => ⟨((-66526561673/4398046511104), (34227985923/4398046511104)), (69/4398046511104), by norm_num⟩
  | 9 => ⟨((88575896823/17592186044416), (-45572392039/17592186044416)), (47/8796093022208), by norm_num⟩
  | 10 => ⟨((-26534967277/17592186044416), (27304537123/35184372088832)), (29/17592186044416), by norm_num⟩
  | 11 => ⟨((3613257175/8796093022208), (-29744393845/140737488355328)), (65/140737488355328), by norm_num⟩
  | 12 => ⟨((-57729872703/562949953421312), (3712760025/70368744177664)), (67/562949953421312), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790524530142089/5070602400912917605986812821504), (3473298837061/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778494651063485/633825300114114700748351602688), (4109300562239/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118089566740831/2475880078570760549798248448), (4622037133269/39614081257132168796771975168)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944594159164237/1237940039285380274899124224), (4909786612897/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885426989467421/77371252455336267181195264), (4908517942703/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549237135954681/9671406556917033397649408), (2300193928989/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314627826414133/151115727451828646838272), (4023991941833/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887340135535331/75557863725914323419136), (25533051019/295147905179352825856)), (289/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297199498005277/4722366482869645213696), (4900136275783/4722366482869645213696)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620979014940603/590295810358705651712), (6734098023973/590295810358705651712)), (299/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455721438730587/18446744073709551616), (1051530056069/9223372036854775808)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821990992185297/9223372036854775808), (4728186657769/4611686018427387904)), (841/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593235214195491/1152921504606846976), (1180891448951/144115188075855872)), (421/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193919139783761/144115188075855872), (4127924878319/72057594037927936)), (369/72057594037927936), by norm_num⟩
  | 4 => ⟨((372658845834229/9007199254740992), (193172035337/562949953421312)), (1109/36028797018963968), by norm_num⟩
  | 3 => ⟨((743994228385907/4503599627370496), (15417462111935/9007199254740992)), (695/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112679904568829/2251799813685248), (15363085019235/2251799813685248)), (1395/2251799813685248), by norm_num⟩
  | 1 => ⟨((553024435321365/562949953421312), (11454472093435/562949953421312)), (2107/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086116244368035/1125899906842624), (22638357497251/562949953421312)), (2135/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1086116244368035/1125899906842624), (22638357497251/562949953421312)), (8144380809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((522958794206577/562949953421312), (21838431350907/281474976710656)), (8583/1125899906842624), by norm_num⟩
  | 2 => ⟨((482419850027547/562949953421312), (162296483475663/1125899906842624)), (135/8796093022208), by norm_num⟩
  | 3 => ⟨((803424436538547/1125899906842624), (17384992383091/70368744177664)), (69197/2251799813685248), by norm_num⟩
  | 4 => ⟨((1009180130442445/2251799813685248), (793962028047407/2251799813685248)), (132947/2251799813685248), by norm_num⟩
  | 5 => ⟨((344674363449363/4503599627370496), (1423307166403785/4503599627370496)), (425833/4503599627370496), by norm_num⟩
  | 6 => ⟨((-423439699552197/4503599627370496), (108930085301471/2251799813685248)), (668679/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-9649929107/4294967296), (-42520000127/4294967296)), (1/4294967296), by norm_num⟩, -2, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-19614186453/8589934592), (-86425009059/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((-738423773086627/9007199254740992), (545687660896579/9007199254740992)), (326617/4503599627370496), by norm_num⟩
  | 1 => ⟨((34304012233/137438953472), (-12675158139/68719476736)), (63/274877906944), by norm_num⟩
  | 2 => ⟨((-26109833737/68719476736), (9647450839/34359738368)), (25/68719476736), by norm_num⟩
  | 3 => ⟨((13248662443/34359738368), (-39162507395/137438953472)), (13/34359738368), by norm_num⟩
  | 4 => ⟨((-20167925039/68719476736), (1862986445/8589934592)), (21/68719476736), by norm_num⟩
  | 5 => ⟨((49121360243/274877906944), (-36300185811/274877906944)), (53/274877906944), by norm_num⟩
  | 6 => ⟨((-6231295143/68719476736), (36838910065/549755813888)), (55/549755813888), by norm_num⟩
  | 7 => ⟨((43363012295/1099511627776), (-32044825221/1099511627776)), (49/1099511627776), by norm_num⟩
  | 8 => ⟨((-33004915975/2199023255552), (48780594699/4398046511104)), (77/4398046511104), by norm_num⟩
  | 9 => ⟨((44659647663/8796093022208), (-33003025575/8796093022208)), (27/4398046511104), by norm_num⟩
  | 10 => ⟨((-13596729937/8796093022208), (20095690375/17592186044416)), (17/8796093022208), by norm_num⟩
  | 11 => ⟨((60211708179/140737488355328), (-44495840181/140737488355328)), (77/140737488355328), by norm_num⟩
  | 12 => ⟨((-61105298855/562949953421312), (22578097303/281474976710656)), (5/35184372088832), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288375/1267650600228229401496703205376), (815817656207/2535301200456458802993406410752)), (305/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889219659656207/316912650057057350374175801344), (3860580496909/633825300114114700748351602688)), (363/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118085680767637/2475880078570760549798248448), (1085568155115/9903520314283042199192993792)), (51/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889122350318849/2475880078570760549798248448), (4612588199167/2475880078570760549798248448)), (217/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770788116087595/154742504910672534362390528), (4611377381209/154742504910672534362390528)), (217/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549175501207307/9671406556917033397649408), (2160940036135/4835703278458516698824704)), (407/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258457486853581/604462909807314587353088), (3780359145629/604462909807314587353088)), (89/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887252889081759/75557863725914323419136), (1535168291093/18889465931478580854784)), (579/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162141780747257/590295810358705651712), (2301698190131/2361183241434822606848)), (217/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810444795095967/295147905179352825856), (3163122468795/295147905179352825856)), (597/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822774418675825/73786976294838206464), (7902670672339/73786976294838206464)), (747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227733293694209/1152921504606846976), (8883446653643/9223372036854775808)), (105/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796555666834257/576460752303423488), (8874629528133/1152921504606846976)), (841/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298452900009503/36028797018963968), (7755388710157/144115188075855872)), (737/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490475781021243/36028797018963968), (11613276666625/36028797018963968)), (1107/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487791932378671/9007199254740992), (14481974829833/9007199254740992)), (347/2251799813685248), by norm_num⟩
  | 2 => ⟨((278121957348089/562949953421312), (14430123761621/2251799813685248)), (697/1125899906842624), by norm_num⟩
  | 1 => ⟨((552885908072237/562949953421312), (10757919858971/562949953421312)), (2103/1125899906842624), by norm_num⟩
  | 0 => ⟨((1085605980581797/1125899906842624), (42515987921957/1125899906842624)), (4259/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1085605980581797/1125899906842624), (42515987921957/1125899906842624)), (16246799949264171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((261287155433273/281474976710656), (81988834847415/1125899906842624)), (1067/140737488355328), by norm_num⟩
  | 2 => ⟨((1928436916768819/2251799813685248), (304433874512277/2251799813685248)), (17091/1125899906842624), by norm_num⟩
  | 3 => ⟨((1610351389128027/2251799813685248), (260716569366633/1125899906842624)), (33895/1125899906842624), by norm_num⟩
  | 4 => ⟨((1030881637075139/2251799813685248), (372897525878325/1125899906842624)), (128355/2251799813685248), by norm_num⟩
  | 5 => ⟨((449868311877223/4503599627370496), (1365710076366315/4503599627370496)), (405091/4503599627370496), by norm_num⟩
  | 6 => ⟨((-738423773086627/9007199254740992), (545687660896579/9007199254740992)), (326617/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-19614186453/8589934592), (-86425009059/8589934592)), (1/4294967296), by norm_num⟩, -2, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨7,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile007Terms2
