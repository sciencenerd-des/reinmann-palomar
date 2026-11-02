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
namespace Reinmann.XiRectangle.Tile032Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-45376701/16777216), (-325618345/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((131898297461701/4503599627370496), (-135425055197589/2251799813685248)), (82454735/9007199254740992), by norm_num⟩
  | 1 => ⟨((-194408053/2147483648), (399212451/2147483648)), (123/4294967296), by norm_num⟩
  | 2 => ⟨((600923545/4294967296), (-616991317/2147483648)), (3/67108864), by norm_num⟩
  | 3 => ⟨((-619160063/4294967296), (1271430903/4294967296)), (25/536870912), by norm_num⟩
  | 4 => ⟨((239231255/2147483648), (-245627931/1073741824)), (39/1073741824), by norm_num⟩
  | 5 => ⟨((-147894793/2147483648), (303698545/2147483648)), (195/8589934592), by norm_num⟩
  | 6 => ⟨((38095757/1073741824), (-39114379/536870912)), (203/17179869184), by norm_num⟩
  | 7 => ⟨((-134577831/8589934592), (276352471/8589934592)), (181/34359738368), by norm_num⟩
  | 8 => ⟨((415985789/68719476736), (-213554305/17179869184)), (141/68719476736), by norm_num⟩
  | 9 => ⟨((-285739941/137438953472), (73345047/17179869184)), (49/68719476736), by norm_num⟩
  | 10 => ⟨((353293715/549755813888), (-725480493/549755813888)), (123/549755813888), by norm_num⟩
  | 11 => ⟨((-198553795/1099511627776), (407725637/1099511627776)), (35/549755813888), by norm_num⟩
  | 12 => ⟨((204579403/4398046511104), (-840198169/8796093022208)), (73/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (-727912240005/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((27778074130461/9903520314283042199192993792), (-1721101114231/633825300114114700748351602688)), (46185/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472162127892073/9903520314283042199192993792), (-1935786834705/39614081257132168796771975168)), (103927/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944177743813731/1237940039285380274899124224), (-1028103119357/1237940039285380274899124224)), (110435/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221252750377761/19342813113834066795298816), (-2055568364553/154742504910672534362390528)), (55225/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48389314569383/302231454903657293676544), (-1926417864777/9671406556917033397649408)), (103561/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157228815840999/75557863725914323419136), (-1684938452127/604462909807314587353088)), (11329/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((235779446163167/9444732965739290427392), (-684188976199/18889465931478580854784)), (18413/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296372559158065/4722366482869645213696), (-2051457115081/4722366482869645213696)), (13813/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809922193063007/295147905179352825856), (-176184454339/36893488147419103232)), (151983/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113841942682333/4611686018427387904), (-3520987760115/73786976294838206464)), (95019/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910202224365011/4611686018427387904), (-3957400265431/9223372036854775808)), (53469/2305843009213693952), by norm_num⟩
  | 6 => ⟨((99478428991293/72057594037927936), (-3952766593959/1152921504606846976)), (106991/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192543286673499/144115188075855872), (-3453464803819/144115188075855872)), (187351/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488585476012177/36028797018963968), (-5169802536873/36028797018963968)), (281263/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485450271654763/9007199254740992), (-6444101278083/9007199254740992)), (351993/9007199254740992), by norm_num⟩
  | 2 => ⟨((1110177863203807/2251799813685248), (-802118854189/281474976710656)), (705229/4503599627370496), by norm_num⟩
  | 1 => ⟨((1102385627539729/1125899906842624), (-597363768895/70368744177664)), (530485/1125899906842624), by norm_num⟩
  | 0 => ⟨((1079145802410809/1125899906842624), (-37693664113533/2251799813685248)), (2134521/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079145802410809/1125899906842624), (-37693664113533/2251799813685248)), (8142551430709075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258504431145899/281474976710656), (-18064198761537/562949953421312)), (1040807/562949953421312), by norm_num⟩
  | 2 => ⟨((948474537705703/1125899906842624), (-132720158062443/2251799813685248)), (7914137/2251799813685248), by norm_num⟩
  | 3 => ⟨((795097577632313/1125899906842624), (-223610801985969/2251799813685248)), (7133441/1125899906842624), by norm_num⟩
  | 4 => ⟨((1100772291567811/2251799813685248), (-157911379076359/1125899906842624)), (11491855/1125899906842624), by norm_num⟩
  | 5 => ⟨((987614988293703/4503599627370496), (-617548574448239/4503599627370496)), (57835711/4503599627370496), by norm_num⟩
  | 6 => ⟨((131898297461701/4503599627370496), (-135425055197589/2251799813685248)), (82454735/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-325618345/8388608)), (1/16777216), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-5753657/2097152), (-660602015/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-1683355639/536870912), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-30381193283727/4503599627370496), (-1152676924844971/18014398509481984)), (194010259/18014398509481984), by norm_num⟩
  | 1 => ⟨((181694137/8589934592), (861695249/4294967296)), (73/2147483648), by norm_num⟩
  | 2 => ⟨((-142425229/4294967296), (-675460117/2147483648)), (231/4294967296), by norm_num⟩
  | 3 => ⟨((148857827/4294967296), (1411934193/4294967296)), (243/4294967296), by norm_num⟩
  | 4 => ⟨((-58342857/2147483648), (-553388937/2147483648)), (3/67108864), by norm_num⟩
  | 5 => ⟨((146346953/8589934592), (1388118249/8589934592)), (243/8589934592), by norm_num⟩
  | 6 => ⟨((-152956675/17179869184), (-1450812247/17179869184)), (1/67108864), by norm_num⟩
  | 7 => ⟨((137027077/34359738368), (1299718117/34359738368)), (231/34359738368), by norm_num⟩
  | 8 => ⟨((-53705951/34359738368), (-1018814659/68719476736)), (183/68719476736), by norm_num⟩
  | 9 => ⟨((149684177/274877906944), (1419772209/274877906944)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((-46933387/274877906944), (-1780675019/1099511627776)), (325/1099511627776), by norm_num⟩
  | 11 => ⟨((3344531/68719476736), (15861637/34359738368)), (187/2199023255552), by norm_num⟩
  | 12 => ⟨((-27964687/2199023255552), (-265248379/2199023255552)), (197/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (-1091482139101/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777734865029719/633825300114114700748351602688), (-1290286321515/316912650057057350374175801344)), (92455/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236072350656765/4951760157141521099596496896), (-2902454297517/39614081257132168796771975168)), (26007/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((236035162407327/309485009821345068724781056), (-3082994562149/2475880078570760549798248448)), (110549/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769947673755927/154742504910672534362390528), (-770505990629/38685626227668133590597632)), (55285/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548388232967445/9671406556917033397649408), (-722091645511/2417851639229258349412352)), (51841/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628884636610485/302231454903657293676544), (-631572575795/151115727451828646838272)), (90745/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886135752540203/75557863725914323419136), (-2051645271925/37778931862957161709568)), (73751/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324074363018445/1180591620717411303424), (-1537889507449/2361183241434822606848)), (13833/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1619740717171467/590295810358705651712), (-2113226696105/295147905179352825856)), (152223/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227667612841259/9223372036854775808), (-5278955579819/73786976294838206464)), (95185/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820257181024343/9223372036854775808), (-5933177003811/9223372036854775808)), (214291/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397876645006855/288230376151711744), (-2963062100967/576460752303423488)), (214447/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192412398766493/144115188075855872), (-647179275387/18014398509481984)), (93909/72057594037927936), by norm_num⟩
  | 4 => ⟨((744193437001339/18014398509481984), (-7750327150955/36028797018963968)), (282079/36028797018963968), by norm_num⟩
  | 3 => ⟨((742599033240313/4503599627370496), (-9660272378765/9007199254740992)), (176609/4503599627370496), by norm_num⟩
  | 2 => ⟨((277479942274413/562949953421312), (-19237857532395/4503599627370496)), (354147/2251799813685248), by norm_num⟩
  | 1 => ⟨((2203967807313667/2251799813685248), (-7162711278101/562949953421312)), (266777/562949953421312), by norm_num⟩
  | 0 => ⟨((539142428268581/562949953421312), (-7060321630189/281474976710656)), (134561/140737488355328), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((539142428268581/562949953421312), (-7060321630189/281474976710656)), (513309479296636537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2063950186888911/2251799813685248), (-108187775483011/2251799813685248)), (4231859/2251799813685248), by norm_num⟩
  | 2 => ⟨((1886573465978895/2251799813685248), (-198325071411937/2251799813685248)), (4082149/1125899906842624), by norm_num⟩
  | 3 => ⟨((781558508707885/1125899906842624), (-166158117204831/1125899906842624)), (15118337/2251799813685248), by norm_num⟩
  | 4 => ⟨((129502005257329/281474976710656), (-461363535081879/2251799813685248)), (25451463/2251799813685248), by norm_num⟩
  | 5 => ⟨((764253485296593/4503599627370496), (-849063083957637/4503599627370496)), (33848925/2251799813685248), by norm_num⟩
  | 6 => ⟨((-30381193283727/4503599627370496), (-1152676924844971/18014398509481984)), (194010259/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-660602015/16777216)), (1/16777216), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-93308067/33554432), (-669568693/16777216)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-853102329/268435456), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-666434138215383/18014398509481984), (-896033110754975/18014398509481984)), (204229367/18014398509481984), by norm_num⟩
  | 1 => ⟨((63120233/536870912), (678930631/4294967296)), (157/4294967296), by norm_num⟩
  | 2 => ⟨((-802397993/4294967296), (-539419523/2147483648)), (251/4294967296), by norm_num⟩
  | 3 => ⟨((425010669/2147483648), (1142869521/4294967296)), (67/1073741824), by norm_num⟩
  | 4 => ⟨((-42209587/268435456), (-908025215/4294967296)), (215/4294967296), by norm_num⟩
  | 5 => ⟨((429261887/4294967296), (1154301205/8589934592)), (69/2147483648), by norm_num⟩
  | 6 => ⟨((-56842391/1073741824), (-1222810455/17179869184)), (147/8589934592), by norm_num⟩
  | 7 => ⟨((206455061/8589934592), (277582675/8589934592)), (269/34359738368), by norm_num⟩
  | 8 => ⟨((-656125297/68719476736), (-882172683/68719476736)), (27/8589934592), by norm_num⟩
  | 9 => ⟨((231689057/68719476736), (623020505/137438953472)), (77/68719476736), by norm_num⟩
  | 10 => ⟨((-147264059/137438953472), (-791997081/549755813888)), (197/549755813888), by norm_num⟩
  | 11 => ⟨((680746337/2199023255552), (457638065/1099511627776)), (229/2199023255552), by norm_num⟩
  | 12 => ⟨((-721149501/8796093022208), (-969598937/8796093022208)), (61/2199023255552), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (-2879152443735/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777674880473073/633825300114114700748351602688), (-3403356146567/633825300114114700748351602688)), (11567/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888511194710319/39614081257132168796771975168), (-3827848612259/39614081257132168796771975168)), (26031/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888209288896879/2475880078570760549798248448), (-4065934764229/2475880078570760549798248448)), (55329/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27654304183131/2417851639229258349412352), (-2032318275981/77371252455336267181195264)), (110685/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774160166048333/4835703278458516698824704), (-1904608940779/4835703278458516698824704)), (103797/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39303426639423/18889465931478580854784), (-208230455181/37778931862957161709568)), (90853/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886038480204753/75557863725914323419136), (-2705704256547/37778931862957161709568)), (147691/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296224158252059/4722366482869645213696), (-2028148543983/2361183241434822606848)), (55409/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809819693609725/295147905179352825856), (-1393434804567/147573952589676412928)), (76227/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455303353840693/18446744073709551616), (-435104609023/4611686018427387904)), (190687/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820112625884953/9223372036854775808), (-3912162994353/4611686018427387904)), (214687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591360613704533/1152921504606846976), (-3907444315337/576460752303423488)), (107447/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192283095635869/144115188075855872), (-6827422697727/144115188075855872)), (188265/144115188075855872), by norm_num⟩
  | 4 => ⟨((744094883271619/18014398509481984), (-10219954749759/36028797018963968)), (282861/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484946192723283/9007199254740992), (-12737948030645/9007199254740992)), (354391/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219319433642139/4503599627370496), (-3170647872413/562949953421312)), (711233/4503599627370496), by norm_num⟩
  | 1 => ⟨((550786786430149/562949953421312), (-37771946331637/2251799813685248)), (1072997/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077384342614681/1125899906842624), (-74446296190919/2251799813685248)), (1085349/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077384342614681/1125899906842624), (-74446296190919/2251799813685248)), (4140277866843795421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((514864355130987/562949953421312), (-71238369764749/1125899906842624)), (2148927/1125899906842624), by norm_num⟩
  | 2 => ⟨((468632382415923/562949953421312), (-130306778023873/1125899906842624)), (4202679/1125899906842624), by norm_num⟩
  | 3 => ⟨((95644090758055/140737488355328), (-433899855283005/2251799813685248)), (15939821/2251799813685248), by norm_num⟩
  | 4 => ⟨((478187643349229/1125899906842624), (-589749861583679/2251799813685248)), (27808051/2251799813685248), by norm_num⟩
  | 5 => ⟨((251731431153241/2251799813685248), (-500952340012321/2251799813685248)), (76373979/4503599627370496), by norm_num⟩
  | 6 => ⟨((-666434138215383/18014398509481984), (-896033110754975/18014398509481984)), (204229367/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-669568693/16777216)), (1/16777216), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-47253303/16777216), (-1356338561/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-54003775/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-984450107999549/18014398509481984), (-219026753259595/9007199254740992)), (96963091/9007199254740992), by norm_num⟩
  | 1 => ⟨((755506195/4294967296), (21011231/268435456)), (151/4294967296), by norm_num⟩
  | 2 => ⟨((-607970157/2147483648), (-135265087/1073741824)), (245/4294967296), by norm_num⟩
  | 3 => ⟨((1304653627/4294967296), (290267679/2147483648)), (265/4294967296), by norm_num⟩
  | 4 => ⟨((-1049879505/4294967296), (-467167807/4294967296)), (215/4294967296), by norm_num⟩
  | 5 => ⟨((1351772703/8589934592), (37593879/536870912)), (279/8589934592), by norm_num⟩
  | 6 => ⟨((-725198079/8589934592), (-322693409/8589934592)), (151/8589934592), by norm_num⟩
  | 7 => ⟨((1333898609/34359738368), (593548579/34359738368)), (35/4294967296), by norm_num⟩
  | 8 => ⟨((-1073413497/68719476736), (-477639793/68719476736)), (227/68719476736), by norm_num⟩
  | 9 => ⟨((767818835/137438953472), (341658485/137438953472)), (41/34359738368), by norm_num⟩
  | 10 => ⟨((-988605395/549755813888), (-439902495/549755813888)), (213/549755813888), by norm_num⟩
  | 11 => ⟨((36161341/68719476736), (257453001/1099511627776)), (63/549755813888), by norm_num⟩
  | 12 => ⟨((-310396977/2199023255552), (-552472827/8796093022208)), (17/549755813888), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (-1773458359385/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777616665420553/633825300114114700748351602688), (-4192451984605/633825300114114700748351602688)), (92613/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888445543761079/39614081257132168796771975168), (-589418053367/4951760157141521099596496896)), (104217/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888139318033707/2475880078570760549798248448), (-5008612233913/2475880078570760549798248448)), (110761/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442451313336383/38685626227668133590597632), (-2503495656049/77371252455336267181195264)), (27699/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548254247628951/9671406556917033397649408), (-4692332639943/9671406556917033397649408)), (25977/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257651570330855/604462909807314587353088), (-1026017480663/151115727451828646838272)), (90957/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885943613150281/75557863725914323419136), (-1666471929935/18889465931478580854784)), (147873/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296152585390739/4722366482869645213696), (-2498297175543/2361183241434822606848)), (110965/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101221268058181/36893488147419103232), (-6865734696729/590295810358705651712)), (152675/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821088515971219/73786976294838206464), (-8575298594853/73786976294838206464)), (11937/4611686018427387904), by norm_num⟩
  | 7 => ⟨((227496338204219/1152921504606846976), (-9637771521879/9223372036854775808)), (53767/2305843009213693952), by norm_num⟩
  | 6 => ⟨((198902117183625/144115188075855872), (-1203247761389/144115188075855872)), (107661/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192155409707997/144115188075855872), (-4204742357477/72057594037927936)), (94347/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487994314829915/36028797018963968), (-3146940393471/9007199254740992)), (283613/36028797018963968), by norm_num⟩
  | 3 => ⟨((742347524106355/4503599627370496), (-7844231611285/4503599627370496)), (5555/140737488355328), by norm_num⟩
  | 2 => ⟨((2218796794885183/4503599627370496), (-31238513634733/4503599627370496)), (714057/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101156400489143/1125899906842624), (-46512800011645/2251799813685248)), (1078657/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076450680604893/1125899906842624), (-22913021127537/562949953421312)), (2187745/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1076450680604893/1125899906842624), (-22913021127537/562949953421312)), (8345584877974700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2054616106807525/2251799813685248), (-175253498379757/2251799813685248)), (2180705/1125899906842624), by norm_num⟩
  | 2 => ⟨((1861059554312735/2251799813685248), (-319814095690965/2251799813685248)), (4318935/1125899906842624), by norm_num⟩
  | 3 => ⟨((1492700011994013/2251799813685248), (-264318823890245/1125899906842624)), (16731597/2251799813685248), by norm_num⟩
  | 4 => ⟨((865394672880287/2251799813685248), (-700859302311607/2251799813685248)), (7509595/562949953421312), by norm_num⟩
  | 5 => ⟨((228887289755223/4503599627370496), (-538697892213111/2251799813685248)), (83573563/4503599627370496), by norm_num⟩
  | 6 => ⟨((-984450107999549/18014398509481984), (-219026753259595/9007199254740992)), (96963091/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-1356338561/33554432)), (1/16777216), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-95658131/33554432), (-343216251/8388608)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-437294315/134217728), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1038322772657585/18014398509481984), (153662541151365/36028797018963968)), (86865449/9007199254740992), by norm_num⟩
  | 1 => ⟨((1613119045/8589934592), (-14920455/1073741824)), (17/536870912), by norm_num⟩
  | 2 => ⟨((-656962197/2147483648), (48612283/2147483648)), (223/4294967296), by norm_num⟩
  | 3 => ⟨((1426964173/4294967296), (-105589007/4294967296)), (61/1073741824), by norm_num⟩
  | 4 => ⟨((-581148379/2147483648), (86004795/4294967296)), (201/4294967296), by norm_num⟩
  | 5 => ⟨((757375009/4294967296), (-56042385/4294967296)), (33/1073741824), by norm_num⟩
  | 6 => ⟨((-1645067263/17179869184), (121727667/17179869184)), (289/17179869184), by norm_num⟩
  | 7 => ⟨((1531367987/34359738368), (-56657213/17179869184)), (271/34359738368), by norm_num⟩
  | 8 => ⟨((-155917023/8589934592), (92297335/68719476736)), (223/68719476736), by norm_num⟩
  | 9 => ⟨((1806196313/274877906944), (-133650501/274877906944)), (325/274877906944), by norm_num⟩
  | 10 => ⟨((-1176952391/549755813888), (87089247/549755813888)), (213/549755813888), by norm_num⟩
  | 11 => ⟨((1394408913/2199023255552), (-103180063/2199023255552)), (127/1099511627776), by norm_num⟩
  | 12 => ⟨((-1514372951/8796093022208), (112056869/8796093022208)), (139/4398046511104), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (1998031530717/5070602400912917605986812821504)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777561287906893/633825300114114700748351602688), (4723074662257/633825300114114700748351602688)), (46333/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888383121912527/39614081257132168796771975168), (2656062704463/19807040628566084398385987584)), (104279/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888072827232007/2475880078570760549798248448), (1410622262329/618970019642690137449562112)), (110831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((884869287125863/77371252455336267181195264), (5640639720331/154742504910672534362390528)), (110871/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548191536112225/9671406556917033397649408), (5286135357369/9671406556917033397649408)), (103983/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257596498105679/604462909807314587353088), (2311702327085/302231454903657293676544)), (45513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885853746907773/75557863725914323419136), (3754675868769/37778931862957161709568)), (147995/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648042429514991/2361183241434822606848), (1407198587419/1180591620717411303424)), (111065/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404861658799847/147573952589676412928), (966795374795/73786976294838206464)), (19103/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1820970655345717/73786976294838206464), (301878564505/2305843009213693952)), (47799/18446744073709551616), by norm_num⟩
  | 7 => ⟨((909918511941837/4611686018427387904), (10856855526423/9223372036854775808)), (215325/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99442618670333/72057594037927936), (5421699844287/576460752303423488)), (215611/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596017864627481/72057594037927936), (4736425439939/72057594037927936)), (94491/72057594037927936), by norm_num⟩
  | 4 => ⟨((743905881843537/18014398509481984), (7089531781097/18014398509481984)), (142059/18014398509481984), by norm_num⟩
  | 3 => ⟨((742230792177547/4503599627370496), (17671035771155/9007199254740992)), (356279/9007199254740992), by norm_num⟩
  | 2 => ⟨((138644634725173/281474976710656), (4398000655619/562949953421312)), (357981/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100774979013443/1125899906842624), (26190972246241/1125899906842624)), (541237/1125899906842624), by norm_num⟩
  | 0 => ⟨((1075611248751573/1125899906842624), (51597127787283/1125899906842624)), (549811/562949953421312), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1075611248751573/1125899906842624), (51597127787283/1125899906842624)), (2097362520458030523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2050408367262373/2251799813685248), (197170106202101/2251799813685248)), (4403601/2251799813685248), by norm_num⟩
  | 2 => ⟨((57805127653407/70368744177664), (359072092531319/2251799813685248)), (8790693/2251799813685248), by norm_num⟩
  | 3 => ⟨((731125027671919/1125899906842624), (589926916789775/2251799813685248)), (4311485/562949953421312), by norm_num⟩
  | 4 => ⟨((397495693515985/1125899906842624), (95770132571523/281474976710656)), (7858541/562949953421312), by norm_num⟩
  | 5 => ⟨((19987804619391/2251799813685248), (2163927505571073/9007199254740992)), (10896511/562949953421312), by norm_num⟩
  | 6 => ⟨((-1038322772657585/18014398509481984), (153662541151365/36028797018963968)), (86865449/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-343216251/8388608)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-6047887/2097152), (-173595957/4194304)), (1/16777216), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-859940730843313/18014398509481984), (524630980351569/18014398509481984)), (184102201/18014398509481984), by norm_num⟩
  | 1 => ⟨((337865873/2147483648), (-206124559/2147483648)), (147/4294967296), by norm_num⟩
  | 2 => ⟨((-69596925/268435456), (679352921/4294967296)), (61/1073741824), by norm_num⟩
  | 3 => ⟨((1223360593/4294967296), (-746345467/4294967296)), (135/2147483648), by norm_num⟩
  | 4 => ⟨((-251999809/1073741824), (307479113/2147483648)), (7/134217728), by norm_num⟩
  | 5 => ⟨((1328880417/8589934592), (-810720797/8589934592)), (297/8589934592), by norm_num⟩
  | 6 => ⟨((-364981089/4294967296), (445333915/8589934592)), (165/8589934592), by norm_num⟩
  | 7 => ⟨((171845447/4294967296), (-419356553/17179869184)), (157/17179869184), by norm_num⟩
  | 8 => ⟨((-1132749119/68719476736), (345532697/34359738368)), (261/68719476736), by norm_num⟩
  | 9 => ⟨((829634735/137438953472), (-126535489/34359738368)), (193/137438953472), by norm_num⟩
  | 10 => ⟨((-546868149/274877906944), (667264527/549755813888)), (1/2147483648), by norm_num⟩
  | 11 => ⟨((655413893/1099511627776), (-799707283/2199023255552)), (309/2199023255552), by norm_num⟩
  | 12 => ⟨((-720045757/4398046511104), (109821031/1099511627776)), (171/4398046511104), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (105584642377/316912650057057350374175801344)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222189232588863/79228162514264337593543950336), (1996592860275/316912650057057350374175801344)), (46297/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888329966010051/39614081257132168796771975168), (4491203232601/39614081257132168796771975168)), (52097/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888016616806525/2475880078570760549798248448), (2385249141173/1237940039285380274899124224)), (110735/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769682664693731/154742504910672534362390528), (2384458999139/77371252455336267181195264)), (6923/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((96758715019341/604462909807314587353088), (4469182115357/9671406556917033397649408)), (12985/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1257551233389461/604462909807314587353088), (3908856454087/604462909807314587353088)), (45465/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885780789447397/75557863725914323419136), (6348746979849/75557863725914323419136)), (36957/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296030663295609/4722366482869645213696), (148712808435/147573952589676412928)), (6933/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619372963721375/590295810358705651712), (1634724165481/147573952589676412928)), (38155/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910439917710241/36893488147419103232), (8166924721833/73786976294838206464)), (190915/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819736593574445/9223372036854775808), (4589295042347/4611686018427387904)), (214973/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397745910257865/288230376151711744), (2291775043475/288230376151711744)), (215215/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1191952191074357/144115188075855872), (8008300760629/144115188075855872)), (94293/72057594037927936), by norm_num⟩
  | 4 => ⟨((743845656909591/18014398509481984), (11986662987089/36028797018963968)), (283423/36028797018963968), by norm_num⟩
  | 3 => ⟨((742159741924605/4503599627370496), (1867284948249/1125899906842624)), (355237/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218055185941867/4503599627370496), (29741731991077/4503599627370496)), (713349/4503599627370496), by norm_num⟩
  | 1 => ⟨((275153005512193/281474976710656), (22138324972723/1125899906842624)), (134655/281474976710656), by norm_num⟩
  | 0 => ⟨((1075408809146325/1125899906842624), (43608109534387/1125899906842624)), (1091743/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1075408809146325/1125899906842624), (43608109534387/1125899906842624)), (4164669041160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2050985940322565/2251799813685248), (166609997419789/2251799813685248)), (1085069/562949953421312), by norm_num⟩
  | 2 => ⟨((1855753078388307/2251799813685248), (37937959687669/281474976710656)), (8548699/2251799813685248), by norm_num⟩
  | 3 => ⟨((744228013813871/1125899906842624), (250123425893503/1125899906842624)), (16394741/2251799813685248), by norm_num⟩
  | 4 => ⟨((436374144254469/1125899906842624), (41333350178317/140737488355328)), (28958409/2251799813685248), by norm_num⟩
  | 5 => ⟨((144030316932067/2251799813685248), (1025273679330973/4503599627370496)), (19728473/1125899906842624), by norm_num⟩
  | 6 => ⟨((-859940730843313/18014398509481984), (524630980351569/18014398509481984)), (184102201/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-173595957/4194304)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile032Terms3
