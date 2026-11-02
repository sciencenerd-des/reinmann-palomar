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
namespace Reinmann.XiRectangle.Tile039Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨39,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((17/32), (7191/512))
  have he : value ((17/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-6887535/4194304), (-91044603/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((734478658406509/4503599627370496), (469584227219417/4503599627370496)), (85722327/4503599627370496), by norm_num⟩
  | 1 => ⟨((-67660353/134217728), (-692131415/2147483648)), (1/16777216), by norm_num⟩
  | 2 => ⟨((418282047/536870912), (534851897/1073741824)), (101/1073741824), by norm_num⟩
  | 3 => ⟨((-430975855/536870912), (-551083307/1073741824)), (53/536870912), by norm_num⟩
  | 4 => ⟨((166520583/268435456), (212927737/536870912)), (21/268435456), by norm_num⟩
  | 5 => ⟨((-411777753/1073741824), (-131633735/536870912)), (53/1073741824), by norm_num⟩
  | 6 => ⟨((106068543/536870912), (542513951/4294967296)), (111/4294967296), by norm_num⟩
  | 7 => ⟨((-749399701/8589934592), (-479123901/8589934592)), (25/2147483648), by norm_num⟩
  | 8 => ⟨((1158213145/34359738368), (740496159/34359738368)), (157/34359738368), by norm_num⟩
  | 9 => ⟨((-795574667/68719476736), (-254322785/34359738368)), (109/68719476736), by norm_num⟩
  | 10 => ⟨((245915507/68719476736), (157224505/68719476736)), (137/274877906944), by norm_num⟩
  | 11 => ⟨((-1105651305/1099511627776), (-706891083/1099511627776)), (39/274877906944), by norm_num⟩
  | 12 => ⟨((1139205041/4398046511104), (728343449/4398046511104)), (163/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581836727270697/10141204801825835211973625643008), (740987232413/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779435646787079/633825300114114700748351602688), (438772900477/316912650057057350374175801344)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890491991652685/39614081257132168796771975168), (493547990219/19807040628566084398385987584)), (25957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945156918798819/1237940039285380274899124224), (1048613770809/2475880078570760549798248448)), (27581/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771979961984243/154742504910672534362390528), (1048416151829/154742504910672534362390528)), (110331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775146618689971/4835703278458516698824704), (245670055705/2417851639229258349412352)), (103443/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629717943106909/302231454903657293676544), (214908833107/151115727451828646838272)), (90521/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236105437501225/9444732965739290427392), (174564255497/9444732965739290427392)), (147109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649163913110925/2361183241434822606848), (130880181771/590295810358705651712)), (110345/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622531772123709/590295810358705651712), (1439123098197/590295810358705651712)), (151745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824828656708673/73786976294838206464), (224758239691/9223372036854775808)), (11857/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1824179439527107/9223372036854775808), (1010836306553/4611686018427387904)), (53367/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199428375814193/144115188075855872), (2020234148851/1152921504606846976)), (213521/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195840709399959/144115188075855872), (441521983777/36028797018963968)), (93445/72057594037927936), by norm_num⟩
  | 4 => ⟨((746762605540717/18014398509481984), (1322950663713/18014398509481984)), (280455/36028797018963968), by norm_num⟩
  | 3 => ⟨((372903438459361/2251799813685248), (3301730603661/9007199254740992)), (175389/4503599627370496), by norm_num⟩
  | 2 => ⟨((2232649177344987/4503599627370496), (6586552805707/4503599627370496)), (87773/562949953421312), by norm_num⟩
  | 1 => ⟨((2223127810810395/2251799813685248), (9837662207989/2251799813685248)), (131857/281474976710656), by norm_num⟩
  | 0 => ⟨((2194671211157069/2251799813685248), (1219204939833/140737488355328)), (1058027/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2194671211157069/2251799813685248), (1219204939833/140737488355328)), (4036052708152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2138822981455045/2251799813685248), (38024751091143/2251799813685248)), (2080701/1125899906842624), by norm_num⟩
  | 2 => ⟨((1015436149455141/1125899906842624), (72233962365193/2251799813685248)), (8045777/2251799813685248), by norm_num⟩
  | 3 => ⟨((1829303175232403/2251799813685248), (130293956253523/2251799813685248)), (7514489/1125899906842624), by norm_num⟩
  | 4 => ⟨((2887771265065/4398046511104), (211694793151339/2251799813685248)), (26157515/2251799813685248), by norm_num⟩
  | 5 => ⟨((950911597034325/2251799813685248), (277998942977463/2251799813685248)), (39268423/2251799813685248), by norm_num⟩
  | 6 => ⟨((734478658406509/4503599627370496), (469584227219417/4503599627370496)), (85722327/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6887535/4194304), (-91044603/2097152)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-13973167/8388608), (-738831201/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1700212739806889/9007199254740992), (-94414699737657/9007199254740992)), (110016621/9007199254740992), by norm_num⟩
  | 1 => ⟨((-317752791/536870912), (17645165/536870912)), (21/536870912), by norm_num⟩
  | 2 => ⟨((498156019/536870912), (-55326313/1073741824)), (67/1073741824), by norm_num⟩
  | 3 => ⟨((-1041310211/1073741824), (57825111/1073741824)), (9/134217728), by norm_num⟩
  | 4 => ⟨((51015971/67108864), (-90655151/2147483648)), (115/2147483648), by norm_num⟩
  | 5 => ⟨((-1023745805/2147483648), (14212435/536870912)), (37/1073741824), by norm_num⟩
  | 6 => ⟨((1069983017/4294967296), (-232099/16777216)), (79/4294967296), by norm_num⟩
  | 7 => ⟨((-59909385/536870912), (26614677/4294967296)), (9/1073741824), by norm_num⟩
  | 8 => ⟨((1502764241/34359738368), (-41725083/17179869184)), (115/34359738368), by norm_num⟩
  | 9 => ⟨((-1047090797/68719476736), (29073057/34359738368)), (41/34359738368), by norm_num⟩
  | 10 => ⟨((1313258855/274877906944), (-36463361/137438953472)), (105/274877906944), by norm_num⟩
  | 11 => ⟨((-1497351107/1099511627776), (83149569/1099511627776)), (61/549755813888), by norm_num⟩
  | 12 => ⟨((782489289/2199023255552), (-43452499/2199023255552)), (65/2199023255552), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395451491523285/2535301200456458802993406410752), (-72261253675/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779399624972039/633825300114114700748351602688), (-21393786329/158456325028528675187087900672)), (92209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890451496601523/39614081257132168796771975168), (-48128959283/19807040628566084398385987584)), (12967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((945135424486153/1237940039285380274899124224), (-102256660571/2475880078570760549798248448)), (27555/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885968507686385/77371252455336267181195264), (-25559279019/38685626227668133590597632)), (27555/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775126509775577/4835703278458516698824704), (-2994579237/302231454903657293676544)), (103333/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314850185052575/151115727451828646838272), (-10478432981/75557863725914323419136)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944393235662211/37778931862957161709568), (-17022590771/9444732965739290427392)), (9183/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1298285127783469/4722366482869645213696), (-51050758749/2361183241434822606848)), (55099/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405618295107047/147573952589676412928), (-1096361845/4611686018427387904)), (37881/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456188898729141/18446744073709551616), (-43833757755/18446744073709551616)), (5919/2305843009213693952), by norm_num⟩
  | 7 => ⟨((57003046539563/288230376151711744), (-98569019461/4611686018427387904)), (6659/288230376151711744), by norm_num⟩
  | 6 => ⟨((1595345361185359/1152921504606846976), (-196995801043/1152921504606846976)), (213093/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195769612257311/144115188075855872), (-43052861711/36028797018963968)), (186463/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493419249083235/36028797018963968), (-257997758167/36028797018963968)), (139853/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491482494869783/9007199254740992), (-321939004221/9007199254740992)), (43707/1125899906842624), by norm_num⟩
  | 2 => ⟨((2232390228133931/4503599627370496), (-321103267115/2251799813685248)), (699379/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222748267381519/2251799813685248), (-959141967539/2251799813685248)), (524621/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096973699087367/1125899906842624), (-950838774565/1125899906842624)), (262401/281474976710656), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1096973699087367/1125899906842624), (-950838774565/1125899906842624)), (1000980378271007449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2137579699725915/2251799813685248), (-926410173259/562949953421312)), (2047049/1125899906842624), by norm_num⟩
  | 2 => ⟨((1014573589787601/1125899906842624), (-3517676070391/1125899906842624)), (7786335/2251799813685248), by norm_num⟩
  | 3 => ⟨((1828487930043755/2251799813685248), (-1584928294583/281474976710656)), (27503/4398046511104), by norm_num⟩
  | 4 => ⟨((185585288384913/281474976710656), (-10295843312597/1125899906842624)), (23027327/2251799813685248), by norm_num⟩
  | 5 => ⟨((978709351516229/2251799813685248), (-27153490838347/2251799813685248)), (30786429/2251799813685248), by norm_num⟩
  | 6 => ⟨((1700212739806889/9007199254740992), (-94414699737657/9007199254740992)), (110016621/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13973167/8388608), (-738831201/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-56651327/33554432), (-1497719445/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((82627477996659/562949953421312), (-505877613343911/4503599627370496)), (43335411/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1001718799/2147483648), (766614097/2147483648)), (133/2147483648), by norm_num⟩
  | 2 => ⟨((397939533/536870912), (-609085217/1073741824)), (27/268435456), by norm_num⟩
  | 3 => ⟨((-843115505/1073741824), (322617601/536870912)), (29/268435456), by norm_num⟩
  | 4 => ⟨((669866615/1073741824), (-512648051/1073741824)), (47/536870912), by norm_num⟩
  | 5 => ⟨((-851548865/2147483648), (651689241/2147483648)), (61/1073741824), by norm_num⟩
  | 6 => ⟨((902089377/4294967296), (-690367829/4294967296)), (131/4294967296), by norm_num⟩
  | 7 => ⟨((-204777757/2147483648), (626864607/8589934592)), (121/8589934592), by norm_num⟩
  | 8 => ⟨((650794735/17179869184), (-249026183/8589934592)), (49/8589934592), by norm_num⟩
  | 9 => ⟨((-459613489/34359738368), (703483213/68719476736)), (35/17179869184), by norm_num⟩
  | 10 => ⟨((1168541127/274877906944), (-3493293/1073741824)), (45/68719476736), by norm_num⟩
  | 11 => ⟨((-337607873/274877906944), (258370867/274877906944)), (53/274877906944), by norm_num⟩
  | 12 => ⟨((715290663/2199023255552), (-68426377/274877906944)), (57/1099511627776), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98861032144007/633825300114114700748351602688), (-850892758687/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779364208561815/633825300114114700748351602688), (-1007629296985/633825300114114700748351602688)), (92299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890411627918085/39614081257132168796771975168), (-141676773287/4951760157141521099596496896)), (103843/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890228455956519/2475880078570760549798248448), (-150505642141/309485009821345068724781056)), (110341/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221486823222055/19342813113834066795298816), (-601905917765/77371252455336267181195264)), (110349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775106601480047/4835703278458516698824704), (-564162886853/4835703278458516698824704)), (103461/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259365861873747/604462909807314587353088), (-987037298341/604462909807314587353088)), (45269/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59022803790455/2361183241434822606848), (-1603471217123/75557863725914323419136)), (36785/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649121250836531/2361183241434822606848), (-1202197214611/4722366482869645213696)), (55185/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811207233147897/295147905179352825856), (-1652361370417/590295810358705651712)), (151781/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912341023789973/36893488147419103232), (-2064462490087/73786976294838206464)), (189761/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912007268061621/4611686018427387904), (-2321160893849/9223372036854775808)), (106765/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595262142981385/1152921504606846976), (-1159731397413/576460752303423488)), (213591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597848249359427/72057594037927936), (-1013810589207/72057594037927936)), (186961/144115188075855872), by norm_num⟩
  | 4 => ⟨((373327246253289/9007199254740992), (-1518809107967/18014398509481984)), (140289/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491343628971719/9007199254740992), (-3790358005543/9007199254740992)), (350963/9007199254740992), by norm_num⟩
  | 2 => ⟨((279013675246541/562949953421312), (-7560757475325/4503599627370496)), (702647/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222319337826029/2251799813685248), (-1411420601673/281474976710656)), (527891/1125899906842624), by norm_num⟩
  | 0 => ⟨((2193059050376627/2251799813685248), (-22384391981867/2251799813685248)), (2118841/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2193059050376627/2251799813685248), (-22384391981867/2251799813685248)), (8082736977584075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266953511376091/281474976710656), (-21800469617533/1125899906842624)), (260579/140737488355328), by norm_num⟩
  | 2 => ⟨((506151376500719/562949953421312), (-82703080494869/2251799813685248)), (2017449/562949953421312), by norm_num⟩
  | 3 => ⟨((227162047806363/281474976710656), (-148717582367395/2251799813685248)), (3775991/562949953421312), by norm_num⟩
  | 4 => ⟨((728406051556427/1125899906842624), (-240042585313837/2251799813685248)), (6593527/562949953421312), by norm_num⟩
  | 5 => ⟨((28653205655537/70368744177664), (-155296639347079/1125899906842624)), (39748675/2251799813685248), by norm_num⟩
  | 6 => ⟨((82627477996659/562949953421312), (-505877613343911/4503599627370496)), (43335411/2251799813685248), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56651327/33554432), (-1497719445/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-57379011/33554432), (-758478801/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((549764424636331/9007199254740992), (-1533479580758395/9007199254740992)), (115136313/4503599627370496), by norm_num⟩
  | 1 => ⟨((-105477775/536870912), (73553329/134217728)), (179/2147483648), by norm_num⟩
  | 2 => ⟨((84879965/268435456), (-473518065/536870912)), (73/536870912), by norm_num⟩
  | 3 => ⟨((-364290757/1073741824), (127016321/134217728)), (159/1073741824), by norm_num⟩
  | 4 => ⟨((146575839/536870912), (-408849765/536870912)), (65/536870912), by norm_num⟩
  | 5 => ⟨((-94361885/536870912), (263207325/536870912)), (169/2147483648), by norm_num⟩
  | 6 => ⟨((404985587/4294967296), (-1129642261/4294967296)), (183/4294967296), by norm_num⟩
  | 7 => ⟨((-186228331/4294967296), (1038908047/8589934592)), (85/4294967296), by norm_num⟩
  | 8 => ⟨((37465367/2147483648), (-836028999/17179869184)), (139/17179869184), by norm_num⟩
  | 9 => ⟨((-3349899/536870912), (598016341/34359738368)), (201/68719476736), by norm_num⟩
  | 10 => ⟨((69010617/34359738368), (-1539952275/274877906944)), (261/274877906944), by norm_num⟩
  | 11 => ⟨((-20194237/34359738368), (225314325/137438953472)), (77/274877906944), by norm_num⟩
  | 12 => ⟨((346681287/2199023255552), (-483505889/1099511627776)), (167/2199023255552), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790874132495493/5070602400912917605986812821504), (-399433602799/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889664692628867/316912650057057350374175801344), (-945986671653/316912650057057350374175801344)), (46193/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472593094635703/9903520314283042199192993792), (-2128147568927/39614081257132168796771975168)), (103947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890186659513357/2475880078570760549798248448), (-2260762110569/2475880078570760549798248448)), (110457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771852683674621/154742504910672534362390528), (-2260318194045/154742504910672534362390528)), (110473/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550173807538685/9671406556917033397649408), (-1059288374007/4835703278458516698824704)), (103585/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259331278748113/604462909807314587353088), (-1853283210791/604462909807314587353088)), (45327/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944336656807379/37778931862957161709568), (-3010701505275/75557863725914323419136)), (73671/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649100006110867/2361183241434822606848), (-1128626562693/2361183241434822606848)), (55267/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((50698617033633/18446744073709551616), (-193904210951/36893488147419103232)), (38007/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824608199199955/73786976294838206464), (-3876201513071/73786976294838206464)), (190101/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823930843049329/9223372036854775808), (-4358139284867/9223372036854775808)), (213955/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797588842009165/576460752303423488), (-2177453483709/576460752303423488)), (214069/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74726358569147/9007199254740992), (-1903454962569/72057594037927936)), (187439/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493195126563087/36028797018963968), (-5703104255601/36028797018963968)), (281415/36028797018963968), by norm_num⟩
  | 3 => ⟨((745599155929273/4503599627370496), (-1779047325401/2251799813685248)), (352219/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231809821538459/4503599627370496), (-14194365849829/4503599627370496)), (705789/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221847727134821/2251799813685248), (-21196727704693/2251799813685248)), (531035/1125899906842624), by norm_num⟩
  | 0 => ⟨((137001726193541/140737488355328), (-21007717054077/1125899906842624)), (534433/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((137001726193541/140737488355328), (-21007717054077/1125899906842624)), (2038700105907249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2133058079580533/2251799813685248), (-81800337164681/2251799813685248)), (4241751/2251799813685248), by norm_num⟩
  | 2 => ⟨((2017606293460055/2251799813685248), (-154973696188363/2251799813685248)), (8344329/2251799813685248), by norm_num⟩
  | 3 => ⟨((1797103936284889/2251799813685248), (-69427997739881/562949953421312)), (16101541/2251799813685248), by norm_num⟩
  | 4 => ⟨((1399972852261983/2251799813685248), (-221634849187635/1125899906842624)), (14836015/1125899906842624), by norm_num⟩
  | 5 => ⟨((97890360349509/281474976710656), (-275586462075477/1125899906842624)), (6072115/281474976710656), by norm_num⟩
  | 6 => ⟨((549764424636331/9007199254740992), (-1533479580758395/9007199254740992)), (115136313/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57379011/33554432), (-758478801/16777216)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-58078151/33554432), (-1535441123/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-327309488515985/9007199254740992), (-390380619631605/2251799813685248)), (269349765/9007199254740992), by norm_num⟩
  | 1 => ⟨((127125491/1073741824), (1212976213/2147483648)), (211/2147483648), by norm_num⟩
  | 2 => ⟨((-207093561/1073741824), (-15437475/16777216)), (173/1073741824), by norm_num⟩
  | 3 => ⟨((224910271/1073741824), (134124757/134217728)), (95/536870912), by norm_num⟩
  | 4 => ⟨((-45798711/268435456), (-873982813/1073741824)), (39/268435456), by norm_num⟩
  | 5 => ⟨((238746595/2147483648), (1139008151/2147483648)), (205/2147483648), by norm_num⟩
  | 6 => ⟨((-259286485/4294967296), (-1236999505/4294967296)), (7/134217728), by norm_num⟩
  | 7 => ⟨((60341457/2147483648), (143937993/1073741824)), (211/8589934592), by norm_num⟩
  | 8 => ⟨((-49149573/4294967296), (-937927753/17179869184)), (87/8589934592), by norm_num⟩
  | 9 => ⟨((142341381/34359738368), (1358159629/68719476736)), (127/34359738368), by norm_num⟩
  | 10 => ⟨((-371009569/274877906944), (-885003037/137438953472)), (167/137438953472), by norm_num⟩
  | 11 => ⟨((109889545/274877906944), (524259151/274877906944)), (25/68719476736), by norm_num⟩
  | 12 => ⟨((-59671791/549755813888), (-1138724617/2199023255552)), (219/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581721123780269/10141204801825835211973625643008), (-2315280450967/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779295141298993/633825300114114700748351602688), (-2741568513897/633825300114114700748351602688)), (46235/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890333738789599/39614081257132168796771975168), (-1541894129337/19807040628566084398385987584)), (52023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472536364152285/618970019642690137449562112), (-102373303881/77371252455336267181195264)), (110569/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771811314191011/154742504910672534362390528), (-3275294109135/154742504910672534362390528)), (27/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((1550134846754521/9671406556917033397649408), (-1534948002917/4835703278458516698824704)), (12963/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157412126409771/75557863725914323419136), (-2685466918007/604462909807314587353088)), (90765/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((7377411319293/295147905179352825856), (-2181293182011/37778931862957161709568)), (147537/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649078855357453/2361183241434822606848), (-204425303317/295147905179352825856)), (27673/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1622297110339939/590295810358705651712), (-1123878240885/147573952589676412928)), (76133/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228066775161845/9223372036854775808), (-5616626577391/73786976294838206464)), (47607/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823846627976547/9223372036854775808), (-3157452530137/4611686018427387904)), (214363/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595092261513025/1152921504606846976), (-788769693199/144115188075855872)), (214529/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195545636599865/144115188075855872), (-1379012509913/36028797018963968)), (187899/144115188075855872), by norm_num⟩
  | 4 => ⟨((746539135267811/18014398509481984), (-8263407287715/36028797018963968)), (70555/9007199254740992), by norm_num⟩
  | 3 => ⟨((372761880474549/2251799813685248), (-5155304090679/4503599627370496)), (353427/9007199254740992), by norm_num⟩
  | 2 => ⟨((278936767363947/562949953421312), (-5141333568509/1125899906842624)), (354407/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110669572869561/1125899906842624), (-15354271828215/1125899906842624)), (534063/1125899906842624), by norm_num⟩
  | 0 => ⟨((1095435709407659/1125899906842624), (-60860741330919/2251799813685248)), (2155935/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1095435709407659/1125899906842624), (-60860741330919/2251799813685248)), (8224239357955168967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((266243335375421/281474976710656), (-118427986270773/2251799813685248)), (4311741/2251799813685248), by norm_num⟩
  | 2 => ⟨((502114759160499/562949953421312), (-28004853606345/281474976710656)), (4305183/1125899906842624), by norm_num⟩
  | 3 => ⟨((884562268995931/1125899906842624), (-12489254363035/70368744177664)), (17073121/2251799813685248), by norm_num⟩
  | 4 => ⟨((82436185683023/140737488355328), (-627978987349341/2251799813685248)), (32887343/2251799813685248), by norm_num⟩
  | 5 => ⟨((298727246761155/1125899906842624), (-735670261152663/2251799813685248)), (56870309/2251799813685248), by norm_num⟩
  | 6 => ⟨((-327309488515985/9007199254740992), (-390380619631605/2251799813685248)), (269349765/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-58078151/33554432), (-1535441123/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-29375451/16777216), (-1553226983/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1050600800317273/9007199254740992), (-579152342027437/4503599627370496)), (141368141/4503599627370496), by norm_num⟩
  | 1 => ⟨((412775141/1073741824), (910182781/2147483648)), (7/67108864), by norm_num⟩
  | 2 => ⟨((-170054941/268435456), (-749953491/1073741824)), (93/536870912), by norm_num⟩
  | 3 => ⟨((729783/1048576), (823908121/1073741824)), (103/536870912), by norm_num⟩
  | 4 => ⟨((-615742903/1073741824), (-339433345/536870912)), (171/1073741824), by norm_num⟩
  | 5 => ⟨((3170919/8388608), (447486773/1073741824)), (227/2147483648), by norm_num⟩
  | 6 => ⟨((-222951077/1073741824), (-122903617/536870912)), (63/1073741824), by norm_num⟩
  | 7 => ⟨((419891645/4294967296), (925874907/8589934592)), (239/8589934592), by norm_num⟩
  | 8 => ⟨((-345973591/8589934592), (-762883163/17179869184)), (199/17179869184), by norm_num⟩
  | 9 => ⟨((506787785/34359738368), (1117483757/68719476736)), (147/34359738368), by norm_num⟩
  | 10 => ⟨((-334057973/68719476736), (-736608833/137438953472)), (195/137438953472), by norm_num⟩
  | 11 => ⟨((800727697/549755813888), (55175967/34359738368)), (59/137438953472), by norm_num⟩
  | 12 => ⟨((-109961161/274877906944), (-484935963/1099511627776)), (261/2199023255552), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581695007013025/10141204801825835211973625643008), (-3005742696061/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779261462082799/633825300114114700748351602688), (-3559040555227/633825300114114700748351602688)), (46275/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945147848606307/19807040628566084398385987584), (-2001644647287/19807040628566084398385987584)), (104141/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890104841339605/2475880078570760549798248448), (-4252733420551/2475880078570760549798248448)), (110677/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771770478451577/154742504910672534362390528), (-4251876828721/154742504910672534362390528)), (55353/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((775048164565053/4835703278458516698824704), (-3985224502327/9671406556917033397649408)), (51909/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((78703942149057/37778931862957161709568), (-3486161532019/604462909807314587353088)), (11359/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888561711902039/75557863725914323419136), (-5663306661887/75557863725914323419136)), (147725/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298115638061689/4722366482869645213696), (-1061496911587/1180591620717411303424)), (110845/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811119319101709/295147905179352825856), (-1458952103083/147573952589676412928)), (152495/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456115044697175/18446744073709551616), (-1822781108025/18446744073709551616)), (190743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823762072356123/9223372036854775808), (-4098758351711/4611686018427387904)), (214757/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595006108004847/1152921504606846976), (-8191270850215/1152921504606846976)), (214971/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597734229037961/72057594037927936), (-7160338163121/144115188075855872)), (94171/72057594037927936), by norm_num⟩
  | 4 => ⟨((93309932680153/2251799813685248), (-5363233239795/18014398509481984)), (70749/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490892091761925/9007199254740992), (-13383527309189/9007199254740992)), (354591/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115582309310457/2251799813685248), (-6673362399589/1125899906842624)), (44483/281474976710656), by norm_num⟩
  | 1 => ⟨((1110399241612671/1125899906842624), (-9964095194173/562949953421312)), (536983/1125899906842624), by norm_num⟩
  | 0 => ⟨((273700771207559/281474976710656), (-39489453113439/1125899906842624)), (33961/35184372088832), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((273700771207559/281474976710656), (-39489453113439/1125899906842624)), (129550933972108353/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((531590050932441/562949953421312), (-38398773127259/562949953421312)), (1094853/562949953421312), by norm_num⟩
  | 2 => ⟨((249678958817047/281474976710656), (-9064929146191/70368744177664)), (4434171/1125899906842624), by norm_num⟩
  | 3 => ⟨((867214786085771/1125899906842624), (-257309928994263/1125899906842624)), (9008979/1125899906842624), by norm_num⟩
  | 4 => ⟨((609159909756191/1125899906842624), (-792763099719113/2251799813685248)), (17995951/1125899906842624), by norm_num⟩
  | 5 => ⟨((380064802003777/2251799813685248), (-428918676827313/1125899906842624)), (64288753/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1050600800317273/9007199254740992), (-579152342027437/4503599627370496)), (141368141/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29375451/16777216), (-1553226983/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨39,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile039Terms3
