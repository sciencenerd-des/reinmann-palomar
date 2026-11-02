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
namespace Reinmann.XiRectangle.Tile043Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨43,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (17907/1280)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (17907/1280))
  have he : value ((7/8), (17907/1280))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-45376701/16777216), (-725500523/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((890615009813139/18014398509481984), (811736407391903/18014398509481984)), (67307939/9007199254740992), by norm_num⟩
  | 1 => ⟨((-328174687/2147483648), (-598218845/4294967296)), (101/4294967296), by norm_num⟩
  | 2 => ⟨((507200945/2147483648), (924559923/4294967296)), (79/2147483648), by norm_num⟩
  | 3 => ⟨((-261296609/1073741824), (-952617991/4294967296)), (165/4294967296), by norm_num⟩
  | 4 => ⟨((807678911/4294967296), (736145663/4294967296)), (129/4294967296), by norm_num⟩
  | 5 => ⟨((-998627921/8589934592), (-455091499/4294967296)), (81/4294967296), by norm_num⟩
  | 6 => ⟨((514466883/8589934592), (468902381/8589934592)), (169/17179869184), by norm_num⟩
  | 7 => ⟨((-454353993/17179869184), (-103528369/4294967296)), (151/34359738368), by norm_num⟩
  | 8 => ⟨((702213741/68719476736), (640021167/68719476736)), (119/68719476736), by norm_num⟩
  | 9 => ⟨((-482349441/137438953472), (-879258933/274877906944)), (83/137438953472), by norm_num⟩
  | 10 => ⟨((37274065/34359738368), (271782669/274877906944)), (13/68719476736), by norm_num⟩
  | 11 => ⟨((-83793249/274877906944), (-610975831/2199023255552)), (119/2199023255552), by norm_num⟩
  | 12 => ⟨((690689307/8796093022208), (629517411/8796093022208)), (125/8796093022208), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (481377655613/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888898819191049/316912650057057350374175801344), (569093067755/316912650057057350374175801344)), (92313/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236081195768481/4951760157141521099596496896), (40005037127/1237940039285380274899124224)), (103859/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888356673622595/2475880078570760549798248448), (339949047795/618970019642690137449562112)), (110359/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885011631310241/77371252455336267181195264), (1359374451407/154742504910672534362390528)), (3449/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1548459325232453/9671406556917033397649408), (1273965630263/9671406556917033397649408)), (103481/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257831706429421/604462909807314587353088), (278568052949/151115727451828646838272)), (90555/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943118816269283/37778931862957161709568), (452463327703/18889465931478580854784)), (147171/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296374234369347/4722366482869645213696), (1356656260341/4722366482869645213696)), (55197/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((809923448452253/295147905179352825856), (466052716711/147573952589676412928)), (151819/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455368632982063/18446744073709551616), (2328477760441/73786976294838206464)), (94907/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1820408755034573/9223372036854775808), (654271067187/2305843009213693952)), (53399/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591659701642905/1152921504606846976), (326752649135/144115188075855872)), (106833/576460752303423488), by norm_num⟩
  | 5 => ⟨((596274057977621/72057594037927936), (2283827306731/144115188075855872)), (46759/36028797018963968), by norm_num⟩
  | 4 => ⟨((93037119260223/2251799813685248), (3418870275757/36028797018963968)), (140355/18014398509481984), by norm_num⟩
  | 3 => ⟨((742731440892199/4503599627370496), (4261590627597/9007199254740992)), (351163/9007199254740992), by norm_num⟩
  | 2 => ⟨((555096779694047/1125899906842624), (8487295290279/4503599627370496)), (703155/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204833642488205/2251799813685248), (6320798433771/1125899906842624)), (1056819/2251799813685248), by norm_num⟩
  | 0 => ⟨((539619197783917/562949953421312), (6232003522381/562949953421312)), (530513/562949953421312), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((539619197783917/562949953421312), (6232003522381/562949953421312)), (2023746492625999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2068745464704983/2251799813685248), (47789807543577/2251799813685248)), (4115197/2251799813685248), by norm_num⟩
  | 2 => ⟨((1899557814170009/2251799813685248), (87809712936337/2251799813685248)), (7735999/2251799813685248), by norm_num⟩
  | 3 => ⟨((1598991758417325/2251799813685248), (148147828554319/2251799813685248)), (13655099/2251799813685248), by norm_num⟩
  | 4 => ⟨((1125689259309745/2251799813685248), (210398060650067/2251799813685248)), (21189597/2251799813685248), by norm_num⟩
  | 5 => ⟨((271540337903889/1125899906842624), (105179348365683/1125899906842624)), (50290709/4503599627370496), by norm_num⟩
  | 6 => ⟨((890615009813139/18014398509481984), (811736407391903/18014398509481984)), (67307939/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-725500523/16777216)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-5753657/2097152), (-5749483/131072)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((575555460398065/9007199254740992), (135558148332771/18014398509481984)), (80746197/18014398509481984), by norm_num⟩
  | 1 => ⟨((-860524567/4294967296), (-202675719/8589934592)), (123/8589934592), by norm_num⟩
  | 2 => ⟨((1349084901/4294967296), (19859017/536870912)), (49/2147483648), by norm_num⟩
  | 3 => ⟨((-44062999/134217728), (-83023777/2147483648)), (105/4294967296), by norm_num⟩
  | 4 => ⟨((276318557/1073741824), (65080143/2147483648)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((-1386232379/8589934592), (-81623365/4294967296)), (27/2147483648), by norm_num⟩
  | 6 => ⟨((724420601/8589934592), (85309863/8589934592)), (115/17179869184), by norm_num⟩
  | 7 => ⟨((-1297952345/34359738368), (-76425309/17179869184)), (105/34359738368), by norm_num⟩
  | 8 => ⟨((1017430517/68719476736), (119815557/68719476736)), (21/17179869184), by norm_num⟩
  | 9 => ⟨((-708921667/137438953472), (-166969327/274877906944)), (119/274877906944), by norm_num⟩
  | 10 => ⟨((1778255829/1099511627776), (3272071/17179869184)), (151/1099511627776), by norm_num⟩
  | 11 => ⟨((-253441403/549755813888), (-119383967/2199023255552)), (11/274877906944), by norm_num⟩
  | 12 => ⟨((1059552071/8796093022208), (124775913/8796093022208)), (47/4398046511104), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (152696035801/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888869210049989/316912650057057350374175801344), (45127079795/158456325028528675187087900672)), (46109/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944291499162615/19807040628566084398385987584), (101512003231/19807040628566084398385987584)), (103747/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944143007410619/1237940039285380274899124224), (53913169605/618970019642690137449562112)), (13779/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884976340968907/77371252455336267181195264), (215584845625/154742504910672534362390528)), (55117/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387098309696163/2417851639229258349412352), (101019375305/4835703278458516698824704)), (51673/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628886981831723/302231454903657293676544), (44177974649/151115727451828646838272)), (45215/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886143955795191/75557863725914323419136), (287021892023/75557863725914323419136)), (146951/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648152056257985/2361183241434822606848), (215148415833/4722366482869645213696)), (13777/590295810358705651712), by norm_num⟩
  | 9 => ⟨((809875349805847/295147905179352825856), (295637451707/590295810358705651712)), (37/144115188075855872), by norm_num⟩
  | 8 => ⟨((1821354615234707/73786976294838206464), (369259620795/73786976294838206464)), (94723/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910137150824869/4611686018427387904), (415022565417/9223372036854775808)), (13321/576460752303423488), by norm_num⟩
  | 6 => ⟨((795762906628519/576460752303423488), (207265002573/576460752303423488)), (53287/288230376151711744), by norm_num⟩
  | 5 => ⟨((1192431597703815/144115188075855872), (362160413385/144115188075855872)), (93259/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488420395123033/36028797018963968), (135533976937/9007199254740992)), (69951/9007199254740992), by norm_num⟩
  | 3 => ⟨((1485248194464923/9007199254740992), (168935265495/2251799813685248)), (87451/2251799813685248), by norm_num⟩
  | 2 => ⟨((554991080440649/1125899906842624), (1345713309345/4503599627370496)), (174939/1125899906842624), by norm_num⟩
  | 1 => ⟨((275526971428183/281474976710656), (1002104763103/1125899906842624)), (525009/1125899906842624), by norm_num⟩
  | 0 => ⟨((2157305633255629/2251799813685248), (987836347469/562949953421312)), (2101639/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157305633255629/2251799813685248), (987836347469/562949953421312)), (8017116555220793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1033384929215693/1125899906842624), (3785531740749/1125899906842624)), (4034269/2251799813685248), by norm_num⟩
  | 2 => ⟨((1896918323182395/2251799813685248), (13897901318521/2251799813685248)), (7432677/2251799813685248), by norm_num⟩
  | 3 => ⟨((1597880038579213/2251799813685248), (5853802701435/562949953421312)), (12614337/2251799813685248), by norm_num⟩
  | 4 => ⟨((566807122480213/1125899906842624), (33230927294895/2251799813685248)), (18164639/2251799813685248), by norm_num⟩
  | 5 => ⟨((1140400628905807/4503599627370496), (33458615926507/2251799813685248)), (37650455/4503599627370496), by norm_num⟩
  | 6 => ⟨((575555460398065/9007199254740992), (135558148332771/18014398509481984)), (80746197/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-5749483/131072)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-93308067/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((495720408255275/9007199254740992), (-32116420516869/1125899906842624)), (104831517/18014398509481984), by norm_num⟩
  | 1 => ⟨((-187805431/1073741824), (389357427/4294967296)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((1193711539/4294967296), (-618699431/4294967296)), (33/1073741824), by norm_num⟩
  | 3 => ⟨((-1264559843/4294967296), (5120469/33554432)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((1004709813/4294967296), (-130185009/1073741824)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((-319302187/2147483648), (330987973/4294967296)), (149/8589934592), by norm_num⟩
  | 6 => ⟨((676506359/8589934592), (-701265063/17179869184)), (5/536870912), by norm_num⟩
  | 7 => ⟨((-1228556357/34359738368), (636759463/34359738368)), (147/34359738368), by norm_num⟩
  | 8 => ⟨((976104559/68719476736), (-505913963/68719476736)), (119/68719476736), by norm_num⟩
  | 9 => ⟨((-689358407/137438953472), (357293735/137438953472)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((438163625/274877906944), (-454199489/549755813888)), (55/274877906944), by norm_num⟩
  | 11 => ⟨((-506366395/1099511627776), (524898337/2199023255552)), (129/2199023255552), by norm_num⟩
  | 12 => ⟨((536419887/4398046511104), (-556051723/8796093022208)), (139/8796093022208), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (-622882015069/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888840402111059/316912650057057350374175801344), (-736289368485/633825300114114700748351602688)), (92273/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888518180902317/39614081257132168796771975168), (-12939496019/618970019642690137449562112)), (25953/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888217145579849/2475880078570760549798248448), (-879636302615/2475880078570760549798248448)), (55153/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884941905946301/77371252455336267181195264), (-879355849757/154742504910672534362390528)), (13789/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774164336136917/4835703278458516698824704), (-824098253307/9671406556917033397649408)), (101/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((1257717467135035/604462909807314587353088), (-720788256873/604462909807314587353088)), (90503/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((7367391200793/295147905179352825856), (-146340375229/9444732965739290427392)), (147079/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648117627452709/2361183241434822606848), (-438777187327/2361183241434822606848)), (6895/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1619656018305591/590295810358705651712), (-1205845026491/590295810358705651712)), (151707/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227654532568477/9223372036854775808), (-753059453053/36893488147419103232)), (47415/18446744073709551616), by norm_num⟩
  | 7 => ⟨((910070574281105/4611686018427387904), (-846376359291/4611686018427387904)), (213403/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795696327645175/576460752303423488), (-1690716291395/1152921504606846976)), (213449/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192315079270685/144115188075855872), (-369272262829/36028797018963968)), (186819/144115188075855872), by norm_num⟩
  | 4 => ⟨((372061401934647/9007199254740992), (-1105533174667/18014398509481984)), (280331/36028797018963968), by norm_num⟩
  | 3 => ⟨((371257423686189/2251799813685248), (-1377929328897/4503599627370496)), (175297/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219527282009013/4503599627370496), (-1371966945871/1125899906842624)), (175433/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203560132425511/2251799813685248), (-4086216816007/1125899906842624)), (1053971/2251799813685248), by norm_num⟩
  | 0 => ⟨((2155994165215207/2251799813685248), (-16108923601561/2251799813685248)), (2113507/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2155994165215207/2251799813685248), (-16108923601561/2251799813685248)), (8062389382369231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2064149448265347/2251799813685248), (-30847098469223/2251799813685248)), (4077411/2251799813685248), by norm_num⟩
  | 2 => ⟨((945857037424373/1125899906842624), (-3534562713949/140737488355328)), (7586965/2251799813685248), by norm_num⟩
  | 3 => ⟨((793894705260959/1125899906842624), (-95019203661379/2251799813685248)), (1641069/281474976710656), by norm_num⟩
  | 4 => ⟨((278893193328533/562949953421312), (-133999909275107/2251799813685248)), (19622385/2251799813685248), by norm_num⟩
  | 5 => ⟨((544696126813647/2251799813685248), (-132770816930859/2251799813685248)), (21777777/2251799813685248), by norm_num⟩
  | 6 => ⟨((495720408255275/9007199254740992), (-32116420516869/1125899906842624)), (104831517/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-372961509/8388608)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-47253303/16777216), (-377752187/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((536818601723945/18014398509481984), (-934269061115265/18014398509481984)), (143000895/18014398509481984), by norm_num⟩
  | 1 => ⟨((-411975961/4294967296), (358497631/2147483648)), (111/4294967296), by norm_num⟩
  | 2 => ⟨((663049731/4294967296), (-576979679/2147483648)), (181/4294967296), by norm_num⟩
  | 3 => ⟨((-711424917/4294967296), (1238150627/4294967296)), (49/1073741824), by norm_num⟩
  | 4 => ⟨((572497117/4294967296), (-62272705/268435456)), (5/134217728), by norm_num⟩
  | 5 => ⟨((-184279713/2147483648), (641433935/4294967296)), (13/536870912), by norm_num⟩
  | 6 => ⟨((395449009/8589934592), (-344116031/4294967296)), (113/8589934592), by norm_num⟩
  | 7 => ⟨((-363686073/17179869184), (316476221/8589934592)), (105/17179869184), by norm_num⟩
  | 8 => ⟨((292665077/34359738368), (-1018697657/68719476736)), (171/68719476736), by norm_num⟩
  | 9 => ⟨((-209345009/68719476736), (91085035/17179869184)), (31/34359738368), by norm_num⟩
  | 10 => ⟨((539084471/549755813888), (-938212535/549755813888)), (161/549755813888), by norm_num⟩
  | 11 => ⟨((-630998535/2199023255552), (549089027/1099511627776)), (95/1099511627776), by norm_num⟩
  | 12 => ⟨((338517655/4398046511104), (-1178299597/8796093022208)), (103/4398046511104), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (-341698707093/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888812348264765/316912650057057350374175801344), (-1615550108755/633825300114114700748351602688)), (11545/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888455014434191/39614081257132168796771975168), (-454263383979/9903520314283042199192993792)), (103915/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472037492174621/618970019642690137449562112), (-1930064949895/2475880078570760549798248448)), (55211/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221227070599389/19342813113834066795298816), (-1929441537147/154742504910672534362390528)), (110435/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548265553589631/9671406556917033397649408), (-904094668489/4835703278458516698824704)), (103547/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257662163839795/604462909807314587353088), (-1581503871829/604462909807314587353088)), (45309/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885962140138737/75557863725914323419136), (-2568703570483/75557863725914323419136)), (9205/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648083813825761/2361183241434822606848), (-1925443133959/4722366482869645213696)), (27621/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((809781416614953/295147905179352825856), (-661430785675/147573952589676412928)), (151953/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455279870845569/18446744073709551616), (-3304514307379/73786976294838206464)), (94999/36893488147419103232), by norm_num⟩
  | 7 => ⟨((227501171055079/1152921504606846976), (-464244071641/1152921504606846976)), (106913/4611686018427387904), by norm_num⟩
  | 6 => ⟨((397815092329641/288230376151711744), (-3709425223803/1152921504606846976)), (213925/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192198761902435/144115188075855872), (-405082614427/18014398509481984)), (187295/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488070002234881/36028797018963968), (-4850836818085/36028797018963968)), (70291/9007199254740992), by norm_num⟩
  | 3 => ⟨((371202055542641/2251799813685248), (-3022907715653/4503599627370496)), (351845/9007199254740992), by norm_num⟩
  | 2 => ⟨((2219078482996249/4503599627370496), (-12038598256937/4503599627370496)), (176215/1125899906842624), by norm_num⟩
  | 1 => ⟨((1101436224893535/1125899906842624), (-1120366961245/140737488355328)), (530117/1125899906842624), by norm_num⟩
  | 0 => ⟨((2154561760927023/2251799813685248), (-4415869897755/281474976710656)), (1066161/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154561760927023/2251799813685248), (-4415869897755/281474976710656)), (4067081455710982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2060968457053349/2251799813685248), (-16900728679537/562949953421312)), (4147393/2251799813685248), by norm_num⟩
  | 2 => ⟨((1884279766391149/2251799813685248), (-61873828211643/1125899906842624)), (1960215/562949953421312), by norm_num⟩
  | 3 => ⟨((1569942733841513/2251799813685248), (-103550592605793/1125899906842624)), (6992035/1125899906842624), by norm_num⟩
  | 4 => ⟨((1075508254289357/2251799813685248), (-144389833819545/1125899906842624)), (22071507/2251799813685248), by norm_num⟩
  | 5 => ⟨((476651744120281/2251799813685248), (-137927410034057/1125899906842624)), (6686183/562949953421312), by norm_num⟩
  | 6 => ⟨((536818601723945/18014398509481984), (-934269061115265/18014398509481984)), (143000895/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-377752187/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-95658131/33554432), (-1529419785/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-14141409006275/9007199254740992), (-2081554521565843/36028797018963968)), (170892411/18014398509481984), by norm_num⟩
  | 1 => ⟨((43939663/8589934592), (404233073/2147483648)), (67/2147483648), by norm_num⟩
  | 2 => ⟨((-8947479/1073741824), (-164628797/536870912)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((4858625/536870912), (715168685/2147483648)), (241/4294967296), by norm_num⟩
  | 4 => ⟨((-31659739/4294967296), (-1165044309/4294967296)), (99/2147483648), by norm_num⟩
  | 5 => ⟨((20630097/4294967296), (379582683/2147483648)), (65/2147483648), by norm_num⟩
  | 6 => ⟨((-22404949/8589934592), (-824478017/8589934592)), (71/4294967296), by norm_num⟩
  | 7 => ⟨((20856425/17179869184), (1534987985/34359738368)), (133/17179869184), by norm_num⟩
  | 8 => ⟨((-33976123/68719476736), (-156285595/8589934592)), (109/34359738368), by norm_num⟩
  | 9 => ⟨((12299721/68719476736), (1810465977/274877906944)), (159/137438953472), by norm_num⟩
  | 10 => ⟨((-32058943/549755813888), (-1179734587/549755813888)), (209/549755813888), by norm_num⟩
  | 11 => ⟨((18991115/1099511627776), (698852577/1099511627776)), (125/1099511627776), by norm_num⟩
  | 12 => ⟨((-10312481/2199023255552), (-1517952775/8796093022208)), (273/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (-260190872185/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444392502797879/158456325028528675187087900672), (-1230111634251/316912650057057350374175801344)), (92443/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888393407955671/39614081257132168796771975168), (-2767070132281/39614081257132168796771975168)), (52007/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944042197391549/1237940039285380274899124224), (-2939157112153/2475880078570760549798248448)), (110533/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769750859405149/154742504910672534362390528), (-734548950029/38685626227668133590597632)), (55277/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548203815227691/9671406556917033397649408), (-2753537567483/9671406556917033397649408)), (103665/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628804001681965/302231454903657293676544), (-2408324825253/604462909807314587353088)), (90729/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471468467072769/18889465931478580854784), (-3911615270075/75557863725914323419136)), (147475/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324025298910801/1180591620717411303424), (-2932038905827/4722366482869645213696)), (55321/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619471119113987/590295810358705651712), (-4028837392677/590295810358705651712)), (76095/295147905179352825856), by norm_num⟩
  | 8 => ⟨((910502143310057/36893488147419103232), (-2515987854679/36893488147419103232)), (47581/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1819879011858711/9223372036854775808), (-5655380075415/9223372036854775808)), (107117/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795564532491009/576460752303423488), (-5648396927759/1152921504606846976)), (214383/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192082807850513/144115188075855872), (-308406356811/9007199254740992)), (187753/144115188075855872), by norm_num⟩
  | 4 => ⟨((1487893954288255/36028797018963968), (-7386087421149/36028797018963968)), (140983/18014398509481984), by norm_num⟩
  | 3 => ⟨((185573059639447/1125899906842624), (-9205253830715/9007199254740992)), (44131/1125899906842624), by norm_num⟩
  | 2 => ⟨((69331875463749/140737488355328), (-4582168773129/1125899906842624)), (22121/140737488355328), by norm_num⟩
  | 1 => ⟨((275269696477031/281474976710656), (-13644623702697/1125899906842624)), (133283/281474976710656), by norm_num⟩
  | 0 => ⟨((2153024908459043/2251799813685248), (-26884157519749/1125899906842624)), (1075227/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2153024908459043/2251799813685248), (-26884157519749/1125899906842624)), (4101665501121139171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((128581179724221/140737488355328), (-102819549821753/2251799813685248)), (4214947/2251799813685248), by norm_num⟩
  | 2 => ⟨((1874903256501611/2251799813685248), (-46969216124617/562949953421312)), (4043337/1125899906842624), by norm_num⟩
  | 3 => ⟨((772707343671757/1125899906842624), (-312861687729695/2251799813685248)), (3703933/562949953421312), by norm_num⟩
  | 4 => ⟨((508576318882343/1125899906842624), (-429435196136075/2251799813685248)), (24453085/2251799813685248), by norm_num⟩
  | 5 => ⟨((755115881673189/4503599627370496), (-387957348467797/2251799813685248)), (62836023/4503599627370496), by norm_num⟩
  | 6 => ⟨((-14141409006275/9007199254740992), (-2081554521565843/36028797018963968)), (170892411/18014398509481984), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-1529419785/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-6047887/2097152), (-1547135897/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-33183710389867/1125899906842624), (-214015057222451/4503599627370496)), (91618595/9007199254740992), by norm_num⟩
  | 1 => ⟨((417206177/4294967296), (672682491/4294967296)), (145/4294967296), by norm_num⟩
  | 2 => ⟨((-687521749/4294967296), (-277131469/1073741824)), (241/4294967296), by norm_num⟩
  | 3 => ⟨((377659921/2147483648), (608920075/2147483648)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-622352745/4294967296), (-125431327/536870912)), (111/2147483648), by norm_num⟩
  | 5 => ⟨((1602479/16777216), (1322883813/8589934592)), (295/8589934592), by norm_num⟩
  | 6 => ⟨((-450688799/8589934592), (-726668207/8589934592)), (41/2147483648), by norm_num⟩
  | 7 => ⟨((212199537/8589934592), (342139981/8589934592)), (39/4294967296), by norm_num⟩
  | 8 => ⟨((-699375057/68719476736), (-1127637563/68719476736)), (259/68719476736), by norm_num⟩
  | 9 => ⟨((512228021/137438953472), (825890989/137438953472)), (191/137438953472), by norm_num⟩
  | 10 => ⟨((-337643999/274877906944), (-272200197/137438953472)), (127/274877906944), by norm_num⟩
  | 11 => ⟨((809323301/2199023255552), (652456323/1099511627776)), (307/2199023255552), by norm_num⟩
  | 12 => ⟨((-222283131/2199023255552), (-358398267/2199023255552)), (85/2199023255552), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (-692320386441/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((888758334817305/316912650057057350374175801344), (-1636461881993/316912650057057350374175801344)), (92523/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472083319468729/9903520314283042199192993792), (-1840559155579/19807040628566084398385987584)), (104109/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888020341274787/2475880078570760549798248448), (-3910037167783/2475880078570760549798248448)), (6915/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769686620192637/154742504910672534362390528), (-977185694411/38685626227668133590597632)), (110667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548143393842161/9671406556917033397649408), (-3663071562463/9671406556917033397649408)), (103779/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257554937738239/604462909807314587353088), (-3203813385571/604462909807314587353088)), (22709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885787267883643/75557863725914323419136), (-2601810628465/37778931862957161709568)), (73831/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648017961557055/2361183241434822606848), (-3900463574059/4722366482869645213696)), (55397/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619380846609529/590295810358705651712), (-1339869886005/147573952589676412928)), (152417/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820890663285907/73786976294838206464), (-3346933261475/36893488147419103232)), (190637/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819750111762513/9223372036854775808), (-7523067172449/9223372036854775808)), (214625/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1590998826132243/1152921504606846976), (-7513660830981/1152921504606846976)), (214823/1152921504606846976), by norm_num⟩
  | 5 => ⟨((595983673817795/72057594037927936), (-3281942066437/72057594037927936)), (94097/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487717773687497/36028797018963968), (-2456180145137/9007199254740992)), (282739/36028797018963968), by norm_num⟩
  | 3 => ⟨((1484359045674143/9007199254740992), (-12244039091953/9007199254740992)), (11069/281474976710656), by norm_num⟩
  | 2 => ⟨((2218153643707239/4503599627370496), (-24377785665381/4503599627370496)), (355387/2251799813685248), by norm_num⟩
  | 1 => ⟨((1100709811864537/1125899906842624), (-36291968679189/2251799813685248)), (67005/140737488355328), by norm_num⟩
  | 0 => ⟨((2151397709078047/2251799813685248), (-71491212050491/2251799813685248)), (2167953/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2151397709078047/2251799813685248), (-71491212050491/2251799813685248)), (8270084389693450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1026601272707999/1125899906842624), (-68303598254999/1125899906842624)), (2140119/1125899906842624), by norm_num⟩
  | 2 => ⟨((931916580873973/1125899906842624), (-249118275871459/2251799813685248)), (8324815/2251799813685248), by norm_num⟩
  | 3 => ⟨((1515149845347253/2251799813685248), (-206197238735361/1125899906842624)), (15622997/2251799813685248), by norm_num⟩
  | 4 => ⟨((471980199103207/1125899906842624), (-554968896404007/2251799813685248)), (26746623/2251799813685248), by norm_num⟩
  | 5 => ⟨((129467715971583/1125899906842624), (-465288838961531/2251799813685248)), (71216451/4503599627370496), by norm_num⟩
  | 6 => ⟨((-33183710389867/1125899906842624), (-214015057222451/4503599627370496)), (91618595/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-1547135897/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨43,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile043Terms3
