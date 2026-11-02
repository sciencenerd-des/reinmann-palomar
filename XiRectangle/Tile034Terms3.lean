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
namespace Reinmann.XiRectangle.Tile034Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8319/640))
  have he : value ((7/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-45376701/16777216), (-168521775/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-950502371673725/18014398509481984), (-740713394122611/18014398509481984)), (221101689/18014398509481984), by norm_num⟩
  | 1 => ⟨((700484081/4294967296), (545877587/4294967296)), (41/1073741824), by norm_num⟩
  | 2 => ⟨((-135326627/536870912), (-421832699/2147483648)), (255/4294967296), by norm_num⟩
  | 3 => ⟨((557733799/2147483648), (869268521/4294967296)), (265/4294967296), by norm_num⟩
  | 4 => ⟨((-861989425/4294967296), (-671736475/4294967296)), (207/4294967296), by norm_num⟩
  | 5 => ⟨((1065778363/8589934592), (830546385/8589934592)), (129/4294967296), by norm_num⟩
  | 6 => ⟨((-1098122055/17179869184), (-855751379/17179869184)), (67/4294967296), by norm_num⟩
  | 7 => ⟨((969811969/34359738368), (377880549/17179869184)), (239/34359738368), by norm_num⟩
  | 8 => ⟨((-187358123/17179869184), (-292011205/34359738368)), (93/34359738368), by norm_num⟩
  | 9 => ⟨((257391961/68719476736), (200582007/68719476736)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((-636487583/549755813888), (-496005999/549755813888)), (5/17179869184), by norm_num⟩
  | 11 => ⟨((715421869/2199023255552), (8711225/34359738368)), (181/2199023255552), by norm_num⟩
  | 12 => ⟨((-737133123/8796093022208), (-574437681/8796093022208)), (47/2199023255552), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (-3229969265803/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777790511920891/633825300114114700748351602688), (-3818526050797/633825300114114700748351602688)), (2893/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((472160289985981/9903520314283042199192993792), (-2147412032185/19807040628566084398385987584)), (104173/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29505425311245/38685626227668133590597632), (-1140497564775/618970019642690137449562112)), (13839/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770013222221287/154742504910672534362390528), (-4560572826479/154742504910672534362390528)), (13843/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((774224644755393/4835703278458516698824704), (-534253931695/1208925819614629174706176)), (6491/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1257822302907905/604462909807314587353088), (-1869136228697/302231454903657293676544)), (90907/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886221186305769/75557863725914323419136), (-1517967956045/18889465931478580854784)), (147787/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324090220277219/1180591620717411303424), (-4551436640581/4722366482869645213696)), (110895/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404956720821029/147573952589676412928), (-6254218154405/590295810358705651712)), (76285/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821447039618643/73786976294838206464), (-7811765384921/73786976294838206464)), (95423/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455093607309691/2305843009213693952), (-4389990873439/4611686018427387904)), (214887/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591621139501351/1152921504606846976), (-8769672461941/1152921504606846976)), (107559/576460752303423488), by norm_num⟩
  | 5 => ⟨((596254810849213/72057594037927936), (-7661877285611/144115188075855872)), (188489/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488526695711187/36028797018963968), (-2867418311991/9007199254740992)), (283255/36028797018963968), by norm_num⟩
  | 3 => ⟨((742681183745821/4503599627370496), (-7148329171119/4503599627370496)), (177491/4503599627370496), by norm_num⟩
  | 2 => ⟨((2220136895661555/4503599627370496), (-14236141387501/2251799813685248)), (712711/4503599627370496), by norm_num⟩
  | 1 => ⟨((2204336373199011/2251799813685248), (-42406768818163/2251799813685248)), (537979/1125899906842624), by norm_num⟩
  | 0 => ⟨((1078500395886415/1125899906842624), (-83612487399691/2251799813685248)), (2179601/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078500395886415/1125899906842624), (-83612487399691/2251799813685248)), (8314517983443450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2063088085994847/2251799813685248), (-40046233334585/562949953421312)), (4337547/2251799813685248), by norm_num⟩
  | 2 => ⟨((1878796335266341/2251799813685248), (-293521320605635/2251799813685248)), (8565195/2251799813685248), by norm_num⟩
  | 3 => ⟨((95582455943437/140737488355328), (-489800894488827/2251799813685248)), (16525737/2251799813685248), by norm_num⟩
  | 4 => ⟨((233026108421329/562949953421312), (-332650333366291/1125899906842624)), (29636249/2251799813685248), by norm_num⟩
  | 5 => ⟨((189268022650515/2251799813685248), (-68848227252087/281474976710656)), (10511835/562949953421312), by norm_num⟩
  | 6 => ⟨((-950502371673725/18014398509481984), (-740713394122611/18014398509481984)), (221101689/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-168521775/4194304)), (1/16777216), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-5753657/2097152), (-683781033/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-577480550445331/9007199254740992), (-97453676097297/18014398509481984)), (193687527/18014398509481984), by norm_num⟩
  | 1 => ⟨((107925351/536870912), (145704955/8589934592)), (291/8589934592), by norm_num⟩
  | 2 => ⟨((-1353597255/4294967296), (-114214261/4294967296)), (115/2147483648), by norm_num⟩
  | 3 => ⟨((1414732121/4294967296), (59686359/2147483648)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-1108971095/4294967296), (-93573117/4294967296)), (3/67108864), by norm_num⟩
  | 5 => ⟨((1390868981/8589934592), (117359187/8589934592)), (243/8589934592), by norm_num⟩
  | 6 => ⟨((-1453687215/17179869184), (-30664921/4294967296)), (1/67108864), by norm_num⟩
  | 7 => ⟨((162786709/4294967296), (109885351/34359738368)), (231/34359738368), by norm_num⟩
  | 8 => ⟨((-1020833569/68719476736), (-86136221/68719476736)), (183/68719476736), by norm_num⟩
  | 9 => ⟨((1422585667/274877906944), (30008847/68719476736)), (257/274877906944), by norm_num⟩
  | 10 => ⟨((-446050913/274877906944), (-75274053/549755813888)), (81/274877906944), by norm_num⟩
  | 11 => ⟨((1017156405/2199023255552), (21456487/549755813888)), (187/2199023255552), by norm_num⟩
  | 12 => ⟨((-132887001/1099511627776), (-44851127/4398046511104)), (197/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790200988601433/5070602400912917605986812821504), (-1991311374649/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888863273220887/316912650057057350374175801344), (-4708023588371/633825300114114700748351602688)), (11583/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888568993793799/39614081257132168796771975168), (-2647621495835/19807040628566084398385987584)), (104277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888270265282835/2475880078570760549798248448), (-1406154534677/618970019642690137449562112)), (110829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769935955086715/154742504910672534362390528), (-5622843728267/154742504910672534362390528)), (27717/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548376519842215/9671406556917033397649408), (-5269531153183/9671406556917033397649408)), (25995/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1257758298054121/604462909807314587353088), (-2304477721781/302231454903657293676544)), (5689/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1886116557768879/75557863725914323419136), (-3743010311771/37778931862957161709568)), (147991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296281867351287/4722366482869645213696), (-701428263935/590295810358705651712)), (55531/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619717359377267/590295810358705651712), (-7710692799211/590295810358705651712)), (38205/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821308817086855/73786976294838206464), (-2407710629639/18446744073709551616)), (95595/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28440892514345/144115188075855872), (-5412179511417/4611686018427387904)), (53829/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591461576899385/1152921504606846976), (-5405722238019/576460752303423488)), (107801/576460752303423488), by norm_num⟩
  | 5 => ⟨((596183738080199/72057594037927936), (-4722748693107/72057594037927936)), (188973/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488308440362259/36028797018963968), (-14139243873777/36028797018963968)), (142051/18014398509481984), by norm_num⟩
  | 3 => ⟨((742540388612769/4503599627370496), (-17623370455651/9007199254740992)), (356255/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109773788210793/2251799813685248), (-4386870735933/562949953421312)), (178975/1125899906842624), by norm_num⟩
  | 1 => ⟨((550846914111567/562949953421312), (-26131992914265/1125899906842624)), (541173/1125899906842624), by norm_num⟩
  | 0 => ⟨((538712011018775/562949953421312), (-51509987751343/1125899906842624)), (1099423/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((538712011018775/562949953421312), (-51509987751343/1125899906842624)), (4193965916160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((514339346413729/562949953421312), (-24646106568119/281474976710656)), (2204773/1125899906842624), by norm_num⟩
  | 2 => ⟨((1862440804198923/2251799813685248), (-90071682335871/562949953421312)), (8829771/2251799813685248), by norm_num⟩
  | 3 => ⟨((1482760235395777/2251799813685248), (-74497375595137/281474976710656)), (8715773/1125899906842624), by norm_num⟩
  | 4 => ⟨((818628250323045/2251799813685248), (-196219478307947/562949953421312)), (32183713/2251799813685248), by norm_num⟩
  | 5 => ⟨((24033607791855/2251799813685248), (-285337634776069/1125899906842624)), (91672063/4503599627370496), by norm_num⟩
  | 6 => ⟨((-577480550445331/9007199254740992), (-97453676097297/18014398509481984)), (193687527/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5753657/2097152), (-683781033/16777216)), (1/16777216), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-93308067/33554432), (-1386124663/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-996100985104797/18014398509481984), (252384935971503/9007199254740992)), (202160549/18014398509481984), by norm_num⟩
  | 1 => ⟨((754752767/4294967296), (-382467705/4294967296)), (155/4294967296), by norm_num⟩
  | 2 => ⟨((-1199322461/4294967296), (607751477/4294967296)), (31/536870912), by norm_num⟩
  | 3 => ⟨((317625945/1073741824), (-643822303/4294967296)), (33/536870912), by norm_num⟩
  | 4 => ⟨((-1009432351/4294967296), (127881371/1073741824)), (211/4294967296), by norm_num⟩
  | 5 => ⟨((320803035/2147483648), (-650262209/8589934592)), (271/8589934592), by norm_num⟩
  | 6 => ⟨((-1359372419/17179869184), (688856101/17179869184)), (289/17179869184), by norm_num⟩
  | 7 => ⟨((154291383/4294967296), (-312745967/17179869184)), (265/34359738368), by norm_num⟩
  | 8 => ⟨((-980692641/68719476736), (496961759/68719476736)), (53/17179869184), by norm_num⟩
  | 9 => ⟨((1385197335/274877906944), (-701942765/274877906944)), (301/274877906944), by norm_num⟩
  | 10 => ⟨((-880446339/549755813888), (446162379/549755813888)), (193/549755813888), by norm_num⟩
  | 11 => ⟨((63593315/137438953472), (-515610203/2199023255552)), (225/2199023255552), by norm_num⟩
  | 12 => ⟨((-1077882551/8796093022208), (546212327/8796093022208)), (15/549755813888), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580353468412699/10141204801825835211973625643008), (3481311797097/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888836004564169/316912650057057350374175801344), (4115149904113/633825300114114700748351602688)), (46303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888507808380909/39614081257132168796771975168), (4628415207399/39614081257132168796771975168)), (6513/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1888205480644209/2475880078570760549798248448), (1229073620623/618970019642690137449562112)), (110751/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769871423176445/154742504910672534362390528), (614340457309/19342813113834066795298816)), (110785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193539536186495/1208925819614629174706176), (4605884923861/9671406556917033397649408)), (103897/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628852932289595/302231454903657293676544), (2014240679077/302231454903657293676544)), (45473/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886031855527821/75557863725914323419136), (6543155981187/75557863725914323419136)), (147855/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648109389779911/2361183241434822606848), (4904632719067/4722366482869645213696)), (110951/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619631325928037/590295810358705651712), (421214313679/36893488147419103232)), (152653/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910601171021533/36893488147419103232), (4208814346221/36893488147419103232)), (190961/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820098800655669/9223372036854775808), (4730342199425/4611686018427387904)), (215031/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591345082877421/1152921504606846976), (9449258988225/1152921504606846976)), (13455/72057594037927936), by norm_num⟩
  | 5 => ⟨((1192267592970345/144115188075855872), (4127630502487/72057594037927936)), (188651/144115188075855872), by norm_num⟩
  | 4 => ⟨((744081350075439/18014398509481984), (12357242724533/36028797018963968)), (141769/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484905719451339/9007199254740992), (7700870499729/4503599627370496)), (22213/562949953421312), by norm_num⟩
  | 2 => ⟨((554804672886267/1125899906842624), (30669336543399/4503599627370496)), (356889/2251799813685248), by norm_num⟩
  | 1 => ⟨((550736745169387/562949953421312), (45669661923485/2251799813685248)), (1078097/2251799813685248), by norm_num⟩
  | 0 => ⟨((2154174757210283/2251799813685248), (45004036651275/1125899906842624)), (546513/562949953421312), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2154174757210283/2251799813685248), (45004036651275/1125899906842624)), (2084781648875999273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1028592196159993/1125899906842624), (172211684426925/2251799813685248)), (1089329/562949953421312), by norm_num⟩
  | 2 => ⟨((1866218628410983/2251799813685248), (157328012563609/1125899906842624)), (8627929/2251799813685248), by norm_num⟩
  | 3 => ⟨((46959152606431/70368744177664), (260776704956353/1125899906842624)), (16712349/2251799813685248), by norm_num⟩
  | 4 => ⟨((440995671634879/1125899906842624), (696096156175805/2251799813685248)), (15023499/1125899906842624), by norm_num⟩
  | 5 => ⟨((16284688650895/281474976710656), (272648918478075/1125899906842624)), (84229145/4503599627370496), by norm_num⟩
  | 6 => ⟨((-996100985104797/18014398509481984), (252384935971503/9007199254740992)), (202160549/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-93308067/33554432), (-1386124663/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-47253303/16777216), (-350982347/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-582498149453829/18014398509481984), (906492578897877/18014398509481984)), (98046619/9007199254740992), by norm_num⟩
  | 1 => ⟨((55879033/536870912), (-173919621/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-359735337/2147483648), (1119651327/4294967296)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((771962253/4294967296), (-600669765/2147483648)), (267/4294967296), by norm_num⟩
  | 4 => ⟨((-621212659/4294967296), (966740693/4294967296)), (217/4294967296), by norm_num⟩
  | 5 => ⟨((199960641/2147483648), (-622363649/4294967296)), (141/4294967296), by norm_num⟩
  | 6 => ⟨((-214549491/4294967296), (667770435/8589934592)), (153/8589934592), by norm_num⟩
  | 7 => ⟨((49329155/2147483648), (-614134317/17179869184)), (71/8589934592), by norm_num⟩
  | 8 => ⟨((-317568849/34359738368), (988411053/68719476736)), (115/34359738368), by norm_num⟩
  | 9 => ⟨((56789705/17179869184), (-707016099/137438953472)), (83/68719476736), by norm_num⟩
  | 10 => ⟨((-584956827/549755813888), (227579703/137438953472)), (27/68719476736), by norm_num⟩
  | 11 => ⟨((342346071/1099511627776), (-1065528443/2199023255552)), (255/2199023255552), by norm_num⟩
  | 12 => ⟨((-91830791/1099511627776), (1143267915/8796093022208)), (69/2199023255552), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940107137/10141204801825835211973625643008), (2790117196623/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777620260859891/633825300114114700748351602688), (3297915712641/633825300114114700748351602688)), (92525/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236056222959685/4951760157141521099596496896), (28978492299/309485009821345068724781056)), (6507/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((472036021551867/618970019642690137449562112), (3939942100875/2475880078570760549798248448)), (110643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769810317343319/154742504910672534362390528), (3938668133687/154742504910672534362390528)), (110671/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548259309167673/9671406556917033397649408), (3691148257181/9671406556917033397649408)), (103783/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628828156455889/302231454903657293676544), (3228402137653/604462909807314587353088)), (90839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1885951907446179/75557863725914323419136), (2621809249949/37778931862957161709568)), (147667/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324039829903607/1180591620717411303424), (3930496900023/4722366482869645213696)), (55399/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619550381711295/590295810358705651712), (5400832765935/590295810358705651712)), (19053/73786976294838206464), by norm_num⟩
  | 8 => ⟨((910551189826137/36893488147419103232), (6745643945469/73786976294838206464)), (95323/36893488147419103232), by norm_num⟩
  | 7 => ⟨((909994007207377/4611686018427387904), (3790717274629/4611686018427387904)), (53659/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1591236381248395/1152921504606846976), (946521866901/144115188075855872)), (214837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596087408890695/72057594037927936), (3307624182807/72057594037927936)), (188207/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488028198738129/36028797018963968), (4951047012335/18014398509481984)), (141381/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484745713930095/9007199254740992), (12341324526017/9007199254740992)), (177121/4503599627370496), by norm_num⟩
  | 2 => ⟨((2218922900000059/4503599627370496), (6143511831189/1125899906842624)), (710859/4503599627370496), by norm_num⟩
  | 1 => ⟨((2202563338981475/2251799813685248), (9147633888571/562949953421312)), (134031/281474976710656), by norm_num⟩
  | 0 => ⟨((2153644651200713/2251799813685248), (36052364861969/1125899906842624)), (2168449/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2153644651200713/2251799813685248), (36052364861969/1125899906842624)), (8271976479537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2057459177072509/2251799813685248), (137923419792891/2251799813685248)), (4286727/2251799813685248), by norm_num⟩
  | 2 => ⟨((935721588122833/1125899906842624), (63009998504639/562949953421312)), (8358653/2251799813685248), by norm_num⟩
  | 3 => ⟨((763561525858679/1125899906842624), (104733672167573/562949953421312)), (985293/140737488355328), by norm_num⟩
  | 4 => ⟨((59857633897133/140737488355328), (568225307013781/2251799813685248)), (6812105/562949953421312), by norm_num⟩
  | 5 => ⟨((527890355805449/4503599627370496), (483348435385507/2251799813685248)), (36930155/2251799813685248), by norm_num⟩
  | 6 => ⟨((-582498149453829/18014398509481984), (906492578897877/18014398509481984)), (98046619/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/16777216), (-350982347/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-95658131/33554432), (-710517853/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-63821258122915/18014398509481984), (2078407151035783/36028797018963968)), (345085419/36028797018963968), by norm_num⟩
  | 1 => ⟨((49575763/4294967296), (-403621861/2147483648)), (135/4294967296), by norm_num⟩
  | 2 => ⟨((-80761311/4294967296), (328759747/1073741824)), (221/4294967296), by norm_num⟩
  | 3 => ⟨((87709383/4294967296), (-714087329/2147483648)), (121/2147483648), by norm_num⟩
  | 4 => ⟨((-71441409/4294967296), (1163282727/4294967296)), (199/4294967296), by norm_num⟩
  | 5 => ⟨((93105203/8589934592), (-758017485/4294967296)), (261/8589934592), by norm_num⟩
  | 6 => ⟨((-101115247/17179869184), (1646462763/17179869184)), (143/8589934592), by norm_num⟩
  | 7 => ⟨((94126639/34359738368), (-1532667037/34359738368)), (67/8589934592), by norm_num⟩
  | 8 => ⟨((-76668419/68719476736), (312098573/17179869184)), (55/17179869184), by norm_num⟩
  | 9 => ⟨((13877395/34359738368), (-903864249/137438953472)), (321/274877906944), by norm_num⟩
  | 10 => ⟨((-18085557/137438953472), (147243849/68719476736)), (211/549755813888), by norm_num⟩
  | 11 => ⟨((42854175/1099511627776), (-1395591781/2199023255552)), (251/2199023255552), by norm_num⟩
  | 12 => ⟨((-46541013/4398046511104), (94728599/549755813888)), (275/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580262236925127/10141204801825835211973625643008), (531508837795/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222196233849333/79228162514264337593543950336), (1256414569021/316912650057057350374175801344)), (2889/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((472098310601753/9903520314283042199192993792), (1413118474629/19807040628566084398385987584)), (26005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944042104304157/1237940039285380274899124224), (375250443711/309485009821345068724781056)), (27635/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1769750661680761/154742504910672534362390528), (1500510824787/77371252455336267181195264)), (110561/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548203617600349/9671406556917033397649408), (2812414933043/9671406556917033397649408)), (103673/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257607818191355/604462909807314587353088), (1229910329571/302231454903657293676544)), (5671/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1885873544445065/75557863725914323419136), (1997627513195/37778931862957161709568)), (147487/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296100932711313/4722366482869645213696), (2994732886603/4722366482869645213696)), (110651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809735362526815/295147905179352825856), (4114983411199/590295810358705651712)), (152205/590295810358705651712), by norm_num⟩
  | 8 => ⟨((910501872667525/36893488147419103232), (5139570976043/73786976294838206464)), (23793/9223372036854775808), by norm_num⟩
  | 7 => ⟨((909939168036717/4611686018427387904), (5776304855827/9223372036854775808)), (214259/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591128305851165/1152921504606846976), (5769171964449/1152921504606846976)), (214411/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596041025063551/72057594037927936), (5040011575617/144115188075855872)), (93891/72057594037927936), by norm_num⟩
  | 4 => ⟨((1487892631433429/36028797018963968), (235750502131/1125899906842624)), (8813/1125899906842624), by norm_num⟩
  | 3 => ⟨((1484582499141641/9007199254740992), (9402077334775/9007199254740992)), (353123/9007199254740992), by norm_num⟩
  | 2 => ⟨((2218615091921395/4503599627370496), (9360282018547/2251799813685248)), (708059/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101073895888647/1125899906842624), (435510924019/35184372088832)), (66665/140737488355328), by norm_num⟩
  | 0 => ⟨((1076497947792119/1125899906842624), (54917772575775/2251799813685248)), (67237/70368744177664), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076497947792119/1125899906842624), (54917772575775/2251799813685248)), (256488800317263581/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1028593957709909/1125899906842624), (105016208129769/2251799813685248)), (4219303/2251799813685248), by norm_num⟩
  | 2 => ⟨((937248881922455/1125899906842624), (191880355415973/2251799813685248)), (126607/35184372088832), by norm_num⟩
  | 3 => ⟨((386016085303643/562949953421312), (159729694872105/1125899906842624)), (14871259/2251799813685248), by norm_num⟩
  | 4 => ⟨((506723638186079/1125899906842624), (219054042536283/1125899906842624)), (3076755/281474976710656), by norm_num⟩
  | 5 => ⟨((370875191793105/2251799813685248), (788701451834253/4503599627370496)), (31733409/2251799813685248), by norm_num⟩
  | 6 => ⟨((-63821258122915/18014398509481984), (2078407151035783/36028797018963968)), (345085419/36028797018963968), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-95658131/33554432), (-710517853/16777216)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-6047887/2097152), (-1437496345/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((6550385050245/281474976710656), (915962021389881/18014398509481984)), (139769899/18014398509481984), by norm_num⟩
  | 1 => ⟨((-329422005/4294967296), (-719752645/4294967296)), (111/4294967296), by norm_num⟩
  | 2 => ⟨((271430297/2147483648), (1186093651/4294967296)), (185/4294967296), by norm_num⟩
  | 3 => ⟨((-74549165/536870912), (-325764265/1073741824)), (103/2147483648), by norm_num⟩
  | 4 => ⟨((491403773/4294967296), (536832937/2147483648)), (43/1073741824), by norm_num⟩
  | 5 => ⟨((-161958667/2147483648), (-353862757/2147483648)), (229/8589934592), by norm_num⟩
  | 6 => ⟨((88964891/2147483648), (777515947/8589934592)), (1/67108864), by norm_num⟩
  | 7 => ⟨((-670202897/34359738368), (-732161635/17179869184)), (243/34359738368), by norm_num⟩
  | 8 => ⟨((276109927/34359738368), (603271327/34359738368)), (101/34359738368), by norm_num⟩
  | 9 => ⟨((-404450345/137438953472), (-220920431/34359738368)), (75/68719476736), by norm_num⟩
  | 10 => ⟨((533200943/549755813888), (1164988321/549755813888)), (25/68719476736), by norm_num⟩
  | 11 => ⟨((-39939621/137438953472), (-349055587/549755813888)), (121/1099511627776), by norm_num⟩
  | 12 => ⟨((351025267/4398046511104), (766953515/4398046511104)), (135/4398046511104), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395054805263161/2535301200456458802993406410752), (1487019314867/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777520761244827/633825300114114700748351602688), (1757459750013/633825300114114700748351602688)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1888338102092849/39614081257132168796771975168), (494163068135/9903520314283042199192993792)), (25983/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888025766531379/2475880078570760549798248448), (2099575486329/2475880078570760549798248448)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442423095495747/38685626227668133590597632), (1049440553139/77371252455336267181195264)), (110455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548149152771539/9671406556917033397649408), (1966963566549/9671406556917033397649408)), (103567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257560333696327/604462909807314587353088), (860177998519/302231454903657293676544)), (22659/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1885796704737447/75557863725914323419136), (1397098562513/37778931862957161709568)), (147313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648021792434153/2361183241434822606848), (2094439881207/4722366482869645213696)), (110511/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619392329291717/590295810358705651712), (2877893277189/590295810358705651712)), (151993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820906435820761/73786976294838206464), (1797213334951/36893488147419103232)), (190053/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819769803226089/9223372036854775808), (4039691521645/9223372036854775808)), (213895/9223372036854775808), by norm_num⟩
  | 6 => ⟨((198877618223383/144115188075855872), (985021799/281474976710656)), (107001/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191989425798463/144115188075855872), (3524653676395/144115188075855872)), (187373/144115188075855872), by norm_num⟩
  | 4 => ⟨((743878158640463/18014398509481984), (5275671734887/36028797018963968)), (70325/9007199254740992), by norm_num⟩
  | 3 => ⟨((185552084386709/1125899906842624), (6574844499667/9007199254740992)), (22003/562949953421312), by norm_num⟩
  | 2 => ⟨((138643566763257/281474976710656), (13090633872261/4503599627370496)), (705369/4503599627370496), by norm_num⟩
  | 1 => ⟨((137606533312663/140737488355328), (19488942512721/2251799813685248)), (1061255/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076121394916499/1125899906842624), (38393614554931/2251799813685248)), (1067699/1125899906842624), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1076121394916499/1125899906842624), (38393614554931/2251799813685248)), (4072948460105514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2056432782615373/2251799813685248), (36696148387295/1125899906842624)), (2077397/1125899906842624), by norm_num⟩
  | 2 => ⟨((234452977043129/281474976710656), (67024752449775/1125899906842624)), (3929739/1125899906842624), by norm_num⟩
  | 3 => ⟨((1554310205288129/2251799813685248), (223311541666199/2251799813685248)), (3507191/562949953421312), by norm_num⟩
  | 4 => ⟨((131340059362855/281474976710656), (154141325556977/1125899906842624)), (22149249/2251799813685248), by norm_num⟩
  | 5 => ⟨((448075054127895/2251799813685248), (287697771013349/2251799813685248)), (53469939/4503599627370496), by norm_num⟩
  | 6 => ⟨((6550385050245/281474976710656), (915962021389881/18014398509481984)), (139769899/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-6047887/2097152), (-1437496345/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile034Terms3
