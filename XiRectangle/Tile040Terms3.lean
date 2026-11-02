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
namespace Reinmann.XiRectangle.Tile040Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨40,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/32), (7191/512)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((19/32), (7191/512))
  have he : value ((19/32), (7191/512))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-30791333/16777216), (-91044603/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1210898545262415/9007199254740992), (774180231256539/9007199254740992)), (70878603/4503599627370496), by norm_num⟩
  | 1 => ⟨((-892386153/2147483648), (-570541373/2147483648)), (53/1073741824), by norm_num⟩
  | 2 => ⟨((689600871/1073741824), (440891901/1073741824)), (83/1073741824), by norm_num⟩
  | 3 => ⟨((-710528523/1073741824), (-454271861/1073741824)), (87/1073741824), by norm_num⟩
  | 4 => ⟨((549068457/1073741824), (175521701/536870912)), (137/2147483648), by norm_num⟩
  | 5 => ⟨((-169719391/536870912), (-434036023/2147483648)), (43/1073741824), by norm_num⟩
  | 6 => ⟨((349739895/2147483648), (111801981/1073741824)), (91/4294967296), by norm_num⟩
  | 7 => ⟨((-1235498129/17179869184), (-98738477/2147483648)), (163/17179869184), by norm_num⟩
  | 8 => ⟨((238686073/8589934592), (38150603/2147483648)), (1/268435456), by norm_num⟩
  | 9 => ⟨((-655812253/68719476736), (-104822341/17179869184)), (45/34359738368), by norm_num⟩
  | 10 => ⟨((405428703/137438953472), (259208245/137438953472)), (113/274877906944), by norm_num⟩
  | 11 => ⟨((-455708121/549755813888), (-291354069/549755813888)), (129/1099511627776), by norm_num⟩
  | 12 => ⟨((117384429/549755813888), (75048983/549755813888)), (135/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581585075520873/10141204801825835211973625643008), (740987232413/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222392208115443/79228162514264337593543950336), (877266208297/633825300114114700748351602688)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890156813522193/39614081257132168796771975168), (493382694185/19807040628566084398385987584)), (25957/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472489443505169/618970019642690137449562112), (1048241939077/2475880078570760549798248448)), (27581/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221452996184243/19342813113834066795298816), (524010592873/77371252455336267181195264)), (110331/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549959569891897/9671406556917033397649408), (491142687481/4835703278458516698824704)), (103443/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259144002631923/604462909807314587353088), (214816322033/151115727451828646838272)), (90521/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472092332663199/18889465931478580854784), (1395866717505/75557863725914323419136)), (147109/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40561635091931/147573952589676412928), (1046515736663/4722366482869645213696)), (110345/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622043156106911/590295810358705651712), (359583733357/147573952589676412928)), (151745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456054547009207/18446744073709551616), (1796982859251/73786976294838206464)), (11857/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1823493076397719/9223372036854775808), (252539974001/1152921504606846976)), (53367/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797370580349707/576460752303423488), (2018713601427/1152921504606846976)), (213521/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195241175821221/144115188075855872), (882284553217/72057594037927936)), (186891/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492627072553875/36028797018963968), (2643247239929/36028797018963968)), (35057/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490493111253801/9007199254740992), (3297757186537/9007199254740992)), (350779/9007199254740992), by norm_num⟩
  | 2 => ⟨((557603493334183/1125899906842624), (6576646211791/4503599627370496)), (351095/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109895085380541/1125899906842624), (4908964832531/1125899906842624)), (527435/1125899906842624), by norm_num⟩
  | 0 => ⟨((2188056373742181/2251799813685248), (19448483223821/2251799813685248)), (2116111/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((2188056373742181/2251799813685248), (19448483223821/2251799813685248)), (8072322854048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2125949394826277/2251799813685248), (9448969979231/562949953421312)), (4148971/2251799813685248), by norm_num⟩
  | 2 => ⟨((2006498212391747/2251799813685248), (71367026098833/2251799813685248)), (7973459/2251799813685248), by norm_num⟩
  | 3 => ⟨((223207109679551/281474976710656), (3974537651525/70368744177664)), (3678785/562949953421312), by norm_num⟩
  | 4 => ⟨((1408826125805401/2251799813685248), (201713433286715/2251799813685248)), (25000215/2251799813685248), by norm_num⟩
  | 5 => ⟨((431677525632677/1125899906842624), (126200896284447/1125899906842624)), (71522941/4503599627370496), by norm_num⟩
  | 6 => ⟨((1210898545262415/9007199254740992), (774180231256539/9007199254740992)), (70878603/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30791333/16777216), (-91044603/2097152)), (1/16777216), by norm_num⟩, -7, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-15617069/8388608), (-738831201/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1397639853057753/9007199254740992), (-38806245823925/4503599627370496)), (90717765/9007199254740992), by norm_num⟩
  | 1 => ⟨((-522409877/1073741824), (1813125/67108864)), (69/2147483648), by norm_num⟩
  | 2 => ⟨((1638013147/2147483648), (-90960687/2147483648)), (55/1073741824), by norm_num⟩
  | 3 => ⟨((-855996791/1073741824), (95068903/2147483648)), (117/2147483648), by norm_num⟩
  | 4 => ⟨((1341986493/2147483648), (-74521999/2147483648)), (93/2147483648), by norm_num⟩
  | 5 => ⟨((-841558177/2147483648), (93465319/4294967296)), (119/4294967296), by norm_num⟩
  | 6 => ⟨((219891733/1073741824), (-763177/67108864)), (63/4294967296), by norm_num⟩
  | 7 => ⟨((-787964865/8589934592), (87513127/17179869184)), (115/17179869184), by norm_num⟩
  | 8 => ⟨((617664819/17179869184), (-34299613/17179869184)), (23/8589934592), by norm_num⟩
  | 9 => ⟨((-215187163/17179869184), (5974791/8589934592)), (65/68719476736), by norm_num⟩
  | 10 => ⟨((134943621/34359738368), (-7493569/34359738368)), (83/274877906944), by norm_num⟩
  | 11 => ⟨((-615439917/549755813888), (68352123/1099511627776)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((160809025/549755813888), (-71439229/4398046511104)), (51/2199023255552), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581550695385817/10141204801825835211973625643008), (-72261253675/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889548685176305/316912650057057350374175801344), (-42773743633/316912650057057350374175801344)), (92209/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945055756420911/19807040628566084398385987584), (-12028152193/4951760157141521099596496896)), (12967/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944954840606387/1237940039285380274899124224), (-51109940181/1237940039285380274899124224)), (27555/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((3460109220115/302231454903657293676544), (-51099023825/77371252455336267181195264)), (27555/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549914570926931/9671406556917033397649408), (-95787479017/9671406556917033397649408)), (103333/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629552337636543/302231454903657293676544), (-41895430457/302231454903657293676544)), (90417/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888305511268225/75557863725914323419136), (-136116696215/75557863725914323419136)), (146929/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324481133743677/1180591620717411303424), (-12756189595/590295810358705651712)), (55099/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621977571976607/590295810358705651712), (-17532044541/73786976294838206464)), (37881/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912068197089373/36893488147419103232), (-87613951641/36893488147419103232)), (189407/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911700657090609/4611686018427387904), (-197004229725/9223372036854775808)), (6659/288230376151711744), by norm_num⟩
  | 6 => ⟨((1594649717882795/1152921504606846976), (-196845403735/1152921504606846976)), (106547/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195161522073963/144115188075855872), (-21507652739/18014398509481984)), (186463/144115188075855872), by norm_num⟩
  | 4 => ⟨((746254153925417/18014398509481984), (-257735251907/36028797018963968)), (69927/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490345904824759/9007199254740992), (-160773009193/4503599627370496)), (349657/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115061647616353/2251799813685248), (-320613385883/2251799813685248)), (87423/562949953421312), by norm_num⟩
  | 1 => ⟨((277420430380587/281474976710656), (-957190527719/2251799813685248)), (1049257/2251799813685248), by norm_num⟩
  | 0 => ⟨((68351243515451/70368744177664), (-236982938345/281474976710656)), (2099267/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((68351243515451/70368744177664), (-236982938345/281474976710656)), (8008068093306731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1062264568657023/1125899906842624), (-1841508324995/1125899906842624)), (127553/70368744177664), by norm_num⟩
  | 2 => ⟨((2004445716379131/2251799813685248), (-3474854264825/1125899906842624)), (3857677/1125899906842624), by norm_num⟩
  | 3 => ⟨((892120673215313/1125899906842624), (-6186301911777/1125899906842624)), (13783311/2251799813685248), by norm_num⟩
  | 4 => ⟨((353424412068115/562949953421312), (-19607170380623/2251799813685248)), (5498555/562949953421312), by norm_num⟩
  | 5 => ⟨((1774719570946769/4503599627370496), (-49238143618105/4503599627370496)), (55998623/4503599627370496), by norm_num⟩
  | 6 => ⟨((1397639853057753/9007199254740992), (-38806245823925/4503599627370496)), (90717765/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15617069/8388608), (-738831201/16777216)), (1/16777216), by norm_num⟩, -7, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-15829047/8388608), (-1497719445/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((270970054163769/2251799813685248), (-829492123029457/9007199254740992)), (142560747/9007199254740992), by norm_num⟩
  | 1 => ⟨((-25664491/67108864), (628512053/2147483648)), (55/1073741824), by norm_num⟩
  | 2 => ⟨((652505071/1073741824), (-124840321/268435456)), (89/1073741824), by norm_num⟩
  | 3 => ⟨((-43202005/67108864), (264499507/536870912)), (3/33554432), by norm_num⟩
  | 4 => ⟨((274596595/536870912), (-840593671/2147483648)), (155/2147483648), by norm_num⟩
  | 5 => ⟨((-21817069/67108864), (534290387/2147483648)), (25/536870912), by norm_num⟩
  | 6 => ⟨((739582077/4294967296), (-141500301/1073741824)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((-671551901/8589934592), (256968899/4294967296)), (25/2147483648), by norm_num⟩
  | 8 => ⟨((1067114045/34359738368), (-408330497/17179869184)), (161/34359738368), by norm_num⟩
  | 9 => ⟨((-753632417/68719476736), (576753911/68719476736)), (115/68719476736), by norm_num⟩
  | 10 => ⟨((239508439/68719476736), (-366590995/137438953472)), (37/68719476736), by norm_num⟩
  | 11 => ⟨((-1107157399/1099511627776), (105913265/137438953472)), (173/1099511627776), by norm_num⟩
  | 12 => ⟨((293217151/1099511627776), (-224398705/1099511627776)), (185/4398046511104), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790758889359627/5070602400912917605986812821504), (-850892758687/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779057863433769/633825300114114700748351602688), (-1007299196569/633825300114114700748351602688)), (92299/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890067044058027/39614081257132168796771975168), (-566511960439/19807040628566084398385987584)), (103843/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889862402399659/2475880078570760549798248448), (-601803095405/1237940039285380274899124224)), (110341/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771528607344193/154742504910672534362390528), (-75209098917/9671406556917033397649408)), (110349/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387467544495201/2417851639229258349412352), (-140982458043/1208925819614629174706176)), (103461/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314766448699121/151115727451828646838272), (-493300236613/302231454903657293676544)), (90537/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944121130917739/37778931862957161709568), (-801353538937/37778931862957161709568)), (36785/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324469259470561/1180591620717411303424), (-1201576637003/4722366482869645213696)), (110369/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621912166054195/590295810358705651712), (-1651431003431/590295810358705651712)), (151781/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824054490835593/73786976294838206464), (-1031592023287/36893488147419103232)), (94881/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823308972561367/9223372036854775808), (-2319564055263/9223372036854775808)), (106765/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594557126277231/1152921504606846976), (-2317668021797/1152921504606846976)), (213591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195080223820639/144115188075855872), (-506457122833/36028797018963968)), (93481/72057594037927936), by norm_num⟩
  | 4 => ⟨((186548225107501/4503599627370496), (-3034485701357/36028797018963968)), (280579/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490191795328757/9007199254740992), (-946417148851/2251799813685248)), (350965/9007199254740992), by norm_num⟩
  | 2 => ⟨((139363260198661/281474976710656), (-3774533326767/2251799813685248)), (351327/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218889511883777/2251799813685248), (-5634040515489/1125899906842624)), (527899/1125899906842624), by norm_num⟩
  | 0 => ⟨((2186263294027415/2251799813685248), (-5578757049505/562949953421312)), (1059451/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2186263294027415/2251799813685248), (-5578757049505/562949953421312)), (4041484837058639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2122413014372937/2251799813685248), (-43331140501939/2251799813685248)), (4156463/2251799813685248), by norm_num⟩
  | 2 => ⟨((1999626871126389/2251799813685248), (-40841364303351/1125899906842624)), (7995237/2251799813685248), by norm_num⟩
  | 3 => ⟨((886365548864027/1125899906842624), (-145070603555629/2251799813685248)), (14779791/2251799813685248), by norm_num⟩
  | 4 => ⟨((693118910008143/1125899906842624), (-114206941809965/1125899906842624)), (25175159/2251799813685248), by norm_num⟩
  | 5 => ⟨((1660433916062557/4503599627370496), (-35153653775793/281474976710656)), (18051833/1125899906842624), by norm_num⟩
  | 6 => ⟨((270970054163769/2251799813685248), (-829492123029457/9007199254740992)), (142560747/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-15829047/8388608), (-1497719445/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-64129483/33554432), (-758478801/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((112394585399377/2251799813685248), (-78376661881929/562949953421312)), (188907383/9007199254740992), by norm_num⟩
  | 1 => ⟨((-345024313/2147483648), (240597479/536870912)), (147/2147483648), by norm_num⟩
  | 2 => ⟨((277647605/1073741824), (-774453409/1073741824)), (239/2147483648), by norm_num⟩
  | 3 => ⟨((-74476097/268435456), (207739113/268435456)), (65/536870912), by norm_num⟩
  | 4 => ⟨((59932327/268435456), (-668686409/1073741824)), (53/536870912), by norm_num⟩
  | 5 => ⟨((-154331775/1073741824), (860967407/2147483648)), (69/1073741824), by norm_num⟩
  | 6 => ⟨((331183213/4294967296), (-923782391/4294967296)), (149/4294967296), by norm_num⟩
  | 7 => ⟨((-152291091/4294967296), (53098943/536870912)), (139/8589934592), by norm_num⟩
  | 8 => ⟨((490206111/34359738368), (-21364863/536870912)), (113/17179869184), by norm_num⟩
  | 9 => ⟨((-87661811/17179869184), (978074183/68719476736)), (41/17179869184), by norm_num⟩
  | 10 => ⟨((451475975/274877906944), (-1259319737/274877906944)), (213/274877906944), by norm_num⟩
  | 11 => ⟨((-132113191/274877906944), (737017065/549755813888)), (251/1099511627776), by norm_num⟩
  | 12 => ⟨((283503971/2199023255552), (-197697201/549755813888)), (17/274877906944), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581486205914137/10141204801825835211973625643008), (-399433602799/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779019116839897/633825300114114700748351602688), (-945672773413/316912650057057350374175801344)), (92387/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890023383161231/39614081257132168796771975168), (-2127405390781/39614081257132168796771975168)), (103947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118113495033305/154742504910672534362390528), (-2259927358303/2475880078570760549798248448)), (110457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771482021874793/154742504910672534362390528), (-1129715757847/77371252455336267181195264)), (110473/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387456598523339/2417851639229258349412352), (-8272227915/37778931862957161709568)), (103585/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259027373961495/604462909807314587353088), (-463113125725/151115727451828646838272)), (45327/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((59005613187989/2361183241434822606848), (-3009248353801/75557863725914323419136)), (73671/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297829877961959/4722366482869645213696), (-564018247555/1180591620717411303424)), (55267/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621847028877651/590295810358705651712), (-3100698135239/590295810358705651712)), (152029/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911986315733537/36893488147419103232), (-3873770371779/73786976294838206464)), (95051/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823216279524977/9223372036854775808), (-1088775675581/2305843009213693952)), (213955/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797231841487515/576460752303423488), (-2175747016405/576460752303423488)), (107035/576460752303423488), by norm_num⟩
  | 5 => ⟨((597498809328697/72057594037927936), (-950875253239/36028797018963968)), (187439/144115188075855872), by norm_num⟩
  | 4 => ⟨((373065053249705/9007199254740992), (-5697147700077/36028797018963968)), (35177/4503599627370496), by norm_num⟩
  | 3 => ⟨((1490031880250719/9007199254740992), (-7107272525765/9007199254740992)), (352221/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114741790991835/2251799813685248), (-14172137002783/4503599627370496)), (705795/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218374901085669/2251799813685248), (-21152458854745/2251799813685248)), (1062087/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185147944650949/2251799813685248), (-20941784374707/1125899906842624)), (2137795/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2185147944650949/2251799813685248), (-20941784374707/1125899906842624)), (8155040749556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((529922473311415/562949953421312), (-81287682511747/2251799813685248)), (2114281/1125899906842624), by norm_num⟩
  | 2 => ⟨((996198136471375/1125899906842624), (-9564831097459/140737488355328)), (8266251/2251799813685248), by norm_num⟩
  | 3 => ⟨((438118707312351/562949953421312), (-270815317973987/2251799813685248)), (3937893/562949953421312), by norm_num⟩
  | 4 => ⟨((665651331988787/1125899906842624), (-421526838434071/2251799813685248)), (3538281/281474976710656), by norm_num⟩
  | 5 => ⟨((708181028305415/2251799813685248), (-498427790547605/2251799813685248)), (22033943/1125899906842624), by norm_num⟩
  | 6 => ⟨((112394585399377/2251799813685248), (-78376661881929/562949953421312)), (188907383/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64129483/33554432), (-758478801/16777216)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-64910875/33554432), (-1535441123/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-267007067456563/9007199254740992), (-1273832725257121/9007199254740992)), (110216381/4503599627370496), by norm_num⟩
  | 1 => ⟨((207408619/2147483648), (989501475/2147483648)), (173/2147483648), by norm_num⟩
  | 2 => ⟨((-84469663/536870912), (-1611945665/2147483648)), (71/536870912), by norm_num⟩
  | 3 => ⟨((366947089/2147483648), (54707027/67108864)), (311/2147483648), by norm_num⟩
  | 4 => ⟨((-74721815/536870912), (-712963101/1073741824)), (255/2147483648), by norm_num⟩
  | 5 => ⟨((194760709/2147483648), (929161045/2147483648)), (21/268435456), by norm_num⟩
  | 6 => ⟨((-211516397/4294967296), (-1009098795/4294967296)), (23/536870912), by norm_num⟩
  | 7 => ⟨((196897383/8589934592), (939354655/8589934592)), (173/8589934592), by norm_num⟩
  | 8 => ⟨((-320755341/34359738368), (-1530254075/34359738368)), (283/34359738368), by norm_num⟩
  | 9 => ⟨((58058437/17179869184), (1107936779/68719476736)), (103/34359738368), by norm_num⟩
  | 10 => ⟨((-75663997/68719476736), (-721952997/137438953472)), (135/137438953472), by norm_num⟩
  | 11 => ⟨((89643857/274877906944), (1710685499/1099511627776)), (161/549755813888), by norm_num⟩
  | 12 => ⟨((-194712227/2199023255552), (-464464875/1099511627776)), (177/2199023255552), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98840991975667/633825300114114700748351602688), (-2315280450967/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889490551902471/316912650057057350374175801344), (-85645240243/19807040628566084398385987584)), (46235/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889980505795845/39614081257132168796771975168), (-1541349860867/19807040628566084398385987584)), (52023/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889770216990497/2475880078570760549798248448), (-3274721416973/2475880078570760549798248448)), (110569/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771436153823461/154742504910672534362390528), (-818498412035/38685626227668133590597632)), (110591/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387445804528125/2417851639229258349412352), (-1534297977923/4835703278458516698824704)), (12963/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258989420417041/604462909807314587353088), (-671062139431/151115727451828646838272)), (90765/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472029405115445/18889465931478580854784), (-4360455106435/75557863725914323419136)), (147537/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81111443180683/295147905179352825856), (-817268506091/1180591620717411303424)), (110693/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405445558135441/147573952589676412928), (-2246459075791/295147905179352825856)), (76133/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823890940722791/73786976294838206464), (-2806530517741/36893488147419103232)), (47607/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823123422739243/9223372036854775808), (-3155225808959/4611686018427387904)), (53591/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594369634873339/1152921504606846976), (-6305152211985/1152921504606846976)), (214529/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194913989163261/144115188075855872), (-1377762672009/36028797018963968)), (187899/144115188075855872), by norm_num⟩
  | 4 => ⟨((746066050500547/18014398509481984), (-4127335935007/18014398509481984)), (282221/36028797018963968), by norm_num⟩
  | 3 => ⟨((744933543762309/4503599627370496), (-5148765960213/4503599627370496)), (353429/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229140101594567/4503599627370496), (-10266368759023/2251799813685248)), (708819/4503599627370496), by norm_num⟩
  | 1 => ⟨((138614072746887/140737488355328), (-30643631300283/2251799813685248)), (534071/1125899906842624), by norm_num⟩
  | 0 => ⟨((2183911724247435/2251799813685248), (-30333703155171/1125899906842624)), (1078001/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2183911724247435/2251799813685248), (-30333703155171/1125899906842624)), (4112247471335982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2116435864393021/2251799813685248), (-117676766038989/2251799813685248)), (2149089/1125899906842624), by norm_num⟩
  | 2 => ⟨((247882433847193/281474976710656), (-110602783842985/1125899906842624)), (2132209/562949953421312), by norm_num⟩
  | 3 => ⟨((1724661729636363/2251799813685248), (-389611717100623/2251799813685248)), (16697591/2251799813685248), by norm_num⟩
  | 4 => ⟨((156689150075395/281474976710656), (-74601260491453/281474976710656)), (31355607/2251799813685248), by norm_num⟩
  | 5 => ⟨((269809301079761/1125899906842624), (-332227276116979/1125899906842624)), (51530345/2251799813685248), by norm_num⟩
  | 6 => ⟨((-267007067456563/9007199254740992), (-1273832725257121/9007199254740992)), (110216381/4503599627370496), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64910875/33554432), (-1535441123/33554432)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-65662773/33554432), (-1553226983/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-855022395744557/9007199254740992), (-471338136075923/4503599627370496)), (57712913/2251799813685248), by norm_num⟩
  | 1 => ⟨((671866973/2147483648), (370372201/1073741824)), (183/2147483648), by norm_num⟩
  | 2 => ⟨((-553590985/1073741824), (-610343177/1073741824)), (19/134217728), by norm_num⟩
  | 3 => ⟨((608181859/1073741824), (670530515/1073741824)), (169/1073741824), by norm_num⟩
  | 4 => ⟨((-62639631/134217728), (-276244899/536870912)), (281/2147483648), by norm_num⟩
  | 5 => ⟨((41290001/134217728), (364183249/1073741824)), (187/2147483648), by norm_num⟩
  | 6 => ⟨((-90723405/536870912), (-800192385/4294967296)), (207/4294967296), by norm_num⟩
  | 7 => ⟨((42715649/536870912), (94189413/1073741824)), (197/8589934592), by norm_num⟩
  | 8 => ⟨((-563135243/17179869184), (-620865879/17179869184)), (41/4294967296), by norm_num⟩
  | 9 => ⟨((824889731/68719476736), (56840907/4294967296)), (121/34359738368), by norm_num⟩
  | 10 => ⟨((-543740397/137438953472), (-299741371/68719476736)), (161/137438953472), by norm_num⟩
  | 11 => ⟨((325832663/274877906944), (718471753/549755813888)), (195/549755813888), by norm_num⟩
  | 12 => ⟨((-715927535/2199023255552), (-789321897/2199023255552)), (27/274877906944), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581426682289427/10141204801825835211973625643008), (-3005742696061/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889471899027205/316912650057057350374175801344), (-3557831273273/633825300114114700748351602688)), (92551/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944969193675369/19807040628566084398385987584), (-2000929920157/19807040628566084398385987584)), (52071/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889725271878451/2475880078570760549798248448), (-2125562841743/1237940039285380274899124224)), (110677/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442847747581011/38685626227668133590597632), (-2125084547041/77371252455336267181195264)), (55353/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774870322720159/4835703278458516698824704), (-1991758657189/4835703278458516698824704)), (51909/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258951937600577/604462909807314587353088), (-1742280812033/302231454903657293676544)), (11359/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1888056276741053/75557863725914323419136), (-2830253992113/37778931862957161709568)), (147725/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297736703570857/4722366482869645213696), (-265232175573/295147905179352825856)), (110845/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810858916945225/295147905179352825856), (-1458100265195/147573952589676412928)), (152495/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823809519414881/73786976294838206464), (-7286442417101/73786976294838206464)), (190743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911515278247735/4611686018427387904), (-8191668823053/9223372036854775808)), (214757/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797137593651517/576460752303423488), (-4092349179907/576460752303423488)), (53743/288230376151711744), by norm_num⟩
  | 5 => ⟨((597414786171909/72057594037927936), (-7153773637343/144115188075855872)), (94171/72057594037927936), by norm_num⟩
  | 4 => ⟨((746000967431457/18014398509481984), (-10714996468475/36028797018963968)), (282997/36028797018963968), by norm_num⟩
  | 3 => ⟨((372424551141615/2251799813685248), (-13366358081947/9007199254740992)), (177297/4503599627370496), by norm_num⟩
  | 2 => ⟨((139298993431209/281474976710656), (-13325325832257/2251799813685248)), (355867/2251799813685248), by norm_num⟩
  | 1 => ⟨((69288907783841/70368744177664), (-9942789948937/562949953421312)), (536991/1125899906842624), by norm_num⟩
  | 0 => ⟨((545642513191619/562949953421312), (-39362557047819/1125899906842624)), (543393/562949953421312), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((545642513191619/562949953421312), (-39362557047819/1125899906842624)), (2072879793407249273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1056358199057181/1125899906842624), (-19076193560981/281474976710656)), (2182739/1125899906842624), by norm_num⟩
  | 2 => ⟨((985940419211775/1125899906842624), (-71591775973957/562949953421312)), (2195851/562949953421312), by norm_num⟩
  | 3 => ⟨((422585069464829/562949953421312), (-501538193133503/2251799813685248)), (2202139/281474976710656), by norm_num⟩
  | 4 => ⟨((1157167559898427/2251799813685248), (-188242801066517/562949953421312)), (8574157/562949953421312), by norm_num⟩
  | 5 => ⟨((685736913676915/4503599627370496), (-386941079672785/1125899906842624)), (116371481/4503599627370496), by norm_num⟩
  | 6 => ⟨((-855022395744557/9007199254740992), (-471338136075923/4503599627370496)), (57712913/2251799813685248), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-65662773/33554432), (-1553226983/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile040Terms3
