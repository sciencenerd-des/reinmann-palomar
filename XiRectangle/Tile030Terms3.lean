/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile030Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (1551/128))
  have he : value ((7/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-45376701/16777216), (-5027090237/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1169233789727035/18014398509481984), (36444185868299/2251799813685248)), (5870439/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3446723253/17179869184), (-859455305/17179869184)), (71/17179869184), by norm_num⟩
  | 2 => ⟨((2663491975/8589934592), (1328306417/17179869184)), (7/1073741824), by norm_num⟩
  | 3 => ⟨((-5488644513/17179869184), (-1368617175/17179869184)), (59/8589934592), by norm_num⟩
  | 4 => ⟨((1060352075/4294967296), (132201681/2147483648)), (93/17179869184), by norm_num⟩
  | 5 => ⟨((-5244149247/34359738368), (-1307651227/34359738368)), (117/34359738368), by norm_num⟩
  | 6 => ⟨((5403295985/68719476736), (84208447/4294967296)), (123/68719476736), by norm_num⟩
  | 7 => ⟨((-2385973897/68719476736), (-594952879/68719476736)), (111/137438953472), by norm_num⟩
  | 8 => ⟨((460946663/34359738368), (919512303/274877906944)), (11/34359738368), by norm_num⟩
  | 9 => ⟨((-5065975837/1099511627776), (-631611459/549755813888)), (123/1099511627776), by norm_num⟩
  | 10 => ⟨((782957319/549755813888), (1561870267/4398046511104)), (77/2199023255552), by norm_num⟩
  | 11 => ⟨((-1760112227/4398046511104), (-438891573/4398046511104)), (11/1099511627776), by norm_num⟩
  | 12 => ⟨((3627054411/35184372088832), (113052707/4398046511104)), (23/8796093022208), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (79580083725/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777798257308435/633825300114114700748351602688), (376323856757/633825300114114700748351602688)), (5765/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236081287027327/4951760157141521099596496896), (105816471631/9903520314283042199192993792)), (25943/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944178747335621/1237940039285380274899124224), (7024937653/38685626227668133590597632)), (13783/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885012067311883/77371252455336267181195264), (224728294811/77371252455336267181195264)), (13783/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548460196830023/9671406556917033397649408), (210608739935/4835703278458516698824704)), (6461/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628916261560653/302231454903657293676544), (368417290685/604462909807314587353088)), (22615/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943119530444109/37778931862957161709568), (18700022981/2361183241434822606848)), (18375/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648187697048337/2361183241434822606848), (448558005635/4722366482869645213696)), (6891/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((202481079385597/73786976294838206464), (308186696929/295147905179352825856)), (18951/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821476919635799/73786976294838206464), (384938212115/36893488147419103232)), (47381/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910205868118593/4611686018427387904), (108162508187/1152921504606846976)), (53309/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591663050783037/1152921504606846976), (864287587961/1152921504606846976)), (26657/576460752303423488), by norm_num⟩
  | 5 => ⟨((298137864803319/36028797018963968), (755114198191/144115188075855872)), (46657/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488599745654873/36028797018963968), (1130400398531/36028797018963968)), (34999/18014398509481984), by norm_num⟩
  | 3 => ⟨((1485471611661895/9007199254740992), (88064710761/562949953421312)), (87521/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220408851485921/4503599627370496), (2806211070345/4503599627370496)), (175113/4503599627370496), by norm_num⟩
  | 1 => ⟨((275609604131115/281474976710656), (1044948002513/562949953421312)), (65713/562949953421312), by norm_num⟩
  | 0 => ⟨((1079302498074483/1125899906842624), (4121115094901/1125899906842624)), (526449/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1079302498074483/1125899906842624), (4121115094901/1125899906842624)), (2008243569380950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258654630771503/281474976710656), (987638818901/140737488355328)), (1013177/2251799813685248), by norm_num⟩
  | 2 => ⟨((1901364507199223/2251799813685248), (14521069376681/1125899906842624)), (938145/1125899906842624), by norm_num⟩
  | 3 => ⟨((802545484160605/1125899906842624), (49044938633711/2251799813685248)), (3216985/2251799813685248), by norm_num⟩
  | 4 => ⟨((1143046373366701/2251799813685248), (17479703916043/562949953421312)), (1181573/562949953421312), by norm_num⟩
  | 5 => ⟨((144513997533445/562949953421312), (35491808902955/1125899906842624)), (10183549/4503599627370496), by norm_num⟩
  | 6 => ⟨((1169233789727035/18014398509481984), (36444185868299/2251799813685248)), (5870439/4503599627370496), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-5027090237/134217728)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-184117023/67108864), (-5099383977/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1109245419880625/18014398509481984), (-168082570532157/9007199254740992)), (23565011/18014398509481984), by norm_num⟩
  | 1 => ⟨((-414613795/2147483648), (1005214553/17179869184)), (9/2147483648), by norm_num⟩
  | 2 => ⟨((325004789/1073741824), (-49247569/536870912)), (115/17179869184), by norm_num⟩
  | 3 => ⟨((-2717468363/8589934592), (1647098323/17179869184)), (123/17179869184), by norm_num⟩
  | 4 => ⟨((4260303167/17179869184), (-80694801/1073741824)), (49/8589934592), by norm_num⟩
  | 5 => ⟨((-5343262375/34359738368), (1619315723/34359738368)), (125/34359738368), by norm_num⟩
  | 6 => ⟨((349036839/4294967296), (-846225847/34359738368)), (133/68719476736), by norm_num⟩
  | 7 => ⟨((-625373137/17179869184), (758096071/68719476736)), (121/137438953472), by norm_num⟩
  | 8 => ⟨((980426927/68719476736), (-1188502923/274877906944)), (97/274877906944), by norm_num⟩
  | 9 => ⟨((-2732553741/549755813888), (414060449/274877906944)), (137/1099511627776), by norm_num⟩
  | 10 => ⟨((856790645/549755813888), (-519313657/1099511627776)), (11/274877906944), by norm_num⟩
  | 11 => ⟨((-3907581253/8796093022208), (1184221795/8796093022208)), (51/4398046511104), by norm_num⟩
  | 12 => ⟨((4084066139/35184372088832), (-1237706863/35184372088832)), (27/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395100494305569/2535301200456458802993406410752), (-383305816811/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777738327455071/633825300114114700748351602688), (-453121709173/633825300114114700748351602688)), (11531/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944291444526403/19807040628566084398385987584), (-63705221747/4951760157141521099596496896)), (12973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944142945965355/1237940039285380274899124224), (-135335735523/618970019642690137449562112)), (1723/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1769952551419707/154742504910672534362390528), (-270586330327/77371252455336267181195264)), (27569/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548393108326427/9671406556917033397649408), (-507168520861/9671406556917033397649408)), (25847/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257773841422663/604462909807314587353088), (-110897923067/151115727451828646838272)), (22617/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471535935500437/18889465931478580854784), (-720497748957/75557863725914323419136)), (18377/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324075984732249/1180591620717411303424), (-270038542529/2361183241434822606848)), (1723/295147905179352825856), by norm_num⟩
  | 9 => ⟨((809875219720989/295147905179352825856), (-371062480865/295147905179352825856)), (9477/147573952589676412928), by norm_num⟩
  | 8 => ⟨((227669282230543/9223372036854775808), (-57933453001/4611686018427387904)), (11847/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820273855426891/9223372036854775808), (-1041811801855/9223372036854775808)), (53317/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591525311965159/1152921504606846976), (-1040575299767/1152921504606846976)), (53325/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298107774324561/36028797018963968), (-454557148657/72057594037927936)), (46667/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488419521406995/36028797018963968), (-1360898195549/36028797018963968)), (547/281474976710656), by norm_num⟩
  | 3 => ⟨((1485246887874603/9007199254740992), (-26504384793/140737488355328)), (21887/2251799813685248), by norm_num⟩
  | 2 => ⟨((1109980534602333/2251799813685248), (-3378079078249/4503599627370496)), (87591/2251799813685248), by norm_num⟩
  | 1 => ⟨((551052326984167/562949953421312), (-5031067332793/2251799813685248)), (262989/2251799813685248), by norm_num⟩
  | 0 => ⟨((2157286449912167/2251799813685248), (-4959425354837/1125899906842624)), (526863/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2157286449912167/2251799813685248), (-4959425354837/1125899906842624)), (2009822854048918967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2066696344449443/2251799813685248), (-19005066173855/2251799813685248)), (1014141/2251799813685248), by norm_num⟩
  | 2 => ⟨((474162108201661/562949953421312), (-34885606214919/2251799813685248)), (117417/140737488355328), by norm_num⟩
  | 3 => ⟨((798485338326253/1125899906842624), (-3672935864065/140737488355328)), (3222951/2251799813685248), by norm_num⟩
  | 4 => ⟨((1131033837642641/2251799813685248), (-41677387742831/1125899906842624)), (2369821/1125899906842624), by norm_num⟩
  | 5 => ⟨((35313128068825/140737488355328), (-167469720941307/4503599627370496)), (10224297/4503599627370496), by norm_num⟩
  | 6 => ⟨((1109245419880625/18014398509481984), (-168082570532157/9007199254740992)), (23565011/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-184117023/67108864), (-5099383977/134217728)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-373232269/134217728), (-5168600439/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((384995288802033/9007199254740992), (-808779505160199/18014398509481984)), (32577365/18014398509481984), by norm_num⟩
  | 1 => ⟨((-583427311/4294967296), (153204489/1073741824)), (25/4294967296), by norm_num⟩
  | 2 => ⟨((3708326801/17179869184), (-3895136905/17179869184)), (161/17179869184), by norm_num⟩
  | 3 => ⟨((-3928420731/17179869184), (4126318253/17179869184)), (173/17179869184), by norm_num⟩
  | 4 => ⟨((1560591569/8589934592), (-1639207691/8589934592)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((-3967715211/34359738368), (4167592225/34359738368)), (179/34359738368), by norm_num⟩
  | 6 => ⟨((2101602087/34359738368), (-275934009/4294967296)), (97/34359738368), by norm_num⟩
  | 7 => ⟨((-954143509/34359738368), (4008837185/137438953472)), (89/68719476736), by norm_num⟩
  | 8 => ⟨((3032319433/274877906944), (-3185075093/274877906944)), (9/17179869184), by norm_num⟩
  | 9 => ⟨((-1070763821/274877906944), (2249408911/549755813888)), (103/549755813888), by norm_num⟩
  | 10 => ⟨((1361178025/1099511627776), (-1429748521/1099511627776)), (133/2199023255552), by norm_num⟩
  | 11 => ⟨((-3146106935/8796093022208), (3304594737/8796093022208)), (39/2199023255552), by norm_num⟩
  | 12 => ⟨((1666416199/17592186044416), (-1750363327/17592186044416)), (167/35184372088832), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790176734201497/5070602400912917605986812821504), (-1055066329797/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444420065136005/158456325028528675187087900672), (-311790235901/158456325028528675187087900672)), (11541/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472129384928619/9903520314283042199192993792), (-1402720598353/39614081257132168796771975168)), (25969/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472054106124391/618970019642690137449562112), (-1489968096239/2475880078570760549798248448)), (13797/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((221235380758677/19342813113834066795298816), (-372373247311/38685626227668133590597632)), (27597/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548327906817845/9671406556917033397649408), (-1395895084655/9671406556917033397649408)), (25875/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314429187477467/151115727451828646838272), (-1220903840903/604462909807314587353088)), (22643/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886050893037921/75557863725914323419136), (-1983023568137/75557863725914323419136)), (575/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1296234236463363/4722366482869645213696), (-743220573689/2361183241434822606848)), (27605/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404913622979487/147573952589676412928), (-1021257200733/295147905179352825856)), (37963/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227654270479379/9223372036854775808), (-1275565684523/36893488147419103232)), (47465/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113758658173287/576460752303423488), (-2867259443869/9223372036854775808)), (53413/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795694857267585/576460752303423488), (-2863809229981/1152921504606846976)), (6679/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192312143829123/144115188075855872), (-2501957036225/144115188075855872)), (46775/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488240482647237/36028797018963968), (-3745197080613/36028797018963968)), (70205/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485022030911217/9007199254740992), (-4667984580319/9007199254740992)), (87831/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109754102737787/2251799813685248), (-9295555806121/4503599627370496)), (10993/281474976710656), by norm_num⟩
  | 1 => ⟨((275440278434837/281474976710656), (-3460681481495/562949953421312)), (132201/1125899906842624), by norm_num⟩
  | 0 => ⟨((67371302620275/70368744177664), (-27285564398655/2251799813685248)), (265553/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((67371302620275/70368744177664), (-27285564398655/2251799813685248)), (1013004307273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2063718677161123/2251799813685248), (-26123302863351/1125899906842624)), (514919/1125899906842624), by norm_num⟩
  | 2 => ⟨((1890134746786429/2251799813685248), (-95765436519873/2251799813685248)), (241929/281474976710656), by norm_num⟩
  | 3 => ⟨((197810564715881/281474976710656), (-160768801922179/2251799813685248)), (3413781/2251799813685248), by norm_num⟩
  | 4 => ⟨((1100635423323089/2251799813685248), (-225965148792695/2251799813685248)), (2642813/1125899906842624), by norm_num⟩
  | 5 => ⟨((1030587248078421/4503599627370496), (-441789266854387/4503599627370496)), (12455663/4503599627370496), by norm_num⟩
  | 6 => ⟨((384995288802033/9007199254740992), (-808779505160199/18014398509481984)), (32577365/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-373232269/134217728), (-5168600439/134217728)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-378026425/134217728), (-2617495469/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((283443866049001/18014398509481984), (-259890896244529/4503599627370496)), (9999977/4503599627370496), by norm_num⟩
  | 1 => ⟨((-27190763/536870912), (3191209881/17179869184)), (247/34359738368), by norm_num⟩
  | 2 => ⟨((1400379035/17179869184), (-5136054169/17179869184)), (25/2147483648), by norm_num⟩
  | 3 => ⟨((-1502548741/17179869184), (5510773533/17179869184)), (217/17179869184), by norm_num⟩
  | 4 => ⟨((1209129455/17179869184), (-2217311963/8589934592)), (177/17179869184), by norm_num⟩
  | 5 => ⟨((-1556815029/34359738368), (5709801499/34359738368)), (115/17179869184), by norm_num⟩
  | 6 => ⟨((1670398087/68719476736), (-3063190335/34359738368)), (249/68719476736), by norm_num⟩
  | 7 => ⟨((-192028715/17179869184), (5634302467/137438953472)), (231/137438953472), by norm_num⟩
  | 8 => ⟨((1236233177/274877906944), (-283376875/17179869184)), (47/68719476736), by norm_num⟩
  | 9 => ⟨((-442142343/274877906944), (3243217679/549755813888)), (271/1099511627776), by norm_num⟩
  | 10 => ⟨((1138561039/2199023255552), (-4175805993/2199023255552)), (11/137438953472), by norm_num⟩
  | 11 => ⟨((-666343019/4398046511104), (4887782167/8796093022208)), (13/549755813888), by norm_num⟩
  | 12 => ⟨((1429916957/35184372088832), (-327774247/2199023255552)), (225/35184372088832), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940097431/10141204801825835211973625643008), (-1699400269687/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888811965976699/316912650057057350374175801344), (-502172351235/158456325028528675187087900672)), (5775/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944227056404785/19807040628566084398385987584), (-2259227115485/39614081257132168796771975168)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472037238683309/618970019642690137449562112), (-1199869673883/1237940039285380274899124224)), (27619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769815487922177/154742504910672534362390528), (-1199482043367/77371252455336267181195264)), (3453/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1548264477239495/9671406556917033397649408), (-1124102722931/4835703278458516698824704)), (12951/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((9825477775911/4722366482869645213696), (-1966356750359/604462909807314587353088)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((14734065440097/590295810358705651712), (-3193787353951/75557863725914323419136)), (36843/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296166195597921/4722366482869645213696), (-2393991732633/4722366482869645213696)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((101222542935381/36893488147419103232), (-3289548334757/590295810358705651712)), (297/4611686018427387904), by norm_num⟩
  | 8 => ⟨((1821116535218387/73786976294838206464), (-2054326275273/36893488147419103232)), (23769/36893488147419103232), by norm_num⟩
  | 7 => ⟨((910002843826883/4611686018427387904), (-1154431090667/2305843009213693952)), (53505/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591256234499731/1152921504606846976), (-4612093440805/1152921504606846976)), (53535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298048658663589/36028797018963968), (-4029255590637/144115188075855872)), (23439/72057594037927936), by norm_num⟩
  | 4 => ⟨((1488062796551963/36028797018963968), (-1507813139807/9007199254740992)), (70385/36028797018963968), by norm_num⟩
  | 3 => ⟨((371199361891893/2251799813685248), (-3758505038665/4503599627370496)), (44051/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219051664853985/4503599627370496), (-14968046189915/4503599627370496)), (88283/2251799813685248), by norm_num⟩
  | 1 => ⟨((550704791794133/562949953421312), (-11143903863997/1125899906842624)), (8305/70368744177664), by norm_num⟩
  | 0 => ⟨((2154403671612995/2251799813685248), (-21961297510225/1125899906842624)), (535187/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((2154403671612995/2251799813685248), (-21961297510225/1125899906842624)), (2041576394087981467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2060363429159927/2251799813685248), (-84045659302159/2251799813685248)), (1044957/2251799813685248), by norm_num⟩
  | 2 => ⟨((1882065075951953/2251799813685248), (-76900531634029/1125899906842624)), (1990245/2251799813685248), by norm_num⟩
  | 3 => ⟨((390633545849855/562949953421312), (-64273832882897/562949953421312)), (3598787/2251799813685248), by norm_num⟩
  | 4 => ⟨((1054896199191349/2251799813685248), (-89199812849497/562949953421312)), (5816201/2251799813685248), by norm_num⟩
  | 5 => ⟨((218825021496325/1125899906842624), (-668596154749779/4503599627370496)), (7292571/2251799813685248), by norm_num⟩
  | 6 => ⟨((283443866049001/18014398509481984), (-259890896244529/4503599627370496)), (9999977/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/134217728), (-2617495469/67108864)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-191316263/67108864), (-5298777207/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-216081575585375/18014398509481984), (-1018491995424541/18014398509481984)), (2797039/1125899906842624), by norm_num⟩
  | 1 => ⟨((335700337/8589934592), (6329241265/34359738368)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((-546872053/8589934592), (-5155319763/17179869184)), (115/8589934592), by norm_num⟩
  | 3 => ⟨((1187841295/17179869184), (5598843157/17179869184)), (63/4294967296), by norm_num⟩
  | 4 => ⟨((-967525403/17179869184), (-4560392877/17179869184)), (207/17179869184), by norm_num⟩
  | 5 => ⟨((630458233/17179869184), (2971640049/17179869184)), (17/2147483648), by norm_num⟩
  | 6 => ⟨((-684697929/34359738368), (-6454593437/68719476736)), (149/34359738368), by norm_num⟩
  | 7 => ⟨((1274749687/137438953472), (3004241219/68719476736)), (35/17179869184), by norm_num⟩
  | 8 => ⟨((-519157193/137438953472), (-4894053957/274877906944)), (115/137438953472), by norm_num⟩
  | 9 => ⟨((375880945/274877906944), (442925007/68719476736)), (21/68719476736), by norm_num⟩
  | 10 => ⟨((-244931281/549755813888), (-2308947891/1099511627776)), (221/2199023255552), by norm_num⟩
  | 11 => ⟨((1160741467/8796093022208), (2735554593/4398046511104)), (33/1099511627776), by norm_num⟩
  | 12 => ⟨((-1260602585/35184372088832), (-5941800633/35184372088832)), (289/35184372088832), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395065559226429/2535301200456458802993406410752), (-2318459602493/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444392307402603/158456325028528675187087900672), (-2740261511239/633825300114114700748351602688)), (11559/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944196243178583/19807040628566084398385987584), (-385254284507/4951760157141521099596496896)), (6503/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888083358362295/2475880078570760549798248448), (-3273709049693/2475880078570760549798248448)), (27643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769749758690339/154742504910672534362390528), (-3272638116101/154742504910672534362390528)), (27649/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548202715054891/9671406556917033397649408), (-3066960799053/9671406556917033397649408)), (25927/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628803486263653/302231454903657293676544), (-2682453750539/604462909807314587353088)), (5673/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((942936032738335/37778931862957161709568), (-2178428299301/37778931862957161709568)), (18443/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296099731933271/4722366482869645213696), (-1632889539185/2361183241434822606848)), (13837/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1619468925431455/590295810358705651712), (-1121855047477/147573952589676412928)), (9517/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455250318340495/18446744073709551616), (-5604739556189/73786976294838206464)), (47609/73786976294838206464), by norm_num⟩
  | 7 => ⟨((454968812465817/2305843009213693952), (-3149550466395/4611686018427387904)), (53593/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591124839021855/1152921504606846976), (-786415041481/144115188075855872)), (26817/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192078589733347/144115188075855872), (-5496163425251/144115188075855872)), (46977/144115188075855872), by norm_num⟩
  | 4 => ⟨((743943295097895/18014398509481984), (-8226789652763/36028797018963968)), (70559/36028797018963968), by norm_num⟩
  | 3 => ⟨((742286733059615/4503599627370496), (-10253003429913/9007199254740992)), (44181/4503599627370496), by norm_num⟩
  | 2 => ⟨((1109296304992045/2251799813685248), (-318981396261/70368744177664)), (88609/2251799813685248), by norm_num⟩
  | 1 => ⟨((2202103128585861/2251799813685248), (-30395105234951/2251799813685248)), (267067/2251799813685248), by norm_num⟩
  | 0 => ⟨((1076431700684507/1125899906842624), (-59887068998007/2251799813685248)), (269559/1125899906842624), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1076431700684507/1125899906842624), (-59887068998007/2251799813685248)), (1028285984519576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2056681209304129/2251799813685248), (-57255835211243/1125899906842624)), (529769/1125899906842624), by norm_num⟩
  | 2 => ⟨((1872646337571447/2251799813685248), (-104589226525655/1125899906842624)), (2043221/2251799813685248), by norm_num⟩
  | 3 => ⟨((384475638037653/562949953421312), (-173957410256785/1125899906842624)), (1888991/1125899906842624), by norm_num⟩
  | 4 => ⟨((124572548808509/281474976710656), (-475227937356629/2251799813685248)), (6327903/2251799813685248), by norm_num⟩
  | 5 => ⟨((681526730358381/4503599627370496), (-841287649983623/4503599627370496)), (8272015/2251799813685248), by norm_num⟩
  | 6 => ⟨((-216081575585375/18014398509481984), (-1018491995424541/18014398509481984)), (2797039/1125899906842624), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-191316263/67108864), (-5298777207/134217728)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-387064769/134217728), (-670019483/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-311335220377031/9007199254740992), (-791844197552999/18014398509481984)), (46210777/18014398509481984), by norm_num⟩
  | 1 => ⟨((1957149691/17179869184), (2488889025/17179869184)), (147/17179869184), by norm_num⟩
  | 2 => ⟨((-806305763/4294967296), (-2050743051/8589934592)), (61/4294967296), by norm_num⟩
  | 3 => ⟨((3543269679/17179869184), (4505943033/17179869184)), (271/17179869184), by norm_num⟩
  | 4 => ⟨((-729877427/4294967296), (-3712713291/17179869184)), (225/17179869184), by norm_num⟩
  | 5 => ⟨((1924445545/17179869184), (2447299467/17179869184)), (75/8589934592), by norm_num⟩
  | 6 => ⟨((-2114219525/34359738368), (-672158317/8589934592)), (167/34359738368), by norm_num⟩
  | 7 => ⟨((1990892187/68719476736), (2531799041/68719476736)), (159/68719476736), by norm_num⟩
  | 8 => ⟨((-3280827933/274877906944), (-1043049577/68719476736)), (33/34359738368), by norm_num⟩
  | 9 => ⟨((300363157/68719476736), (3055752221/549755813888)), (195/549755813888), by norm_num⟩
  | 10 => ⟨((-3167833491/2199023255552), (-4028504329/2199023255552)), (259/2199023255552), by norm_num⟩
  | 11 => ⟨((1898302255/4398046511104), (301756661/549755813888)), (157/4398046511104), by norm_num⟩
  | 12 => ⟨((-2085498185/17592186044416), (-41439197/274877906944)), (87/8796093022208), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580219221042939/10141204801825835211973625643008), (-2914152547803/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777516052350003/633825300114114700748351602688), (-3444142088065/633825300114114700748351602688)), (23135/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944166275032691/19807040628566084398385987584), (-60526396881/618970019642690137449562112)), (26033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236002440349007/309485009821345068724781056), (-2057291790903/1237940039285380274899124224)), (27667/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769685750939751/154742504910672534362390528), (-2056610640035/77371252455336267181195264)), (27673/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548142525022069/9671406556917033397649408), (-3854698016387/9671406556917033397649408)), (25951/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157194265459865/75557863725914323419136), (-3371414406293/604462909807314587353088)), (22715/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942892922099087/37778931862957161709568), (-5475837711751/75557863725914323419136)), (18463/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648017383614955/2361183241434822606848), (-2052253822551/2361183241434822606848)), (27707/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809689557143661/295147905179352825856), (-5639848015345/590295810358705651712)), (38117/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1820888283784631/73786976294838206464), (-7044039032105/73786976294838206464)), (47677/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1819747141044535/9223372036854775808), (-7916615313525/9223372036854775808)), (53677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795497744549403/576460752303423488), (-7906714325301/1152921504606846976)), (26865/576460752303423488), by norm_num⟩
  | 5 => ⟨((595982008436667/72057594037927936), (-3453624915973/72057594037927936)), (1471/4503599627370496), by norm_num⟩
  | 4 => ⟨((1487711958939103/36028797018963968), (-1292332229679/4503599627370496)), (35363/18014398509481984), by norm_num⟩
  | 3 => ⟨((1484350351662467/9007199254740992), (-6442258995305/4503599627370496)), (44307/4503599627370496), by norm_num⟩
  | 2 => ⟨((554533001700025/1125899906842624), (-6413230957347/1125899906842624)), (177847/4503599627370496), by norm_num⟩
  | 1 => ⟨((275172080403897/281474976710656), (-38190156327859/2251799813685248)), (268327/2251799813685248), by norm_num⟩
  | 0 => ⟨((2151270226899007/2251799813685248), (-18807421749413/562949953421312)), (542911/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2151270226899007/2251799813685248), (-18807421749413/562949953421312)), (2071041115767668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2052715368055553/2251799813685248), (-35935562485041/562949953421312)), (1073623/2251799813685248), by norm_num⟩
  | 2 => ⟨((1862056530225679/2251799813685248), (-262067634696323/2251799813685248)), (1047237/1125899906842624), by norm_num⟩
  | 3 => ⟨((188658815047969/281474976710656), (-433417524578671/2251799813685248)), (1975719/1125899906842624), by norm_num⟩
  | 4 => ⟨((464083605564167/1125899906842624), (-145249211073015/562949953421312)), (852253/281474976710656), by norm_num⟩
  | 5 => ⟨((232674785543637/2251799813685248), (-957922133865673/4503599627370496)), (18277855/4503599627370496), by norm_num⟩
  | 6 => ⟨((-311335220377031/9007199254740992), (-791844197552999/18014398509481984)), (46210777/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-387064769/134217728), (-670019483/16777216)), (1/67108864), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile030Terms3
