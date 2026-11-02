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
namespace Reinmann.XiRectangle.Tile034Terms2
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
  | 0 => ⟨((-10175445/4194304), (-1209278953/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-141515353887245/18014398509481984), (1585961718096777/18014398509481984)), (264068987/18014398509481984), by norm_num⟩
  | 1 => ⟨((93546837/4294967296), (-1048378843/4294967296)), (11/268435456), by norm_num⟩
  | 2 => ⟨((-129683453/4294967296), (726680839/2147483648)), (123/2147483648), by norm_num⟩
  | 3 => ⟨((3745405/134217728), (-1343191399/4294967296)), (229/4294967296), by norm_num⟩
  | 4 => ⟨((-166151483/8589934592), (931029331/4294967296)), (5/134217728), by norm_num⟩
  | 5 => ⟨((46066973/4294967296), (-1032544569/8589934592)), (179/8589934592), by norm_num⟩
  | 6 => ⟨((-170299693/34359738368), (954273809/17179869184)), (333/34359738368), by norm_num⟩
  | 7 => ⟨((67453001/34359738368), (-1511890743/68719476736)), (133/34359738368), by norm_num⟩
  | 8 => ⟨((-93509715/137438953472), (523981403/68719476736)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((28807109/137438953472), (-1291364381/549755813888)), (231/549755813888), by norm_num⟩
  | 10 => ⟨((-127792425/2199023255552), (44755279/68719476736)), (129/1099511627776), by norm_num⟩
  | 11 => ⟨((64421061/4398046511104), (-1443932879/8796093022208)), (131/4398046511104), by norm_num⟩
  | 12 => ⟨((-119075405/35184372088832), (1334477339/35184372088832)), (61/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395203902880331/2535301200456458802993406410752), (2162062611011/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889112017836529/316912650057057350374175801344), (1278602412959/316912650057057350374175801344)), (23113/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118070562505003/2475880078570760549798248448), (719061468081/9903520314283042199192993792)), (104025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888865731853545/2475880078570760549798248448), (3055254683103/2475880078570760549798248448)), (110545/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770531938291039/154742504910672534362390528), (3054403854763/154742504910672534362390528)), (110567/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548935802443981/9671406556917033397649408), (2862599892321/9671406556917033397649408)), (51839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258248218030931/604462909807314587353088), (156491968953/37778931862957161709568)), (90741/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886913703294295/75557863725914323419136), (4067097990661/75557863725914323419136)), (18437/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648440311244609/2361183241434822606848), (762210654635/1180591620717411303424)), (110659/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620542101108243/590295810358705651712), (4189753449107/590295810358705651712)), (19027/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1822341919875523/73786976294838206464), (2616793152553/36893488147419103232)), (190359/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455345586434069/2305843009213693952), (5882830629005/9223372036854775808)), (107139/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796315260501695/576460752303423488), (5876643580719/1152921504606846976)), (6701/36028797018963968), by norm_num⟩
  | 5 => ⟨((1193394471428737/144115188075855872), (5135110133039/144115188075855872)), (187803/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489857234142833/36028797018963968), (7688777756235/36028797018963968)), (282053/36028797018963968), by norm_num⟩
  | 3 => ⟨((371757802965421/2251799813685248), (9586710877805/9007199254740992)), (353177/9007199254740992), by norm_num⟩
  | 2 => ⟨((2223491437400365/4503599627370496), (4775201103385/1125899906842624)), (708191/4503599627370496), by norm_num⟩
  | 1 => ⟨((552352439312107/562949953421312), (3558780674855/281474976710656)), (1066895/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167310498606583/2251799813685248), (7027516337153/281474976710656)), (538075/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167310498606583/2251799813685248), (7027516337153/281474976710656)), (2052593233348655523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2084587655504101/2251799813685248), (54110706801115/1125899906842624)), (66415/35184372088832), by norm_num⟩
  | 2 => ⟨((962295536392603/1125899906842624), (200370407249661/2251799813685248)), (517401/140737488355328), by norm_num⟩
  | 3 => ⟨((1627099565012775/2251799813685248), (342509218358907/2251799813685248)), (15624227/2251799813685248), by norm_num⟩
  | 4 => ⟨((561804032140663/1125899906842624), (123744703418503/562949953421312)), (13666231/1125899906842624), by norm_num⟩
  | 5 => ⟨((903713598294239/4503599627370496), (123492813018383/562949953421312)), (78585965/4503599627370496), by norm_num⟩
  | 6 => ⟨((-141515353887245/18014398509481984), (1585961718096777/18014398509481984)), (264068987/18014398509481984), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/4194304), (-1209278953/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-41591753/16777216), (-1235720697/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((971649270782287/18014398509481984), (1155853746434535/18014398509481984)), (90831033/9007199254740992), by norm_num⟩
  | 1 => ⟨((-328170023/2147483648), (-97596057/536870912)), (31/1073741824), by norm_num⟩
  | 2 => ⟨((116221961/536870912), (276510451/1073741824)), (89/2147483648), by norm_num⟩
  | 3 => ⟨((-878084295/4294967296), (-1044550799/4294967296)), (171/4294967296), by norm_num⟩
  | 4 => ⟨((621950035/4294967296), (5780147/33554432)), (123/4294967296), by norm_num⟩
  | 5 => ⟨((-704846855/8589934592), (-209617787/2147483648)), (141/8589934592), by norm_num⟩
  | 6 => ⟨((665660505/17179869184), (395927941/8589934592)), (135/17179869184), by norm_num⟩
  | 7 => ⟨((-538845207/34359738368), (-640999043/34359738368)), (111/34359738368), by norm_num⟩
  | 8 => ⟨((763331715/137438953472), (908043521/137438953472)), (159/137438953472), by norm_num⟩
  | 9 => ⟨((-961191823/549755813888), (-1143413787/549755813888)), (101/274877906944), by norm_num⟩
  | 10 => ⟨((136163075/274877906944), (20247095/34359738368)), (29/274877906944), by norm_num⟩
  | 11 => ⟨((-561133151/4398046511104), (-667512317/4398046511104)), (121/4398046511104), by norm_num⟩
  | 12 => ⟨((132484161/4398046511104), (630401601/17592186044416)), (29/4398046511104), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512500455/10141204801825835211973625643008), (1135571571137/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444536212323063/158456325028528675187087900672), (671496448539/316912650057057350374175801344)), (92333/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472260018905039/9903520314283042199192993792), (755271253301/19807040628566084398385987584)), (103883/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944385730110789/1237940039285380274899124224), (802272834787/1237940039285380274899124224)), (55193/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885218951683975/77371252455336267181195264), (802044705291/77371252455336267181195264)), (110397/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548847896031849/9671406556917033397649408), (751674611701/4835703278458516698824704)), (103509/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629085775525841/302231454903657293676544), (657473084849/302231454903657293676544)), (45291/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943394794953099/37778931862957161709568), (533969923841/18889465931478580854784)), (147217/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296787948676855/4722366482869645213696), (1601115840773/4722366482869645213696)), (110433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620415342080129/590295810358705651712), (2200244932213/590295810358705651712)), (37969/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911092235458833/36893488147419103232), (687093380287/18446744073709551616)), (189893/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910603294099883/4611686018427387904), (3089265065013/9223372036854775808)), (106847/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1592456475815339/1152921504606846976), (3085949488197/1152921504606846976)), (13361/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193244103712295/144115188075855872), (2696480387853/144115188075855872)), (93573/72057594037927936), by norm_num⟩
  | 4 => ⟨((93102219675803/2251799813685248), (2018640631157/18014398509481984)), (140451/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486760743530989/9007199254740992), (1258402155941/2251799813685248)), (175725/4503599627370496), by norm_num⟩
  | 2 => ⟨((555742610283333/1125899906842624), (5014170800831/2251799813685248)), (5499/35184372088832), by norm_num⟩
  | 1 => ⟨((2208677757758265/2251799813685248), (14945683632853/2251799813685248)), (132281/281474976710656), by norm_num⟩
  | 0 => ⟨((2166042353011185/2251799813685248), (14753103485909/1125899906842624)), (1063159/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2166042353011185/2251799813685248), (14753103485909/1125899906842624)), (4055629734519576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2083164245009591/2251799813685248), (28382493678723/1125899906842624)), (1036601/562949953421312), by norm_num⟩
  | 2 => ⟨((1925726692729363/2251799813685248), (3282118799837/70368744177664)), (3940409/1125899906842624), by norm_num⟩
  | 3 => ⟨((1641972094282867/2251799813685248), (44909596266187/562949953421312)), (7107207/1125899906842624), by norm_num⟩
  | 4 => ⟨((591482953508081/1125899906842624), (130989093056025/1125899906842624)), (5749429/562949953421312), by norm_num⟩
  | 5 => ⟨((1181966317854953/4503599627370496), (550512990842283/4503599627370496)), (29514537/2251799813685248), by norm_num⟩
  | 6 => ⟨((971649270782287/18014398509481984), (1155853746434535/18014398509481984)), (90831033/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-41591753/16777216), (-1235720697/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-84861685/33554432), (-1260650635/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((178055030637431/2251799813685248), (184482273422705/18014398509481984)), (25198165/4503599627370496), by norm_num⟩
  | 1 => ⟨((-122700985/536870912), (-31782529/1073741824)), (71/4294967296), by norm_num⟩
  | 2 => ⟨((1418605847/4294967296), (22965831/536870912)), (105/4294967296), by norm_num⟩
  | 3 => ⟨((-341691523/1073741824), (-44253193/1073741824)), (103/4294967296), by norm_num⟩
  | 4 => ⟨((123451941/536870912), (127908179/4294967296)), (19/1073741824), by norm_num⟩
  | 5 => ⟨((-285457603/2147483648), (-147880875/8589934592)), (45/4294967296), by norm_num⟩
  | 6 => ⟨((137513099/2147483648), (71238451/8589934592)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((-227122273/8589934592), (-117660347/34359738368)), (37/17179869184), by norm_num⟩
  | 8 => ⟨((1312935607/137438953472), (10627567/8589934592)), (109/137438953472), by norm_num⟩
  | 9 => ⟨((-1686609777/549755813888), (-218436405/549755813888)), (143/549755813888), by norm_num⟩
  | 10 => ⟨((974985853/1099511627776), (126272483/1099511627776)), (21/274877906944), by norm_num⟩
  | 11 => ⟨((-256188325/1099511627776), (-66358985/2199023255552)), (45/2199023255552), by norm_num⟩
  | 12 => ⟨((987305999/17592186044416), (127868091/17592186044416)), (11/2199023255552), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395170341040317/2535301200456458802993406410752), (167770128781/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889034374956283/316912650057057350374175801344), (198398310569/633825300114114700748351602688)), (23055/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944477267400633/19807040628566084398385987584), (111574686025/19807040628566084398385987584)), (103749/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944340332983193/1237940039285380274899124224), (118517537395/1237940039285380274899124224)), (110235/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770347213488779/154742504910672534362390528), (236966333599/154742504910672534362390528)), (110237/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548762985096081/9671406556917033397649408), (111041464215/4835703278458516698824704)), (103349/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314524341181499/151115727451828646838272), (97124792397/302231454903657293676544)), (1413/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((943334622297185/37778931862957161709568), (315518809729/75557863725914323419136)), (146955/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162087233881399/590295810358705651712), (59129876199/1180591620717411303424)), (110219/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620291779722641/590295810358705651712), (325020091259/590295810358705651712)), (37889/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1822030458961849/73786976294838206464), (202991996527/36893488147419103232)), (189453/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910516965088915/4611686018427387904), (114083014791/2305843009213693952)), (26643/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796142286589655/576460752303423488), (113958169979/288230376151711744)), (213157/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193094536793707/144115188075855872), (49786566351/18014398509481984)), (186527/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489412855417305/36028797018963968), (596318509169/36028797018963968)), (279819/36028797018963968), by norm_num⟩
  | 3 => ⟨((743242683873099/4503599627370496), (371720884791/4503599627370496)), (174913/4503599627370496), by norm_num⟩
  | 2 => ⟨((277803561504327/562949953421312), (1481030944125/4503599627370496)), (349905/2251799813685248), by norm_num⟩
  | 1 => ⟨((68996459084111/70368744177664), (1103486267885/1125899906842624)), (1050121/2251799813685248), by norm_num⟩
  | 0 => ⟨((2164546752271681/2251799813685248), (4355993897083/2251799813685248)), (1050961/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2164546752271681/2251799813685248), (4355993897083/2251799813685248)), (4009098057273482921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2080666158515787/2251799813685248), (8374414444431/2251799813685248)), (2024543/1125899906842624), by norm_num⟩
  | 2 => ⟨((1922507278873355/2251799813685248), (3868985294789/562949953421312)), (939105/281474976710656), by norm_num⟩
  | 3 => ⟨((102578910159569/140737488355328), (26425625744813/2251799813685248)), (808229/140737488355328), by norm_num⟩
  | 4 => ⟨((597975998837791/1125899906842624), (38521532832015/2251799813685248)), (9577221/1125899906842624), by norm_num⟩
  | 5 => ⟨((634522333454729/2251799813685248), (40918294658331/2251799813685248)), (10500779/1125899906842624), by norm_num⟩
  | 6 => ⟨((178055030637431/2251799813685248), (184482273422705/18014398509481984)), (25198165/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-84861685/33554432), (-1260650635/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-86449105/33554432), (-642116167/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1150415236786231/18014398509481984), (-743879451837555/18014398509481984)), (34299905/4503599627370496), by norm_num⟩
  | 1 => ⟨((-807601801/4294967296), (522210039/4294967296)), (49/2147483648), by norm_num⟩
  | 2 => ⟨((1188967111/4294967296), (-768807797/4294967296)), (73/2147483648), by norm_num⟩
  | 3 => ⟨((-1166947035/4294967296), (754569215/4294967296)), (73/2147483648), by norm_num⟩
  | 4 => ⟨((214750271/1073741824), (-69430719/536870912)), (109/4294967296), by norm_num⟩
  | 5 => ⟨((-505855255/4294967296), (654190449/8589934592)), (65/4294967296), by norm_num⟩
  | 6 => ⟨((992973287/17179869184), (-642074619/17179869184)), (129/17179869184), by norm_num⟩
  | 7 => ⟨((-835356929/34359738368), (270078505/17179869184)), (55/17179869184), by norm_num⟩
  | 8 => ⟨((76864297/8589934592), (-397614839/68719476736)), (165/137438953472), by norm_num⟩
  | 9 => ⟨((-402350635/137438953472), (260167251/137438953472)), (55/137438953472), by norm_num⟩
  | 10 => ⟨((473878757/549755813888), (-153209319/274877906944)), (131/1099511627776), by norm_num⟩
  | 11 => ⟨((-253692197/1099511627776), (656167987/4398046511104)), (71/2199023255552), by norm_num⟩
  | 12 => ⟨((995974925/17592186044416), (-644015533/17592186044416)), (71/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395154934790955/2535301200456458802993406410752), (-373845763207/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444498869866915/158456325028528675187087900672), (-442060651857/316912650057057350374175801344)), (92287/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888872101736379/39614081257132168796771975168), (-124301910249/4951760157141521099596496896)), (103829/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472148268579973/618970019642690137449562112), (-264072174489/618970019642690137449562112)), (110325/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885129807268957/77371252455336267181195264), (-527988309035/77371252455336267181195264)), (110333/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548680853335687/9671406556917033397649408), (-30926456967/302231454903657293676544)), (25861/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258025491710777/604462909807314587353088), (-865609483071/604462909807314587353088)), (45261/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943276218250509/37778931862957161709568), (-702997253435/37778931862957161709568)), (18389/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162076281547935/590295810358705651712), (-1053952896637/4722366482869645213696)), (110347/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405042820914769/147573952589676412928), (-362075864845/147573952589676412928)), (37937/147573952589676412928), by norm_num⟩
  | 8 => ⟨((910939904210829/36893488147419103232), (-14133263039/576460752303423488)), (47429/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820864406651505/9223372036854775808), (-1016687116709/4611686018427387904)), (106737/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796057498944489/576460752303423488), (-2031107123357/1152921504606846976)), (26691/144115188075855872), by norm_num⟩
  | 5 => ⟨((1192946100621599/144115188075855872), (-1774671592291/144115188075855872)), (93449/72057594037927936), by norm_num⟩
  | 4 => ⟨((1489190086673699/36028797018963968), (-83028796585/1125899906842624)), (70117/9007199254740992), by norm_num⟩
  | 3 => ⟨((1486206708935741/9007199254740992), (-3312270372889/9007199254740992)), (21925/562949953421312), by norm_num⟩
  | 2 => ⟨((2221870590605353/4503599627370496), (-3298985716863/2251799813685248)), (351123/2251799813685248), by norm_num⟩
  | 1 => ⟨((2207048413268975/2251799813685248), (-9830796198963/2251799813685248)), (263749/562949953421312), by norm_num⟩
  | 0 => ⟨((2162864700342187/2251799813685248), (-9699258370289/1125899906842624)), (1058281/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2162864700342187/2251799813685248), (-9699258370289/1125899906842624)), (4037021641257857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2077274978489003/2251799813685248), (-37264739824743/2251799813685248)), (1025601/562949953421312), by norm_num⟩
  | 2 => ⟨((1915659930872185/2251799813685248), (-68753102427125/2251799813685248)), (7704679/2251799813685248), by norm_num⟩
  | 3 => ⟨((1627598492273505/2251799813685248), (-116979815561175/2251799813685248)), (13579597/2251799813685248), by norm_num⟩
  | 4 => ⟨((585174703094329/1125899906842624), (-42276442665257/562949953421312)), (21041543/2251799813685248), by norm_num⟩
  | 5 => ⟨((1191154704556471/4503599627370496), (-87890955969265/1125899906842624)), (12516301/1125899906842624), by norm_num⟩
  | 6 => ⟨((1150415236786231/18014398509481984), (-743879451837555/18014398509481984)), (34299905/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-86449105/33554432), (-642116167/16777216)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-87955083/33554432), (-1306604171/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((212265411257589/9007199254740992), (-1239135402905069/18014398509481984)), (188953593/18014398509481984), by norm_num⟩
  | 1 => ⟨((-18951009/268435456), (110629735/536870912)), (137/4294967296), by norm_num⟩
  | 2 => ⟨((227088597/2147483648), (-662834135/2147483648)), (207/4294967296), by norm_num⟩
  | 3 => ⟨((-453531093/4294967296), (1323782407/4294967296)), (209/4294967296), by norm_num⟩
  | 4 => ⟨((339664433/4294967296), (-247856105/1073741824)), (79/2147483648), by norm_num⟩
  | 5 => ⟨((-203508741/4294967296), (1188016853/8589934592)), (191/8589934592), by norm_num⟩
  | 6 => ⟨((406438469/17179869184), (-1186326809/17179869184)), (193/17179869184), by norm_num⟩
  | 7 => ⟨((-21742515/2147483648), (1015405003/34359738368)), (167/34359738368), by norm_num⟩
  | 8 => ⟨((521078031/137438953472), (-1520940769/137438953472)), (63/34359738368), by norm_num⟩
  | 9 => ⟨((-86722793/68719476736), (1012518077/274877906944)), (85/137438953472), by norm_num⟩
  | 10 => ⟨((25979827/68719476736), (-75830827/68719476736)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((-226410491/2199023255552), (660854853/2199023255552)), (227/4398046511104), by norm_num⟩
  | 12 => ⟨((226088405/8796093022208), (-659914737/8796093022208)), (229/17592186044416), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (-101011581721/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((888962405927647/316912650057057350374175801344), (-955472866999/316912650057057350374175801344)), (92389/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944396266884291/19807040628566084398385987584), (-2149326204397/39614081257132168796771975168)), (51975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236063555304313/309485009821345068724781056), (-1141524286629/1237940039285380274899124224)), (27615/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885087440251617/77371252455336267181195264), (-2282362048235/154742504910672534362390528)), (27619/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548601306742785/9671406556917033397649408), (-1069492628997/4835703278458516698824704)), (25897/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157244472514655/75557863725914323419136), (-467720810755/151115727451828646838272)), (90657/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471609738071885/18889465931478580854784), (-759704827111/18889465931478580854784)), (36837/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1296524961943353/4722366482869645213696), (-569479977875/1180591620717411303424)), (110539/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202506715207939/73786976294838206464), (-1565099956863/295147905179352825856)), (152035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227716553154387/9223372036854775808), (-3909842063829/73786976294838206464)), (190111/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820698009612083/9223372036854775808), (-4394577497903/9223372036854775808)), (13373/576460752303423488), by norm_num⟩
  | 6 => ⟨((795973932012059/576460752303423488), (-2194794561775/576460752303423488)), (53521/288230376151711744), by norm_num⟩
  | 5 => ⟨((596399516062313/72057594037927936), (-3835285643429/144115188075855872)), (93727/72057594037927936), by norm_num⟩
  | 4 => ⟨((372241959398023/9007199254740992), (-717717058419/4503599627370496)), (140721/18014398509481984), by norm_num⟩
  | 3 => ⟨((742963015421823/4503599627370496), (-1789406077707/2251799813685248)), (352261/9007199254740992), by norm_num⟩
  | 2 => ⟨((2221300691399151/4503599627370496), (-14256768389357/4503599627370496)), (176475/1125899906842624), by norm_num⟩
  | 1 => ⟨((137885775389119/140737488355328), (-2654938212237/281474976710656)), (132789/281474976710656), by norm_num⟩
  | 0 => ⟨((2161029242292245/2251799813685248), (-41899735140325/2251799813685248)), (133659/140737488355328), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2161029242292245/2251799813685248), (-41899735140325/2251799813685248)), (509868622363042787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2073138016028759/2251799813685248), (-40210747124255/1125899906842624)), (4184263/2251799813685248), by norm_num⟩
  | 2 => ⟨((952889681996915/1125899906842624), (-37020355010947/562949953421312)), (4001715/1125899906842624), by norm_num⟩
  | 3 => ⟨((1603191747029405/2251799813685248), (-250653288800565/2251799813685248)), (14599817/2251799813685248), by norm_num⟩
  | 4 => ⟨((1113507822195395/2251799813685248), (-89227577320293/562949953421312)), (24039259/2251799813685248), by norm_num⟩
  | 5 => ⟨((988111549221981/4503599627370496), (-88245504505205/562949953421312)), (62790241/4503599627370496), by norm_num⟩
  | 6 => ⟨((212265411257589/9007199254740992), (-1239135402905069/18014398509481984)), (188953593/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-1306604171/33554432)), (1/16777216), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-5586723/2097152), (-663942127/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-375851662173243/18014398509481984), (-1197500873609373/18014398509481984)), (54853379/4503599627370496), by norm_num⟩
  | 1 => ⟨((136409857/2147483648), (434615407/2147483648)), (161/4294967296), by norm_num⟩
  | 2 => ⟨((-207651435/2147483648), (-1323196359/4294967296)), (247/4294967296), by norm_num⟩
  | 3 => ⟨((210733151/2147483648), (335708417/1073741824)), (253/4294967296), by norm_num⟩
  | 4 => ⟨((-320790903/4294967296), (-998117/4194304)), (97/2147483648), by norm_num⟩
  | 5 => ⟨((390662041/8589934592), (1244688221/8589934592)), (119/4294967296), by norm_num⟩
  | 6 => ⟨((-396459783/17179869184), (-631580203/8589934592)), (243/17179869184), by norm_num⟩
  | 7 => ⟨((86216479/8589934592), (68673575/2147483648)), (213/34359738368), by norm_num⟩
  | 8 => ⟨((-262488005/68719476736), (-6533695/536870912)), (163/68719476736), by norm_num⟩
  | 9 => ⟨((177589027/137438953472), (1131632699/274877906944)), (111/137438953472), by norm_num⟩
  | 10 => ⟨((-216269511/549755813888), (-689056229/549755813888)), (17/68719476736), by norm_num⟩
  | 11 => ⟨((119715887/1099511627776), (762853509/2199023255552)), (19/274877906944), by norm_num⟩
  | 12 => ⟨((-15186571/549755813888), (-774174875/8796093022208)), (311/17592186044416), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790252832762771/5070602400912917605986812821504), (-2442296267815/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777856548114447/633825300114114700748351602688), (-180469965613/39614081257132168796771975168)), (92485/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888715616653399/39614081257132168796771975168), (-3247706570479/39614081257132168796771975168)), (813/309485009821345068724781056), by norm_num⟩
  | 15 => ⟨((236053319375635/309485009821345068724781056), (-1724875097171/1237940039285380274899124224)), (110589/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770092809934845/154742504910672534362390528), (-3448695307797/154742504910672534362390528)), (110613/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193565521396427/1208925819614629174706176), (-50500490877/151115727451828646838272)), (103725/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((628944046136019/302231454903657293676544), (-176681717741/37778931862957161709568)), (90785/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886328595786463/75557863725914323419136), (-286976597761/4722366482869645213696)), (36893/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162055234586751/590295810358705651712), (-1720941687801/2361183241434822606848)), (110721/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((809969481834599/295147905179352825856), (-1182402045135/147573952589676412928)), (152309/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821588205420119/73786976294838206464), (-2953770512747/36893488147419103232)), (23811/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1820534702556379/9223372036854775808), (-3319921680705/4611686018427387904)), (107219/4611686018427387904), by norm_num⟩
  | 6 => ⟨((795891617763673/576460752303423488), (-6632175278309/1152921504606846976)), (214613/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192653500048669/144115188075855872), (-5794536780425/144115188075855872)), (11749/9007199254740992), by norm_num⟩
  | 4 => ⟨((93046661648263/2251799813685248), (-2168649246221/9007199254740992)), (141185/18014398509481984), by norm_num⟩
  | 3 => ⟨((371411080991779/2251799813685248), (-5406594035575/4503599627370496)), (353653/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220721949108343/4503599627370496), (-21536426006151/4503599627370496)), (88673/562949953421312), by norm_num⟩
  | 1 => ⟨((2205266320079663/2251799813685248), (-16040273723463/1125899906842624)), (1069289/2251799813685248), by norm_num⟩
  | 0 => ⟨((134941703724365/140737488355328), (-15817354979529/562949953421312)), (2159527/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((134941703724365/140737488355328), (-15817354979529/562949953421312)), (8237941750533293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((258546984484909/281474976710656), (-7582986076751/140737488355328)), (4262543/2251799813685248), by norm_num⟩
  | 2 => ⟨((236669480368615/281474976710656), (-55722415013833/562949953421312)), (8289997/2251799813685248), by norm_num⟩
  | 3 => ⟨((1569907114293493/2251799813685248), (-187409838847091/1125899906842624)), (7790955/1125899906842624), by norm_num⟩
  | 4 => ⟨((516057986726393/1125899906842624), (-65329084207787/281474976710656)), (26914079/2251799813685248), by norm_num⟩
  | 5 => ⟨((351771265928221/2251799813685248), (-958198020013855/4503599627370496)), (74330993/4503599627370496), by norm_num⟩
  | 6 => ⟨((-375851662173243/18014398509481984), (-1197500873609373/18014398509481984)), (54853379/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-5586723/2097152), (-663942127/16777216)), (1/16777216), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile034Terms2
