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
namespace Reinmann.XiRectangle.Tile033Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨33,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8319/640))
  have he : value ((5/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-64823859/33554432), (-168521775/4194304)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1029268954587729/9007199254740992), (-802095106270211/9007199254740992)), (236515545/9007199254740992), by norm_num⟩
  | 1 => ⟨((94816507/268435456), (591113573/2147483648)), (11/134217728), by norm_num⟩
  | 2 => ⟨((-586163697/1073741824), (-456789287/1073741824)), (275/2147483648), by norm_num⟩
  | 3 => ⟨((603952291/1073741824), (470651693/1073741824)), (143/1073741824), by norm_num⟩
  | 4 => ⟨((-466710543/1073741824), (-363701091/1073741824)), (223/2147483648), by norm_num⟩
  | 5 => ⟨((1154097681/4294967296), (449686205/2147483648)), (139/2147483648), by norm_num⟩
  | 6 => ⟨((-594560821/4294967296), (-231666525/2147483648)), (289/8589934592), by norm_num⟩
  | 7 => ⟨((262544677/4294967296), (818389787/17179869184)), (257/17179869184), by norm_num⟩
  | 8 => ⟨((-811536743/34359738368), (-316209697/17179869184)), (201/34359738368), by norm_num⟩
  | 9 => ⟨((139360807/17179869184), (434407821/68719476736)), (279/137438953472), by norm_num⟩
  | 10 => ⟨((-689232273/274877906944), (-537109207/274877906944)), (87/137438953472), by norm_num⟩
  | 11 => ⟨((774707715/1099511627776), (4716555/8589934592)), (197/1099511627776), by norm_num⟩
  | 12 => ⟨((-798218145/4398046511104), (-311020197/2199023255552)), (205/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581459249645961/10141204801825835211973625643008), (-3229969265803/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778981299876611/633825300114114700748351602688), (-3823401037101/633825300114114700748351602688)), (92577/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889980509445141/39614081257132168796771975168), (-537572500059/4951760157141521099596496896)), (104173/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889769940341373/2475880078570760549798248448), (-4568463711969/2475880078570760549798248448)), (13839/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771435561794503/154742504910672534362390528), (-4567448424591/154742504910672534362390528)), (110743/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774891164096471/4835703278458516698824704), (-2140452150545/4835703278458516698824704)), (103855/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39343384595887/18889465931478580854784), (-3744712830335/604462909807314587353088)), (90907/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944057592120119/37778931862957161709568), (-760392079445/9444732965739290427392)), (73893/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297780715547847/4722366482869645213696), (-4560583825731/4722366482869645213696)), (55447/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202722259568305/73786976294838206464), (-6267929356645/590295810358705651712)), (152569/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823884412435571/73786976294838206464), (-1957650683921/18446744073709551616)), (190845/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823114247663247/9223372036854775808), (-2200876280147/2305843009213693952)), (214885/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594358175141289/1152921504606846976), (-1099513027739/144115188075855872)), (53779/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194901396859859/144115188075855872), (-7688269034749/144115188075855872)), (94243/72057594037927936), by norm_num⟩
  | 4 => ⟨((746054047729053/18014398509481984), (-11515768876683/36028797018963968)), (283249/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489828154879827/9007199254740992), (-7182811075541/4503599627370496)), (88743/2251799813685248), by norm_num⟩
  | 2 => ⟨((557258893933313/1125899906842624), (-7161016153503/1125899906842624)), (89085/562949953421312), by norm_num⟩
  | 1 => ⟨((138600133185023/140737488355328), (-2671778349709/140737488355328)), (537939/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091601559285081/1125899906842624), (-21157044070019/562949953421312)), (1089639/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1091601559285081/1125899906842624), (-21157044070019/562949953421312)), (4156642918113326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((264189444138751/281474976710656), (-82050143734221/1125899906842624)), (1097397/562949953421312), by norm_num⟩
  | 2 => ⟨((123235285556541/140737488355328), (-77011399442911/562949953421312)), (2219957/562949953421312), by norm_num⟩
  | 3 => ⟨((105275883146607/140737488355328), (-33717106622987/140737488355328)), (4495143/562949953421312), by norm_num⟩
  | 4 => ⟨((1130748420709117/2251799813685248), (-25221411994517/70368744177664)), (34683/2199023255552), by norm_num⟩
  | 5 => ⟨((278535193570601/2251799813685248), (-810560771380269/2251799813685248)), (122254067/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1029268954587729/9007199254740992), (-802095106270211/9007199254740992)), (236515545/9007199254740992), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64823859/33554432), (-168521775/4194304)), (1/16777216), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-4109755/2097152), (-683781033/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-632323506420987/4503599627370496), (-106708788955711/9007199254740992)), (26183467/1125899906842624), by norm_num⟩
  | 1 => ⟨((1890799233/4294967296), (159542461/4294967296)), (315/4294967296), by norm_num⟩
  | 2 => ⟨((-741073757/1073741824), (-31265279/536870912)), (249/2147483648), by norm_num⟩
  | 3 => ⟨((1549088319/2147483648), (130709469/2147483648)), (131/1073741824), by norm_num⟩
  | 4 => ⟨((-607144683/1073741824), (-6403731/134217728)), (207/2147483648), by norm_num⟩
  | 5 => ⟨((1522958913/4294967296), (64252357/2147483648)), (131/2147483648), by norm_num⟩
  | 6 => ⟨((-795871477/4294967296), (-33577149/2147483648)), (69/2147483648), by norm_num⟩
  | 7 => ⟨((89123229/1073741824), (120321093/17179869184)), (249/17179869184), by norm_num⟩
  | 8 => ⟨((-279445369/8589934592), (-94316523/34359738368)), (197/34359738368), by norm_num⟩
  | 9 => ⟨((48677741/4294967296), (2053673/2147483648)), (69/34359738368), by norm_num⟩
  | 10 => ⟨((-488412081/137438953472), (-164845563/549755813888)), (87/137438953472), by norm_num⟩
  | 11 => ⟨((556877547/549755813888), (93976783/1099511627776)), (25/137438953472), by norm_num⟩
  | 12 => ⟨((-72753597/274877906944), (-24555305/1099511627776)), (211/4398046511104), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395355765008039/2535301200456458802993406410752), (-1991311374649/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778934392458799/633825300114114700748351602688), (-294632562245/39614081257132168796771975168)), (11583/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944963758222341/19807040628566084398385987584), (-5302441654961/39614081257132168796771975168)), (104277/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889713346349755/2475880078570760549798248448), (-5632714095417/2475880078570760549798248448)), (110829/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221422330371677/19342813113834066795298816), (-2815721287859/77371252455336267181195264)), (27717/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((193716077735669/1208925819614629174706176), (-2639063252985/4835703278458516698824704)), (25995/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258940969381907/604462909807314587353088), (-2308504937267/302231454903657293676544)), (5689/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1888037614769999/75557863725914323419136), (-937513556879/9444732965739290427392)), (147991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297721973953073/4722366482869645213696), (-351429094857/295147905179352825856)), (111061/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621696390531323/590295810358705651712), (-7727839737947/590295810358705651712)), (152819/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823780932143017/73786976294838206464), (-9654399789353/73786976294838206464)), (47797/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822995947547693/9223372036854775808), (-10853775969143/9223372036854775808)), (107657/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594237523206843/1152921504606846976), (-5422248901695/576460752303423488)), (215599/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298698296585903/36028797018963968), (-9478499823203/144115188075855872)), (94485/72057594037927936), by norm_num⟩
  | 4 => ⟨((745970256916969/18014398509481984), (-1774610465143/4503599627370496)), (4439/562949953421312), by norm_num⟩
  | 3 => ⟨((1489609494756261/9007199254740992), (-17709601607349/9007199254740992)), (89061/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114285417326845/2251799813685248), (-4413718071359/562949953421312)), (357933/2251799813685248), by norm_num⟩
  | 1 => ⟨((554209229062433/562949953421312), (-13172787377227/562949953421312)), (541131/1125899906842624), by norm_num⟩
  | 0 => ⟨((545350741519045/562949953421312), (-52144762769829/1125899906842624)), (1099253/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((545350741519045/562949953421312), (-52144762769829/1125899906842624)), (4193317417625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527094212195841/562949953421312), (-101029176288353/1125899906842624)), (2231597/1125899906842624), by norm_num⟩
  | 2 => ⟨((244494722170233/281474976710656), (-189188732536053/1125899906842624)), (2289707/562949953421312), by norm_num⟩
  | 3 => ⟨((408850877680941/562949953421312), (-328666136789059/1125899906842624)), (9494529/1125899906842624), by norm_num⟩
  | 4 => ⟨((995851812124575/2251799813685248), (-119349364604747/281474976710656)), (19334265/1125899906842624), by norm_num⟩
  | 5 => ⟨((71131987848505/4503599627370496), (-844510459910125/2251799813685248)), (133988185/4503599627370496), by norm_num⟩
  | 6 => ⟨((-632323506420987/4503599627370496), (-106708788955711/9007199254740992)), (26183467/1125899906842624), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-4109755/2097152), (-683781033/16777216)), (1/16777216), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-66648619/33554432), (-1386124663/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-68897934840751/562949953421312), (279309847228359/4503599627370496)), (220932445/9007199254740992), by norm_num⟩
  | 1 => ⟨((835271247/2147483648), (-423270097/2147483648)), (169/2147483648), by norm_num⟩
  | 2 => ⟨((-1327268493/2147483648), (84073447/268435456)), (271/2147483648), by norm_num⟩
  | 3 => ⟨((351510893/536870912), (-712506507/2147483648)), (145/1073741824), by norm_num⟩
  | 4 => ⟨((-279280135/536870912), (70762001/268435456)), (233/2147483648), by norm_num⟩
  | 5 => ⟨((355026921/1073741824), (-719633435/4294967296)), (299/4294967296), by norm_num⟩
  | 6 => ⟨((-188049111/1073741824), (381172299/4294967296)), (5/134217728), by norm_num⟩
  | 7 => ⟨((170751485/2147483648), (-173055155/4294967296)), (293/17179869184), by norm_num⟩
  | 8 => ⟨((-542657411/17179869184), (274989299/17179869184)), (235/34359738368), by norm_num⟩
  | 9 => ⟨((191621607/17179869184), (-388413687/68719476736)), (21/8589934592), by norm_num⟩
  | 10 => ⟨((-974374051/274877906944), (246879921/137438953472)), (215/274877906944), by norm_num⟩
  | 11 => ⟨((563020579/549755813888), (-570616493/1099511627776)), (125/549755813888), by norm_num⟩
  | 12 => ⟨((-596436569/2199023255552), (302241655/2199023255552)), (267/4398046511104), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581388410907415/10141204801825835211973625643008), (3481311797097/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778896185318921/633825300114114700748351602688), (4120552148439/633825300114114700748351602688)), (46303/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889884701297721/39614081257132168796771975168), (4634792648511/39614081257132168796771975168)), (104207/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889668071402611/2475880078570760549798248448), (4923466849639/2475880078570760549798248448)), (110751/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771333611055777/154742504910672534362390528), (615292688981/19342813113834066795298816)), (110785/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549686662535099/9671406556917033397649408), (576687455355/1208925819614629174706176)), (12987/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((157363064107327/75557863725914323419136), (1008904206967/151115727451828646838272)), (45473/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887978856148287/75557863725914323419136), (6555636396699/75557863725914323419136)), (73927/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162209790932837/590295810358705651712), (2457383409261/2361183241434822606848)), (55475/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405409265618967/147573952589676412928), (6754619255905/590295810358705651712)), (38163/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911853899865855/36893488147419103232), (2109624386201/18446744073709551616)), (11935/4611686018427387904), by norm_num⟩
  | 7 => ⟨((911457542377109/4611686018427387904), (4743371947055/4611686018427387904)), (53757/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797079210792457/576460752303423488), (9478539411023/1152921504606846976)), (215277/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597362974953705/72057594037927936), (8284495828041/144115188075855872)), (23581/18014398509481984), by norm_num⟩
  | 4 => ⟨((1491843604561913/36028797018963968), (387759411477/1125899906842624)), (70883/9007199254740992), by norm_num⟩
  | 3 => ⟨((744747620516235/4503599627370496), (7739061961411/4503599627370496)), (355397/9007199254740992), by norm_num⟩
  | 2 => ⟨((34818170150737/70368744177664), (1928723650343/281474976710656)), (44609/281474976710656), by norm_num⟩
  | 1 => ⟨((554144025883369/562949953421312), (23024001948881/1125899906842624)), (269503/562949953421312), by norm_num⟩
  | 0 => ⟨((272635494241437/281474976710656), (45566211317673/1125899906842624)), (546427/562949953421312), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((272635494241437/281474976710656), (45566211317673/1125899906842624)), (2084453584911155523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1054450326086101/1125899906842624), (88270486339351/1125899906842624)), (1102763/562949953421312), by norm_num⟩
  | 2 => ⟨((490307266531653/562949953421312), (20667210854765/140737488355328)), (2238477/562949953421312), by norm_num⟩
  | 3 => ⟨((829796952720217/1125899906842624), (576010487579489/2251799813685248)), (4556689/562949953421312), by norm_num⟩
  | 4 => ⟨((268947514167447/562949953421312), (212262095601699/562949953421312)), (9047833/562949953421312), by norm_num⟩
  | 5 => ⟨((387637557929911/4503599627370496), (811260221156117/2251799813685248)), (61872701/2251799813685248), by norm_num⟩
  | 6 => ⟨((-68897934840751/562949953421312), (279309847228359/4503599627370496)), (220932445/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-66648619/33554432), (-1386124663/33554432)), (1/16777216), by norm_num⟩, -7, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-67504719/33554432), (-350982347/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-651252719856313/9007199254740992), (506744749395605/4503599627370496)), (108232407/4503599627370496), by norm_num⟩
  | 1 => ⟨((499797257/2147483648), (-777792179/2147483648)), (21/268435456), by norm_num⟩
  | 2 => ⟨((-402196327/1073741824), (1251808221/2147483648)), (17/134217728), by norm_num⟩
  | 3 => ⟨((431540011/1073741824), (-671569203/1073741824)), (37/268435456), by norm_num⟩
  | 4 => ⟨((-694536855/2147483648), (135106117/268435456)), (15/134217728), by norm_num⟩
  | 5 => ⟨((223562789/1073741824), (-347911851/1073741824)), (39/536870912), by norm_num⟩
  | 6 => ⟨((-239873619/2147483648), (746590031/4294967296)), (169/4294967296), by norm_num⟩
  | 7 => ⟨((55151671/1073741824), (-686623029/8589934592)), (157/8589934592), by norm_num⟩
  | 8 => ⟨((-355052761/17179869184), (1105077135/34359738368)), (255/34359738368), by norm_num⟩
  | 9 => ⟨((507942555/68719476736), (-790468017/68719476736)), (23/8589934592), by norm_num⟩
  | 10 => ⟨((-163500401/68719476736), (254441839/68719476736)), (239/274877906944), by norm_num⟩
  | 11 => ⟨((382754537/549755813888), (-297824249/274877906944)), (141/549755813888), by norm_num⟩
  | 12 => ⟨((-821359551/4398046511104), (1278212367/4398046511104)), (305/4398046511104), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49417349261741/316912650057057350374175801344), (2790117196623/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778860098837441/633825300114114700748351602688), (1651150493193/316912650057057350374175801344)), (46263/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889844296371625/39614081257132168796771975168), (3714423511007/39614081257132168796771975168)), (6507/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((944812694835249/1237940039285380274899124224), (986440957609/618970019642690137449562112)), (110643/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110705700544291/9671406556917033397649408), (3944851432903/154742504910672534362390528)), (55335/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549647207007011/9671406556917033397649408), (3697328982883/9671406556917033397649408)), (51891/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314717571437015/151115727451828646838272), (1617096917325/302231454903657293676544)), (90839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471980948142779/18889465931478580854784), (5253748505217/75557863725914323419136)), (73833/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297637515406761/4722366482869645213696), (3938722408859/4722366482869645213696)), (110797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810790867131651/295147905179352825856), (2706581036583/295147905179352825856)), (152423/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823639820649089/73786976294838206464), (6762582198421/73786976294838206464)), (190645/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911420115099265/4611686018427387904), (7602585564539/9223372036854775808)), (107317/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594085591099749/1152921504606846976), (7595939876861/1152921504606846976)), (107417/576460752303423488), by norm_num⟩
  | 5 => ⟨((37333265492207/4503599627370496), (1659743976911/36028797018963968)), (47051/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491755956967559/36028797018963968), (9943533180035/36028797018963968)), (282755/36028797018963968), by norm_num⟩
  | 3 => ⟨((744696794899435/4503599627370496), (1550414429681/1125899906842624)), (354231/9007199254740992), by norm_num⟩
  | 2 => ⟨((557045802409753/1125899906842624), (6182109604561/1125899906842624)), (355413/2251799813685248), by norm_num⟩
  | 1 => ⟨((554091320534055/562949953421312), (9224390986019/562949953421312)), (268041/562949953421312), by norm_num⟩
  | 0 => ⟨((1090447482542699/1125899906842624), (36508539588021/1125899906842624)), (1084051/1125899906842624), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1090447482542699/1125899906842624), (36508539588021/1125899906842624)), (4135326389793014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((527463778752617/562949953421312), (141435823355593/2251799813685248)), (271267/140737488355328), by norm_num⟩
  | 2 => ⟨((245996807047153/281474976710656), (265040518734341/2251799813685248)), (8678583/2251799813685248), by norm_num⟩
  | 3 => ⟨((844363908654669/1125899906842624), (28954226281805/140737488355328)), (17212371/2251799813685248), by norm_num⟩
  | 4 => ⟨((585572646537003/1125899906842624), (173712803611015/562949953421312)), (4112371/281474976710656), by norm_num⟩
  | 5 => ⟨((789380194343727/4503599627370496), (361387244211161/1125899906842624)), (54524705/2251799813685248), by norm_num⟩
  | 6 => ⟨((-651252719856313/9007199254740992), (506744749395605/4503599627370496)), (108232407/4503599627370496), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67504719/33554432), (-350982347/8388608)), (1/16777216), by norm_num⟩, -7, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-68327237/33554432), (-710517853/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-36028708798835/4503599627370496), (586656611076755/4503599627370496)), (192314329/9007199254740992), by norm_num⟩
  | 1 => ⟨((111947071/4294967296), (-1822837709/4294967296)), (301/4294967296), by norm_num⟩
  | 2 => ⟨((-91183591/2147483648), (1484745307/2147483648)), (247/2147483648), by norm_num⟩
  | 3 => ⟨((49514157/1073741824), (-806240591/1073741824)), (135/1073741824), by norm_num⟩
  | 4 => ⟨((-10082619/268435456), (1313404839/2147483648)), (111/1073741824), by norm_num⟩
  | 5 => ⟨((105120467/4294967296), (-53489997/134217728)), (291/4294967296), by norm_num⟩
  | 6 => ⟨((-57082105/4294967296), (1858939457/8589934592)), (159/4294967296), by norm_num⟩
  | 7 => ⟨((106273719/17179869184), (-865229173/8589934592)), (149/8589934592), by norm_num⟩
  | 8 => ⟨((-86562509/34359738368), (1409500087/34359738368)), (61/8589934592), by norm_num⟩
  | 9 => ⟨((31336557/34359738368), (-1020508301/68719476736)), (89/34359738368), by norm_num⟩
  | 10 => ⟨((-40839011/137438953472), (1329965825/274877906944)), (117/137438953472), by norm_num⟩
  | 11 => ⟨((12096131/137438953472), (-1575693473/1099511627776)), (279/1099511627776), by norm_num⟩
  | 12 => ⟨((-26273575/1099511627776), (1711253817/4398046511104)), (305/4398046511104), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245525873/10141204801825835211973625643008), (531508837795/2535301200456458802993406410752)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222353094341989/79228162514264337593543950336), (2516211378395/633825300114114700748351602688)), (2889/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889804680562187/39614081257132168796771975168), (2830229146545/39614081257132168796771975168)), (26005/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889583487115141/2475880078570760549798248448), (46976458715/38685626227668133590597632)), (110539/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771249518900611/154742504910672534362390528), (1502895142873/77371252455336267181195264)), (3455/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774804174360931/4835703278458516698824704), (2817181562225/9671406556917033397649408)), (12959/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((78677281906725/37778931862957161709568), (308035905311/75557863725914323419136)), (90735/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943934665391581/37778931862957161709568), (1000766821571/18889465931478580854784)), (73743/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297597038851099/4722366482869645213696), (3001076355305/4722366482869645213696)), (110651/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810763339650105/295147905179352825856), (4124491631817/590295810358705651712)), (152203/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56986621917093/2305843009213693952), (2576316720569/36893488147419103232)), (95171/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822765055956571/9223372036854775808), (5792615944153/9223372036854775808)), (13391/576460752303423488), by norm_num⟩
  | 6 => ⟨((398502989504829/288230376151711744), (5787498596671/1152921504606846976)), (214409/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194601797102791/144115188075855872), (2529154532529/72057594037927936)), (93889/72057594037927936), by norm_num⟩
  | 4 => ⟨((745832680414145/18014398509481984), (7575971199343/36028797018963968)), (141005/18014398509481984), by norm_num⟩
  | 3 => ⟨((744643182822041/4503599627370496), (2362469830049/2251799813685248)), (353111/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227986745778857/4503599627370496), (18839612586969/4503599627370496)), (88503/562949953421312), by norm_num⟩
  | 1 => ⟨((277014409122153/281474976710656), (28109431291741/2251799813685248)), (1066553/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180572051435539/2251799813685248), (27810587157049/1125899906842624)), (33613/35184372088832), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2180572051435539/2251799813685248), (27810587157049/1125899906842624)), (128223419323670853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((1055111721652783/1125899906842624), (107723588429339/2251799813685248)), (2136323/1125899906842624), by norm_num⟩
  | 2 => ⟨((986197481272445/1125899906842624), (100950732973267/1125899906842624)), (4208413/1125899906842624), by norm_num⟩
  | 3 => ⟨((1709555912974769/2251799813685248), (353698789690935/2251799813685248)), (16254265/2251799813685248), by norm_num⟩
  | 4 => ⟨((621165027360907/1125899906842624), (537052941965183/2251799813685248)), (29786565/2251799813685248), by norm_num⟩
  | 5 => ⟨((557313352086041/2251799813685248), (148147496665833/562949953421312)), (23537487/1125899906842624), by norm_num⟩
  | 6 => ⟨((-36028708798835/4503599627370496), (586656611076755/4503599627370496)), (192314329/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-68327237/33554432), (-710517853/16777216)), (1/16777216), by norm_num⟩, -7, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-69118709/33554432), (-1437496345/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((477812759197543/9007199254740992), (1043970930247301/9007199254740992)), (19654911/1125899906842624), by norm_num⟩
  | 1 => ⟨((-375459887/2147483648), (-820340605/2147483648)), (125/2147483648), by norm_num⟩
  | 2 => ⟨((618727269/2147483648), (337963601/536870912)), (13/134217728), by norm_num⟩
  | 3 => ⟨((-339870691/1073741824), (-371290965/536870912)), (29/268435456), by norm_num⟩
  | 4 => ⟨((560079177/2147483648), (611857225/1073741824)), (97/1073741824), by norm_num⟩
  | 5 => ⟨((-2884265/16777216), (-12603635/33554432)), (65/1073741824), by norm_num⟩
  | 6 => ⟨((405592189/4294967296), (886176531/4294967296)), (145/4294967296), by norm_num⟩
  | 7 => ⟨((-190966527/4294967296), (-417241897/4294967296)), (69/4294967296), by norm_num⟩
  | 8 => ⟨((78674315/4294967296), (687580613/17179869184)), (229/34359738368), by norm_num⟩
  | 9 => ⟨((-460973703/68719476736), (-251794837/17179869184)), (85/34359738368), by norm_num⟩
  | 10 => ⟨((303858825/137438953472), (663899765/137438953472)), (113/137438953472), by norm_num⟩
  | 11 => ⟨((-91042647/137438953472), (-397837331/274877906944)), (137/549755813888), by norm_num⟩
  | 12 => ⟨((400082283/2199023255552), (874137961/2199023255552)), (19/274877906944), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581292519908217/10141204801825835211973625643008), (1487019314867/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778790121871265/633825300114114700748351602688), (1759852803231/633825300114114700748351602688)), (46187/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236220727984007/4951760157141521099596496896), (989738346577/19807040628566084398385987584)), (103931/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944771169090557/1237940039285380274899124224), (2102751954883/2475880078570760549798248448)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771208523188073/154742504910672534362390528), (2102254827437/154742504910672534362390528)), (55227/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387392519485475/2417851639229258349412352), (1970335852315/9671406556917033397649408)), (51783/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((19668799783847/9444732965739290427392), (1723515990559/604462909807314587353088)), (90637/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943907741677083/37778931862957161709568), (2799724066543/75557863725914323419136)), (9207/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1297556919594533/4722366482869645213696), (2098927666215/4722366482869645213696)), (55255/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621471947649205/590295810358705651712), (721154990485/147573952589676412928)), (18999/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823504134512005/73786976294838206464), (3603667754655/73786976294838206464)), (47513/18446744073709551616), by norm_num⟩
  | 7 => ⟨((56959053364317/288230376151711744), (2025615364353/4611686018427387904)), (213893/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796968859803579/576460752303423488), (2023807105131/576460752303423488)), (213999/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298634521142557/36028797018963968), (1768798883717/72057594037927936)), (187369/144115188075855872), by norm_num⟩
  | 4 => ⟨((745786138917377/18014398509481984), (2649138550479/18014398509481984)), (281293/36028797018963968), by norm_num⟩
  | 3 => ⟨((744587173898537/4503599627370496), (1652164787637/2251799813685248)), (88009/2251799813685248), by norm_num⟩
  | 2 => ⟨((2227775660836991/4503599627370496), (13174844451299/4503599627370496)), (352667/2251799813685248), by norm_num⟩
  | 1 => ⟨((138489426483881/140737488355328), (19656388900931/2251799813685248)), (530583/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090065338971245/1125899906842624), (2430693963865/140737488355328)), (2135043/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((1090065338971245/1125899906842624), (2430693963865/140737488355328)), (8144542702681731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((131879431125043/140737488355328), (75306594443869/2251799813685248)), (2103965/1125899906842624), by norm_num⟩
  | 2 => ⟨((987371986709883/1125899906842624), (141133552279225/2251799813685248)), (8167615/2251799813685248), by norm_num⟩
  | 3 => ⟨((430732680742755/562949953421312), (123768831543957/1125899906842624)), (7674605/1125899906842624), by norm_num⟩
  | 4 => ⟨((1291062981638909/2251799813685248), (47349928958453/281474976710656)), (26863075/2251799813685248), by norm_num⟩
  | 5 => ⟨((676505346464855/2251799813685248), (434367141092841/2251799813685248)), (9960397/562949953421312), by norm_num⟩
  | 6 => ⟨((477812759197543/9007199254740992), (1043970930247301/9007199254740992)), (19654911/1125899906842624), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-69118709/33554432), (-1437496345/33554432)), (1/16777216), by norm_num⟩, -7, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨33,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile033Terms3
