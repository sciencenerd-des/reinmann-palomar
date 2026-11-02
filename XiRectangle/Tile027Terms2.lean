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
namespace Reinmann.XiRectangle.Tile027Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-232581599/134217728), (-2172602865/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/134217728), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((915307834210973/9007199254740992), (-1302886327629165/9007199254740992)), (24799183/4503599627370496), by norm_num⟩
  | 1 => ⟨((-605052037/2147483648), (861255631/2147483648)), (133/8589934592), by norm_num⟩
  | 2 => ⟨((3355120909/8589934592), (-4775815299/8589934592)), (187/8589934592), by norm_num⟩
  | 3 => ⟨((-775197533/2147483648), (2206895273/4294967296)), (175/8589934592), by norm_num⟩
  | 4 => ⟨((1074651969/4294967296), (-3059406473/8589934592)), (123/8589934592), by norm_num⟩
  | 5 => ⟨((-297956793/2147483648), (1696495177/8589934592)), (69/8589934592), by norm_num⟩
  | 6 => ⟨((68842637/1073741824), (-1567894465/17179869184)), (129/34359738368), by norm_num⟩
  | 7 => ⟨((-1745118345/68719476736), (4968144585/137438953472)), (207/137438953472), by norm_num⟩
  | 8 => ⟨((2419247721/274877906944), (-860913853/68719476736)), (145/274877906944), by norm_num⟩
  | 9 => ⟨((-2981146199/1099511627776), (4243484515/1099511627776)), (181/1099511627776), by norm_num⟩
  | 10 => ⟨((826549233/1099511627776), (-1176543731/1099511627776)), (203/4398046511104), by norm_num⟩
  | 11 => ⟨((-3333354301/17592186044416), (4744831825/17592186044416)), (207/17592186044416), by norm_num⟩
  | 12 => ⟨((1540336757/35184372088832), (-548144467/8796093022208)), (193/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790859256563237/5070602400912917605986812821504), (-1248395606369/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779294900345733/633825300114114700748351602688), (-1478244578005/633825300114114700748351602688)), (23087/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890333631947621/39614081257132168796771975168), (-415692676657/9903520314283042199192993792)), (25975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890145553524751/2475880078570760549798248448), (-110398842097/154742504910672534362390528)), (27601/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771811647697729/154742504910672534362390528), (-883015056023/77371252455336267181195264)), (6901/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387533852665451/2417851639229258349412352), (-1655279997389/9671406556917033397649408)), (12941/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629648877895903/302231454903657293676544), (-1447996865121/604462909807314587353088)), (11325/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472154744514451/18889465931478580854784), (-1176147747387/37778931862957161709568)), (36813/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298159382309217/4722366482869645213696), (-440902462229/1180591620717411303424)), (27615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622300076637643/590295810358705651712), (-2423969810795/590295810358705651712)), (37979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824538909906589/73786976294838206464), (-378559045381/9223372036854775808)), (23743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911926649743639/4611686018427387904), (-3404983927015/9223372036854775808)), (835/144115188075855872), by norm_num⟩
  | 6 => ⟨((1595100648386841/1152921504606846976), (-1701213135943/576460752303423488)), (26731/576460752303423488), by norm_num⟩
  | 5 => ⟨((597777450704417/72057594037927936), (-2974247957277/144115188075855872)), (11701/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493096011625101/36028797018963968), (-2227813849359/18014398509481984)), (70257/36028797018963968), by norm_num⟩
  | 3 => ⟨((745538202733445/4503599627370496), (-5559495300215/9007199254740992)), (87909/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231571949501903/4503599627370496), (-5544462468781/2251799813685248)), (176081/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221505697287229/2251799813685248), (-1034900378027/140737488355328)), (264783/2251799813685248), by norm_num⟩
  | 0 => ⟨((547850557918305/562949953421312), (-32817981270319/2251799813685248)), (532225/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((547850557918305/562949953421312), (-32817981270319/2251799813685248)), (2030277260787200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2132146335526257/2251799813685248), (-7984435045881/281474976710656)), (525707/1125899906842624), by norm_num⟩
  | 2 => ⟨((2017038944360083/2251799813685248), (-120962681111241/2251799813685248)), (2050741/2251799813685248), by norm_num⟩
  | 3 => ⟨((1800255115133539/2251799813685248), (-108351744738925/1125899906842624)), (60847/35184372088832), by norm_num⟩
  | 4 => ⟨((1418402318803567/2251799813685248), (-346497555447721/2251799813685248)), (218005/70368744177664), by norm_num⟩
  | 5 => ⟨((840130002036017/2251799813685248), (-109128913929183/562949953421312)), (10935453/2251799813685248), by norm_num⟩
  | 6 => ⟨((915307834210973/9007199254740992), (-1302886327629165/9007199254740992)), (24799183/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/134217728), (-2172602865/67108864)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-237667161/134217728), (-1110054185/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-190133729/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-73069376832481/4503599627370496), (-1526078926837361/9007199254740992)), (63016015/9007199254740992), by norm_num⟩
  | 1 => ⟨((98715369/2147483648), (4123408489/8589934592)), (43/2147483648), by norm_num⟩
  | 2 => ⟨((-559363401/8589934592), (-5841247977/8589934592)), (123/4294967296), by norm_num⟩
  | 3 => ⟨((132066321/2147483648), (1379125143/2147483648)), (117/4294967296), by norm_num⟩
  | 4 => ⟨((-374172063/8589934592), (-7814711517/17179869184)), (333/17179869184), by norm_num⟩
  | 5 => ⟨((424043713/17179869184), (2214074495/8589934592)), (95/8589934592), by norm_num⟩
  | 6 => ⟨((-400468769/34359738368), (-4181963603/34359738368)), (181/34359738368), by norm_num⟩
  | 7 => ⟨((648350549/137438953472), (6770511477/137438953472)), (295/137438953472), by norm_num⟩
  | 8 => ⟨((-459228857/274877906944), (-2397787933/137438953472)), (211/274877906944), by norm_num⟩
  | 9 => ⟨((144565925/274877906944), (1509654393/274877906944)), (67/274877906944), by norm_num⟩
  | 10 => ⟨((-655337773/4398046511104), (-3421738377/2199023255552)), (153/2199023255552), by norm_num⟩
  | 11 => ⟨((675167899/17592186044416), (440659765/1099511627776)), (159/8796093022208), by norm_num⟩
  | 12 => ⟨((-637631567/70368744177664), (-3329288337/35184372088832)), (151/35184372088832), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790834578331793/5070602400912917605986812821504), (-2170497704233/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889617047476069/316912650057057350374175801344), (-2569959330597/633825300114114700748351602688)), (11557/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236283137584395/4951760157141521099596496896), (-2890748802999/39614081257132168796771975168)), (26007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945036288814225/1237940039285380274899124224), (-1535432588105/1237940039285380274899124224)), (27637/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771738490330025/154742504910672534362390528), (-3070240432845/154742504910672534362390528)), (27643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775033316463155/4835703278458516698824704), (-719421685805/2417851639229258349412352)), (25921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629618691346917/302231454903657293676544), (-1258656190421/302231454903657293676544)), (11343/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888520510950277/75557863725914323419136), (-4089388823911/75557863725914323419136)), (36875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298085216521109/4722366482869645213696), (-3065953601385/4722366482869645213696)), (13833/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811098793276681/295147905179352825856), (-4213918745041/590295810358705651712)), (38055/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824410029974527/73786976294838206464), (-1316187060867/18446744073709551616)), (47591/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113981703493047/576460752303423488), (-5919199386337/9223372036854775808)), (53571/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594953289791687/1152921504606846976), (-1478662208161/288230376151711744)), (53609/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195424486147343/144115188075855872), (-5170201697477/144115188075855872)), (46953/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492897442943623/36028797018963968), (-7745078837133/36028797018963968)), (70515/36028797018963968), by norm_num⟩
  | 3 => ⟨((372705763910433/2251799813685248), (-9663475845967/9007199254740992)), (88297/9007199254740992), by norm_num⟩
  | 2 => ⟨((8715038661875/17592186044416), (-4818352183043/1125899906842624)), (44263/1125899906842624), by norm_num⟩
  | 1 => ⟨((277585557923915/281474976710656), (-7194129650721/562949953421312)), (33341/281474976710656), by norm_num⟩
  | 0 => ⟨((2189608487604313/2251799813685248), (-57020235909479/2251799813685248)), (538069/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2189608487604313/2251799813685248), (-57020235909479/2251799813685248)), (2052570351607512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((132980682623509/140737488355328), (-110890845406249/2251799813685248)), (1073667/2251799813685248), by norm_num⟩
  | 2 => ⟨((62655046149451/70368744177664), (-209558099851691/2251799813685248)), (1067365/1125899906842624), by norm_num⟩
  | 3 => ⟨((1765679125650683/2251799813685248), (-373173418699905/2251799813685248)), (4198777/2251799813685248), by norm_num⟩
  | 4 => ⟨((661329740821867/1125899906842624), (-585224771439851/2251799813685248)), (7976345/2251799813685248), by norm_num⟩
  | 5 => ⟨((312403452279507/1125899906842624), (-171874313190147/562949953421312)), (6758125/1125899906842624), by norm_num⟩
  | 6 => ⟨((-73069376832481/4503599627370496), (-1526078926837361/9007199254740992)), (63016015/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-237667161/134217728), (-1110054185/33554432)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-242461957/134217728), (-4529795503/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6207026087/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-511090714935529/4503599627370496), (-534638816885703/4503599627370496)), (1046381/140737488355328), by norm_num⟩
  | 1 => ⟨((1408807915/4294967296), (2947435259/8589934592)), (93/4294967296), by norm_num⟩
  | 2 => ⟨((-2035989305/4294967296), (-532448977/1073741824)), (271/8589934592), by norm_num⟩
  | 3 => ⟨((3923177325/8589934592), (4103934629/8589934592)), (33/1073741824), by norm_num⟩
  | 4 => ⟨((-2834860235/8589934592), (-2965474187/8589934592)), (193/8589934592), by norm_num⟩
  | 5 => ⟨((204844999/1073741824), (214283071/1073741824)), (225/17179869184), by norm_num⟩
  | 6 => ⟨((-3157750399/34359738368), (-1651620631/17179869184)), (219/34359738368), by norm_num⟩
  | 7 => ⟨((2607735021/68719476736), (1363942179/34359738368)), (183/68719476736), by norm_num⟩
  | 8 => ⟨((-3768661829/274877906944), (-1971149977/137438953472)), (267/274877906944), by norm_num⟩
  | 9 => ⟨((2420629715/549755813888), (1266079161/274877906944)), (173/549755813888), by norm_num⟩
  | 10 => ⟨((-1399303953/1099511627776), (-365943945/274877906944)), (101/1099511627776), by norm_num⟩
  | 11 => ⟨((2941460819/8796093022208), (3076986309/8796093022208)), (107/4398046511104), by norm_num⟩
  | 12 => ⟨((-177123235/2199023255552), (-370568097/4398046511104)), (13/2199023255552), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581622622146687/10141204801825835211973625643008), (-3039878687409/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222396950225407/79228162514264337593543950336), (-3599130380357/633825300114114700748351602688)), (23139/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890199111711195/39614081257132168796771975168), (-4048363924047/39614081257132168796771975168)), (13019/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890002226575791/2475880078570760549798248448), (-4300592250439/2475880078570760549798248448)), (27671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771667871952523/154742504910672534362390528), (-2149849292743/77371252455336267181195264)), (27679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550000144330111/9671406556917033397649408), (-4030018022975/9671406556917033397649408)), (25957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629589460745397/302231454903657293676544), (-3525316501857/604462909807314587353088)), (355/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((236053122498467/9444732965739290427392), (-2863429859817/37778931862957161709568)), (18467/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298013103624861/4722366482869645213696), (-4293587925577/4722366482869645213696)), (13857/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622097676965161/590295810358705651712), (-184411063219/18446744073709551616)), (38127/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228035501593719/9223372036854775808), (-3686324697131/36893488147419103232)), (23845/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823563934533513/9223372036854775808), (-8289016517143/9223372036854775808)), (53695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594808031615603/1152921504606846976), (-4141250609031/576460752303423488)), (53749/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298823802662209/36028797018963968), (-7239861972797/144115188075855872)), (11773/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492699191319271/36028797018963968), (-10845147580837/36028797018963968)), (70759/36028797018963968), by norm_num⟩
  | 3 => ⟨((93160479578227/562949953421312), (-13530822662709/9007199254740992)), (88663/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115258263068507/2251799813685248), (-13492440218919/2251799813685248)), (88985/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109914114595121/1125899906842624), (-20142828038015/1125899906842624)), (134283/1125899906842624), by norm_num⟩
  | 0 => ⟨((273459167435395/281474976710656), (-9975768158241/281474976710656)), (33975/140737488355328), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((273459167435395/281474976710656), (-9975768158241/281474976710656)), (129604340136480287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1061272318794869/1125899906842624), (-77533435816153/1125899906842624)), (273693/562949953421312), by norm_num⟩
  | 2 => ⟨((497507591111015/562949953421312), (-73082952323437/562949953421312)), (553661/562949953421312), by norm_num⟩
  | 3 => ⟨((860370211671491/1125899906842624), (-516697064678543/2251799813685248)), (4489405/2251799813685248), by norm_num⟩
  | 4 => ⟨((1196363784874049/2251799813685248), (-789680788151365/2251799813685248)), (8921543/2251799813685248), by norm_num⟩
  | 5 => ⟨((358686661964391/2251799813685248), (-839102562149109/2251799813685248)), (15737263/2251799813685248), by norm_num⟩
  | 6 => ⟨((-511090714935529/4503599627370496), (-534638816885703/4503599627370496)), (1046381/140737488355328), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-242461957/134217728), (-4529795503/134217728)), (1/67108864), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-61749361/33554432), (-4614529743/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-197597955/67108864), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1407866543705053/9007199254740992), (-251237045903969/9007199254740992)), (15108735/2251799813685248), by norm_num⟩
  | 1 => ⟨((3953339699/8589934592), (705482627/8589934592)), (171/8589934592), by norm_num⟩
  | 2 => ⟨((-2910091877/4294967296), (-1038625273/8589934592)), (127/4294967296), by norm_num⟩
  | 3 => ⟨((2856195985/4294967296), (1019389579/8589934592)), (251/8589934592), by norm_num⟩
  | 4 => ⟨((-4204947395/8589934592), (-750382603/8589934592)), (93/4294967296), by norm_num⟩
  | 5 => ⟨((2476242203/8589934592), (441891157/8589934592)), (221/17179869184), by norm_num⟩
  | 6 => ⟨((-4860762709/34359738368), (-867414365/34359738368)), (219/34359738368), by norm_num⟩
  | 7 => ⟨((2044602741/34359738368), (729728191/68719476736)), (93/34359738368), by norm_num⟩
  | 8 => ⟨((-6020208007/274877906944), (-1074320065/274877906944)), (69/68719476736), by norm_num⟩
  | 9 => ⟨((3939141137/549755813888), (702948861/549755813888)), (91/274877906944), by norm_num⟩
  | 10 => ⟨((-4639424283/2199023255552), (-827916011/2199023255552)), (27/274877906944), by norm_num⟩
  | 11 => ⟨((4967455163/8796093022208), (443226941/4398046511104)), (117/4398046511104), by norm_num⟩
  | 12 => ⟨((-4875456203/35184372088832), (-435018227/17592186044416)), (29/4398046511104), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (-965560635639/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444779808007693/158456325028528675187087900672), (-1143132753875/158456325028528675187087900672)), (23163/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890135462766865/39614081257132168796771975168), (-5143234808227/39614081257132168796771975168)), (13033/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((236241787281931/309485009821345068724781056), (-1365914363001/618970019642690137449562112)), (27703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110724975303651/9671406556917033397649408), (-5462499133451/154742504910672534362390528)), (27713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387483946049281/2417851639229258349412352), (-2559931137367/4835703278458516698824704)), (25991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259122246883597/604462909807314587353088), (-2239324442043/302231454903657293676544)), (711/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((236041526277333/9444732965739290427392), (-7275497170515/75557863725914323419136)), (36991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648971468735023/2361183241434822606848), (-170456379415/147573952589676412928)), (27759/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811000121309031/295147905179352825856), (-7496800475797/590295810358705651712)), (38195/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912080393835651/36893488147419103232), (-4683040334653/36893488147419103232)), (5973/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823423339853409/9223372036854775808), (-10530076513541/9223372036854775808)), (13453/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199333122868529/144115188075855872), (-1315202776125/144115188075855872)), (53881/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149395910994871/18014398509481984), (-2299227430121/36028797018963968)), (5903/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492501811139065/36028797018963968), (-13776348643751/36028797018963968)), (70991/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490311361399397/9007199254740992), (-17187165864825/9007199254740992)), (44505/4503599627370496), by norm_num⟩
  | 2 => ⟨((557493817237769/1125899906842624), (-17137277109803/2251799813685248)), (89419/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109472600802887/1125899906842624), (-12790625731705/562949953421312)), (67577/562949953421312), by norm_num⟩
  | 0 => ⟨((1092812682225901/1125899906842624), (-50664201362277/1125899906842624)), (34303/140737488355328), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1092812682225901/1125899906842624), (-50664201362277/1125899906842624)), (130855560839605287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1058417972940343/1125899906842624), (-49175314294863/562949953421312)), (557417/1125899906842624), by norm_num⟩
  | 2 => ⟨((493194711425793/562949953421312), (-184911771138279/1125899906842624)), (143175/140737488355328), by norm_num⟩
  | 3 => ⟨((104224598996615/140737488355328), (-2531239318309/8796093022208)), (297897/140737488355328), by norm_num⟩
  | 4 => ⟨((131060046434293/281474976710656), (-239940530186887/562949953421312)), (2450689/562949953421312), by norm_num⟩
  | 5 => ⟨((158244760357771/4503599627370496), (-893766611732255/2251799813685248)), (34969915/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1407866543705053/9007199254740992), (-251237045903969/9007199254740992)), (15108735/2251799813685248), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-4614529743/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-251300237/134217728), (-4694916681/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6433286071/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-631647304070797/4503599627370496), (141923968830259/2251799813685248)), (3838967/562949953421312), by norm_num⟩
  | 1 => ⟨((1804586615/4294967296), (-1621880393/8589934592)), (177/8589934592), by norm_num⟩
  | 2 => ⟨((-5406058363/8589934592), (1214679859/4294967296)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((5398367837/8589934592), (-1212951885/4294967296)), (135/4294967296), by norm_num⟩
  | 4 => ⟨((-1010754047/2147483648), (908419777/4294967296)), (51/2147483648), by norm_num⟩
  | 5 => ⟨((4844717631/17179869184), (-2177105955/17179869184)), (247/17179869184), by norm_num⟩
  | 6 => ⟨((-2418912827/17179869184), (2174008857/34359738368)), (249/34359738368), by norm_num⟩
  | 7 => ⟨((4140808699/68719476736), (-465196321/17179869184)), (215/68719476736), by norm_num⟩
  | 8 => ⟨((-775297141/34359738368), (87100227/8589934592)), (163/137438953472), by norm_num⟩
  | 9 => ⟨((1032258963/137438953472), (-927747417/274877906944)), (219/549755813888), by norm_num⟩
  | 10 => ⟨((-309237149/137438953472), (2223426303/2199023255552)), (33/274877906944), by norm_num⟩
  | 11 => ⟨((5389915389/8796093022208), (-1211052715/4398046511104)), (145/4398046511104), by norm_num⟩
  | 12 => ⟨((-5382247827/35184372088832), (1209329901/17592186044416)), (73/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790768422377973/5070602400912917605986812821504), (3542135478457/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889535785462301/316912650057057350374175801344), (4193332646337/633825300114114700748351602688)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890081955434457/39614081257132168796771975168), (294793762377/2475880078570760549798248448)), (13027/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944938794347925/1237940039285380274899124224), (5010534002131/2475880078570760549798248448)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442885763738761/38685626227668133590597632), (2504727020471/77371252455336267181195264)), (27699/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549882938212857/9671406556917033397649408), (4695215805105/9671406556917033397649408)), (25977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259076176102497/604462909807314587353088), (4107166583931/604462909807314587353088)), (22739/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944128831362927/37778931862957161709568), (3335997426707/37778931862957161709568)), (4621/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297887304484221/4722366482869645213696), (1250528597637/1180591620717411303424)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621924198038931/590295810358705651712), (1718712473837/147573952589676412928)), (38169/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912033203724791/36893488147419103232), (8588977073049/73786976294838206464)), (47747/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823318089843209/9223372036854775808), (9656295713869/9223372036854775808)), (53767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594560890997777/1152921504606846976), (1206052285709/144115188075855872)), (53829/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298769377025021/36028797018963968), (8433506566921/144115188075855872)), (11793/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492369736998293/36028797018963968), (12632547693407/36028797018963968)), (17725/9007199254740992), by norm_num⟩
  | 3 => ⟨((186268849828193/1125899906842624), (15759703505899/9007199254740992)), (88875/9007199254740992), by norm_num⟩
  | 2 => ⟨((557416920798697/1125899906842624), (7856631168843/1125899906842624)), (89251/2251799813685248), by norm_num⟩
  | 1 => ⟨((554629374448075/562949953421312), (23453898093321/1125899906842624)), (134815/1125899906842624), by norm_num⟩
  | 0 => ⟨((68278237766817/70368744177664), (23222232831779/562949953421312)), (273403/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((68278237766817/70368744177664), (23222232831779/562949953421312)), (1042949680808639171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1058081494651455/1125899906842624), (22532349458467/281474976710656)), (276559/562949953421312), by norm_num⟩
  | 2 => ⟨((987133167180653/1125899906842624), (42350233529873/281474976710656)), (564079/562949953421312), by norm_num⟩
  | 3 => ⟨((419990803587367/562949953421312), (37130583190489/140737488355328)), (579427/281474976710656), by norm_num⟩
  | 4 => ⟨((68537794004135/140737488355328), (443222446388093/1125899906842624)), (9362449/2251799813685248), by norm_num⟩
  | 5 => ⟨((92538716478751/1125899906842624), (1726760315736777/4503599627370496)), (32980199/4503599627370496), by norm_num⟩
  | 6 => ⟨((-631647304070797/4503599627370496), (141923968830259/2251799813685248)), (3838967/562949953421312), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-251300237/134217728), (-4694916681/134217728)), (1/67108864), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-255393053/134217728), (-1192845177/33554432)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-734815809175529/9007199254740992), (1124609886915987/9007199254740992)), (30142625/4503599627370496), by norm_num⟩
  | 1 => ⟨((2133525103/8589934592), (-3265285525/8589934592)), (177/8589934592), by norm_num⟩
  | 2 => ⟨((-811945631/2147483648), (4970617523/8589934592)), (17/536870912), by norm_num⟩
  | 3 => ⟨((205998891/536870912), (-2522192763/4294967296)), (139/4294967296), by norm_num⟩
  | 4 => ⟨((-2508672983/8589934592), (1919718115/4294967296)), (107/4294967296), by norm_num⟩
  | 5 => ⟨((1527542237/8589934592), (-1168924975/4294967296)), (263/17179869184), by norm_num⟩
  | 6 => ⟨((-1550212205/17179869184), (2372545543/17179869184)), (269/34359738368), by norm_num⟩
  | 7 => ⟨((2696946195/68719476736), (-2063790897/34359738368)), (59/17179869184), by norm_num⟩
  | 8 => ⟨((-2052728301/137438953472), (1570814423/68719476736)), (181/137438953472), by norm_num⟩
  | 9 => ⟨((2777589943/549755813888), (-1062751057/137438953472)), (247/549755813888), by norm_num⟩
  | 10 => ⟨((-1691286981/1099511627776), (2588455551/1099511627776)), (303/2199023255552), by norm_num⟩
  | 11 => ⟨((1872422241/4398046511104), (-2865676729/4398046511104)), (169/4398046511104), by norm_num⟩
  | 12 => ⟨((-1900210509/17592186044416), (727051425/4398046511104)), (173/17592186044416), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581497123104531/10141204801825835211973625643008), (175002237673/633825300114114700748351602688)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779028076365295/633825300114114700748351602688), (3314636300167/633825300114114700748351602688)), (5783/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472508308625485/9903520314283042199192993792), (3728332116451/39614081257132168796771975168)), (26029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472456523268701/618970019642690137449562112), (495072830083/309485009821345068724781056)), (13831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110718241457757/9671406556917033397649408), (989929059967/38685626227668133590597632)), (27669/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96864704304401/604462909807314587353088), (3711313579291/9671406556917033397649408)), (25947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629517394019719/302231454903657293676544), (3246479160793/604462909807314587353088)), (22711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((59005969112351/2361183241434822606848), (5273803592627/75557863725914323419136)), (18459/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324459461156093/1180591620717411303424), (3953843652219/4722366482869645213696)), (27701/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621857048728655/590295810358705651712), (5434083523835/590295810358705651712)), (9527/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911991878207213/36893488147419103232), (848616046953/9223372036854775808)), (47663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823226872869879/9223372036854775808), (7632491861953/9223372036854775808)), (53661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797235938716897/576460752303423488), (953272391429/144115188075855872)), (53711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((18671907740709/2251799813685248), (6665809003943/144115188075855872)), (47053/144115188075855872), by norm_num⟩
  | 4 => ⟨((746130777328491/18014398509481984), (2496132063307/9007199254740992)), (17673/9007199254740992), by norm_num⟩
  | 3 => ⟨((1490024183740701/9007199254740992), (12455859131717/9007199254740992)), (44281/4503599627370496), by norm_num⟩
  | 2 => ⟨((278680023489589/562949953421312), (12418703403189/2251799813685248)), (88859/2251799813685248), by norm_num⟩
  | 1 => ⟨((1109120112678575/1125899906842624), (9267663552713/562949953421312)), (67015/562949953421312), by norm_num⟩
  | 0 => ⟨((1092301377450519/1125899906842624), (9175177836405/281474976710656)), (4235/17592186044416), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1092301377450519/1125899906842624), (9175177836405/281474976710656)), (16155242987030739/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((529254576594263/562949953421312), (71211014962519/1125899906842624)), (543575/1125899906842624), by norm_num⟩
  | 2 => ⟨((1981296227050497/2251799813685248), (66948678730291/562949953421312)), (2181679/2251799813685248), by norm_num⟩
  | 3 => ⟨((1711440202882753/2251799813685248), (235625145305003/1125899906842624)), (2179055/1125899906842624), by norm_num⟩
  | 4 => ⟨((1202127611518541/2251799813685248), (358165360911997/1125899906842624)), (4224357/1125899906842624), by norm_num⟩
  | 5 => ⟨((25867671653201/140737488355328), (382414517689447/1125899906842624)), (7198023/1125899906842624), by norm_num⟩
  | 6 => ⟨((-734815809175529/9007199254740992), (1124609886915987/9007199254740992)), (30142625/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-255393053/134217728), (-1192845177/33554432)), (1/67108864), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile027Terms2
