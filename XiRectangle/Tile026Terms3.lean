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
namespace Reinmann.XiRectangle.Tile026Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨26,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7191/640))
  have he : value ((7/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-45376701/16777216), (-2330741837/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1186997947214103/18014398509481984), (103859236589265/9007199254740992)), (51580385/18014398509481984), by norm_num⟩
  | 1 => ⟨((1749544643/8589934592), (-153080611/4294967296)), (153/17179869184), by norm_num⟩
  | 2 => ⟨((-2703958383/8589934592), (946357335/17179869184)), (119/8589934592), by norm_num⟩
  | 3 => ⟨((1393008359/4294967296), (-243769225/4294967296)), (247/17179869184), by norm_num⟩
  | 4 => ⟨((-538230997/2147483648), (753501023/17179869184)), (193/17179869184), by norm_num⟩
  | 5 => ⟨((5323823557/34359738368), (-232910365/8589934592)), (241/34359738368), by norm_num⟩
  | 6 => ⟨((-2742694105/34359738368), (959914435/68719476736)), (125/34359738368), by norm_num⟩
  | 7 => ⟨((302777997/8589934592), (-211938305/34359738368)), (223/137438953472), by norm_num⟩
  | 8 => ⟨((-3743598571/274877906944), (327555149/137438953472)), (87/137438953472), by norm_num⟩
  | 9 => ⟨((5142943161/1099511627776), (-449994165/549755813888)), (241/1099511627776), by norm_num⟩
  | 10 => ⟨((-3179411129/2199023255552), (556380427/2199023255552)), (75/1099511627776), by norm_num⟩
  | 11 => ⟨((7147414383/17592186044416), (-625380189/8796093022208)), (339/17592186044416), by norm_num⟩
  | 12 => ⟨((-3682160215/35184372088832), (644358905/35184372088832)), (11/2199023255552), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580452642685485/10141204801825835211973625643008), (1933304967801/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888893562408499/316912650057057350374175801344), (4571173764311/633825300114114700748351602688)), (5791/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((472159291149209/9903520314283042199192993792), (5141342322173/39614081257132168796771975168)), (13033/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1888342726738175/2475880078570760549798248448), (2730583186061/1237940039285380274899124224)), (3463/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770008450196183/154742504910672534362390528), (5459468118981/154742504910672534362390528)), (27713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548444519712743/9671406556917033397649408), (5116447419141/9671406556917033397649408)), (25991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1257817833587623/604462909807314587353088), (4475088056411/604462909807314587353088)), (711/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943106684862045/37778931862957161709568), (56786232251/590295810358705651712)), (36991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296354534567453/4722366482869645213696), (5448521555929/4722366482869645213696)), (1735/295147905179352825856), by norm_num⟩
  | 9 => ⟨((809908685611209/295147905179352825856), (935864307275/73786976294838206464)), (9549/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1821433973120493/73786976294838206464), (2337860647399/18446744073709551616)), (47785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820358114982497/9223372036854775808), (5255239000471/4611686018427387904)), (53813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591602811882267/1152921504606846976), (2624529497849/288230376151711744)), (53883/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596245663222597/72057594037927936), (4585980051965/72057594037927936)), (23613/72057594037927936), by norm_num⟩
  | 4 => ⟨((744247375874993/18014398509481984), (13730183573339/36028797018963968)), (70993/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485314596785715/9007199254740992), (16713107713/8796093022208)), (11127/1125899906842624), by norm_num⟩
  | 2 => ⟨((1110008988098059/2251799813685248), (17041595341577/2251799813685248)), (44713/1125899906842624), by norm_num⟩
  | 1 => ⟨((551025013015385/562949953421312), (12690647163651/562949953421312)), (67585/562949953421312), by norm_num⟩
  | 0 => ⟨((1078149694297157/1125899906842624), (25020504723089/562949953421312)), (274483/1125899906842624), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1078149694297157/1125899906842624), (25020504723089/562949953421312)), (1047069553855514171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1030200512174649/1125899906842624), (47918734790569/562949953421312)), (137521/281474976710656), by norm_num⟩
  | 2 => ⟨((934477628353031/1125899906842624), (350765852800843/2251799813685248)), (2200607/2251799813685248), by norm_num⟩
  | 3 => ⟨((748280785795723/1125899906842624), (582259293637861/2251799813685248)), (1084629/562949953421312), by norm_num⟩
  | 4 => ⟨((844067328270181/2251799813685248), (773947025188095/2251799813685248)), (500655/140737488355328), by norm_num⟩
  | 5 => ⟨((25192216503025/1125899906842624), (1160428904564217/4503599627370496)), (11511745/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1186997947214103/18014398509481984), (103859236589265/9007199254740992)), (51580385/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-45376701/16777216), (-2330741837/67108864)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-184117023/67108864), (-591064961/16777216)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-906555388388857/18014398509481984), (722211694294689/18014398509481984)), (53219041/18014398509481984), by norm_num⟩
  | 1 => ⟨((2710818459/17179869184), (-539896629/4294967296)), (161/17179869184), by norm_num⟩
  | 2 => ⟨((-4249877799/17179869184), (3385685515/17179869184)), (127/8589934592), by norm_num⟩
  | 3 => ⟨((4441822419/17179869184), (-884649779/4294967296)), (67/4294967296), by norm_num⟩
  | 4 => ⟨((-1740913563/8589934592), (2773814265/17179869184)), (53/4294967296), by norm_num⟩
  | 5 => ⟨((2183449763/17179869184), (-1739455717/17179869184)), (67/8589934592), by norm_num⟩
  | 6 => ⟨((-2282064701/34359738368), (454504445/8589934592)), (283/68719476736), by norm_num⟩
  | 7 => ⟨((4088800383/137438953472), (-3257362419/137438953472)), (255/137438953472), by norm_num⟩
  | 8 => ⟨((-400637811/34359738368), (19948127/2147483648)), (101/137438953472), by norm_num⟩
  | 9 => ⟨((4466480139/1099511627776), (-1779121403/549755813888)), (283/1099511627776), by norm_num⟩
  | 10 => ⟨((-175057783/137438953472), (2231369947/2199023255552)), (179/2199023255552), by norm_num⟩
  | 11 => ⟨((1596778665/4398046511104), (-1272081375/4398046511104)), (103/4398046511104), by norm_num⟩
  | 12 => ⟨((-417224189/4398046511104), (664767299/8796093022208)), (217/35184372088832), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395100494305569/2535301200456458802993406410752), (1608005567543/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777730683703301/633825300114114700748351602688), (59402815517/9903520314283042199192993792)), (2893/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1888573873536267/39614081257132168796771975168), (4275976215505/39614081257132168796771975168)), (26043/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888275753030367/2475880078570760549798248448), (2270975994157/1237940039285380274899124224)), (13839/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((884970891681671/77371252455336267181195264), (1135130148451/38685626227668133590597632)), (13843/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774191172678967/4835703278458516698824704), (4255217668341/9671406556917033397649408)), (6491/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((628881878271475/302231454903657293676544), (232612224865/37778931862957161709568)), (22727/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943063052131433/37778931862957161709568), (3022534611869/37778931862957161709568)), (18473/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324072404596371/1180591620717411303424), (4531310491125/4722366482869645213696)), (6931/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1619728976323047/590295810358705651712), (6226505453223/590295810358705651712)), (19071/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455331193697239/18446744073709551616), (7777065776093/73786976294838206464)), (47711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820237044666445/9223372036854775808), (4370432075479/4611686018427387904)), (53721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591483958999039/1152921504606846976), (4365227263519/576460752303423488)), (26889/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192389818156765/144115188075855872), (3813724582771/72057594037927936)), (47121/144115188075855872), by norm_num⟩
  | 4 => ⟨((372086862185323/9007199254740992), (356806479601/1125899906842624)), (70811/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485139109856853/9007199254740992), (14231436998877/9007199254740992)), (22185/2251799813685248), by norm_num⟩
  | 2 => ⟨((554923194881189/1125899906842624), (28340683327763/4503599627370496)), (44541/1125899906842624), by norm_num⟩
  | 1 => ⟨((2203676182421967/2251799813685248), (1318953534221/70368744177664)), (134481/1125899906842624), by norm_num⟩
  | 0 => ⟨((2155704257081471/2251799813685248), (83200760662763/2251799813685248)), (544817/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2155704257081471/2251799813685248), (83200760662763/2251799813685248)), (2078311928755950217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((515158857508559/562949953421312), (159300336435861/2251799813685248)), (1083395/2251799813685248), by norm_num⟩
  | 2 => ⟨((937215145118975/1125899906842624), (72888343644297/562949953421312)), (1068065/1125899906842624), by norm_num⟩
  | 3 => ⟨((1522553435655185/2251799813685248), (242693188447417/1125899906842624)), (4109445/2251799813685248), by norm_num⟩
  | 4 => ⟨((924846434791211/2251799813685248), (164096890689403/562949953421312)), (3664411/1125899906842624), by norm_num⟩
  | 5 => ⟨((377028448819715/4503599627370496), (269587773108557/1125899906842624)), (20585459/4503599627370496), by norm_num⟩
  | 6 => ⟨((-906555388388857/18014398509481984), (722211694294689/18014398509481984)), (53219041/18014398509481984), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-184117023/67108864), (-591064961/16777216)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-373232269/134217728), (-2396351113/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-455243797784999/18014398509481984), (509843814845409/9007199254740992)), (49859373/18014398509481984), by norm_num⟩
  | 1 => ⟨((43117681/536870912), (-772624535/4294967296)), (153/17179869184), by norm_num⟩
  | 2 => ⟨((-548121245/4294967296), (2455442363/8589934592)), (245/17179869184), by norm_num⟩
  | 3 => ⟨((2322611763/17179869184), (-5202352005/17179869184)), (131/8589934592), by norm_num⟩
  | 4 => ⟨((-922673151/8589934592), (4133338679/17179869184)), (105/8589934592), by norm_num⟩
  | 5 => ⟨((2345843953/34359738368), (-656798641/4294967296)), (269/34359738368), by norm_num⟩
  | 6 => ⟨((-2485072787/68719476736), (5566243831/68719476736)), (287/68719476736), by norm_num⟩
  | 7 => ⟨((2256484311/137438953472), (-39486211/1073741824)), (263/137438953472), by norm_num⟩
  | 8 => ⟨((-112050447/17179869184), (1003914433/68719476736)), (211/274877906944), by norm_num⟩
  | 9 => ⟨((1266141697/549755813888), (-5671989527/1099511627776)), (75/274877906944), by norm_num⟩
  | 10 => ⟨((-402386647/549755813888), (450647201/274877906944)), (3/34359738368), by norm_num⟩
  | 11 => ⟨((232510259/1099511627776), (-4166344911/8796093022208)), (7/274877906944), by norm_num⟩
  | 12 => ⟨((-985240159/17592186044416), (4413622801/35184372088832)), (239/35184372088832), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790176734201497/5070602400912917605986812821504), (1296552963597/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777676053975783/633825300114114700748351602688), (191576843541/39614081257132168796771975168)), (23127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888512578685045/39614081257132168796771975168), (3447550516021/39614081257132168796771975168)), (13011/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944105422656875/1237940039285380274899124224), (3661982986731/2475880078570760549798248448)), (13827/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769877120709757/154742504910672534362390528), (3660814087219/154742504910672534362390528)), (6915/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548321984294857/9671406556917033397649408), (857692922491/2417851639229258349412352)), (12969/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628855600278495/302231454903657293676544), (1500342102789/302231454903657293676544)), (22703/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886041187691765/75557863725914323419136), (2436892982179/37778931862957161709568)), (4613/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((5063384205121/18446744073709551616), (1826652692781/2361183241434822606848)), (13845/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25306916903975/9223372036854775808), (2509995738661/295147905179352825856)), (19045/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455304485253637/18446744073709551616), (783754705181/9223372036854775808)), (5955/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455029569062057/2305843009213693952), (7046989333187/9223372036854775808)), (419/72057594037927936), by norm_num⟩
  | 6 => ⟨((1591366961157839/1152921504606846976), (7038493932683/1152921504606846976)), (26839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192289431596389/144115188075855872), (1537284090055/36028797018963968)), (47021/144115188075855872), by norm_num⟩
  | 4 => ⟨((1488200828654279/36028797018963968), (9204641588383/36028797018963968)), (17659/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484962734348513/9007199254740992), (5736253171317/4503599627370496)), (44239/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219360607757145/4503599627370496), (22845383479023/4503599627370496)), (177507/4503599627370496), by norm_num⟩
  | 1 => ⟨((1101614477951463/1125899906842624), (8504975641595/562949953421312)), (267645/2251799813685248), by norm_num⟩
  | 0 => ⟨((1077505719076259/1125899906842624), (67052503391775/2251799813685248)), (540855/2251799813685248), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((1077505719076259/1125899906842624), (67052503391775/2251799813685248)), (2063198098189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((128774165229969/140737488355328), (128340815100745/2251799813685248)), (1067427/2251799813685248), by norm_num⟩
  | 2 => ⟨((469482425894637/562949953421312), (234862530554839/2251799813685248)), (1037529/1125899906842624), by norm_num⟩
  | 3 => ⟨((770818867251497/1125899906842624), (391735819237621/2251799813685248)), (3893923/2251799813685248), by norm_num⟩
  | 4 => ⟨((493647334647241/1125899906842624), (536384022436529/2251799813685248)), (6686571/2251799813685248), by norm_num⟩
  | 5 => ⟨((610216716705123/4503599627370496), (940703667933315/4503599627370496)), (9048927/2251799813685248), by norm_num⟩
  | 6 => ⟨((-455243797784999/18014398509481984), (509843814845409/9007199254740992)), (49859373/18014398509481984), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-373232269/134217728), (-2396351113/67108864)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-378026425/134217728), (-4854264325/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((83533848813969/36028797018963968), (2153405114175171/36028797018963968)), (43328065/18014398509481984), by norm_num⟩
  | 1 => ⟨((-256428801/34359738368), (-6610435165/34359738368)), (67/8589934592), by norm_num⟩
  | 2 => ⟨((206353117/17179869184), (2659771243/8589934592)), (217/17179869184), by norm_num⟩
  | 3 => ⟨((-221408353/17179869184), (-5707648903/17179869184)), (235/17179869184), by norm_num⟩
  | 4 => ⟨((178171499/17179869184), (1148263317/4294967296)), (191/17179869184), by norm_num⟩
  | 5 => ⟨((-57351193/8589934592), (-5913787251/34359738368)), (31/4294967296), by norm_num⟩
  | 6 => ⟨((246141825/68719476736), (6345248939/68719476736)), (67/17179869184), by norm_num⟩
  | 7 => ⟨((-56592855/34359738368), (-5835590975/137438953472)), (31/17179869184), by norm_num⟩
  | 8 => ⟨((182165373/274877906944), (2348005339/137438953472)), (201/274877906944), by norm_num⟩
  | 9 => ⟨((-260607873/1099511627776), (-839770847/137438953472)), (145/549755813888), by norm_num⟩
  | 10 => ⟨((41943219/549755813888), (4324988925/2199023255552)), (189/2199023255552), by norm_num⟩
  | 11 => ⟨((-98189101/4398046511104), (-2531200417/4398046511104)), (223/8796093022208), by norm_num⟩
  | 12 => ⟨((105352841/17592186044416), (2715873277/17592186044416)), (241/35184372088832), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580306940097431/10141204801825835211973625643008), (249454079773/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1777623111345095/633825300114114700748351602688), (2358835765757/633825300114114700748351602688)), (23109/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888453145108471/39614081257132168796771975168), (2653044937533/39614081257132168796771975168)), (26001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888147866458623/2475880078570760549798248448), (704512614879/618970019642690137449562112)), (27631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1769814332128823/154742504910672534362390528), (1408569939209/77371252455336267181195264)), (6909/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774131661003239/4835703278458516698824704), (2640101519413/9671406556917033397649408)), (12957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((628830036440351/302231454903657293676544), (2309122135737/604462909807314587353088)), (2835/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((942979241629485/37778931862957161709568), (3750511817949/75557863725914323419136)), (9/18446744073709551616), by norm_num⟩
  | 10 => ⟨((648082329295025/2361183241434822606848), (2811299565121/4722366482869645213696)), (27657/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404889595850707/147573952589676412928), (3862964099469/590295810358705651712)), (38041/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821113370982467/73786976294838206464), (1206212215613/18446744073709551616)), (11893/18446744073709551616), by norm_num⟩
  | 7 => ⟨((28437527142177/144115188075855872), (5422657387259/9223372036854775808)), (53547/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795625898318087/576460752303423488), (2708021283913/576460752303423488)), (26791/576460752303423488), by norm_num⟩
  | 5 => ⟨((1192190204916621/144115188075855872), (4731605408777/144115188075855872)), (46925/144115188075855872), by norm_num⟩
  | 4 => ⟨((46501720711291/1125899906842624), (3541284495365/18014398509481984)), (17617/9007199254740992), by norm_num⟩
  | 3 => ⟨((1484785883300723/9007199254740992), (2206824483859/2251799813685248)), (44113/4503599627370496), by norm_num⟩
  | 2 => ⟨((2219022881287131/4503599627370496), (17577076184869/4503599627370496)), (176877/4503599627370496), by norm_num⟩
  | 1 => ⟨((550690494970147/562949953421312), (3271572993171/281474976710656)), (16649/140737488355328), by norm_num⟩
  | 0 => ⟨((269279249838191/281474976710656), (51577644712355/2251799813685248)), (537065/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((269279249838191/281474976710656), (51577644712355/2251799813685248)), (2048740395552825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2059714118260885/2251799813685248), (98685784710737/2251799813685248)), (1052195/2251799813685248), by norm_num⟩
  | 2 => ⟨((1879689011045845/2251799813685248), (11283446623731/140737488355328)), (2017105/2251799813685248), by norm_num⟩
  | 3 => ⟨((777297746015781/1125899906842624), (301403284557715/2251799813685248)), (1845497/1125899906842624), by norm_num⟩
  | 4 => ⟨((1032917397793065/2251799813685248), (208082523414945/1125899906842624)), (3042225/1125899906842624), by norm_num⟩
  | 5 => ⟨((793787262108367/4503599627370496), (763592064643531/4503599627370496)), (3915477/1125899906842624), by norm_num⟩
  | 6 => ⟨((83533848813969/36028797018963968), (2153405114175171/36028797018963968)), (43328065/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-378026425/134217728), (-4854264325/134217728)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-191316263/67108864), (-614176449/16777216)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((480281966298165/18014398509481984), (923767516694589/18014398509481984)), (2204257/1125899906842624), by norm_num⟩
  | 1 => ⟨((-746157175/8589934592), (-1435148119/8589934592)), (111/17179869184), by norm_num⟩
  | 2 => ⟨((2431052109/17179869184), (2337925559/8589934592)), (183/17179869184), by norm_num⟩
  | 3 => ⟨((-660050205/4294967296), (-1269531195/4294967296)), (25/2147483648), by norm_num⟩
  | 4 => ⟨((268813411/2147483648), (4136255191/17179869184)), (165/17179869184), by norm_num⟩
  | 5 => ⟨((-700656035/8589934592), (-5390527487/34359738368)), (217/34359738368), by norm_num⟩
  | 6 => ⟨((1521870001/34359738368), (2927143157/34359738368)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-2833371075/137438953472), (-2724832853/68719476736)), (113/68719476736), by norm_num⟩
  | 8 => ⟨((2307849123/274877906944), (4438884243/274877906944)), (93/137438953472), by norm_num⟩
  | 9 => ⟨((-1670932275/549755813888), (-3213847419/549755813888)), (17/68719476736), by norm_num⟩
  | 10 => ⟨((272202933/274877906944), (1047102515/549755813888)), (179/2199023255552), by norm_num⟩
  | 11 => ⟨((-161247897/549755813888), (-1240567665/2199023255552)), (215/8796093022208), by norm_num⟩
  | 12 => ⟨((175120405/2199023255552), (5389185619/35184372088832)), (59/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395065559226429/2535301200456458802993406410752), (1421595808309/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444392936082571/158456325028528675187087900672), (1680229525613/633825300114114700748351602688)), (23093/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1888395451583939/39614081257132168796771975168), (1889794938371/39614081257132168796771975168)), (25981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888086693036215/2475880078570760549798248448), (2007323469099/2475880078570760549798248448)), (3451/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((884876650117735/77371252455336267181195264), (2006667203673/154742504910672534362390528)), (6903/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774103127431041/4835703278458516698824704), (470138377603/2417851639229258349412352)), (12945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257610289250963/604462909807314587353088), (1644787653825/604462909807314587353088)), (22657/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((942938933027051/37778931862957161709568), (1335737188077/37778931862957161709568)), (36825/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324026110361591/1180591620717411303424), (500616026587/1180591620717411303424)), (27625/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((404868995914411/147573952589676412928), (687883554177/147573952589676412928)), (18997/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1821010968611133/73786976294838206464), (3436639138685/73786976294838206464)), (47507/73786976294838206464), by norm_num⟩
  | 7 => ⟨((909943677111113/4611686018427387904), (1931201042201/4611686018427387904)), (53465/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1591138436234611/1152921504606846976), (482204550559/144115188075855872)), (53491/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298023040436121/36028797018963968), (3370078021933/144115188075855872)), (23417/72057594037927936), by norm_num⟩
  | 4 => ⟨((743955142306929/18014398509481984), (2522214118177/18014398509481984)), (70307/36028797018963968), by norm_num⟩
  | 3 => ⟨((371152223699653/2251799813685248), (3143436138915/4503599627370496)), (87985/9007199254740992), by norm_num⟩
  | 2 => ⟨((1109340393755657/2251799813685248), (12517924632109/4503599627370496)), (88137/2251799813685248), by norm_num⟩
  | 1 => ⟨((550569576424589/562949953421312), (9318963701451/1125899906842624)), (265175/2251799813685248), by norm_num⟩
  | 0 => ⟨((538345768724071/562949953421312), (18361772365143/1125899906842624)), (66679/281474976710656), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((538345768724071/562949953421312), (18361772365143/1125899906842624)), (254360200048351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1029334406268893/1125899906842624), (70237024793935/2251799813685248)), (259409/562949953421312), by norm_num⟩
  | 2 => ⟨((469977838875461/562949953421312), (128425956472637/2251799813685248)), (1962013/2251799813685248), by norm_num⟩
  | 3 => ⟨((1562116426545077/2251799813685248), (214432395319349/2251799813685248)), (3499765/2251799813685248), by norm_num⟩
  | 4 => ⟨((1063250144781399/2251799813685248), (297511674950857/2251799813685248)), (5522253/2251799813685248), by norm_num⟩
  | 5 => ⟨((115683870665695/562949953421312), (280956885725963/2251799813685248)), (13348383/4503599627370496), by norm_num⟩
  | 6 => ⟨((480281966298165/18014398509481984), (923767516694589/18014398509481984)), (2204257/1125899906842624), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-191316263/67108864), (-614176449/16777216)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-387064769/134217728), (-2485163173/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((395632478654197/9007199254740992), (311703175442181/9007199254740992)), (13483673/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2487068383/17179869184), (-979731385/8589934592)), (11/4294967296), by norm_num⟩
  | 2 => ⟨((512310729/2147483648), (3229034817/17179869184)), (75/17179869184), by norm_num⟩
  | 3 => ⟨((-1125661725/4294967296), (-1773728665/8589934592)), (85/17179869184), by norm_num⟩
  | 4 => ⟨((927499353/4294967296), (1461480081/8589934592)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-2445509249/17179869184), (-481679993/4294967296)), (49/17179869184), by norm_num⟩
  | 6 => ⟨((2686666513/34359738368), (1058359119/17179869184)), (55/34359738368), by norm_num⟩
  | 7 => ⟨((-2529947011/68719476736), (-249155643/8589934592)), (53/68719476736), by norm_num⟩
  | 8 => ⟨((2084573157/137438953472), (1642352707/137438953472)), (89/274877906944), by norm_num⟩
  | 9 => ⟨((-763379229/137438953472), (-2405745155/549755813888)), (67/549755813888), by norm_num⟩
  | 10 => ⟨((4025557449/2199023255552), (3171577429/2199023255552)), (45/1099511627776), by norm_num⟩
  | 11 => ⟨((-1206143695/2199023255552), (-237568223/549755813888)), (7/549755813888), by norm_num⟩
  | 12 => ⟨((1325084285/8796093022208), (2087962953/17592186044416)), (63/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580219221042939/10141204801825835211973625643008), (869225992823/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1777521852545021/633825300114114700748351602688), (1027309921775/633825300114114700748351602688)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472084847198069/9903520314283042199192993792), (577718989381/19807040628566084398385987584)), (12981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888027213542891/2475880078570760549798248448), (613645973599/1237940039285380274899124224)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1769693918755309/154742504910672534362390528), (1226886156659/154742504910672534362390528)), (13795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548150688782263/9671406556917033397649408), (17965231343/151115727451828646838272)), (6467/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257561772897535/604462909807314587353088), (251405549817/151115727451828646838272)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1885799221722703/75557863725914323419136), (816664426185/37778931862957161709568)), (9197/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296045628403943/4722366482869645213696), (612145383089/2361183241434822606848)), (13797/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619395391946031/590295810358705651712), (52570424835/18446744073709551616)), (9487/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227613830333659/9223372036854775808), (1050549570151/36893488147419103232)), (11861/36893488147419103232), by norm_num⟩
  | 7 => ⟨((454943763835391/2305843009213693952), (590344213793/2305843009213693952)), (13347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1591026845565797/1152921504606846976), (2358430809653/1152921504606846976)), (13351/576460752303423488), by norm_num⟩
  | 5 => ⟨((1191995314529865/144115188075855872), (1030158767111/72057594037927936)), (23373/144115188075855872), by norm_num⟩
  | 4 => ⟨((743883298875347/18014398509481984), (3083869626137/36028797018963968)), (35077/36028797018963968), by norm_num⟩
  | 3 => ⟨((742216023147373/4503599627370496), (3843302688137/9007199254740992)), (43877/9007199254740992), by norm_num⟩
  | 2 => ⟨((554583830870237/1125899906842624), (7652111427641/4503599627370496)), (87847/4503599627370496), by norm_num⟩
  | 1 => ⟨((2201780527460339/2251799813685248), (11392312885359/2251799813685248)), (16501/281474976710656), by norm_num⟩
  | 0 => ⟨((538117051916807/562949953421312), (2805435376475/281474976710656)), (264973/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((538117051916807/562949953421312), (2805435376475/281474976710656)), (1010791787154387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((514323658672263/562949953421312), (42906907939705/2251799813685248)), (127963/562949953421312), by norm_num⟩
  | 2 => ⟨((939386393377409/1125899906842624), (78401420018761/2251799813685248)), (477393/1125899906842624), by norm_num⟩
  | 3 => ⟨((1564810681737641/2251799813685248), (32706827107583/562949953421312)), (1659725/2251799813685248), by norm_num⟩
  | 4 => ⟨((134976290425087/281474976710656), (181827859164557/2251799813685248)), (2499595/2251799813685248), by norm_num⟩
  | 5 => ⟨((503121528507555/2251799813685248), (174384595126519/2251799813685248)), (1400473/1125899906842624), by norm_num⟩
  | 6 => ⟨((395632478654197/9007199254740992), (311703175442181/9007199254740992)), (13483673/18014398509481984), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-387064769/134217728), (-2485163173/67108864)), (1/134217728), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨26,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile026Terms3
