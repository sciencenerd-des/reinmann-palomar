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
namespace Reinmann.XiRectangle.Tile040Terms2
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
  | 0 => ⟨((-27619065/16777216), (-1306636157/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((561208154746477/9007199254740992), (-821590470676657/4503599627370496)), (61688161/2251799813685248), by norm_num⟩
  | 1 => ⟨((-185489583/1073741824), (1086202847/2147483648)), (165/2147483648), by norm_num⟩
  | 2 => ⟨((257143163/1073741824), (-752898441/1073741824)), (231/2147483648), by norm_num⟩
  | 3 => ⟨((-475301489/2147483648), (695825909/1073741824)), (27/268435456), by norm_num⟩
  | 4 => ⟨((329453887/2147483648), (-482309767/1073741824)), (151/2147483648), by norm_num⟩
  | 5 => ⟨((-365376053/4294967296), (1069797297/4294967296)), (85/2147483648), by norm_num⟩
  | 6 => ⟨((337679175/8589934592), (-61793915/536870912)), (159/8589934592), by norm_num⟩
  | 7 => ⟨((-534997413/34359738368), (783218797/17179869184)), (127/17179869184), by norm_num⟩
  | 8 => ⟨((92707987/17179869184), (-542885901/34359738368)), (89/34359738368), by norm_num⟩
  | 9 => ⟨((-228480995/137438953472), (1337954957/274877906944)), (221/274877906944), by norm_num⟩
  | 10 => ⟨((63348383/137438953472), (-741919765/549755813888)), (247/1099511627776), by norm_num⟩
  | 11 => ⟨((-255474927/2199023255552), (374006977/1099511627776)), (251/4398046511104), by norm_num⟩
  | 12 => ⟨((236108967/8796093022208), (-1382623369/17592186044416)), (117/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197728921977025/1267650600228229401496703205376), (-202178378915/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111214234968281/39614081257132168796771975168), (-1915494115121/633825300114114700748351602688)), (92389/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945241515052965/19807040628566084398385987584), (-1077308005909/19807040628566084398385987584)), (103949/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472576050781675/618970019642690137449562112), (-572223699457/618970019642690137449562112)), (27615/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221496275082549/19342813113834066795298816), (-1144231042007/77371252455336267181195264)), (27619/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550283951426077/9671406556917033397649408), (-2144973539349/9671406556917033397649408)), (25897/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314856906592117/151115727451828646838272), (-469098072065/151115727451828646838272)), (2833/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((944414912741379/37778931862957161709568), (-381034502573/9444732965739290427392)), (147347/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298317349746557/4722366482869645213696), (-2285453473199/4722366482869645213696)), (55269/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811258504417065/295147905179352825856), (-785318610145/147573952589676412928)), (152035/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824809665928591/73786976294838206464), (-981189414949/18446744073709551616)), (95055/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824157337851159/9223372036854775808), (-4412829901481/9223372036854775808)), (106983/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797701992415721/576460752303423488), (-2204839306857/576460752303423488)), (214081/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195819532212733/144115188075855872), (-3854926054631/144115188075855872)), (187451/144115188075855872), by norm_num⟩
  | 4 => ⟨((186686422917885/4503599627370496), (-2887654890021/18014398509481984)), (70359/9007199254740992), by norm_num⟩
  | 3 => ⟨((745783935394165/4503599627370496), (-1801690576149/2251799813685248)), (352251/9007199254740992), by norm_num⟩
  | 2 => ⟨((139534166014971/281474976710656), (-14376455236849/4503599627370496)), (352935/2251799813685248), by norm_num⟩
  | 1 => ⟨((555736820428569/562949953421312), (-10736101547391/1125899906842624)), (132779/281474976710656), by norm_num⟩
  | 0 => ⟨((137137750058971/140737488355328), (-5321955954953/281474976710656)), (2138211/2251799813685248), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((137137750058971/140737488355328), (-5321955954953/281474976710656)), (8156627663619231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2137276361218049/2251799813685248), (-82973322784619/2251799813685248)), (2123949/1125899906842624), by norm_num⟩
  | 2 => ⟨((506380012580137/562949953421312), (-157506826602899/2251799813685248)), (4188381/1125899906842624), by norm_num⟩
  | 3 => ⟨((113185102230241/140737488355328), (-283358434801903/2251799813685248)), (16241851/2251799813685248), by norm_num⟩
  | 4 => ⟨((1420770187430415/2251799813685248), (-113942467588595/562949953421312)), (15105977/1125899906842624), by norm_num⟩
  | 5 => ⟨((804184164046355/2251799813685248), (-143783705858997/562949953421312)), (50354337/2251799813685248), by norm_num⟩
  | 6 => ⟨((561208154746477/9007199254740992), (-821590470676657/4503599627370496)), (61688161/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-27619065/16777216), (-1306636157/33554432)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-56445951/33554432), (-1335206685/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-104460348076109/1125899906842624), (-725810999461223/4503599627370496)), (148960447/4503599627370496), by norm_num⟩
  | 1 => ⟨((564495949/2147483648), (122569645/268435456)), (203/2147483648), by norm_num⟩
  | 2 => ⟨((-99958591/268435456), (-173632977/268435456)), (73/536870912), by norm_num⟩
  | 3 => ⟨((47200669/134217728), (655919023/1073741824)), (139/1073741824), by norm_num⟩
  | 4 => ⟨((-534918261/2147483648), (-7259213/16777216)), (199/2147483648), by norm_num⟩
  | 5 => ⟨((303107511/2147483648), (263256309/1073741824)), (227/4294967296), by norm_num⟩
  | 6 => ⟨((-572512163/8589934592), (-994481717/8589934592)), (27/1073741824), by norm_num⟩
  | 7 => ⟨((57930325/2147483648), (805022535/17179869184)), (177/17179869184), by norm_num⟩
  | 8 => ⟨((-656515879/68719476736), (-570200147/34359738368)), (253/68719476736), by norm_num⟩
  | 9 => ⟨((51668043/17179869184), (717999407/137438953472)), (161/137438953472), by norm_num⟩
  | 10 => ⟨((-117109271/137438953472), (-101712275/68719476736)), (185/549755813888), by norm_num⟩
  | 11 => ⟨((120652927/549755813888), (419160109/1099511627776)), (3/34359738368), by norm_num⟩
  | 12 => ⟨((-113945161/2199023255552), (-791713343/8796093022208)), (183/8796093022208), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581784487175485/10141204801825835211973625643008), (-2726559280557/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222421077445527/79228162514264337593543950336), (-3228830798545/633825300114114700748351602688)), (46259/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890416299094351/39614081257132168796771975168), (-3631885434345/39614081257132168796771975168)), (104103/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472558261705175/618970019642690137449562112), (-3858214758509/2475880078570760549798248448)), (110633/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771898758096413/154742504910672534362390528), (-1928734181019/77371252455336267181195264)), (110659/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550216670035969/9671406556917033397649408), (-3615583643019/9671406556917033397649408)), (103771/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629684225674373/302231454903657293676544), (-3162842853475/604462909807314587353088)), (90829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944366548416561/37778931862957161709568), (-5138133311405/75557863725914323419136)), (2307/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298244305560659/4722366482869645213696), (-3852299687419/4722366482869645213696)), (110783/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202801970630809/73786976294838206464), (-5294799536705/590295810358705651712)), (76201/295147905179352825856), by norm_num⟩
  | 8 => ⟨((456170475104953/18446744073709551616), (-6615331404585/73786976294838206464)), (190615/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824011938908077/9223372036854775808), (-3718946541235/4611686018427387904)), (107299/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797628255278681/576460752303423488), (-58066027823/9007199254740992)), (26849/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195688161736173/144115188075855872), (-3248638019117/72057594037927936)), (94081/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493289677296057/36028797018963968), (-9733682491603/36028797018963968)), (141341/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491307624062877/9007199254740992), (-6072856360485/4503599627370496)), (44265/1125899906842624), by norm_num⟩
  | 2 => ⟨((1116000957902903/2251799813685248), (-3028414217587/562949953421312)), (355273/2251799813685248), by norm_num⟩
  | 1 => ⟨((1111034943640289/1125899906842624), (-18090449976731/1125899906842624)), (535799/1125899906842624), by norm_num⟩
  | 0 => ⟨((1096105036948699/1125899906842624), (-35861386086811/1125899906842624)), (270797/281474976710656), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1096105036948699/1125899906842624), (-35861386086811/1125899906842624)), (1033008576513194949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532978200690089/562949953421312), (-69824760945131/1125899906842624)), (1089025/562949953421312), by norm_num⟩
  | 2 => ⟨((502437004180549/562949953421312), (-132214507616451/1125899906842624)), (1098583/281474976710656), by norm_num⟩
  | 3 => ⟨((1762663076219865/2251799813685248), (-29500606897777/140737488355328)), (17752003/2251799813685248), by norm_num⟩
  | 4 => ⟨((640418374684551/1125899906842624), (-738959194347737/2251799813685248)), (17616983/1125899906842624), by norm_num⟩
  | 5 => ⟨((486047685487701/2251799813685248), (-210162130455053/562949953421312)), (63207593/2251799813685248), by norm_num⟩
  | 6 => ⟨((-104460348076109/1125899906842624), (-725810999461223/4503599627370496)), (148960447/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56445951/33554432), (-1335206685/33554432)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-57584715/33554432), (-1362143695/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1570483137223305/9007199254740992), (-196878073434277/4503599627370496)), (277656007/9007199254740992), by norm_num⟩
  | 1 => ⟨((1082248713/2147483648), (271344577/2147483648)), (193/2147483648), by norm_num⟩
  | 2 => ⟨((-782025279/1073741824), (-392143351/2147483648)), (281/2147483648), by norm_num⟩
  | 3 => ⟨((753447927/1073741824), (94453339/536870912)), (273/2147483648), by norm_num⟩
  | 4 => ⟨((-1088872305/2147483648), (-17062829/134217728)), (199/2147483648), by norm_num⟩
  | 5 => ⟨((9835143/33554432), (157817341/2147483648)), (29/536870912), by norm_num⟩
  | 6 => ⟨((-606447351/4294967296), (-76025131/2147483648)), (113/4294967296), by norm_num⟩
  | 7 => ⟨((31301041/536870912), (7847889/536870912)), (189/17179869184), by norm_num⟩
  | 8 => ⟨((-1447546319/68719476736), (-90733267/17179869184)), (275/68719476736), by norm_num⟩
  | 9 => ⟨((58110375/8589934592), (3642401/2147483648)), (89/68719476736), by norm_num⟩
  | 10 => ⟨((-1074947755/549755813888), (-67378515/137438953472)), (13/34359738368), by norm_num⟩
  | 11 => ⟨((1129817685/2199023255552), (141635605/1099511627776)), (55/549755813888), by norm_num⟩
  | 12 => ⟨((-1088531043/8796093022208), (-136459851/4398046511104)), (107/4398046511104), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581740279386373/10141204801825835211973625643008), (-1886138484347/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222413896829319/79228162514264337593543950336), (-4466934712419/633825300114114700748351602688)), (2895/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((945175695046159/19807040628566084398385987584), (-2512256452805/19807040628566084398385987584)), (13031/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236270464619655/309485009821345068724781056), (-5337606859601/2475880078570760549798248448)), (27699/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771829018904413/154742504910672534362390528), (-5336551383307/154742504910672534362390528)), (110833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387537713717723/2417851639229258349412352), (-5001895496727/9671406556917033397649408)), (103945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629655214337649/302231454903657293676544), (-68367768047/9444732965739290427392)), (90991/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888637996051881/75557863725914323419136), (-444259080451/4722366482869645213696)), (147933/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298172268350463/4722366482869645213696), (-5329269243961/4722366482869645213696)), (55507/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811157779281251/295147905179352825856), (-7324755747625/590295810358705651712)), (152749/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456138727801513/18446744073709551616), (-9151460640393/73786976294838206464)), (47773/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455966674701929/2305843009213693952), (-10289227907683/9223372036854775808)), (107597/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398777075867863/288230376151711744), (-10281521645681/1152921504606846976)), (215463/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597777574471047/72057594037927936), (-4493831213855/72057594037927936)), (188833/144115188075855872), by norm_num⟩
  | 4 => ⟨((373270877642933/9007199254740992), (-13464156982539/36028797018963968)), (141929/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491038317676565/9007199254740992), (-16799860241317/9007199254740992)), (355885/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115714324897705/2251799813685248), (-4188590707153/562949953421312)), (89371/562949953421312), by norm_num⟩
  | 1 => ⟨((1110561923583687/1125899906842624), (-6254456187793/281474976710656)), (540229/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094988188733629/1125899906842624), (-49580924176617/1125899906842624)), (1096523/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1094988188733629/1125899906842624), (-49580924176617/1125899906842624)), (4182903294089889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062741774958861/1125899906842624), (-24109836953509/281474976710656)), (2229411/1125899906842624), by norm_num⟩
  | 2 => ⟨((994865996194173/1125899906842624), (-182059032155315/1125899906842624)), (143457/35184372088832), by norm_num⟩
  | 3 => ⟨((849642897543829/1125899906842624), (-40217682604503/140737488355328)), (4798669/562949953421312), by norm_num⟩
  | 4 => ⟨((17163367552913/35184372088832), (-971188807755765/2251799813685248)), (19970109/1125899906842624), by norm_num⟩
  | 5 => ⟨((58485846509825/1125899906842624), (-1895031172215063/4503599627370496)), (146837293/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1570483137223305/9007199254740992), (-196878073434277/4503599627370496)), (277656007/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57584715/33554432), (-1362143695/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-58661893/33554432), (-86726495/2097152)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-341390584730473/2251799813685248), (770506086114101/9007199254740992)), (280592875/9007199254740992), by norm_num⟩
  | 1 => ⟨((479318497/1073741824), (-270451087/1073741824)), (199/2147483648), by norm_num⟩
  | 2 => ⟨((-705662033/1073741824), (398163361/1073741824)), (37/268435456), by norm_num⟩
  | 3 => ⟨((173148233/268435456), (-48848655/134217728)), (73/536870912), by norm_num⟩
  | 4 => ⟨((-1019648813/2147483648), (575327535/2147483648)), (217/2147483648), by norm_num⟩
  | 5 => ⟨((300229371/1073741824), (-84700841/536870912)), (257/4294967296), by norm_num⟩
  | 6 => ⟨((-1178676083/8589934592), (665057221/8589934592)), (255/8589934592), by norm_num⟩
  | 7 => ⟨((991582801/17179869184), (-69936443/2147483648)), (217/17179869184), by norm_num⟩
  | 8 => ⟨((-729913763/34359738368), (205923589/17179869184)), (81/17179869184), by norm_num⟩
  | 9 => ⟨((29849813/4294967296), (-33684969/8589934592)), (107/68719476736), by norm_num⟩
  | 10 => ⟨((-1125004197/549755813888), (634773349/549755813888)), (127/274877906944), by norm_num⟩
  | 11 => ⟨((9410529/17179869184), (-169913763/549755813888)), (275/2199023255552), by norm_num⟩
  | 12 => ⟨((-591119539/4398046511104), (667067609/8796093022208)), (17/549755813888), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581698462418273/10141204801825835211973625643008), (3423109362455/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779263541993629/633825300114114700748351602688), (253328369749/39614081257132168796771975168)), (92599/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890297920931491/39614081257132168796771975168), (4559187516449/39614081257132168796771975168)), (104199/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890107055141613/2475880078570760549798248448), (1210817560851/618970019642690137449562112)), (55371/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771772524832803/154742504910672534362390528), (2421147707945/77371252455336267181195264)), (110775/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387524517455779/2417851639229258349412352), (2269308134511/4835703278458516698824704)), (103887/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259264419808883/604462909807314587353088), (496281703939/75557863725914323419136)), (90937/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888563565288751/75557863725914323419136), (6449720563143/75557863725914323419136)), (73919/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298116737017625/4722366482869645213696), (4835591702349/4722366482869645213696)), (110937/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811119838341071/295147905179352825856), (6646178489321/590295810358705651712)), (152633/590295810358705651712), by norm_num⟩
  | 8 => ⟨((456115192188457/18446744073709551616), (259486984953/2305843009213693952)), (190933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911880881797153/4611686018427387904), (4667920214329/4611686018427387904)), (107497/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595004585467651/1152921504606846976), (9328728012595/1152921504606846976)), (215239/1152921504606846976), by norm_num⟩
  | 5 => ⟨((4669788136147/562949953421312), (8154637435529/144115188075855872)), (94305/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492952160278981/36028797018963968), (3053990439019/9007199254740992)), (283465/36028797018963968), by norm_num⟩
  | 3 => ⟨((745439446464393/4503599627370496), (15241972757193/9007199254740992)), (11103/281474976710656), by norm_num⟩
  | 2 => ⟨((1115562020124541/2251799813685248), (3800006316887/562949953421312)), (356745/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110351179906009/1125899906842624), (22695245697705/1125899906842624)), (538749/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094637036626189/1125899906842624), (2810736697813/70368744177664)), (1092071/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1094637036626189/1125899906842624), (2810736697813/70368744177664)), (4165920261863326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531222967975675/562949953421312), (87446110502199/1125899906842624)), (2210737/1125899906842624), by norm_num⟩
  | 2 => ⟨((995776389858329/1125899906842624), (165035566933039/1125899906842624)), (4515693/1125899906842624), by norm_num⟩
  | 3 => ⟨((856500541820517/1125899906842624), (145961927912101/562949953421312)), (9311433/1125899906842624), by norm_num⟩
  | 4 => ⟨((143967868857413/281474976710656), (888295448517921/2251799813685248)), (18995431/1125899906842624), by norm_num⟩
  | 5 => ⟨((238672646533741/2251799813685248), (908684701804425/2251799813685248)), (68836331/2251799813685248), by norm_num⟩
  | 6 => ⟨((-341390584730473/2251799813685248), (770506086114101/9007199254740992)), (280592875/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-58661893/33554432), (-86726495/2097152)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-29841903/16777216), (-1411796879/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-62804163022593/1125899906842624), (1435522482362935/9007199254740992)), (32969767/1125899906842624), by norm_num⟩
  | 1 => ⟨((358857075/2147483648), (-64081565/134217728)), (95/1073741824), by norm_num⟩
  | 2 => ⟨((-537519861/2147483648), (1535769699/2147483648)), (287/2147483648), by norm_num⟩
  | 3 => ⟨((268377599/1073741824), (-1533584951/2147483648)), (289/2147483648), by norm_num⟩
  | 4 => ⟨((-401993717/2147483648), (1148552483/2147483648)), (109/1073741824), by norm_num⟩
  | 5 => ⟨((481706221/4294967296), (-1376302297/4294967296)), (263/4294967296), by norm_num⟩
  | 6 => ⟨((-240510479/4294967296), (1374344403/8589934592)), (265/8589934592), by norm_num⟩
  | 7 => ⟨((411717145/17179869184), (-1176333681/17179869184)), (229/17179869184), by norm_num⟩
  | 8 => ⟨((-308348585/34359738368), (880995193/34359738368)), (173/34359738368), by norm_num⟩
  | 9 => ⟨((410546581/137438953472), (-1172989215/137438953472)), (29/17179869184), by norm_num⟩
  | 10 => ⟨((-491955057/549755813888), (1405584659/549755813888)), (35/68719476736), by norm_num⟩
  | 11 => ⟨((535914779/2199023255552), (-1531183755/2199023255552)), (307/2199023255552), by norm_num⟩
  | 12 => ⟨((-33447025/549755813888), (1529005531/8796093022208)), (309/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581658790884579/10141204801825835211973625643008), (2484694490095/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779220724980395/633825300114114700748351602688), (2941942742313/633825300114114700748351602688)), (46245/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890249998871967/39614081257132168796771975168), (3309159956623/39614081257132168796771975168)), (104069/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890056453944859/2475880078570760549798248448), (1757671770881/1237940039285380274899124224)), (110595/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771722278933733/154742504910672534362390528), (439328108313/19342813113834066795298816)), (110619/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550051341600135/9671406556917033397649408), (3294197348835/9671406556917033397649408)), (25933/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259223909700427/604462909807314587353088), (2881659361685/604462909807314587353088)), (90791/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888498442930999/75557863725914323419136), (4681265548543/75557863725914323419136)), (147583/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298068513027873/4722366482869645213696), (1754848709797/2361183241434822606848)), (55365/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811087185853757/295147905179352825856), (1205950112315/147573952589676412928)), (76161/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824380640514913/73786976294838206464), (753337664845/9223372036854775808)), (190505/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823673683424557/9223372036854775808), (3387923959089/4611686018427387904)), (53615/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199364885209613/144115188075855872), (1692652887989/288230376151711744)), (107319/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195393840316647/144115188075855872), (2959198793375/72057594037927936)), (188007/144115188075855872), by norm_num⟩
  | 4 => ⟨((746425025087551/18014398509481984), (8865829816591/36028797018963968)), (282411/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490761330367465/9007199254740992), (5530857433637/4503599627370496)), (353713/9007199254740992), by norm_num⟩
  | 2 => ⟨((557729756201039/1125899906842624), (2757723610115/562949953421312)), (354765/2251799813685248), by norm_num⟩
  | 1 => ⟨((1110234853492289/1125899906842624), (16469424275539/1125899906842624)), (534781/1125899906842624), by norm_num⟩
  | 0 => ⟨((547276457448593/562949953421312), (16315990777761/562949953421312)), (16877/17592186044416), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((547276457448593/562949953421312), (16315990777761/562949953421312)), (64380645819061989/67108864000000000000000000), by norm_num⟩
  | 1 => ⟨((531566451873327/562949953421312), (7930862751075/140737488355328)), (2162723/1125899906842624), by norm_num⟩
  | 2 => ⟨((1000289683665215/1125899906842624), (239639380929661/2251799813685248)), (8656117/2251799813685248), by norm_num⟩
  | 3 => ⟨((1751883425924859/2251799813685248), (212904183655257/1125899906842624)), (8611599/1125899906842624), by norm_num⟩
  | 4 => ⟨((1282433169595343/2251799813685248), (662551454865413/2251799813685248)), (33312747/2251799813685248), by norm_num⟩
  | 5 => ⟨((133855194054853/562949953421312), (754665629794589/2251799813685248)), (57547551/2251799813685248), by norm_num⟩
  | 6 => ⟨((-62804163022593/1125899906842624), (1435522482362935/9007199254740992)), (32969767/1125899906842624), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29841903/16777216), (-1411796879/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-30327925/16777216), (-717395095/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((252326212815113/4503599627370496), (1388624369676073/9007199254740992)), (104393261/4503599627370496), by norm_num⟩
  | 1 => ⟨((-11447263/67108864), (-503980881/1073741824)), (77/1073741824), by norm_num⟩
  | 2 => ⟨((557623185/2147483648), (1534381101/2147483648)), (237/2147483648), by norm_num⟩
  | 3 => ⟨((-282949383/1073741824), (-389288141/536870912)), (243/2147483648), by norm_num⟩
  | 4 => ⟨((430722873/2147483648), (18518695/33554432)), (187/2147483648), by norm_num⟩
  | 5 => ⟨((-524538181/4294967296), (-1443342911/4294967296)), (115/2147483648), by norm_num⟩
  | 6 => ⟨((266161377/4294967296), (1464763293/8589934592)), (235/8589934592), by norm_num⟩
  | 7 => ⟨((-463048163/17179869184), (-1274144203/17179869184)), (207/17179869184), by norm_num⟩
  | 8 => ⟨((352440131/34359738368), (484895077/17179869184)), (159/34359738368), by norm_num⟩
  | 9 => ⟨((-119223543/34359738368), (-82015219/8589934592)), (217/137438953472), by norm_num⟩
  | 10 => ⟨((290383001/274877906944), (399515479/137438953472)), (67/137438953472), by norm_num⟩
  | 11 => ⟨((-160741375/549755813888), (-884606429/1099511627776)), (75/549755813888), by norm_num⟩
  | 12 => ⟨((326253815/4398046511104), (897734707/4398046511104)), (77/2199023255552), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790810527653985/5070602400912917605986812821504), (99504659911/633825300114114700748351602688)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889589387146611/316912650057057350374175801344), (235620937989/79228162514264337593543950336)), (46193/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236275371089473/4951760157141521099596496896), (2120249743527/39614081257132168796771975168)), (51973/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890006694927957/2475880078570760549798248448), (2252349724367/2475880078570760549798248448)), (13807/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885836378305175/77371252455336267181195264), (562970564781/38685626227668133590597632)), (13809/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1550005165776067/9671406556917033397649408), (527660763175/2417851639229258349412352)), (3237/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629591878529573/302231454903657293676544), (230789529629/75557863725914323419136)), (90653/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944216832790341/37778931862957161709568), (374916668737/9444732965739290427392)), (36835/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298020341553375/4722366482869645213696), (281085759075/590295810358705651712)), (110533/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811054402042769/295147905179352825856), (3090621219733/590295810358705651712)), (76013/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57009365068169/2305843009213693952), (3861294242921/73786976294838206464)), (190099/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911791990126719/4611686018427387904), (2170615934779/4611686018427387904)), (3343/144115188075855872), by norm_num⟩
  | 6 => ⟨((797415547334439/576460752303423488), (2168914450935/576460752303423488)), (107033/576460752303423488), by norm_num⟩
  | 5 => ⟨((597659389446601/72057594037927936), (3791775007455/144115188075855872)), (46859/36028797018963968), by norm_num⟩
  | 4 => ⟨((746370651889649/18014398509481984), (5680019585189/36028797018963968)), (281409/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490632107917599/9007199254740992), (7086666531207/9007199254740992)), (176105/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115340316836597/2251799813685248), (441666494471/140737488355328)), (88221/562949953421312), by norm_num⟩
  | 1 => ⟨((1110080991382259/1125899906842624), (21100218464541/2251799813685248)), (531015/1125899906842624), by norm_num⟩
  | 0 => ⟨((2188688204264443/2251799813685248), (20901390162135/1125899906842624)), (1068809/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2188688204264443/2251799813685248), (20901390162135/1125899906842624)), (4077182774070357921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((531642350481251/562949953421312), (20315583038319/562949953421312)), (1058695/562949953421312), by norm_num⟩
  | 2 => ⟨((2005370915803741/2251799813685248), (76743051507499/1125899906842624)), (8304187/2251799813685248), by norm_num⟩
  | 3 => ⟨((1775448466526799/2251799813685248), (136689134218641/1125899906842624)), (7961433/1125899906842624), by norm_num⟩
  | 4 => ⟨((683338181514913/1125899906842624), (6735848371835/35184372088832)), (14487609/1125899906842624), by norm_num⟩
  | 5 => ⟨((746941170868417/2251799813685248), (523284868150985/2251799813685248)), (46265923/2251799813685248), by norm_num⟩
  | 6 => ⟨((252326212815113/4503599627370496), (1388624369676073/9007199254740992)), (104393261/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30327925/16777216), (-717395095/16777216)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨40,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile040Terms2
