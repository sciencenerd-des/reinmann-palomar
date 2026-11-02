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
namespace Reinmann.XiRectangle.Tile028Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨28,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (7473/640))
  have he : value ((7/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-325614239/134217728), (-2172602865/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((915307832467595/18014398509481984), (-1302886325147623/18014398509481984)), (50144363/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2420208143/17179869184), (1722511259/8589934592)), (67/8589934592), by norm_num⟩
  | 2 => ⟨((1677560451/8589934592), (-4775815291/17179869184)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((-3100790125/17179869184), (4413790539/17179869184)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((2149303933/17179869184), (-764851617/4294967296)), (31/4294967296), by norm_num⟩
  | 5 => ⟨((-1191827169/17179869184), (848247587/8589934592)), (139/34359738368), by norm_num⟩
  | 6 => ⟨((2202964379/68719476736), (-3135788925/68719476736)), (131/68719476736), by norm_num⟩
  | 7 => ⟨((-1745118341/137438953472), (4968144577/274877906944)), (105/137438953472), by norm_num⟩
  | 8 => ⟨((604811929/137438953472), (-1721827703/274877906944)), (37/137438953472), by norm_num⟩
  | 9 => ⟨((-2981146193/2199023255552), (1060871127/549755813888)), (23/274877906944), by norm_num⟩
  | 10 => ⟨((1653098463/4398046511104), (-1176543729/2199023255552)), (103/4398046511104), by norm_num⟩
  | 11 => ⟨((-3333354295/35184372088832), (4744831817/35184372088832)), (105/17592186044416), by norm_num⟩
  | 12 => ⟨((3080673509/140737488355328), (-4385155729/140737488355328)), (197/140737488355328), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580815611531029/10141204801825835211973625643008), (-1248395606369/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222278296469255/79228162514264337593543950336), (-1476554496175/633825300114114700748351602688)), (23087/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889131757571959/39614081257132168796771975168), (-830387015313/19807040628566084398385987584)), (25975/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944434416531951/1237940039285380274899124224), (-441033954329/618970019642690137449562112)), (27601/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770535232102487/154742504910672534362390528), (-1763644861675/154742504910672534362390528)), (6901/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1548939094878661/9671406556917033397649408), (-206611950113/1208925819614629174706176)), (25883/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78640706451649/37778931862957161709568), (-1445762400309/604462909807314587353088)), (11325/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((235864887432985/9444732965739290427392), (-2348386994327/75557863725914323419136)), (36813/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81055312758683/295147905179352825856), (-880217945551/2361183241434822606848)), (27615/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810274334397279/295147905179352825856), (-2419211845247/590295810358705651712)), (37979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((56948466958423/2305843009213693952), (-1510967492671/36893488147419103232)), (23743/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455348403144383/2305843009213693952), (-3396819436613/9223372036854775808)), (835/144115188075855872), by norm_num⟩
  | 6 => ⟨((1592643180196545/1152921504606846976), (-3393251154631/1152921504606846976)), (53463/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596703555321679/72057594037927936), (-1482542622161/72057594037927936)), (46805/144115188075855872), by norm_num⟩
  | 4 => ⟨((186234913485781/4503599627370496), (-4439620822923/36028797018963968)), (35129/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487064232884815/9007199254740992), (-1383885158975/2251799813685248)), (43955/4503599627370496), by norm_num⟩
  | 2 => ⟨((555893419289051/1125899906842624), (-11029232625573/4503599627370496)), (176087/4503599627370496), by norm_num⟩
  | 1 => ⟨((2209573301414775/2251799813685248), (-16439602778097/2251799813685248)), (264799/2251799813685248), by norm_num⟩
  | 0 => ⟨((2167796475682429/2251799813685248), (-32464466408109/2251799813685248)), (8317/35184372088832), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2167796475682429/2251799813685248), (-32464466408109/2251799813685248)), (31726837292420853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((2086458836104475/2251799813685248), (-62506760535905/2251799813685248)), (1040211/2251799813685248), by norm_num⟩
  | 2 => ⟨((241440388773259/281474976710656), (-115834260260433/2251799813685248)), (1985415/2251799813685248), by norm_num⟩
  | 3 => ⟨((1650841218984309/2251799813685248), (-99358987990221/1125899906842624)), (902579/562949953421312), by norm_num⟩
  | 4 => ⟨((596364712350769/1125899906842624), (-145684276065715/1125899906842624)), (2965403/1125899906842624), by norm_num⟩
  | 5 => ⟨((594061620952189/2251799813685248), (-617326359914899/4503599627370496)), (15635311/4503599627370496), by norm_num⟩
  | 6 => ⟨((915307832467595/18014398509481984), (-1302886325147623/18014398509481984)), (50144363/18014398509481984), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-325614239/134217728), (-2172602865/67108864)), (1/67108864), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-166367013/67108864), (-1110054185/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-35985137918677/4503599627370496), (-1503123826632361/18014398509481984)), (31383305/9007199254740992), by norm_num⟩
  | 1 => ⟨((12153813/536870912), (2030692331/8589934592)), (171/17179869184), by norm_num⟩
  | 2 => ⟨((-550949523/17179869184), (-2876692305/8589934592)), (61/4294967296), by norm_num⟩
  | 3 => ⟨((130079795/4294967296), (5433522017/17179869184)), (29/2147483648), by norm_num⟩
  | 4 => ⟨((-368543811/17179869184), (-3848581771/17179869184)), (331/34359738368), by norm_num⟩
  | 5 => ⟨((417665297/34359738368), (1090385323/8589934592)), (189/34359738368), by norm_num⟩
  | 6 => ⟨((-98611241/17179869184), (-4119058997/68719476736)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((638598135/274877906944), (3334335119/137438953472)), (147/137438953472), by norm_num⟩
  | 8 => ⟨((-452321189/549755813888), (-4723441377/549755813888)), (105/274877906944), by norm_num⟩
  | 9 => ⟨((142391381/549755813888), (1486946349/549755813888)), (267/2199023255552), by norm_num⟩
  | 10 => ⟨((-645480257/8796093022208), (-6740537981/8796093022208)), (305/8796093022208), by norm_num⟩
  | 11 => ⟨((665012101/35184372088832), (3472251301/17592186044416)), (79/8796093022208), by norm_num⟩
  | 12 => ⟨((-314020193/70368744177664), (-6558419147/140737488355328)), (75/35184372088832), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580746512481045/10141204801825835211973625643008), (-2170497704233/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889071142078483/316912650057057350374175801344), (-1283478326653/316912650057057350374175801344)), (11557/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889037048153537/39614081257132168796771975168), (-1443600908175/19807040628566084398385987584)), (26007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888768055406079/2475880078570760549798248448), (-766718980531/618970019642690137449562112)), (27637/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770434287125971/154742504910672534362390528), (-1533001615017/77371252455336267181195264)), (27643/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774422140667537/4835703278458516698824704), (-1436725545965/4835703278458516698824704)), (25921/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258168163914271/604462909807314587353088), (-314167888209/75557863725914323419136)), (11343/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1886783665695265/75557863725914323419136), (-255152867931/4722366482869645213696)), (36875/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324195784581973/1180591620717411303424), (-765078888077/1180591620717411303424)), (13833/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810204065964631/295147905179352825856), (-4205467071357/590295810358705651712)), (38055/590295810358705651712), by norm_num⟩
  | 8 => ⟨((113885910355193/4611686018427387904), (-656641995235/9223372036854775808)), (5949/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1821194219727915/9223372036854775808), (-1476174294979/2305843009213693952)), (53571/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592442579237101/1152921504606846976), (-720013661/140737488355328)), (26805/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193230229544565/144115188075855872), (-1288481832345/36028797018963968)), (46953/144115188075855872), by norm_num⟩
  | 4 => ⟨((1489611285361171/36028797018963968), (-7716649378241/36028797018963968)), (70517/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486724499835445/9007199254740992), (-4810466438649/4503599627370496)), (88299/9007199254740992), by norm_num⟩
  | 2 => ⟨((1111440091341923/2251799813685248), (-19167404901003/4503599627370496)), (88529/2251799813685248), by norm_num⟩
  | 1 => ⟨((2208498289670987/2251799813685248), (-14282784500979/1125899906842624)), (33343/281474976710656), by norm_num⟩
  | 0 => ⟨((1082754584055563/1125899906842624), (-14098164618111/562949953421312)), (538135/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1082754584055563/1125899906842624), (-14098164618111/562949953421312)), (2052822121627043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520278245513123/562949953421312), (-108463299618433/2251799813685248)), (1061981/2251799813685248), by norm_num⟩
  | 2 => ⟨((479534962483463/562949953421312), (-25060440490795/281474976710656)), (258159/281474976710656), by norm_num⟩
  | 3 => ⟨((808035158903115/1125899906842624), (-42694229984521/281474976710656)), (3886255/2251799813685248), by norm_num⟩
  | 4 => ⟨((138501668276457/281474976710656), (-490252303248277/2251799813685248)), (1689277/562949953421312), by norm_num⟩
  | 5 => ⟨((109617454507095/562949953421312), (-241231965518771/1125899906842624)), (2398005/562949953421312), by norm_num⟩
  | 6 => ⟨((-35985137918677/4503599627370496), (-1503123826632361/18014398509481984)), (31383305/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-166367013/67108864), (-1110054185/33554432)), (1/67108864), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-339446739/134217728), (-4529795503/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-248130337815779/4503599627370496), (-1038250990413723/18014398509481984)), (32885917/9007199254740992), by norm_num⟩
  | 1 => ⟨((2735858615/17179869184), (2861911145/17179869184)), (183/17179869184), by norm_num⟩
  | 2 => ⟨((-3953824237/17179869184), (-2067996787/8589934592)), (267/17179869184), by norm_num⟩
  | 3 => ⟨((3809340637/17179869184), (1992426503/8589934592)), (259/17179869184), by norm_num⟩
  | 4 => ⟨((-344075331/2147483648), (-2879426647/17179869184)), (189/17179869184), by norm_num⟩
  | 5 => ⟨((1591208991/17179869184), (416130673/4294967296)), (55/8589934592), by norm_num⟩
  | 6 => ⟨((-1533061843/34359738368), (-400924115/8589934592)), (107/34359738368), by norm_num⟩
  | 7 => ⟨((1266033901/68719476736), (165545677/8589934592)), (179/137438953472), by norm_num⟩
  | 8 => ⟨((-457413579/68719476736), (-956977099/137438953472)), (261/549755813888), by norm_num⟩
  | 9 => ⟨((587597907/274877906944), (2458684071/1099511627776)), (85/549755813888), by norm_num⟩
  | 10 => ⟨((-2717402233/4398046511104), (-177662775/274877906944)), (99/2199023255552), by norm_num⟩
  | 11 => ⟨((1428055031/8796093022208), (2987703083/17592186044416)), (105/8796093022208), by norm_num⟩
  | 12 => ⟨((-1375869977/35184372088832), (-719631051/17592186044416)), (51/17592186044416), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790340682085487/5070602400912917605986812821504), (-3039878687409/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222257730398715/79228162514264337593543950336), (-224677509751/39614081257132168796771975168)), (23139/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944473192120963/19807040628566084398385987584), (-2021648264745/19807040628566084398385987584)), (26037/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888671499567939/2475880078570760549798248448), (-2147446531313/1237940039285380274899124224)), (27671/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770337477961191/154742504910672534362390528), (-536705651453/19342813113834066795298816)), (27679/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774376626904227/4835703278458516698824704), (-4023966913443/9671406556917033397649408)), (6489/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258088246146915/604462909807314587353088), (-3519645991851/604462909807314587353088)), (355/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((1886653296082827/75557863725914323419136), (-5716941135983/75557863725914323419136)), (36935/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1296684921320201/4722366482869645213696), (-1071383395767/1180591620717411303424)), (13857/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810136184938761/295147905179352825856), (-5889080392789/590295810358705651712)), (38127/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822003794378337/73786976294838206464), (-7356060957479/73786976294838206464)), (47691/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821000635348065/9223372036854775808), (-8268300167833/9223372036854775808)), (53695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592247165807791/1152921504606846976), (-8259221703467/1152921504606846976)), (26875/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193057190986907/144115188075855872), (-902076925701/18014398509481984)), (11773/36028797018963968), by norm_num⟩
  | 4 => ⟨((1489347638568699/36028797018963968), (-1350567518699/4503599627370496)), (70761/36028797018963968), by norm_num⟩
  | 3 => ⟨((1486387818580955/9007199254740992), (-13470059462653/9007199254740992)), (44333/4503599627370496), by norm_num⟩
  | 2 => ⟨((2222185583162273/4503599627370496), (-6708372364971/1125899906842624)), (177975/4503599627370496), by norm_num⟩
  | 1 => ⟨((551850938932277/562949953421312), (-9996105504687/562949953421312)), (134291/1125899906842624), by norm_num⟩
  | 0 => ⟨((2163112296005279/2251799813685248), (-78910160400043/2251799813685248)), (543669/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2163112296005279/2251799813685248), (-78910160400043/2251799813685248)), (2073932656295012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2075152490605911/2251799813685248), (-37901135172787/562949953421312)), (541309/1125899906842624), by norm_num⟩
  | 2 => ⟨((1902155731818729/2251799813685248), (-139711593495307/1125899906842624)), (2141157/2251799813685248), by norm_num⟩
  | 3 => ⟨((1572128698629373/2251799813685248), (-472072529278169/2251799813685248)), (2074387/1125899906842624), by norm_num⟩
  | 4 => ⟨((7801870858231/17592186044416), (-329584702246761/1125899906842624)), (7532579/2251799813685248), by norm_num⟩
  | 5 => ⟨((249922965402525/2251799813685248), (-584663503963781/2251799813685248)), (22182393/4503599627370496), by norm_num⟩
  | 6 => ⟨((-248130337815779/4503599627370496), (-1038250990413723/18014398509481984)), (32885917/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-339446739/134217728), (-4529795503/134217728)), (1/67108864), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-345796421/134217728), (-4614529743/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-337165472557141/4503599627370496), (-60167959587387/4503599627370496)), (14642779/4503599627370496), by norm_num⟩
  | 1 => ⟨((3787090911/17179869184), (675815145/17179869184)), (83/8589934592), by norm_num⟩
  | 2 => ⟨((-696928631/2147483648), (-248737057/4294967296)), (123/8589934592), by norm_num⟩
  | 3 => ⟨((5472170205/17179869184), (122065181/2147483648)), (61/4294967296), by norm_num⟩
  | 4 => ⟨((-4028117813/17179869184), (-359413477/8589934592)), (181/17179869184), by norm_num⟩
  | 5 => ⟨((593027355/4294967296), (846616841/34359738368)), (215/34359738368), by norm_num⟩
  | 6 => ⟨((-4656354293/68719476736), (-830937209/68719476736)), (213/68719476736), by norm_num⟩
  | 7 => ⟨((1958621583/68719476736), (174760279/34359738368)), (181/137438953472), by norm_num⟩
  | 8 => ⟨((-2883520867/274877906944), (-1029141955/549755813888)), (67/137438953472), by norm_num⟩
  | 9 => ⟨((3773489439/1099511627776), (673387931/1099511627776)), (177/1099511627776), by norm_num⟩
  | 10 => ⟨((-1111080939/1099511627776), (-793099869/4398046511104)), (105/2199023255552), by norm_num⟩
  | 11 => ⟨((4758560037/17592186044416), (849176061/17592186044416)), (227/17592186044416), by norm_num⟩
  | 12 => ⟨((-2335214943/35184372088832), (-833449031/70368744177664)), (225/70368744177664), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580619739154115/10141204801825835211973625643008), (-965560635639/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888992357708769/316912650057057350374175801344), (-1141744553505/158456325028528675187087900672)), (23163/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944429700337273/19807040628566084398385987584), (-2568338390755/19807040628566084398385987584)), (13033/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472144697597217/618970019642690137449562112), (-5456281853987/2475880078570760549798248448)), (3463/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770244443853247/154742504910672534362390528), (-170458288079/4835703278458516698824704)), (27713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548665689388999/9671406556917033397649408), (-2556015674971/4835703278458516698824704)), (25991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258011282666839/604462909807314587353088), (-4471310568507/604462909807314587353088)), (711/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((943263792489769/37778931862957161709568), (-7262661469735/75557863725914323419136)), (18495/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296590073926469/4722366482869645213696), (-2722090543741/2361183241434822606848)), (27759/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202517629927087/73786976294838206464), (-935147038767/73786976294838206464)), (9549/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455459565164245/18446744073709551616), (-9344614360581/73786976294838206464)), (47785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910406264501175/4611686018427387904), (-164113578075/144115188075855872)), (13453/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1592056713911811/1152921504606846976), (-10491498619935/1152921504606846976)), (26941/576460752303423488), by norm_num⟩
  | 5 => ⟨((596443957252603/72057594037927936), (-4583414846227/72057594037927936)), (5903/18014398509481984), by norm_num⟩
  | 4 => ⟨((372272120212467/9007199254740992), (-6861903271749/18014398509481984)), (4437/2251799813685248), by norm_num⟩
  | 3 => ⟨((743027369597161/4503599627370496), (-8554274226389/4503599627370496)), (89013/9007199254740992), by norm_num⟩
  | 2 => ⟨((555373049823821/1125899906842624), (-17039347527269/2251799813685248)), (89423/2251799813685248), by norm_num⟩
  | 1 => ⟨((1103148108030853/1125899906842624), (-793325543803/35184372088832)), (33791/281474976710656), by norm_num⟩
  | 0 => ⟨((1080315469985787/1125899906842624), (-12521203632689/281474976710656)), (274461/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1080315469985787/1125899906842624), (-12521203632689/281474976710656)), (1046985630515670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1034348629897181/1125899906842624), (-96114049961473/1125899906842624)), (551117/1125899906842624), by norm_num⟩
  | 2 => ⟨((471018414303161/562949953421312), (-353194578975713/2251799813685248)), (2213403/2251799813685248), by norm_num⟩
  | 3 => ⟨((760499915305423/1125899906842624), (-591033535107545/2251799813685248)), (4398239/2251799813685248), by norm_num⟩
  | 4 => ⟨((218061107514933/562949953421312), (-199609641434485/562949953421312)), (8250493/2251799813685248), by norm_num⟩
  | 5 => ⟨((27379477021709/1125899906842624), (-154639321727723/562949953421312)), (12242615/2251799813685248), by norm_num⟩
  | 6 => ⟨((-337165472557141/4503599627370496), (-60167959587387/4503599627370496)), (14642779/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-345796421/134217728), (-4614529743/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-87955083/33554432), (-4694916681/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-1194750274130875/18014398509481984), (8388962656301/281474976710656)), (58782831/18014398509481984), by norm_num⟩
  | 1 => ⟨((1706672647/8589934592), (-1533879771/17179869184)), (169/17179869184), by norm_num⟩
  | 2 => ⟨((-5112734329/17179869184), (2297546567/17179869184)), (255/17179869184), by norm_num⟩
  | 3 => ⟨((2552730539/8589934592), (-2294278133/17179869184)), (257/17179869184), by norm_num⟩
  | 4 => ⟨((-3823648631/17179869184), (859130381/8589934592)), (97/8589934592), by norm_num⟩
  | 5 => ⟨((2290925521/17179869184), (-257372461/4294967296)), (235/34359738368), by norm_num⟩
  | 6 => ⟨((-4575333013/68719476736), (1028025317/34359738368)), (59/17179869184), by norm_num⟩
  | 7 => ⟨((3916135077/137438953472), (-1759822069/137438953472)), (51/34359738368), by norm_num⟩
  | 8 => ⟨((-5865846119/549755813888), (658994471/137438953472)), (77/137438953472), by norm_num⟩
  | 9 => ⟨((3905001007/1099511627776), (-1754818671/1099511627776)), (207/1099511627776), by norm_num⟩
  | 10 => ⟨((-2339667509/2199023255552), (2102786771/4398046511104)), (125/2199023255552), by norm_num⟩
  | 11 => ⟨((318591703/1099511627776), (-2290685889/17592186044416)), (137/8796093022208), by norm_num⟩
  | 12 => ⟨((-1272553929/17592186044416), (2287427215/70368744177664)), (69/17592186044416), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790280637907115/5070602400912917605986812821504), (3542135478457/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((888958681937847/316912650057057350374175801344), (2094075676297/316912650057057350374175801344)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118048984155593/2475880078570760549798248448), (2355290758581/19807040628566084398385987584)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1888498560090945/2475880078570760549798248448), (625456567471/309485009821345068724781056)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770164384730035/154742504910672534362390528), (5002145008459/154742504910672534362390528)), (27699/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548590815711321/9671406556917033397649408), (4687909608677/9671406556917033397649408)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1257945949811217/604462909807314587353088), (4100320037357/604462909807314587353088)), (22739/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943210879659593/37778931862957161709568), (832502427553/9444732965739290427392)), (4621/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296511002089493/4722366482869645213696), (609422607/576460752303423488)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620032798380229/590295810358705651712), (214383536879/18446744073709551616)), (38169/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227712960313759/9223372036854775808), (4284475065613/36893488147419103232)), (11937/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1820662121356873/9223372036854775808), (2407821521883/2305843009213693952)), (53767/9223372036854775808), by norm_num⟩
  | 6 => ⟨((397976886222715/288230376151711744), (4810157753721/576460752303423488)), (53831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149094847731617/18014398509481984), (8405445074945/144115188075855872)), (47173/144115188075855872), by norm_num⟩
  | 4 => ⟨((744448777166625/18014398509481984), (3145883224865/9007199254740992)), (35451/18014398509481984), by norm_num⟩
  | 3 => ⟨((742910457417159/4503599627370496), (1960795844513/1125899906842624)), (44439/4503599627370496), by norm_num⟩
  | 2 => ⟨((555259744990085/1125899906842624), (3905478871935/562949953421312)), (44627/1125899906842624), by norm_num⟩
  | 1 => ⟨((275706526143469/281474976710656), (23272174913377/1125899906842624)), (134825/1125899906842624), by norm_num⟩
  | 0 => ⟨((2159484710493565/2251799813685248), (91808273001665/2251799813685248)), (546883/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2159484710493565/2251799813685248), (91808273001665/2251799813685248)), (2086193093306731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2067211049389751/2251799813685248), (44022244037637/562949953421312)), (1093521/2251799813685248), by norm_num⟩
  | 2 => ⟨((1883983722449279/2251799813685248), (80827139908677/562949953421312)), (544697/562949953421312), by norm_num⟩
  | 3 => ⟨((1529827927324933/2251799813685248), (540996637426183/2251799813685248)), (533931/281474976710656), by norm_num⟩
  | 4 => ⟨((909359754393819/2251799813685248), (735084672708069/2251799813685248)), (982039/281474976710656), by norm_num⟩
  | 5 => ⟨((15908701404047/281474976710656), (593708564473579/2251799813685248)), (1434327/281474976710656), by norm_num⟩
  | 6 => ⟨((-1194750274130875/18014398509481984), (8388962656301/281474976710656)), (58782831/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-87955083/33554432), (-4694916681/134217728)), (1/67108864), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-178775137/67108864), (-1192845177/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-686520742759811/18014398509481984), (1050695977467925/18014398509481984)), (57004979/18014398509481984), by norm_num⟩
  | 1 => ⟨((996650603/8589934592), (-762669439/4294967296)), (167/17179869184), by norm_num⟩
  | 2 => ⟨((-3034325123/17179869184), (4643928439/17179869184)), (257/17179869184), by norm_num⟩
  | 3 => ⟨((3079356973/17179869184), (-4712848111/17179869184)), (263/17179869184), by norm_num⟩
  | 4 => ⟨((-1171896425/8589934592), (3587092955/17179869184)), (101/8589934592), by norm_num⟩
  | 5 => ⟨((5574789/67108864), (-4368393995/34359738368)), (31/4294967296), by norm_num⟩
  | 6 => ⟨((-724162995/17179869184), (69269133/1073741824)), (127/34359738368), by norm_num⟩
  | 7 => ⟨((2519691985/137438953472), (-964075107/34359738368)), (223/137438953472), by norm_num⟩
  | 8 => ⟨((-239726837/34359738368), (2935148295/274877906944)), (171/274877906944), by norm_num⟩
  | 9 => ⟨((2595035499/1099511627776), (-3971611041/1099511627776)), (233/1099511627776), by norm_num⟩
  | 10 => ⟨((-3160257521/4398046511104), (4836663571/4398046511104)), (143/2199023255552), by norm_num⟩
  | 11 => ⟨((874679539/4398046511104), (-1338666433/4398046511104)), (5/274877906944), by norm_num⟩
  | 12 => ⟨((-443830247/8796093022208), (2717066661/35184372088832)), (41/8796093022208), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395126416376533/2535301200456458802993406410752), (175002237673/633825300114114700748351602688)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1777855142119891/633825300114114700748351602688), (413809226741/79228162514264337593543950336)), (23133/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118044622375581/2475880078570760549798248448), (3723417009511/39614081257132168796771975168)), (26029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59013271552241/77371252455336267181195264), (3955054797049/2475880078570760549798248448)), (13831/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885045414414299/77371252455336267181195264), (988461240417/38685626227668133590597632)), (27669/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774261095488129/4835703278458516698824704), (3705444612933/9671406556917033397649408)), (25947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314471559201617/151115727451828646838272), (3240979460343/604462909807314587353088)), (22711/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886325350655133/75557863725914323419136), (2632092013007/37778931862957161709568)), (18459/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1296439241836011/4722366482869645213696), (3946032354735/4722366482869645213696)), (27701/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1619935014549211/590295810358705651712), (5422374624367/590295810358705651712)), (38107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1821582780521849/73786976294838206464), (6772841707483/73786976294838206464)), (47663/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1820527929138259/9223372036854775808), (475775194803/576460752303423488)), (53661/9223372036854775808), by norm_num⟩
  | 6 => ⟨((795887813006819/576460752303423488), (1900901552157/288230376151711744)), (53711/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1192645903744157/144115188075855872), (1660817423521/36028797018963968)), (23527/72057594037927936), by norm_num⟩
  | 4 => ⟨((372183330628017/9007199254740992), (2486290000975/9007199254740992)), (70693/36028797018963968), by norm_num⟩
  | 3 => ⟨((1485624487405187/9007199254740992), (12396957628151/9007199254740992)), (88565/9007199254740992), by norm_num⟩
  | 2 => ⟨((2220672564484319/4503599627370496), (12345340062473/2251799813685248)), (44431/1125899906842624), by norm_num⟩
  | 1 => ⟨((2205168169130599/2251799813685248), (18389389103247/1125899906842624)), (268079/2251799813685248), by norm_num⟩
  | 0 => ⟨((2158775884092749/2251799813685248), (72533654371925/2251799813685248)), (271079/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2158775884092749/2251799813685248), (72533654371925/2251799813685248)), (1034084324363326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((258407305926627/281474976710656), (139074444265957/2251799813685248)), (537225/1125899906842624), by norm_num⟩
  | 2 => ⟨((1889251327537073/2251799813685248), (255353800085407/2251799813685248)), (263189/281474976710656), by norm_num⟩
  | 3 => ⟨((1556117463944477/2251799813685248), (214240849861987/1125899906842624)), (4010563/2251799813685248), by norm_num⟩
  | 4 => ⟨((248457365192261/562949953421312), (296104410289417/1125899906842624)), (7069333/2251799813685248), by norm_num⟩
  | 5 => ⟨((282878480604649/2251799813685248), (16335670949789/70368744177664)), (155601/35184372088832), by norm_num⟩
  | 6 => ⟨((-686520742759811/18014398509481984), (1050695977467925/18014398509481984)), (57004979/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-178775137/67108864), (-1192845177/33554432)), (1/67108864), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨28,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile028Terms2
