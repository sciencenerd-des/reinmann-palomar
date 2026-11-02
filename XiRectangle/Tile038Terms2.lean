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
namespace Reinmann.XiRectangle.Tile038Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨38,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((9/16), (35673/2560)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((9/16), (35673/2560))
  have he : value ((9/16), (35673/2560))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-13082715/8388608), (-648194015/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((280622346285457/2251799813685248), (-381237695858783/2251799813685248)), (58138915/2251799813685248), by norm_num⟩
  | 1 => ⟨((-371003319/1073741824), (504024189/1073741824)), (39/536870912), by norm_num⟩
  | 2 => ⟨((514319809/1073741824), (-698725891/1073741824)), (55/536870912), by norm_num⟩
  | 3 => ⟨((-237666217/536870912), (322879921/536870912)), (103/1073741824), by norm_num⟩
  | 4 => ⟨((658950673/2147483648), (-223803307/536870912)), (145/2147483648), by norm_num⟩
  | 5 => ⟨((-365399841/2147483648), (124102905/536870912)), (163/4294967296), by norm_num⟩
  | 6 => ⟨((675402319/8589934592), (-458781753/4294967296)), (153/8589934592), by norm_num⟩
  | 7 => ⟨((-133758061/4294967296), (726864637/17179869184)), (123/17179869184), by norm_num⟩
  | 8 => ⟨((741712183/68719476736), (-251912087/17179869184)), (173/68719476736), by norm_num⟩
  | 9 => ⟨((-456991741/137438953472), (310421605/68719476736)), (27/34359738368), by norm_num⟩
  | 10 => ⟨((506820059/549755813888), (-688537153/549755813888)), (121/549755813888), by norm_num⟩
  | 11 => ⟨((-31936445/137438953472), (694192853/2199023255552)), (123/2199023255552), by norm_num⟩
  | 12 => ⟨((472248679/8796093022208), (-641570425/8796093022208)), (115/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790972119257815/5070602400912917605986812821504), (-609793003061/5070602400912917605986812821504)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444890569194761/158456325028528675187087900672), (-722271726917/316912650057057350374175801344)), (46171/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890634389321017/39614081257132168796771975168), (-1624886669901/39614081257132168796771975168)), (103895/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945232529219731/1237940039285380274899124224), (-1726167291823/2475880078570760549798248448)), (55199/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((443032774150021/38685626227668133590597632), (-862929108095/77371252455336267181195264)), (55205/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550434834503145/9671406556917033397649408), (-1617663753829/9671406556917033397649408)), (51761/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259559692157933/604462909807314587353088), (-707563769191/302231454903657293676544)), (90595/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889044513119887/75557863725914323419136), (-2298966953139/75557863725914323419136)), (147239/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298478436034855/4722366482869645213696), (-1723686995097/4722366482869645213696)), (110451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622738616995787/590295810358705651712), (-592298830055/147573952589676412928)), (151903/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1825086847649123/73786976294838206464), (-2960183243899/73786976294838206464)), (189929/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824469402711563/9223372036854775808), (-1664202265693/4611686018427387904)), (213739/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595716343353849/1152921504606846976), (-3326153825687/1152921504606846976)), (213827/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196093175439445/144115188075855872), (-2907854363193/144115188075855872)), (46799/36028797018963968), by norm_num⟩
  | 4 => ⟨((746951252549969/18014398509481984), (-68073837459/562949953421312)), (140495/18014398509481984), by norm_num⟩
  | 3 => ⟨((746041458910723/4503599627370496), (-5437069253315/9007199254740992)), (351581/9007199254740992), by norm_num⟩
  | 2 => ⟨((2233580165788025/4503599627370496), (-10847665894597/4503599627370496)), (704193/4503599627370496), by norm_num⟩
  | 1 => ⟨((2224506018323505/2251799813685248), (-16205459295139/2251799813685248)), (1058875/2251799813685248), by norm_num⟩
  | 0 => ⟨((2197354966245773/2251799813685248), (-32147610861933/2251799813685248)), (266015/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2197354966245773/2251799813685248), (-32147610861933/2251799813685248)), (1014766694188976199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1071883777026457/1125899906842624), (-15685167027525/562949953421312)), (263381/140737488355328), by norm_num⟩
  | 2 => ⟨((1019585068456921/1125899906842624), (-59730624275127/1125899906842624)), (8258673/2251799813685248), by norm_num⟩
  | 3 => ⟨((920140376642571/1125899906842624), (-216361871141153/2251799813685248)), (3958485/562949953421312), by norm_num⟩
  | 4 => ⟨((741589188197451/1125899906842624), (-353642970201861/2251799813685248)), (14461657/1125899906842624), by norm_num⟩
  | 5 => ⟨((230344048927325/562949953421312), (-232931721185755/1125899906842624)), (23593111/1125899906842624), by norm_num⟩
  | 6 => ⟨((280622346285457/2251799813685248), (-381237695858783/2251799813685248)), (58138915/2251799813685248), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13082715/8388608), (-648194015/16777216)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-53475111/33554432), (-331183619/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-381949185994885/9007199254740992), (-1789744960977343/9007199254740992)), (308537279/9007199254740992), by norm_num⟩
  | 1 => ⟨((258003123/2147483648), (302239019/536870912)), (105/1073741824), by norm_num⟩
  | 2 => ⟨((-365488945/2147483648), (-428153811/536870912)), (75/536870912), by norm_num⟩
  | 3 => ⟨((345169385/2147483648), (808700727/1073741824)), (143/1073741824), by norm_num⟩
  | 4 => ⟨((-244484627/2147483648), (-572805423/1073741824)), (51/536870912), by norm_num⟩
  | 5 => ⟨((277070843/4294967296), (649151987/2147483648)), (233/4294967296), by norm_num⟩
  | 6 => ⟨((-261666937/8589934592), (-76632753/536870912)), (111/4294967296), by norm_num⟩
  | 7 => ⟨((211816645/17179869184), (62033411/1073741824)), (181/17179869184), by norm_num⟩
  | 8 => ⟨((-300060873/68719476736), (-1406031103/68719476736)), (259/68719476736), by norm_num⟩
  | 9 => ⟨((188919215/137438953472), (110655169/17179869184)), (165/137438953472), by norm_num⟩
  | 10 => ⟨((-13381211/34359738368), (-1003231045/549755813888)), (189/549755813888), by norm_num⟩
  | 11 => ⟨((110288947/1099511627776), (258397053/549755813888)), (197/2199023255552), by norm_num⟩
  | 12 => ⟨((-26039343/1099511627776), (-976125305/8796093022208)), (47/2199023255552), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395474954429125/2535301200456458802993406410752), (-2320019201121/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889753371864103/316912650057057350374175801344), (-1373900683873/316912650057057350374175801344)), (92471/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945285877054459/19807040628566084398385987584), (-772708759753/9903520314283042199192993792)), (104047/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236299787949651/309485009821345068724781056), (-1641738750937/1237940039285380274899124224)), (55285/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110754006959153/9671406556917033397649408), (-820719000635/38685626227668133590597632)), (27/37778931862957161709568), by norm_num⟩
  | 13 => ⟨((775185895569805/4835703278458516698824704), (-3077057250897/9671406556917033397649408)), (12963/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1259504284665885/604462909807314587353088), (-2691786195989/604462909807314587353088)), (90765/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888954017711917/75557863725914323419136), (-34163709785/590295810358705651712)), (147539/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298410163820437/4722366482869645213696), (-3278668356663/4722366482869645213696)), (110693/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811322046092661/295147905179352825856), (-2253233376929/295147905179352825856)), (152267/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912483858416063/36893488147419103232), (-5630530805709/73786976294838206464)), (95215/36893488147419103232), by norm_num⟩
  | 7 => ⟨((912167020880803/4611686018427387904), (-6330838448441/9223372036854775808)), (107183/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595579311287969/1152921504606846976), (-3163227157481/576460752303423488)), (53633/288230376151711744), by norm_num⟩
  | 5 => ⟨((1195971395618797/144115188075855872), (-1382679446119/36028797018963968)), (187901/144115188075855872), by norm_num⟩
  | 4 => ⟨((746858044970361/18014398509481984), (-1035777902413/4503599627370496)), (282225/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491843362570229/9007199254740992), (-10340549035547/9007199254740992)), (176717/4503599627370496), by norm_num⟩
  | 2 => ⟨((558270379763585/1125899906842624), (-5157365595717/1125899906842624)), (177207/1125899906842624), by norm_num⟩
  | 1 => ⟨((555927365374417/562949953421312), (-15407647229555/1125899906842624)), (267039/562949953421312), by norm_num⟩
  | 0 => ⟨((1097784512362861/1125899906842624), (-15279033538179/562949953421312)), (134751/140737488355328), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1097784512362861/1125899906842624), (-15279033538179/562949953421312)), (514034271777105287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1069541824101635/1125899906842624), (-29794986712669/562949953421312)), (1080347/562949953421312), by norm_num⟩
  | 2 => ⟨((126606364122519/140737488355328), (-28303567878531/281474976710656)), (2166897/562949953421312), by norm_num⟩
  | 3 => ⟨((1799537409131087/2251799813685248), (-407386758160525/2251799813685248)), (8668861/1125899906842624), by norm_num⟩
  | 4 => ⟨((1364406772513897/2251799813685248), (-81391306060941/281474976710656)), (33984405/2251799813685248), by norm_num⟩
  | 5 => ⟨((319219091145899/1125899906842624), (-98632967760625/281474976710656)), (60837411/2251799813685248), by norm_num⟩
  | 6 => ⟨((-381949185994885/9007199254740992), (-1789744960977343/9007199254740992)), (308537279/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-53475111/33554432), (-331183619/8388608)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-13638485/8388608), (-1351460215/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-748815935777433/4503599627370496), (-473706883918549/4503599627370496)), (79477551/2251799813685248), by norm_num⟩
  | 1 => ⟨((1032045571/2147483648), (652880191/2147483648)), (221/2147483648), by norm_num⟩
  | 2 => ⟨((-745748843/1073741824), (-58970827/134217728)), (161/1073741824), by norm_num⟩
  | 3 => ⟨((179624283/268435456), (56815871/134217728)), (157/1073741824), by norm_num⟩
  | 4 => ⟨((-1038361909/2147483648), (-164218989/536870912)), (229/2147483648), by norm_num⟩
  | 5 => ⟨((1200500775/4294967296), (759446285/4294967296)), (267/4294967296), by norm_num⟩
  | 6 => ⟨((-1156631179/8589934592), (-731694031/8589934592)), (65/2147483648), by norm_num⟩
  | 7 => ⟨((955169741/17179869184), (151061983/4294967296)), (217/17179869184), by norm_num⟩
  | 8 => ⟨((-690198911/34359738368), (-436625289/34359738368)), (79/17179869184), by norm_num⟩
  | 9 => ⟨((221659049/34359738368), (560893069/137438953472)), (205/137438953472), by norm_num⟩
  | 10 => ⟨((-128135411/68719476736), (-324237897/274877906944)), (239/549755813888), by norm_num⟩
  | 11 => ⟨((538703961/1099511627776), (681576771/2199023255552)), (253/2199023255552), by norm_num⟩
  | 12 => ⟨((-1038036477/8796093022208), (-656670083/8796093022208)), (123/4398046511104), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581857936655173/10141204801825835211973625643008), (-3357535168959/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444863181380315/158456325028528675187087900672), (-3976411303775/633825300114114700748351602688)), (92591/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890510736952591/39614081257132168796771975168), (-2236400239305/19807040628566084398385987584)), (104191/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236291644686649/309485009821345068724781056), (-296972487873/154742504910672534362390528)), (110731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442999652658829/38685626227668133590597632), (-4750670221211/154742504910672534362390528)), (27691/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550310007648137/9671406556917033397649408), (-2226404094469/4835703278458516698824704)), (25969/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629724923877781/302231454903657293676544), (-1947631033555/302231454903657293676544)), (90927/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888864852532833/75557863725914323419136), (-6328028896319/75557863725914323419136)), (36955/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649171336676265/2361183241434822606848), (-74132364087/73786976294838206464)), (55461/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811275145858789/295147905179352825856), (-6521128869339/590295810358705651712)), (152611/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228106120770609/9223372036854775808), (-127306760173/1152921504606846976)), (190903/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824198387131137/9223372036854775808), (-9160891905797/9223372036854775808)), (214957/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398860271304829/288230376151711744), (-9154399160279/1152921504606846976)), (215197/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195847560058899/144115188075855872), (-1000349502107/18014398509481984)), (188567/144115188075855872), by norm_num⟩
  | 4 => ⟨((746762286944555/18014398509481984), (-5994795137769/18014398509481984)), (141695/18014398509481984), by norm_num⟩
  | 3 => ⟨((1491593911512369/9007199254740992), (-14961437521453/9007199254740992)), (22199/562949953421312), by norm_num⟩
  | 2 => ⟨((279069070483091/562949953421312), (-7461562330273/1125899906842624)), (356605/2251799813685248), by norm_num⟩
  | 1 => ⟨((555710324433927/562949953421312), (-11144474836709/562949953421312)), (538467/1125899906842624), by norm_num⟩
  | 0 => ⟨((137096011237739/140737488355328), (-44195224288923/1125899906842624)), (68201/70368744177664), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((137096011237739/140737488355328), (-44195224288923/1125899906842624)), (260166168481326081/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1066655230965399/1125899906842624), (-86103411913549/1125899906842624)), (138227/70368744177664), by norm_num⟩
  | 2 => ⟨((501971612810823/562949953421312), (-163145327863311/1125899906842624)), (4528783/1125899906842624), by norm_num⟩
  | 3 => ⟨((871556695496849/1125899906842624), (-18184192673875/70368744177664)), (9388919/1125899906842624), by norm_num⟩
  | 4 => ⟨((1198971355062695/2251799813685248), (-900886043218663/2251799813685248)), (38776641/2251799813685248), by norm_num⟩
  | 5 => ⟨((69492927789427/562949953421312), (-239838495729161/562949953421312)), (72320299/2251799813685248), by norm_num⟩
  | 6 => ⟨((-748815935777433/4503599627370496), (-473706883918549/4503599627370496)), (79477551/2251799813685248), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-13638485/8388608), (-1351460215/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-55574425/33554432), (-1376740595/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-422082539490645/2251799813685248), (323583503090481/9007199254740992)), (290670555/9007199254740992), by norm_num⟩
  | 1 => ⟨((592611447/1073741824), (-113579259/1073741824)), (103/1073741824), by norm_num⟩
  | 2 => ⟨((-436227061/536870912), (334427197/2147483648)), (153/1073741824), by norm_num⟩
  | 3 => ⟨((1712591949/2147483648), (-328233491/2147483648)), (303/2147483648), by norm_num⟩
  | 4 => ⟨((-630327811/1073741824), (241615871/2147483648)), (225/2147483648), by norm_num⟩
  | 5 => ⟨((1484769421/4294967296), (-284569275/4294967296)), (267/4294967296), by norm_num⟩
  | 6 => ⟨((-728635493/4294967296), (279298955/8589934592)), (33/1073741824), by norm_num⟩
  | 7 => ⟨((1225955855/17179869184), (-234965351/17179869184)), (7/536870912), by norm_num⟩
  | 8 => ⟨((-225609513/8589934592), (172960285/34359738368)), (167/34359738368), by norm_num⟩
  | 9 => ⟨((1180966123/137438953472), (-226342669/137438953472)), (55/34359738368), by norm_num⟩
  | 10 => ⟨((-695456537/274877906944), (266580871/549755813888)), (261/549755813888), by norm_num⟩
  | 11 => ⟨((1489257699/2199023255552), (-142714747/1099511627776)), (141/1099511627776), by norm_num⟩
  | 12 => ⟨((-365419035/2199023255552), (280143243/8796093022208)), (279/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197727290069707/1267650600228229401496703205376), (3845609315429/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222425396587407/79228162514264337593543950336), (4554221064759/633825300114114700748351602688)), (11581/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890454846470555/39614081257132168796771975168), (1280679853725/9903520314283042199192993792)), (52129/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472568397327665/618970019642690137449562112), (5441966016103/2475880078570760549798248448)), (110807/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885969417474485/77371252455336267181195264), (5440927086371/154742504910672534362390528)), (110845/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550253747592181/9671406556917033397649408), (637470658471/1208925819614629174706176)), (103957/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259400399994545/604462909807314587353088), (4461190718905/604462909807314587353088)), (91003/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236098010914587/9444732965739290427392), (7247365093015/75557863725914323419136)), (147953/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298281738704593/4722366482869645213696), (1358428173133/1180591620717411303424)), (111031/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101404120058151/36893488147419103232), (1867102953769/147573952589676412928)), (152773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824742625173009/73786976294838206464), (4665549984235/36893488147419103232)), (191125/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912038774252025/4611686018427387904), (5245708482293/4611686018427387904)), (215235/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595318742670955/1152921504606846976), (10483828623141/1152921504606846976)), (107755/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195738821638273/144115188075855872), (9164812875789/144115188075855872)), (188881/144115188075855872), by norm_num⟩
  | 4 => ⟨((746679048462997/18014398509481984), (3432536074629/9007199254740992)), (70985/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491379937082533/9007199254740992), (4283199419215/2251799813685248)), (356009/9007199254740992), by norm_num⟩
  | 2 => ⟨((279013381589867/562949953421312), (17087971047043/2251799813685248)), (178819/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111064689268257/1125899906842624), (25519882087981/1125899906842624)), (270269/562949953421312), by norm_num⟩
  | 0 => ⟨((1095969624890683/1125899906842624), (50591427898265/1125899906842624)), (1097451/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1095969624890683/1125899906842624), (50591427898265/1125899906842624)), (4186443333152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1064561706437529/1125899906842624), (24623267094779/281474976710656)), (2235181/1125899906842624), by norm_num⟩
  | 2 => ⟨((124743631235097/140737488355328), (93127238317283/562949953421312)), (2308943/562949953421312), by norm_num⟩
  | 3 => ⟨((106715922331305/140737488355328), (165087923770019/562949953421312)), (9714039/1125899906842624), by norm_num⟩
  | 4 => ⟨((1101046981159771/2251799813685248), (1001439503106539/2251799813685248)), (40857921/2251799813685248), by norm_num⟩
  | 5 => ⟨((46501330861209/1125899906842624), (1958667790997019/4503599627370496)), (152594787/4503599627370496), by norm_num⟩
  | 6 => ⟨((-422082539490645/2251799813685248), (323583503090481/9007199254740992)), (290670555/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55574425/33554432), (-1376740595/33554432)), (1/16777216), by norm_num⟩, -7, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-56542553/33554432), (-1400723963/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-258197817845883/2251799813685248), (328139306388443/2251799813685248)), (150359749/4503599627370496), by norm_num⟩
  | 1 => ⟨((184414753/536870912), (-117184819/268435456)), (217/2147483648), by norm_num⟩
  | 2 => ⟨((-552457227/1073741824), (702108689/1073741824)), (165/1073741824), by norm_num⟩
  | 3 => ⟨((551671315/1073741824), (-350554943/536870912)), (167/1073741824), by norm_num⟩
  | 4 => ⟨((-826329781/2147483648), (1050168757/2147483648)), (253/2147483648), by norm_num⟩
  | 5 => ⟨((495092559/2147483648), (-78650611/268435456)), (153/2147483648), by norm_num⟩
  | 6 => ⟨((-494388253/4294967296), (628309797/4294967296)), (155/4294967296), by norm_num⟩
  | 7 => ⟨((423158527/8589934592), (-537785125/8589934592)), (67/4294967296), by norm_num⟩
  | 8 => ⟨((-158458707/8589934592), (50345633/2147483648)), (203/34359738368), by norm_num⟩
  | 9 => ⟨((843910867/137438953472), (-268128067/34359738368)), (17/8589934592), by norm_num⟩
  | 10 => ⟨((-126406551/68719476736), (642591923/274877906944)), (41/68719476736), by norm_num⟩
  | 11 => ⟨((550807541/1099511627776), (-175003033/274877906944)), (45/274877906944), by norm_num⟩
  | 12 => ⟨((-68752997/549755813888), (87377039/549755813888)), (181/4398046511104), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790890368501753/5070602400912917605986812821504), (364319315911/1267650600228229401496703205376)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779363383512705/633825300114114700748351602688), (3451441090871/633825300114114700748351602688)), (23135/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890410363557887/39614081257132168796771975168), (1941140732225/19807040628566084398385987584)), (104129/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945113341353599/1237940039285380274899124224), (4124213379277/2475880078570760549798248448)), (55331/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442973082303147/38685626227668133590597632), (2061706953447/77371252455336267181195264)), (110691/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550210574175359/9671406556917033397649408), (3864851189973/9671406556917033397649408)), (103803/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629681524364829/302231454903657293676544), (3380895546475/604462909807314587353088)), (45429/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888724188774667/75557863725914323419136), (2746181574051/37778931862957161709568)), (36925/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324559377975425/1180591620717411303424), (1029469869915/1180591620717411303424)), (110825/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622406240928939/590295810358705651712), (353738828965/36893488147419103232)), (9529/36893488147419103232), by norm_num⟩
  | 8 => ⟨((228083715162941/9223372036854775808), (1767845691981/18446744073709551616)), (190701/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911998930578921/4611686018427387904), (7950640294909/9223372036854775808)), (13419/576460752303423488), by norm_num⟩
  | 6 => ⟨((1595241963196471/1152921504606846976), (993101300715/144115188075855872)), (214913/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195674905438297/144115188075855872), (6945152902501/144115188075855872)), (188283/144115188075855872), by norm_num⟩
  | 4 => ⟨((23332324070635/562949953421312), (1300577877011/4503599627370496)), (282893/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491279616881613/9007199254740992), (3245714089717/2251799813685248)), (354437/9007199254740992), by norm_num⟩
  | 2 => ⟨((278992551779617/562949953421312), (12948500171497/2251799813685248)), (177835/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110981995906555/1125899906842624), (19336956106537/1125899906842624)), (268297/562949953421312), by norm_num⟩
  | 0 => ⟨((547986039774315/562949953421312), (38331316020841/1125899906842624)), (1085581/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((547986039774315/562949953421312), (38331316020841/1125899906842624)), (4141162876609420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1065534779842511/1125899906842624), (74624843426813/1125899906842624)), (273421/140737488355328), by norm_num⟩
  | 2 => ⟨((1003459981594503/1125899906842624), (17655958053713/140737488355328)), (4430143/1125899906842624), by norm_num⟩
  | 3 => ⟨((109576906654451/140737488355328), (62943596445607/281474976710656)), (9008295/1125899906842624), by norm_num⟩
  | 4 => ⟨((313111297276163/562949953421312), (98014603966813/281474976710656)), (18056431/1125899906842624), by norm_num⟩
  | 5 => ⟨((211781646864313/1125899906842624), (872247477447507/2251799813685248)), (32661023/1125899906842624), by norm_num⟩
  | 6 => ⟨((-258197817845883/2251799813685248), (328139306388443/2251799813685248)), (150359749/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-56542553/33554432), (-1400723963/33554432)), (1/16777216), by norm_num⟩, -7, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-57463437/33554432), (-1423536933/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((21458185793277/9007199254740992), (1624813598975611/9007199254740992)), (258860597/9007199254740992), by norm_num⟩
  | 1 => ⟨((-15575869/2147483648), (-1179404607/2147483648)), (95/1073741824), by norm_num⟩
  | 2 => ⟨((23710541/2147483648), (1795361895/2147483648)), (291/2147483648), by norm_num⟩
  | 3 => ⟨((-24062425/2147483648), (-1822006525/2147483648)), (149/1073741824), by norm_num⟩
  | 4 => ⟨((2289331/268435456), (1386784937/2147483648)), (57/536870912), by norm_num⟩
  | 5 => ⟨((-22303743/4294967296), (-1688839143/4294967296)), (35/536870912), by norm_num⟩
  | 6 => ⟨((22634749/8589934592), (214237861/1073741824)), (287/8589934592), by norm_num⟩
  | 7 => ⟨((-19689143/17179869184), (-1490861657/17179869184)), (251/17179869184), by norm_num⟩
  | 8 => ⟨((14986009/34359738368), (567370221/17179869184)), (193/34359738368), by norm_num⟩
  | 9 => ⟨((-20277885/137438953472), (-1535441217/137438953472)), (263/137438953472), by norm_num⟩
  | 10 => ⟨((12347295/274877906944), (1869874095/549755813888)), (161/274877906944), by norm_num⟩
  | 11 => ⟨((-13669679/1099511627776), (-2070135869/2199023255552)), (359/2199023255552), by norm_num⟩
  | 12 => ⟨((3468137/1099511627776), (4103239/17179869184)), (367/8796093022208), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581744987501705/10141204801825835211973625643008), (2028935587103/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889662165900583/316912650057057350374175801344), (2402574601067/633825300114114700748351602688)), (23109/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945183313341545/19807040628566084398385987584), (675621151441/9903520314283042199192993792)), (104007/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890180462680209/2475880078570760549798248448), (717721937391/618970019642690137449562112)), (27631/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885923195367115/77371252455336267181195264), (717580734983/38685626227668133590597632)), (6909/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550167805847195/9671406556917033397649408), (84072742507/302231454903657293676544)), (12957/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629662962634507/302231454903657293676544), (2353436922737/604462909807314587353088)), (2835/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((236083052886527/9444732965739290427392), (1911605260507/37778931862957161709568)), (147459/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298193177229843/4722366482869645213696), (1433212122577/2361183241434822606848)), (110629/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202793259458369/73786976294838206464), (3939735424839/590295810358705651712)), (152171/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912297852959213/36893488147419103232), (4922273308327/73786976294838206464)), (190297/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455979057457527/2305843009213693952), (2767132232297/4611686018427387904)), (26775/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797581186991221/576460752303423488), (5530150387963/1152921504606846976)), (214345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597803779160693/72057594037927936), (4834256253543/144115188075855872)), (187715/144115188075855872), by norm_num⟩
  | 4 => ⟨((1493172296912427/36028797018963968), (1810535301843/9007199254740992)), (140949/18014398509481984), by norm_num⟩
  | 3 => ⟨((372791762539323/2251799813685248), (9036517824139/9007199254740992)), (22059/562949953421312), by norm_num⟩
  | 2 => ⟨((2231739155927321/4503599627370496), (18024627038395/4503599627370496)), (707605/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221721483914655/2251799813685248), (420564921545/35184372088832)), (1065707/2251799813685248), by norm_num⟩
  | 0 => ⟨((1095847407876883/1125899906842624), (26675291206259/1125899906842624)), (2148661/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1095847407876883/1125899906842624), (26675291206259/1125899906842624)), (8196491250045012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2131930134988993/2251799813685248), (103853099356641/2251799813685248)), (4284433/2251799813685248), by norm_num⟩
  | 2 => ⟨((503412937361359/562949953421312), (196649409760877/2251799813685248)), (8507919/2251799813685248), by norm_num⟩
  | 3 => ⟨((222939576670931/281474976710656), (175851967650865/1125899906842624)), (4175563/562949953421312), by norm_num⟩
  | 4 => ⟨((1357685453862597/2251799813685248), (278563754995063/1125899906842624)), (31675101/2251799813685248), by norm_num⟩
  | 5 => ⟨((340376333616785/1125899906842624), (167955408749761/562949953421312)), (53869705/2251799813685248), by norm_num⟩
  | 6 => ⟨((21458185793277/9007199254740992), (1624813598975611/9007199254740992)), (258860597/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57463437/33554432), (-1423536933/33554432)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨38,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile038Terms2
