/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile018Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5217/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5217/640))
  have he : value ((3/4), (5217/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1116391677/536870912), (-12133782039/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-230745604573641/2251799813685248), (644789931239557/9007199254740992)), (3188567/4503599627370496), by norm_num⟩
  | 1 => ⟨((19524006987/68719476736), (-3409838279/17179869184)), (137/68719476736), by norm_num⟩
  | 2 => ⟨((-13533010397/34359738368), (9454079157/34359738368)), (97/34359738368), by norm_num⟩
  | 3 => ⟨((12507157335/34359738368), (-8737424417/34359738368)), (91/34359738368), by norm_num⟩
  | 4 => ⟨((-17338601687/68719476736), (1514080275/8589934592)), (129/68719476736), by norm_num⟩
  | 5 => ⟨((19229124599/137438953472), (-839584379/8589934592)), (145/137438953472), by norm_num⟩
  | 6 => ⟨((-4442871167/68719476736), (6207525815/137438953472)), (17/34359738368), by norm_num⟩
  | 7 => ⟨((7039002567/274877906944), (-4917404591/274877906944)), (55/274877906944), by norm_num⟩
  | 8 => ⟨((-19516259133/2199023255552), (426060641/68719476736)), (155/2199023255552), by norm_num⟩
  | 9 => ⟨((12024568883/4398046511104), (-8400291045/4398046511104)), (97/4398046511104), by norm_num⟩
  | 10 => ⟨((-6667836815/8796093022208), (4658110443/8796093022208)), (109/17592186044416), by norm_num⟩
  | 11 => ⟨((13445213931/70368744177664), (-9392745077/70368744177664)), (7/4398046511104), by norm_num⟩
  | 12 => ⟨((-12426016171/281474976710656), (8680739691/281474976710656)), (53/140737488355328), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326325/10141204801825835211973625643008), (412245808641/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889376748759579/316912650057057350374175801344), (15245862463/2475880078570760549798248448)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944862130621727/19807040628566084398385987584), (4389991879099/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889497708179681/2475880078570760549798248448), (1165843722435/618970019642690137449562112)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442790841294477/38685626227668133590597632), (2331129791783/77371252455336267181195264)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549527181660551/9671406556917033397649408), (4369683539859/9671406556917033397649408)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258765091680865/604462909807314587353088), (955572123629/151115727451828646838272)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943876265116469/37778931862957161709568), (3104499067133/37778931862957161709568)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324377196808581/1180591620717411303424), (4654805976285/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621404276306839/590295810358705651712), (6397202317977/590295810358705651712)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455854328537411/18446744073709551616), (3995885281707/36893488147419103232)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822588971477269/9223372036854775808), (4492118694047/4611686018427387904)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593833161236617/1152921504606846976), (8976110466589/1152921504606846976)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194442305512703/144115188075855872), (1961239740277/36028797018963968)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((46606876623503/1125899906842624), (5874587892383/18014398509481984)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488969143350811/9007199254740992), (1831817347221/1125899906842624)), (11097/9007199254740992), by norm_num⟩
  | 2 => ⟨((556830174489247/1125899906842624), (14606699833277/2251799813685248)), (5571/1125899906842624), by norm_num⟩
  | 1 => ⟨((553759433905571/562949953421312), (21790654001145/1125899906842624)), (16821/1125899906842624), by norm_num⟩
  | 0 => ⟨((68065823709943/70368744177664), (43104937968937/1125899906842624)), (34081/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((68065823709943/70368744177664), (43104937968937/1125899906842624)), (130008701804732921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525881023969369/562949953421312), (83388531175549/1125899906842624)), (34271/562949953421312), by norm_num⟩
  | 2 => ⟨((976329913229421/1125899906842624), (77897592664121/562949953421312)), (34553/281474976710656), by norm_num⟩
  | 3 => ⟨((103133941353207/140737488355328), (135098598772995/562949953421312)), (277953/1125899906842624), by norm_num⟩
  | 4 => ⟨((1079556897951201/2251799813685248), (792013620568611/2251799813685248)), (1081565/2251799813685248), by norm_num⟩
  | 5 => ⟨((29873743520471/281474976710656), (47463353656027/140737488355328)), (3595747/4503599627370496), by norm_num⟩
  | 6 => ⟨((-230745604573641/2251799813685248), (644789931239557/9007199254740992)), (3188567/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/536870912), (-12133782039/536870912)), (1/536870912), by norm_num⟩, -4, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-570401187/268435456), (-6199547901/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-121048853601835/2251799813685248), (480368412055805/4503599627370496)), (1495401/2251799813685248), by norm_num⟩
  | 1 => ⟨((5233111989/34359738368), (-5191750317/17179869184)), (131/68719476736), by norm_num⟩
  | 2 => ⟨((-7413261359/34359738368), (14709336277/34359738368)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((3500558501/17179869184), (-868222663/2147483648)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((-9917829057/68719476736), (4919720069/17179869184)), (133/68719476736), by norm_num⟩
  | 5 => ⟨((2809932563/34359738368), (-11150893239/68719476736)), (153/137438953472), by norm_num⟩
  | 6 => ⟨((-10614851245/274877906944), (21061906349/274877906944)), (147/274877906944), by norm_num⟩
  | 7 => ⟨((268519091/17179869184), (-8524696303/274877906944)), (121/549755813888), by norm_num⟩
  | 8 => ⟨((-3043087487/549755813888), (3019035415/274877906944)), (87/1099511627776), by norm_num⟩
  | 9 => ⟨((7663747623/4398046511104), (-7603174599/2199023255552)), (7/274877906944), by norm_num⟩
  | 10 => ⟨((-8685212813/17592186044416), (17233132585/17592186044416)), (129/17592186044416), by norm_num⟩
  | 11 => ⟨((8948022123/70368744177664), (-277415575/1099511627776)), (135/70368744177664), by norm_num⟩
  | 12 => ⟨((-4225275947/140737488355328), (16767520191/281474976710656)), (129/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (2654234817779/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((111167892518065/39614081257132168796771975168), (1570444100665/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944824409523673/19807040628566084398385987584), (1766417263509/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944708889968499/1237940039285380274899124224), (3752822082227/2475880078570760549798248448)), (1729/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771083694489231/154742504910672534362390528), (937976461729/38685626227668133590597632)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549452763879115/9671406556917033397649408), (3516438452021/9671406556917033397649408)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258700249429261/604462909807314587353088), (1537955307005/302231454903657293676544)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887647673638275/75557863725914323419136), (2498265420281/37778931862957161709568)), (2307/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297430592457933/4722366482869645213696), (3745802738461/4722366482869645213696)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405324371306981/147573952589676412928), (5147887241209/590295810358705651712)), (4763/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823284914141727/73786976294838206464), (6430973493693/73786976294838206464)), (5957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911220758283179/4611686018427387904), (7229505346867/9223372036854775808)), (3353/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398421893028327/288230376151711744), (7222834767181/1152921504606846976)), (839/144115188075855872), by norm_num⟩
  | 5 => ⟨((1194317009802569/144115188075855872), (6312481810215/144115188075855872)), (735/18014398509481984), by norm_num⟩
  | 4 => ⟨((745618143673507/18014398509481984), (9453739968615/36028797018963968)), (69/281474976710656), by norm_num⟩
  | 3 => ⟨((186093340873239/1125899906842624), (5895493858737/4503599627370496)), (1383/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113448819194353/2251799813685248), (23503543927109/4503599627370496)), (22197/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214457247269225/2251799813685248), (35059692753585/2251799813685248)), (33471/2251799813685248), by norm_num⟩
  | 0 => ⟨((2177159799715077/2251799813685248), (34669812789163/1125899906842624)), (67647/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177159799715077/2251799813685248), (34669812789163/1125899906842624)), (258052834517668967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2102858691541721/2251799813685248), (67041237155697/1125899906842624)), (2109/35184372088832), by norm_num⟩
  | 2 => ⟨((1955785119045525/2251799813685248), (250427675475903/2251799813685248)), (67043/562949953421312), by norm_num⟩
  | 3 => ⟨((1670832988070205/2251799813685248), (108753610804187/562949953421312)), (525487/2251799813685248), by norm_num⟩
  | 4 => ⟨((577858940301919/1125899906842624), (645560477975181/2251799813685248)), (982855/2251799813685248), by norm_num⟩
  | 5 => ⟨((408089335134979/2251799813685248), (662657295619941/2251799813685248)), (3144855/4503599627370496), by norm_num⟩
  | 6 => ⟨((-121048853601835/2251799813685248), (480368412055805/4503599627370496)), (1495401/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-6199547901/268435456)), (1/536870912), by norm_num⟩, -4, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2327634783/1073741824), (-25298480543/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-926470548601/9007199254740992), (515353488341293/4503599627370496)), (10380205/18014398509481984), by norm_num⟩
  | 1 => ⟨((20430331/68719476736), (-177569767/536870912)), (117/68719476736), by norm_num⟩
  | 2 => ⟨((-14762813/34359738368), (16423764467/34359738368)), (171/68719476736), by norm_num⟩
  | 3 => ⟨((28446679/68719476736), (-31647189983/68719476736)), (167/68719476736), by norm_num⟩
  | 4 => ⟨((-20555369/68719476736), (5717009009/17179869184)), (123/68719476736), by norm_num⟩
  | 5 => ⟨((23765063/137438953472), (-26438850207/137438953472)), (9/8589934592), by norm_num⟩
  | 6 => ⟨((-11448311/137438953472), (25472701983/274877906944)), (141/274877906944), by norm_num⟩
  | 7 => ⟨((4727125/137438953472), (-10517939773/274877906944)), (59/274877906944), by norm_num⟩
  | 8 => ⟨((-27326297/2199023255552), (30400756071/2199023255552)), (173/2199023255552), by norm_num⟩
  | 9 => ⟨((17551813/4398046511104), (-19526552615/4398046511104)), (113/4398046511104), by norm_num⟩
  | 10 => ⟨((-10146253/8796093022208), (22575598483/17592186044416)), (33/4398046511104), by norm_num⟩
  | 11 => ⟨((10664161/35184372088832), (-11863976777/35184372088832)), (141/70368744177664), by norm_num⟩
  | 12 => ⟨((-20548927/281474976710656), (11430434471/140737488355328)), (69/140737488355328), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290011/2535301200456458802993406410752), (2047308472887/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778622341953443/633825300114114700748351602688), (605627656041/158456325028528675187087900672)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((59049281971711/1237940039285380274899124224), (2724805392901/39614081257132168796771975168)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889341671216951/2475880078570760549798248448), (1447232594437/1237940039285380274899124224)), (3455/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885503890956995/77371252455336267181195264), (1446872396035/77371252455336267181195264)), (3455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774690902058973/4835703278458516698824704), (2712120530715/9671406556917033397649408)), (405/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((629319183887463/302231454903657293676544), (593085122111/151115727451828646838272)), (709/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887547505905867/75557863725914323419136), (3853619465053/75557863725914323419136)), (4609/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297355807569781/4722366482869645213696), (1444480249881/2361183241434822606848)), (1729/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621195209424717/590295810358705651712), (992570928857/147573952589676412928)), (1189/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911578949265399/36893488147419103232), (1239950207403/18446744073709551616)), (1487/18446744073709551616), by norm_num⟩
  | 7 => ⟨((455574940619545/2305843009213693952), (696947450847/1152921504606846976)), (6695/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593547238723555/1152921504606846976), (5570338199547/1152921504606846976)), (1675/288230376151711744), by norm_num⟩
  | 5 => ⟨((298548953270945/36028797018963968), (1217038709875/36028797018963968)), (5867/144115188075855872), by norm_num⟩
  | 4 => ⟨((372764418513209/9007199254740992), (7290463824313/36028797018963968)), (8811/36028797018963968), by norm_num⟩
  | 3 => ⟨((744264505023035/4503599627370496), (9092515896647/9007199254740992)), (1379/1125899906842624), by norm_num⟩
  | 2 => ⟨((1113239389956691/2251799813685248), (18123463516861/4503599627370496)), (5529/1125899906842624), by norm_num⟩
  | 1 => ⟨((2213870141026719/2251799813685248), (6757926447367/562949953421312)), (16655/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088074388080443/1125899906842624), (6681504501913/281474976710656)), (33583/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1088074388080443/1125899906842624), (6681504501913/281474976710656)), (128108982566451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2101770480248329/2251799813685248), (103312543194189/2251799813685248)), (133009/2251799813685248), by norm_num⟩
  | 2 => ⟨((1956997084412233/2251799813685248), (96429199525317/1125899906842624)), (65125/562949953421312), by norm_num⟩
  | 3 => ⟨((842135966808401/1125899906842624), (335219252042497/2251799813685248)), (248707/1125899906842624), by norm_num⟩
  | 4 => ⟨((1209876643062091/2251799813685248), (501465871337099/2251799813685248)), (892197/2251799813685248), by norm_num⟩
  | 5 => ⟨((538384213349427/2251799813685248), (1077736735452703/4503599627370496)), (169515/281474976710656), by norm_num⟩
  | 6 => ⟨((-926470548601/9007199254740992), (515353488341293/4503599627370496)), (10380205/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2327634783/1073741824), (-25298480543/1073741824)), (1/536870912), by norm_num⟩, -4, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-592793865/268435456), (-12885856641/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((210711768737633/4503599627370496), (895546213169831/9007199254740992)), (4225561/9007199254740992), by norm_num⟩
  | 1 => ⟨((-9466979145/68719476736), (-20117806837/68719476736)), (97/68719476736), by norm_num⟩
  | 2 => ⟨((3484367801/17179869184), (1851114207/4294967296)), (37/17179869184), by norm_num⟩
  | 3 => ⟨((-6839672247/34359738368), (-908415471/2147483648)), (37/17179869184), by norm_num⟩
  | 4 => ⟨((314671837/2147483648), (21398191377/68719476736)), (111/68719476736), by norm_num⟩
  | 5 => ⟨((-370612809/4294967296), (-12601133755/68719476736)), (67/68719476736), by norm_num⟩
  | 6 => ⟨((5819982939/137438953472), (6183878235/68719476736)), (67/137438953472), by norm_num⟩
  | 7 => ⟨((-9792334071/549755813888), (-5202300605/137438953472)), (115/549755813888), by norm_num⟩
  | 8 => ⟨((3604116267/549755813888), (15317856683/1099511627776)), (87/1099511627776), by norm_num⟩
  | 9 => ⟨((-9432978153/4398046511104), (-5011388255/1099511627776)), (29/1099511627776), by norm_num⟩
  | 10 => ⟨((5554965713/8796093022208), (5902290767/4398046511104)), (35/4398046511104), by norm_num⟩
  | 11 => ⟨((-5947730027/35184372088832), (-12639225455/35184372088832)), (77/35184372088832), by norm_num⟩
  | 12 => ⟨((5837576043/140737488355328), (12405142699/140737488355328)), (77/140737488355328), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (1473205401293/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444640339365629/158456325028528675187087900672), (871538634209/316912650057057350374175801344)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889508514199901/39614081257132168796771975168), (980291775287/19807040628566084398385987584)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944634504247797/1237940039285380274899124224), (2082650726851/2475880078570760549798248448)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770935263056575/154742504910672534362390528), (2082122956763/154742504910672534362390528)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774656985225633/4835703278458516698824704), (975714844591/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258579165973747/604462909807314587353088), (213367573727/75557863725914323419136)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943725794494089/37778931862957161709568), (86647754495/2361183241434822606848)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297284119916767/4722366482869645213696), (2078627495725/4722366482869645213696)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621097044791613/590295810358705651712), (2856620836127/590295810358705651712)), (4751/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823035800844075/73786976294838206464), (1784269721823/36893488147419103232)), (1485/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822163237539329/9223372036854775808), (4011533746295/9223372036854775808)), (6685/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593411755707237/1152921504606846976), (62620244267/18014398509481984)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((1194078435168681/144115188075855872), (3502420330517/144115188075855872)), (183/4503599627370496), by norm_num⟩
  | 4 => ⟨((745441970270629/18014398509481984), (1311253777431/9007199254740992)), (8791/36028797018963968), by norm_num⟩
  | 3 => ⟨((744157956433935/4503599627370496), (3270608689665/4503599627370496)), (11001/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113032370068595/2251799813685248), (3259345437137/1125899906842624)), (22041/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213279277453907/2251799813685248), (9721897342773/1125899906842624)), (4145/281474976710656), by norm_num⟩
  | 0 => ⟨((2175086695846041/2251799813685248), (19220299744511/1125899906842624)), (8339/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2175086695846041/2251799813685248), (19220299744511/1125899906842624)), (31810761571788699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1050165389039875/1125899906842624), (18565512800199/562949953421312)), (131157/2251799813685248), by norm_num⟩
  | 2 => ⟨((978300668275209/1125899906842624), (138533515130815/2251799813685248)), (253321/2251799813685248), by norm_num⟩
  | 3 => ⟨((422894747595535/562949953421312), (240745077972431/2251799813685248)), (235697/1125899906842624), by norm_num⟩
  | 4 => ⟨((1244995790077001/2251799813685248), (361701172067863/2251799813685248)), (809031/2251799813685248), by norm_num⟩
  | 5 => ⟨((1260491071017169/4503599627370496), (399961340927041/2251799813685248)), (1154515/2251799813685248), by norm_num⟩
  | 6 => ⟨((210711768737633/4503599627370496), (895546213169831/9007199254740992)), (4225561/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-12885856641/536870912)), (1/536870912), by norm_num⟩, -4, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2412482277/1073741824), (-26220666745/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((720492869074875/9007199254740992), (622853881386221/9007199254740992)), (3247689/9007199254740992), by norm_num⟩
  | 1 => ⟨((-514603553/2147483648), (-7117856881/34359738368)), (19/17179869184), by norm_num⟩
  | 2 => ⟨((6166457887/17179869184), (2665399197/8589934592)), (59/34359738368), by norm_num⟩
  | 3 => ⟨((-6157685635/17179869184), (-5323214931/17179869184)), (61/34359738368), by norm_num⟩
  | 4 => ⟨((4611694397/17179869184), (996682923/4294967296)), (47/34359738368), by norm_num⟩
  | 5 => ⟨((-11052321393/68719476736), (-9554544637/68719476736)), (29/34359738368), by norm_num⟩
  | 6 => ⟨((1379574829/17179869184), (18634673/268435456)), (15/34359738368), by norm_num⟩
  | 7 => ⟨((-9446484203/274877906944), (-4083162793/137438953472)), (53/274877906944), by norm_num⟩
  | 8 => ⟨((14149568799/1099511627776), (12232062557/1099511627776)), (81/1099511627776), by norm_num⟩
  | 9 => ⟨((-4709813323/1099511627776), (-8143107683/2199023255552)), (55/2199023255552), by norm_num⟩
  | 10 => ⟨((11287471819/8796093022208), (9757828197/8796093022208)), (17/2199023255552), by norm_num⟩
  | 11 => ⟨((-12296088587/35184372088832), (-10629760309/35184372088832)), (19/8796093022208), by norm_num⟩
  | 12 => ⟨((12278596473/140737488355328), (10614638673/140737488355328)), (39/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060283875/10141204801825835211973625643008), (928556773103/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889251524423047/316912650057057350374175801344), (1098586401223/633825300114114700748351602688)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472360746235609/9903520314283042199192993792), (1235667989379/39614081257132168796771975168)), (1623/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889199471780487/2475880078570760549798248448), (656298199723/1237940039285380274899124224)), (3449/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885432912698733/77371252455336267181195264), (656129044845/77371252455336267181195264)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((48414030557149/302231454903657293676544), (1229882624315/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629261201269921/302231454903657293676544), (537894047901/302231454903657293676544)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471839886334401/18889465931478580854784), (873741220023/37778931862957161709568)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((648607629669541/2361183241434822606848), (1310023051475/4722366482869645213696)), (1725/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621002640970879/590295810358705651712), (1800325464927/590295810358705651712)), (4745/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822918214777051/73786976294838206464), (1124486709669/36893488147419103232)), (1483/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822031528124587/9223372036854775808), (316015709113/1152921504606846976)), (6675/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398320190927793/288230376151711744), (1262833083645/576460752303423488)), (6677/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193964622593493/144115188075855872), (137949629781/9007199254740992)), (5845/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490714828341705/36028797018963968), (413158909443/4503599627370496)), (2193/9007199254740992), by norm_num⟩
  | 3 => ⟨((1488107324894687/9007199254740992), (2060973450823/4503599627370496)), (10973/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225655933579339/4503599627370496), (8215037201115/4503599627370496)), (21969/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212686860484507/2251799813685248), (6125329320967/1125899906842624)), (4127/281474976710656), by norm_num⟩
  | 0 => ⟨((543496063309933/562949953421312), (12107595080859/1125899906842624)), (33141/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((543496063309933/562949953421312), (12107595080859/1125899906842624)), (126422886375045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2098597366062437/2251799813685248), (23378384606323/1125899906842624)), (64705/1125899906842624), by norm_num⟩
  | 2 => ⟨((244355908250837/281474976710656), (87151293040265/2251799813685248)), (246587/2251799813685248), by norm_num⟩
  | 3 => ⟨((6615944746101/8796093022208), (151316707545055/2251799813685248)), (223613/1125899906842624), by norm_num⟩
  | 4 => ⟨((631863779072595/1125899906842624), (28453057901743/281474976710656)), (732865/2251799813685248), by norm_num⟩
  | 5 => ⟨((1372408360255911/4503599627370496), (127744618026545/1125899906842624)), (1941487/4503599627370496), by norm_num⟩
  | 6 => ⟨((720492869074875/9007199254740992), (622853881386221/9007199254740992)), (3247689/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2412482277/1073741824), (-26220666745/1073741824)), (1/536870912), by norm_num⟩, -4, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2451773307/1073741824), (-13323855563/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((872961200584793/9007199254740992), (142287941863457/4503599627370496)), (2356511/9007199254740992), by norm_num⟩
  | 1 => ⟨((-20277023029/68719476736), (-3305044797/34359738368)), (7/8589934592), by norm_num⟩
  | 2 => ⟨((964591431/2147483648), (5031141521/34359738368)), (11/8589934592), by norm_num⟩
  | 3 => ⟨((-7831254013/17179869184), (-5105807749/34359738368)), (47/34359738368), by norm_num⟩
  | 4 => ⟨((11921214279/34359738368), (7772373127/68719476736)), (37/34359738368), by norm_num⟩
  | 5 => ⟨((-14517761743/68719476736), (-1183158219/17179869184)), (23/34359738368), by norm_num⟩
  | 6 => ⟨((3683304281/34359738368), (2401434497/68719476736)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((-3203972151/68719476736), (-4177840691/274877906944)), (43/274877906944), by norm_num⟩
  | 8 => ⟨((19509130207/1099511627776), (6359764863/1099511627776)), (17/274877906944), by norm_num⟩
  | 9 => ⟨((-13199107701/2199023255552), (-4302765961/2199023255552)), (3/137438953472), by norm_num⟩
  | 10 => ⟨((16073991821/8796093022208), (5239947005/8796093022208)), (15/2199023255552), by norm_num⟩
  | 11 => ⟨((-2224437671/4398046511104), (-5801140447/35184372088832)), (17/8796093022208), by norm_num⟩
  | 12 => ⟨((18059601069/140737488355328), (5887234085/140737488355328)), (71/140737488355328), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394306545/10141204801825835211973625643008), (410487183587/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889223588225221/316912650057057350374175801344), (242811430215/316912650057057350374175801344)), (2883/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236172521259041/4951760157141521099596496896), (546217385477/39614081257132168796771975168)), (811/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472283196183587/618970019642690137449562112), (72527605589/309485009821345068724781056)), (3447/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442699799694015/38685626227668133590597632), (580068890761/154742504910672534362390528)), (3447/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549186579534789/9671406556917033397649408), (543653190003/9671406556917033397649408)), (101/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((629233934076885/302231454903657293676544), (59441901147/75557863725914323419136)), (707/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((943635523548653/37778931862957161709568), (386221175549/37778931862957161709568)), (4595/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297148990688751/4722366482869645213696), (144766832187/1180591620717411303424)), (3447/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620911692081557/590295810358705651712), (795788121497/590295810358705651712)), (1185/147573952589676412928), by norm_num⟩
  | 8 => ⟨((455701196031947/18446744073709551616), (62130712933/4611686018427387904)), (5925/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821904269426189/9223372036854775808), (279367098817/2305843009213693952)), (3333/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796576971386529/576460752303423488), (1116363915055/1152921504606846976)), (6667/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596927072884101/72057594037927936), (975577350577/144115188075855872)), (5835/144115188075855872), by norm_num⟩
  | 4 => ⟨((745275046818673/18014398509481984), (1460887533849/36028797018963968)), (8753/36028797018963968), by norm_num⟩
  | 3 => ⟨((92993944808155/562949953421312), (227722534289/1125899906842624)), (10945/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225252626889243/4503599627370496), (907651481887/1125899906842624)), (21901/4503599627370496), by norm_num⟩
  | 1 => ⟨((2212094596776549/2251799813685248), (2706818438993/1125899906842624)), (2055/140737488355328), by norm_num⟩
  | 0 => ⟨((2172850052656955/2251799813685248), (1337358829683/281474976710656)), (32937/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172850052656955/2251799813685248), (1337358829683/281474976710656)), (125644688132857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2096617495394433/2251799813685248), (10323760347923/1125899906842624)), (31939/562949953421312), by norm_num⟩
  | 2 => ⟨((1951940210302157/2251799813685248), (38449202157613/2251799813685248)), (30031/281474976710656), by norm_num⟩
  | 3 => ⟨((1691354720033843/2251799813685248), (66658273341497/2251799813685248)), (424717/2251799813685248), by norm_num⟩
  | 4 => ⟨((317106059585891/562949953421312), (25033927207973/562949953421312)), (331583/1125899906842624), by norm_num⟩
  | 5 => ⟨((1420084395173213/4503599627370496), (225623182725495/4503599627370496)), (1612191/4503599627370496), by norm_num⟩
  | 6 => ⟨((872961200584793/9007199254740992), (142287941863457/4503599627370496)), (2356511/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2451773307/1073741824), (-13323855563/536870912)), (1/536870912), by norm_num⟩, -4, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile018Terms2
