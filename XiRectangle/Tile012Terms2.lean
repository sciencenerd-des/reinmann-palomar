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
namespace Reinmann.XiRectangle.Tile012Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨12,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (705/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (705/128))
  have he : value ((3/4), (705/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1116391677/536870912), (-16397002755/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1020063211513501/9007199254740992), (-476572811252841/9007199254740992)), (3137405/4503599627370496), by norm_num⟩
  | 1 => ⟨((337149591/1073741824), (2520256809/17179869184)), (135/68719476736), by norm_num⟩
  | 2 => ⟨((-3739108615/8589934592), (-3493817803/17179869184)), (95/34359738368), by norm_num⟩
  | 3 => ⟨((13822680503/34359738368), (6457946559/34359738368)), (89/34359738368), by norm_num⟩
  | 4 => ⟨((-19162304037/68719476736), (-8952614899/68719476736)), (63/34359738368), by norm_num⟩
  | 5 => ⟨((10625837613/68719476736), (4964383821/68719476736)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((-9820359177/137438953472), (-4588064865/137438953472)), (133/274877906944), by norm_num⟩
  | 7 => ⟨((7779376315/274877906944), (3634519115/274877906944)), (107/549755813888), by norm_num⟩
  | 8 => ⟨((-21569011037/2199023255552), (-10077026709/2199023255552)), (151/2199023255552), by norm_num⟩
  | 9 => ⟨((3322333153/1099511627776), (3104383401/2199023255552)), (95/4398046511104), by norm_num⟩
  | 10 => ⟨((-14738341491/17592186044416), (-3442871363/8796093022208)), (107/17592186044416), by norm_num⟩
  | 11 => ⟨((14859403419/70368744177664), (6942302773/70368744177664)), (55/35184372088832), by norm_num⟩
  | 12 => ⟨((-3433251195/70368744177664), (-6416050125/281474976710656)), (103/281474976710656), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326325/10141204801825835211973625643008), (-110092186009/316912650057057350374175801344)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778752347040811/633825300114114700748351602688), (-2084597463389/316912650057057350374175801344)), (2895/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944861451029631/19807040628566084398385987584), (-2344734521207/19807040628566084398385987584)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944748089761055/1237940039285380274899124224), (-4981501382873/2475880078570760549798248448)), (1731/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885580870748847/77371252455336267181195264), (-4980309545297/154742504910672534362390528)), (3463/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387381389640887/2417851639229258349412352), (-4667774049997/9671406556917033397649408)), (203/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((1258763570646961/604462909807314587353088), (-2041518172833/302231454903657293676544)), (2843/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887749869662393/75557863725914323419136), (-1658140208923/18889465931478580854784)), (2311/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297506626681819/4722366482869645213696), (-4972344480953/4722366482869645213696)), (867/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621401037509339/590295810358705651712), (-3416800362775/295147905179352825856)), (1193/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911706432051373/36893488147419103232), (-8536942906699/73786976294838206464)), (5969/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822583413866163/9223372036854775808), (-9597108302715/9223372036854775808)), (6721/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398456728930935/288230376151711744), (-2397105286847/288230376151711744)), (6729/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194436068494511/144115188075855872), (-4190050087931/72057594037927936)), (5897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491409156269989/36028797018963968), (-12550625432635/36028797018963968)), (8863/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488952837993757/9007199254740992), (-3913535000013/2251799813685248)), (11109/9007199254740992), by norm_num⟩
  | 2 => ⟨((278410008499419/562949953421312), (-15602980784499/2251799813685248)), (2789/562949953421312), by norm_num⟩
  | 1 => ⟨((1107478437694467/1125899906842624), (-23276760925175/1125899906842624)), (16851/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088932886116135/1125899906842624), (-46043812659539/1125899906842624)), (17085/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1088932886116135/1125899906842624), (-46043812659539/1125899906842624)), (65174104930686773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((525648323881795/562949953421312), (-22266020941305/281474976710656)), (17223/281474976710656), by norm_num⟩
  | 2 => ⟨((974591279307567/1125899906842624), (-83162608087505/562949953421312)), (139555/1125899906842624), by norm_num⟩
  | 3 => ⟨((1638092477958779/2251799813685248), (-143972927102985/562949953421312)), (282833/1125899906842624), by norm_num⟩
  | 4 => ⟨((1044362688119587/2251799813685248), (-837875436293371/2251799813685248)), (556167/1125899906842624), by norm_num⟩
  | 5 => ⟨((345197805977693/4503599627370496), (-1554393667924921/4503599627370496)), (3719119/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1020063211513501/9007199254740992), (-476572811252841/9007199254740992)), (3137405/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/536870912), (-16397002755/1073741824)), (1/536870912), by norm_num⟩, -2, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-570401187/268435456), (-16755534867/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-66883395839165/562949953421312), (-110783360477321/9007199254740992)), (1398853/2251799813685248), by norm_num⟩
  | 1 => ⟨((2891463159/8589934592), (1197330075/34359738368)), (123/68719476736), by norm_num⟩
  | 2 => ⟨((-4096066003/8589934592), (-1696145773/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((30946743621/68719476736), (3203695225/68719476736)), (85/34359738368), by norm_num⟩
  | 4 => ⟨((-10959840873/34359738368), (-2269188015/68719476736)), (123/68719476736), by norm_num⟩
  | 5 => ⟨((3105156741/17179869184), (1285818753/68719476736)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((-1466261919/17179869184), (-2428665899/274877906944)), (17/34359738368), by norm_num⟩
  | 7 => ⟨((9495389337/274877906944), (982989805/274877906944)), (7/34359738368), by norm_num⟩
  | 8 => ⟨((-26902463777/2199023255552), (-2785019833/2199023255552)), (161/2199023255552), by norm_num⟩
  | 9 => ⟨((16937870969/4398046511104), (1753456745/4398046511104)), (103/4398046511104), by norm_num⟩
  | 10 => ⟨((-4798860205/4398046511104), (-1987166819/17592186044416)), (59/8796093022208), by norm_num⟩
  | 11 => ⟨((19776283301/70368744177664), (1023648645/35184372088832)), (31/17592186044416), by norm_num⟩
  | 12 => ⟨((-18676809915/281474976710656), (-1933476667/281474976710656)), (119/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-1978951885285/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778679817881305/633825300114114700748351602688), (-2341792288255/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472410296292183/9903520314283042199192993792), (-2634011148069/19807040628566084398385987584)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((118088074640843/154742504910672534362390528), (-5596056744281/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885537287587763/77371252455336267181195264), (-174833989643/4835703278458516698824704)), (1733/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387360911977979/2417851639229258349412352), (-655445650193/1208925819614629174706176)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629345853382441/302231454903657293676544), (-4586665237613/604462909807314587353088)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943816365541787/37778931862957161709568), (-1862651135785/18889465931478580854784)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648709229147031/2361183241434822606848), (-5585568118713/4722366482869645213696)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621279295636525/590295810358705651712), (-959535095715/73786976294838206464)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((1823259922384867/73786976294838206464), (-2397384770555/18446744073709551616)), (5975/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822410305254821/9223372036854775808), (-5390121064319/4611686018427387904)), (6729/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796826249198175/576460752303423488), (-10770258446681/1152921504606846976)), (3369/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194281984815907/144115188075855872), (-9412748624863/144115188075855872)), (2953/72057594037927936), by norm_num⟩
  | 4 => ⟨((745587551589973/18014398509481984), (-7048339129517/18014398509481984)), (4439/18014398509481984), by norm_num⟩
  | 3 => ⟨((744327584822637/4503599627370496), (-17581593037305/9007199254740992)), (2783/2251799813685248), by norm_num⟩
  | 2 => ⟨((556667377569741/1125899906842624), (-17522757919231/2251799813685248)), (11185/2251799813685248), by norm_num⟩
  | 1 => ⟨((17296900648403/17592186044416), (-6534303741981/281474976710656)), (16909/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087904670048493/1125899906842624), (-807621045277/17592186044416)), (4293/140737488355328), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1087904670048493/1125899906842624), (-807621045277/17592186044416)), (16376495898199037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((262204690833813/281474976710656), (-99886927590239/1125899906842624)), (69525/1125899906842624), by norm_num⟩
  | 2 => ⟨((484076512217455/562949953421312), (-186096975817933/1125899906842624)), (141867/1125899906842624), by norm_num⟩
  | 3 => ⟨((1603496347815329/2251799813685248), (-640093666875153/2251799813685248)), (290879/1125899906842624), by norm_num⟩
  | 4 => ⟨((959890227340407/2251799813685248), (-911615544913173/2251799813685248)), (1159275/2251799813685248), by norm_num⟩
  | 5 => ⟨((2507614860655/140737488355328), (-777201283467259/2251799813685248)), (3853967/4503599627370496), by norm_num⟩
  | 6 => ⟨((-66883395839165/562949953421312), (-110783360477321/9007199254740992)), (1398853/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-16755534867/1073741824)), (1/536870912), by norm_num⟩, -2, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2327634783/1073741824), (-8546783967/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1007705110067945/9007199254740992), (216536697289043/9007199254740992)), (1380109/2251799813685248), by norm_num⟩
  | 1 => ⟨((22221697925/68719476736), (-2387510507/34359738368)), (31/17179869184), by norm_num⟩
  | 2 => ⟨((-2007155253/4294967296), (3450396471/34359738368)), (23/8589934592), by norm_num⟩
  | 3 => ⟨((15470466285/34359738368), (-811599/8388608)), (91/34359738368), by norm_num⟩
  | 4 => ⟨((-2794712427/8589934592), (150132661/2147483648)), (67/34359738368), by norm_num⟩
  | 5 => ⟨((12924412593/68719476736), (-2777210901/68719476736)), (157/137438953472), by norm_num⟩
  | 6 => ⟨((-12452119049/137438953472), (5351447969/274877906944)), (77/137438953472), by norm_num⟩
  | 7 => ⟨((10283215207/274877906944), (-2209667725/274877906944)), (65/274877906944), by norm_num⟩
  | 8 => ⟨((-14861157407/1099511627776), (3193380593/1099511627776)), (3/34359738368), by norm_num⟩
  | 9 => ⟨((19090786515/4398046511104), (-2051123795/2199023255552)), (125/4398046511104), by norm_num⟩
  | 10 => ⟨((-2758973509/2199023255552), (4742808231/17592186044416)), (147/17592186044416), by norm_num⟩
  | 11 => ⟨((23198426505/70368744177664), (-4984901441/70368744177664)), (157/70368744177664), by norm_num⟩
  | 12 => ⟨((-11175346133/140737488355328), (4802739447/281474976710656)), (153/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290011/2535301200456458802993406410752), (1908280622507/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889307282054235/316912650057057350374175801344), (2258003687833/316912650057057350374175801344)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889567836300275/39614081257132168796771975168), (5079518420783/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944665669516649/1237940039285380274899124224), (1348947910451/618970019642690137449562112)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770996807618977/154742504910672534362390528), (2697222710121/77371252455336267181195264)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549370833928447/9671406556917033397649408), (5055862410663/9671406556917033397649408)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258628087583195/604462909807314587353088), (1105612412813/151115727451828646838272)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887529524289525/75557863725914323419136), (1795949991091/18889465931478580854784)), (289/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((648670602838957/2361183241434822606848), (5385504797151/4722366482869645213696)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405293330220307/147573952589676412928), (3700629517553/295147905179352825856)), (4775/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823127825001149/73786976294838206464), (9245860192247/73786976294838206464)), (5973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822262205374025/9223372036854775808), (5196869469319/4611686018427387904)), (6727/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796752517406035/576460752303423488), (10383925359847/1152921504606846976)), (6735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194153668915375/144115188075855872), (4537449716749/72057594037927936)), (5903/144115188075855872), by norm_num⟩
  | 4 => ⟨((23296625875867/562949953421312), (13590291217729/36028797018963968)), (8873/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488418851333223/9007199254740992), (16949291030149/9007199254740992)), (11125/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113102160359863/2251799813685248), (4222872133033/562949953421312)), (1397/281474976710656), by norm_num⟩
  | 1 => ⟨((276665503723857/281474976710656), (25192926959741/1125899906842624)), (8445/562949953421312), by norm_num⟩
  | 0 => ⟨((1087262219441631/1125899906842624), (24904920246991/562949953421312)), (2143/70368744177664), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1087262219441631/1125899906842624), (24904920246991/562949953421312)), (8174896508669831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1047746879137095/1125899906842624), (96201016442735/1125899906842624)), (69257/1125899906842624), by norm_num⟩
  | 2 => ⟨((241699746256631/281474976710656), (44761667593681/281474976710656)), (140735/1125899906842624), by norm_num⟩
  | 3 => ⟨((801707648957299/1125899906842624), (153745584433073/562949953421312)), (286457/1125899906842624), by norm_num⟩
  | 4 => ⟨((973770993557059/2251799813685248), (875807949067599/2251799813685248)), (8819/17592186044416), by norm_num⟩
  | 5 => ⟨((80464694570951/2251799813685248), (1514941730691401/4503599627370496)), (463599/562949953421312), by norm_num⟩
  | 6 => ⟨((-1007705110067945/9007199254740992), (216536697289043/9007199254740992)), (1380109/2251799813685248), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2327634783/1073741824), (-8546783967/536870912)), (1/536870912), by norm_num⟩, -3, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-592793865/268435456), (-17413319785/1073741824)), (1/1073741824), by norm_num⟩
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
  | 0 => ⟨((-864060424417453/9007199254740992), (120675287656739/2251799813685248)), (2786835/9007199254740992), by norm_num⟩
  | 1 => ⟨((19410501053/68719476736), (-2710884253/17179869184)), (65/68719476736), by norm_num⟩
  | 2 => ⟨((-446508093/1073741824), (3991016631/17179869184)), (25/17179869184), by norm_num⟩
  | 3 => ⟨((7011817779/17179869184), (-3917101645/17179869184)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-20645869583/68719476736), (11533666769/68719476736)), (77/68719476736), by norm_num⟩
  | 5 => ⟨((1519762579/8589934592), (-6792035601/68719476736)), (47/68719476736), by norm_num⟩
  | 6 => ⟨((-11932928471/137438953472), (3333122395/68719476736)), (3/8589934592), by norm_num⟩
  | 7 => ⟨((10038794207/274877906944), (-5608100287/274877906944)), (83/549755813888), by norm_num⟩
  | 8 => ⟨((-14779308483/1099511627776), (4128177271/549755813888)), (63/1099511627776), by norm_num⟩
  | 9 => ⟨((4835196887/1099511627776), (-5402296031/2199023255552)), (85/4398046511104), by norm_num⟩
  | 10 => ⟨((-11389553749/8796093022208), (1590673101/2199023255552)), (13/2199023255552), by norm_num⟩
  | 11 => ⟨((1524356637/4398046511104), (-6812567101/35184372088832)), (57/35184372088832), by norm_num⟩
  | 12 => ⟨((-11969000267/140737488355328), (835799505/17592186044416)), (57/140737488355328), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (1714326881907/5070602400912917605986812821504)), (607/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778554171378895/633825300114114700748351602688), (2028369035213/316912650057057350374175801344)), (181/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944750013608755/19807040628566084398385987584), (2281465623127/19807040628566084398385987584)), (1629/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472314865850467/618970019642690137449562112), (4847020087809/2475880078570760549798248448)), (1731/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770925124827141/154742504910672534362390528), (2422894536639/77371252455336267181195264)), (1731/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549303836082331/9671406556917033397649408), (1135404884673/2417851639229258349412352)), (1625/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629284834551657/302231454903657293676544), (248288102705/37778931862957161709568)), (711/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887434977662801/75557863725914323419136), (3226519878965/37778931862957161709568)), (2311/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297270630897219/4722366482869645213696), (4837635832431/4722366482869645213696)), (867/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25329325385937/9223372036854775808), (6648266347157/590295810358705651712)), (1193/295147905179352825856), by norm_num⟩
  | 8 => ⟨((113938001252645/4611686018427387904), (8305110397193/73786976294838206464)), (373/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822128544252579/9223372036854775808), (9336071211751/9223372036854775808)), (105/288230376151711744), by norm_num⟩
  | 6 => ⟨((398343192677339/288230376151711744), (1165887904729/144115188075855872)), (3365/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149254938288365/18014398509481984), (8151132565083/144115188075855872)), (737/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490815941199183/36028797018963968), (12206548832825/36028797018963968)), (2215/18014398509481984), by norm_num⟩
  | 3 => ⟨((744107082918121/4503599627370496), (15222958478021/9007199254740992)), (5553/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112905626458319/2251799813685248), (7585093579479/1125899906842624)), (5575/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106387468892609/1125899906842624), (2827949746921/140737488355328)), (2105/281474976710656), by norm_num⟩
  | 0 => ⟨((1086793403306199/1125899906842624), (44721941639555/1125899906842624)), (17067/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1086793403306199/1125899906842624), (44721941639555/1125899906842624)), (65105442527389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1047268804482345/1125899906842624), (86337179462449/1125899906842624)), (34305/1125899906842624), by norm_num⟩
  | 2 => ⟨((967508597934907/1125899906842624), (80307524823923/562949953421312)), (69081/1125899906842624), by norm_num⟩
  | 3 => ⟨((808487226415435/1125899906842624), (552079063325667/2251799813685248)), (276871/2251799813685248), by norm_num⟩
  | 4 => ⟨((512881978874701/1125899906842624), (792874869173587/2251799813685248)), (533395/2251799813685248), by norm_num⟩
  | 5 => ⟨((47022512422799/562949953421312), (1444715394078489/4503599627370496)), (1723161/4503599627370496), by norm_num⟩
  | 6 => ⟨((-864060424417453/9007199254740992), (120675287656739/2251799813685248)), (2786835/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-17413319785/1073741824)), (1/1073741824), by norm_num⟩, -3, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-2412482277/1073741824), (-553645835/33554432)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-20906438318113/281474976710656), (677855345100265/9007199254740992)), (5429007/9007199254740992), by norm_num⟩
  | 1 => ⟨((15290549803/68719476736), (-1936600813/8589934592)), (63/34359738368), by norm_num⟩
  | 2 => ⟨((-11451598381/34359738368), (11603075113/34359738368)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((5717653809/17179869184), (-11586568863/34359738368)), (97/34359738368), by norm_num⟩
  | 4 => ⟨((-4282140011/17179869184), (8677564571/34359738368)), (37/17179869184), by norm_num⟩
  | 5 => ⟨((10262516025/68719476736), (-324945753/2147483648)), (91/68719476736), by norm_num⟩
  | 6 => ⟨((-10247916821/137438953472), (2595867945/34359738368)), (93/137438953472), by norm_num⟩
  | 7 => ⟨((4385716451/137438953472), (-4443728789/137438953472)), (81/274877906944), by norm_num⟩
  | 8 => ⟨((-13138432315/1099511627776), (3328055437/274877906944)), (123/1099511627776), by norm_num⟩
  | 9 => ⟨((4373247301/1099511627776), (-8862189405/2199023255552)), (83/2199023255552), by norm_num⟩
  | 10 => ⟨((-40940869/34359738368), (5309749363/4398046511104)), (101/8796093022208), by norm_num⟩
  | 11 => ⟨((11417402887/35184372088832), (-11568427295/35184372088832)), (7/2199023255552), by norm_num⟩
  | 12 => ⟨((-5700580385/70368744177664), (5775985167/70368744177664)), (57/70368744177664), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060283875/10141204801825835211973625643008), (765161983325/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778496672422245/633825300114114700748351602688), (3621088441605/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472358863727853/9903520314283042199192993792), (4072913150519/39614081257132168796771975168)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889191002971329/2475880078570760549798248448), (4326476915287/2475880078570760549798248448)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770856830384699/154742504910672534362390528), (4325359652519/154742504910672534362390528)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387309996574669/2417851639229258349412352), (4053837843705/9671406556917033397649408)), (3245/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258513976679361/604462909807314587353088), (3545921576205/604462909807314587353088)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471836201869165/18889465931478580854784), (2879949214053/37778931862957161709568)), (2309/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648601645878263/2361183241434822606848), (2158989164133/2361183241434822606848)), (3465/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620984701717093/590295810358705651712), (185439373287/18446744073709551616)), (4767/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822893567985979/73786976294838206464), (7412836594257/73786976294838206464)), (2981/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911000374569367/4611686018427387904), (8332929281647/9223372036854775808)), (6713/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593246177884041/1152921504606846976), (4162397206897/576460752303423488)), (105/18014398509481984), by norm_num⟩
  | 5 => ⟨((149241260922419/18014398509481984), (3637525124481/72057594037927936)), (23/562949953421312), by norm_num⟩
  | 4 => ⟨((186331813181677/4503599627370496), (10894302808043/36028797018963968)), (8847/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488017067678533/9007199254740992), (13585940139887/9007199254740992)), (11085/9007199254740992), by norm_num⟩
  | 2 => ⟨((556357770960667/1125899906842624), (13538109841473/2251799813685248)), (5563/1125899906842624), by norm_num⟩
  | 1 => ⟨((1106119767258617/1125899906842624), (10093929747699/562949953421312)), (8395/562949953421312), by norm_num⟩
  | 0 => ⟨((271581762263079/281474976710656), (9975030355557/281474976710656)), (33987/1125899906842624), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((271581762263079/281474976710656), (9975030355557/281474976710656)), (129650120261764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2093462181941427/2251799813685248), (153990886394119/2251799813685248)), (135989/2251799813685248), by norm_num⟩
  | 2 => ⟨((967863725637511/1125899906842624), (143162858026059/1125899906842624)), (135727/1125899906842624), by norm_num⟩
  | 3 => ⟨((406903216670577/562949953421312), (492271599988269/2251799813685248)), (535737/2251799813685248), by norm_num⟩
  | 4 => ⟨((16700476526929/35184372088832), (711633054744703/2251799813685248)), (504353/1125899906842624), by norm_num⟩
  | 5 => ⟨((282430535962105/2251799813685248), (1351123856528681/4503599627370496)), (1595137/2251799813685248), by norm_num⟩
  | 6 => ⟨((-20906438318113/281474976710656), (677855345100265/9007199254740992)), (5429007/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2412482277/1073741824), (-553645835/33554432)), (1/536870912), by norm_num⟩, -3, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2451773307/1073741824), (-18005210221/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-224156394967839/4503599627370496), (400643336929947/4503599627370496)), (1286287/2251799813685248), by norm_num⟩
  | 1 => ⟨((10413347993/68719476736), (-18612176953/68719476736)), (61/34359738368), by norm_num⟩
  | 2 => ⟨((-495369869/2147483648), (14166297587/34359738368)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((4021772483/17179869184), (-7188268477/17179869184)), (97/34359738368), by norm_num⟩
  | 4 => ⟨((-3061094141/17179869184), (21884844667/68719476736)), (75/34359738368), by norm_num⟩
  | 5 => ⟨((7455655837/68719476736), (-13325780127/68719476736)), (93/68719476736), by norm_num⟩
  | 6 => ⟨((-1891575957/34359738368), (3380886383/34359738368)), (3/4294967296), by norm_num⟩
  | 7 => ⟨((205676623/8589934592), (-5881819687/137438953472)), (85/274877906944), by norm_num⟩
  | 8 => ⟨((-5009496749/549755813888), (4476833003/274877906944)), (131/1099511627776), by norm_num⟩
  | 9 => ⟨((1694613917/549755813888), (-12115394247/2199023255552)), (91/2199023255552), by norm_num⟩
  | 10 => ⟨((-4127432075/4398046511104), (14754235851/8796093022208)), (113/8796093022208), by norm_num⟩
  | 11 => ⟨((9138952409/35184372088832), (-4083600191/8796093022208)), (127/35184372088832), by norm_num⟩
  | 12 => ⟨((-9274581889/140737488355328), (518025517/4398046511104)), (131/140737488355328), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394306545/10141204801825835211973625643008), (677650228241/2535301200456458802993406410752)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778441794490973/633825300114114700748351602688), (1603374991315/316912650057057350374175801344)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889373814998747/39614081257132168796771975168), (3606867433441/39614081257132168796771975168)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((118070352336809/154742504910672534362390528), (3831403081833/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885395803688401/77371252455336267181195264), (3830398067229/154742504910672534362390528)), (3459/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549178991121269/9671406556917033397649408), (448741328869/1208925819614629174706176)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((314615189296793/151115727451828646838272), (196257628101/37778931862957161709568)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887258609245055/75557863725914323419136), (318793617467/4722366482869645213696)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297138890873851/4722366482869645213696), (3823773661983/4722366482869645213696)), (3463/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620896552748235/590295810358705651712), (5254846658553/590295810358705651712)), (1191/147573952589676412928), by norm_num⟩
  | 8 => ⟨((911391992207633/36893488147419103232), (1641074313987/18446744073709551616)), (5957/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821878295071841/9223372036854775808), (7378978894323/9223372036854775808)), (6707/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593124756360785/1152921504606846976), (3685832334077/576460752303423488)), (6713/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596912501363989/72057594037927936), (6441985189955/144115188075855872)), (5881/144115188075855872), by norm_num⟩
  | 4 => ⟨((186312398846381/4503599627370496), (9646552764311/36028797018963968)), (4417/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487826957207049/9007199254740992), (12029487133313/9007199254740992)), (11067/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225062907103945/4503599627370496), (2996627822235/562949953421312)), (5551/1125899906842624), by norm_num⟩
  | 1 => ⟨((2211717189814643/2251799813685248), (35745213510599/2251799813685248)), (16743/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171727953176345/2251799813685248), (35318247963095/1125899906842624)), (33847/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2171727953176345/2251799813685248), (35318247963095/1125899906842624)), (129116062644576671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046143791161477/1125899906842624), (136249458575341/2251799813685248)), (67411/1125899906842624), by norm_num⟩
  | 2 => ⟨((1935830789970065/2251799813685248), (126597865646355/1125899906842624)), (66715/562949953421312), by norm_num⟩
  | 3 => ⟨((204466042377853/281474976710656), (435335405524575/2251799813685248)), (259421/1125899906842624), by norm_num⟩
  | 4 => ⟨((276011467434847/562949953421312), (632463379265627/2251799813685248)), (954397/2251799813685248), by norm_num⟩
  | 5 => ⟨((181833960416823/1125899906842624), (77523385670867/281474976710656)), (2943991/4503599627370496), by norm_num⟩
  | 6 => ⟨((-224156394967839/4503599627370496), (400643336929947/4503599627370496)), (1286287/2251799813685248), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2451773307/1073741824), (-18005210221/1073741824)), (1/536870912), by norm_num⟩, -3, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨12,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile012Terms2
