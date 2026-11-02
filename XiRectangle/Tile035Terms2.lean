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
namespace Reinmann.XiRectangle.Tile035Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8601/640))
  have he : value ((5/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-7268175/4194304), (-312567865/8388608)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((1441875864952239/9007199254740992), (337748118566297/4503599627370496)), (71359627/4503599627370496), by norm_num⟩
  | 1 => ⟨((-953132811/2147483648), (-446527779/2147483648)), (3/67108864), by norm_num⟩
  | 2 => ⟨((1321322641/2147483648), (309509471/1073741824)), (135/2147483648), by norm_num⟩
  | 3 => ⟨((-610580709/1073741824), (-572094979/2147483648)), (127/2147483648), by norm_num⟩
  | 4 => ⟨((423222297/1073741824), (198273011/1073741824)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-469368547/2147483648), (-439783611/4294967296)), (51/2147483648), by norm_num⟩
  | 6 => ⟨((867577293/8589934592), (50805795/1073741824)), (3/268435456), by norm_num⟩
  | 7 => ⟨((-171816787/4294967296), (-80493471/4294967296)), (77/17179869184), by norm_num⟩
  | 8 => ⟨((238188643/17179869184), (111587645/17179869184)), (27/17179869184), by norm_num⟩
  | 9 => ⟨((-1174042925/274877906944), (-17188147/8589934592)), (135/274877906944), by norm_num⟩
  | 10 => ⟨((1302055269/1099511627776), (19062265/34359738368)), (19/137438953472), by norm_num⟩
  | 11 => ⟨((-164093807/549755813888), (-4804711/34359738368)), (39/1099511627776), by norm_num⟩
  | 12 => ⟨((1213239037/17592186044416), (142095867/4398046511104)), (73/8796093022208), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581718513116769/10141204801825835211973625643008), (570698549039/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779295824555307/633825300114114700748351602688), (675772993335/633825300114114700748351602688)), (92267/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890334724755161/39614081257132168796771975168), (760128695147/39614081257132168796771975168)), (25951/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472536695663923/618970019642690137449562112), (403746986019/1237940039285380274899124224)), (55149/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771812953303803/154742504910672534362390528), (807333406879/154742504910672534362390528)), (110303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((193767089484897/1208925819614629174706176), (378352256363/4835703278458516698824704)), (103415/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259298979020127/604462909807314587353088), (330972971103/302231454903657293676544)), (45247/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888621117881541/75557863725914323419136), (537671281155/37778931862957161709568)), (147063/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((162270140017743/590295810358705651712), (806227382917/4722366482869645213696)), (27577/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((405575670508125/147573952589676412928), (1108108599107/590295810358705651712)), (151689/590295810358705651712), by norm_num⟩
  | 8 => ⟨((114033905632793/4611686018427387904), (1384455016911/73786976294838206464)), (94817/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823857771461715/9223372036854775808), (1556576450519/9223372036854775808)), (213371/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797552837412915/576460752303423488), (1555407990009/1152921504606846976)), (53353/288230376151711744), by norm_num⟩
  | 5 => ⟨((298889980546727/36028797018963968), (1359668632601/144115188075855872)), (93391/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493104785262393/36028797018963968), (1018439563701/18014398509481984)), (280265/36028797018963968), by norm_num⟩
  | 3 => ⟨((745544770253581/4503599627370496), (1270756864861/4503599627370496)), (350493/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115802349150223/2251799813685248), (5069297915815/4503599627370496)), (21921/140737488355328), by norm_num⟩
  | 1 => ⟨((277696366137591/281474976710656), (1892428457223/562949953421312)), (1053431/2251799813685248), by norm_num⟩
  | 0 => ⟨((2191596602611619/2251799813685248), (1875379877669/281474976710656)), (263973/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2191596602611619/2251799813685248), (1875379877669/281474976710656)), (1006977082372569949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1066451499864599/1125899906842624), (29203847649523/2251799813685248)), (2069395/1125899906842624), by norm_num⟩
  | 2 => ⟨((63122040116163/70368744177664), (1728866334963/70368744177664)), (7947871/2251799813685248), by norm_num⟩
  | 3 => ⟨((1810532453247253/2251799813685248), (24813191464777/562949953421312)), (14649307/2251799813685248), by norm_num⟩
  | 4 => ⟨((725680993680829/1125899906842624), (159605976135483/2251799813685248)), (6212149/562949953421312), by norm_num⟩
  | 5 => ⟨((924139676223943/2251799813685248), (102871509852239/1125899906842624)), (35554043/2251799813685248), by norm_num⟩
  | 6 => ⟨((1441875864952239/9007199254740992), (337748118566297/4503599627370496)), (71359627/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7268175/4194304), (-312567865/8388608)), (1/16777216), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-29708395/16777216), (-638804767/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((89100811752501/562949953421312), (-35239197680665/562949953421312)), (131166155/9007199254740992), by norm_num⟩
  | 1 => ⟨((-962988315/2147483648), (380860005/2147483648)), (45/1073741824), by norm_num⟩
  | 2 => ⟨((170521959/268435456), (-67441103/268435456)), (65/1073741824), by norm_num⟩
  | 3 => ⟨((-1288333573/2147483648), (509533421/2147483648)), (125/2147483648), by norm_num⟩
  | 4 => ⟨((114066371/268435456), (-180452111/1073741824)), (45/1073741824), by norm_num⟩
  | 5 => ⟨((-517078983/2147483648), (409007463/4294967296)), (13/536870912), by norm_num⟩
  | 6 => ⟨((976663383/8589934592), (-386268467/8589934592)), (25/2147483648), by norm_num⟩
  | 7 => ⟨((-197649695/4294967296), (312680279/17179869184)), (83/17179869184), by norm_num⟩
  | 8 => ⟨((1119967507/68719476736), (-442944969/68719476736)), (15/8589934592), by norm_num⟩
  | 9 => ⟨((-1410269727/274877906944), (139439733/68719476736)), (153/274877906944), by norm_num⟩
  | 10 => ⟨((399559501/274877906944), (-158025005/274877906944)), (11/68719476736), by norm_num⟩
  | 11 => ⟨((-411649931/1099511627776), (325613493/2199023255552)), (23/549755813888), by norm_num⟩
  | 12 => ⟨((194382013/2199023255552), (-307510831/8796093022208)), (11/1099511627776), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581669156673291/10141204801825835211973625643008), (-490588785427/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779237446390991/633825300114114700748351602688), (-580877475315/633825300114114700748351602688)), (46129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890269063121649/39614081257132168796771975168), (-326692725109/19807040628566084398385987584)), (103793/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472519258586023/618970019642690137449562112), (-5422630043/19342813113834066795298816)), (110285/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110733951519087/9671406556917033397649408), (-693955618701/154742504910672534362390528)), (55145/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1550071365456641/9671406556917033397649408), (-650433591525/9671406556917033397649408)), (51701/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259241817906245/604462909807314587353088), (-284489818275/302231454903657293676544)), (45241/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888528269503705/75557863725914323419136), (-924311212363/75557863725914323419136)), (73521/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81130719841909/295147905179352825856), (-692987894865/4722366482869645213696)), (55145/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((811103516474199/295147905179352825856), (-952459573503/590295810358705651712)), (75831/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824423010600019/73786976294838206464), (-297494151755/18446744073709551616)), (94799/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911861734713517/4611686018427387904), (-668951066995/4611686018427387904)), (106663/4611686018427387904), by norm_num⟩
  | 6 => ⟨((12460714946875/9007199254740992), (-668437979965/576460752303423488)), (213361/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298860672136641/36028797018963968), (-1168613066125/144115188075855872)), (186731/144115188075855872), by norm_num⟩
  | 4 => ⟨((93308078120165/2251799813685248), (-1750615416515/36028797018963968)), (280175/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490870671796759/9007199254740992), (-1092121413807/4503599627370496)), (175179/4503599627370496), by norm_num⟩
  | 2 => ⟨((557792152072815/1125899906842624), (-4356429797749/4503599627370496)), (701137/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110460449356425/1125899906842624), (-1626146761591/562949953421312)), (1052761/2251799813685248), by norm_num⟩
  | 0 => ⟨((1095156438584819/1125899906842624), (-12889434197129/2251799813685248)), (131861/140737488355328), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((1095156438584819/1125899906842624), (-12889434197129/2251799813685248)), (503009796679449037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((532607775925033/562949953421312), (-25074958732853/2251799813685248)), (4128489/2251799813685248), by norm_num⟩
  | 2 => ⟨((2015324766649899/2251799813685248), (-47446910408115/2251799813685248)), (3951943/1125899906842624), by norm_num⟩
  | 3 => ⟨((1802683649361289/2251799813685248), (-84928449736393/2251799813685248)), (905049/140737488355328), by norm_num⟩
  | 4 => ⟨((1439939500125179/2251799813685248), (-2124677207857/35184372088832)), (24277561/2251799813685248), by norm_num⟩
  | 5 => ⟨((228143657605661/562949953421312), (-347814265820599/4503599627370496)), (67962465/4503599627370496), by norm_num⟩
  | 6 => ⟨((89100811752501/562949953421312), (-35239197680665/562949953421312)), (131166155/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-29708395/16777216), (-638804767/16777216)), (1/16777216), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-60615489/33554432), (-1303384555/33554432)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((611305832890371/9007199254740992), (-1347039251446701/9007199254740992)), (202074399/9007199254740992), by norm_num⟩
  | 1 => ⟨((-421262053/2147483648), (232067359/536870912)), (141/2147483648), by norm_num⟩
  | 2 => ⟨((304400985/1073741824), (-1341521881/2147483648)), (103/1073741824), by norm_num⟩
  | 3 => ⟨((-293277337/1073741824), (646249493/1073741824)), (201/2147483648), by norm_num⟩
  | 4 => ⟨((211920133/1073741824), (-466975321/1073741824)), (147/2147483648), by norm_num⟩
  | 5 => ⟨((-245011187/2147483648), (33743307/134217728)), (43/1073741824), by norm_num⟩
  | 6 => ⟨((236057805/4294967296), (-260081871/2147483648)), (21/1073741824), by norm_num⟩
  | 7 => ⟨((-194941375/8589934592), (429561883/8589934592)), (141/17179869184), by norm_num⟩
  | 8 => ⟨((563453045/68719476736), (-1241593535/68719476736)), (103/34359738368), by norm_num⟩
  | 9 => ⟨((-361908615/137438953472), (797481531/137438953472)), (67/68719476736), by norm_num⟩
  | 10 => ⟨((26151261/34359738368), (-461003619/274877906944)), (39/137438953472), by norm_num⟩
  | 11 => ⟨((-439778131/2199023255552), (484535215/1099511627776)), (83/1099511627776), by norm_num⟩
  | 12 => ⟨((211853715/4398046511104), (-466828967/4398046511104)), (81/4398046511104), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197702827769549/1267650600228229401496703205376), (-1491197070155/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111198803910969/39614081257132168796771975168), (-882767575659/316912650057057350374175801344)), (92375/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945102665517659/19807040628566084398385987584), (-992955134327/19807040628566084398385987584)), (25983/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890009221638819/2475880078570760549798248448), (-2109640655957/2475880078570760549798248448)), (13805/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221459412768471/19342813113834066795298816), (-527300784627/38685626227668133590597632)), (110455/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550007572209331/9671406556917033397649408), (-988456595733/4835703278458516698824704)), (103567/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314796470666873/151115727451828646838272), (-864667208481/302231454903657293676544)), (90637/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236054644641045/9444732965739290427392), (-2809297520845/75557863725914323419136)), (147313/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649011496471019/2361183241434822606848), (-2106211363407/4722366482869645213696)), (110511/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622112502877303/590295810358705651712), (-361850404445/73786976294838206464)), (151993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912152192640671/36893488147419103232), (-3616648833463/73786976294838206464)), (47513/18446744073709551616), by norm_num⟩
  | 7 => ⟨((911794690280777/4611686018427387904), (-4066180440063/9223372036854775808)), (106947/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797418315706499/576460752303423488), (-1015748923327/288230376151711744)), (214001/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195323776739711/144115188075855872), (-1775770655997/72057594037927936)), (187371/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492749106203105/36028797018963968), (-2660079712313/18014398509481984)), (17581/2251799813685248), by norm_num⟩
  | 3 => ⟨((1490642394186917/9007199254740992), (-1659424682869/2251799813685248)), (44005/1125899906842624), by norm_num⟩
  | 2 => ⟨((557675699830991/1125899906842624), (-3309490337515/1125899906842624)), (705343/4503599627370496), by norm_num⟩
  | 1 => ⟨((2220199190958881/2251799813685248), (-4940895198687/562949953421312)), (265295/562949953421312), by norm_num⟩
  | 0 => ⟨((547194580409619/562949953421312), (-19577544207923/1125899906842624)), (266883/281474976710656), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((547194580409619/562949953421312), (-19577544207923/1125899906842624)), (1018077851415538699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2126839779992591/2251799813685248), (-38059248511165/1125899906842624)), (4224871/2251799813685248), by norm_num⟩
  | 2 => ⟨((2006241139516083/2251799813685248), (-71894422619829/1125899906842624)), (2066617/562949953421312), by norm_num⟩
  | 3 => ⟨((444569745225047/562949953421312), (-256217355530553/2251799813685248)), (15785733/2251799813685248), by norm_num⟩
  | 4 => ⟨((343794859318385/562949953421312), (-25292320342641/140737488355328)), (28524753/2251799813685248), by norm_num⟩
  | 5 => ⟨((767099676584677/2251799813685248), (-494274542804407/2251799813685248)), (5636599/281474976710656), by norm_num⟩
  | 6 => ⟨((611305832890371/9007199254740992), (-1347039251446701/9007199254740992)), (202074399/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-60615489/33554432), (-1303384555/33554432)), (1/16777216), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-61749361/33554432), (-663882817/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-211716770045119/4503599627370496), (-1365984002558333/9007199254740992)), (246607813/9007199254740992), by norm_num⟩
  | 1 => ⟨((148627069/1073741824), (479466503/1073741824)), (175/2147483648), by norm_num⟩
  | 2 => ⟨((-437623335/2147483648), (-1411759861/2147483648)), (65/536870912), by norm_num⟩
  | 3 => ⟨((214759201/1073741824), (346403397/536870912)), (257/2147483648), by norm_num⟩
  | 4 => ⟨((-316172681/2147483648), (-1019963665/2147483648)), (191/2147483648), by norm_num⟩
  | 5 => ⟨((186190233/2147483648), (1201288309/4294967296)), (227/4294967296), by norm_num⟩
  | 6 => ⟨((-365483853/8589934592), (-1179040041/8589934592)), (225/8589934592), by norm_num⟩
  | 7 => ⟨((76867493/4294967296), (991888987/17179869184)), (191/17179869184), by norm_num⟩
  | 8 => ⟨((-452663285/68719476736), (-730139149/34359738368)), (283/68719476736), by norm_num⟩
  | 9 => ⟨((148093269/68719476736), (955488965/137438953472)), (187/137438953472), by norm_num⟩
  | 10 => ⟨((-348841275/549755813888), (-1125351581/549755813888)), (111/274877906944), by norm_num⟩
  | 11 => ⟨((186753063/1099511627776), (602459829/1099511627776)), (15/137438953472), by norm_num⟩
  | 12 => ⟨((-366588665/8796093022208), (-147825517/1099511627776)), (119/4398046511104), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (-609422834577/2535301200456458802993406410752)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779125960234617/633825300114114700748351602688), (-721499176179/158456325028528675187087900672)), (23121/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890143416234299/39614081257132168796771975168), (-3246214160501/39614081257132168796771975168)), (104063/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889943243690647/2475880078570760549798248448), (-3448454195331/2475880078570760549798248448)), (27647/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771609106697813/154742504910672534362390528), (-861931230089/38685626227668133590597632)), (27653/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549945283015433/9671406556917033397649408), (-1615733700949/4835703278458516698824704)), (25931/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((157391393602043/75557863725914323419136), (-2826759427313/604462909807314587353088)), (2837/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1888347782183225/75557863725914323419136), (-4592032132741/75557863725914323419136)), (73785/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648977791837889/2361183241434822606848), (-1721376999191/2361183241434822606848)), (110719/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622019201401907/590295810358705651712), (-2365861738617/295147905179352825856)), (76153/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824186838900731/73786976294838206464), (-5911560567521/73786976294838206464)), (47621/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823455878250313/9223372036854775808), (-6646253523389/9223372036854775808)), (214433/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398675388350591/288230376151711744), (-830117640781/144115188075855872)), (214607/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195203814378835/144115188075855872), (-5804850815521/144115188075855872)), (187977/144115188075855872), by norm_num⟩
  | 4 => ⟨((746282816674157/18014398509481984), (-8695340325843/36028797018963968)), (141179/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490406896791505/9007199254740992), (-10848308833263/9007199254740992)), (176817/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115106707644341/2251799813685248), (-10817051467429/2251799813685248)), (177333/1125899906842624), by norm_num⟩
  | 1 => ⟨((2219419420195997/2251799813685248), (-16147582529471/1125899906842624)), (66823/140737488355328), by norm_num⟩
  | 0 => ⟨((2187037666278599/2251799813685248), (-63968157800941/2251799813685248)), (269885/281474976710656), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((2187037666278599/2251799813685248), (-63968157800941/2251799813685248)), (1029529572606944949/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2122320909462913/2251799813685248), (-31064211326173/562949953421312)), (2158319/1125899906842624), by norm_num⟩
  | 2 => ⟨((1993430433672577/2251799813685248), (-234224107606137/2251799813685248)), (8613255/2251799813685248), by norm_num⟩
  | 3 => ⟨((1740342963655615/2251799813685248), (-12959340944859/70368744177664)), (17041797/2251799813685248), by norm_num⟩
  | 4 => ⟨((634341122961481/1125899906842624), (-641014646220113/2251799813685248)), (8154763/562949953421312), by norm_num⟩
  | 5 => ⟨((532309691637171/2251799813685248), (-22572052589155/70368744177664)), (27663429/1125899906842624), by norm_num⟩
  | 6 => ⟨((-211716770045119/4503599627370496), (-1365984002558333/9007199254740992)), (246607813/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-663882817/16777216)), (1/16777216), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-62825059/33554432), (-675447919/16777216)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-1157829073926219/9007199254740992), (-380007808462721/4503599627370496)), (31216247/1125899906842624), by norm_num⟩
  | 1 => ⟨((826965791/2147483648), (542832211/2147483648)), (45/536870912), by norm_num⟩
  | 2 => ⟨((-1238684055/2147483648), (-813089987/2147483648)), (17/134217728), by norm_num⟩
  | 3 => ⟨((618460967/1073741824), (811933305/2147483648)), (137/1073741824), by norm_num⟩
  | 4 => ⟨((-926371739/2147483648), (-304041851/1073741824)), (13/134217728), by norm_num⟩
  | 5 => ⟨((555032343/2147483648), (728662389/4294967296)), (63/1073741824), by norm_num⟩
  | 6 => ⟨((-1108485535/8589934592), (-181906453/2147483648)), (127/4294967296), by norm_num⟩
  | 7 => ⟨((474389413/8589934592), (622792037/17179869184)), (55/4294967296), by norm_num⟩
  | 8 => ⟨((-710571837/34359738368), (-466429551/34359738368)), (167/34359738368), by norm_num⟩
  | 9 => ⟨((946081327/137438953472), (38813835/8589934592)), (7/4294967296), by norm_num⟩
  | 10 => ⟨((-566841273/274877906944), (-186041373/137438953472)), (135/274877906944), by norm_num⟩
  | 11 => ⟨((1234985233/2199023255552), (405331015/1099511627776)), (297/2199023255552), by norm_num⟩
  | 12 => ⟨((-1233228373/8796093022208), (-404754401/4398046511104)), (299/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581536844765651/10141204801825835211973625643008), (-3335625572769/10141204801825835211973625643008)), (38821/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889536317874193/316912650057057350374175801344), (-3948857319403/633825300114114700748351602688)), (92589/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236260401758889/4951760157141521099596496896), (-1110428675545/9903520314283042199192993792)), (104187/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944939502151707/1237940039285380274899124224), (-4718418192655/2475880078570760549798248448)), (13841/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771544558604681/154742504910672534362390528), (-4717401585905/154742504910672534362390528)), (13845/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((96867777585939/604462909807314587353088), (-276342747559/604462909807314587353088)), (103873/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629538792399633/302231454903657293676544), (-1933859286703/302231454903657293676544)), (90923/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944130063455015/37778931862957161709568), (-3141509083629/37778931862957161709568)), (147815/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648944652831867/2361183241434822606848), (-2355246229635/2361183241434822606848)), (55459/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621927198111085/590295810358705651712), (-6474049519609/590295810358705651712)), (38151/147573952589676412928), by norm_num⟩
  | 8 => ⟨((456017632448007/18446744073709551616), (-8088246415841/73786976294838206464)), (190893/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455830809659447/2305843009213693952), (-9093344947951/9223372036854775808)), (214945/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594566677710643/1152921504606846976), (-4542965947329/576460752303423488)), (13449/72057594037927936), by norm_num⟩
  | 5 => ⟨((149385410964391/18014398509481984), (-1985463467391/36028797018963968)), (94277/72057594037927936), by norm_num⟩
  | 4 => ⟨((93273739710217/2251799813685248), (-5948057806455/18014398509481984)), (283367/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490165914272211/9007199254740992), (-14840998222911/9007199254740992)), (355149/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114852680374487/2251799813685248), (-14797314492101/2251799813685248)), (356563/2251799813685248), by norm_num⟩
  | 1 => ⟨((554648129641857/562949953421312), (-11043443977541/562949953421312)), (33649/70368744177664), by norm_num⟩
  | 0 => ⟨((546281750406843/562949953421312), (-5467274814809/140737488355328)), (34093/35184372088832), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((546281750406843/562949953421312), (-5467274814809/140737488355328)), (130054474011170853/134217728000000000000000000), by norm_num⟩
  | 1 => ⟨((529257514836619/562949953421312), (-84886336702229/1125899906842624)), (2202111/1125899906842624), by norm_num⟩
  | 2 => ⟨((988763185003993/1125899906842624), (-159611813922589/1125899906842624)), (1118171/281474976710656), by norm_num⟩
  | 3 => ⟨((422851400505833/562949953421312), (-17521349426715/70368744177664)), (9123935/1125899906842624), by norm_num⟩
  | 4 => ⟨((141358440528831/281474976710656), (-842297497892845/2251799813685248)), (4562553/281474976710656), by norm_num⟩
  | 5 => ⟨((252862745143915/2251799813685248), (-1692027648850127/4503599627370496)), (127935637/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1157829073926219/9007199254740992), (-380007808462721/4503599627370496)), (31216247/1125899906842624), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-62825059/33554432), (-675447919/16777216)), (1/16777216), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-63848263/33554432), (-83795/2048)), (1/16777216), by norm_num⟩
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
  | 0 => ⟨((-669816577744863/4503599627370496), (100422640715983/9007199254740992)), (110444907/4503599627370496), by norm_num⟩
  | 1 => ⟨((1944800949/4294967296), (-36446927/1073741824)), (323/4294967296), by norm_num⟩
  | 2 => ⟨((-370061883/536870912), (110963487/2147483648)), (31/268435456), by norm_num⟩
  | 3 => ⟨((187776951/268435456), (-112610275/2147483648)), (127/1073741824), by norm_num⟩
  | 4 => ⟨((-1143382281/2147483648), (85711127/2147483648)), (195/2147483648), by norm_num⟩
  | 5 => ⟨((348105301/1073741824), (-26094945/1073741824)), (239/4294967296), by norm_num⟩
  | 6 => ⟨((-706542933/4294967296), (105928861/8589934592)), (245/8589934592), by norm_num⟩
  | 7 => ⟨((1229191893/17179869184), (-92143655/17179869184)), (215/17179869184), by norm_num⟩
  | 8 => ⟨((-935575575/34359738368), (140266713/68719476736)), (165/34359738368), by norm_num⟩
  | 9 => ⟨((316486759/34359738368), (-94898923/137438953472)), (225/137438953472), by norm_num⟩
  | 10 => ⟨((-1541681663/549755813888), (14446095/68719476736)), (69/137438953472), by norm_num⟩
  | 11 => ⟨((1706794333/2199023255552), (-127946067/2199023255552)), (77/549755813888), by norm_num⟩
  | 12 => ⟨((-433031137/2199023255552), (129844891/8796093022208)), (315/8796093022208), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395374280778559/2535301200456458802993406410752), (3994810079603/10141204801825835211973625643008)), (77643/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444755497528991/158456325028528675187087900672), (591123803185/79228162514264337593543950336)), (46333/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945013020504569/19807040628566084398385987584), (5319191871109/39614081257132168796771975168)), (52139/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472454500617617/618970019642690137449562112), (5650540328841/2475880078570760549798248448)), (110831/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771483269568359/154742504910672534362390528), (5649301554485/154742504910672534362390528)), (55435/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774913338970021/4835703278458516698824704), (1323726016367/2417851639229258349412352)), (51991/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314756684260965/151115727451828646838272), (4631724977891/604462909807314587353088)), (45513/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888176928355513/75557863725914323419136), (1881021393379/18889465931478580854784)), (73997/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297826407618647/4722366482869645213696), (5640905237961/4722366482869645213696)), (13883/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810919951532391/295147905179352825856), (7752736673635/590295810358705651712)), (76411/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823960197120881/73786976294838206464), (9685659243709/73786976294838206464)), (95597/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56974920241821/288230376151711744), (1361141584851/1152921504606846976)), (215321/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797219403565207/576460752303423488), (10880091315639/1152921504606846976)), (215607/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194969066298561/144115188075855872), (9509909894061/144115188075855872)), (188977/144115188075855872), by norm_num⟩
  | 4 => ⟨((746101923184431/18014398509481984), (7122264342785/18014398509481984)), (284109/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489937806495849/9007199254740992), (8885040691955/4503599627370496)), (44533/1125899906842624), by norm_num⟩
  | 2 => ⟨((557306223114377/1125899906842624), (17716730064273/2251799813685248)), (178979/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108905787681625/1125899906842624), (13220890360453/562949953421312)), (541181/1125899906842624), by norm_num⟩
  | 0 => ⟨((136457905946519/140737488355328), (26175348956163/562949953421312)), (549699/562949953421312), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((136457905946519/140737488355328), (26175348956163/562949953421312)), (2096935274364280523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((66002095485011/70368744177664), (101517608356329/1125899906842624)), (558543/281474976710656), by norm_num⟩
  | 2 => ⟨((981349212511885/1125899906842624), (95218053959121/562949953421312)), (4593959/1125899906842624), by norm_num⟩
  | 3 => ⟨((411573160307665/562949953421312), (331973248072251/1125899906842624)), (37353/4398046511104), by norm_num⟩
  | 4 => ⟨((1007840260504117/2251799813685248), (970823626621331/2251799813685248)), (19621067/1125899906842624), by norm_num⟩
  | 5 => ⟨((16263318844259/1125899906842624), (1738049947088871/4503599627370496)), (68964385/2251799813685248), by norm_num⟩
  | 6 => ⟨((-669816577744863/4503599627370496), (100422640715983/9007199254740992)), (110444907/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-63848263/33554432), (-83795/2048)), (1/16777216), by norm_num⟩, -7, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile035Terms2
