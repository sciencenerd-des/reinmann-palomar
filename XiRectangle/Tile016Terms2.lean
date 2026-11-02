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
namespace Reinmann.XiRectangle.Tile016Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨16,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (4653/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (4653/640))
  have he : value ((3/4), (4653/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1116391677/536870912), (-21644043637/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((292455213869709/9007199254740992), (-543626836117649/4503599627370496)), (5170909/9007199254740992), by norm_num⟩
  | 1 => ⟨((-6186355803/68719476736), (22998865279/68719476736)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4288055083/34359738368), (-15941598625/34359738368)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((-990751097/8589934592), (14733165521/34359738368)), (75/34359738368), by norm_num⟩
  | 4 => ⟨((1373472659/17179869184), (-5106126071/17179869184)), (53/34359738368), by norm_num⟩
  | 5 => ⟨((-761614961/17179869184), (11325750047/68719476736)), (15/17179869184), by norm_num⟩
  | 6 => ⟨((5631053471/274877906944), (-20934431235/274877906944)), (113/274877906944), by norm_num⟩
  | 7 => ⟨((-557592691/68719476736), (16583590843/549755813888)), (91/549755813888), by norm_num⟩
  | 8 => ⟨((6183900827/2199023255552), (-22989738473/2199023255552)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-952522983/1099511627776), (7082343291/2199023255552)), (5/274877906944), by norm_num⟩
  | 10 => ⟨((4225527169/17592186044416), (-15709140109/17592186044416)), (91/17592186044416), by norm_num⟩
  | 11 => ⟨((-4260235991/70368744177664), (15466969/68719476736)), (47/35184372088832), by norm_num⟩
  | 12 => ⟨((492161761/35184372088832), (-3659395739/70368744177664)), (89/281474976710656), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326325/10141204801825835211973625643008), (-851927899653/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889379737593709/316912650057057350374175801344), (-2016408705953/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889731323307877/39614081257132168796771975168), (-2268045589445/39614081257132168796771975168)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472376412706931/618970019642690137449562112), (-1204643546875/1237940039285380274899124224)), (3453/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771171801551327/154742504910672534362390528), (-1204356002957/77371252455336267181195264)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549535615008399/9671406556917033397649408), (-1128778321823/4835703278458516698824704)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629386497365373/302231454903657293676544), (-987375695659/302231454903657293676544)), (1417/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887766354144895/75557863725914323419136), (-3207826404815/75557863725914323419136)), (2303/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648760006570645/2361183241434822606848), (-2404868676845/4722366482869645213696)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((810710552317083/295147905179352825856), (-3305068356039/590295810358705651712)), (4753/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911720217995919/36893488147419103232), (-4128897656193/73786976294838206464)), (5943/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822617848132963/9223372036854775808), (-4641660052473/9223372036854775808)), (6689/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796932806116793/576460752303423488), (-4637476010567/1152921504606846976)), (6693/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194474712494811/144115188075855872), (-253318055541/9007199254740992)), (5861/144115188075855872), by norm_num⟩
  | 4 => ⟨((372869166309085/9007199254740992), (-5927967919/35184372088832)), (8799/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489053865655717/9007199254740992), (-1892845992045/2251799813685248)), (11013/9007199254740992), by norm_num⟩
  | 2 => ⟨((556882953289345/1125899906842624), (-3773405580377/1125899906842624)), (22071/4503599627370496), by norm_num⟩
  | 1 => ⟨((2215457898789301/2251799813685248), (-22517916394869/2251799813685248)), (33219/2251799813685248), by norm_num⟩
  | 0 => ⟨((2179356543203437/2251799813685248), (-44547841632753/2251799813685248)), (16723/562949953421312), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((2179356543203437/2251799813685248), (-44547841632753/2251799813685248)), (63793184520530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1054181282757915/1125899906842624), (-21557340390095/562949953421312)), (132127/2251799813685248), by norm_num⟩
  | 2 => ⟨((1970760090618643/2251799813685248), (-80736643132011/1125899906842624)), (128771/1125899906842624), by norm_num⟩
  | 3 => ⟨((856608498045097/1125899906842624), (-17665042110769/140737488355328)), (487735/2251799813685248), by norm_num⟩
  | 4 => ⟨((1267975380346551/2251799813685248), (-430078023055365/2251799813685248)), (432299/1125899906842624), by norm_num⟩
  | 5 => ⟨((1263695334374555/4503599627370496), (-968697735114999/4503599627370496)), (1303965/2251799813685248), by norm_num⟩
  | 6 => ⟨((292455213869709/9007199254740992), (-543626836117649/4503599627370496)), (5170909/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/536870912), (-21644043637/1073741824)), (1/536870912), by norm_num⟩, -3, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-570401187/268435456), (-22117306025/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-190486038263331/9007199254740992), (-1058855756826175/9007199254740992)), (1418557/2251799813685248), by norm_num⟩
  | 1 => ⟨((4117489513/68719476736), (22887910917/68719476736)), (31/17179869184), by norm_num⟩
  | 2 => ⟨((-1458215779/17179869184), (-16211583657/34359738368)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((344286367/4294967296), (15310291715/34359738368)), (43/17179869184), by norm_num⟩
  | 4 => ⟨((-3901746917/68719476736), (-21688661395/68719476736)), (31/17179869184), by norm_num⟩
  | 5 => ⟨((1105448143/34359738368), (768107561/4294967296)), (71/68719476736), by norm_num⟩
  | 6 => ⟨((-4175960573/274877906944), (-11606467155/137438953472)), (17/34359738368), by norm_num⟩
  | 7 => ⟨((3380396349/549755813888), (4697656803/137438953472)), (7/34359738368), by norm_num⟩
  | 8 => ⟨((-2394346011/1099511627776), (-26618927881/2199023255552)), (161/2199023255552), by norm_num⟩
  | 9 => ⟨((3014974697/4398046511104), (2094919491/549755813888)), (103/4398046511104), by norm_num⟩
  | 10 => ⟨((-3416826617/17592186044416), (-18993132341/17592186044416)), (119/17592186044416), by norm_num⟩
  | 11 => ⟨((3520217733/70368744177664), (19567853089/70368744177664)), (31/17592186044416), by norm_num⟩
  | 12 => ⟨((-3324509285/281474976710656), (-2309995937/35184372088832)), (119/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-2277994839633/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778687671501043/633825300114114700748351602688), (-1347832352015/316912650057057350374175801344)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889650462450857/39614081257132168796771975168), (-3032054690173/39614081257132168796771975168)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472354907062757/618970019642690137449562112), (-3220859253457/2475880078570760549798248448)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1771085657683371/154742504910672534362390528), (-3220073244321/154742504910672534362390528)), (3457/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549454726354027/9671406556917033397649408), (-1508991871323/4835703278458516698824704)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314675522121389/151115727451828646838272), (-2639901087969/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887650890459471/75557863725914323419136), (-4288274733773/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648716602346937/2361183241434822606848), (-200927349155/295147905179352825856)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621301401078263/590295810358705651712), (-4418178871601/590295810358705651712)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823290294369823/73786976294838206464), (-1379847756563/18446744073709551616)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822448235756125/9223372036854775808), (-3102367656435/4611686018427387904)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796847561413451/576460752303423488), (-3099507423025/576460752303423488)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194324550056867/144115188075855872), (-5417707994061/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((186406182410531/4503599627370496), (-8113715813907/36028797018963968)), (8819/36028797018963968), by norm_num⟩
  | 3 => ⟨((1453873474551/8796093022208), (-316240469445/281474976710656)), (11043/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226946751732111/4503599627370496), (-1260760310711/281474976710656)), (22147/4503599627370496), by norm_num⟩
  | 1 => ⟨((2214554982980205/2251799813685248), (-15045309451803/1125899906842624)), (33371/2251799813685248), by norm_num⟩
  | 0 => ⟨((272181320002625/281474976710656), (-29756662426135/1125899906842624)), (67349/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((272181320002625/281474976710656), (-29756662426135/1125899906842624)), (256916054732512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2103983256729689/2251799813685248), (-14387082917043/281474976710656)), (33453/562949953421312), by norm_num⟩
  | 2 => ⟨((1959986973915177/2251799813685248), (-215082576251577/2251799813685248)), (32967/281474976710656), by norm_num⟩
  | 3 => ⟨((842723318530449/1125899906842624), (-374419648857945/2251799813685248)), (127375/562949953421312), by norm_num⟩
  | 4 => ⟨((1199280804855089/2251799813685248), (-280248863234587/1125899906842624)), (466073/1125899906842624), by norm_num⟩
  | 5 => ⟨((499208118183939/2251799813685248), (-1194056701548971/4503599627370496)), (728471/1125899906842624), by norm_num⟩
  | 6 => ⟨((-190486038263331/9007199254740992), (-1058855756826175/9007199254740992)), (1418557/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-22117306025/1073741824)), (1/536870912), by norm_num⟩, -3, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-2327634783/1073741824), (-22563509673/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-576485359012369/9007199254740992), (-427206730100961/4503599627370496)), (5813551/9007199254740992), by norm_num⟩
  | 1 => ⟨((794533253/4294967296), (18841343193/68719476736)), (131/68719476736), by norm_num⟩
  | 2 => ⟨((-9185985901/34359738368), (-6807310781/17179869184)), (97/34359738368), by norm_num⟩
  | 3 => ⟨((8850304739/34359738368), (6558552943/17179869184)), (95/34359738368), by norm_num⟩
  | 4 => ⟨((-12790335433/68719476736), (-18956656199/68719476736)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((3696882431/34359738368), (2739589185/17179869184)), (83/68719476736), by norm_num⟩
  | 6 => ⟨((-7123576381/137438953472), (-5278954139/68719476736)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((5882795425/274877906944), (8718937117/274877906944)), (69/274877906944), by norm_num⟩
  | 8 => ⟨((-8501732877/1099511627776), (-12600484801/1099511627776)), (101/1099511627776), by norm_num⟩
  | 9 => ⟨((10921408267/4398046511104), (1011669039/274877906944)), (33/1099511627776), by norm_num⟩
  | 10 => ⟨((-12626772005/17592186044416), (-2339279695/2199023255552)), (155/17592186044416), by norm_num⟩
  | 11 => ⟨((13271296435/70368744177664), (4917373065/17592186044416)), (165/70368744177664), by norm_num⟩
  | 12 => ⟨((-6393163401/140737488355328), (-9475357487/140737488355328)), (161/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290011/2535301200456458802993406410752), (-2819307525257/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889309762664539/316912650057057350374175801344), (-3335990898865/633825300114114700748351602688)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889573696241459/39614081257132168796771975168), (-3752269021789/39614081257132168796771975168)), (3255/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944668964784243/1237940039285380274899124224), (-3985903065597/2475880078570760549798248448)), (3459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885501903866565/77371252455336267181195264), (-1992455073555/77371252455336267181195264)), (865/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549377831422299/9671406556917033397649408), (-466849815251/1208925819614629174706176)), (811/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((4916541581837/2361183241434822606848), (-1633447114993/302231454903657293676544)), (355/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1887540994116577/75557863725914323419136), (-5306726541073/75557863725914323419136)), (577/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162168814962059/590295810358705651712), (-3978315957269/4722366482869645213696)), (433/590295810358705651712), by norm_num⟩
  | 9 => ⟨((202648410348045/73786976294838206464), (-5467375952275/590295810358705651712)), (4765/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823147007796235/73786976294838206464), (-6830009048571/73786976294838206464)), (5959/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455571540411419/2305843009213693952), (-7677973196151/9223372036854775808)), (6709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398382988769753/288230376151711744), (-7670743955753/1152921504606846976)), (6715/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194180551034307/144115188075855872), (-6703774238039/144115188075855872)), (5883/144115188075855872), by norm_num⟩
  | 4 => ⟨((745515507000151/18014398509481984), (-5019711670335/18014398509481984)), (4419/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488489116898261/9007199254740992), (-12520897363695/9007199254740992)), (173/140737488355328), by norm_num⟩
  | 2 => ⟨((69574355802681/140737488355328), (-12478394075343/2251799813685248)), (11109/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106836183016549/1125899906842624), (-18611575880911/1125899906842624)), (16757/1125899906842624), by norm_num⟩
  | 0 => ⟨((1087780250627807/1125899906842624), (-36800548627451/1125899906842624)), (67779/2251799813685248), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1087780250627807/1125899906842624), (-36800548627451/1125899906842624)), (258556374556731467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099496742283359/2251799813685248), (-71109180782275/1125899906842624)), (16925/281474976710656), by norm_num⟩
  | 2 => ⟨((487128172076671/562949953421312), (-265198518076959/2251799813685248)), (67397/562949953421312), by norm_num⟩
  | 3 => ⟨((827420674754259/1125899906842624), (-458959694598601/2251799813685248)), (530057/2251799813685248), by norm_num⟩
  | 4 => ⟨((1122593525150043/2251799813685248), (-168644094329277/562949953421312)), (995147/2251799813685248), by norm_num⟩
  | 5 => ⟨((357564171104897/2251799813685248), (-672595377966585/2251799813685248)), (3176923/4503599627370496), by norm_num⟩
  | 6 => ⟨((-576485359012369/9007199254740992), (-427206730100961/4503599627370496)), (5813551/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2327634783/1073741824), (-22563509673/1073741824)), (1/536870912), by norm_num⟩, -3, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-592793865/268435456), (-5746395529/268435456)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-206406288758337/2251799813685248), (-272921197984467/4503599627370496)), (2804105/4503599627370496), by norm_num⟩
  | 1 => ⟨((1159192509/4294967296), (6130980023/34359738368)), (1/536870912), by norm_num⟩
  | 2 => ⟨((-13652686431/34359738368), (-1128268535/4294967296)), (3/1073741824), by norm_num⟩
  | 3 => ⟨((837489627/2147483648), (4429490471/17179869184)), (3/1073741824), by norm_num⟩
  | 4 => ⟨((-19727496819/68719476736), (-13042364401/68719476736)), (9/4294967296), by norm_num⟩
  | 5 => ⟨((11617282119/68719476736), (7680489225/68719476736)), (87/68719476736), by norm_num⟩
  | 6 => ⟨((-11402126101/137438953472), (-7538243951/137438953472)), (87/137438953472), by norm_num⟩
  | 7 => ⟨((19184494021/549755813888), (6341685521/274877906944)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((-7060946499/549755813888), (-9336353021/1099511627776)), (111/1099511627776), by norm_num⟩
  | 9 => ⟨((9240233823/2199023255552), (12217920781/4398046511104)), (37/1099511627776), by norm_num⟩
  | 10 => ⟨((-5441460929/4398046511104), (-3597492219/4398046511104)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((11652399755/35184372088832), (1925926603/8796093022208)), (97/35184372088832), by norm_num⟩
  | 12 => ⟨((-5718296673/70368744177664), (-1890257787/35184372088832)), (97/140737488355328), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-3331345400053/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889277332266071/316912650057057350374175801344), (-3941604093351/633825300114114700748351602688)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889500609646431/39614081257132168796771975168), (-4433432270499/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889260118442421/2475880078570760549798248448), (-4709458628387/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442731455142969/38685626227668133590597632), (-2354131366029/77371252455336267181195264)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549304531561773/9671406556917033397649408), (-2206362955675/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258570320833485/604462909807314587353088), (-3859865041965/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887436117627147/75557863725914323419136), (-3134949885693/37778931862957161709568)), (4621/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648635778295089/2361183241434822606848), (-4700342094947/4722366482869645213696)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405269553078903/147573952589676412928), (-6459587013183/590295810358705651712)), (2385/295147905179352825856), by norm_num⟩
  | 8 => ⟨((227876240814161/9223372036854775808), (-8069410596911/73786976294838206464)), (5967/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822130925091565/9223372036854775808), (-9071114372141/9223372036854775808)), (3359/4611686018427387904), by norm_num⟩
  | 6 => ⟨((99585965378851/72057594037927936), (-4531201637971/576460752303423488)), (3363/576460752303423488), by norm_num⟩
  | 5 => ⟨((597021088898671/72057594037927936), (-7919809199043/144115188075855872)), (5893/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490820607625613/36028797018963968), (-11860142264755/36028797018963968)), (1107/4503599627370496), by norm_num⟩
  | 3 => ⟨((744110574065297/4503599627370496), (-3697740807599/2251799813685248)), (11099/9007199254740992), by norm_num⟩
  | 2 => ⟨((556457162006643/1125899906842624), (-14739712574709/2251799813685248)), (11143/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106404773229035/1125899906842624), (-5495422982157/281474976710656)), (16825/1125899906842624), by norm_num⟩
  | 0 => ⟨((1086844863608099/1125899906842624), (-43453377113563/1125899906842624)), (17047/562949953421312), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1086844863608099/1125899906842624), (-43453377113563/1125899906842624)), (65029146434593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1047467500797635/1125899906842624), (-83892146069611/1125899906842624)), (8557/140737488355328), by norm_num⟩
  | 2 => ⟨((1936495893515439/2251799813685248), (-156096107737521/1125899906842624)), (275153/2251799813685248), by norm_num⟩
  | 3 => ⟨((1622059094241265/2251799813685248), (-67119525854465/281474976710656)), (274773/1125899906842624), by norm_num⟩
  | 4 => ⟨((1040391656004841/2251799813685248), (-386790465659447/1125899906842624)), (1053805/2251799813685248), by norm_num⟩
  | 5 => ⟨((429867111315019/4503599627370496), (-178707525708395/562949953421312)), (1697819/2251799813685248), by norm_num⟩
  | 6 => ⟨((-206406288758337/2251799813685248), (-272921197984467/4503599627370496)), (2804105/4503599627370496), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-5746395529/268435456)), (1/536870912), by norm_num⟩, -3, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-2412482277/1073741824), (-11693000035/536870912)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-931225452988609/9007199254740992), (-199689978846529/9007199254740992)), (5106751/9007199254740992), by norm_num⟩
  | 1 => ⟨((21283738277/68719476736), (2282019479/34359738368)), (119/68719476736), by norm_num⟩
  | 2 => ⟨((-15940095415/34359738368), (-3418159701/34359738368)), (91/34359738368), by norm_num⟩
  | 3 => ⟨((7958709713/17179869184), (3413297111/34359738368)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((-23842163543/68719476736), (-5112662157/68719476736)), (35/17179869184), by norm_num⟩
  | 5 => ⟨((14284947759/68719476736), (1531616703/34359738368)), (43/34359738368), by norm_num⟩
  | 6 => ⟨((-14264626343/137438953472), (-3058875725/137438953472)), (11/17179869184), by norm_num⟩
  | 7 => ⟨((24418858003/549755813888), (2618163637/274877906944)), (153/549755813888), by norm_num⟩
  | 8 => ⟨((-18288090251/1099511627776), (-980414663/274877906944)), (117/1099511627776), by norm_num⟩
  | 9 => ⟨((24349432083/4398046511104), (5221439729/4398046511104)), (79/2199023255552), by norm_num⟩
  | 10 => ⟨((-14588875907/8796093022208), (-1564203551/4398046511104)), (3/274877906944), by norm_num⟩
  | 11 => ⟨((15892496869/35184372088832), (3407952771/35184372088832)), (53/17592186044416), by norm_num⟩
  | 12 => ⟨((-15869888593/140737488355328), (-3403104701/140737488355328)), (27/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060283875/10141204801825835211973625643008), (-3817113096089/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222311596489363/79228162514264337593543950336), (-1129017810425/158456325028528675187087900672)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((236178856091715/4951760157141521099596496896), (-5079557107513/39614081257132168796771975168)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944592911282955/1237940039285380274899124224), (-5395789318003/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770851328101803/154742504910672534362390528), (-5394394275367/154742504910672534362390528)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((48413577692205/302231454903657293676544), (-2527881312559/4835703278458516698824704)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258508822558143/604462909807314587353088), (-2211155270593/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887335792298543/75557863725914323419136), (-7183476873725/75557863725914323419136)), (289/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((40537374099175/147573952589676412928), (-2692588827947/2361183241434822606848)), (1735/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810486864138139/295147905179352825856), (-7400671535319/590295810358705651712)), (2387/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911439245789683/36893488147419103232), (-2311229892945/18446744073709551616)), (5973/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821981921733391/9223372036854775808), (-10392397599559/9223372036854775808)), (3363/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796612510965087/576460752303423488), (-10382230764321/1152921504606846976)), (6735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596954481250167/72057594037927936), (-9073020169367/144115188075855872)), (5903/144115188075855872), by norm_num⟩
  | 4 => ⟨((745308803387075/18014398509481984), (-13586681634745/36028797018963968)), (8873/36028797018963968), by norm_num⟩
  | 3 => ⟨((743980929614501/4503599627370496), (-16943400517901/9007199254740992)), (11125/9007199254740992), by norm_num⟩
  | 2 => ⟨((278161693817721/562949953421312), (-16883540543581/2251799813685248)), (1397/281474976710656), by norm_num⟩
  | 1 => ⟨((276495741087541/281474976710656), (-25175897362485/1125899906842624)), (8445/562949953421312), by norm_num⟩
  | 0 => ⟨((1085920282875769/1125899906842624), (-49755566836589/1125899906842624)), (2143/70368744177664), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1085920282875769/1125899906842624), (-49755566836589/1125899906842624)), (8174896508669831/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1045161507855283/1125899906842624), (-95977588923249/1125899906842624)), (17293/281474976710656), by norm_num⟩
  | 2 => ⟨((962031236830193/1125899906842624), (-178190052152405/1125899906842624)), (140217/1125899906842624), by norm_num⟩
  | 3 => ⟨((793811599520703/1125899906842624), (-304510898741865/1125899906842624)), (568003/2251799813685248), by norm_num⟩
  | 4 => ⟨((954631872362623/2251799813685248), (-107347146106281/281474976710656)), (554091/1125899906842624), by norm_num⟩
  | 5 => ⟨((77193267774387/2251799813685248), (-1456285859265777/4503599627370496)), (3569745/4503599627370496), by norm_num⟩
  | 6 => ⟨((-931225452988609/9007199254740992), (-199689978846529/9007199254740992)), (5106751/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2412482277/1073741824), (-11693000035/536870912)), (1/536870912), by norm_num⟩, -3, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-2451773307/1073741824), (-23766877491/1073741824)), (1/536870912), by norm_num⟩
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
  | 0 => ⟨((-1817479444501161/18014398509481984), (262578053380879/18014398509481984)), (2420977/4503599627370496), by norm_num⟩
  | 1 => ⟨((21108081623/68719476736), (-190597719/4294967296)), (57/34359738368), by norm_num⟩
  | 2 => ⟨((-8033003515/17179869184), (72534879/1073741824)), (89/34359738368), by norm_num⟩
  | 3 => ⟨((16304439629/34359738368), (-2355563377/34359738368)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((-24819616143/68719476736), (3585782777/68719476736)), (71/34359738368), by norm_num⟩
  | 5 => ⟨((15112775649/68719476736), (-272924903/8589934592)), (11/8589934592), by norm_num⟩
  | 6 => ⟨((-958566345/8589934592), (2215802643/137438953472)), (91/137438953472), by norm_num⟩
  | 7 => ⟨((3335287709/68719476736), (-1927445961/274877906944)), (161/549755813888), by norm_num⟩
  | 8 => ⟨((-20308716533/1099511627776), (1467038119/549755813888)), (31/274877906944), by norm_num⟩
  | 9 => ⟨((13740076259/2199023255552), (-1985080209/2199023255552)), (85/2199023255552), by norm_num⟩
  | 10 => ⟨((-16732788187/8796093022208), (2417448495/8796093022208)), (105/8796093022208), by norm_num⟩
  | 11 => ⟨((18524854211/35184372088832), (-83636093/1099511627776)), (59/17592186044416), by norm_num⟩
  | 12 => ⟨((-4699944525/35184372088832), (2716074259/140737488355328)), (61/70368744177664), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394306545/10141204801825835211973625643008), (3905375221341/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778435868446719/633825300114114700748351602688), (2310108039753/316912650057057350374175801344)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944683408732103/19807040628566084398385987584), (2598339652933/19807040628566084398385987584)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889117767538747/2475880078570760549798248448), (5520182317555/2475880078570760549798248448)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1770783248590349/154742504910672534362390528), (2759365883569/77371252455336267181195264)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549170635629751/9671406556917033397649408), (2586135027711/4835703278458516698824704)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629226463706897/302231454903657293676544), (2262097792143/302231454903657293676544)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943622457069677/37778931862957161709568), (7348929542637/75557863725914323419136)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((40535242817455/147573952589676412928), (2754585234083/2361183241434822606848)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810439941573715/295147905179352825856), (473187785705/36893488147419103232)), (597/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911380541173941/36893488147419103232), (9457600314477/73786976294838206464)), (2987/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821849695423331/9223372036854775808), (5315669831713/4611686018427387904)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593092620143659/1152921504606846976), (5310384141641/576460752303423488)), (6737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596896457229447/72057594037927936), (4640642809901/72057594037927936)), (5905/144115188075855872), by norm_num⟩
  | 4 => ⟨((745221572041725/18014398509481984), (13898170642149/36028797018963968)), (2219/9007199254740992), by norm_num⟩
  | 3 => ⟨((743871551246289/4503599627370496), (17331172066769/9007199254740992)), (5565/4503599627370496), by norm_num⟩
  | 2 => ⟨((556213505700627/1125899906842624), (8634465108255/1125899906842624)), (5591/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105650837081581/1125899906842624), (804626146631/35184372088832)), (8451/562949953421312), by norm_num⟩
  | 0 => ⟨((542623159854005/562949953421312), (50876122604635/1125899906842624)), (34323/1125899906842624), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((542623159854005/562949953421312), (50876122604635/1125899906842624)), (130931858543014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1043761694486721/1125899906842624), (49039105947285/562949953421312)), (34635/562949953421312), by norm_num⟩
  | 2 => ⟨((479536028321339/562949953421312), (181846148164951/1125899906842624)), (70251/562949953421312), by norm_num⟩
  | 3 => ⟨((1575186538059347/2251799813685248), (77450738850397/281474976710656)), (284753/1125899906842624), by norm_num⟩
  | 4 => ⟨((465694404146157/1125899906842624), (866857598679583/2251799813685248)), (1110177/2251799813685248), by norm_num⟩
  | 5 => ⟨((103066902411481/4503599627370496), (179274698595869/562949953421312)), (1773135/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1817479444501161/18014398509481984), (262578053380879/18014398509481984)), (2420977/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2451773307/1073741824), (-23766877491/1073741824)), (1/536870912), by norm_num⟩, -4, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨16,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile016Terms2
