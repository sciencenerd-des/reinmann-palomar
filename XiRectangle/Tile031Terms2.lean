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
namespace Reinmann.XiRectangle.Tile031Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8037/640))
  have he : value ((5/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-232581599/134217728), (-4673145785/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-192336706661389/1125899906842624), (204770026745025/4503599627370496)), (34248009/4503599627370496), by norm_num⟩
  | 1 => ⟨((1017132919/2147483648), (-541441981/4294967296)), (183/8589934592), by norm_num⟩
  | 2 => ⟨((-5640182521/8589934592), (750597965/4294967296)), (1/33554432), by norm_num⟩
  | 3 => ⟨((5212635483/8589934592), (-1387399635/8589934592)), (239/8589934592), by norm_num⟩
  | 4 => ⟨((-3613123589/8589934592), (961672145/8589934592)), (21/1073741824), by norm_num⟩
  | 5 => ⟨((2003541143/8589934592), (-533264269/8589934592)), (47/4294967296), by norm_num⟩
  | 6 => ⟨((-3703330385/34359738368), (492840833/17179869184)), (11/2147483648), by norm_num⟩
  | 7 => ⟨((2933660589/68719476736), (-1561651355/137438953472)), (281/137438953472), by norm_num⟩
  | 8 => ⟨((-1016729283/68719476736), (541227117/137438953472)), (197/274877906944), by norm_num⟩
  | 9 => ⟨((5011506033/1099511627776), (-1333866845/1099511627776)), (245/1099511627776), by norm_num⟩
  | 10 => ⟨((-1389484511/1099511627776), (1479305669/4398046511104)), (137/2199023255552), by norm_num⟩
  | 11 => ⟨((5603591397/17592186044416), (-1491456805/17592186044416)), (279/17592186044416), by norm_num⟩
  | 12 => ⟨((-647352263/8796093022208), (1378398773/70368744177664)), (65/17592186044416), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790859256563237/5070602400912917605986812821504), (1876713331639/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444821376716755/158456325028528675187087900672), (4444490661153/633825300114114700748351602688)), (2895/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1890322524880101/39614081257132168796771975168), (4999260550925/39614081257132168796771975168)), (13031/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890133060975525/2475880078570760549798248448), (5310771941521/2475880078570760549798248448)), (27699/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442949594473365/38685626227668133590597632), (663713955917/19342813113834066795298816)), (27709/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550122144827595/9671406556917033397649408), (622091016703/1208925819614629174706176)), (12993/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259285323289685/604462909807314587353088), (1088377652771/151115727451828646838272)), (5687/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944298614806167/37778931862957161709568), (1768085652145/18889465931478580854784)), (36983/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((649070859800837/2361183241434822606848), (5302408903317/4722366482869645213696)), (27753/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((6337006235959/2305843009213693952), (910976159719/73786976294838206464)), (19093/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824502522053191/73786976294838206464), (2276314341587/18446744073709551616)), (11943/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823807848357633/9223372036854775808), (2559305393515/2305843009213693952)), (13449/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797524781083455/576460752303423488), (639342556787/72057594037927936)), (6733/144115188075855872), by norm_num⟩
  | 5 => ⟨((597751936518379/72057594037927936), (4471044148917/72057594037927936)), (23603/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493006842053751/36028797018963968), (13395719364563/36028797018963968)), (4435/2251799813685248), by norm_num⟩
  | 3 => ⟨((372735727768613/2251799813685248), (1044636294143/562949953421312)), (22241/2251799813685248), by norm_num⟩
  | 2 => ⟨((1115619561259045/2251799813685248), (8334243487751/1125899906842624)), (44681/1125899906842624), by norm_num⟩
  | 1 => ⟨((277605345848693/281474976710656), (24888528730607/1125899906842624)), (67519/562949953421312), by norm_num⟩
  | 0 => ⟨((273678379101941/281474976710656), (24660227155305/562949953421312)), (34259/140737488355328), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((273678379101941/281474976710656), (24660227155305/562949953421312)), (130687714159917787/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((531115229925859/562949953421312), (95908646303393/1125899906842624)), (556973/1125899906842624), by norm_num⟩
  | 2 => ⟨((993991628029749/1125899906842624), (180970057546775/1125899906842624)), (286461/281474976710656), by norm_num⟩
  | 3 => ⟨((848449483883183/1125899906842624), (319535903737667/1125899906842624)), (2391551/1125899906842624), by norm_num⟩
  | 4 => ⟨((548684060785291/1125899906842624), (963176463416353/2251799813685248)), (1240473/281474976710656), by norm_num⟩
  | 5 => ⟨((245588344825011/4503599627370496), (1877536608674645/4503599627370496)), (36323655/4503599627370496), by norm_num⟩
  | 6 => ⟨((-192336706661389/1125899906842624), (204770026745025/4503599627370496)), (34248009/4503599627370496), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-232581599/134217728), (-4673145785/134217728)), (1/67108864), by norm_num⟩, -6, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-237667161/134217728), (-4775327437/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((-800465929464667/9007199254740992), (653744545297729/4503599627370496)), (34230317/4503599627370496), by norm_num⟩
  | 1 => ⟨((540707291/2147483648), (-3532786883/8589934592)), (187/8589934592), by norm_num⟩
  | 2 => ⟨((-191492389/536870912), (2502284735/4294967296)), (267/8589934592), by norm_num⟩
  | 3 => ⟨((2893540223/8589934592), (-1181584417/2147483648)), (127/4294967296), by norm_num⟩
  | 4 => ⟨((-2049504193/8589934592), (1673840369/4294967296)), (91/4294967296), by norm_num⟩
  | 5 => ⟨((2322673051/17179869184), (-474234687/2147483648)), (209/17179869184), by norm_num⟩
  | 6 => ⟨((-2193542761/34359738368), (3582954783/34359738368)), (199/34359738368), by norm_num⟩
  | 7 => ⟨((443912473/17179869184), (-725091093/17179869184)), (163/68719476736), by norm_num⟩
  | 8 => ⟨((-628849371/68719476736), (4108675521/274877906944)), (233/274877906944), by norm_num⟩
  | 9 => ⟨((1583701715/549755813888), (-646708573/137438953472)), (37/137438953472), by norm_num⟩
  | 10 => ⟨((-1794785933/2199023255552), (1465810687/1099511627776)), (169/2199023255552), by norm_num⟩
  | 11 => ⟨((1849095075/8796093022208), (-377541309/1099511627776)), (11/549755813888), by norm_num⟩
  | 12 => ⟨((-873146807/17592186044416), (713103383/8796093022208)), (21/4398046511104), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790834578331793/5070602400912917605986812821504), (1380865978409/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779231908761841/633825300114114700748351602688), (102187662955/19807040628566084398385987584)), (23131/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890262515915633/39614081257132168796771975168), (57471434923/618970019642690137449562112)), (6507/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((945034835229379/1237940039285380274899124224), (976837579343/618970019642690137449562112)), (6915/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771735402300949/154742504910672534362390528), (3906554730473/154742504910672534362390528)), (27667/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775031772920313/4835703278458516698824704), (1830774934741/4835703278458516698824704)), (25945/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259234489553135/604462909807314587353088), (3203011081159/604462909807314587353088)), (22709/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944257724978905/37778931862957161709568), (650413602235/9444732965739290427392)), (36915/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324520276585679/1180591620717411303424), (3901095736571/4722366482869645213696)), (13849/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1622191424571179/590295810358705651712), (1340438782283/147573952589676412928)), (4763/73786976294838206464), by norm_num⟩
  | 8 => ⟨((456100390646451/18446744073709551616), (6698817595953/73786976294838206464)), (47659/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823696679654507/9223372036854775808), (941441112769/1152921504606846976)), (53655/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594941402524735/1152921504606846976), (58794766387/9007199254740992)), (53705/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597706306308773/72057594037927936), (6578493361277/144115188075855872)), (47047/144115188075855872), by norm_num⟩
  | 4 => ⟨((186609586893941/4503599627370496), (76989898851/281474976710656)), (70681/36028797018963968), by norm_num⟩
  | 3 => ⟨((186348999458099/1125899906842624), (12295594010879/9007199254740992)), (44273/4503599627370496), by norm_num⟩
  | 2 => ⟨((1115486231610869/2251799813685248), (12261445197067/2251799813685248)), (44419/1125899906842624), by norm_num⟩
  | 1 => ⟨((555132560266527/562949953421312), (18306921583913/1125899906842624)), (133989/1125899906842624), by norm_num⟩
  | 0 => ⟨((547287260938595/562949953421312), (36273614795409/1125899906842624)), (270913/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((547287260938595/562949953421312), (36273614795409/1125899906842624)), (1033451084617232921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1062952045327451/1125899906842624), (70528782052723/1125899906842624)), (34013/70368744177664), by norm_num⟩
  | 2 => ⟨((499552728768991/562949953421312), (133171186322649/1125899906842624)), (547873/562949953421312), by norm_num⟩
  | 3 => ⟨((1741677292016417/2251799813685248), (236347935075127/1125899906842624)), (4407809/2251799813685248), by norm_num⟩
  | 4 => ⟨((623944985426957/1125899906842624), (365611391415505/1125899906842624)), (8669097/2251799813685248), by norm_num⟩
  | 5 => ⟨((454100144698557/2251799813685248), (101306249739553/281474976710656)), (15238585/2251799813685248), by norm_num⟩
  | 6 => ⟨((-800465929464667/9007199254740992), (653744545297729/4503599627370496)), (34230317/4503599627370496), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-237667161/134217728), (-4775327437/134217728)), (1/67108864), by norm_num⟩, -6, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-242461957/134217728), (-4871666861/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((247976944411047/9007199254740992), (182290846275667/1125899906842624)), (56060265/9007199254740992), by norm_num⟩
  | 1 => ⟨((-683541829/8589934592), (-1004959705/2147483648)), (39/2147483648), by norm_num⟩
  | 2 => ⟨((987844999/8589934592), (5809414299/8589934592)), (227/8589934592), by norm_num⟩
  | 3 => ⟨((-951746429/8589934592), (-1399280585/2147483648)), (221/8589934592), by norm_num⟩
  | 4 => ⟨((343862625/4294967296), (1011110271/2147483648)), (81/4294967296), by norm_num⟩
  | 5 => ⟨((-49694541/1073741824), (-2337987657/8589934592)), (189/17179869184), by norm_num⟩
  | 6 => ⟨((766057055/34359738368), (2252551165/17179869184)), (23/4294967296), by norm_num⟩
  | 7 => ⟨((-316312811/34359738368), (-3720405869/68719476736)), (153/68719476736), by norm_num⟩
  | 8 => ⟨((57141351/17179869184), (2688339013/137438953472)), (223/274877906944), by norm_num⟩
  | 9 => ⟨((-1174469313/1099511627776), (-3453466293/549755813888)), (9/34359738368), by norm_num⟩
  | 10 => ⟨((678930587/2199023255552), (62386259/34359738368)), (21/274877906944), by norm_num⟩
  | 11 => ⟨((-713586107/8796093022208), (-2098263053/4398046511104)), (89/4398046511104), by norm_num⟩
  | 12 => ⟨((343754855/17592186044416), (4043173513/35184372088832)), (173/35184372088832), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581622622146687/10141204801825835211973625643008), (1826737318013/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889590013963635/316912650057057350374175801344), (270350664215/79228162514264337593543950336)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((472551086077129/9903520314283042199192993792), (1216383389575/19807040628566084398385987584)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890008111835079/2475880078570760549798248448), (2584338032081/2475880078570760549798248448)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771674123308399/154742504910672534362390528), (1291900949441/77371252455336267181195264)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((387501598434431/2417851639229258349412352), (1210872382379/4835703278458516698824704)), (12953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259184778240881/604462909807314587353088), (2118457295527/604462909807314587353088)), (22673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236054403145295/9444732965739290427392), (107544557217/2361183241434822606848)), (9213/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162252677993873/590295810358705651712), (2580135809427/4722366482869645213696)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622110150669673/590295810358705651712), (1773085130737/295147905179352825856)), (38027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824301153072643/73786976294838206464), (2215219549995/36893488147419103232)), (743/1152921504606846976), by norm_num⟩
  | 7 => ⟨((227948167926675/1152921504606846976), (2490559608937/4611686018427387904)), (26761/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797416046948763/576460752303423488), (311075978887/72057594037927936)), (53555/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195319244564087/144115188075855872), (2175337755785/72057594037927936)), (46897/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492741186896191/36028797018963968), (6517245145639/36028797018963968)), (70419/36028797018963968), by norm_num⟩
  | 3 => ⟨((372657634798277/2251799813685248), (8131230801285/9007199254740992)), (11019/1125899906842624), by norm_num⟩
  | 2 => ⟨((1115336622786285/2251799813685248), (16216558980651/4503599627370496)), (88345/2251799813685248), by norm_num⟩
  | 1 => ⟨((2220140334069917/2251799813685248), (24210341598707/2251799813685248)), (133001/1125899906842624), by norm_num⟩
  | 0 => ⟨((2188603000013301/2251799813685248), (47964251692089/2251799813685248)), (133973/562949953421312), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((2188603000013301/2251799813685248), (47964251692089/2251799813685248)), (511066438915061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((33221221067323/35184372088832), (46618133862841/1125899906842624)), (1064535/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003666330629959/2251799813685248), (176068093742685/2251799813685248)), (8197/8796093022208), by norm_num⟩
  | 3 => ⟨((1769108766532109/2251799813685248), (78333275717139/562949953421312)), (4062551/2251799813685248), by norm_num⟩
  | 4 => ⟨((1346286724087663/2251799813685248), (246167681407825/1125899906842624)), (3757007/1125899906842624), by norm_num⟩
  | 5 => ⟨((697261730120801/2251799813685248), (588706472688465/2251799813685248)), (12270569/2251799813685248), by norm_num⟩
  | 6 => ⟨((247976944411047/9007199254740992), (182290846275667/1125899906842624)), (56060265/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-242461957/134217728), (-4871666861/134217728)), (1/67108864), by norm_num⟩, -6, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-61749361/33554432), (-4962796139/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((535975789100855/4503599627370496), (473320206654393/4503599627370496)), (9754521/2251799813685248), by norm_num⟩
  | 1 => ⟨((-376259805/1073741824), (-2658200199/8589934592)), (111/8589934592), by norm_num⟩
  | 2 => ⟨((276968509/536870912), (978363535/2147483648)), (83/4294967296), by norm_num⟩
  | 3 => ⟨((-4349423327/8589934592), (-3840975637/8589934592)), (165/8589934592), by norm_num⟩
  | 4 => ⟨((3201652895/8589934592), (706844899/2147483648)), (123/8589934592), by norm_num⟩
  | 5 => ⟨((-3770828633/17179869184), (-832504669/4294967296)), (147/17179869184), by norm_num⟩
  | 6 => ⟨((3700991603/34359738368), (3268345597/34359738368)), (73/17179869184), by norm_num⟩
  | 7 => ⟨((-3113526839/68719476736), (-1374777739/34359738368)), (31/17179869184), by norm_num⟩
  | 8 => ⟨((2291897447/137438953472), (2023974581/137438953472)), (93/137438953472), by norm_num⟩
  | 9 => ⟨((-2999267635/549755813888), (-2648653177/549755813888)), (123/549755813888), by norm_num⟩
  | 10 => ⟨((3532464213/2199023255552), (3119519063/2199023255552)), (147/2199023255552), by norm_num⟩
  | 11 => ⟨((-3782227389/8796093022208), (-1670042459/4398046511104)), (5/274877906944), by norm_num⟩
  | 12 => ⟨((3712179251/35184372088832), (3278225409/35184372088832)), (159/35184372088832), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581578604278889/10141204801825835211973625643008), (235577064091/2535301200456458802993406410752)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222391218686599/79228162514264337593543950336), (34862629037/19807040628566084398385987584)), (11539/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945073947774433/19807040628566084398385987584), (1254851622415/39614081257132168796771975168)), (25965/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944974140850787/1237940039285380274899124224), (1333029539449/2475880078570760549798248448)), (13795/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771614458075441/154742504910672534362390528), (1332748026443/154742504910672534362390528)), (27591/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((24217978635875/151115727451828646838272), (1249152247101/9671406556917033397649408)), (12935/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314784040584823/151115727451828646838272), (546354639197/302231454903657293676544)), (22639/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944178276122221/37778931862957161709568), (1775092259889/75557863725914323419136)), (36791/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297962705973121/4722366482869645213696), (665414553971/2361183241434822606848)), (13799/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((101376867433755/36893488147419103232), (1829093989757/590295810358705651712)), (37953/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824201510920349/73786976294838206464), (1142587031159/36893488147419103232)), (11863/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823474203890305/9223372036854775808), (1284590438477/4611686018427387904)), (13349/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398680537495619/288230376151711744), (2567132471093/1152921504606846976)), (53413/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195224386273611/144115188075855872), (2243938548223/144115188075855872)), (11689/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492601578679233/36028797018963968), (3361308321023/36028797018963968)), (70171/36028797018963968), by norm_num⟩
  | 3 => ⟨((745230351980289/4503599627370496), (4193598020563/9007199254740992)), (21945/2251799813685248), by norm_num⟩
  | 2 => ⟨((2230347545956843/4503599627370496), (4181565409211/2251799813685248)), (10985/281474976710656), by norm_num⟩
  | 1 => ⟨((277460815291291/281474976710656), (6242348544189/1125899906842624)), (264141/2251799813685248), by norm_num⟩
  | 0 => ⟨((1093916597289521/1125899906842624), (6182594681077/562949953421312)), (530299/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((1093916597289521/1125899906842624), (6182594681077/562949953421312)), (2022930153853606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2125412066642557/2251799813685248), (48055731383159/2251799813685248)), (1042119/2251799813685248), by norm_num⟩
  | 2 => ⟨((1002546290365339/1125899906842624), (45358486457081/1125899906842624)), (251467/281474976710656), by norm_num⟩
  | 3 => ⟨((1781759934316841/2251799813685248), (161556039068007/2251799813685248)), (3744753/2251799813685248), by norm_num⟩
  | 4 => ⟨((1398245124030155/2251799813685248), (255665779709969/2251799813685248)), (6463487/2251799813685248), by norm_num⟩
  | 5 => ⟨((209801557899891/562949953421312), (158754533901387/1125899906842624)), (74177/17592186044416), by norm_num⟩
  | 6 => ⟨((535975789100855/4503599627370496), (473320206654393/4503599627370496)), (9754521/2251799813685248), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-61749361/33554432), (-4962796139/134217728)), (1/67108864), by norm_num⟩, -6, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-251300237/134217728), (-5049250015/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1380639129186825/9007199254740992), (54834908530725/4503599627370496)), (11479961/4503599627370496), by norm_num⟩
  | 1 => ⟨((-7888842005/17179869184), (-313321505/8589934592)), (133/17179869184), by norm_num⟩
  | 2 => ⟨((5908214649/8589934592), (58664209/1073741824)), (51/4294967296), by norm_num⟩
  | 3 => ⟨((-5899809767/8589934592), (-234323019/4294967296)), (13/1073741824), by norm_num⟩
  | 4 => ⟨((552320329/1073741824), (350984515/8589934592)), (5/536870912), by norm_num⟩
  | 5 => ⟨((-330920767/1073741824), (-26286391/1073741824)), (49/8589934592), by norm_num⟩
  | 6 => ⟨((5287200115/34359738368), (209991973/17179869184)), (25/8589934592), by norm_num⟩
  | 7 => ⟨((-4525438863/68719476736), (-89868533/17179869184)), (87/68719476736), by norm_num⟩
  | 8 => ⟨((6778501627/274877906944), (538444129/274877906944)), (133/274877906944), by norm_num⟩
  | 9 => ⟨((-282035779/34359738368), (-358452101/549755813888)), (45/274877906944), by norm_num⟩
  | 10 => ⟨((5407383587/2199023255552), (429530611/2199023255552)), (55/1099511627776), by norm_num⟩
  | 11 => ⟨((-5890572191/8796093022208), (-116978065/2199023255552)), (61/4398046511104), by norm_num⟩
  | 12 => ⟨((5882192407/35184372088832), (467246619/35184372088832)), (31/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790768422377973/5070602400912917605986812821504), (51627483701/5070602400912917605986812821504)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1779080969157911/633825300114114700748351602688), (122237680725/633825300114114700748351602688)), (11527/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890093064283915/39614081257132168796771975168), (68747413123/19807040628566084398385987584)), (1621/2475880078570760549798248448), by norm_num⟩
  | 15 => ⟨((1889890083051645/2475880078570760549798248448), (146060355255/2475880078570760549798248448)), (27557/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771556326397213/154742504910672534362390528), (146028980875/154742504910672534362390528)), (27557/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549896205368729/9671406556917033397649408), (136868843829/9671406556917033397649408)), (25835/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629544304754035/302231454903657293676544), (59863461671/302231454903657293676544)), (11303/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((14752182906891/590295810358705651712), (48623451897/18889465931478580854784)), (36735/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648952483652127/2361183241434822606848), (145815740991/4722366482869645213696)), (861/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1621950677343621/590295810358705651712), (200407937681/590295810358705651712)), (9471/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824102792249995/73786976294838206464), (62594234381/18446744073709551616)), (11839/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823363534496221/9223372036854775808), (140745661111/4611686018427387904)), (53277/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797305983141761/576460752303423488), (140631544211/576460752303423488)), (53279/1152921504606846976), by norm_num⟩
  | 5 => ⟨((74695532562069/9007199254740992), (7682771535/4503599627370496)), (23311/72057594037927936), by norm_num⟩
  | 4 => ⟨((746229434648389/18014398509481984), (92065157739/9007199254740992)), (69937/36028797018963968), by norm_num⟩
  | 3 => ⟨((745142108421519/4503599627370496), (459430485605/9007199254740992)), (21857/2251799813685248), by norm_num⟩
  | 2 => ⟨((2230000249275479/4503599627370496), (458090329777/2251799813685248)), (174879/4503599627370496), by norm_num⟩
  | 1 => ⟨((1109589848468177/1125899906842624), (683794880511/1125899906842624)), (65595/562949953421312), by norm_num⟩
  | 0 => ⟨((136679723655769/140737488355328), (1354285793923/1125899906842624)), (525013/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((136679723655769/140737488355328), (1354285793923/1125899906842624)), (2002765664107512717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2123819990738519/2251799813685248), (2630477639291/1125899906842624)), (1021015/2251799813685248), by norm_num⟩
  | 2 => ⟨((2003101540375471/2251799813685248), (9923903468797/2251799813685248)), (241343/281474976710656), by norm_num⟩
  | 3 => ⟨((222728352272357/281474976710656), (17655731387909/2251799813685248)), (863007/562949953421312), by norm_num⟩
  | 4 => ⟨((352450855737379/562949953421312), (27941609631855/2251799813685248)), (5517245/2251799813685248), by norm_num⟩
  | 5 => ⟨((1764601760544473/4503599627370496), (34987281429107/2251799813685248)), (14090759/4503599627370496), by norm_num⟩
  | 6 => ⟨((1380639129186825/9007199254740992), (54834908530725/4503599627370496)), (11479961/4503599627370496), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-251300237/134217728), (-5049250015/134217728)), (1/67108864), by norm_num⟩, -6, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-255393053/134217728), (-5131484913/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((1156751705153251/9007199254740992), (-341550568652911/4503599627370496)), (16176141/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3358608743/8589934592), (247921555/1073741824)), (95/8589934592), by norm_num⟩
  | 2 => ⟨((5112679839/8589934592), (-754802737/2147483648)), (147/8589934592), by norm_num⟩
  | 3 => ⟨((-2594278081/4294967296), (766004623/2147483648)), (151/8589934592), by norm_num⟩
  | 4 => ⟨((1974584457/4294967296), (-1166059131/4294967296)), (117/8589934592), by norm_num⟩
  | 5 => ⟨((-1202333337/4294967296), (1420037275/8589934592)), (145/17179869184), by norm_num⟩
  | 6 => ⟨((4880707763/34359738368), (-720555891/8589934592)), (149/34359738368), by norm_num⟩
  | 7 => ⟨((-4245549799/68719476736), (156696327/4294967296)), (131/68719476736), by norm_num⟩
  | 8 => ⟨((1615708953/68719476736), (-954130967/68719476736)), (101/137438953472), by norm_num⟩
  | 9 => ⟨((-2186249849/274877906944), (161381841/34359738368)), (139/549755813888), by norm_num⟩
  | 10 => ⟨((20800271/8589934592), (-1572258035/1099511627776)), (171/2199023255552), by norm_num⟩
  | 11 => ⟨((-1473789481/2199023255552), (870322703/2199023255552)), (97/4398046511104), by norm_num⟩
  | 12 => ⟨((2991323429/17592186044416), (-883238999/8796093022208)), (25/4398046511104), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581497123104531/10141204801825835211973625643008), (-173713060263/2535301200456458802993406410752)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889516796081459/316912650057057350374175801344), (-822554647039/633825300114114700748351602688)), (23071/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472509938440693/9903520314283042199192993792), (-115652448505/4951760157141521099596496896)), (25957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889833425409911/2475880078570760549798248448), (-491427505171/1237940039285380274899124224)), (6895/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771499651658967/154742504910672534362390528), (-982640428349/154742504910672534362390528)), (27581/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774921527325487/4835703278458516698824704), (-920997472825/9671406556917033397649408)), (6465/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259042084495589/604462909807314587353088), (-12588202073/9444732965739290427392)), (22629/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472050943742273/18889465931478580854784), (-1308745939933/75557863725914323419136)), (36775/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20278878277847/73786976294838206464), (-981185918119/4722366482869645213696)), (27585/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810936293786663/295147905179352825856), (-1348523929375/590295810358705651712)), (37933/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824005107883543/73786976294838206464), (-1684745355681/73786976294838206464)), (741/1152921504606846976), by norm_num⟩
  | 7 => ⟨((911626770277817/4611686018427387904), (-236761088421/1152921504606846976)), (53361/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594501848831463/1152921504606846976), (-1892527666929/1152921504606846976)), (26687/576460752303423488), by norm_num⟩
  | 5 => ⟨((149379003706033/18014398509481984), (-827103615161/72057594037927936)), (11679/36028797018963968), by norm_num⟩
  | 4 => ⟨((1492313856069605/36028797018963968), (-1238903057655/18014398509481984)), (35051/18014398509481984), by norm_num⟩
  | 3 => ⟨((1490102469049225/9007199254740992), (-3091133863653/9007199254740992)), (87677/9007199254740992), by norm_num⟩
  | 2 => ⟨((557408829578983/1125899906842624), (-3081967157909/2251799813685248)), (43875/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218628741393319/2251799813685248), (-9200200433417/2251799813685248)), (263623/2251799813685248), by norm_num⟩
  | 0 => ⟨((2185759606145659/2251799813685248), (-18218389508255/2251799813685248)), (528743/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2185759606145659/2251799813685248), (-18218389508255/2251799813685248)), (2016994484908293967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1060754405677711/1125899906842624), (-35368170504465/2251799813685248)), (1035029/2251799813685248), by norm_num⟩
  | 2 => ⟨((999100519910337/1125899906842624), (-66643477728995/2251799813685248)), (1982797/2251799813685248), by norm_num⟩
  | 3 => ⟨((1771190324369613/2251799813685248), (-3696128583623/70368744177664)), (28409/17592186044416), by norm_num⟩
  | 4 => ⟨((1386946524667509/2251799813685248), (-93032030931383/1125899906842624)), (3051233/1125899906842624), by norm_num⟩
  | 5 => ⟨((419442442372111/1125899906842624), (-114602062935491/1125899906842624)), (17051683/4503599627370496), by norm_num⟩
  | 6 => ⟨((1156751705153251/9007199254740992), (-341550568652911/4503599627370496)), (16176141/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-255393053/134217728), (-5131484913/134217728)), (1/67108864), by norm_num⟩, -6, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile031Terms2
