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
namespace Reinmann.XiRectangle.Tile034Terms0
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨34,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8319/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (8319/640))
  have he : value ((7/8), (8319/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
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

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog2 : Sound J_negLog2 F_negLog2 c := by
  apply sound_round (sound_scale (A_log2 hcre) S_log2)
  intro k
  fin_cases k <;> norm_num [J_negLog2, J_log2, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/16777216), (-1209278953/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-372130559/536870912), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg2 : Sound J_arg2 F_arg2 c := by
  apply sound_round (sound_mul (A_negLog2 hcre) (A_variable hcre) S_negLog2 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg2, J_negLog2, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-280902016070325/562949953421312), (-247489406837015/1125899906842624)), (53324147/2251799813685248), by norm_num⟩
  | 1 => ⟨((371373063/1073741824), (654398287/4294967296)), (73/4294967296), by norm_num⟩
  | 2 => ⟨((-514832383/4294967296), (-56699291/1073741824)), (53/8589934592), by norm_num⟩
  | 3 => ⟨((475806153/17179869184), (419210173/34359738368)), (51/34359738368), by norm_num⟩
  | 4 => ⟨((-659607387/137438953472), (-581148699/274877906944)), (73/274877906944), by norm_num⟩
  | 5 => ⟨((731528001/1099511627776), (161128633/549755813888)), (83/2199023255552), by norm_num⟩
  | 6 => ⟨((-1352150857/17592186044416), (-148914477/4398046511104)), (79/17592186044416), by norm_num⟩
  | 7 => ⟨((1071130919/140737488355328), (471861257/140737488355328)), (65/140737488355328), by norm_num⟩
  | 8 => ⟨((-1484902753/2251799813685248), (-81767325/281474976710656)), (23/562949953421312), by norm_num⟩
  | 9 => ⟨((457447181/9007199254740992), (403034957/18014398509481984)), (59/18014398509481984), by norm_num⟩
  | 10 => ⟨((-253662579/72057594037927936), (-446980071/288230376151711744)), (67/288230376151711744), by norm_num⟩
  | 11 => ⟨((31968273/144115188075855872), (450651601/4611686018427387904)), (35/2305843009213693952), by norm_num⟩
  | 12 => ⟨((-945438647/73786976294838206464), (-104122629/18446744073709551616)), (67/73786976294838206464), by norm_num⟩
  | _ => zero

def term2ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1583185728209367/10141204801825835211973625643008), (-1775879769595/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((890512788663111/316912650057057350374175801344), (-4213507117627/633825300114114700748351602688)), (11577/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((473069983263103/9903520314283042199192993792), (-4739911104203/39614081257132168796771975168)), (26055/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((946106318330599/1237940039285380274899124224), (-78685010331/38685626227668133590597632)), (27691/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443469440351117/38685626227668133590597632), (-629435774083/19342813113834066795298816)), (6925/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1552071362402545/9671406556917033397649408), (-1180097871281/2417851639229258349412352)), (12989/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39405958871413/18889465931478580854784), (-4129965506749/604462909807314587353088)), (5685/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((945684027970949/37778931862957161709568), (-838810815161/9444732965739290427392)), (36969/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((81263718882505/295147905179352825856), (-5032245420355/4722366482869645213696)), (13871/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1625129998115747/590295810358705651712), (-432395620565/36893488147419103232)), (38169/590295810358705651712), by norm_num⟩
  | 8 => ⟨((457018049529175/18446744073709551616), (-8646399578967/73786976294838206464)), (11937/18446744073709551616), by norm_num⟩
  | 7 => ⟨((913911297256757/4611686018427387904), (-1215639608843/1152921504606846976)), (6721/1152921504606846976), by norm_num⟩
  | 6 => ⟨((799531439357775/576460752303423488), (-9722509787667/1152921504606846976)), (53831/1152921504606846976), by norm_num⟩
  | 5 => ⟨((599506954690569/72057594037927936), (-8504257925885/144115188075855872)), (47173/144115188075855872), by norm_num⟩
  | 4 => ⟨((749134323507941/18014398509481984), (-12750497702747/36028797018963968)), (35451/18014398509481984), by norm_num⟩
  | 3 => ⟨((1497514439518255/9007199254740992), (-15927787048445/9007199254740992)), (88877/9007199254740992), by norm_num⟩
  | 2 => ⟨((1122182416233235/2251799813685248), (-15912226524567/2251799813685248)), (22313/562949953421312), by norm_num⟩
  | 1 => ⟨((560121848439461/562949953421312), (-11914618142815/562949953421312)), (134817/1125899906842624), by norm_num⟩
  | 0 => ⟨((557134282251165/562949953421312), (-47500849199229/1125899906842624)), (273397/1125899906842624), by norm_num⟩
  | _ => zero

def term2ValueSquares : ℕ → Disk
  | 0 => ⟨((557134282251165/562949953421312), (-47500849199229/1125899906842624)), (1042926792625045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1100753357941851/1125899906842624), (-94020263663215/1125899906842624)), (564215/1125899906842624), by norm_num⟩
  | 2 => ⟨((267079279812279/281474976710656), (-91920356607977/562949953421312)), (1197459/1125899906842624), by norm_num⟩
  | 3 => ⟨((983661205329315/1125899906842624), (-174438402516915/562949953421312)), (665871/281474976710656), by norm_num⟩
  | 4 => ⟨((751287336146429/1125899906842624), (-609604062431077/1125899906842624)), (1576159/281474976710656), by norm_num⟩
  | 5 => ⟨((171254609179461/1125899906842624), (-203387445626595/281474976710656)), (15241009/1125899906842624), by norm_num⟩
  | 6 => ⟨((-280902016070325/562949953421312), (-247489406837015/1125899906842624)), (53324147/2251799813685248), by norm_num⟩
  | _ => zero

def term2Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/16777216), (-1209278953/134217728)), (1/67108864), by norm_num⟩, -1, term2ValuePoly, term2ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term2Value_checks : CertifiedScalarExp.Checks term2Value := by
  constructor
  · norm_num [term2Value, CertifiedScalarExp.reduced, term2ValuePoly, term2ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term2ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value, term2ValueSquares, term2ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term2Value, CertifiedScalarExp.roundingCheck, term2ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term2 : Sound J_term2 F_term2 c := by
  apply exp_sound (A_arg2 hcre) S_arg2 term2Value term2Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term2Value,J_arg2]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term2,J_arg2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log3 : Sound J_log3 F_log3 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log3_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_negLog3 : Sound J_negLog3 F_negLog3 c := by
  apply sound_round (sound_scale (A_log3 hcre) S_log3)
  intro k
  fin_cases k <;> norm_num [J_negLog3, J_log3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-64510795/67108864), (-958330897/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((-1179625963/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_arg3 : Sound J_arg3 F_arg3 c := by
  apply sound_round (sound_mul (A_negLog3 hcre) (A_variable hcre) S_negLog3 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg3, J_negLog3, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-245563283128311/4503599627370496), (-213072921032937/562949953421312)), (53059845/2251799813685248), by norm_num⟩
  | 1 => ⟨((257281151/4294967296), (1785923229/4294967296)), (57/2147483648), by norm_num⟩
  | 2 => ⟨((-141326117/4294967296), (-981018603/4294967296)), (1/67108864), by norm_num⟩
  | 3 => ⟨((51754203/4294967296), (359253031/4294967296)), (3/536870912), by norm_num⟩
  | 4 => ⟨((-113715607/34359738368), (-1578719179/68719476736)), (27/17179869184), by norm_num⟩
  | 5 => ⟨((199886981/274877906944), (1387520233/274877906944)), (97/274877906944), by norm_num⟩
  | 6 => ⟨((-73199431/549755813888), (-508115593/549755813888)), (73/1099511627776), by norm_num⟩
  | 7 => ⟨((91906051/4398046511104), (1275936079/8796093022208)), (47/4398046511104), by norm_num⟩
  | 8 => ⟨((-100969117/35184372088832), (-87609941/4398046511104)), (53/35184372088832), by norm_num⟩
  | 9 => ⟨((197201623/562949953421312), (342219939/140737488355328)), (53/281474976710656), by norm_num⟩
  | 10 => ⟨((-173318501/4503599627370496), (-601547249/2251799813685248)), (95/4503599627370496), by norm_num⟩
  | 11 => ⟨((17309985/4503599627370496), (480630691/18014398509481984)), (77/36028797018963968), by norm_num⟩
  | 12 => ⟨((-202847597/576460752303423488), (-1408071423/576460752303423488)), (115/576460752303423488), by norm_num⟩
  | _ => zero

def term3ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395680896270333/2535301200456458802993406410752), (-1116255181405/5070602400912917605986812821504)), (29117/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1780483210772119/633825300114114700748351602688), (-330864311567/79228162514264337593543950336)), (34673/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945835082673473/19807040628566084398385987584), (-1488758239891/19807040628566084398385987584)), (39013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472891308659673/618970019642690137449562112), (-790825034831/618970019642690137449562112)), (41459/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886615447531903/77371252455336267181195264), (-3162950110957/154742504910672534362390528)), (41467/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775732747151381/4835703278458516698824704), (-1482446910511/4835703278458516698824704)), (9721/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((630230559158385/302231454903657293676544), (-2593910182171/604462909807314587353088)), (2127/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1890508578642441/75557863725914323419136), (-2107203352845/37778931862957161709568)), (55319/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1299575827389779/4722366482869645213696), (-3160194849741/4722366482869645213696)), (41503/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((812123230790315/295147905179352825856), (-271517272761/36893488147419103232)), (28545/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1826970051245337/73786976294838206464), (-5428858102305/73786976294838206464)), (71397/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1826585804890193/9223372036854775808), (-6105420220253/9223372036854775808)), (80369/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1597829994800971/1152921504606846976), (-3051431869101/576460752303423488)), (80429/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1197939528085909/144115188075855872), (-5337129659907/144115188075855872)), (35221/72057594037927936), by norm_num⟩
  | 4 => ⟨((1496665854837769/36028797018963968), (-3999971050141/18014398509481984)), (105797/36028797018963968), by norm_num⟩
  | 3 => ⟨((1495526303729439/9007199254740992), (-2497465144571/2251799813685248)), (132481/9007199254740992), by norm_num⟩
  | 2 => ⟨((560108645843241/1125899906842624), (-2493689826543/562949953421312)), (66417/1125899906842624), by norm_num⟩
  | 1 => ⟨((1117353466285577/1125899906842624), (-14924383454501/1125899906842624)), (200135/1125899906842624), by norm_num⟩
  | 0 => ⟨((277179373344469/281474976710656), (-7424432996959/281474976710656)), (201905/562949953421312), by norm_num⟩
  | _ => zero

def term3ValueSquares : ℕ → Disk
  | 0 => ⟨((277179373344469/281474976710656), (-7424432996959/281474976710656)), (770206453563499273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((545506983956345/562949953421312), (-29244513449599/562949953421312)), (408299/562949953421312), by norm_num⟩
  | 2 => ⟨((1054170539227941/1125899906842624), (-113353496041395/1125899906842624)), (1667435/1125899906842624), by norm_num⟩
  | 3 => ⟨((60974920152519/70368744177664), (-212263835033841/1125899906842624)), (216135/70368744177664), by norm_num⟩
  | 4 => ⟨((805344174960147/1125899906842624), (-183927829659409/562949953421312)), (7296953/1125899906842624), by norm_num⟩
  | 5 => ⟨((455867747150547/1125899906842624), (-1052492892691725/2251799813685248)), (475219/35184372088832), by norm_num⟩
  | 6 => ⟨((-245563283128311/4503599627370496), (-213072921032937/562949953421312)), (53059845/2251799813685248), by norm_num⟩
  | _ => zero

def term3Value : CertifiedScalarExp.Data :=
  ⟨⟨((-64510795/67108864), (-958330897/67108864)), (3/134217728), by norm_num⟩, -2, term3ValuePoly, term3ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term3Value_checks : CertifiedScalarExp.Checks term3Value := by
  constructor
  · norm_num [term3Value, CertifiedScalarExp.reduced, term3ValuePoly, term3ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term3ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value, term3ValueSquares, term3ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term3Value, CertifiedScalarExp.roundingCheck, term3ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term3 : Sound J_term3 F_term3 c := by
  apply exp_sound (A_arg3 hcre) S_arg3 term3Value term3Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term3Value,J_arg3]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term3,J_arg3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log4 : Sound J_log4 F_log4 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log4_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
theorem S_negLog4 : Sound J_negLog4 F_negLog4 c := by
  apply sound_round (sound_scale (A_log4 hcre) S_log4)
  intro k
  fin_cases k <;> norm_num [J_negLog4, J_log4, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10175445/8388608), (-1209278953/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-372130559/268435456), 0), (1/1073741824), by norm_num⟩
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
theorem S_arg4 : Sound J_arg4 F_arg4 c := by
  apply sound_round (sound_mul (A_negLog4 hcre) (A_variable hcre) S_negLog4 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg4, J_negLog4, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((903713598294239/4503599627370496), (987942504147097/4503599627370496)), (150579/8796093022208), by norm_num⟩
  | 1 => ⟨((-298693911/1073741824), (-653066217/2147483648)), (53/2147483648), by norm_num⟩
  | 2 => ⟨((828155369/4294967296), (452671007/2147483648)), (75/4294967296), by norm_num⟩
  | 3 => ⟨((-765378079/8589934592), (-418356843/4294967296)), (71/8589934592), by norm_num⟩
  | 4 => ⟨((265259829/8589934592), (144991433/4294967296)), (51/17179869184), by norm_num⟩
  | 5 => ⟨((-73545641/8589934592), (-643202579/68719476736)), (29/34359738368), by norm_num⟩
  | 6 => ⟨((67970605/34359738368), (297222703/137438953472)), (7/34359738368), by norm_num⟩
  | 7 => ⟨((-215376609/549755813888), (-470900751/1099511627776)), (91/2199023255552), by norm_num⟩
  | 8 => ⟨((597150757/8796093022208), (40800441/549755813888)), (65/8796093022208), by norm_num⟩
  | 9 => ⟨((-183961495/17592186044416), (-804429103/70368744177664)), (41/35184372088832), by norm_num⟩
  | 10 => ⟨((408039653/281474976710656), (111517553/70368744177664)), (93/562949953421312), by norm_num⟩
  | 11 => ⟨((-822782647/4503599627370496), (-449734269/2251799813685248)), (3/140737488355328), by norm_num⟩
  | 12 => ⟨((760412629/36028797018963968), (415642721/18014398509481984)), (91/36028797018963968), by norm_num⟩
  | _ => zero

def term4ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582395689313353/10141204801825835211973625643008), (540515652753/5070602400912917605986812821504)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1780097391224413/633825300114114700748351602688), (1281163544123/633825300114114700748351602688)), (11541/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((945618166062351/19807040628566084398385987584), (720576378593/19807040628566084398385987584)), (25969/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472776137437705/618970019642690137449562112), (765517598413/1237940039285380274899124224)), (55189/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443192626470039/38685626227668133590597632), (1530821921773/154742504910672534362390528)), (27597/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((3029363659277/18889465931478580854784), (358729745615/2417851639229258349412352)), (25875/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1260084044175839/604462909807314587353088), (627663790215/302231454903657293676544)), (45287/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889896421758195/75557863725914323419136), (127467666303/4722366482869645213696)), (73601/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324779306139563/1180591620717411303424), (191155063173/590295810358705651712)), (27605/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1623616718934831/590295810358705651712), (2102102182451/590295810358705651712)), (75929/590295810358705651712), by norm_num⟩
  | 8 => ⟨((913092063345085/36893488147419103232), (2626722737937/73786976294838206464)), (94933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1825703362668599/9223372036854775808), (738454792821/2305843009213693952)), (106831/9223372036854775808), by norm_num⟩
  | 6 => ⟨((49904678271847/36028797018963968), (738066240937/288230376151711744)), (106869/1152921504606846976), by norm_num⟩
  | 5 => ⟨((598585846653495/72057594037927936), (2581484292515/144115188075855872)), (46777/72057594037927936), by norm_num⟩
  | 4 => ⟨((1495518935604745/36028797018963968), (1934366834005/18014398509481984)), (140417/36028797018963968), by norm_num⟩
  | 3 => ⟨((1494101100661713/9007199254740992), (4829809977613/9007199254740992)), (175673/9007199254740992), by norm_num⟩
  | 2 => ⟨((2237609468520465/4503599627370496), (9641319584801/4503599627370496)), (175901/2251799813685248), by norm_num⟩
  | 1 => ⟨((2230532325338127/2251799813685248), (3604075429887/562949953421312)), (528845/2251799813685248), by norm_num⟩
  | 0 => ⟨((276167131758541/281474976710656), (28650331916593/2251799813685248)), (265567/562949953421312), by norm_num⟩
  | _ => zero

def term4ValueSquares : ℕ → Disk
  | 0 => ⟨((276167131758541/281474976710656), (28650331916593/2251799813685248)), (1013057710887718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((270913812325823/281474976710656), (56220130697225/2251799813685248)), (2111505/2251799813685248), by norm_num⟩
  | 2 => ⟨((2084587655504103/2251799813685248), (13527676700279/281474976710656)), (4169995/2251799813685248), by norm_num⟩
  | 3 => ⟨((962295536392605/1125899906842624), (200370407249665/2251799813685248)), (8121507/2251799813685248), by norm_num⟩
  | 4 => ⟨((1627099565012781/2251799813685248), (342509218358915/2251799813685248)), (7664043/1125899906842624), by norm_num⟩
  | 5 => ⟨((280902016070333/562949953421312), (247489406837013/1125899906842624)), (26814403/2251799813685248), by norm_num⟩
  | 6 => ⟨((903713598294239/4503599627370496), (987942504147097/4503599627370496)), (150579/8796093022208), by norm_num⟩
  | _ => zero

def term4Value : CertifiedScalarExp.Data :=
  ⟨⟨((-10175445/8388608), (-1209278953/67108864)), (1/33554432), by norm_num⟩, -3, term4ValuePoly, term4ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term4Value_checks : CertifiedScalarExp.Checks term4Value := by
  constructor
  · norm_num [term4Value, CertifiedScalarExp.reduced, term4ValuePoly, term4ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term4ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value, term4ValueSquares, term4ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term4Value, CertifiedScalarExp.roundingCheck, term4ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term4 : Sound J_term4 F_term4 c := by
  apply exp_sound (A_arg4 hcre) S_arg4 term4Value term4Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term4Value,J_arg4]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term4,J_arg4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/10000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log5 : Sound J_log5 F_log5 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log5_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
theorem S_negLog5 : Sound J_negLog5 F_negLog5 c := by
  apply sound_round (sound_scale (A_log5 hcre) S_log5)
  intro k
  fin_cases k <;> norm_num [J_negLog5, J_log5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47253303/33554432), (-350982347/16777216)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-54003775/33554432), 0), (1/1073741824), by norm_num⟩
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
theorem S_arg5 : Sound J_arg5 F_arg5 c := by
  apply sound_round (sound_mul (A_negLog5 hcre) (A_variable hcre) S_negLog5 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg5, J_negLog5, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-263945177902741/2251799813685248), (-966696870771029/4503599627370496)), (48639891/2251799813685248), by norm_num⟩
  | 1 => ⟨((405124069/2147483648), (370940827/1073741824)), (19/536870912), by norm_num⟩
  | 2 => ⟨((-163005509/1073741824), (-1194012461/4294967296)), (31/1073741824), by norm_num⟩
  | 3 => ⟨((43724541/536870912), (1281125949/8589934592)), (135/8589934592), by norm_num⟩
  | 4 => ⟨((-35185967/1073741824), (-1030946337/17179869184)), (55/8589934592), by norm_num⟩
  | 5 => ⟨((724859255/68719476736), (1327395297/68719476736)), (9/4294967296), by norm_num⟩
  | 6 => ⟨((-388871989/137438953472), (-712120105/137438953472)), (79/137438953472), by norm_num⟩
  | 7 => ⟨((357637327/549755813888), (654921769/549755813888)), (147/1099511627776), by norm_num⟩
  | 8 => ⟨((-575595073/4398046511104), (-1054055925/4398046511104)), (15/549755813888), by norm_num⟩
  | 9 => ⟨((411726459/17592186044416), (188493063/4398046511104)), (87/17592186044416), by norm_num⟩
  | 10 => ⟨((-265059269/70368744177664), (-485388611/70368744177664)), (57/70368744177664), by norm_num⟩
  | 11 => ⟨((155125977/281474976710656), (568147515/562949953421312)), (135/1125899906842624), by norm_num⟩
  | 12 => ⟨((-332887505/4503599627370496), (-609598767/4503599627370496)), (147/9007199254740992), by norm_num⟩
  | _ => zero

def term5ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1582141353606259/10141204801825835211973625643008), (-84288018551/316912650057057350374175801344)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779791440724339/633825300114114700748351602688), (-1597762999633/316912650057057350374175801344)), (23129/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890891910520345/39614081257132168796771975168), (-3594507355425/39614081257132168796771975168)), (26025/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890738312586829/2475880078570760549798248448), (-3818614025103/2475880078570760549798248448)), (55315/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((443100985881507/38685626227668133590597632), (-954498808195/38685626227668133590597632)), (1729/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((1550690195995867/9671406556917033397649408), (-1789356552205/4835703278458516698824704)), (12971/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629891350578799/302231454903657293676544), (-1565358292781/302231454903657293676544)), (11353/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((472351523145407/18889465931478580854784), (-2543090979697/37778931862957161709568)), (73821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298748912150587/4722366482869645213696), (-476694766987/590295810358705651712)), (55389/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1623109371145885/590295810358705651712), (-655236290847/73786976294838206464)), (19049/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912774282961779/36893488147419103232), (-6549735062555/73786976294838206464)), (95301/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824986466895653/9223372036854775808), (-7364839176957/9223372036854775808)), (107291/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1596230449733343/1152921504606846976), (-1840080999439/288230376151711744)), (107387/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1196539695510869/144115188075855872), (-6435204998595/144115188075855872)), (11759/18014398509481984), by norm_num⟩
  | 4 => ⟨((1494565650477305/36028797018963968), (-9642653200423/36028797018963968)), (35331/9007199254740992), by norm_num⟩
  | 3 => ⟨((373225066037927/2251799813685248), (-3008888145375/2251799813685248)), (88517/4503599627370496), by norm_num⟩
  | 2 => ⟨((1117590101857811/2251799813685248), (-12008918964351/2251799813685248)), (44401/562949953421312), by norm_num⟩
  | 1 => ⟨((1113409896485903/1125899906842624), (-8973418790107/562949953421312)), (133917/562949953421312), by norm_num⟩
  | 0 => ⟨((1100819755227551/1125899906842624), (-35627772841355/1125899906842624)), (541389/1125899906842624), by norm_num⟩
  | _ => zero

def term5ValueSquares : ℕ → Disk
  | 0 => ⟨((1100819755227551/1125899906842624), (-35627772841355/1125899906842624)), (2065235142234420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1075170881482999/1125899906842624), (-34834141063665/562949953421312)), (1092923/1125899906842624), by norm_num⟩
  | 2 => ⟨((31950518754441/35184372088832), (-133058556717187/1125899906842624)), (277827/140737488355328), by norm_num⟩
  | 3 => ⟨((912719788397793/1125899906842624), (-60414463289239/281474976710656)), (4562001/1125899906842624), by norm_num⟩
  | 4 => ⟨((688035312404341/1125899906842624), (-195901876585653/562949953421312)), (9354779/1125899906842624), by norm_num⟩
  | 5 => ⟨((568225307013779/2251799813685248), (-478861071177073/1125899906842624)), (8972073/562949953421312), by norm_num⟩
  | 6 => ⟨((-263945177902741/2251799813685248), (-966696870771029/4503599627370496)), (48639891/2251799813685248), by norm_num⟩
  | _ => zero

def term5Value : CertifiedScalarExp.Data :=
  ⟨⟨((-47253303/33554432), (-350982347/16777216)), (1/33554432), by norm_num⟩, -3, term5ValuePoly, term5ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term5Value_checks : CertifiedScalarExp.Checks term5Value := by
  constructor
  · norm_num [term5Value, CertifiedScalarExp.reduced, term5ValuePoly, term5ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term5ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value, term5ValueSquares, term5ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term5Value, CertifiedScalarExp.roundingCheck, term5ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term5 : Sound J_term5 F_term5 c := by
  apply exp_sound (A_arg5 hcre) S_arg5 term5Value term5Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term5Value,J_arg5]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term5,J_arg5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((358351893845611/200000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log6 : Sound J_log6 F_log6 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log6_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_negLog6 : Sound J_negLog6 F_negLog6 c := by
  apply sound_round (sound_scale (A_log6 hcre) S_log6)
  intro k
  fin_cases k <;> norm_num [J_negLog6, J_log6, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-105212575/67108864), (-781485187/33554432)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-1923887081/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_arg6 : Sound J_arg6 F_arg6 c := by
  apply sound_round (sound_mul (A_negLog6 hcre) (A_variable hcre) S_negLog6 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg6, J_negLog6, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-252160849108647/4503599627370496), (452267611276383/2251799813685248)), (20041077/1125899906842624), by norm_num⟩
  | 1 => ⟨((430881109/4294967296), (-1545629073/4294967296)), (139/4294967296), by norm_num⟩
  | 2 => ⟨((-193008827/2147483648), (346174441/1073741824)), (63/2147483648), by norm_num⟩
  | 3 => ⟨((461100525/8589934592), (-1654030221/8589934592)), (153/8589934592), by norm_num⟩
  | 4 => ⟨((-51636327/2147483648), (370453039/4294967296)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((296063609/34359738368), (-1062020385/34359738368)), (101/34359738368), by norm_num⟩
  | 6 => ⟨((-176824925/68719476736), (634295027/68719476736)), (61/68719476736), by norm_num⟩
  | 7 => ⟨((362088839/549755813888), (-1298861853/549755813888)), (127/549755813888), by norm_num⟩
  | 8 => ⟨((-324388053/2199023255552), (290906003/549755813888)), (115/2199023255552), by norm_num⟩
  | 9 => ⟨((258322385/8796093022208), (-463318743/4398046511104)), (93/8796093022208), by norm_num⟩
  | 10 => ⟨((-23142579/4398046511104), (166031149/8796093022208)), (135/70368744177664), by norm_num⟩
  | 11 => ⟨((120628175/140737488355328), (-865419297/281474976710656)), (45/140737488355328), by norm_num⟩
  | 12 => ⟨((-288182233/2251799813685248), (516874407/1125899906842624)), (109/2251799813685248), by norm_num⟩
  | _ => zero

def term6ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790966773092659/5070602400912917605986812821504), (2400280472181/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779546408124799/633825300114114700748351602688), (2842983188417/633825300114114700748351602688)), (46241/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472654088383669/9903520314283042199192993792), (799476456751/9903520314283042199192993792)), (52029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472611415458111/618970019642690137449562112), (3397230594381/2475880078570760549798248448)), (55291/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((886055718677835/77371252455336267181195264), (849154565739/38685626227668133590597632)), (55303/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387604031261151/2417851639229258349412352), (1591839552127/4835703278458516698824704)), (12965/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259543042617017/604462909807314587353088), (1392534397183/302231454903657293676544)), (45389/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1889016935255439/75557863725914323419136), (1131129363165/18889465931478580854784)), (18445/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298457295894331/4722366482869645213696), (3392321371429/4722366482869645213696)), (13839/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811354403851137/295147905179352825856), (2331354424649/295147905179352825856)), (76147/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912524237345669/36893488147419103232), (2912893586491/36893488147419103232)), (47617/36893488147419103232), by norm_num⟩
  | 7 => ⟨((456106176690275/2305843009213693952), (1637609545087/2305843009213693952)), (53603/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1595669742016603/1152921504606846976), (3272987159203/576460752303423488)), (26823/288230376151711744), by norm_num⟩
  | 5 => ⟨((1196050259253081/144115188075855872), (5722707918911/144115188075855872)), (93977/144115188075855872), by norm_num⟩
  | 4 => ⟨((746916929819497/18014398509481984), (4287014124913/18014398509481984)), (70579/18014398509481984), by norm_num⟩
  | 3 => ⟨((745994828159769/4503599627370496), (5349994525487/4503599627370496)), (11049/562949953421312), by norm_num⟩
  | 2 => ⟨((1116685679103555/2251799813685248), (10673694859267/2251799813685248)), (44323/562949953421312), by norm_num⟩
  | 1 => ⟨((1112068686529673/1125899906842624), (15944895113431/1125899906842624)), (267209/1125899906842624), by norm_num⟩
  | 0 => ⟨((549099400311321/562949953421312), (7906933041431/281474976710656)), (539513/1125899906842624), by norm_num⟩
  | _ => zero

def term6ValueSquares : ℕ → Disk
  | 0 => ⟨((549099400311321/562949953421312), (7906933041431/281474976710656)), (2058078770164107921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1070290782442973/1125899906842624), (3856197309339/70368744177664)), (541395/562949953421312), by norm_num⟩
  | 2 => ⟨((507023566693353/562949953421312), (7331473091673/70368744177664)), (2177295/1125899906842624), by norm_num⟩
  | 3 => ⟨((1802169900102781/2251799813685248), (105650020602081/562949953421312)), (8751345/2251799813685248), by norm_num⟩
  | 4 => ⟨((1363009935666491/2251799813685248), (676434151622761/2251799813685248)), (17292595/2251799813685248), by norm_num⟩
  | 5 => ⟨((621828332489457/2251799813685248), (818888485452935/2251799813685248)), (15661819/1125899906842624), by norm_num⟩
  | 6 => ⟨((-252160849108647/4503599627370496), (452267611276383/2251799813685248)), (20041077/1125899906842624), by norm_num⟩
  | _ => zero

def term6Value : CertifiedScalarExp.Data :=
  ⟨⟨((-105212575/67108864), (-781485187/33554432)), (1/33554432), by norm_num⟩, -4, term6ValuePoly, term6ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term6Value_checks : CertifiedScalarExp.Checks term6Value := by
  constructor
  · norm_num [term6Value, CertifiedScalarExp.reduced, term6ValuePoly, term6ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term6ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value, term6ValueSquares, term6ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term6Value, CertifiedScalarExp.roundingCheck, term6ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term6 : Sound J_term6 F_term6 c := by
  apply exp_sound (A_arg6 hcre) S_arg6 term6Value term6Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term6Value,J_arg6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term6,J_arg6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1945910149055313/1000000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log7 : Sound J_log7 F_log7 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log7_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_negLog7 : Sound J_negLog7 F_negLog7 c := by
  apply sound_round (sound_scale (A_log7 hcre) S_log7)
  intro k
  fin_cases k <;> norm_num [J_negLog7, J_log7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-57132171/33554432), (-1697437611/67108864)), (1/33554432), by norm_num⟩
  | 1 => ⟨((-2089405113/1073741824), 0), (1/1073741824), by norm_num⟩
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
theorem S_arg7 : Sound J_arg7 F_arg7 c := by
  apply sound_round (sound_mul (A_negLog7 hcre) (A_variable hcre) S_negLog7 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg7, J_negLog7, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1619840609942079/9007199254740992), (-32894351214585/1125899906842624)), (58524059/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1503021375/4294967296), (244176681/4294967296)), (7/536870912), by norm_num⟩
  | 2 => ⟨((731186137/2147483648), (-237572941/4294967296)), (7/536870912), by norm_num⟩
  | 3 => ⟨((-474274175/2147483648), (38524633/1073741824)), (19/2147483648), by norm_num⟩
  | 4 => ⟨((1845789861/17179869184), (-299861897/17179869184)), (19/4294967296), by norm_num⟩
  | 5 => ⟨((-718348245/17179869184), (233401723/34359738368)), (61/34359738368), by norm_num⟩
  | 6 => ⟨((465947047/34359738368), (-151392927/68719476736)), (41/68719476736), by norm_num⟩
  | 7 => ⟨((-518109193/137438953472), (84170581/137438953472)), (47/274877906944), by norm_num⟩
  | 8 => ⟨((1008193937/1099511627776), (-40947097/274877906944)), (47/1099511627776), by norm_num⟩
  | 9 => ⟨((-871935473/4398046511104), (17706527/549755813888)), (83/8796093022208), by norm_num⟩
  | 10 => ⟨((1357366469/35184372088832), (-55128497/8796093022208)), (33/17592186044416), by norm_num⟩
  | 11 => ⟨((-960477523/140737488355328), (4876141/4398046511104)), (3/8796093022208), by norm_num⟩
  | 12 => ⟨((1246001973/1125899906842624), (-101211011/562949953421312)), (1/17592186044416), by norm_num⟩
  | _ => zero

def term7ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581757847530181/10141204801825835211973625643008), (-209785905005/10141204801825835211973625643008)), (19411/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((55604456668215/19807040628566084398385987584), (-248423112865/633825300114114700748351602688)), (46113/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472596841598489/9903520314283042199192993792), (-279434133741/39614081257132168796771975168)), (25939/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((945101360092947/1237940039285380274899124224), (-4638237523/38685626227668133590597632)), (55121/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885934448669057/77371252455336267181195264), (-148394603643/77371252455336267181195264)), (27561/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387547292578785/2417851639229258349412352), (-278178279007/9671406556917033397649408)), (25839/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259344883547717/604462909807314587353088), (-60836102327/151115727451828646838272)), (11305/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1888695725652807/75557863725914323419136), (-395319231821/75557863725914323419136)), (18371/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((649108543626897/2361183241434822606848), (-74097114487/1180591620717411303424)), (55115/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811189827558151/295147905179352825856), (-407370131697/590295810358705651712)), (75785/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824638733883595/73786976294838206464), (-508966792953/73786976294838206464)), (94735/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455991520821145/2305843009213693952), (-71531221503/1152921504606846976)), (13323/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398803508377885/288230376151711744), (-35739233719/72057594037927936)), (106591/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195654788579417/144115188075855872), (-249937452287/72057594037927936)), (23319/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493247189491461/36028797018963968), (-374432334301/18014398509481984)), (139931/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491267727915465/9007199254740992), (-934424733671/9007199254740992)), (5467/281474976710656), by norm_num⟩
  | 2 => ⟨((557990403874743/1125899906842624), (-232986319597/562949953421312)), (174989/2251799813685248), by norm_num⟩
  | 1 => ⟨((2222107646955517/2251799813685248), (-2783471381589/2251799813685248)), (32825/140737488355328), by norm_num⟩
  | 0 => ⟨((1096337661765271/1125899906842624), (-1379420347653/562949953421312)), (1051341/2251799813685248), by norm_num⟩
  | _ => zero

def term7ValueSquares : ℕ → Disk
  | 0 => ⟨((1096337661765271/1125899906842624), (-1379420347653/562949953421312)), (4010547646529387717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((66721553693303/70368744177664), (-5372806123693/1125899906842624)), (1026313/1125899906842624), by norm_num⟩
  | 2 => ⟨((506094348264841/562949953421312), (-20377340903547/2251799813685248)), (3912069/2251799813685248), by norm_num⟩
  | 3 => ⟨((454934822425593/562949953421312), (-36638628358613/2251799813685248)), (7104737/2251799813685248), by norm_num⟩
  | 4 => ⟨((183747944271145/281474976710656), (-3701081194017/140737488355328)), (5857127/1125899906842624), by norm_num⟩
  | 5 => ⟨((119756702388873/281474976710656), (-154629119829501/4503599627370496)), (7955169/1125899906842624), by norm_num⟩
  | 6 => ⟨((1619840609942079/9007199254740992), (-32894351214585/1125899906842624)), (58524059/9007199254740992), by norm_num⟩
  | _ => zero

def term7Value : CertifiedScalarExp.Data :=
  ⟨⟨((-57132171/33554432), (-1697437611/67108864)), (1/33554432), by norm_num⟩, -4, term7ValuePoly, term7ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term7Value_checks : CertifiedScalarExp.Checks term7Value := by
  constructor
  · norm_num [term7Value, CertifiedScalarExp.reduced, term7ValuePoly, term7ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term7ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value, term7ValueSquares, term7ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term7Value, CertifiedScalarExp.roundingCheck, term7ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term7 : Sound J_term7 F_term7 c := by
  apply exp_sound (A_arg7 hcre) S_arg7 term7Value term7Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term7Value,J_arg7]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term7,J_arg7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((519860385419959/250000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log8 : Sound J_log8 F_log8 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log8_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_negLog8 : Sound J_negLog8 F_negLog8 c := by
  apply sound_round (sound_scale (A_log8 hcre) S_log8)
  intro k
  fin_cases k <;> norm_num [J_negLog8, J_log8, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30526335/16777216), (-906959215/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((-1116391677/536870912), 0), (1/536870912), by norm_num⟩
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
theorem S_arg8 : Sound J_arg8 F_arg8 c := by
  apply sound_round (sound_mul (A_negLog8 hcre) (A_variable hcre) S_negLog8 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg8, J_negLog8, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-467545371100395/9007199254740992), (-1383230637202933/9007199254740992)), (23708407/1125899906842624), by norm_num⟩
  | 1 => ⟨((115899237/1073741824), (21430457/67108864)), (191/4294967296), by norm_num⟩
  | 2 => ⟨((-30125711/268435456), (-1426028241/4294967296)), (201/4294967296), by norm_num⟩
  | 3 => ⟨((167052413/2147483648), (988447455/4294967296)), (71/2147483648), by norm_num⟩
  | 4 => ⟨((-347375727/8589934592), (-513854675/4294967296)), (75/4294967296), by norm_num⟩
  | 5 => ⟨((288939007/17179869184), (427412303/8589934592)), (63/8589934592), by norm_num⟩
  | 6 => ⟨((-100138629/17179869184), (-1185038531/68719476736)), (177/68719476736), by norm_num⟩
  | 7 => ⟨((475959829/274877906944), (1408124771/274877906944)), (213/274877906944), by norm_num⟩
  | 8 => ⟨((-61858165/137438953472), (-366014143/274877906944)), (7/34359738368), by norm_num⟩
  | 9 => ⟨((114338167/1099511627776), (338268895/1099511627776)), (105/2199023255552), by norm_num⟩
  | 10 => ⟨((-380415255/17592186044416), (-281364157/4398046511104)), (177/17592186044416), by norm_num⟩
  | 11 => ⟨((287655013/70368744177664), (851025915/70368744177664)), (17/8796093022208), by norm_num⟩
  | 12 => ⟨((-199387261/281474976710656), (-1179772427/562949953421312)), (191/562949953421312), by norm_num⟩
  | _ => zero

def term8ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790802825208669/5070602400912917605986812821504), (-1235364121695/5070602400912917605986812821504)), (58233/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779157859290953/633825300114114700748351602688), (-2925209480253/633825300114114700748351602688)), (34683/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472544822417317/9903520314283042199192993792), (-3290326821085/39614081257132168796771975168)), (78051/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889981343097677/2475880078570760549798248448), (-3495322454305/2475880078570760549798248448)), (82945/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771647187977627/154742504910672534362390528), (-3494591549051/154742504910672534362390528)), (82963/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549980964960995/9671406556917033397649408), (-3275403129075/9671406556917033397649408)), (38899/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629581175635541/302231454903657293676544), (-2865201445681/604462909807314587353088)), (17023/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((944199225048485/37778931862957161709568), (-4654497132553/75557863725914323419136)), (110685/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324498388264845/1180591620717411303424), (-3489599866145/4722366482869645213696)), (83045/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622071358059269/590295810358705651712), (-4796131839405/590295810358705651712)), (57119/295147905179352825856), by norm_num⟩
  | 8 => ⟨((228031494737631/9223372036854775808), (-1498015980433/18446744073709551616)), (142875/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455882257892855/2305843009213693952), (-3368404986169/4611686018427387904)), (160839/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398693643723345/288230376151711744), (-6731485198537/1152921504606846976)), (40243/288230376151711744), by norm_num⟩
  | 5 => ⟨((298816890007399/36028797018963968), (-1471015705825/36028797018963968)), (140999/144115188075855872), by norm_num⟩
  | 4 => ⟨((373165238976021/9007199254740992), (-8814129897991/36028797018963968)), (211797/36028797018963968), by norm_num⟩
  | 3 => ⟨((372631383249261/2251799813685248), (-2749186323019/2251799813685248)), (66317/2251799813685248), by norm_num⟩
  | 2 => ⟨((278806142527175/562949953421312), (-5482705348721/1125899906842624)), (66513/562949953421312), by norm_num⟩
  | 1 => ⟨((1109884575538945/1125899906842624), (-16369923183437/1125899906842624)), (401043/1125899906842624), by norm_num⟩
  | 0 => ⟨((546930443784599/562949953421312), (-16213968457879/562949953421312)), (809967/1125899906842624), by norm_num⟩
  | _ => zero

def term8ValueSquares : ℕ → Disk
  | 0 => ⟨((546930443784599/562949953421312), (-16213968457879/562949953421312)), (3089778904441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((132724949948433/140737488355328), (-126020622760979/2251799813685248)), (810247/562949953421312), by norm_num⟩
  | 2 => ⟨((997822349496709/1125899906842624), (-118845952445819/1125899906842624)), (3237851/1125899906842624), by norm_num⟩
  | 3 => ⟨((1743538790219607/2251799813685248), (-210653090522437/1125899906842624)), (3211303/562949953421312), by norm_num⟩
  | 4 => ⟨((1271173661804885/2251799813685248), (-652423598888971/2251799813685248)), (24698371/2251799813685248), by norm_num⟩
  | 5 => ⟨((132141622763893/562949953421312), (-736605172633289/2251799813685248)), (10549277/562949953421312), by norm_num⟩
  | 6 => ⟨((-467545371100395/9007199254740992), (-1383230637202933/9007199254740992)), (23708407/1125899906842624), by norm_num⟩
  | _ => zero

def term8Value : CertifiedScalarExp.Data :=
  ⟨⟨((-30526335/16777216), (-906959215/33554432)), (3/67108864), by norm_num⟩, -4, term8ValuePoly, term8ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term8Value_checks : CertifiedScalarExp.Checks term8Value := by
  constructor
  · norm_num [term8Value, CertifiedScalarExp.reduced, term8ValuePoly, term8ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term8ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value, term8ValueSquares, term8ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term8Value, CertifiedScalarExp.roundingCheck, term8ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term8 : Sound J_term8 F_term8 c := by
  apply exp_sound (A_arg8 hcre) S_arg8 term8Value term8Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term8Value,J_arg8]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term8,J_arg8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term2Jet : Jet 12 := J_term2
theorem term2Jet_sound : Sound term2Jet F_term2 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term2

def term3Jet : Jet 12 := J_term3
theorem term3Jet_sound : Sound term3Jet F_term3 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term3

def term4Jet : Jet 12 := J_term4
theorem term4Jet_sound : Sound term4Jet F_term4 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term4

def term5Jet : Jet 12 := J_term5
theorem term5Jet_sound : Sound term5Jet F_term5 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term5

def term6Jet : Jet 12 := J_term6
theorem term6Jet_sound : Sound term6Jet F_term6 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term6

def term7Jet : Jet 12 := J_term7
theorem term7Jet_sound : Sound term7Jet F_term7 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term7

def term8Jet : Jet 12 := J_term8
theorem term8Jet_sound : Sound term8Jet F_term8 (Data.centre ⟨34,by norm_num [Data.count]⟩) := S_term8

end Reinmann.XiRectangle.Tile034Terms0
