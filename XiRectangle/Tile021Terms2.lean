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
namespace Reinmann.XiRectangle.Tile021Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6063/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6063/640))
  have he : value ((3/4), (6063/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-279097919/134217728), (-7050711185/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((238555228253579/4503599627370496), (-254952963422009/2251799813685248)), (19207441/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2523100035/17179869184), (2696532101/8589934592)), (13/2147483648), by norm_num⟩
  | 2 => ⟨((437219919/2147483648), (-1869093623/4294967296)), (37/4294967296), by norm_num⟩
  | 3 => ⟨((-808154011/4294967296), (431852325/1073741824)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((2240678697/17179869184), (-598674443/2147483648)), (99/17179869184), by norm_num⟩
  | 5 => ⟨((-1242496097/17179869184), (5311609629/34359738368)), (7/2147483648), by norm_num⟩
  | 6 => ⟨((574155111/17179869184), (-1227242413/17179869184)), (53/34359738368), by norm_num⟩
  | 7 => ⟨((-909654849/68719476736), (3888729685/137438953472)), (43/68719476736), by norm_num⟩
  | 8 => ⟨((315262347/68719476736), (-5390924035/549755813888)), (61/274877906944), by norm_num⟩
  | 9 => ⟨((-1553942805/1099511627776), (3321514485/1099511627776)), (77/1099511627776), by norm_num⟩
  | 10 => ⟨((1723377719/4398046511104), (-3683677441/4398046511104)), (87/4398046511104), by norm_num⟩
  | 11 => ⟨((-1737533683/17592186044416), (3713935465/17592186044416)), (45/8796093022208), by norm_num⟩
  | 12 => ⟨((802911049/35184372088832), (-3432405195/70368744177664)), (85/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98829191395547/633825300114114700748351602688), (-1476125704657/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111172501131445/39614081257132168796771975168), (-873452061839/316912650057057350374175801344)), (11547/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889731964712607/39614081257132168796771975168), (-1964908896037/39614081257132168796771975168)), (203/618970019642690137449562112), by norm_num⟩
  | 15 => ⟨((1889506372213007/2475880078570760549798248448), (-1043636385711/1237940039285380274899124224)), (6903/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771172567778953/154742504910672534362390528), (-2086774635663/154742504910672534362390528)), (13807/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549536380961405/9671406556917033397649408), (-244477762935/1208925819614629174706176)), (12947/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258773712520043/604462909807314587353088), (-1710815393855/604462909807314587353088)), (5665/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887767609693169/75557863725914323419136), (-694770900681/18889465931478580854784)), (18415/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297521032728009/4722366482869645213696), (-2083445578905/4722366482869645213696)), (6907/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621422633058897/590295810358705651712), (-715832318879/147573952589676412928)), (18999/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911721268012245/36893488147419103232), (-223565636871/4611686018427387904)), (23757/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455655117712153/2305843009213693952), (-1005320053301/2305843009213693952)), (26737/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398467139898639/288230376151711744), (-4017656544215/1152921504606846976)), (13375/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194477655867495/144115188075855872), (-1755688412453/72057594037927936)), (23421/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491481807176775/36028797018963968), (-328683116653/2251799813685248)), (35161/36028797018963968), by norm_num⟩
  | 3 => ⟨((744530780336105/4503599627370496), (-204982742343/281474976710656)), (44003/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113775494099961/2251799813685248), (-13076340933809/4503599627370496)), (44081/2251799813685248), by norm_num⟩
  | 1 => ⟨((553874015474415/562949953421312), (-19508436447651/2251799813685248)), (33159/562949953421312), by norm_num⟩
  | 0 => ⟨((1089735050628089/1125899906842624), (-38594437484381/2251799813685248)), (8339/70368744177664), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089735050628089/1125899906842624), (-38594437484381/2251799813685248)), (31810760766482331/268435456000000000000000000), by norm_num⟩
  | 1 => ⟨((1054401097914077/1125899906842624), (-74709503092415/2251799813685248)), (525701/2251799813685248), by norm_num⟩
  | 2 => ⟨((986203383685453/1125899906842624), (-34982586643143/562949953421312)), (509759/1125899906842624), by norm_num⟩
  | 3 => ⟨((1718984045808115/2251799813685248), (-245136855294967/2251799813685248)), (1912751/2251799813685248), by norm_num⟩
  | 4 => ⟨((160694461732665/281474976710656), (-187133128233983/1125899906842624)), (3336775/2251799813685248), by norm_num⟩
  | 5 => ⟨((1343439325375253/4503599627370496), (-213669134395713/1125899906842624)), (9838269/4503599627370496), by norm_num⟩
  | 6 => ⟨((238555228253579/4503599627370496), (-254952963422009/2251799813685248)), (19207441/9007199254740992), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/134217728), (-7050711185/268435456)), (1/134217728), by norm_num⟩, -4, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-570401187/268435456), (-7204879993/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-73322813211417/4503599627370496), (-1065812133909249/9007199254740992)), (22471377/9007199254740992), by norm_num⟩
  | 1 => ⟨((792462055/17179869184), (2879784737/8589934592)), (31/4294967296), by norm_num⟩
  | 2 => ⟨((-561303517/8589934592), (-4079522273/8589934592)), (45/4294967296), by norm_num⟩
  | 3 => ⟨((265048769/4294967296), (3852718981/8589934592)), (87/8589934592), by norm_num⟩
  | 4 => ⟨((-750939709/17179869184), (-2728893707/8589934592)), (125/17179869184), by norm_num⟩
  | 5 => ⟨((425514481/17179869184), (1546307613/8589934592)), (9/2147483648), by norm_num⟩
  | 6 => ⟨((-803715537/68719476736), (-5841359151/68719476736)), (69/34359738368), by norm_num⟩
  | 7 => ⟨((325299655/68719476736), (295532441/8589934592)), (57/68719476736), by norm_num⟩
  | 8 => ⟨((-921643323/549755813888), (-1674612911/137438953472)), (41/137438953472), by norm_num⟩
  | 9 => ⟨((580269369/1099511627776), (4217365019/1099511627776)), (105/1099511627776), by norm_num⟩
  | 10 => ⟨((-41100673/274877906944), (-1194869485/1099511627776)), (121/4398046511104), by norm_num⟩
  | 11 => ⟨((338754837/8796093022208), (4924102065/17592186044416)), (63/8796093022208), by norm_num⟩
  | 12 => ⟨((-319921575/35184372088832), (-4650343893/70368744177664)), (121/70368744177664), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-1112123135663/5070602400912917605986812821504)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889343926459597/316912650057057350374175801344), (-2632061347273/633825300114114700748351602688)), (5779/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472412669188881/9903520314283042199192993792), (-2960514620521/39614081257132168796771975168)), (13005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944709934638423/1237940039285380274899124224), (-3144864454015/2475880078570760549798248448)), (3455/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442771478422483/38685626227668133590597632), (-1572048517481/77371252455336267181195264)), (13823/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774727491133415/4835703278458516698824704), (-2946775796099/9671406556917033397649408)), (6481/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((39334447759507/18889465931478580854784), (-1288806940981/302231454903657293676544)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235956413742881/9444732965739290427392), (-2093547522361/37778931862957161709568)), (2305/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((81089596583607/295147905179352825856), (-3138985207477/4722366482869645213696)), (13835/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621301911717687/590295810358705651712), (-4313934470597/590295810358705651712)), (19031/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911645497984521/36893488147419103232), (-5389164437617/73786976294838206464)), (23799/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822449111960693/9223372036854775808), (-189323089903/288230376151711744)), (13395/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593696107465525/1152921504606846976), (-6052753962361/1152921504606846976)), (13405/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194325533332383/144115188075855872), (-5289882157845/144115188075855872)), (23481/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491251176952951/36028797018963968), (-3961140892425/18014398509481984)), (17633/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488769008325225/9007199254740992), (-9880935419099/9007199254740992)), (345/70368744177664), by norm_num⟩
  | 2 => ⟨((2226953156321207/4503599627370496), (-9848121606935/2251799813685248)), (22139/1125899906842624), by norm_num⟩
  | 1 => ⟨((2214567728197129/2251799813685248), (-29380725131925/2251799813685248)), (133425/2251799813685248), by norm_num⟩
  | 0 => ⟨((272186059622075/281474976710656), (-29054731993529/1125899906842624)), (269221/2251799813685248), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((272186059622075/281474976710656), (-29054731993529/1125899906842624)), (1026996621138762717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2104129918106161/2251799813685248), (-112383603077065/2251799813685248)), (534569/2251799813685248), by norm_num⟩
  | 2 => ⟨((1960535128921517/2251799813685248), (-210027285819887/2251799813685248)), (1052385/2251799813685248), by norm_num⟩
  | 3 => ⟨((1687355380284945/2251799813685248), (-365721561374535/2251799813685248)), (1014419/1125899906842624), by norm_num⟩
  | 4 => ⟨((301249682857199/562949953421312), (-274048448055245/1125899906842624)), (28903/17592186044416), by norm_num⟩
  | 5 => ⟨((1022836691094979/4503599627370496), (-586602823660699/2251799813685248)), (5760481/2251799813685248), by norm_num⟩
  | 6 => ⟨((-73322813211417/4503599627370496), (-1065812133909249/9007199254740992)), (22471377/9007199254740992), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-7204879993/268435456)), (1/134217728), by norm_num⟩, -4, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-72738587/33554432), (-1837558553/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-646672924259003/9007199254740992), (-802603175411963/9007199254740992)), (23390423/9007199254740992), by norm_num⟩
  | 1 => ⟨((3565073313/17179869184), (276544279/1073741824)), (131/17179869184), by norm_num⟩
  | 2 => ⟨((-2576096805/8589934592), (-3197263095/8589934592)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((1240979575/4294967296), (1540213159/4294967296)), (3/268435456), by norm_num⟩
  | 4 => ⟨((-896723079/4294967296), (-556473577/2147483648)), (141/17179869184), by norm_num⟩
  | 5 => ⟨((1036745225/8589934592), (1286732409/8589934592)), (83/17179869184), by norm_num⟩
  | 6 => ⟨((-499429853/8589934592), (-2479423343/34359738368)), (41/17179869184), by norm_num⟩
  | 7 => ⟨((3299515297/137438953472), (4095117261/137438953472)), (69/68719476736), by norm_num⟩
  | 8 => ⟨((-2384206457/274877906944), (-2959102819/274877906944)), (51/137438953472), by norm_num⟩
  | 9 => ⟨((1531387335/549755813888), (3801292097/1099511627776)), (67/549755813888), by norm_num⟩
  | 10 => ⟨((-3541022963/4398046511104), (-274678683/274877906944)), (157/4398046511104), by norm_num⟩
  | 11 => ⟨((3721771915/17592186044416), (4619191319/17592186044416)), (21/2199023255552), by norm_num⟩
  | 12 => ⟨((-224110509/4398046511104), (-2225196689/35184372088832)), (41/17592186044416), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996579415/5070602400912917605986812821504), (-2929593105727/10141204801825835211973625643008)), (9707/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778619050004871/633825300114114700748351602688), (-1733244041403/316912650057057350374175801344)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889573134812787/39614081257132168796771975168), (-3899049115907/39614081257132168796771975168)), (13017/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944668649070819/1237940039285380274899124224), (-1035455565443/618970019642690137449562112)), (6917/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771003137065211/154742504910672534362390528), (-4140790348991/154742504910672534362390528)), (6919/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774688580502649/4835703278458516698824704), (-485111847447/1208925819614629174706176)), (12977/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258634016700843/604462909807314587353088), (-1697343511673/302231454903657293676544)), (11359/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((58985621725403/2361183241434822606848), (-2757156072305/37778931862957161709568)), (577/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((648674813668271/2361183241434822606848), (-4133937184345/4722366482869645213696)), (6927/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621185945117851/590295810358705651712), (-5681244678115/590295810358705651712)), (4765/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823145169923287/73786976294838206464), (-7097179262043/73786976294838206464)), (745/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1822283866430951/9223372036854775808), (-7978311854727/9223372036854775808)), (3355/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796764687942129/576460752303423488), (-7970797821481/1152921504606846976)), (13433/576460752303423488), by norm_num⟩
  | 5 => ⟨((149272246936093/18014398509481984), (-3483000487359/72057594037927936)), (11769/72057594037927936), by norm_num⟩
  | 4 => ⟨((93189157187367/2251799813685248), (-10432122646613/36028797018963968)), (35365/36028797018963968), by norm_num⟩
  | 3 => ⟨((372120596194611/2251799813685248), (-6505325043665/4503599627370496)), (44309/9007199254740992), by norm_num⟩
  | 2 => ⟨((2174182238903/4398046511104), (-12966464680579/2251799813685248)), (44465/2251799813685248), by norm_num⟩
  | 1 => ⟨((1106819495657915/1125899906842624), (-9669738272273/562949953421312)), (33543/562949953421312), by norm_num⟩
  | 0 => ⟨((1087730615712303/1125899906842624), (-4779941230735/140737488355328)), (135733/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1087730615712303/1125899906842624), (-4779941230735/140737488355328)), (517780308250045421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2099113115710039/2251799813685248), (-147772664660579/2251799813685248)), (542967/2251799813685248), by norm_num⟩
  | 2 => ⟨((973541050469655/1125899906842624), (-17219089406131/140737488355328)), (1083565/2251799813685248), by norm_num⟩
  | 3 => ⟨((1649891541417279/2251799813685248), (-119111763215867/562949953421312)), (2139017/2251799813685248), by norm_num⟩
  | 4 => ⟨((277016221545745/562949953421312), (-349092293939813/1125899906842624)), (3945/2199023255552), by norm_num⟩
  | 5 => ⟨((657559405360659/4503599627370496), (-1374249737835151/4503599627370496)), (6480745/2251799813685248), by norm_num⟩
  | 6 => ⟨((-646672924259003/9007199254740992), (-802603175411963/9007199254740992)), (23390423/9007199254740992), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72738587/33554432), (-1837558553/67108864)), (1/134217728), by norm_num⟩, -4, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-592793865/268435456), (-7487727507/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-919006008672437/9007199254740992), (-367462615629047/9007199254740992)), (21929061/9007199254740992), by norm_num⟩
  | 1 => ⟨((2580601801/8589934592), (1031848191/8589934592)), (125/17179869184), by norm_num⟩
  | 2 => ⟨((-1899606133/4294967296), (-1519107017/8589934592)), (93/8589934592), by norm_num⟩
  | 3 => ⟨((1864424781/4294967296), (745486319/4294967296)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((-5489684999/17179869184), (-8574371/67108864)), (139/17179869184), by norm_num⟩
  | 5 => ⟨((3232808499/17179869184), (80789479/1073741824)), (21/4294967296), by norm_num⟩
  | 6 => ⟨((-3172935785/34359738368), (-634345843/17179869184)), (21/8589934592), by norm_num⟩
  | 7 => ⟨((5338580459/137438953472), (133413759/8589934592)), (143/137438953472), by norm_num⟩
  | 8 => ⟨((-3929781099/274877906944), (-1571314689/274877906944)), (107/274877906944), by norm_num⟩
  | 9 => ⟨((2571333477/549755813888), (1028142271/549755813888)), (71/549755813888), by norm_num⟩
  | 10 => ⟨((-3028453807/2199023255552), (-2421841743/4398046511104)), (169/4398046511104), by norm_num⟩
  | 11 => ⟨((1621290443/4398046511104), (1296539133/8796093022208)), (23/2199023255552), by norm_num⟩
  | 12 => ⟨((-198907949/2199023255552), (-1272526787/35184372088832)), (23/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (-1798396984439/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444638321448263/158456325028528675187087900672), (-4255679351185/633825300114114700748351602688)), (5789/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944749490656905/19807040628566084398385987584), (-4786693708351/39614081257132168796771975168)), (13029/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889258287105877/2475880078570760549798248448), (-1241385195/604462909807314587353088)), (13847/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770923875436289/154742504910672534362390528), (-5083422024905/154742504910672534362390528)), (13851/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774651293584009/4835703278458516698824704), (-4764335906539/9671406556917033397649408)), (12991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629284249376175/302231454903657293676544), (-4167421929459/604462909807314587353088)), (11371/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887432930560763/75557863725914323419136), (-6769488694441/75557863725914323419136)), (18487/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297268968575425/4722366482869645213696), (-2537433305413/2361183241434822606848)), (13873/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621074332876789/590295810358705651712), (-3487143248057/295147905179352825856)), (19087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911502298240557/36893488147419103232), (-8712377248273/73786976294838206464)), (11939/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822124268842739/9223372036854775808), (-9793891082215/9223372036854775808)), (3361/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593367966427603/1152921504606846976), (-9784478748975/1152921504606846976)), (3365/144115188075855872), by norm_num⟩
  | 5 => ⟨((298508677240899/36028797018963968), (-8550835976533/144115188075855872)), (23591/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490807561447533/36028797018963968), (-1600637874135/4503599627370496)), (35459/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488201627376305/9007199254740992), (-15969398090969/9007199254740992)), (22225/4503599627370496), by norm_num⟩
  | 2 => ⟨((34777812745537/70368744177664), (-3978498589247/562949953421312)), (44641/2251799813685248), by norm_num⟩
  | 1 => ⟨((553178197416735/562949953421312), (-23732718178473/1125899906842624)), (67439/1125899906842624), by norm_num⟩
  | 0 => ⟨((271675248722879/281474976710656), (-23456881909527/562949953421312)), (136797/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((271675248722879/281474976710656), (-23456881909527/562949953421312)), (521839146140670421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1046912024682581/1125899906842624), (-90560863370597/1125899906842624)), (137735/562949953421312), by norm_num⟩
  | 2 => ⟨((120772671580233/140737488355328), (-168415071805431/1125899906842624)), (139151/281474976710656), by norm_num⟩
  | 3 => ⟨((803928309193303/1125899906842624), (-578095812111277/2251799813685248)), (1121807/1125899906842624), by norm_num⟩
  | 4 => ⟨((499824212531811/1125899906842624), (-206389389482075/562949953421312)), (4356013/2251799813685248), by norm_num⟩
  | 5 => ⟨((70555048976493/1125899906842624), (-732984617519601/2251799813685248)), (14123141/4503599627370496), by norm_num⟩
  | 6 => ⟨((-919006008672437/9007199254740992), (-367462615629047/9007199254740992)), (21929061/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-7487727507/268435456)), (1/134217728), by norm_num⟩, -4, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-603120569/268435456), (-7618166689/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-473547604148181/4503599627370496), (200674861975649/18014398509481984)), (39728563/18014398509481984), by norm_num⟩
  | 1 => ⟨((5411612857/17179869184), (-286659317/8589934592)), (29/4294967296), by norm_num⟩
  | 2 => ⟨((-2026467911/4294967296), (107344321/2147483648)), (89/8589934592), by norm_num⟩
  | 3 => ⟨((4047170215/8589934592), (-214383231/4294967296)), (91/8589934592), by norm_num⟩
  | 4 => ⟨((-6062119215/17179869184), (160558691/4294967296)), (69/8589934592), by norm_num⟩
  | 5 => ⟨((7264194471/34359738368), (-192396341/8589934592)), (167/34359738368), by norm_num⟩
  | 6 => ⟨((-3626930303/34359738368), (768490571/68719476736)), (169/68719476736), by norm_num⟩
  | 7 => ⟨((6208749807/137438953472), (-82221143/17179869184)), (147/137438953472), by norm_num⟩
  | 8 => ⟨((-1162484511/68719476736), (492625063/274877906944)), (7/17179869184), by norm_num⟩
  | 9 => ⟨((6191097541/1099511627776), (-327949511/549755813888)), (151/1099511627776), by norm_num⟩
  | 10 => ⟨((-7418748285/4398046511104), (785959147/4398046511104)), (183/4398046511104), by norm_num⟩
  | 11 => ⟨((2020416697/4398046511104), (-107023781/2199023255552)), (101/8796093022208), by norm_num⟩
  | 12 => ⟨((-4035085003/35184372088832), (213743063/17592186044416)), (103/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((49407783133909/316912650057057350374175801344), (1977393193383/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889245984877291/316912650057057350374175801344), (4678954125481/633825300114114700748351602688)), (11583/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889429901448413/39614081257132168796771975168), (5262761075091/39614081257132168796771975168)), (13035/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944592378595149/1237940039285380274899124224), (2795199264829/1237940039285380274899124224)), (6927/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((110678137283171/9671406556917033397649408), (2794476411145/77371252455336267181195264)), (13859/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774616677509415/4835703278458516698824704), (1309526854543/2417851639229258349412352)), (6499/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((19664183790451/9444732965739290427392), (4581808375275/604462909807314587353088)), (11379/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943666969142781/37778931862957161709568), (1860639958707/18889465931478580854784)), (18499/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324298616415697/1180591620717411303424), (1394850363209/1180591620717411303424)), (13883/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405242867885113/147573952589676412928), (3833792753747/295147905179352825856)), (19103/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822875391053733/73786976294838206464), (4789173154907/36893488147419103232)), (11949/36893488147419103232), by norm_num⟩
  | 7 => ⟨((56936814056381/288230376151711744), (10767205886321/9223372036854775808)), (26913/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398305167783347/288230376151711744), (5378333903769/576460752303423488)), (26949/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193904618104629/144115188075855872), (2350058647341/36028797018963968)), (5905/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490610018474717/36028797018963968), (14076666426019/36028797018963968)), (35509/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487950505542285/9007199254740992), (17554415137605/9007199254740992)), (22263/4503599627370496), by norm_num⟩
  | 2 => ⟨((278158158360759/562949953421312), (4373087962599/562949953421312)), (699/35184372088832), by norm_num⟩
  | 1 => ⟨((1105954831319559/1125899906842624), (26083593084013/1125899906842624)), (33815/562949953421312), by norm_num⟩
  | 0 => ⟨((1085836635381413/1125899906842624), (51548797174969/1125899906842624)), (68685/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((1085836635381413/1125899906842624), (51548797174969/1125899906842624)), (262012483836936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1044838811244945/1125899906842624), (99429038304825/1125899906842624)), (277543/1125899906842624), by norm_num⟩
  | 2 => ⟨((960833197738899/1125899906842624), (92270474093007/562949953421312)), (564143/1125899906842624), by norm_num⟩
  | 3 => ⟨((1579438930434245/2251799813685248), (78742820867877/281474976710656)), (573901/562949953421312), by norm_num⟩
  | 4 => ⟨((931610210008545/2251799813685248), (220924570674681/562949953421312)), (2252361/1125899906842624), by norm_num⟩
  | 5 => ⟨((38624627295421/2251799813685248), (1462407693127597/4503599627370496)), (1815761/562949953421312), by norm_num⟩
  | 6 => ⟨((-473547604148181/4503599627370496), (200674861975649/18014398509481984)), (39728563/18014398509481984), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-603120569/268435456), (-7618166689/268435456)), (1/134217728), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-612943327/268435456), (-7742240395/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-774120480988121/9007199254740992), (123435755220533/2251799813685248)), (10405123/4503599627370496), by norm_num⟩
  | 1 => ⟨((280955693/1073741824), (-2867148791/17179869184)), (123/17179869184), by norm_num⟩
  | 2 => ⟨((-3421503645/8589934592), (2182274707/8589934592)), (3/268435456), by norm_num⟩
  | 3 => ⟨((3472281539/8589934592), (-2214661437/8589934592)), (99/8589934592), by norm_num⟩
  | 4 => ⟨((-660714941/2147483648), (1685646609/8589934592)), (77/8589934592), by norm_num⟩
  | 5 => ⟨((3218498341/17179869184), (-2052795569/17179869184)), (3/536870912), by norm_num⟩
  | 6 => ⟨((-204141467/2147483648), (2083260723/34359738368)), (99/34359738368), by norm_num⟩
  | 7 => ⟨((2841203551/68719476736), (-7078721/268435456)), (11/8589934592), by norm_num⟩
  | 8 => ⟨((-4325053981/274877906944), (2758569589/274877906944)), (17/34359738368), by norm_num⟩
  | 9 => ⟨((91442527/17179869184), (-233292417/68719476736)), (47/274877906944), by norm_num⟩
  | 10 => ⟨((-3563504963/2199023255552), (1136422397/1099511627776)), (29/549755813888), by norm_num⟩
  | 11 => ⟨((7705377/17179869184), (-1258132177/4398046511104)), (65/4398046511104), by norm_num⟩
  | 12 => ⟨((-4003702301/35184372088832), (1276803881/17592186044416)), (67/17592186044416), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394305331/10141204801825835211973625643008), (1676352754511/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778438875716133/633825300114114700748351602688), (3966385564685/633825300114114700748351602688)), (11575/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472342592119803/9903520314283042199192993792), (4461278076975/39614081257132168796771975168)), (13025/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944560880609163/1237940039285380274899124224), (296187616579/154742504910672534362390528)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770787490387697/154742504910672534362390528), (592219712415/19342813113834066795298816)), (6923/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549174875754173/9671406556917033397649408), (4440326185627/9671406556917033397649408)), (12985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258456900753365/604462909807314587353088), (3883964056941/604462909807314587353088)), (11367/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887251863930375/75557863725914323419136), (6308964692893/75557863725914323419136)), (18479/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648566706766799/2361183241434822606848), (4729556874533/4722366482869645213696)), (6933/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((810444171192087/295147905179352825856), (101556579817/9223372036854775808)), (19077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822772704335189/73786976294838206464), (2029812275493/18446744073709551616)), (2983/9223372036854775808), by norm_num⟩
  | 7 => ⟨((910932104359593/4611686018427387904), (4563451200795/4611686018427387904)), (13435/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593108928103293/1152921504606846976), (2279460373949/288230376151711744)), (26901/1152921504606846976), by norm_num⟩
  | 5 => ⟨((596904599030921/72057594037927936), (3983962431611/72057594037927936)), (23571/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490471585630389/36028797018963968), (5965766048587/18014398509481984)), (35425/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487785655407681/9007199254740992), (14878833363347/9007199254740992)), (44399/9007199254740992), by norm_num⟩
  | 2 => ⟨((69530000708539/140737488355328), (7412770234745/1125899906842624)), (44577/2251799813685248), by norm_num⟩
  | 1 => ⟨((552878132166495/562949953421312), (2763169734161/140737488355328)), (33655/562949953421312), by norm_num⟩
  | 0 => ⟨((1085559745433279/1125899906842624), (43680583232649/1125899906842624)), (68205/562949953421312), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1085559745433279/1125899906842624), (43680583232649/1125899906842624)), (260181429149436773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((522485151834227/562949953421312), (21057770111815/281474976710656)), (273631/1125899906842624), by norm_num⟩
  | 2 => ⟨((240889099919623/281474976710656), (312706226116061/2251799813685248)), (1097735/2251799813685248), by norm_num⟩
  | 3 => ⟨((1605817060476583/2251799813685248), (535234230968911/2251799813685248)), (2183789/2251799813685248), by norm_num⟩
  | 4 => ⟨((1017929185261567/2251799813685248), (381689462010533/1125899906842624)), (1038193/562949953421312), by norm_num⟩
  | 5 => ⟨((50341114007115/562949953421312), (1380345946299527/4503599627370496)), (3285091/1125899906842624), by norm_num⟩
  | 6 => ⟨((-774120480988121/9007199254740992), (123435755220533/2251799813685248)), (10405123/4503599627370496), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-612943327/268435456), (-7742240395/268435456)), (1/134217728), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile021Terms2
