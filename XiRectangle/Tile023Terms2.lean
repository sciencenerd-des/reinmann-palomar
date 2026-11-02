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
namespace Reinmann.XiRectangle.Tile023Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-279097919/134217728), (-7706591295/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-510532909684433/4503599627370496), (7412826674327/140737488355328)), (4704545/1125899906842624), by norm_num⟩
  | 1 => ⟨((5399695541/17179869184), (-2508876909/17179869184)), (201/17179869184), by norm_num⟩
  | 2 => ⟨((-935695935/2147483648), (434755239/2147483648)), (141/8589934592), by norm_num⟩
  | 3 => ⟨((3459066663/8589934592), (-803598315/4294967296)), (33/2147483648), by norm_num⟩
  | 4 => ⟨((-2397642305/8589934592), (1114023813/8589934592)), (185/17179869184), by norm_num⟩
  | 5 => ⟨((1329535203/8589934592), (-154436493/2147483648)), (207/34359738368), by norm_num⟩
  | 6 => ⟨((-4915005747/68719476736), (570918505/17179869184)), (97/34359738368), by norm_num⟩
  | 7 => ⟨((3893511287/137438953472), (-7066617/536870912)), (39/34359738368), by norm_num⟩
  | 8 => ⟨((-2698776371/274877906944), (2507881293/549755813888)), (219/549755813888), by norm_num⟩
  | 9 => ⟨((831399659/274877906944), (-6035871/4294967296)), (137/1099511627776), by norm_num⟩
  | 10 => ⟨((-3688206909/4398046511104), (1713662757/4398046511104)), (77/2199023255552), by norm_num⟩
  | 11 => ⟨((3718502139/17592186044416), (-1727738921/17592186044416)), (157/17592186044416), by norm_num⟩
  | 12 => ⟨((-1718312849/35184372088832), (199596227/8796093022208)), (147/70368744177664), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98829191395547/633825300114114700748351602688), (1762848282495/5070602400912917605986812821504)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444688083132411/158456325028528675187087900672), (260777835891/39614081257132168796771975168)), (8683/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889722884915493/39614081257132168796771975168), (2346562537545/19807040628566084398385987584)), (19541/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889496160240537/2475880078570760549798248448), (4985385087105/2475880078570760549798248448)), (649/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((885580860508675/77371252455336267181195264), (4984192314695/154742504910672534362390528)), (10387/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((387381384522587/2417851639229258349412352), (2335706576419/4835703278458516698824704)), (19483/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157345443932619/75557863725914323419136), (1021554891737/151115727451828646838272)), (8527/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887749836102157/75557863725914323419136), (1659432926645/18889465931478580854784)), (27725/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297506599428493/4722366482869645213696), (4976221002889/4722366482869645213696)), (10403/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621400996654553/590295810358705651712), (6838928291533/590295810358705651712)), (14313/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823412807968465/73786976294838206464), (533974899065/4611686018427387904)), (17905/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455645835940003/2305843009213693952), (4802295120955/4611686018427387904)), (10081/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593826836939305/1152921504606846976), (9595896240249/1152921504606846976)), (40371/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597217994908229/72057594037927936), (8386633174641/144115188075855872)), (17689/72057594037927936), by norm_num⟩
  | 4 => ⟨((186426127352877/4503599627370496), (6280204751293/18014398509481984)), (53173/36028797018963968), by norm_num⟩
  | 3 => ⟨((744476316151437/4503599627370496), (15666343058519/9007199254740992)), (16663/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113639777723541/2251799813685248), (15615143240999/2251799813685248)), (16733/562949953421312), by norm_num⟩
  | 1 => ⟨((1107477927663791/1125899906842624), (11647451451611/562949953421312)), (101101/1125899906842624), by norm_num⟩
  | 0 => ⟨((1088931368598097/1125899906842624), (46079688602057/1125899906842624)), (51255/281474976710656), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1088931368598097/1125899906842624), (46079688602057/1125899906842624)), (195522309423351199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((262822694233669/281474976710656), (22283338895873/281474976710656)), (413359/1125899906842624), by norm_num⟩
  | 2 => ⟨((974569351966129/1125899906842624), (166453650227119/1125899906842624)), (104673/140737488355328), by norm_num⟩
  | 3 => ⟨((1637940634889199/2251799813685248), (576323437095425/2251799813685248)), (106079/70368744177664), by norm_num⟩
  | 4 => ⟨((521960434713031/1125899906842624), (838425841160989/2251799813685248)), (6675889/2251799813685248), by norm_num⟩
  | 5 => ⟨((85889715450261/1125899906842624), (1554756737672237/4503599627370496)), (22322301/4503599627370496), by norm_num⟩
  | 6 => ⟨((-510532909684433/4503599627370496), (7412826674327/140737488355328)), (4704545/1125899906842624), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-279097919/134217728), (-7706591295/268435456)), (3/268435456), by norm_num⟩, -5, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-570401187/268435456), (-1968775347/67108864)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-261707055944607/4503599627370496), (469972901349739/4503599627370496)), (3006059/1125899906842624), by norm_num⟩
  | 1 => ⟨((1414245459/8589934592), (-79365581/268435456)), (33/4294967296), by norm_num⟩
  | 2 => ⟨((-2003429553/8589934592), (3597753971/8589934592)), (3/268435456), by norm_num⟩
  | 3 => ⟨((1892047781/8589934592), (-3397734853/8589934592)), (93/8589934592), by norm_num⟩
  | 4 => ⟨((-2680287511/17179869184), (4813253863/17179869184)), (67/8589934592), by norm_num⟩
  | 5 => ⟨((3037530537/34359738368), (-2727395015/17179869184)), (77/17179869184), by norm_num⟩
  | 6 => ⟨((-1434328675/34359738368), (160985249/2147483648)), (37/17179869184), by norm_num⟩
  | 7 => ⟨((2322148081/137438953472), (-2085053969/68719476736)), (61/68719476736), by norm_num⟩
  | 8 => ⟨((-1644785233/274877906944), (738425341/68719476736)), (11/34359738368), by norm_num⟩
  | 9 => ⟨((258890415/137438953472), (-3719318275/1099511627776)), (113/1099511627776), by norm_num⟩
  | 10 => ⟨((-2347173691/4398046511104), (4215048867/4398046511104)), (65/2199023255552), by norm_num⟩
  | 11 => ⟨((1209098877/8796093022208), (-1085648427/4398046511104)), (17/2199023255552), by norm_num⟩
  | 12 => ⟨((-2283756715/70368744177664), (2050582407/35184372088832)), (65/35184372088832), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (338497923109/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444671516054513/158456325028528675187087900672), (801122889163/158456325028528675187087900672)), (11565/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889648563808159/39614081257132168796771975168), (3604374402853/39614081257132168796771975168)), (13013/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889417492873145/2475880078570760549798248448), (3828816653309/2475880078570760549798248448)), (6915/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885541694791621/77371252455336267181195264), (3827881799679/154742504910672534362390528)), (13833/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387363114771217/2417851639229258349412352), (3587646126267/9671406556917033397649408)), (3243/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258699963803345/604462909807314587353088), (3138197548049/604462909807314587353088)), (5677/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((117977948376889/4722366482869645213696), (5097710020307/75557863725914323419136)), (2307/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((162178773343597/590295810358705651712), (955413668097/1180591620717411303424)), (13849/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621296877053193/590295810358705651712), (5252130919919/590295810358705651712)), (9525/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455821019633321/18446744073709551616), (6561199000399/73786976294838206464)), (23827/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822440473002965/9223372036854775808), (3687950148711/4611686018427387904)), (3353/1152921504606846976), by norm_num⟩
  | 6 => ⟨((796843199702965/576460752303423488), (7369093797167/1152921504606846976)), (26849/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194315838720631/144115188075855872), (3220152782461/72057594037927936)), (735/4503599627370496), by norm_num⟩
  | 4 => ⟨((1491234241607127/36028797018963968), (602823115237/2251799813685248)), (17667/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488743665673747/9007199254740992), (6014870035385/4503599627370496)), (44263/9007199254740992), by norm_num⟩
  | 2 => ⟨((556722502652023/1125899906842624), (11989722004741/2251799813685248)), (22203/1125899906842624), by norm_num⟩
  | 1 => ⟨((138402629252457/140737488355328), (35769532589163/2251799813685248)), (8371/140737488355328), by norm_num⟩
  | 0 => ⟨((2177114642505773/2251799813685248), (35371636086335/1125899906842624)), (135379/1125899906842624), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((2177114642505773/2251799813685248), (35371636086335/1125899906842624)), (516429905418014171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2102684051788081/2251799813685248), (136793877297495/2251799813685248)), (540569/2251799813685248), by norm_num⟩
  | 2 => ⟨((1955132792009921/2251799813685248), (255470581734317/2251799813685248)), (1075223/2251799813685248), by norm_num⟩
  | 3 => ⟨((208570883689687/281474976710656), (443626390505093/2251799813685248)), (2111105/2251799813685248), by norm_num⟩
  | 4 => ⟨((1148997204547809/2251799813685248), (328723886496055/1125899906842624)), (3960443/2251799813685248), by norm_num⟩
  | 5 => ⟨((98583030832699/562949953421312), (670934999384191/2251799813685248)), (6354315/2251799813685248), by norm_num⟩
  | 6 => ⟨((-261707055944607/4503599627370496), (469972901349739/4503599627370496)), (3006059/1125899906842624), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-1968775347/67108864)), (1/134217728), by norm_num⟩, -5, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-72738587/33554432), (-4016988465/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((172474822266449/18014398509481984), (2054186785150823/18014398509481984)), (80876827/18014398509481984), by norm_num⟩
  | 1 => ⟨((-118855561/4294967296), (-707788881/2147483648)), (225/17179869184), by norm_num⟩
  | 2 => ⟨((343536757/8589934592), (4091545985/8589934592)), (41/2147483648), by norm_num⟩
  | 3 => ⟨((-82745745/2147483648), (-1971014827/4294967296)), (159/8589934592), by norm_num⟩
  | 4 => ⟨((478331929/17179869184), (5696965591/17179869184)), (29/2147483648), by norm_num⟩
  | 5 => ⟨((-553022839/34359738368), (-1646634845/8589934592)), (271/34359738368), by norm_num⟩
  | 6 => ⟨((532813865/68719476736), (396615571/4294967296)), (263/68719476736), by norm_num⟩
  | 7 => ⟨((-220004307/68719476736), (-5240532321/137438953472)), (219/137438953472), by norm_num⟩
  | 8 => ⟨((158973559/137438953472), (7573543309/549755813888)), (319/549755813888), by norm_num⟩
  | 9 => ⟨((-204218971/549755813888), (-2432261743/549755813888)), (207/1099511627776), by norm_num⟩
  | 10 => ⟨((472214997/4398046511104), (703014065/549755813888)), (241/4398046511104), by norm_num⟩
  | 11 => ⟨((-496318869/17592186044416), (-2955595635/8796093022208)), (1/68719476736), by norm_num⟩
  | 12 => ⟨((239091007/35184372088832), (5695180101/70368744177664)), (31/8796093022208), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790575996579415/5070602400912917605986812821504), (1937022889991/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889311335689537/316912650057057350374175801344), (71625419917/19807040628566084398385987584)), (5777/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889577412195615/39614081257132168796771975168), (322253062137/4951760157141521099596496896)), (25999/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944671054416075/1237940039285380274899124224), (2738545047863/2475880078570760549798248448)), (27629/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771008246725877/154742504910672534362390528), (2737863528075/154742504910672534362390528)), (27633/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549382268756347/9671406556917033397649408), (1283011572789/4835703278458516698824704)), (25911/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((39332462599661/18889465931478580854784), (2244546568481/604462909807314587353088)), (22677/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943774133756171/37778931862957161709568), (3646031751031/75557863725914323419136)), (36859/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297356426029789/4722366482869645213696), (1366668713887/2361183241434822606848)), (27653/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202649517063853/73786976294838206464), (1878205997349/295147905179352825856)), (9509/147573952589676412928), by norm_num⟩
  | 8 => ⟨((56973724134169/2305843009213693952), (4692626128891/73786976294838206464)), (47565/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822301353211255/9223372036854775808), (1318808696511/2305843009213693952)), (26769/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398387256569599/288230376151711744), (2635138321141/576460752303423488)), (13393/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194197598116281/144115188075855872), (4605919464547/144115188075855872)), (46915/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491060792191381/36028797018963968), (6897747277301/36028797018963968)), (35225/18014398509481984), by norm_num⟩
  | 3 => ⟨((744266837967347/4503599627370496), (8602733078681/9007199254740992)), (88199/9007199254740992), by norm_num⟩
  | 2 => ⟨((2226490405096839/4503599627370496), (17147232326481/4503599627370496)), (176809/4503599627370496), by norm_num⟩
  | 1 => ⟨((2213893273096787/2251799813685248), (12787840277271/1125899906842624)), (266243/2251799813685248), by norm_num⟩
  | 0 => ⟨((1088108791556607/1125899906842624), (50573184116455/2251799813685248)), (268311/1125899906842624), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((1088108791556607/1125899906842624), (50573184116455/2251799813685248)), (1023525242332076671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((525509116455707/562949953421312), (12218920598467/281474976710656)), (1061325/2251799813685248), by norm_num⟩
  | 2 => ⟨((1957990203008047/2251799813685248), (91250088981707/1125899906842624)), (2073623/2251799813685248), by norm_num⟩
  | 3 => ⟨((1687725212970477/2251799813685248), (317375957070345/2251799813685248)), (3942243/2251799813685248), by norm_num⟩
  | 4 => ⟨((610109495451355/1125899906842624), (118936728185805/562949953421312)), (7020693/2251799813685248), by norm_num⟩
  | 5 => ⟨((1121413416149617/4503599627370496), (1031202532773199/4503599627370496)), (10575413/2251799813685248), by norm_num⟩
  | 6 => ⟨((172474822266449/18014398509481984), (2054186785150823/18014398509481984)), (80876827/18014398509481984), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-72738587/33554432), (-4016988465/134217728)), (1/67108864), by norm_num⟩, -5, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-74099233/33554432), (-4092130149/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((593939111633027/9007199254740992), (395865241222371/4503599627370496)), (7638351/2251799813685248), by norm_num⟩
  | 1 => ⟨((-3335604613/17179869184), (-2223207563/8589934592)), (87/8589934592), by norm_num⟩
  | 2 => ⟨((613842765/2147483648), (3273049503/8589934592)), (65/4294967296), by norm_num⟩
  | 3 => ⟨((-150618547/536870912), (-401553939/1073741824)), (65/4294967296), by norm_num⟩
  | 4 => ⟨((1773948483/8589934592), (4729404281/17179869184)), (97/8589934592), by norm_num⟩
  | 5 => ⟨((-261164153/2147483648), (-2785088463/17179869184)), (29/4294967296), by norm_num⟩
  | 6 => ⟨((32040913/536870912), (2733507677/34359738368)), (115/34359738368), by norm_num⟩
  | 7 => ⟨((-3450240481/137438953472), (-2299613301/68719476736)), (49/34359738368), by norm_num⟩
  | 8 => ⟨((317469455/34359738368), (105797985/8589934592)), (73/137438953472), by norm_num⟩
  | 9 => ⟨((-830906167/274877906944), (-4430445667/1099511627776)), (193/1099511627776), by norm_num⟩
  | 10 => ⟨((1957242005/2199023255552), (2609035383/2199023255552)), (115/2199023255552), by norm_num⟩
  | 11 => ⟨((-523907241/2199023255552), (-2793507447/8796093022208)), (31/2199023255552), by norm_num⟩
  | 12 => ⟨((1028408601/17592186044416), (1370885369/17592186044416)), (31/8796093022208), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581099171721355/10141204801825835211973625643008), (603878417447/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778561890994967/633825300114114700748351602688), (178625251683/79228162514264337593543950336)), (11543/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889509144317561/39614081257132168796771975168), (401829387335/9903520314283042199192993792)), (12987/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889269717175621/2475880078570760549798248448), (1707390216491/2475880078570760549798248448)), (1725/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885468007887085/77371252455336267181195264), (106684850829/9671406556917033397649408)), (27603/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549314722882263/9671406556917033397649408), (24997082307/151115727451828646838272)), (25881/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314644967768369/151115727451828646838272), (174922159855/75557863725914323419136)), (22649/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887452822304429/75557863725914323419136), (1136563591495/37778931862957161709568)), (18405/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324321280354089/1180591620717411303424), (1704092453137/4722366482869645213696)), (27613/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810549273022241/295147905179352825856), (2341904259429/590295810358705651712)), (4747/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911518931724393/36893488147419103232), (1462773586591/36893488147419103232)), (23741/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911082906685263/4611686018427387904), (3288721845389/9223372036854775808)), (26717/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593414650186979/1152921504606846976), (3285576225175/1152921504606846976)), (3341/72057594037927936), by norm_num⟩
  | 5 => ⟨((1194081325490733/144115188075855872), (1435672100311/72057594037927936)), (46799/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490888989264167/36028797018963968), (2149977931727/18014398509481984)), (35123/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488323467305497/9007199254740992), (5362610534393/9007199254740992)), (87893/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113041780560541/2251799813685248), (10688303922619/4503599627370496)), (88021/2251799813685248), by norm_num⟩
  | 1 => ⟨((2213316724697025/2251799813685248), (15940462456463/2251799813685248)), (66177/562949953421312), by norm_num⟩
  | 0 => ⟨((8496867453709/8796093022208), (31514742663163/2251799813685248)), (532009/2251799813685248), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((8496867453709/8796093022208), (31514742663163/2251799813685248)), (2029453286177825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2100761101376229/2251799813685248), (60885347749409/2251799813685248)), (1042715/2251799813685248), by norm_num⟩
  | 2 => ⟨((489551752412265/562949953421312), (113602967207281/2251799813685248)), (1000969/1125899906842624), by norm_num⟩
  | 3 => ⟨((212145249061125/281474976710656), (197582507423837/2251799813685248)), (3683841/2251799813685248), by norm_num⟩
  | 4 => ⟨((630899772759839/1125899906842624), (297832444911361/2251799813685248)), (6199431/2251799813685248), by norm_num⟩
  | 5 => ⟨((1335317570145189/4503599627370496), (333781752131097/2251799813685248)), (17175295/4503599627370496), by norm_num⟩
  | 6 => ⟨((593939111633027/9007199254740992), (395865241222371/4503599627370496)), (7638351/2251799813685248), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-74099233/33554432), (-4092130149/134217728)), (1/67108864), by norm_num⟩, -5, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-301560285/134217728), (-4163416679/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((878670508253549/9007199254740992), (183708372701491/4503599627370496)), (20837299/9007199254740992), by norm_num⟩
  | 1 => ⟨((-5020640563/17179869184), (-2099384693/17179869184)), (121/17179869184), by norm_num⟩
  | 2 => ⟨((1880061871/4294967296), (393074655/2147483648)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((-1877387341/4294967296), (-785030953/4294967296)), (47/4294967296), by norm_num⟩
  | 4 => ⟨((5624149847/17179869184), (1175871281/8589934592)), (143/17179869184), by norm_num⟩
  | 5 => ⟨((-3369689441/17179869184), (-704519109/8589934592)), (11/2147483648), by norm_num⟩
  | 6 => ⟨((3364895803/34359738368), (1407033755/34359738368)), (45/17179869184), by norm_num⟩
  | 7 => ⟨((-5760186831/137438953472), (-2408626531/137438953472)), (39/34359738368), by norm_num⟩
  | 8 => ⟨((2156997199/137438953472), (901950029/137438953472)), (119/274877906944), by norm_num⟩
  | 9 => ⟨((-5743809887/1099511627776), (-2401778499/1099511627776)), (161/1099511627776), by norm_num⟩
  | 10 => ⟨((1720691665/1099511627776), (1439017073/2199023255552)), (49/1099511627776), by norm_num⟩
  | 11 => ⟨((-3748895675/8796093022208), (-1567603595/8796093022208)), (109/8796093022208), by norm_num⟩
  | 12 => ⟨((935890647/8796093022208), (1565373561/35184372088832)), (111/35184372088832), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060280235/10141204801825835211973625643008), (515905870859/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((222312936963073/79228162514264337593543950336), (610374282383/633825300114114700748351602688)), (11533/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889443512645725/39614081257132168796771975168), (85817118175/4951760157141521099596496896)), (12975/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((14759375509967/19342813113834066795298816), (729278378365/2475880078570760549798248448)), (27573/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885433227884879/77371252455336267181195264), (364545219471/77371252455336267181195264)), (13787/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549249607957649/9671406556917033397649408), (341661334371/4835703278458516698824704)), (6463/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258522993027121/604462909807314587353088), (597707793759/604462909807314587353088)), (11311/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887360578173433/75557863725914323419136), (242725296745/18889465931478580854784)), (36763/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297216098033801/4722366482869645213696), (727848821737/4722366482869645213696)), (27575/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810501949082859/295147905179352825856), (500130473713/295147905179352825856)), (37919/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911459971022035/36893488147419103232), (624764970989/36893488147419103232)), (47403/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822033685146125/9223372036854775808), (702313607205/4611686018427387904)), (6667/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1593283187527499/1152921504606846976), (87703815291/72057594037927936)), (53345/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193967042872795/144115188075855872), (1226318249321/144115188075855872)), (1459/4503599627370496), by norm_num⟩
  | 4 => ⟨((1490719055883685/36028797018963968), (1836411479485/36028797018963968)), (17513/9007199254740992), by norm_num⟩
  | 3 => ⟨((744056825171623/4503599627370496), (572539749385/2251799813685248)), (87603/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112835845904015/2251799813685248), (285268232367/281474976710656)), (43829/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212718211298339/2251799813685248), (6806510766393/2251799813685248)), (131627/1125899906842624), by norm_num⟩
  | 0 => ⟨((543519370304671/562949953421312), (13454144863391/2251799813685248)), (527645/2251799813685248), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((543519370304671/562949953421312), (13454144863391/2251799813685248)), (2012805947310637717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((524739349786271/562949953421312), (25979532637657/2251799813685248)), (256293/562949953421312), by norm_num⟩
  | 2 => ⟨((489047383401811/562949953421312), (48432309057615/2251799813685248)), (120927/140737488355328), by norm_num⟩
  | 3 => ⟨((1698344488524961/2251799813685248), (5259280570321/140737488355328)), (107653/70368744177664), by norm_num⟩
  | 4 => ⟨((1277774789745697/2251799813685248), (126932351494859/2251799813685248)), (5453863/2251799813685248), by norm_num⟩
  | 5 => ⟨((358956551472477/1125899906842624), (72027254713123/1125899906842624)), (13608813/4503599627370496), by norm_num⟩
  | 6 => ⟨((878670508253549/9007199254740992), (183708372701491/4503599627370496)), (20837299/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-301560285/134217728), (-4163416679/134217728)), (1/67108864), by norm_num⟩, -5, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-306471663/134217728), (-2115612201/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((912710453841739/9007199254740992), (-100021615085123/9007199254740992)), (15756675/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1325019577/4294967296), (580822089/17179869184)), (93/17179869184), by norm_num⟩
  | 2 => ⟨((4034051833/8589934592), (-442081471/8589934592)), (73/8589934592), by norm_num⟩
  | 3 => ⟨((-511740055/1073741824), (448642319/8589934592)), (19/2147483648), by norm_num⟩
  | 4 => ⟨((6232016319/17179869184), (-682950803/17179869184)), (59/8589934592), by norm_num⟩
  | 5 => ⟨((-3794702703/17179869184), (831703617/34359738368)), (73/17179869184), by norm_num⟩
  | 6 => ⟨((7702038349/68719476736), (-422023387/34359738368)), (151/68719476736), by norm_num⟩
  | 7 => ⟨((-6699722449/137438953472), (367102763/68719476736)), (67/68719476736), by norm_num⟩
  | 8 => ⟨((5099363831/274877906944), (-558826299/274877906944)), (13/34359738368), by norm_num⟩
  | 9 => ⟨((-862507089/137438953472), (756159647/1099511627776)), (143/1099511627776), by norm_num⟩
  | 10 => ⟨((525184437/274877906944), (-230214501/1099511627776)), (89/2199023255552), by norm_num⟩
  | 11 => ⟨((-4651449607/8796093022208), (509740519/8796093022208)), (25/2199023255552), by norm_num⟩
  | 12 => ⟨((4720480899/35184372088832), (-517305483/35184372088832)), (103/35184372088832), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197625174288773/1267650600228229401496703205376), (-71091264973/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889223643811267/316912650057057350374175801344), (-168207655821/633825300114114700748351602688)), (23055/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944690150672623/19807040628566084398385987584), (-23649512621/4951760157141521099596496896)), (25937/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944566466186451/1237940039285380274899124224), (-200974053905/2475880078570760549798248448)), (13779/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442699838896727/38685626227668133590597632), (-200921422583/154742504910672534362390528)), (27559/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387296684070927/2417851639229258349412352), (-23538491549/1208925819614629174706176)), (25837/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629234007520077/302231454903657293676544), (-164713561509/604462909807314587353088)), (1413/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943635652008583/37778931862957161709568), (-33444351289/9444732965739290427392)), (18369/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297149199313171/4722366482869645213696), (-100287259037/2361183241434822606848)), (13777/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620912004803249/590295810358705651712), (-275641216453/590295810358705651712)), (37/576460752303423488), by norm_num⟩
  | 8 => ⟨((1822805213771273/73786976294838206464), (-172164277195/36893488147419103232)), (47361/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821904805957979/9223372036854775808), (-387063293091/9223372036854775808)), (53283/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796577272826921/576460752303423488), (-386680751349/1152921504606846976)), (53285/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193854747753605/144115188075855872), (-337915808239/144115188075855872)), (11657/36028797018963968), by norm_num⟩
  | 4 => ⟨((372637786275247/9007199254740992), (-506015287997/36028797018963968)), (17487/9007199254740992), by norm_num⟩
  | 3 => ⟨((1487904690113331/9007199254740992), (-315509864691/4503599627370496)), (87445/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225256545841069/4503599627370496), (-314388185597/1125899906842624)), (43731/1125899906842624), by norm_num⟩
  | 1 => ⟨((553025598203601/562949953421312), (-1875152210207/2251799813685248)), (262471/2251799813685248), by norm_num⟩
  | 0 => ⟨((1086436616232287/1125899906842624), (-1852917660951/1125899906842624)), (525295/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((1086436616232287/1125899906842624), (-1852917660951/1125899906842624)), (2003841408736418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2096706964114509/2251799813685248), (-3575944151849/1125899906842624)), (126937/281474976710656), by norm_num⟩
  | 2 => ⟨((1952273429077765/2251799813685248), (-3329650780189/562949953421312)), (1897559/2251799813685248), by norm_num⟩
  | 3 => ⟨((1692510201631399/2251799813685248), (-11547010008199/1125899906842624)), (3312753/2251799813685248), by norm_num⟩
  | 4 => ⟨((1271897009432017/2251799813685248), (-34716109519935/2251799813685248)), (2523925/1125899906842624), by norm_num⟩
  | 5 => ⟨((358938832954327/1125899906842624), (-78435597354911/4503599627370496)), (11716117/4503599627370496), by norm_num⟩
  | 6 => ⟨((912710453841739/9007199254740992), (-100021615085123/9007199254740992)), (15756675/9007199254740992), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-306471663/134217728), (-2115612201/67108864)), (1/67108864), by norm_num⟩, -5, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile023Terms2
