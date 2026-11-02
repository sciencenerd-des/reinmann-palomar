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
namespace Reinmann.XiRectangle.Tile024Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨24,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6909/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6909/640))
  have he : value ((3/4), (6909/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-3183607725/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((272369993807227/9007199254740992), (1711904205714901/9007199254740992)), (16444331/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1141468133/17179869184), (-7174373617/17179869184)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((627015459/8589934592), (1970463755/4294967296)), (79/8589934592), by norm_num⟩
  | 3 => ⟨((-459231259/8589934592), (-5772735189/17179869184)), (59/8589934592), by norm_num⟩
  | 4 => ⟨((1009034209/34359738368), (3170998909/17179869184)), (33/8589934592), by norm_num⟩
  | 5 => ⟨((-886829905/68719476736), (-2786958695/34359738368)), (119/68719476736), by norm_num⟩
  | 6 => ⟨((40595093/8589934592), (4082382761/137438953472)), (89/137438953472), by norm_num⟩
  | 7 => ⟨((-815511187/549755813888), (-2562831925/274877906944)), (57/274877906944), by norm_num⟩
  | 8 => ⟨((223982653/549755813888), (5631117293/2199023255552)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((-874915893/8796093022208), (-5499035251/8796093022208)), (127/8796093022208), by norm_num⟩
  | 10 => ⟨((768954681/35184372088832), (2416523081/17592186044416)), (57/17592186044416), by norm_num⟩
  | 11 => ⟨((-614387681/140737488355328), (-965389801/35184372088832)), (93/140737488355328), by norm_num⟩
  | 12 => ⟨((449982571/562949953421312), (5656475193/1125899906842624)), (139/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (1840610172189/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779424567821419/633825300114114700748351602688), (272475051089/79228162514264337593543950336)), (11553/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890479406543295/39614081257132168796771975168), (306489499375/4951760157141521099596496896)), (6499/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890300311016653/2475880078570760549798248448), (1302361200749/1237940039285380274899124224)), (13813/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771966261244651/154742504910672534362390528), (2604229357347/154742504910672534362390528)), (13815/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387570051996799/2417851639229258349412352), (152558828943/604462909807314587353088)), (6477/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259424300651703/604462909807314587353088), (1067649979113/302231454903657293676544)), (11337/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888824327114845/75557863725914323419136), (3468880832963/75557863725914323419136)), (18427/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298313143713543/4722366482869645213696), (1300400982179/2361183241434822606848)), (27/9223372036854775808), by norm_num⟩
  | 9 => ⟨((811255545992951/295147905179352825856), (1787353912879/295147905179352825856)), (19015/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912401034870023/36893488147419103232), (1116573313241/18446744073709551616)), (23777/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1824148517289075/9223372036854775808), (627713166251/1152921504606846976)), (13381/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797697410598049/576460752303423488), (5018114014769/1152921504606846976)), (26779/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195811128746417/144115188075855872), (4386812157743/144115188075855872)), (11725/72057594037927936), by norm_num⟩
  | 4 => ⟨((746739004625515/18014398509481984), (6572149585221/36028797018963968)), (8803/9007199254740992), by norm_num⟩
  | 3 => ⟨((745774905691043/4503599627370496), (4100540796611/4503599627370496)), (44079/9007199254740992), by norm_num⟩
  | 2 => ⟨((558126631777791/1125899906842624), (8179952998915/2251799813685248)), (2761/140737488355328), by norm_num⟩
  | 1 => ⟨((555719278704633/562949953421312), (12217211152965/1125899906842624)), (133015/2251799813685248), by norm_num⟩
  | 0 => ⟨((1097012044468535/1125899906842624), (12112083609947/562949953421312)), (16749/140737488355328), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1097012044468535/1125899906842624), (12112083609947/562949953421312)), (63892365038824037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1068344182392467/1125899906842624), (94410535238309/2251799813685248)), (533749/2251799813685248), by norm_num⟩
  | 2 => ⟨((2023503062461943/2251799813685248), (44792146027109/562949953421312)), (1057685/2251799813685248), by norm_num⟩
  | 3 => ⟨((1804096100182591/2251799813685248), (322007468369981/2251799813685248)), (2069219/2251799813685248), by norm_num⟩
  | 4 => ⟨((699678965656145/1125899906842624), (515971636897163/2251799813685248)), (1953715/1125899906842624), by norm_num⟩
  | 5 => ⟨((187847059001575/562949953421312), (641290578350811/2251799813685248)), (6647143/2251799813685248), by norm_num⟩
  | 6 => ⟨((272369993807227/9007199254740992), (1711904205714901/9007199254740992)), (16444331/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-3183607725/134217728)), (1/134217728), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-231785805/134217728), (-6672533855/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1541278902007223/9007199254740992), (217947108965105/4503599627370496)), (11832725/4503599627370496), by norm_num⟩
  | 1 => ⟨((-3384519409/8589934592), (-957187203/8589934592)), (27/4294967296), by norm_num⟩
  | 2 => ⟨((3896571969/8589934592), (275500623/2147483648)), (1/134217728), by norm_num⟩
  | 3 => ⟨((-5981459019/17179869184), (-422909085/4294967296)), (101/17179869184), by norm_num⟩
  | 4 => ⟨((3443204593/17179869184), (973784155/17179869184)), (15/4294967296), by norm_num⟩
  | 5 => ⟨((-3171308627/34359738368), (-1793776703/68719476736)), (113/68719476736), by norm_num⟩
  | 6 => ⟨((2434069323/68719476736), (1376774499/137438953472)), (89/137438953472), by norm_num⟩
  | 7 => ⟨((-400332267/34359738368), (-1811508821/549755813888)), (15/68719476736), by norm_num⟩
  | 8 => ⟨((3687196441/1099511627776), (521394151/549755813888)), (71/1099511627776), by norm_num⟩
  | 9 => ⟨((-3773370471/4398046511104), (-533579733/2199023255552)), (75/4398046511104), by norm_num⟩
  | 10 => ⟨((3475402639/17592186044416), (982890191/17592186044416)), (71/17592186044416), by norm_num⟩
  | 11 => ⟨((-2909967385/70368744177664), (-1645955129/140737488355328)), (61/70368744177664), by norm_num⟩
  | 12 => ⟨((2233482507/281474976710656), (4934833/2199023255552)), (3/17592186044416), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581726236476819/10141204801825835211973625643008), (359020081909/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779305117491511/633825300114114700748351602688), (53140674825/79228162514264337593543950336)), (1081/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((945172593107095/19807040628566084398385987584), (59774178307/4951760157141521099596496896)), (19459/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890157906886279/2475880078570760549798248448), (253995506733/1237940039285380274899124224)), (20675/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885912043786743/77371252455336267181195264), (253945176795/77371252455336267181195264)), (5169/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((775073582458627/4835703278458516698824704), (238020141691/4835703278458516698824704)), (19385/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629654066290807/302231454903657293676544), (208214178183/302231454903657293676544)), (8481/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888636012378617/75557863725914323419136), (676495724301/75557863725914323419136)), (6891/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((162271538558053/590295810358705651712), (126799137425/1180591620717411303424)), (20675/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811159047151737/295147905179352825856), (348555305263/295147905179352825856)), (28429/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824561797905515/73786976294838206464), (13608773665/1152921504606846976)), (35539/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823879550993115/9223372036854775808), (979245280825/9223372036854775808)), (39985/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797563763542459/576460752303423488), (978512786047/1152921504606846976)), (19995/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195579124567779/144115188075855872), (855375364879/144115188075855872)), (34997/144115188075855872), by norm_num⟩
  | 4 => ⟨((746566875865727/18014398509481984), (640709117007/18014398509481984)), (26253/18014398509481984), by norm_num⟩
  | 3 => ⟨((372781508185611/2251799813685248), (1598898487549/9007199254740992)), (65651/9007199254740992), by norm_num⟩
  | 2 => ⟨((2231678531537901/4503599627370496), (1594595254605/2251799813685248)), (4105/140737488355328), by norm_num⟩
  | 1 => ⟨((2221683788032321/2251799813685248), (4762327061743/2251799813685248)), (197185/2251799813685248), by norm_num⟩
  | 0 => ⟨((1095915340014747/1125899906842624), (2359790805335/562949953421312)), (24685/140737488355328), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095915340014747/1125899906842624), (2359790805335/562949953421312)), (94165802538824037/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2133419055690415/2251799813685248), (18375565551255/2251799813685248)), (193049/562949953421312), by norm_num⟩
  | 2 => ⟨((2021111813809663/2251799813685248), (34819064703605/2251799813685248)), (1475805/2251799813685248), by norm_num⟩
  | 3 => ⟨((1813518489448175/2251799813685248), (31251989004781/1125899906842624)), (1347435/1125899906842624), by norm_num⟩
  | 4 => ⟨((729403773892161/1125899906842624), (50338453309885/1125899906842624)), (1122577/562949953421312), by norm_num⟩
  | 5 => ⟨((1881147346290729/4503599627370496), (65222596774327/1125899906842624)), (777441/281474976710656), by norm_num⟩
  | 6 => ⟨((1541278902007223/9007199254740992), (217947108965105/4503599627370496)), (11832725/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-231785805/134217728), (-6672533855/268435456)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-482760083/268435456), (-1737181987/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1087770303471503/9007199254740992), (-1020063270941477/9007199254740992)), (10352969/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1243762621/4294967296), (2332692047/8589934592)), (25/4294967296), by norm_num⟩
  | 2 => ⟨((2982412509/8589934592), (-43699619/134217728)), (31/4294967296), by norm_num⟩
  | 3 => ⟨((-2383837619/8589934592), (2235458343/8589934592)), (51/8589934592), by norm_num⟩
  | 4 => ⟨((2858096479/17179869184), (-2680197497/17179869184)), (63/17179869184), by norm_num⟩
  | 5 => ⟨((-2741366415/34359738368), (2570733163/34359738368)), (63/34359738368), by norm_num⟩
  | 6 => ⟨((34237029/1073741824), (-4109565933/137438953472)), (103/137438953472), by norm_num⟩
  | 7 => ⟨((-3002397623/274877906944), (1407758389/137438953472)), (73/274877906944), by norm_num⟩
  | 8 => ⟨((1799858767/549755813888), (-1687828593/549755813888)), (45/549755813888), by norm_num⟩
  | 9 => ⟨((-959082851/1099511627776), (3597543293/4398046511104)), (49/2199023255552), by norm_num⟩
  | 10 => ⟨((3679648375/17592186044416), (-1725306411/8796093022208)), (97/17592186044416), by norm_num⟩
  | 11 => ⟨((-802128313/17592186044416), (752200743/17592186044416)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((2564559587/281474976710656), (-1202465737/140737488355328)), (9/35184372088832), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122367159/10141204801825835211973625643008), (-490620590677/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779194239853007/633825300114114700748351602688), (-1161777252093/633825300114114700748351602688)), (2885/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((29534694254965/618970019642690137449562112), (-1306792541807/39614081257132168796771975168)), (1623/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1890025333563203/2475880078570760549798248448), (-347053080159/618970019642690137449562112)), (3449/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885845744591033/77371252455336267181195264), (-693962902239/77371252455336267181195264)), (13797/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775011413656503/4835703278458516698824704), (-1300876097155/9671406556917033397649408)), (1617/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((19674989227989/9444732965739290427392), (-1137962329205/604462909807314587353088)), (11321/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888459126849033/75557863725914323419136), (-1848618493833/75557863725914323419136)), (9199/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((162254950100107/590295810358705651712), (-1385965054079/4722366482869645213696)), (13801/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811067775327051/295147905179352825856), (-1904891726057/590295810358705651712)), (18979/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824333512604465/73786976294838206464), (-594974985099/18446744073709551616)), (1483/4611686018427387904), by norm_num⟩
  | 7 => ⟨((227952823115975/1152921504606846976), (-1337859100085/4611686018427387904)), (26701/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594870380076985/1152921504606846976), (-1305484943/562949953421312)), (13355/576460752303423488), by norm_num⟩
  | 5 => ⟨((298838479492975/36028797018963968), (-2337085417883/144115188075855872)), (23381/144115188075855872), by norm_num⟩
  | 4 => ⟨((746397768699279/18014398509481984), (-3500946088619/36028797018963968)), (35091/36028797018963968), by norm_num⟩
  | 3 => ⟨((745351280200477/4503599627370496), (-273000040321/562949953421312)), (43899/9007199254740992), by norm_num⟩
  | 2 => ⟨((1115414743458505/2251799813685248), (-8711501734811/4503599627370496)), (21975/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110202508893927/1125899906842624), (-3251541405893/562949953421312)), (8257/140737488355328), by norm_num⟩
  | 0 => ⟨((2189252604264619/2251799813685248), (-25768952515515/2251799813685248)), (33159/281474976710656), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2189252604264619/2251799813685248), (-25768952515515/2251799813685248)), (126491547704601199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((1064073923721247/1125899906842624), (-50106360308677/2251799813685248)), (521879/2251799813685248), by norm_num⟩
  | 2 => ⟨((1005085484446941/1125899906842624), (-94709789197091/2251799813685248)), (1009669/2251799813685248), by norm_num⟩
  | 3 => ⟨((447621648637543/562949953421312), (-169093955472423/2251799813685248)), (1887587/2251799813685248), by norm_num⟩
  | 4 => ⟨((705491105420855/1125899906842624), (-134452653674105/1125899906842624)), (3285265/2251799813685248), by norm_num⟩
  | 5 => ⟨((426006060425915/1125899906842624), (-336993193412069/2251799813685248)), (4901747/2251799813685248), by norm_num⟩
  | 6 => ⟨((1087770303471503/9007199254740992), (-1020063270941477/9007199254740992)), (10352969/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-482760083/268435456), (-1737181987/67108864)), (1/134217728), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-500277787/268435456), (-900109175/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-169745785043279/9007199254740992), (-1354172899839/8796093022208)), (3618843/1125899906842624), by norm_num⟩
  | 1 => ⟨((3142673/67108864), (6572252429/17179869184)), (139/17179869184), by norm_num⟩
  | 2 => ⟨((-249895969/4294967296), (-4082858441/8589934592)), (11/1073741824), by norm_num⟩
  | 3 => ⟨((206989385/4294967296), (6763681393/17179869184)), (37/4294967296), by norm_num⟩
  | 4 => ⟨((-514349299/17179869184), (-4201779217/17179869184)), (47/8589934592), by norm_num⟩
  | 5 => ⟨((511243997/34359738368), (4176411647/34359738368)), (95/34359738368), by norm_num⟩
  | 6 => ⟨((-52933067/8589934592), (-6918662049/137438953472)), (5/4294967296), by norm_num⟩
  | 7 => ⟨((150324263/68719476736), (1228016381/68719476736)), (29/68719476736), by norm_num⟩
  | 8 => ⟨((-747083521/1099511627776), (-3051506071/549755813888)), (147/1099511627776), by norm_num⟩
  | 9 => ⟨((825081249/4398046511104), (6740184647/4398046511104)), (165/4398046511104), by norm_num⟩
  | 10 => ⟨((-820099953/17592186044416), (-1674872965/4398046511104)), (83/8796093022208), by norm_num⟩
  | 11 => ⟨((741044301/70368744177664), (6053677045/70368744177664)), (153/70368744177664), by norm_num⟩
  | 12 => ⟨((-613808637/281474976710656), (-5014274115/281474976710656)), (129/281474976710656), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115842083/10141204801825835211973625643008), (-2204803851913/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889545338026169/316912650057057350374175801344), (-326272386023/79228162514264337593543950336)), (5779/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((472525943665545/9903520314283042199192993792), (-2935965766979/39614081257132168796771975168)), (13005/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889901192320883/2475880078570760549798248448), (-97464686321/77371252455336267181195264)), (3455/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((221445891445015/19342813113834066795298816), (-3118202221761/154742504910672534362390528)), (13823/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549906012279647/9671406556917033397649408), (-365325656977/1208925819614629174706176)), (12961/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629548433916239/302231454903657293676544), (-639142609323/151115727451828646838272)), (11345/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888292227193185/75557863725914323419136), (-4153097634429/75557863725914323419136)), (18439/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297914049993529/4722366482869645213696), (-1556830208559/2361183241434822606848)), (6917/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621962307816785/590295810358705651712), (-4279394168741/590295810358705651712)), (19029/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912058022221047/36893488147419103232), (-5346410507433/73786976294838206464)), (11899/36893488147419103232), by norm_num⟩
  | 7 => ⟨((113961042339673/576460752303423488), (-6010819415525/9223372036854775808)), (26789/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594622905497805/1152921504606846976), (-3002978360013/576460752303423488)), (3351/144115188075855872), by norm_num⟩
  | 5 => ⟨((1195135618419635/144115188075855872), (-5249745462097/144115188075855872)), (23479/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492464578657751/36028797018963968), (-7863694516007/36028797018963968)), (35263/36028797018963968), by norm_num⟩
  | 3 => ⟨((745141370560277/4503599627370496), (-9810523435043/9007199254740992)), (11039/2251799813685248), by norm_num⟩
  | 2 => ⟨((2229971568090427/4503599627370496), (-19563849604795/4503599627370496)), (2767/140737488355328), by norm_num⟩
  | 1 => ⟨((2219072726151785/2251799813685248), (-14601542554811/1125899906842624)), (133401/2251799813685248), by norm_num⟩
  | 0 => ⟨((546602021211719/562949953421312), (-28918617466069/1125899906842624)), (269147/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((546602021211719/562949953421312), (-28918617466069/1125899906842624)), (1026714333541106467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1060714886533629/1125899906842624), (-112315310883573/2251799813685248)), (536489/2251799813685248), by norm_num⟩
  | 2 => ⟨((996502780958269/1125899906842624), (-105812711694727/1125899906842624)), (133047/281474976710656), by norm_num⟩
  | 3 => ⟨((1744065269984269/2251799813685248), (-187303792857085/1125899906842624)), (1042081/1125899906842624), by norm_num⟩
  | 4 => ⟨((1288495009661751/2251799813685248), (-580282559884839/2251799813685248)), (3921893/2251799813685248), by norm_num⟩
  | 5 => ⟨((587748312515727/2251799813685248), (-166020793247537/562949953421312)), (3254795/1125899906842624), by norm_num⟩
  | 6 => ⟨((-169745785043279/9007199254740992), (-1354172899839/8796093022208)), (3618843/1125899906842624), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-500277787/268435456), (-900109175/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-516392513/268435456), (-7432824731/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1096922533748683/9007199254740992), (-363191133018943/4503599627370496)), (14842789/4503599627370496), by norm_num⟩
  | 1 => ⟨((1341605543/4294967296), (1776822783/8589934592)), (37/4294967296), by norm_num⟩
  | 2 => ⟨((-3441150275/8589934592), (-569682557/2147483648)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((735531349/2147483648), (974137939/4294967296)), (85/8589934592), by norm_num⟩
  | 4 => ⟨((-1886600661/8589934592), (-2498614481/17179869184)), (111/17179869184), by norm_num⟩
  | 5 => ⟨((3871228123/34359738368), (2563527843/34359738368)), (29/8589934592), by norm_num⟩
  | 6 => ⟨((-413729337/8589934592), (-2191773031/68719476736)), (101/68719476736), by norm_num⟩
  | 7 => ⟨((4851176215/274877906944), (200778101/17179869184)), (151/274877906944), by norm_num⟩
  | 8 => ⟨((-3110755329/549755813888), (-2059942645/549755813888)), (99/549755813888), by norm_num⟩
  | 9 => ⟨((3546191059/2199023255552), (1174144125/1099511627776)), (115/2199023255552), by norm_num⟩
  | 10 => ⟨((-3638320191/8796093022208), (-2409296175/8796093022208)), (15/1099511627776), by norm_num⟩
  | 11 => ⟨((848373367/8796093022208), (1123585941/17592186044416)), (57/17592186044416), by norm_num⟩
  | 12 => ⟨((-1450689815/70368744177664), (-1921294025/140737488355328)), (99/140737488355328), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917417231/10141204801825835211973625643008), (-3330372398745/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889496716939707/316912650057057350374175801344), (-985576045423/158456325028528675187087900672)), (5787/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944997064766819/19807040628566084398385987584), (-2217162319623/19807040628566084398385987584)), (407/1237940039285380274899124224), by norm_num⟩
  | 15 => ⟨((1889784372389649/2475880078570760549798248448), (-4710543107057/2475880078570760549798248448)), (6921/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((885724974829669/77371252455336267181195264), (-588687560197/19342813113834066795298816)), (6923/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193724471237049/1208925819614629174706176), (-4414049048335/9671406556917033397649408)), (12985/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78687501354203/37778931862957161709568), (-3861185417351/604462909807314587353088)), (5683/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((472033533150351/18889465931478580854784), (-1568087516647/18889465931478580854784)), (18477/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297794849999333/4722366482869645213696), (-2351223084477/2361183241434822606848)), (6933/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25340584167155/9223372036854775808), (-403932029693/36893488147419103232)), (19077/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823908363242231/73786976294838206464), (-1009276894365/9223372036854775808)), (11931/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455785233918971/2305843009213693952), (-2269352203657/2305843009213693952)), (26869/9223372036854775808), by norm_num⟩
  | 6 => ⟨((99649033926621/72057594037927936), (-2267451847683/288230376151711744)), (26899/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194924108871985/144115188075855872), (-7927533472547/144115188075855872)), (11785/72057594037927936), by norm_num⟩
  | 4 => ⟨((746070722847053/18014398509481984), (-11874213256437/36028797018963968)), (35421/36028797018963968), by norm_num⟩
  | 3 => ⟨((744934295123615/4503599627370496), (-7406442391705/4503599627370496)), (44393/9007199254740992), by norm_num⟩
  | 2 => ⟨((278639087992163/562949953421312), (-115375804539/17592186044416)), (22285/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108854259256659/1125899906842624), (-1377521473353/70368744177664)), (2103/35184372088832), by norm_num⟩
  | 0 => ⟨((545844745909031/562949953421312), (-43634309455941/1125899906842624)), (68183/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((545844745909031/562949953421312), (-43634309455941/1125899906842624)), (260097505809593023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((528413754345661/562949953421312), (-42308483042131/562949953421312)), (34377/140737488355328), by norm_num⟩
  | 2 => ⟨((985633221419669/1125899906842624), (-79425832541923/562949953421312)), (557627/1125899906842624), by norm_num⟩
  | 3 => ⟨((1680858111658885/2251799813685248), (-139061631884791/562949953421312)), (2267327/2251799813685248), by norm_num⟩
  | 4 => ⟨((558636202214767/1125899906842624), (-830421498584403/2251799813685248)), (2252531/1125899906842624), by norm_num⟩
  | 5 => ⟨((248111646955967/2251799813685248), (-824058176730145/2251799813685248)), (15586611/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1096922533748683/9007199254740992), (-363191133018943/4503599627370496)), (14842789/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516392513/268435456), (-7432824731/268435456)), (1/134217728), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-265656209/134217728), (-955947265/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1215813422581425/9007199254740992), (132824808209155/4503599627370496)), (26603053/9007199254740992), by norm_num⟩
  | 1 => ⟨((6119921349/17179869184), (-83573409/1073741824)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((-4037705823/8589934592), (441110035/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((1775956191/4294967296), (-776076447/8589934592)), (83/8589934592), by norm_num⟩
  | 4 => ⟨((-4686850203/17179869184), (512027559/8589934592)), (7/1073741824), by norm_num⟩
  | 5 => ⟨((618443319/4294967296), (-540508033/17179869184)), (15/4294967296), by norm_num⟩
  | 6 => ⟨((-2176143165/34359738368), (950954457/68719476736)), (27/17179869184), by norm_num⟩
  | 7 => ⟨((6563390365/274877906944), (-717035237/137438953472)), (165/274877906944), by norm_num⟩
  | 8 => ⟨((-2165145431/274877906944), (946148549/549755813888)), (111/549755813888), by norm_num⟩
  | 9 => ⟨((1269765093/549755813888), (-277437807/549755813888)), (33/549755813888), by norm_num⟩
  | 10 => ⟨((-670196575/1099511627776), (1171478845/8796093022208)), (71/4398046511104), by norm_num⟩
  | 11 => ⟨((2572635903/17592186044416), (-1124218121/35184372088832)), (69/17592186044416), by norm_num⟩
  | 12 => ⟨((-565777803/17592186044416), (988958691/140737488355328)), (123/140737488355328), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197674689623573/1267650600228229401496703205376), (3812064284211/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889452577516439/316912650057057350374175801344), (564011204263/79228162514264337593543950336)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889894687394351/39614081257132168796771975168), (5075191386199/39614081257132168796771975168)), (1629/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889678546077043/2475880078570760549798248448), (5391298687715/2475880078570760549798248448)), (13851/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221417991665683/19342813113834066795298816), (5390069975049/154742504910672534362390528)), (433/4835703278458516698824704), by norm_num⟩
  | 13 => ⟨((774848088914613/4835703278458516698824704), (631485650691/1208925819614629174706176)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((78682042313469/37778931862957161709568), (276193392709/37778931862957161709568)), (711/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((943995909948957/37778931862957161709568), (3589290545791/37778931862957161709568)), (9247/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648843892687581/2361183241434822606848), (5381794855391/4722366482869645213696)), (13879/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621649637074359/590295810358705651712), (7396489360063/590295810358705651712)), (2387/73786976294838206464), by norm_num⟩
  | 8 => ⟨((911861436843525/36893488147419103232), (9240394726753/73786976294838206464)), (11945/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911465579138089/4611686018427387904), (10388272156477/9223372036854775808)), (26903/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594173391096079/1152921504606846976), (5189654707675/576460752303423488)), (26937/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194737808741507/144115188075855872), (4535907809579/72057594037927936)), (2951/18014398509481984), by norm_num⟩
  | 4 => ⟨((745929460071595/18014398509481984), (6793785317633/18014398509481984)), (1109/1125899906842624), by norm_num⟩
  | 3 => ⟨((1489510072516821/9007199254740992), (8474606374889/4503599627370496)), (44495/9007199254740992), by norm_num⟩
  | 2 => ⟨((1114189835155619/2251799813685248), (16896370853293/2251799813685248)), (44697/2251799813685248), by norm_num⟩
  | 1 => ⟨((554142316725701/562949953421312), (25212571296367/1125899906842624)), (2111/35184372088832), by norm_num⟩
  | 0 => ⟨((1090471718608265/1125899906842624), (49897929468961/1125899906842624)), (137135/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090471718608265/1125899906842624), (49897929468961/1125899906842624)), (523128513816451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1053946943691363/1125899906842624), (96655627329433/1125899906842624)), (69449/281474976710656), by norm_num⟩
  | 2 => ⟨((978294645134809/1125899906842624), (90478649474359/562949953421312)), (567783/1125899906842624), by norm_num⟩
  | 3 => ⟨((820956519348771/1125899906842624), (78616915892655/281474976710656)), (1169205/1125899906842624), by norm_num⟩
  | 4 => ⟨((1021546749821461/2251799813685248), (458591881860351/1125899906842624)), (147387/70368744177664), by norm_num⟩
  | 5 => ⟨((179706654568717/4503599627370496), (1664350600126415/4503599627370496)), (2030331/562949953421312), by norm_num⟩
  | 6 => ⟨((-1215813422581425/9007199254740992), (132824808209155/4503599627370496)), (26603053/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-265656209/134217728), (-955947265/33554432)), (1/134217728), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-272601259/134217728), (-7847508743/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-169458378096949/2251799813685248), (968012000584593/9007199254740992)), (6660367/2251799813685248), by norm_num⟩
  | 1 => ⟨((875285711/4294967296), (-4999971567/17179869184)), (35/4294967296), by norm_num⟩
  | 2 => ⟨((-1185158823/4294967296), (1692521751/4294967296)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((2139646393/8589934592), (-3055622579/8589934592)), (89/8589934592), by norm_num⟩
  | 4 => ⟨((-2897134923/17179869184), (2068694835/8589934592)), (123/17179869184), by norm_num⟩
  | 5 => ⟨((784558681/8589934592), (-4481703571/34359738368)), (17/4294967296), by norm_num⟩
  | 6 => ⟨((-354104049/8589934592), (4045559419/68719476736)), (125/68719476736), by norm_num⟩
  | 7 => ⟨((2191843523/137438953472), (-1565082571/68719476736)), (99/137438953472), by norm_num⟩
  | 8 => ⟨((-2967811147/549755813888), (4238322171/549755813888)), (17/68719476736), by norm_num⟩
  | 9 => ⟨((1785995905/1099511627776), (-637643845/274877906944)), (21/274877906944), by norm_num⟩
  | 10 => ⟨((-483656657/1099511627776), (690708617/1099511627776)), (93/4398046511104), by norm_num⟩
  | 11 => ⟨((238139365/2199023255552), (-1360344443/8796093022208)), (93/17592186044416), by norm_num⟩
  | 12 => ⟨((-859857807/35184372088832), (2455920695/70368744177664)), (85/70368744177664), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (2841879634581/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778830217420257/633825300114114700748351602688), (840864674457/158456325028528675187087900672)), (723/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889810673638329/39614081257132168796771975168), (3783207089609/39614081257132168796771975168)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((944794828400667/1237940039285380274899124224), (502352928883/309485009821345068724781056)), (1729/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885627733025123/77371252455336267181195264), (4017885214943/154742504910672534362390528)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549613687875953/9671406556917033397649408), (3765770726371/9671406556917033397649408)), (12975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258840946133393/604462909807314587353088), (1647026469363/302231454903657293676544)), (11357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943938048136751/37778931862957161709568), (5350968146187/75557863725914323419136)), (18461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297601726217049/4722366482869645213696), (4011592173951/4722366482869645213696)), (3463/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((810766248305895/295147905179352825856), (5513284953759/590295810358705651712)), (1191/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1823578232407217/73786976294838206464), (6887626269401/73786976294838206464)), (11917/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822770886963239/9223372036854775808), (3871554802899/4611686018427387904)), (13417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594016177518981/1152921504606846976), (3868137921121/576460752303423488)), (6715/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194603680049415/144115188075855872), (3380779213033/72057594037927936)), (23531/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491664576579905/36028797018963968), (316468262215/1125899906842624)), (35353/36028797018963968), by norm_num⟩
  | 3 => ⟨((186159886456055/1125899906842624), (6315945358139/4503599627370496)), (44291/9007199254740992), by norm_num⟩
  | 2 => ⟨((556988350627435/1125899906842624), (3147921976057/562949953421312)), (44441/2251799813685248), by norm_num⟩
  | 1 => ⟨((554004642345297/562949953421312), (18787223887841/1125899906842624)), (67039/1125899906842624), by norm_num⟩
  | 0 => ⟨((272524210091705/281474976710656), (18587205525609/562949953421312)), (67795/562949953421312), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((272524210091705/281474976710656), (18587205525609/562949953421312)), (258617403270530523/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((527102443710667/562949953421312), (71984565915937/1125899906842624)), (271511/1125899906842624), by norm_num⟩
  | 2 => ⟨((982472918072227/1125899906842624), (269602939821865/2251799813685248)), (1086325/2251799813685248), by norm_num⟩
  | 3 => ⟨((105147179680377/140737488355328), (235258556642427/1125899906842624)), (1078003/1125899906842624), by norm_num⟩
  | 4 => ⟨((1158598359988831/2251799813685248), (703061395103857/2251799813685248)), (2061287/1125899906842624), by norm_num⟩
  | 5 => ⟨((376612001355271/2251799813685248), (361739873317463/1125899906842624)), (6816619/2251799813685248), by norm_num⟩
  | 6 => ⟨((-169458378096949/2251799813685248), (968012000584593/9007199254740992)), (6660367/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-7847508743/268435456)), (1/134217728), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨24,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile024Terms1
